open Common
open Vocab

open SynthLang
open Exprs
open Operators
open Grammar
open GrammarUtil

open Dom.AbstDom

exception EarlyBotTermination of string * rewrite * AbstState.t

let _ = Printexc.register_printer (fun exn ->
        match exn with
        | EarlyBotTermination (msg, rw, st) -> Some (
            Printf.sprintf "Infeasible(%s): %s" msg (SynthLang.Grammar.string_of_rewrite rw)
        )
        | _ -> None
    )

let is_empty_concretized (t: AbstSig.t): bool =
    AbstSig.is_bot t

let zip_with_sub_addrs (addr: addr) (subs: 'a list): (addr * 'a) list =
    BatList.map (fun (index, sub) -> (addr@[index], sub) ) (zip_with_index subs)

let forward_analysis
    (pgm: rewrite)
    (subst_spot: addr)
    (prev_semantics: AbstState.t)
    (spec: SynthSpec.Specification.iospec)
    : addr option * AbstState.t (* last_updated_spot * state *)
=
    let rec forward_aux
        (e: rewrite)
        (addr: addr)
        (m: AbstState.t)
        : AbstState.t =
        let addr_relation = compare_addr subst_spot addr in
        if addr_relation = ADDR_NO_ORDER then begin
            m
        end
        else begin
            let next_m =
                match e with
                | NTRewrite nt ->
                    AbstState.update_value addr AbstSig.top_repr m
                | ExprRewrite e -> begin
                    try
                        let v = AbstSig.alpha (SynthLang.Exprs.compute_signature spec e) in
                        AbstState.update_value addr v m
                    with UndefinedSemantics -> begin
                        raise (EarlyBotTermination ("Undefined semantics in eval expr", (ExprRewrite e), m))
                    end
                end
                | FuncRewrite (op, operands) -> begin
                    let addr_operands = zip_with_sub_addrs addr operands in
                    let m' = BatList.fold_left (fun m (sub_addr, a) ->
                            forward_aux a sub_addr m
                        ) m addr_operands
                    in
                    let sub_addrs = BatList.map fst addr_operands in
                    if BatList.exists (fun sub_addr -> AbstState.is_updated sub_addr m m') sub_addrs then
                        let v = AbstSig.forward_operation op addr (BatList.map (fun sub_addr -> (sub_addr, AbstState.lookup sub_addr m')) sub_addrs) in
                        AbstState.update_value addr v m'
                    else
                        m'
                end
            in
            if is_empty_concretized (AbstState.lookup addr next_m) then begin
                raise (EarlyBotTermination ("forward result is bot", e, next_m))
            end else
                next_m
        end
    in
    Logger.g_with_increased_depth (fun () ->
        let next_semantics = forward_aux pgm [] prev_semantics in
        (AbstState.dominant_diff_addr prev_semantics next_semantics, next_semantics)
    )

let backward_analysis
    (pgm: rewrite)
    (start_spot: addr)
    (prev_semantics: AbstState.t)
    (spec: SynthSpec.Specification.iospec)
    : AbstState.t
=
    let rec backward_aux
        (m: AbstState.t)
        (post: AbstSig.t)
        (addr: addr)
        (e: rewrite)
        : AbstState.t
    =
        let m = AbstState.update_value addr post m in
        let post = AbstState.lookup addr m in
        if is_empty_concretized post then
                raise (EarlyBotTermination ("post-value update result is bot", e, m))
        else begin
            match e with
            | NTRewrite _  | ExprRewrite _ ->
                m
            | FuncRewrite (op, operands) ->
                let addr_operands = zip_with_sub_addrs addr operands in
                let vs = BatList.map (fun addr -> (addr, AbstState.lookup addr m)) (BatList.map fst addr_operands) in
                let posts = Dom.AbstDom.AbstSig.backward_operation op (addr, post) vs in
                let m' = BatList.fold_left (fun m (sub_addr, post_v) -> AbstState.update_value sub_addr post_v m) m posts in
                let vs_updated = BatList.map (fun (sub_addr, sub_rewrite) -> (sub_addr, sub_rewrite, AbstState.lookup sub_addr m')) addr_operands in
                BatList.fold_left (fun m (sub_addr, sub_rewrite, v_updated) ->
                        if is_empty_concretized v_updated then
                            raise (EarlyBotTermination ("sub-expression post-value update result is bot at " ^ string_of_list string_of_int sub_addr, sub_rewrite, m'))
                        else
                            backward_aux m' v_updated sub_addr sub_rewrite
                    ) m' vs_updated
        end
    in
    let start_post_cond =
        if start_spot = [] then
            AbstSig.alpha (BatList.map snd spec |> signature_of_const_list)
        else
            AbstState.lookup start_spot prev_semantics
    in
    backward_aux prev_semantics start_post_cond start_spot (access_addr start_spot pgm)

type feasibility =
    | NotDesiredExpr
    | Infeasible
    | DoBruteForce
    | NeedMoreAnalysis of AbstState.t

let check_feasibility
    (candidate: rewrite)
    (plugged_spot: addr)
    (spec: SynthSpec.Specification.iospec)
    (prev_semantics: AbstState.t)
    : feasibility =
    (* assume candidate is not ExprRewrite *)
    let hole_size = count_holes candidate in
    let feasibility = Logger.g_with_increased_depth (fun () ->
        try
            let (last_updated, forward_result) =
                if Global.t.cli_options.force_full_analysis then
                    forward_analysis candidate [] AbstState.empty spec
                else
                    forward_analysis candidate plugged_spot prev_semantics spec
            in
            let backward_starting_point  =
                match BatOption.default plugged_spot last_updated with
                | [] -> []
                | non_empty -> BatList.take (BatList.length non_empty - 1) non_empty
            in
            let (_, backward_result) =
                if Global.t.cli_options.force_full_analysis then
                    (candidate, backward_analysis candidate [] forward_result spec)
                else if Global.t.cli_options.no_backward then
                    (candidate, forward_result)
                else
                    (candidate, backward_analysis candidate backward_starting_point forward_result spec)
            in
            if AbstState.has_bot backward_result then begin
                Logger.g_in_debug_lazy (fun () -> Logger.g_debug_f "infeasible by backward: %s" (SynthLang.Grammar.string_of_rewrite candidate));
                Logger.g_in_debug_lazy (fun () -> Logger.g_debug_f "  with %s" (SynthSpec.Specification.string_of_io_spec spec));
                Logger.g_in_debug_lazy (fun () -> Logger.g_debug_f "  forward result: %s" (AbstState.to_string candidate forward_result));
                Logger.g_in_debug_lazy (fun () -> Logger.g_debug_f "  backward result: %s" (AbstState.to_string candidate backward_result));
                Infeasible
            end
            else
                NeedMoreAnalysis backward_result
        with EarlyBotTermination (msg, part, st) -> begin
            Logger.g_in_debug_lazy (fun () -> Logger.g_debug_f "infeasible(msg=%s) by early termination at part: %s" msg (SynthLang.Grammar.string_of_rewrite part));
            Infeasible
        end
    ) in
    feasibility
