open Common
open Vocab
open SynthLang

type expr_set = {
    s: Exprs.ExprSigSet.t;
    mutable l: (Exprs.expr * Exprs.signature) list option; (* lazy cache for BatSet.to_list result *)
    mutable c: int option; (* lazy cache for BatSet.cardinal result *)
}

let expr_set_empty: expr_set = {s = Exprs.ExprSigSet.empty; l=Some []; c=Some 0;}

let expr_set_add (expr: Exprs.expr) (signature: Exprs.signature) (expr_set: expr_set): expr_set =
    {s = Exprs.ExprSigSet.add (expr, signature) expr_set.s;
    l = None;
    c = None}

let expr_set_to_list (expr_set: expr_set): (Exprs.expr * Exprs.signature) list =
    match expr_set.l with
    | Some l -> l
    | None -> begin
        let l = Exprs.ExprSigSet.to_list expr_set.s in
        expr_set.l <- Some l;
        l
    end

let expr_set_cardinal (expr_set: expr_set): int =
    match expr_set.c with
    | Some c -> c
    | None -> begin
        let c = BatList.length (expr_set_to_list expr_set) in
        expr_set.c <- Some c;
        c
    end

(**
  For max term size is N,
  sized_expr_set = (empty_set, expr_set_size_1, ..., expr_set_size_N)
  We will use this array like immutable (always copy to modification)
  why use array? to lookup by size in constant time
    *)
type sized_expr_set = expr_set array

let sized_expr_set_empty: sized_expr_set = BatArray.make 2 expr_set_empty

let sized_expr_set_add (la: sized_expr_set) (expr: Exprs.expr) (signature: Exprs.signature) (size: int): sized_expr_set =
    arr_copy_update_extend size
        (expr_set_add expr signature)
        expr_set_empty
        la

type nt_sig_to_expr = (Grammar.non_terminal, Exprs.expr Exprs.SignatureMap.t) BatMap.t

let ns2e_empty = BatMap.empty

let ns2e_add ((nt, s): Grammar.non_terminal * Exprs.signature) (e: Exprs.expr) (m: nt_sig_to_expr): nt_sig_to_expr =
    let sub_map = BatMap.find_default Exprs.SignatureMap.empty nt m in
    BatMap.add nt (Exprs.SignatureMap.add s e sub_map) m

let ns2e_mem ((nt, s): Grammar.non_terminal * Exprs.signature) (m: nt_sig_to_expr): bool =
    try
        let sub_map = BatMap.find nt m in
        Exprs.SignatureMap.mem s sub_map
    with Not_found ->
        false

let ns2e_find ((nt, s): Grammar.non_terminal * Exprs.signature) (m: nt_sig_to_expr): Exprs.expr =
    let sub_map = BatMap.find nt m in
    Exprs.SignatureMap.find s sub_map

type component_pool = {
    min_term_size: int;
    max_term_size: int;
    nt_sig_to_expr: nt_sig_to_expr;
    predicate_nts: Grammar.non_terminal BatSet.t;
    nt_sig_search: (Grammar.non_terminal, SigSearch.t) BatMap.t;
    nt_to_expr_size_ordered: (Grammar.non_terminal, sized_expr_set) BatMap.t;
}

let create_empty (grammar: Grammar.grammar) (spec: (Exprs.const list * Exprs.const_opt) list): component_pool =
    let nts: Grammar.non_terminal BatSet.t = bm_key_set grammar in
    let predicate_nts =
        BatMap.foldi (fun nt rules s ->
                let contains_cmp = BatSet.exists (fun rule ->
                        Grammar.is_function_rule rule && (match Grammar.op_of_rule rule with
                            | GEN_CMP_OP _ -> true
                            | _ -> false
                    )) rules
                in
                if contains_cmp then BatSet.add nt s else s
            ) grammar BatSet.empty
    in
    {min_term_size=0;
    max_term_size=0;
    nt_sig_to_expr=BatSet.fold (fun nt m -> BatMap.add nt Exprs.SignatureMap.empty m) nts BatMap.empty;
    predicate_nts=predicate_nts;
    nt_sig_search=BatSet.fold (fun nt m -> BatMap.add nt (SigSearch.create_empty (BatList.length spec)) m) nts BatMap.empty;
    nt_to_expr_size_ordered=BatSet.fold (fun nt m -> BatMap.add nt sized_expr_set_empty m) nts BatMap.empty;
    }

let get_sized_components (t: component_pool) (nt: Grammar.non_terminal) (target_size: int): (Exprs.expr * Exprs.signature) list =
    try
        let sized_set_for_nt = BatMap.find nt t.nt_to_expr_size_ordered in
        if target_size < BatArray.length sized_set_for_nt then
            expr_set_to_list sized_set_for_nt.(target_size)
        else []
    with Not_found -> []

let get_num_of_sized_components (t: component_pool) (nt: Grammar.non_terminal) (target_size: int): int =
    try
        let sized_set_for_nt = BatMap.find nt t.nt_to_expr_size_ordered in
        if target_size < BatArray.length sized_set_for_nt then
            expr_set_cardinal sized_set_for_nt.(target_size)
        else 0
    with Not_found -> 0

let get_num_of_components (t: component_pool) (nt: Grammar.non_terminal): int =
    try
        let sized_set_for_nt = BatMap.find nt t.nt_to_expr_size_ordered in
        BatArray.sum (BatArray.map expr_set_cardinal sized_set_for_nt)
    with Not_found -> 0

let add_components (t: component_pool) (nt: Grammar.non_terminal) (term_size: int)
    (candidate_components: (Exprs.expr * Exprs.signature) BatEnum.t): component_pool =
    (* let _ =
        Logger.g_info_f "before adding component to nt %s, search table =" (Grammar.string_of_non_terminal nt);
        SigSearch.dump_table search;
    in *)
    let size_bound_updated_t =
        if BatSet.mem nt t.predicate_nts then begin
            t (* ignore... *)
        end
        else begin
            {t with
                min_term_size = min term_size t.min_term_size;
                max_term_size = max term_size t.max_term_size;
            }
        end
    in
    let building_t = ref size_bound_updated_t in
    let _ =
        BatEnum.iter (fun (expr, signature) ->
            (* try *)
                let next_sub_map =
                    Exprs.SignatureMap.update_stdlib signature (function
                        | None -> begin
                            let updated_sig_search =
                                SigSearch.add
                                    signature expr signature term_size (BatMap.find nt (!building_t).nt_sig_search)
                            in
                            building_t := {!building_t with
                                nt_sig_search =
                                    BatMap.add nt
                                        updated_sig_search
                                        (!building_t).nt_sig_search;
                            };
                            begin
                                try
                                    let updated_sized_exprs_map =
                                        sized_expr_set_add
                                            (BatMap.find nt (!building_t).nt_to_expr_size_ordered)
                                            expr signature term_size
                                    in
                                    building_t :=
                                        {!building_t with nt_to_expr_size_ordered =
                                            BatMap.add nt
                                                updated_sized_exprs_map
                                                (!building_t).nt_to_expr_size_ordered
                                        }
                                with Not_found -> ()
                            end;
                            Some expr
                        end
                        | some_existing ->
                            some_existing
                    ) (BatMap.find nt (!building_t).nt_sig_to_expr)
                in
                building_t := {!building_t with
                    nt_sig_to_expr = BatMap.add nt next_sub_map (!building_t).nt_sig_to_expr}
            (* with Not_found -> begin
                (* Logger.g_info_f "add_component: %s -> %s, result:" (Exprs.string_of_signature signature) (Exprs.string_of_expr expr);
                SigSearch.dump_table search; *)
                let _ =
                    begin try
                        let sized_expr_set = BatMap.find nt t.nt_to_expr_size_ordered in
                        building_t := {!building_t with nt_to_expr_size_ordered =
                            BatMap.add nt (sized_expr_set_add sized_expr_set expr signature term_size) t.nt_to_expr_size_ordered
                        }
                    with Not_found ->
                        ()
                    end
                in
                building_t := {!building_t with
                    nt_sig_to_expr =
                        ns2e_add (nt, signature) expr (!building_t).nt_sig_to_expr;
                    nt_sig_search =
                        BatMap.add nt
                            (SigSearch.add signature expr signature term_size
                                (BatMap.find nt (!building_t).nt_sig_search))
                            (!building_t).nt_sig_search;
                }
            end *)
        ) candidate_components
    in
    !building_t

let find_expr_of_nt_sig (t: component_pool) (nt: Grammar.non_terminal) (s: Exprs.signature): Exprs.expr =
    ns2e_find (nt, s) t.nt_sig_to_expr

let find_exprs_of_nt_partial_sig
    (t: component_pool)
    ?(expr_size_range_opt: (int * int) option=None)
    (nt: Grammar.non_terminal)
    (ps: (int * Exprs.const) list): Exprs.ExprSigSet.t =
    let search = BatMap.find nt t.nt_sig_search in
    let min_size, max_size =
        let existing_min, existing_max = t.min_term_size, t.max_term_size in
        match expr_size_range_opt with
        | None ->
            (existing_min, existing_max)
        | Some (l,u) ->
            (max existing_min l, min existing_max u)
    in
    let rec loop acc expr_size =
        if expr_size <= max_size then
            loop (Exprs.ExprSigSet.union acc (SigSearch.find ps expr_size search)) (expr_size + 1)
        else acc
    in
    loop Exprs.ExprSigSet.empty min_size

let get_num_total_components (t: component_pool): int =
    BatMap.foldi (fun nt submap sum -> Exprs.SignatureMap.cardinal submap + sum) t.nt_sig_to_expr 0

let max_size (t: component_pool): int = t.max_term_size

let min_size (t: component_pool): int = t.min_term_size

let helper_less_spec_subset (s1: (int * Exprs.const) list) (s2: (int * Exprs.const) list): bool =
    let rec aux l1 l2 =
        match l1, l2 with
        | [], _ -> true
        | _ , [] -> false
        | (i1, _) :: tail1, (i2, _) :: tail2 ->
            if i1 < i2 then false
            else if i1 > i2 then aux l1 tail2
            else aux tail1 tail2
    in
    aux s1 s2
