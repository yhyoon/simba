open Common
open Vocab

open SynthLang
open Exprs
open Operators
open Grammar
open GrammarUtil

open Dom
open AbstDom

type t = {
    m: AbstSig.t AddrMap.t;
    br: ABoolRel.t array; (* TODO: to signature ... T_T *)
}

let empty: t = {
    m = AddrMap.empty;
    br = BatArray.make 0 ABoolRel.empty;
}

let update_value (addr: addr) (v: AbstSig.t) (t: t): t =
    try
        let prev_v = AddrMap.find addr t.m in
        let v' = AbstSig.meet prev_v v in
        if not (AbstSig.leq prev_v v') then
            {t with m = AddrMap.add addr v' t.m}
        else
            t
    with Not_found ->
        {t with m = AddrMap.add addr v t.m}

let lookup (addr: addr) (t: t): AbstSig.t =
    try
        AddrMap.find addr t.m
    with Not_found ->
        AbstSig.top_repr

let update_relation (sig_index: int) (addr1: addr) (r: ABoolRel.rel_op) (addr2: addr) (t: t): t =
    let as_abool (sig_index) (addr: addr) (t: t): ABitSeq.Elem.t =
        if ABoolRel.is_zero (addr) t.br.(sig_index) then
            ABitSeq.Elem.B_Zero
        else if ABoolRel.is_one (addr) t.br.(sig_index) then
            ABitSeq.Elem.B_One
        else
            ABitSeq.Elem.B_Top
    in
    try
        let updated =
            {t with br = arr_copy_set_extend sig_index (ABoolRel.set_relation addr1 r addr2 t.br.(sig_index)) ABoolRel.empty t.br}
        in
        let sig1 = AddrMap.find addr1 t.m in
        let sig2 = AddrMap.find addr2 t.m in
        let sig1' =
            match sig1 with
            | AbstSig.Bool bl ->
                let updated = BatList.modify_at sig_index (fun _ -> as_abool sig_index addr1 t) (ABoolSig.to_elem_list bl) in
                AbstSig.Bool (ABoolSig.of_list updated)
            | _ -> sig1
        in
        let sig2' =
            match sig2 with
            | AbstSig.Bool bl ->
                let updated = BatList.modify_at sig_index (fun _ -> as_abool sig_index addr2 t) (ABoolSig.to_elem_list bl) in
                AbstSig.Bool (ABoolSig.of_list updated)
            | _ -> sig2
        in
        {t with m = t.m |> AddrMap.add addr1 sig1' |> AddrMap.add addr2 sig2'}
    with ABoolRel.Contradiction msg -> begin
        Logger.g_info_f "contradiction %s" (msg);
        (* Logger.g_debug_lazy (fun () -> msg); *)
        update_value addr1 AbstSig.bot_repr t
        |> update_value addr2 AbstSig.bot_repr
    end

let is_updated (addr: addr) (prev_t: t) (next_t: t): bool =
    let m_updated =
        try
            let next_v = AddrMap.find addr next_t.m in
            begin try
                let prev_v = AddrMap.find addr prev_t.m in
                not (AbstSig.leq prev_v next_v)
            with Not_found ->
                true
            end 
        with Not_found ->
            false
    in
    if m_updated then
        true
    else
        BatArray.exists2 (fun prev_rel next_rel ->
                ABoolRel.is_updated addr prev_rel next_rel
            ) prev_t.br next_t.br

let dominant_diff_addr (prev_t: t) (next_t: t): addr option =
    let diff_spots = BatEnum.fold (fun ds addr ->
            if is_updated addr prev_t next_t then addr :: ds else ds
        ) [] (AddrMap.keys next_t.m)
    in
    match diff_spots with
    | [] -> None
    | first :: remains ->
        Some (BatList.fold_left common_prefix first remains)

let has_bot (t: t): bool =
    BatEnum.exists AbstSig.is_bot (AddrMap.values t.m)

let to_string (pgm: rewrite) (semantics: t): string =
    let rec string_of_semantics_aux (indent: string) (addr: addr) (e: rewrite) (s: t): string * t =
        let s_ref = ref s in
        let head_line =
            try
                Printf.sprintf "%s(%s) --> %s" indent (SynthLang.Grammar.string_of_rewrite e) (AddrMap.find addr semantics.m |> AbstSig.to_string)
            with Not_found -> Printf.sprintf "%s(%s) --> %s" indent (SynthLang.Grammar.string_of_rewrite e) ("??Not_found")
        in
        let _ = s_ref := {!s_ref with m = AddrMap.remove addr !s_ref.m} in
        let more_lines =
            match e with
            | FuncRewrite (_, operands) ->
                BatList.mapi (fun idx sub ->
                        let sub_addr = addr@[idx] in
                        let _ = s_ref := {!s_ref with m = AddrMap.remove sub_addr !s_ref.m} in
                        let (sub_line, s') = string_of_semantics_aux (indent ^ "  ") sub_addr sub !s_ref in
                        let _ = s_ref := s' in
                        sub_line
                    ) operands
            | _ -> []
        in
        (BatList.fold_left (fun lines next -> lines ^ "\n" ^ next) head_line more_lines, !s_ref)
    in
    let (result, check) = string_of_semantics_aux "" [] pgm semantics in
    if not (AddrMap.is_empty check.m) then begin
        (* integrity broken *)
        Logger.g_error_f "string_of_semantics: not printed entry exists for %s, remain key values = %s"
            (string_of_rewrite pgm)
            (BatList.of_enum (AddrMap.keys check.m) |>
                string_of_list (fun addr -> string_of_list string_of_int addr ^ " |-> " ^ (try AddrMap.find addr check.m |> AbstSig.to_string with Not_found -> "??Not_found"))
            );
        result
    end
    else
        result

