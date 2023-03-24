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
 * mutable expr list partitioned by size.
   array idx = size of expr in list (first element is ignored because size cannot be zero)
 *)
type m_expr_list = expr_set array ref

let m_expr_list_create_empty(): m_expr_list = ref (BatArray.make 2 expr_set_empty)

let m_expr_list_add (la: m_expr_list) (expr: Exprs.expr) (signature: Exprs.signature) (size: int): unit =
    if size < (BatArray.length !la) then
        !la.(size) <- expr_set_add expr signature !la.(size)
    else
        la := BatArray.init (size + 1) (fun idx ->
            if idx < BatArray.length !la then
                !la.(idx)
            else if idx = size then
                expr_set_add expr signature expr_set_empty 
            else expr_set_empty
        )

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
    mutable min_size: int;
    mutable max_size: int;
    mutable nt_sig_to_expr: nt_sig_to_expr;
    mutable nt_sig_search: (Grammar.non_terminal, SigSearch.t) BatMap.t;
    nt_to_expr_size_ordered: (Grammar.non_terminal, m_expr_list) BatMap.t;
}

let create_empty (grammar: Grammar.grammar) (spec: (Exprs.const list * Exprs.const) list): component_pool =
    let nts: Grammar.non_terminal BatSet.t = bm_key_set grammar in
    {min_size=0;
    max_size=0;
    nt_sig_to_expr=BatSet.fold (fun nt m -> BatMap.add nt Exprs.SignatureMap.empty m) nts BatMap.empty;
    nt_sig_search=BatSet.fold (fun nt m -> BatMap.add nt (SigSearch.create_empty (BatList.length spec)) m) nts BatMap.empty;
    nt_to_expr_size_ordered=BatSet.fold (fun nt m -> BatMap.add nt (m_expr_list_create_empty()) m) nts BatMap.empty;
    }

let get_sized_components (t: component_pool) (nt: Grammar.non_terminal) (target_size: int): (Exprs.expr * Exprs.signature) list =
    try
        let m_expr_list_for_nt = !(BatMap.find nt t.nt_to_expr_size_ordered) in
        if target_size < BatArray.length m_expr_list_for_nt then
            expr_set_to_list m_expr_list_for_nt.(target_size)
        else []
    with Not_found -> []

let get_num_of_sized_components (t: component_pool) (nt: Grammar.non_terminal) (target_size: int): int =
    try
        let m_expr_list_for_nt = !(BatMap.find nt t.nt_to_expr_size_ordered) in
        if target_size < BatArray.length m_expr_list_for_nt then
            expr_set_cardinal m_expr_list_for_nt.(target_size)
        else 0
    with Not_found -> 0

let get_num_of_components (t: component_pool) (nt: Grammar.non_terminal): int =
    try
        let m_expr_list_for_nt = !(BatMap.find nt t.nt_to_expr_size_ordered) in
        BatArray.sum (BatArray.map expr_set_cardinal m_expr_list_for_nt)
    with Not_found -> 0

let add_component (t: component_pool) (nt: Grammar.non_terminal) (expr_size: int)
    : Exprs.expr -> Exprs.signature -> unit =
    let search = BatMap.find nt t.nt_sig_search in
    (* let _ =
        Logger.g_info_f "before adding component to nt %s, search table =" (Grammar.string_of_non_terminal nt);
        SigSearch.dump_table search;
    in *)
    t.min_size <- min t.min_size expr_size;
    t.max_size <- max t.max_size expr_size;
    fun (expr: Exprs.expr) (signature: Exprs.signature) -> begin
        try
            let sub_map = BatMap.find nt t.nt_sig_to_expr in
            t.nt_sig_to_expr <- BatMap.add nt (Exprs.SignatureMap.update_stdlib signature (function
                    | None -> begin
                        SigSearch.add signature expr signature expr_size search;
                        begin
                            try
                                let m_expr_list_for_nt = BatMap.find nt t.nt_to_expr_size_ordered in
                                m_expr_list_add m_expr_list_for_nt expr signature expr_size
                            with Not_found -> ()
                        end;
                        Some expr
                    end
                    | Some existing ->
                        Some existing
                ) sub_map) t.nt_sig_to_expr
        with Not_found -> begin
            t.nt_sig_to_expr <- ns2e_add (nt, signature) expr t.nt_sig_to_expr;
            SigSearch.add signature expr signature expr_size search;
            (* Logger.g_info_f "add_component: %s -> %s, result:" (Exprs.string_of_signature signature) (Exprs.string_of_expr expr);
            SigSearch.dump_table search; *)
            begin
                try
                    let m_expr_list_for_nt = BatMap.find nt t.nt_to_expr_size_ordered in
                    m_expr_list_add m_expr_list_for_nt expr signature expr_size
                with Not_found -> ()
            end
        end
    end

let find_expr_of_nt_sig (t: component_pool) (nt: Grammar.non_terminal) (s: Exprs.signature): Exprs.expr =
    ns2e_find (nt, s) t.nt_sig_to_expr

let find_exprs_of_nt_partial_sig
    (t: component_pool)
    ?(expr_size_range_opt: (int * int) option=None)
    (nt: Grammar.non_terminal)
    (ps: (int * Exprs.const) list): Exprs.ExprSigSet.t =
    let search = BatMap.find nt t.nt_sig_search in
    let min_size, max_size =
        match expr_size_range_opt with
        | None ->
            t.min_size, t.max_size
        | Some (l,u) ->
            max t.min_size l, min t.max_size u
    in
    let rec loop acc expr_size =
        if expr_size <= max_size then
            loop (Exprs.ExprSigSet.union acc (SigSearch.find ps expr_size search)) (expr_size + 1)
        else acc
    in
    loop Exprs.ExprSigSet.empty min_size

let get_num_total_components t =
    BatMap.foldi (fun nt submap sum -> Exprs.SignatureMap.cardinal submap + sum) t.nt_sig_to_expr 0

let max_size (t: component_pool): int = t.max_size