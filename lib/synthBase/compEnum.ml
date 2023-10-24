open Common
open Vocab

open SynthLang
open Components

type t = {
    size_upper_bound: int;
    initial_count: int;
    iter_type: iter_type;
    mutable cur_comp_size: int;
    mutable count: int;
    mutable cur_h: (Exprs.expr * Exprs.signature) list;
    mutable cur_t: (Exprs.expr * Exprs.signature) list list;
}
and iter_type =
    | IterEmpty
    | IterAll
    | IterSelectedSet
    | IterSymmBreak

exception No_more_elements

let string_of_iter_type (iter_type: iter_type): string = match iter_type with
    | IterEmpty -> "empty"
    | IterAll -> "bruteforce"
    | IterSelectedSet -> "pruned-subset"
    | IterSymmBreak -> "symmetric-broken-set"

let empty(): t = {
    size_upper_bound = 1;
    cur_comp_size = 0;
    initial_count = 0;
    iter_type = IterEmpty;
    count = 0;
    cur_h = [];
    cur_t = [];
}

let make_ranged ?(iter_type: iter_type option = None) (lb: int) (ub: int) (comp: component_pool) (nt: Grammar.non_terminal): t =
    let lb = max comp.min_term_size lb in
    let ub = min comp.max_term_size ub in
    try
        let la = BatMap.find nt comp.nt_to_expr_size_ordered in
        let llr = BatArray.to_list la |> BatList.drop lb in
        match llr with
        | [] -> empty()
        | h :: t ->
            let initial_count = BatList.fold_lefti (fun sum size_idx sub_set ->
                    if size_idx > ub then sum
                    else sum + expr_set_cardinal sub_set
                ) (expr_set_cardinal h) t
            in
            {
                size_upper_bound = ub;
                cur_comp_size = lb;
                initial_count = initial_count;
                iter_type = BatOption.default IterAll iter_type;
                count = initial_count;
                cur_h = expr_set_to_list h;
                cur_t = BatList.map expr_set_to_list t;
            }
    with Not_found -> empty()

let make_full (comp: component_pool) (nt: Grammar.non_terminal): t =
    make_ranged comp.min_term_size comp.max_term_size comp nt

let singleton (((expr, signature), size): (Exprs.expr * Exprs.signature) * int): t = {
    size_upper_bound = size;
    cur_comp_size = size;
    initial_count = 1;
    iter_type = IterSelectedSet;
    count = 1;
    cur_h = [(expr, signature)];
    cur_t = [];
}

let from_set (exprs: Exprs.ExprSigSet.t): t =
    let (ess, max_size) =
        Exprs.ExprSigSet.fold (fun (e,signature) (m, max_size) ->
            let s = Exprs.size_of_expr e in
            let set' = try
                    Exprs.ExprSigSet.add (e,signature) (BatMap.find s m)
                with Not_found -> 
                    Exprs.ExprSigSet.singleton (e,signature)
            in
            (BatMap.add s set' m, max max_size s)
        ) exprs (BatMap.empty, 1)
    in
    match BatList.of_seq (BatMap.to_seq ess) with
    | [] -> empty()
    | (min_size, min_size_exprs) :: others ->
        let cur_h = Exprs.ExprSigSet.to_list min_size_exprs in
        let cur_t = BatList.fold_left (fun (last_size, result_rev) (cur_size, cur_exprs) ->
                    let result_rev' =
                        if last_size + 1 < cur_size then
                            BatList.init (cur_size - last_size - 1) (fun _ -> []) @ result_rev
                        else result_rev
                    in
                    (cur_size, Exprs.ExprSigSet.to_list cur_exprs :: result_rev')
                ) (min_size, []) others |> snd |> BatList.rev
        in
        let initial_count = Exprs.ExprSigSet.cardinal exprs in
        {size_upper_bound = max_size;
        cur_comp_size = min_size;
        initial_count = initial_count;
        iter_type = IterSelectedSet;
        count = initial_count;
        cur_h = cur_h;
        cur_t = cur_t;
        }

let rec next (t: t): Exprs.expr * Exprs.signature * int = 
    let next_comp_size (t: t): unit =
        match t.cur_t with
        | [] -> raise No_more_elements
        | head :: tail -> begin
            t.cur_h <- head;
            t.cur_t <- tail;
            t.cur_comp_size <- t.cur_comp_size + 1;
        end
    in
    if t.cur_comp_size > t.size_upper_bound then
        (* greater than upper bound => end of enum *)
        raise No_more_elements
    else 
    match t.cur_h with
    | [] -> begin (* end of current size => go to next size *)
        next_comp_size t;
        next t
    end
    | expr :: tail -> begin
        t.cur_h <- tail;
        t.count <- t.count - 1;
        (fst expr, snd expr, t.cur_comp_size)
    end

let iter f t =
    let rec loop () =
        f (next t);
        loop()
    in
    try loop()
    with No_more_elements -> ()

let count (t: t): int = t.count

let initial_count (t: t): int = t.initial_count

let iter_type (t: t): iter_type = t.iter_type

let clone ?(iter_type: iter_type option = None) (t: t): t = {
    size_upper_bound = t.size_upper_bound;
    cur_comp_size = t.cur_comp_size;
    initial_count = t.initial_count;
    iter_type = BatOption.default t.iter_type iter_type;
    count = t.count;
    cur_h = t.cur_h;
    cur_t = t.cur_t;
}

let clone_ranged ?(iter_type: iter_type option = None) (lb: int) (ub: int) (t: t): t =
    if t.cur_comp_size < lb then (* quick skip *)
        match BatList.drop (lb - t.cur_comp_size) (t.cur_h :: t.cur_t) with
        | [] -> empty()
        | new_h :: new_t ->
            let new_ub = min ub t.size_upper_bound in
            let initial_count = BatList.fold_lefti (fun sum size_idx sub_list ->
                    if size_idx > new_ub then sum
                    else sum + BatList.length sub_list
                ) (BatList.length new_h) new_t
            in
            {
                size_upper_bound = new_ub;
                cur_comp_size = lb;
                initial_count = initial_count;
                iter_type = BatOption.default t.iter_type iter_type;
                count = initial_count;
                cur_h = new_h;
                cur_t = new_t;
            }
    else
        let ub = min ub t.size_upper_bound in
        if t.cur_comp_size > ub then empty()
        else
            let initial_count = BatList.fold_lefti (fun sum size_idx sub_list ->
                    if size_idx > ub then sum
                    else sum + BatList.length sub_list
                ) (BatList.length t.cur_h) t.cur_t
            in
            {
                size_upper_bound = ub;
                cur_comp_size = t.cur_comp_size;
                initial_count = initial_count;
                iter_type = BatOption.default t.iter_type iter_type;
                count = initial_count;
                cur_h = t.cur_h;
                cur_t = t.cur_t;
            }