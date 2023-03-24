open Common
open Vocab

open SynthLang
open GrammarUtil

type rel_op =
    | BR_NE (* not equal *)
    | BR_ZO (* a is zero -> b is one (partial ne) *)
    | BR_OZ (* a is one -> b is zero (partial ne) *)
    | BR_OO (* a is one -> b is one (partial eq) *)
    | BR_ZZ (* a is zero -> b is zero (partial eq) *)

let (relay_next, relay_prev) =
    (* X r1 Y && Y r2 Z => X r_derived Z *)
    let l = [
        (BR_ZO, BR_OZ, BR_ZZ);
        (BR_OZ, BR_ZO, BR_OO);
        (BR_OO, BR_OZ, BR_OZ);
        (BR_ZO, BR_OO, BR_ZO);
        (BR_OO, BR_OO, BR_OO);
        (BR_OZ, BR_ZZ, BR_OZ);
        (BR_ZZ, BR_ZO, BR_ZO);
        (BR_ZZ, BR_ZZ, BR_ZZ);
        ]
    in
    BatList.fold_left (fun (fm, bm) (r1, r2, r_derived) ->
            let sub_fmap = BatMap.find_default BatMap.empty r1 fm in
            let sub_bmap = BatMap.find_default BatMap.empty r2 bm in
            (BatMap.add r1 (BatMap.add r2 r_derived sub_fmap) fm,
             BatMap.add r2 (BatMap.add r1 r_derived sub_bmap) bm)
        ) (BatMap.empty, BatMap.empty) l

exception Contradiction of string

module EquivGroup = struct
    type gid = (* group id *)
        | GR_ZERO
        | GR_ONE
        | GR_General of int (* starts from 2 *)

    let index_of_gid (gid: gid): int =
        match gid with
        | GR_ZERO -> 0
        | GR_ONE -> 1
        | GR_General id -> id

    let sort_gid (gid1: gid) (gid2: gid): gid * gid =
        if index_of_gid gid1 <= index_of_gid gid2 then
            (gid1, gid2)
        else
            (gid2, gid1)

    type t = {
        addr_gid: (addr, gid) BatMap.t; (* addr to group id *)
        gid_addr: addr BatSet.t array; (* group id to addr set *)
    }

    let empty: t = {
        addr_gid = BatMap.empty;
        gid_addr = BatArray.make 2 BatSet.empty; (* special group: const 0 and const 1 *)
    }

    let generate_gid (addr: addr) (t: t): gid * t =
        try
            (BatMap.find addr t.addr_gid, t)
        with Not_found ->
            let new_id = BatArray.length t.gid_addr in
            (GR_General new_id,
                {addr_gid = BatMap.add addr (GR_General new_id) t.addr_gid;
                gid_addr = arr_copy_add (BatSet.singleton addr) t.gid_addr;}
            )

    let assign_gid (addr: addr) (gid: gid) (t: t): t =
        let idx = index_of_gid gid in
        {addr_gid = BatMap.add addr gid t.addr_gid;
        gid_addr = arr_copy_set idx (BatSet.add addr (t.gid_addr.(idx))) t.gid_addr}
end

type t = {
    query_set: (EquivGroup.gid * EquivGroup.gid * rel_op) BatSet.t;
    equiv_set: EquivGroup.t;
    rel_map: (EquivGroup.gid, (EquivGroup.gid, rel_op) BatMap.t) BatMap.t;
    rel_rev_map: (EquivGroup.gid, (EquivGroup.gid, rel_op) BatMap.t) BatMap.t;
}

let empty: t = {
    query_set = BatSet.empty;
    equiv_set = EquivGroup.empty;
    rel_map = BatMap.empty;
    rel_rev_map = BatMap.empty;
}

(* internal logics *)
let remove_relation_by_gid (gid1: EquivGroup.gid) (gid2: EquivGroup.gid) (t: t): t =
    try
        let sub_map_f = BatMap.find gid1 t.rel_map in
        let sub_map_b = BatMap.find gid2 t.rel_rev_map in
        {t with
            rel_map = BatMap.add gid1 (BatMap.remove gid2 sub_map_f) t.rel_map;
            rel_rev_map = BatMap.add gid2 (BatMap.remove gid1 sub_map_b) t.rel_rev_map}
    with Not_found ->
        t

let append_query (q: EquivGroup.gid * EquivGroup.gid * rel_op) (t: t): t =
    {t with query_set = BatSet.add q t.query_set}

let append_queries (ql: (EquivGroup.gid * EquivGroup.gid * rel_op) BatSet.t) (t: t): t =
    {t with query_set = BatSet.union ql t.query_set}

let set_eq_gid (gid1: EquivGroup.gid) (gid2: EquivGroup.gid) (t: t): t =
    let alive_gid, dead_gid = EquivGroup.sort_gid gid1 gid2 in
    if alive_gid = dead_gid then
        t
    else if EquivGroup.index_of_gid alive_gid < 2 && EquivGroup.index_of_gid dead_gid < 2 then
        (* union zero and one => contra *)
        raise (Contradiction "zero equals one")
    else
        let updating_addrs = t.equiv_set.gid_addr.(EquivGroup.index_of_gid dead_gid) in

        let equiv_set' = {
            EquivGroup.addr_gid = BatSet.fold (fun updating_addr ->
                    BatMap.add updating_addr alive_gid
                ) updating_addrs t.equiv_set.addr_gid;
            EquivGroup.gid_addr =
                arr_copy_set
                    (EquivGroup.index_of_gid dead_gid)
                    BatSet.empty t.equiv_set.gid_addr |>
                arr_copy_set
                    (EquivGroup.index_of_gid alive_gid)
                    (BatSet.union updating_addrs (t.equiv_set.gid_addr.(EquivGroup.index_of_gid alive_gid)));
        }
        in

        let (cleared_map, cleared_rev_map, fw_bindings, bw_bindings) =
            let (m, fw_bindings) =
                try
                    let sub_map = BatMap.find dead_gid t.rel_map in
                    (BatMap.remove dead_gid t.rel_map, BatMap.foldi (fun k v l -> BatSet.add (alive_gid, k, v) l) sub_map BatSet.empty)
                with Not_found ->
                    (t.rel_map, BatSet.empty)
            in
            let (rm, bw_bindings) =
                try
                    let sub_map = BatMap.find dead_gid t.rel_rev_map in
                    (BatMap.remove dead_gid t.rel_rev_map, BatMap.foldi (fun k v l -> BatSet.add (k, alive_gid, v) l) sub_map BatSet.empty)
                with Not_found ->
                    (t.rel_rev_map, BatSet.empty)
            in
            let m' =
                BatSet.fold (fun (k, _, _) m -> BatMap.remove k m) bw_bindings m
            in
            let rm' =
                BatSet.fold (fun (_, k, _) m -> BatMap.remove k m) fw_bindings m
            in
            (m', rm', fw_bindings, bw_bindings)
        in
        append_queries (BatSet.union fw_bindings bw_bindings) {t with
            equiv_set = equiv_set';
            rel_map = cleared_map;
            rel_rev_map = cleared_rev_map}

let rec process_queries (g: t): t =
    if BatSet.is_empty g.query_set then
        g
    else
        let (gid1, gid2, r) as pick = BatSet.choose g.query_set in
        let tail = BatSet.remove pick g.query_set in
        let g = {g with query_set = tail} in
        let next =
            if gid1 = gid2 then
                (*
                 * eq + zo = 1 & 1
                 * eq + oz = 0 & 0
                 * eq + zz | oo = eq (ignore zz | oo)
                 * eq + ne = Contradiction
                 *)    
                match r with
                | BR_ZO ->
                    set_eq_gid gid1 EquivGroup.GR_ONE g
                | BR_OZ ->
                    set_eq_gid gid1 EquivGroup.GR_ZERO g
                | BR_OO | BR_ZZ ->
                    g
                | BR_NE ->
                    raise (Contradiction "neq & eq")
            else
                let sub_map = BatMap.find_default BatMap.empty gid1 g.rel_map in
                try
                    let existing_r = BatMap.find gid2 sub_map in
                    if existing_r = r then
                        g (* dup *)
                    else
                        let rset = BatSet.of_list [r; existing_r] in
                        if BatSet.mem BR_NE rset then
                            (*
                             * ne + oz | zo = ne (ignore oz | zo)
                             * ne + oo | zz = Contradiction
                             *)
                            if BatSet.mem BR_ZZ rset || BatSet.mem BR_OO rset then
                                raise (Contradiction "neq & (zz | oo)")
                            else (* if BatSet.mem BR_OZ rset || BatSet.mem BR_ZO rset then *)
                                if existing_r = BR_NE then (* ignore *)
                                    g
                                else
                                    (* replace with ne *)
                                    remove_relation_by_gid gid1 gid2 g |>
                                    append_query (gid1, gid2, BR_NE)
                        else if BatSet.equal rset (BatSet.of_list [BR_ZO; BR_OZ]) then
                            (* zo + oz = ne *)
                            remove_relation_by_gid gid1 gid2 g |>
                            append_query (gid1, gid2, BR_NE)
                        else if BatSet.mem BR_ZO rset then
                            if BatSet.mem BR_ZZ rset then
                                raise (Contradiction "zo & zz")
                            else (* if BatSet.mem BR_OO rset then *)
                                (* zo + oo = ?1 *)
                                set_eq_gid gid2 GR_ONE g
                        else if BatSet.mem BR_OZ rset then
                            if BatSet.mem BR_ZZ rset then
                                (* oz + zz = ?0 *)
                                set_eq_gid gid2 GR_ZERO g
                            else (* if BatSet.mem BR_OO rset then *)
                                raise (Contradiction "oz & oo")
                        else (* if oo + zz *)
                            set_eq_gid gid1 gid2 g
                with Not_found -> begin
                    let post_propagation (added_g: t): t =
                        let propag =
                            let prev_qs =
                                let relay_prev_submap =
                                    BatMap.find_default BatMap.empty r relay_prev
                                in
                                let prev_submap = BatMap.find_default BatMap.empty gid1 g.rel_rev_map in
                                BatMap.foldi (fun v existing_prev qs ->
                                        match BatMap.find_opt existing_prev relay_prev_submap with
                                        | None -> qs
                                        | Some relay -> BatSet.add (v, gid2, relay) qs
                                    ) prev_submap BatSet.empty
                            in
                            let relay_next_submap =
                                BatMap.find_default BatMap.empty r relay_next
                            in
                            let next_submap = BatMap.find_default BatMap.empty gid2 g.rel_map in
                            BatMap.foldi (fun v existing_next qs ->
                                    match BatMap.find_opt existing_next relay_next_submap with
                                    | None -> qs
                                    | Some relay -> BatSet.add (gid1, v, relay) qs
                                ) next_submap prev_qs
                        in
                        if r = BR_NE then
                            (* special case: X ne Y && Y ne Z => X eq Z (may introduce new equal) *)
                            let prev_ne = BatMap.find_default BatMap.empty gid1 g.rel_rev_map |> BatMap.filterv (fun v -> v = BR_NE) |> BatMap.keys in
                            let next_ne = BatMap.find_default BatMap.empty gid2 g.rel_map |> BatMap.filterv (fun v -> v = BR_NE) |> BatMap.keys in
                            let prev_ne_processed_g = BatEnum.fold (fun g p -> set_eq_gid p gid2 g) g prev_ne in
                            BatEnum.fold (fun g n -> set_eq_gid gid1 n g) prev_ne_processed_g next_ne
                        else
                            append_queries propag added_g
                    in
                    {g with
                        rel_map = BatMap.add gid1 (BatMap.add gid2 r (BatMap.find_default BatMap.empty gid1 g.rel_map)) g.rel_map;
                        rel_rev_map = BatMap.add gid2 (BatMap.add gid1 r (BatMap.find_default BatMap.empty gid2 g.rel_rev_map)) g.rel_rev_map;
                    } |> post_propagation
                end
        in
        process_queries next

let add_relation_gid (gid1: EquivGroup.gid) (r: rel_op) (gid2: EquivGroup.gid) (g: t): t =
    g |> append_query (gid1, gid2, r) |> process_queries

(* interfaces *)
let set_eq (addr1: addr) (addr2: addr) (g: t): t =
    let gid1opt = BatMap.find_opt addr1 g.equiv_set.addr_gid in
    let gid2opt = BatMap.find_opt addr2 g.equiv_set.addr_gid in
    match gid1opt, gid2opt with
    | None, None ->
        let eqset =
            let (gid1, eqset) = EquivGroup.generate_gid addr1 g.equiv_set in
            EquivGroup.assign_gid addr2 gid1 eqset
        in
        {g with equiv_set = eqset}
    | Some gid, None ->
        {g with equiv_set = EquivGroup.assign_gid addr2 gid g.equiv_set}
    | None, Some gid ->
        {g with equiv_set = EquivGroup.assign_gid addr1 gid g.equiv_set}
    | Some gid1, Some gid2 ->
        if gid1 = gid2 then
            g
        else
            set_eq_gid gid1 gid2 g |> process_queries

let set_relation (addr1: addr) (r: rel_op) (addr2: addr) (g: t): t =
    let gid1opt = BatMap.find_opt addr1 g.equiv_set.addr_gid in
    let gid2opt = BatMap.find_opt addr2 g.equiv_set.addr_gid in
    let (gid1, gid2, eqset) =
        match gid1opt, gid2opt with
        | None, None ->
            let (gid1, eqset) = EquivGroup.generate_gid addr1 g.equiv_set in
            let (gid2, eqset) = EquivGroup.generate_gid addr2 g.equiv_set in
            (gid1, gid2, eqset)
        | Some gid1, None ->
            let (gid2, eqset) = EquivGroup.generate_gid addr2 g.equiv_set in
            (gid1, gid2, eqset)
        | None, Some gid2 ->
            let (gid1, eqset) = EquivGroup.generate_gid addr1 g.equiv_set in
            (gid1, gid2, eqset)
        | Some gid1, Some gid2 ->
            (gid1, gid2, g.equiv_set)
        in
    {g with equiv_set = eqset} |> add_relation_gid gid1 r gid2

let is_zero (addr: addr) (g: t): bool =
    match BatMap.find_opt addr g.equiv_set.addr_gid with
    | Some GR_ZERO -> true
    | _ -> false

let is_one (addr: addr) (g: t): bool =
    match BatMap.find_opt addr g.equiv_set.addr_gid with
    | Some GR_ONE -> true
    | _ -> false

let is_updated (addr: addr) (prev_t: t) (next_t: t): bool =
    let gid1opt = BatMap.find_opt addr prev_t.equiv_set.addr_gid in
    let gid2opt = BatMap.find_opt addr next_t.equiv_set.addr_gid in
    match gid1opt, gid2opt with
    | None, None ->
        false
    | None, Some _ ->
        true
    | Some _, None ->
        failwith (Printf.sprintf "assert failure: addr %s lose it's equiv group id" (string_of_list string_of_int addr))
    | Some gid1, Some gid2 ->
        if gid1 <> gid2 then true
        else
            BatMap.find_opt gid1 prev_t.rel_map <> BatMap.find_opt gid1 next_t.rel_map ||
                BatMap.find_opt gid1 prev_t.rel_rev_map <> BatMap.find_opt gid1 next_t.rel_rev_map
