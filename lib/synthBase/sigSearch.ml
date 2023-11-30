open Common
open Vocab
open SynthLang.Exprs

type node_key = int * const

let string_of_node_key ((idx,c): node_key): string = "(" ^ string_of_const c  ^ "," ^ string_of_int idx ^ ")"

type bool_table = {
    true_subsig_set: BatBitSet.t array;
    false_subsig_set: BatBitSet.t array;
    subsig_expr_set: ExprSigSet.t option array;
}

let up_true_subsig_set (bt: bool_table) (f: BatBitSet.t array -> BatBitSet.t array): bool_table =
    {bt with true_subsig_set = f bt.true_subsig_set}

let up_false_subsig_set (bt: bool_table) (f: BatBitSet.t array -> BatBitSet.t array): bool_table =
    {bt with false_subsig_set = f bt.false_subsig_set}

let up_subsig_expr_set (bt: bool_table) (f: ExprSigSet.t option array -> ExprSigSet.t option array): bool_table =
    {bt with subsig_expr_set = f bt.subsig_expr_set}

let up_subsig_expr_set_byte (bt: bool_table) (byte: int) (f: ExprSigSet.t option -> ExprSigSet.t option): bool_table =
    up_subsig_expr_set bt (fun arr ->
            arr_copy_set byte (f arr.(byte)) arr
        )

(**
    holding information for same-sized exprs
    *)
type sized_table = {
    index_const_exprs: (const, ExprSigSet.t) BatMap.t array; (* index -> const -> expr set *)
    index_sorted_consts: const array option array; (* index |-> sorted key list of index_const_exprs.(index), sort by unsigned order *)
    bool_table: bool_table array; (* byte_index |-> byte_info *)
}

let up_index_const_exprs (st: sized_table) (f: (const, ExprSigSet.t) BatMap.t array -> (const, ExprSigSet.t) BatMap.t array): sized_table =
    {st with index_const_exprs = f st.index_const_exprs}

let up_index_const_exprs_idx (st: sized_table) ((idx, c): node_key) (f: ExprSigSet.t -> ExprSigSet.t): sized_table =
    up_index_const_exprs st (fun arr ->
        arr_copy_set
            idx
            (BatMap.update_stdlib c (function
                | None -> Some (f ExprSigSet.empty)
                | Some s -> Some (f s)
            ) (arr.(idx)))
            arr
    )

let up_index_sorted_consts (st: sized_table) (f: const array option array -> const array option array): sized_table =
    {st with index_sorted_consts = f st.index_sorted_consts}

let up_bool_table (st: sized_table) (f: bool_table array -> bool_table array): sized_table =
    {st with bool_table = f st.bool_table}

let up_bool_table_idx (st: sized_table) (idx: int) (f: bool_table -> bool_table): sized_table =
    up_bool_table st (fun arr ->
            arr_copy_set idx (f arr.(idx)) arr
        )

type t = {
    io_pair_count: int;
    tables: sized_table array; (* expr_size |-> (index |-> const |-> exprs set) | (byte_index |-> byte_info) *)
}

(* mod in range [1, b] instead of [0, b-1] *)
let mod_from_one a b =
    let m = a mod b in
    if m = 0 then b else m

let byte_count_in_word = (Sys.int_size - 1) / 8 + 1

(*
0: 0
1~8: 1
9~16: 2
...
~Sys.int_size: byte_count_in_word
Sys.int_size+1 ~ Sys.int_size+8: byte_count_in_word + 1
Sys.int_size+9 ~ Sys.int_size+16: byte_count_in_word + 2
...
*)
let bit_width_to_bt_size_cache: int array ref =
    BatArray.init Sys.int_size (fun bit_width ->
        if bit_width = 0 then
            0
        else
            ((bit_width - 1) / Sys.int_size * byte_count_in_word) + ((mod_from_one bit_width Sys.int_size) - 1) / 8 + 1
    ) |> ref

let bit_width_to_bt_size (bit_width: int): int =
    if bit_width >= BatArray.length (!bit_width_to_bt_size_cache) then begin
        (* extend *)
        bit_width_to_bt_size_cache := (BatArray.init (bit_width * 2) (fun bit_width ->
            if bit_width < BatArray.length !bit_width_to_bt_size_cache then
                (!bit_width_to_bt_size_cache).(bit_width)
            else
                ((bit_width - 1) / Sys.int_size * byte_count_in_word) + ((mod_from_one bit_width Sys.int_size) - 1) / 8 + 1
        ))
    end;
    (!bit_width_to_bt_size_cache).(bit_width)

let empty_bool_table: bool_table = {
    true_subsig_set = BatArray.init 8 (fun _ -> BatBitSet.create 256);
    false_subsig_set = BatArray.init 8 (fun _ -> BatBitSet.create 256);
    subsig_expr_set = BatArray.make 256 (Some ExprSigSet.empty);
}

let create_sized_table(io_pair_count: int): sized_table = {
    index_const_exprs = BatArray.make io_pair_count BatMap.empty;
    index_sorted_consts = BatArray.make io_pair_count None;
    bool_table = BatArray.make (bit_width_to_bt_size io_pair_count) empty_bool_table;
}

let up_tables (t: t) (f: sized_table array -> sized_table array): t =
    {t with tables = f t.tables}

let up_tables_idx (t: t) (size: int) (f: sized_table -> sized_table): t =
    up_tables t (fun arr ->
            arr_copy_update_extend size f (create_sized_table t.io_pair_count) arr
        )

let bit_set_fold (f: int -> 'a -> 'a) (set: BatBitSet.t) (z: 'a): 'a =
    let rec aux i z =
        match BatBitSet.next_set_bit set i with
        | Some x ->
            aux (x + 1) (f x z)
        | None -> z
    in
    aux 0 z

let bit_set_to_string (set: BatBitSet.t): string =
    (bit_set_fold (fun i l -> i :: l) set []) |> BatList.rev |> string_of_list ~first:"{" ~last:"}" ~sep:"," (bin_string_of_int ~min_length:8)

let get_sized_table (expr_size: int) (t: t): sized_table =
    if expr_size < BatArray.length t.tables then
        t.tables.(expr_size)
    else
        create_sized_table t.io_pair_count

let dump_table (t: t): unit =
    Logger.g_info_f "=== %d io pairs ===" t.io_pair_count;
    Logger.g_with_increased_depth (fun () ->
        BatArray.iteri (fun expr_size sized_tbl ->
            Logger.g_with_increased_depth (fun () ->
                if expr_size > 0 then begin
                    Logger.g_info_f "size of exprs %d" expr_size;
                    Logger.g_info_f "=== Non-bool table ===";
                    BatArray.iteri (fun idx m ->
                        BatMap.iter (fun const node ->
                            Logger.g_info_f "%s |->" (string_of_node_key (idx,const));
                            Logger.g_with_increased_depth (fun () ->
                                Logger.g_info_f "exprs: %s" (ExprSigSet.to_string node);
                            )
                        ) m
                    ) sized_tbl.index_const_exprs;
                    Logger.g_info_f "=== Bool table ===";
                    BatArray.iteri (fun idx bt ->
                        Logger.g_info_f "byte_idx %d |->" idx;
                        Logger.g_with_increased_depth (fun () ->
                            (BatList.range 0 `To 7) |> BatList.iter (fun x ->
                                let fs = (bit_set_to_string bt.false_subsig_set.(x)) in
                                let ts = (bit_set_to_string bt.true_subsig_set.(x)) in
                                if BatString.length fs > 2 then Logger.g_info_f "[%s0%s] |-> %s" (BatString.make (7-x) '*') (BatString.make x '*') fs;
                                if BatString.length ts > 2 then Logger.g_info_f "[%s1%s] |-> %s" (BatString.make (7-x) '*') (BatString.make x '*') ts;
                            );
                        );
                        BatArray.iteri (fun subsig eso ->
                            match eso with
                            | Some es ->
                                if ExprSigSet.is_empty es then ()
                                else Logger.g_info_f "subsig %s |-> %s" (bin_string_of_int ~min_length:8 subsig) (ExprSigSet.to_string es)
                            | None ->
                                Logger.g_info_f "subsig %s |-> TooBigSet" (bin_string_of_int ~min_length:8 subsig)
                        ) bt.subsig_expr_set
                    ) sized_tbl.bool_table
                end
            );
        ) t.tables
    )

let find_node ((idx,c): node_key) (sized_table: sized_table): ExprSigSet.t =
    if idx < BatArray.length sized_table.index_const_exprs then
        BatMap.find c sized_table.index_const_exprs.(idx)
    else
        failwith_f "idx %d in node_key is over %d" idx (BatArray.length sized_table.index_const_exprs)

let create_empty(io_pair_count: int): t = {
    io_pair_count = io_pair_count;
    tables = BatArray.init 2 (fun _ -> create_sized_table io_pair_count);
}

let key_of_sig (signature: signature): node_key list =
    const_list_of_signature signature |> zip_with_index

let add (full_sig: signature) (expr: expr) (signature: signature) (expr_size: int) (t: t): t =
    let start_time = Unix.gettimeofday() in
    let result =
        up_tables_idx t expr_size (fun sized_table ->
            match full_sig with
            | SigBool bl ->
                let arr_len = BatArray.length bl.bits in
                let rec handle_bits ?(bit_idx: int = 0) (bt: bool_table) (byte: int): bool_table =
                    if bit_idx < 8 then begin
                        let updater =
                            if byte land (1 lsl bit_idx) <> 0 then
                                up_true_subsig_set
                            else
                                up_false_subsig_set
                        in
                        let updated_bt =
                            updater bt (fun arr ->
                                    arr_copy_set bit_idx
                                        (BatBitSet.add byte arr.(bit_idx))
                                        arr
                                )
                        in
                        handle_bits ~bit_idx:(bit_idx + 1) updated_bt byte
                    end
                    else bt
                in
                let rec handle_byte ((st, byte_idx): sized_table * int) (remain_byte_cnt: int) (v: int): sized_table * int =
                    if remain_byte_cnt > 0 then begin
                        let byte = v land 255 in
                        let st_1 =
                            up_bool_table_idx st byte_idx (fun bt ->
                                    handle_bits bt byte
                                )
                        in
                        let st_2 =
                            let _ =
                                (* assertion *)
                                failcond_f
                                    (byte_idx >= BatArray.length st_1.bool_table)
                                    "bool_table.(%d) out of bound %d" byte_idx (BatArray.length st_1.bool_table);
                                failcond_f
                                    (byte >= BatArray.length (st_1.bool_table.(byte_idx).subsig_expr_set))
                                    "sized_table.bool_table.(%d).subsig_expr_set.(%d) out of bound %d"
                                        byte_idx
                                        byte
                                        (BatArray.length (st_1.bool_table.(byte_idx).subsig_expr_set))
                            in
                            (* add expr to actual expr set *)
                            (* Logger.g_info_f "add expr to bool_table.(%d).sub_table.(%d) = %s" byte_idx byte (string_of_set string_of_expr set); *)
                            up_bool_table_idx st_1 byte_idx (fun bt ->
                                    up_subsig_expr_set_byte bt byte (fun opt ->
                                        match opt with
                                        | Some set ->
                                            Some (ExprSigSet.add (expr, signature) set)
                                        | None ->
                                            opt
                                    ) 
                                )
                        in
                        handle_byte (st_2, byte_idx + 1) (remain_byte_cnt - 1) (v lsr 8)
                    end
                    else (st, byte_idx)
                in
                (* hack: this logic is exploitation of ImmBitVec internal data structure *)
                BatArray.fold_lefti (fun (st, byte_idx) word_idx v ->
                    if word_idx < arr_len - 1 then (* use all bits in word *)
                        handle_byte (st, byte_idx) byte_count_in_word v
                    else
                        (* last word *)
                        let last_word_bit_width = mod_from_one bl.bits_width Sys.int_size in
                        handle_byte (st, byte_idx) ((last_word_bit_width - 1) / 8 + 1) v
                ) (sized_table, 0) bl.bits |> fst
            | _ ->
                BatList.fold_left (fun sized_table key ->
                        up_index_const_exprs_idx sized_table
                            key
                            (ExprSigSet.add (expr, signature))
                    ) sized_table (key_of_sig full_sig)
        )
    in
    let _ = (* record time *)
        let end_time = Unix.gettimeofday() in
        Global.add_search_tbl_build_time (end_time -. start_time) Global.t
    in
    result

exception Too_big_set

let find_bool (partial_bits: (int * bool) list) (bt: bool_table array): ExprSigSet.t =
    let group_by_range_idx: (int, (int * bool) list) BatMap.t =
        BatList.fold_left (fun m (sig_idx, b) ->
            let range_idx = (sig_idx / Sys.int_size) * byte_count_in_word + (sig_idx mod Sys.int_size) / 8 in
            BatMap.add range_idx ((sig_idx, b) :: (BatMap.find_default [] range_idx m)) m
        ) BatMap.empty partial_bits
    in
    let sets_by_range_idx: ExprSigSet.t list =
        BatMap.foldi (fun range_idx pbs collected_sets ->
                let sub_sigs = BatList.map (fun (sig_idx, b) ->
                    let in_range_idx = (sig_idx mod Sys.int_size) mod 8 in
                        if range_idx >= BatArray.length bt then failwith_f "bt.(%d) out of range %d, sig_idx = %d" range_idx (BatArray.length bt) sig_idx;
                        if b then bt.(range_idx).true_subsig_set.(in_range_idx) else bt.(range_idx).false_subsig_set.(in_range_idx)
                    ) pbs
                in
                match sub_sigs with
                | [] -> failwith "unreachable in SigSearch.find_bool.sets_by_range_idx"
                | first :: tail -> begin
                    let reduced_subsigs =
                        let accum = BatBitSet.copy first in
                        BatList.iter (BatBitSet.intersect accum) tail;
                        accum
                    in
                    let set_of_range_idx =
                        bit_set_fold (fun i accum ->
                            match bt.(range_idx).subsig_expr_set.(i) with
                            | None -> raise Too_big_set
                            | Some x -> ExprSigSet.union accum x
                        ) reduced_subsigs ExprSigSet.empty
                    in
                    set_of_range_idx :: collected_sets
                end
            ) group_by_range_idx []
    in
    BatList.reduce ExprSigSet.inter sets_by_range_idx

let find (partial_sig: node_key list) (expr_size: int) (t: t): ExprSigSet.t =
    let sized_table = get_sized_table expr_size t in
    try
        match partial_sig with
        | [] -> raise Not_found
        | ((idx, CBool b) as first) :: tail ->
            (* use bool table *)
            let all_bool_partial_sig =
                BatList.map (function
                    | (idx, CBool b) -> (idx, b)
                    | (_, c) -> failwith_f "non-bool const %s after find_bool" (string_of_const c)
                ) partial_sig
            in
            find_bool all_bool_partial_sig (get_sized_table expr_size t).bool_table
        | first :: tail ->
            (* use general table *)
            let first_s = find_node first sized_table in
            BatList.fold_left (fun result k ->
                    if ExprSigSet.is_empty result then raise Not_found
                    else
                        let s = find_node k sized_table in
                        ExprSigSet.inter result s
                ) first_s tail
    with Not_found -> ExprSigSet.empty

let compare_const_for_sort (c1: const) (c2: const): int =
    match c1, c2 with
    | CInt i1, CInt i2 -> BatInt.compare i1 i2
    | CInt _, _ -> -1
    | _, CInt _ -> 1
    | CBV (len1, b1), CBV (len2, b2) ->
        let lc = BatInt.compare len1 len2 in
        if lc = 0 then
            BatInt64.unsigned_compare b1 b2
        else lc
    | CBV _, _ -> -1
    | _, CBV _ -> 1
    | CString s1, CString s2 -> BatString.compare s1 s2
    | CString _, _ -> -1
    | _, CString _ -> 1
    | CBool b1, CBool b2 ->
        BatBool.compare b1 b2

module ConstOrder = BatOrd.Ord (
    struct
        type t = const
        let compare = compare_const_for_sort
    end
)

let ready_const_array (t: t) (expr_size: int) (index_in_sig: int): const array =
    match t.tables.(expr_size).index_sorted_consts.(index_in_sig) with
        | None ->
            let created_array =
                BatMap.keys t.tables.(expr_size).index_const_exprs.(index_in_sig)
                |> BatArray.of_enum
            in
            BatArray.fast_sort compare_const_for_sort created_array;
            t.tables.(expr_size).index_sorted_consts.(index_in_sig) <- Some created_array;
            created_array
        | Some key_array -> key_array

let find_start_index_opt (key_array: const array) (bit_len: int) (i: int64): int option =
    match BatArray.bsearch ConstOrder.ord key_array (CBV(bit_len, i)) with
    | `All_bigger -> begin
        try
            Some (BatArray.findi (function
                | CBV (bit_len', _) when bit_len = bit_len' -> true
                | _ -> false
            ) key_array)
        with Not_found -> None
    end
    | `All_lower ->
        None
    | `At idx ->
        Some idx
    | `Empty ->
        None
    | `Just_after prev_idx ->
        Some (prev_idx + 1)

let find_last_index (key_array: const array) (bit_len: int) (i: int64) (start_index: int): int =
    match BatArray.bsearch ConstOrder.ord key_array (CBV(bit_len, i)) with
    | `All_bigger ->
        (* will be empty set *)
        start_index - 1
    | `All_lower -> begin
        let rec loop idx =
            if idx >= 0 then
                match key_array.(idx) with
                | CBV (bit_len', _) when bit_len = bit_len' ->
                    idx
                | _ ->
                    loop (idx - 1)
            else
                failwith_f "SigSearch.find_last_index: do not call with empty const range: All_lower, finding i = %Lx" i
        in
        loop (BatArray.length key_array - 1)
    end
    | `At idx ->
        idx
    | `Empty ->
        failwith_f "SigSearch.find_last_index: do not call with empty const range: Empty, finding i = %Lx" i
    | `Just_after prev_idx ->
        prev_idx

let enum_existing_bv_consts_unsigned (t: t) (expr_size: int) (index_in_sig: int) (bit_len: int) (lb: int64) (ub: int64): const BatEnum.t =
    let key_array = ready_const_array t expr_size index_in_sig in
    match find_start_index_opt key_array bit_len lb with
    | None ->
        BatEnum.empty ()
    | Some start_index ->
        let last_index = try find_last_index key_array bit_len ub start_index with (Failure msg) as exn ->
            Logger.g_error_f "find_start_index of %Lx is %d, find_last_index of %08Lx is failed with %s" lb start_index ub msg;
            raise exn
        in
        if last_index < start_index then
            BatEnum.empty ()
        else
            let counter = ref (last_index - start_index + 1) in
            let cursor = ref start_index in
            let make_next (cursor_ref: int ref) (counter_ref: int ref): unit -> const =
                fun () ->
                    if !cursor_ref > last_index then
                        raise BatEnum.No_more_elements;
                    let result = key_array.(!cursor_ref) in
                    incr cursor_ref;
                    decr counter_ref;
                    result
            in
            let make_count (cursor_ref: int ref) (counter_ref: int ref): unit -> int =
                fun () -> !counter_ref
            in
            let rec make (cursor_ref: int ref) (counter_ref: int ref): const BatEnum.t =
                BatEnum.make
                    ~next: (make_next cursor counter)
                    ~count: (make_count cursor counter)
                    ~clone: (fun () ->
                        let new_cursor = ref !cursor in
                        let new_counter = ref !counter in
                        make new_cursor new_counter
                    )
            in
            make cursor counter
