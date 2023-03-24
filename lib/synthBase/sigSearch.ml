open Common
open Vocab
open SynthLang.Exprs

type node_key = int * const

let string_of_node_key ((idx,c): node_key): string = "(" ^ string_of_const c  ^ "," ^ string_of_int idx ^ ")"

type node_val = {
    mutable exprs: ExprSigSet.t
}

type bool_table = {
    true_subsig_set: BatBitSet.t array;
    false_subsig_set: BatBitSet.t array;
    subsig_expr_set: ExprSigSet.t option array;
}

type sized_table = {
    index_const_exprs: (const, node_val) BatMap.t array;
    index_sorted_consts: const array option array; (* index |-> sorted key list of index_const_exprs.(index), sort by unsigned order *)
    bool_table: bool_table array; (* byte_index |-> byte_info *)
}

type t = {
    io_pair_count: int;
    mutable tables: sized_table array; (* expr_size |-> (index |-> const |-> exprs set) | (byte_index |-> byte_info) *)
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

let create_bool_table(): bool_table = {
    true_subsig_set = BatArray.init 8 (fun _ -> BatBitSet.create 256);
    false_subsig_set = BatArray.init 8 (fun _ -> BatBitSet.create 256);
    subsig_expr_set = BatArray.make 256 (Some ExprSigSet.empty);
}

let create_sized_table(io_pair_count: int): sized_table = {
    index_const_exprs = BatArray.make io_pair_count BatMap.empty;
    index_sorted_consts = BatArray.make io_pair_count None;
    bool_table = BatArray.init (bit_width_to_bt_size io_pair_count) (fun _ -> create_bool_table());
}

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
    if expr_size >= BatArray.length t.tables then begin
        t.tables <- BatArray.init (expr_size + 1) (fun idx ->
            if idx < BatArray.length t.tables then
                t.tables.(idx)
            else
                create_sized_table t.io_pair_count
        )
    end;
    t.tables.(expr_size)

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
                                Logger.g_info_f "exprs: %s" (ExprSigSet.to_string node.exprs);
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

let find_node ((idx,c): node_key) (sized_table: sized_table): node_val =
    if idx < BatArray.length sized_table.index_const_exprs then BatMap.find c sized_table.index_const_exprs.(idx)
    else failwith_f "idx %d in node_key is over %d" idx (BatArray.length sized_table.index_const_exprs)

let add_node ((idx,c): node_key) (node_val: node_val) (sized_table: sized_table): unit =
    sized_table.index_const_exprs.(idx) <- BatMap.add c node_val sized_table.index_const_exprs.(idx)

let create_empty(io_pair_count: int): t = {
    io_pair_count = io_pair_count;
    tables = BatArray.init 2 (fun _ -> create_sized_table io_pair_count);
}

let key_of_sig (signature: signature): node_key list =
    const_list_of_signature signature |> zip_with_index

let add (full_sig: signature) (expr: expr) (signature: signature) (expr_size: int) (t: t): unit =
    let start_time = Unix.gettimeofday() in
    let sized_table = get_sized_table expr_size t in
    (match full_sig with
    | SigBool bl ->
        let arr_len = BatArray.length bl.bits in
        let rec handle_bits ?(bit_idx: int = 0) (bt: bool_table) (byte: int): unit =
            if bit_idx < 8 then begin
                let _ =
                    if byte land (1 lsl bit_idx) <> 0 then
                        BatBitSet.set bt.true_subsig_set.(bit_idx) byte
                    else
                        BatBitSet.set bt.false_subsig_set.(bit_idx) byte
                in
                handle_bits ~bit_idx:(bit_idx + 1) bt byte;
            end
            else ()
        in
        let rec handle_byte (byte_idx: int) (remain_byte_cnt: int) (v: int): int =
            if remain_byte_cnt > 0 then begin
                let byte = v land 255 in
                let _ = handle_bits sized_table.bool_table.(byte_idx) byte in (* register byte to bit field *)
                let _ =
                    if byte_idx >= BatArray.length sized_table.bool_table then failwith_f "bool_table.(%d) out of bound %d" byte_idx (BatArray.length sized_table.bool_table);
                    if byte >= BatArray.length (sized_table.bool_table.(byte_idx).subsig_expr_set) then failwith_f "sized_table.bool_table.(%d).subsig_expr_set.(%d) out of bound %d" byte_idx byte (BatArray.length (sized_table.bool_table.(byte_idx).subsig_expr_set));
                    match sized_table.bool_table.(byte_idx).subsig_expr_set.(byte) with
                    | Some set -> begin
                        (* add expr to actual expr set *)
                        (* Logger.g_info_f "add expr to bool_table.(%d).sub_table.(%d) = %s" byte_idx byte (string_of_set string_of_expr set); *)
                        sized_table.bool_table.(byte_idx).subsig_expr_set.(byte) <- Some(ExprSigSet.add (expr, signature) set);
                        (* Logger.g_info_f "after add: bool_table.(%d).sub_table.(%d) = %s" byte_idx byte (string_of_set string_of_expr (BatOption.get sized_table.bool_table.(byte_idx).subsig_expr_set.(byte))); *)
                    end
                    | None -> begin
                        Logger.g_info_f "ignore None set";
                        ()
                    end
                in
                handle_byte (byte_idx + 1) (remain_byte_cnt - 1) (v lsr 8)
            end
            else byte_idx
        in
        (* hack: this logic is exploitation of ImmBitVec internal data structure *)
        BatArray.fold_lefti (fun byte_idx word_idx v ->
                if word_idx < arr_len - 1 then (* use all bits in word *)
                    handle_byte byte_idx byte_count_in_word v
                else
                    (* last word *)
                    let last_word_bit_width = mod_from_one bl.bits_width Sys.int_size in
                    handle_byte byte_idx ((last_word_bit_width - 1) / 8 + 1) v
            ) 0 bl.bits |> ignore
    | _ ->
        BatList.iter (fun key ->
                try
                    let node = find_node key sized_table in
                    node.exprs <- ExprSigSet.add (expr, signature) node.exprs
                with Not_found ->
                    add_node key {exprs = ExprSigSet.singleton (expr, signature)} sized_table
            ) (key_of_sig full_sig)
    );
    let end_time = Unix.gettimeofday() in
    Global.add_search_tbl_build_time (end_time -. start_time) Global.t

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
            let first_s = (find_node first sized_table).exprs in
            BatList.fold_left (fun result k ->
                    if ExprSigSet.is_empty result then raise Not_found
                    else
                        let s = (find_node k sized_table).exprs in
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

let consts_matching_bv_partial_sig (t: t) (expr_size_range: int * int) (max_const_set_size: int) (d: Dom.AbstDom.AbstSig.t): (int * const BatSet.t) list =
    let abst_bv_opt =
        match d with
        | Dom.AbstDom.AbstSig.BitVec64 bvs ->
            Some (64, bvs)
        | Dom.AbstDom.AbstSig.BitVec32 bvs ->
            Some (32, bvs)
        | Dom.AbstDom.AbstSig.BitVecGeneral (bit_len, bvs) ->
            Some (bit_len, bvs)
        | _ -> None
    in
    match abst_bv_opt with
    | None ->
        []
    | Some (bit_len, pl) ->
        let module I = Int64Util.MaskedInt64(struct let size = bit_len end) in
        let module P = Dom.RedProd.Make(I) in    
        BatList.fold_lefti (fun acc_rev index_in_sig p ->
            begin match p with
            | Dom.SignedIntv.SIBot, _, _
            | _, Dom.UnsignedIntv.UIBot, _ ->
                (index_in_sig, BatSet.empty) :: acc_rev
            | _, _, b when P.B.is_bot b ->
                (index_in_sig, BatSet.empty) :: acc_rev
            | (Dom.SignedIntv.SIntv (s_lower, s_upper) as s), (Dom.UnsignedIntv.UIntv (u_lower, u_upper) as u), bits ->
                let u_intvs =
                    if s = P.S.top_repr then
                        [(u_lower, u_upper)]
                    else if I.signed_compare s_lower 0L < 0 && I.signed_compare s_upper 0L >= 0 then
                        [(u_lower, s_upper); (s_lower, u_upper)]
                    else
                        [(u_lower, u_upper)]
                in
                let _ = BatList.iter (fun (l,u) -> if I.unsigned_compare l u > 0 then failwith_f "for sigidx %d / %s, reversed interval found with %Ld %Ld" index_in_sig (P.to_string p) l u) u_intvs in
                let check_in_intv i = BatList.exists (fun (l,u) -> I.unsigned_compare l i <= 0 && I.unsigned_compare i u <= 0) u_intvs in
                let bits_gamma_size = P.B.gamma_result_size (P.B.get_top_indices bits) in
                try
                    let rec loop_expr_size (expr_size: int) (accum_loop: const BatSet.t): const BatSet.t =
                        if expr_size > snd expr_size_range then
                            accum_loop (* done *)
                        else
                            let enums = BatList.map (fun (l,u) ->
                                enum_existing_bv_consts_unsigned t expr_size index_in_sig bit_len l u
                                ) u_intvs
                            in
                            let intv_count = BatList.fold_left (fun acc e -> acc + BatEnum.count e) 0 enums in
                            let by_bits_opt =
                                match bits_gamma_size with
                                | Some x when x <= Int64.of_int (max_const_set_size lsl 2) -> begin
                                    match P.B.gamma_size_constraint (max_const_set_size lsl 2) bits with
                                    | Some set ->
                                        begin try
                                            Some (BatSet.fold (fun c accum_set_fold ->
                                                    match c with
                                                    | CBV (len, i) when len = bit_len && check_in_intv i ->
                                                        let next_set = BatSet.add c accum_set_fold in
                                                        if BatSet.cardinal next_set > max_const_set_size then
                                                            raise Not_found (* hack: early failure *)
                                                        else next_set
                                                    | _ -> accum_set_fold
                                                ) set accum_loop)
                                        with Not_found ->
                                            None
                                        end
                                    | None -> failwith_f ""
                                    end
                                | _ -> None
                            in
                            let next =
                                match by_bits_opt with
                                | Some succeeded ->
                                    succeeded
                                | None -> begin
                                    if intv_count < (max_const_set_size lsl 5) then
                                        BatList.fold_left (fun accum_enums_fold enum ->        
                                                BatEnum.fold (fun accum_enum_fold c ->
                                                        match c with
                                                        | CBV (len, i) when len = bit_len && P.B.leq (P.B.from_int64 i) bits ->
                                                            let next_set = BatSet.add c accum_enum_fold in
                                                            if BatSet.cardinal next_set > max_const_set_size then
                                                                raise Not_found (* hack: early failure *)
                                                            else next_set
                                                        | _ ->
                                                            accum_enum_fold
                                                    ) accum_enums_fold enum
                                            ) accum_loop enums
                                    else
                                        raise Not_found (* hack: early failure *)
                                end
                            in
                            loop_expr_size (expr_size + 1) next
                    in
                    let const_set = loop_expr_size (fst expr_size_range) BatSet.empty in
                    (index_in_sig, const_set) :: acc_rev
                with Not_found -> acc_rev
            end
        ) [] pl |> BatList.rev
