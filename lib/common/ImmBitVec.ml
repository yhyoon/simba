open Vocab

(** represents fixed-width immutable bit vector *)

type t = {
    bits_width: int;
    bits: int array;
}

let create_full_bits (width: int): int array =
    let arr_length = (width - 1) / Sys.int_size + 1 in
    BatArray.init arr_length (fun idx ->
        if idx < arr_length - 1 then
            (-1)
        else
            let last_word_length = width mod Sys.int_size in
            if last_word_length = 0 then (* full *)
                (-1)
            else
                (-1) lsr (Sys.int_size - last_word_length)
    )

let create_empty_bits (width: int): int array =
    let arr_length = (width - 1) / Sys.int_size + 1 in
    BatArray.make arr_length 0

(* index_in_array = index / Sys.int_size *)
(* index_in_word_from_low = index mod Sys.int_size *)

let internal_mem (index: int) (bits_width: int) (bits: int array): bool =
    if index < 0 || index >= bits_width then
        failwith_f "ImmBitVec.mem out of index %d" index
    else
        let v = bits.(index / Sys.int_size) in
        (1 lsl (index mod Sys.int_size)) land v <> 0

let mem (index: int) (t: t): bool =
    internal_mem index t.bits_width t.bits

let internal_set (index: int) (bits_width: int) (bits: int array): unit =
    if index < 0 || index >= bits_width then
        failwith_f "ImmBitVec.set out of index %d" index
    else
        let arr_index = index / Sys.int_size in
        let v = bits.(arr_index) in
        bits.(arr_index) <- ((1 lsl (index mod Sys.int_size)) lor v)

let foldi (f: int -> bool -> 'a -> 'a) (t: t) (z: 'a): 'a =
    let result = ref z in
    let array_cursor = ref 0 in
    let index = ref 0 in
    while !array_cursor < BatArray.length t.bits do
        let elem = t.bits.(!array_cursor) in
        let in_elem_index = ref 0 in
        while !index < t.bits_width && !in_elem_index < Sys.int_size do
            let b = (1 lsl !in_elem_index) land elem <> 0 in
            result := f !index  b !result;
            incr in_elem_index;
            incr index;
        done;
        incr array_cursor
    done;
    !result

(* internal *)
let count_8bit_array: int array =
    let rec count_bits i =
        if i = 0 then
            0
        else
            count_bits (i lsr 1) + (i land 1)
    in
    Array.init 256 count_bits

(* internal *)
let rec count_bit (accum: int) (v: int): int =
    if v = 0 then accum
    else
        count_bit (count_8bit_array.(v land 255) + accum) (v lsr 8)

let count_internal (bits_width: int) (bits: int array): int =
    BatArray.fold_left count_bit 0 bits

let count (t: t): int =
    BatArray.fold_left count_bit 0 t.bits

let is_empty_internal (bits_width: int) (bits: int array): bool =
    BatArray.for_all (Int.equal 0) bits

let is_empty (t: t): bool =
    is_empty_internal t.bits_width t.bits

let compare (t1: t) (t2: t): int =
    let c1 = Int.compare t1.bits_width t2.bits_width in
    if c1 <> 0 then c1
    else
        BatArray.compare Int.compare t1.bits t2.bits

let equal (t1: t) (t2: t): bool =
    t1.bits_width = t2.bits_width && BatArray.equal Int.equal t1.bits t2.bits

let valid (bits_width: int) (bits: int array): bool =
    if (bits_width - 1) / Sys.int_size + 1 = BatArray.length bits then
        let last_elem = bits.(BatArray.length bits - 1) in
        let last_valid_range = bits_width mod Sys.int_size in
        if last_valid_range = 0 then (* full *)
            true
        else
            (lnot ((-1) lsr (Sys.int_size - last_valid_range))) land last_elem = 0
    else
        false

let internal_lognot (bits_width: int) (bits: int array): int array =
    let arr_len = BatArray.length bits in
    assert (valid bits_width bits);
    BatArray.init arr_len (fun idx ->
            if idx < arr_len - 1 then
                lnot bits.(idx)
            else
                let valid = bits_width mod Sys.int_size in
                if valid = 0 then (* full *)
                    lnot bits.(idx)
                else
                    (lnot bits.(idx)) land ((-1) lsr (Sys.int_size - valid))
        )

let internal_logand (bits_width: int) (bits1: int array) (bits2: int array): int array =
    assert (valid bits_width bits1);
    assert (valid bits_width bits2);
    BatArray.init (BatArray.length bits1) (fun idx ->
            bits1.(idx) land bits2.(idx)
        )

let internal_logor (bits_width: int) (bits1: int array) (bits2: int array): int array =
    assert (valid bits_width bits1);
    assert (valid bits_width bits2);
    BatArray.init (BatArray.length bits1) (fun idx ->
            bits1.(idx) lor bits2.(idx)
        )

let internal_logxor (bits_width: int) (bits1: int array) (bits2: int array): int array =
    assert (valid bits_width bits1);
    assert (valid bits_width bits2);
    BatArray.init (BatArray.length bits1) (fun idx ->
            bits1.(idx) lxor bits2.(idx)
        )

let internal_diff (bits_width: int) (bits1: int array) (bits2: int array): int array =
    assert (valid bits_width bits1);
    assert (valid bits_width bits2);
    BatArray.init (BatArray.length bits1) (fun idx ->
            bits1.(idx) land (lnot bits2.(idx))
        )

let lognot (t: t): t =
    {t with bits = internal_lognot t.bits_width t.bits}

(* inter *)
let logand (t1: t) (t2: t): t =
    assert (t1.bits_width = t2.bits_width);
    {t1 with bits = internal_logand t1.bits_width t1.bits t2.bits}

(* union *)
let logor (t1: t) (t2: t): t =
    assert (t1.bits_width = t2.bits_width);
    {t1 with bits = internal_logor t1.bits_width t1.bits t2.bits}

(* sym_diff *)
let logxor (t1: t) (t2: t): t =
    assert (t1.bits_width = t2.bits_width);
    {t1 with bits = internal_logxor t1.bits_width t1.bits t2.bits}

let diff (t1: t) (t2: t): t =
    assert (t1.bits_width = t2.bits_width);
    {t1 with bits = internal_diff t1.bits_width t1.bits t2.bits}

let full_set_cache: t BatDynArray.t = BatDynArray.init 3 (fun len -> {bits_width = len; bits = create_full_bits len})
let empty_set_cache: t BatDynArray.t = BatDynArray.init 3 (fun len -> {bits_width = len; bits = create_empty_bits len})

let ensure_full_set_cache (required: int): unit =
    if required >= BatDynArray.length full_set_cache then begin
        BatList.range (BatDynArray.length full_set_cache) `To required |>
            BatList.iter (fun len ->
                BatDynArray.add full_set_cache ({bits_width = len; bits = create_full_bits len})
            )
    end

let ensure_empty_set_cache (required: int): unit =
    if required >= BatDynArray.length empty_set_cache then begin
        BatList.range (BatDynArray.length empty_set_cache) `To required |>
            BatList.iter (fun len ->
                BatDynArray.add empty_set_cache ({bits_width = len; bits = create_empty_bits len})
            )
    end

let full_set (len: int): t = begin
    ensure_full_set_cache len;
    BatDynArray.get full_set_cache len
end

let empty_set (len: int): t = begin
    ensure_empty_set_cache len;
    BatDynArray.get empty_set_cache len
end

let length (t: t): int = t.bits_width

let map_as_list (f: int -> bool -> 'a) (t: t): 'a list =
    foldi (fun i b acc_rev -> f i b :: acc_rev) t [] |> BatList.rev

let to_list (t: t): bool list =
    map_as_list (fun _ b -> b) t

let of_list (bl: bool list): t =
    let width = BatList.length bl in
    let arr =
        let lref = ref bl in
        let arr_length = (width - 1) / Sys.int_size + 1 in
        let rec build_prepared_list idx result =
            if idx < arr_length then begin
                let v = ref 0 in
                let cnt_in_elem = ref 0 in
                begin try
                    while !cnt_in_elem < Sys.int_size do
                        begin match !lref with
                        | true :: tail ->
                            v := !v lor (1 lsl !cnt_in_elem);
                            lref := tail;
                        | false :: tail ->
                            lref := tail;
                        | [] ->
                            raise Exit
                        end;
                        incr cnt_in_elem
                    done;
                with Exit ->
                    ()
                end;
                build_prepared_list (succ idx) (!v :: result)
            end
            else
                result |> BatList.rev
        in
        let prepared_list = build_prepared_list 0 [] in
        BatArray.of_list prepared_list
    in
    {
        bits_width = width;
        bits = arr;
    }

(* lower index at tail *)
let to_string (t: t): string =
    map_as_list (fun idx b ->
        let sep_spot = idx > 0 && idx mod Sys.int_size = 0 in
        if b && sep_spot then
            "1 "
        else if b then
            "1"
        else if sep_spot then
            "0 "
        else
            "0"
    ) t
    |> BatList.rev
    |> string_of_list ~first:"b" ~last:"" ~sep:"" identity
