open Vocab

let ($&&$) b1 b2 = Int64.logand b1 b2
let ($||$) b1 b2 = Int64.logor b1 b2
let ($^^$) b1 b2 = Int64.logxor b1 b2
let (%>>%) b i = Int64.shift_right b i
let (%>>>%) b i = Int64.shift_right_logical b i
let (%<<%) b i = Int64.shift_left b i
let (~~) i = Int64.lognot i

(** ???10000 -> 11110000 *)
let postzeros (x: int64): int64 =
    ((x $^^$ Int64.succ (~~x)) %>>% 1) $||$ x

(** bit test for i[idx] (idx is zero-based, count from lsb ) *)
let is_bit_set (i: int64) (idx: int): bool =
    if idx < 0 || idx > 63 then
        invalid_arg ("Int64Util.is_bit_set: invalid idx " ^ string_of_int idx)
    else
        0L <> (i $&&$ (1L %<<% idx))

let mask_by_bit_length (bit_length: int) (i: int64): int64 =
    (Int64.minus_one %>>>% (64 - bit_length)) $&&$ i

(* calculate mult inverse of a modulo m *)
let mult_inverse_ext_euclidean (a: int64) (m: int64): int64 =
    let rec aux (a: int64) (m: int64) (x: int64) (y: int64): int64 =
        if Int64.unsigned_compare a 1L <= 0 then
            x
        else
            let q = Int64.unsigned_div a m in
            let m' = Int64.sub a (Int64.mul q m) in
            let y' = Int64.sub x (Int64.mul q y) in
            aux m m' y y'
    in
    let s_inv = aux a m 1L 0L in
    if Int64.compare s_inv 0L < 0 then
        Int64.add s_inv m
    else
        s_inv

(* speical extension of Int64.unsigned_div: (unsigned) 2^64 / d  *)
let unsigned_div_2pow64 d =
    if d = Int64.min_int then
        2L
    else if d < 0L then
        1L
    else
        let q = Int64.shift_left (Int64.unsigned_div Int64.min_int d) 1 in
        let r = Int64.sub 0L (Int64.mul q d) in
        if Int64.unsigned_compare r d >= 0 then Int64.succ q else q

(* special extension of mult_inverse a modulo 2^64 *)
let mult_inverse_int64 (a: int64): int64 =
    let rec aux (a: int64) (m: int64) (x: int64) (y: int64): int64 =
        if Int64.unsigned_compare a 1L <= 0 then
            x
        else
            let q = Int64.unsigned_div a m in
            let m' = Int64.sub a (Int64.mul q m) in
            let y' = Int64.sub x (Int64.mul q y) in
            aux m m' y y'
    in
    let first_q = unsigned_div_2pow64 a in
    let first_m = Int64.neg (Int64.mul first_q a) in
    let first_y = Int64.neg first_q in
    aux a first_m 1L first_y

let sqrt_through_float (a: int64): int64 =
    Int64.of_float (Float.sqrt (Int64.to_float a))

let usqrt_through_bits (a: int64): int64 =
    let guess_max =
        let general = Int64.sub (Int64.shift_left 1L 32) 1L in
        let from_a = a %>>>% 1 in
        if Int64.unsigned_compare from_a general < 0 then from_a else general
    in
    let rec aux (guess_lb: int64) (guess_ub: int64) (cnt: int): int64 =
        if cnt > 200 then begin
            Printf.fprintf stderr "oscilation? input=%LX / lb=%LX / ub=%LX\n" a guess_lb guess_ub
        end;
        if cnt > 210 then begin
            exit(-1)
        end;
        if guess_lb = guess_ub then guess_lb
        else
            let guess = (Int64.add guess_lb guess_ub) %>>>% 1 in
            let g1 = Int64.succ guess in
            let guess_sq = Int64.mul guess guess in
            let guess1_sq = Int64.mul g1 g1 in
            if Int64.unsigned_compare guess_sq a <= 0 then
                if Int64.unsigned_compare guess1_sq a > 0 then
                    guess
                else if guess1_sq = a then
                    g1
                else if guess = guess_lb then
                    aux (Int64.succ guess) guess_ub (succ cnt)
            else
                aux guess guess_ub (succ cnt)
            else if guess = guess_ub then
                guess
            else aux guess_lb guess (succ cnt)
    in
    aux 1L guess_max 0

let known_primes_cache = ref [97L;89L;83L;79L;73L;71L;67L;61L;59L;53L;47L;43L;41L;37L;31L;29L;23L;19L;17L;13L;11L;7L;5L;3L;2L]

let find_next_prime(): int64 =
    let last_known = BatList.hd !known_primes_cache in
    let incr_order = BatList.rev !known_primes_cache in
    let rec aux (trial: int64): int64 =
        if BatList.for_all (fun x -> Int64.unsigned_rem trial x <> 0L) incr_order then begin
            known_primes_cache := trial :: !known_primes_cache;
            trial
        end else
            aux (Int64.add trial 2L)
    in
    aux (Int64.add last_known 2L)

let maximum_proper_udivisor (a: int64): int64 option =
    let limit = usqrt_through_bits a in
    let incr_order_known_primes = BatList.rev !known_primes_cache in
    let rec aux (remain_known_primes: int64 list): int64 option =
        match remain_known_primes with
        | [] ->
            let prime_candidate = find_next_prime() in
            if prime_candidate > limit then
                None
            else if Int64.unsigned_rem a prime_candidate = 0L then
                Some (Int64.unsigned_div a prime_candidate) (* found! *)
            else
                aux []
        | prime_candidate :: tail ->
            if prime_candidate > limit then
                None
            else if Int64.unsigned_rem a prime_candidate = 0L then
                Some (Int64.unsigned_div a prime_candidate) (* found! *)
            else
                aux tail
    in
    aux incr_order_known_primes

let approx_maximum_proper_udivisor (a: int64): int64 =
    if a = 0L then 0L
    else
        let limit = 1024L in
        let incr_order_known_primes = BatList.rev !known_primes_cache in
        let rec aux (remain_known_primes: int64 list): int64 =
            match remain_known_primes with
            | [] ->
                let prime_candidate = find_next_prime() in
                if Int64.unsigned_rem a prime_candidate = 0L then
                    Int64.unsigned_div a prime_candidate (* found! *)
                else if prime_candidate > limit then
                    (* just use current result ('real' maximum proper divisor will be smaller than this) *)
                    Int64.unsigned_div a prime_candidate
                else
                    aux []
            | prime_candidate :: tail ->
                if Int64.unsigned_rem a prime_candidate = 0L then
                    Int64.unsigned_div a prime_candidate (* found! *)
                else if prime_candidate > limit then
                    (* just use current result ('real' maximum proper divisor will be smaller than this) *)
                    Int64.unsigned_div a prime_candidate
                else
                    aux tail
        in
        aux incr_order_known_primes

let int64_to_string_in_binary (bv: int64): string =
    let bv_bigint =
        if (Int64.compare bv 0L) < 0 then 
            BatBig_int.add (BatBig_int.shift_left_big_int (BatBig_int.one) 63) (BatBig_int.big_int_of_int64 bv)	
        else (BatBig_int.big_int_of_int64 bv)
    in
    let str = BatBig_int.to_string_in_binary bv_bigint in 
    try 
        (BatString.make (63 - (String.length str)) '0') ^ str
    with _ ->
        failwith (Printf.sprintf "%s %s" (Int64.to_string bv) str )  	 

module type BitVecSize = sig
    val size: int
end

module type MaskedInt64Type = sig
    val bit_length: int

    val minus_one: int64

    val mask: int64

    val signed_min_int: int64

    val signed_max_int: int64

    val msb_marker: int64

    val extend_msb: int64 -> int64

    val apply_mask: int64 -> int64

    val signed_compare: int64 -> int64 -> int
    
    val unsigned_compare: int64 -> int64 -> int

    val signed_min: int64 -> int64 -> int64
    
    val signed_max: int64 -> int64 -> int64
    
    val unsigned_min: int64 -> int64 -> int64
    
    val unsigned_max: int64 -> int64 -> int64
    
    val unsigned_to_int: int64 -> int option

    val lognot: int64 -> int64
    val logand: int64 -> int64 -> int64
    val logor: int64 -> int64 -> int64
    val logxor: int64 -> int64 -> int64

    val neg: int64 -> int64
    val abs: int64 -> int64
    val add: int64 -> int64 -> int64
    val sub: int64 -> int64 -> int64
    val mul: int64 -> int64 -> int64
    val signed_div: int64 -> int64 -> int64
    val unsigned_div: int64 -> int64 -> int64
    val signed_rem: int64 -> int64 -> int64
    val unsigned_rem: int64 -> int64 -> int64
    val arith_shift_right: int64 -> int -> int64
    val logical_shift_right: int64 -> int -> int64
    val shift_left: int64 -> int -> int64
end

module MaskedInt64(S: BitVecSize) = struct
    let bit_length: int = begin
        assert (1 <= S.size && S.size <= 64);
        S.size
    end

    let minus_one: int64 = Int64.minus_one %>>>% (64 - bit_length)

    let mask: int64 = minus_one

    let signed_min_int: int64 = 1L %<<% (bit_length - 1)

    let signed_max_int: int64 = Int64.minus_one %>>>% (64 - bit_length + 1)

    let msb_marker: int64 = 1L %<<% (bit_length - 1)

    (** when S is msb in 0000Sxxxx, 0000Sxxxx => SSSSSxxxx *)
    let extend_msb (i: int64): int64 =
        (*
        extended_msb =
            if msb is 1, 00010000 => 00001111 => 11110000
            if msb is 0, 00000000 => 11111111 => 00000000
        extended_msb_of_i || i
         *)
        (~~(Int64.sub (i $&&$ msb_marker) 1L) $||$ i)

    let apply_mask (i: int64): int64 = i $&&$ mask

    let wrap_unary (f: int64 -> int64): int64 -> int64 = fun i ->
        apply_mask (f (extend_msb i))

    let wrap_binary (f: int64 -> int64 -> int64): int64 -> int64 -> int64 = fun i1 i2 ->
        apply_mask (f (extend_msb i1) (extend_msb i2))

    let signed_compare (i1: int64) (i2: int64): int =
        Int64.compare (extend_msb i1) (extend_msb i2)

    let unsigned_compare (i1: int64) (i2: int64): int = Int64.unsigned_compare i1 i2

    let signed_min (i1: int64) (i2: int64): int64 =
        if signed_compare i1 i2 < 0 then i1 else i2

    let signed_max (i1: int64) (i2: int64): int64 =
        if signed_compare i1 i2 < 0 then i2 else i1

    let unsigned_min (i1: int64) (i2: int64): int64 =
        if unsigned_compare i1 i2 < 0 then i1 else i2

    let unsigned_max (i1: int64) (i2: int64): int64 =
        if unsigned_compare i1 i2 < 0 then i2 else i1

    let unsigned_to_int (i: int64): int option =
        Int64.unsigned_to_int i

    let lognot: int64 -> int64 = fun i -> Int64.lognot i |> apply_mask
    let logand: int64 -> int64 -> int64 = fun i1 i2 -> Int64.logand i1 i2 |> apply_mask
    let logor: int64 -> int64 -> int64 = fun i1 i2 -> Int64.logor i1 i2 |> apply_mask
    let logxor: int64 -> int64 -> int64 = fun i1 i2 -> Int64.logxor i1 i2 |> apply_mask

    let neg: int64 -> int64 = wrap_unary Int64.neg
    let abs: int64 -> int64 = wrap_unary Int64.abs
    let add: int64 -> int64 -> int64 = wrap_binary Int64.add
    let sub: int64 -> int64 -> int64 = wrap_binary Int64.sub
    let mul: int64 -> int64 -> int64 = wrap_binary Int64.mul
    let arith_shift_right: int64 -> int -> int64 = fun i c -> apply_mask (Int64.shift_right (extend_msb i) c)
    let logical_shift_right: int64 -> int -> int64 = Int64.shift_right_logical (* no need msb extension *)
    let shift_left: int64 -> int -> int64 = fun i c -> apply_mask (Int64.shift_left i c) (* no need msb extension *)
    let signed_div: int64 -> int64 -> int64 = wrap_binary Int64.div
    let signed_rem: int64 -> int64 -> int64 = wrap_binary Int64.rem
    let unsigned_rem: int64 -> int64 -> int64 = Int64.unsigned_rem (* no need msb extension *)
    let unsigned_div: int64 -> int64 -> int64 = fun n d -> (* special implementation *)
        (* copied from Int64 *)
        if signed_compare d 0L < 0 then
            if unsigned_compare n d < 0 then 0L else 1L
        else
            let q = shift_left (signed_div (logical_shift_right n 1) d) 1 in
            let r = sub n (mul q d) in
            if unsigned_compare r d >= 0 then add q 1L else q
end
