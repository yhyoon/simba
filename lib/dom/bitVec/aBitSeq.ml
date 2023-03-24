open Common
open Vocab
open Int64Util
open SynthLang
open BitVecCommon

module Elem = struct
    type t = B_Bot | B_Top | B_Zero | B_One

    let from_bool (mb: bool) (vb: bool): t =
        if mb then
            if vb then
                B_Top
            else B_Bot
        else
            if vb then
                B_One
            else B_Zero

    let to_bit (e: t): int64 * int64 =
        match e with
        | B_Zero -> (0L,0L)
        | B_One -> (0L,1L)
        | B_Bot -> (1L,0L)
        | B_Top -> (1L,1L)

    let is_bot (e: t): bool =
        match e with
        | B_Bot -> true
        | _ -> false

    let join (e1: t) (e2: t): t =
        match e1, e2 with
        | B_Bot, _ -> e2
        | _, B_Bot -> e1
        | B_Top, _ -> B_Top
        | _, B_Top -> B_Top
        | _ ->
            if e1 = e2 then e1 else B_Top

    let meet (e1: t) (e2: t): t =
        match e1, e2 with
        | B_Bot, _ -> B_Bot
        | _, B_Bot -> B_Bot
        | B_Top, _ -> e2
        | _, B_Top -> e1
        | _ ->
            if e1 = e2 then e1 else B_Bot

    let leq (e1: t) (e2: t): bool =
        match e1, e2 with
        | B_Bot, _ -> true
        | _, B_Top -> true
        | _ ->
            if e1 = e2 then true else false

    let to_string (e: t): string =
        match e with
        | B_Bot -> "_"
        | B_Top -> "T"
        | B_One -> "1"
        | B_Zero -> "0"

    let forward_not (e: t): t =
        match e with
        | B_One -> B_Zero
        | B_Zero -> B_One
        | _ -> e

    let forward_and (e1: t) (e2: t): t =
        match e1, e2 with
        | B_Bot, _ | _, B_Bot -> B_Bot
        | B_Top, _ | _, B_Top -> B_Top
        | B_One, B_One -> B_One
        | _ -> B_Zero

    let forward_or (e1: t) (e2: t): t =
        match e1, e2 with
        | B_Bot, _ | _, B_Bot -> B_Bot
        | B_Top, _ | _, B_Top -> B_Top
        | B_Zero, B_Zero -> B_Zero
        | _ -> B_One

    let forward_xor (e1: t) (e2: t): t =
        match e1, e2 with
        | B_Bot, _ | _, B_Bot -> B_Bot
        | B_Top, _ | _, B_Top -> B_Top
        | _, _ -> if e1 = e2 then B_Zero else B_One

    let backward_not (post: t) (e: t): t =
        forward_not post

    let backward_and (post: t) (e1: t) (e2: t): t * t =
        match post, e1, e2 with
        | B_One, _, _ -> (B_One, B_One)
        | B_Zero, B_One, _ -> (B_One, B_Zero)
        | B_Zero, _, B_One -> (B_Zero, B_One)
        | _, _, _ -> (B_Top, B_Top)

    let backward_or (post: t) (e1: t) (e2: t): t * t =
        match post, e1, e2 with
        | B_Zero, _, _ -> (B_Zero, B_Zero)
        | B_One, B_Zero, _ -> (B_Zero, B_One)
        | B_One, _, B_Zero -> (B_One, B_Zero)
        | _, _, _ -> (B_Top, B_Top)

    let backward_xor (post: t) (e1: t) (e2: t): t * t =
        match post with
        | B_Zero -> begin
            if e1 <> B_Top then
                (e1, e1)
            else if e2 <> B_Top then
                (e2, e2)
            else (B_Top, B_Top)
        end
        | B_One -> begin
            if e1 <> B_Top then
                (e1, forward_not e1)
            else if e2 <> B_Top then
                (forward_not e2, e2)
            else (B_Top, B_Top)
        end
        | _ -> (B_Top, B_Top)
end

type t = int64 * int64 (* (mask * value). for each bit, B_Zero(0,0) B_One(0,1) B_Bot(1,0) B_Top(1,1) *)
type elem = Elem.t

module Make(I: MaskedInt64Type) = struct
    let apply_mask_t ((m,v): t): t = (I.apply_mask m, I.apply_mask v)

    let is_valid_idx (idx: int): bool =
        0 <= idx && idx <= I.bit_length - 1
    
    let assert_valid_idx (at: string) (idx: int): unit =
        if not (is_valid_idx idx) then
            failwith_bit_length_f I.bit_length idx "%s: bit idx out of range" at

    let bot_repr: t = (I.mask, 0L)

    let top_repr: t = (I.mask, I.mask)

    let is_bot ((m,v): t): bool =
        let intermediate = m $&&$ ~~v in
        intermediate <> 0L

    let from_int64 (i: int64): t = (0L, I.apply_mask i)

    let zero: t = (0L, 0L)

    let gamma_if_singleton ((m,v): t): Exprs.const option =
        if m = 0L then Some (Exprs.CBV (I.bit_length, v)) else None
    
    let bool_array_to_int64 (a: bool Array.t): int64 =
        if BatArray.length a = I.bit_length then
            BatArray.fold_right (fun e result ->
                    if e then Int64.succ (Int64.shift_left result 1)
                    else (Int64.shift_left result 1)
                ) a 0L
        else
            failwith_bit_length_f I.bit_length (BatArray.length a) "bool_array_to_int64 %s" (string_of_array string_of_bool a)
    
    let get_elem ((m,v): t) (idx: int): elem =
        assert_valid_idx "get_elem" idx;
        Elem.from_bool (is_bit_set m idx) (is_bit_set v idx)

    let msb (t: t): elem = get_elem t (I.bit_length - 1)

    let lsb (t: t): elem = get_elem t 0

    let sign_bit: t -> elem = msb

    let set_bit ((m,v):t) (idx: int) (e: elem): t =
        assert_valid_idx "set_bit" idx;
        let mb, vb = Elem.to_bit e in
        let mb', vb', x = Int64.shift_left mb idx, Int64.shift_left vb idx, ~~ (Int64.shift_left 1L idx) in
        ((x $&&$ m) $||$ mb', (x $&&$ v) $||$ vb')

    let sign_split ((m,v) as t: t): t * t =
        match sign_bit t with
        | Elem.B_Top ->
            set_bit t (I.bit_length - 1) B_One, set_bit t (I.bit_length - 1) B_Zero
        | Elem.B_Bot ->
            bot_repr, bot_repr
        | Elem.B_Zero ->
            bot_repr, t
        | Elem.B_One ->
            t, bot_repr
    
    let bits_fold_from_low (f: elem -> 'a -> 'a) ((m,v):t) (z: 'a): 'a =
        let rec worker cnt z =
            if cnt < I.bit_length then
                let e =
                    Elem.from_bool (is_bit_set m cnt) (is_bit_set v cnt)
                in
                worker (cnt + 1) (f e z)
            else z
        in
        worker 0 z

    let bits_fold_from_low2 (f2: elem -> elem -> 'a -> 'a) ((m1,v1):t) ((m2,v2):t) (z: 'a): 'a =
        let rec worker cnt z =
            if cnt < I.bit_length then
                let e1 =
                    Elem.from_bool (is_bit_set m1 cnt) (is_bit_set v1 cnt)
                in
                let e2 =
                    Elem.from_bool (is_bit_set m2 cnt) (is_bit_set v2 cnt)
                in
                worker (cnt + 1) (f2 e1 e2 z)
            else z
        in
        worker 0 z

    let bits_fold_from_high (f: elem -> 'a -> 'a) ((m,v):t) (z: 'a): 'a =
        let rec worker cnt z =
            if cnt >= 0 then
                let e =
                    Elem.from_bool (is_bit_set m cnt) (is_bit_set v cnt)
                in
                worker (cnt - 1) (f e z)
            else z
        in
        worker (I.bit_length - 1) z

    let bits_fold_from_high2 (f: elem -> elem -> 'a -> 'a) ((m1,v1):t) ((m2,v2):t) (z: 'a): 'a =
        let rec worker cnt z =
            if cnt >= 0 then
                let e1 =
                    Elem.from_bool (is_bit_set m1 cnt) (is_bit_set v1 cnt)
                in
                let e2 =
                    Elem.from_bool (is_bit_set m2 cnt) (is_bit_set v2 cnt)
                in
                worker (cnt - 1) (f e1 e2 z)
            else z
        in
        worker (I.bit_length - 1) z

    let bits_fold_from_high3 (f: elem -> elem -> elem -> 'a -> 'a) ((m1,v1):t) ((m2,v2):t) ((m3,v3):t) (z: 'a): 'a =
        let rec worker cnt z =
            if cnt >= 0 then
                let e1 =
                    Elem.from_bool (is_bit_set m1 cnt) (is_bit_set v1 cnt)
                in
                let e2 =
                    Elem.from_bool (is_bit_set m2 cnt) (is_bit_set v2 cnt)
                in
                let e3 =
                    Elem.from_bool (is_bit_set m3 cnt) (is_bit_set v3 cnt)
                in
                worker (cnt - 1) (f e1 e2 e3 z)
            else z
        in
        worker (I.bit_length - 1) z

    let bits_map (f: elem -> elem) (t:t): t =
        bits_fold_from_high (fun e (m,v) ->
            let slm, slv = Int64.shift_left m 1, Int64.shift_left v 1 in
            set_bit (slm, slv) 0 (f e)
        ) t zero

    let bits_map2 (f: elem -> elem -> elem) (t1:t) (t2:t): t =
        bits_fold_from_high2 (fun e1 e2 (m,v) ->
            let slm, slv = Int64.shift_left m 1, Int64.shift_left v 1 in
            set_bit (slm, slv) 0 (f e1 e2)
        ) t1 t2 zero

    let bits_exists (pred: elem -> bool) ((m,v):t): bool =
        let rec worker cnt =
            if cnt < I.bit_length then
                let e =
                    Elem.from_bool (is_bit_set m cnt) (is_bit_set v cnt)
                in
                if pred e then
                    true
                else
                    worker (cnt + 1)
            else false
        in
        worker 0

    let bits_exists2 (pred: elem -> elem -> bool) ((m1,v1):t) ((m2,v2):t): bool =
        let rec worker cnt =
            if cnt < I.bit_length then
                let e1 =
                    Elem.from_bool (is_bit_set m1 cnt) (is_bit_set v1 cnt)
                in
                let e2 =
                    Elem.from_bool (is_bit_set m2 cnt) (is_bit_set v2 cnt)
                in
                if pred e1 e2 then
                    true
                else
                    worker (cnt + 1)
            else false
        in
        worker 0

    let to_string ((m,v) as t: t): string =
        if t = top_repr then "T"
        else
            let rec worker (cnt: int) (acc: string list): string list =
                if cnt < ((I.bit_length - 1) / 4) + 1 then
                    let m' = m %>>>% (cnt * 4) in
                    let v' = v %>>>% (cnt * 4) in
                    let m_cursor = m' $&&$ 0xFL in
                    let v_cursor = v' $&&$ 0xFL in
                    let acc' =
                        if m_cursor = 0L then
                            Int64.format "%Lx" v_cursor :: acc
                        else if m_cursor = 0xFL && v_cursor = 0L then
                            "_" :: acc
                        else if m_cursor = 0xFL && v_cursor = 15L then
                            "T" :: acc
                        else
                            let rec sub_worker (mini_m: int64) (mini_v: int64) (sub_cnt: int) (sub_acc: string list): string list =
                                if sub_cnt < 4 then
                                    let sub_acc' = Elem.to_string (Elem.from_bool (mini_m $&&$ 1L = 1L) (mini_v $&&$ 1L = 1L)) :: sub_acc in
                                    sub_worker (mini_m %>>>% 1) (mini_v %>>>% 1) (sub_cnt + 1) sub_acc'
                                else
                                    sub_acc
                            in
                            "{" :: (sub_worker m_cursor v_cursor 0 ("}" ::acc))
                    in
                    if cnt mod 4 = 3 then
                        worker (cnt + 1) ("-" :: acc')
                    else worker (cnt + 1) acc'
                else
                    acc
            in
            string_of_list ~first:"0bx[" ~last:"]" ~sep:"" identity (worker 0 [])

    let get_top_indices ((m,v) as t: t): int list =
        bits_fold_from_low (fun e (idx, result) ->
                if e = B_Top then (idx + 1, idx :: result)
                else (idx + 1, result)
            ) t (0, []) |> snd

    let gamma_result_size (top_indices: int list): int64 option =
        let top_cnt = BatList.length top_indices in
        if top_cnt <> I.bit_length then 
            Some (Int64.shift_left 1L top_cnt)
        else None
    
    let gamma_size_constraint (max_size: int) ((m,v) as t: t): SynthLang.Exprs.const BatSet.t option =
        if m = 0L then Some (BatSet.singleton (SynthLang.Exprs.CBV (I.bit_length, v)))
        else
            let collected_top_pos = get_top_indices t in
            match gamma_result_size collected_top_pos with
            | Some cnt_64 when Int64.unsigned_compare cnt_64 (Int64.of_int max_size) <= 0 ->
                (* do concretize *)
                let rec work (top_pos: int list) (making: t) (result_set: SynthLang.Exprs.const BatSet.t): SynthLang.Exprs.const BatSet.t =
                    match top_pos with
                    | [] ->
                        if fst making <> 0L then begin
                            Logger.g_error_f "no more top_pos, but making is %s" (to_string making);
                            failwith "assertion fail: BitVecDom.concretize_if_available is not correct"
                        end else
                            BatSet.add (SynthLang.Exprs.CBV (I.bit_length, snd making)) result_set
                    | cur :: tail ->
                        let with_zero = set_bit making cur B_Zero in
                        let with_zero_set = work tail with_zero result_set in
                        let with_one = set_bit making cur B_One in
                        work tail with_one with_zero_set
                in
                Some (work collected_top_pos t BatSet.empty)
            | _ -> None

    let forward_arith_shift_right ((m,v): t) (count: int): t =
        (I.arith_shift_right m count, I.arith_shift_right v count)

    let forward_logical_shift_right ((m,v): t) (count: int): t =
        (m %>>>% count, v %>>>% count)

    let forward_shift_left ((m,v): t) (count: int): t =
        (m %<<% count, v %<<% count) |> apply_mask_t

    let init (f: int -> elem): t =
        let rec worker cnt z =
            if cnt < I.bit_length then
                let e = f cnt in
                worker (cnt + 1) (set_bit z cnt e)
            else z
        in
        worker 0 zero

    let bit_string_to_int64 (s: string): int64 =
        s |> BatString.to_list
        |> BatList.map (fun c -> match c with
            | '0' -> [false]
            | '1' -> [true]
            | _ -> []
        ) |> BatList.flatten
        |> BatList.rev
        |> BatArray.of_list
        |> bool_array_to_int64
    
    let bit_string_to_t (s: string): t =
        s |> BatString.to_list
        |> BatList.map (fun c -> match c with
            | '0' -> [Elem.B_Zero]
            | '1' -> [Elem.B_One]
            | '.' -> [Elem.B_Bot]
            | 'T' -> [Elem.B_Top]
            | _ -> []
        ) |> BatList.flatten
        |> BatList.rev
        |> BatArray.of_list
        |> fun a -> (init (fun idx -> if idx < BatArray.length a then a.(idx) else Elem.B_Bot))

    let join ((m1,v1): t) ((m2,v2): t): t =
        (
            (~~ (m1 $||$ v1) $&&$ v2) $||$ ((~~ (m2 $||$ v2) $&&$ v1)) $||$ (m1 $&&$ v1) $||$ (m2 $&&$ v2) $||$ (m1 $&&$ m2),
            v1 $||$ v2
        )

    let meet ((m1,v1): t) ((m2,v2): t): t =
        (
            (~~(v1 $||$ m2) $&&$ v2) $||$ (~~(v2 $||$ m1) $&&$ v1) $||$ (m2 $&&$ ~~v2) $||$ (m1 $&&$ ~~v1) $||$ (m1 $&&$ m2),
            v1 $&&$ v2
        )

    let leq ((m1,v1): t) ((m2,v2): t): bool =
        let each_leq = ~~(v1 $||$ m2 $||$ v2) $||$ (~~m1 $&&$ v1 $&&$ v2) $||$ (m1 $&&$ ~~v1) $||$ (m2 $&&$ v2) in
        0L = ~~each_leq

    let forward_not ((m,v): t): t =
        (m, ~~(Int64.logxor m v) |> I.apply_mask)

    let forward_add (t1: t) (t2: t): t =
        let carry: elem ref = ref Elem.B_Zero in
        bits_fold_from_low2 (fun e1 e2 (z, idx) ->
                let operands = [e1; e2; !carry] in
                let e' =
                    if BatList.mem Elem.B_Bot operands then begin
                        carry := Elem.B_Bot;
                        Elem.B_Bot
                    end
                    else if BatList.mem Elem.B_Top operands then begin
                        carry := Elem.B_Top;
                        Elem.B_Top
                    end
                    else
                        let count = BatList.fold_left (fun ones e -> if e = Elem.B_One then succ ones else ones) 0 operands in
                        match count with
                        | 0 ->
                            carry := Elem.B_Zero;
                            Elem.B_Zero
                        | 1 ->
                            carry := Elem.B_Zero;
                            Elem.B_One
                        | 2 ->
                            carry := Elem.B_One;
                            Elem.B_Zero
                        | _ ->
                            carry := Elem.B_One;
                            Elem.B_One
                in
                (set_bit z idx e', idx + 1)
        ) t1 t2 (zero, 0) |> fst
    
    let forward_succ (t: t): t = forward_add t (from_int64 1L)

    let forward_neg (t: t): t = forward_succ (forward_not t)

    let forward_and ((m1,v1): t) ((m2,v2): t): t =
        (m1 $||$ m2, (~~m1 $&&$ m2 $&&$ v2) $||$ (~~m2 $&&$ m1 $&&$ v1) $||$ (v1 $&&$ v2))

    let forward_or ((m1,v1): t) ((m2,v2): t): t =
        (m1 $||$ m2, (~~m1 $&&$ v2) $||$ (~~m2 $&&$ v1) $||$ (v1 $&&$ v2))

    let forward_xor ((m1,v1): t) ((m2,v2): t): t =
        (m1 $||$ m2, (~~(m1 $||$ v1) $&&$ v2) $||$ (~~(m2 $||$ v2) $&&$ v1) $||$ (m1 $&&$ v1 $&&$ v2) $||$ (m2 $&&$ v1 $&&$ v2))

    let forward_mul ((m1,v1): t) ((m2,v2): t): t =
        (** using ?????100 * ???1000 = ??100000 *)
        let using_post_zeros: t  = 
            let postzeros1 = postzeros (Int64.logor m1 v1) in
            let postzeros2 = postzeros (Int64.logor m2 v2) in
            let bits = postzeros (Int64.mul postzeros1 postzeros2) in
            (bits,bits)
        in

        (* using TTTTTTabc * TTdefghi = TTTTT(abc * ghi mod 1000) *)
        let using_non_top_postfix: t =
            let cm = postzeros m1 $||$ postzeros m2 in
            let cvm = ~~cm in
            (cm, cm $||$ ((Int64.mul v1 v2) $&&$ cvm))
        in

        meet using_post_zeros using_non_top_postfix |> apply_mask_t
    
    let unsigned_concretized_min ((m,v): t): int64 =
        if is_bot (m,v) then
            raise EarlyBotReduction
        else
            I.logand (I.lognot m) v
    
    let unsigned_concretized_max ((m,v): t): int64 =
        if is_bot (m,v) then
            raise EarlyBotReduction
        else
            v
    
    let signed_concretized_min (t: t): int64 =
        match sign_bit t with
        | B_Bot ->
            raise EarlyBotReduction
        | B_Zero | B_One ->
            unsigned_concretized_min t
        | B_Top ->
            (set_bit t (I.bit_length - 1) B_One) |> unsigned_concretized_min

    let signed_concretized_max (t: t): int64 =
        match sign_bit t with
        | B_Bot -> raise EarlyBotReduction
        | B_Zero | B_One -> unsigned_concretized_max t
        | B_Top ->
            (set_bit t (I.bit_length - 1) B_Zero) |> unsigned_concretized_max
    
    let common_prefix_and_tops (v1: int64) (v2: int64): t =
        (* short-circuit for constant range *)
        if v1 = v2 then
            from_int64 v1
        else
            let rec worker cnt vz =
                if cnt >= 0 then
                    let p = I.shift_left 1L cnt in
                    let e1 = I.logand v1 p in
                    let e2 = I.logand v2 p in
                    if e1 = e2 then
                        worker
                            (cnt - 1)
                            (I.logor (I.shift_left vz 1) (e1 %>>>% cnt))
                    else
                        (vz,cnt)
                else (vz,cnt)
            in
            let (vz,cnt) = worker (I.bit_length - 1) 0L in
            if cnt < 0 then
                from_int64 vz
            else if cnt >= I.bit_length - 1 then
                top_repr
            else
                let m =
                    I.lognot (I.shift_left I.minus_one (cnt + 1))
                in
                (m, I.logor (I.shift_left vz (cnt + 1)) m)
end