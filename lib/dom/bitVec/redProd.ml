open Common
open Vocab
open Int64Util
open SynthLang
open BitVecCommon

type t = SignedIntv.t * UnsignedIntv.t * ABitSeq.t

module Make(I: MaskedInt64Type) = struct
    module S = SignedIntv.Make(I)
    module U = UnsignedIntv.Make(I)
    module B = ABitSeq.Make(I)

    let bot_repr: t = (S.bot_repr, U.bot_repr, B.bot_repr)

    let top_repr: t = (S.top_repr, U.top_repr, B.top_repr)

    let from_int64 (i: int64): t = (S.from_int64 i, U.from_int64 i, B.from_int64 i)

    let from_const (c: Exprs.const): t = match c with
        | Exprs.CBV (len, bv) ->
            if len = I.bit_length then
                from_int64 bv
            else failwith_bit_length I.bit_length len "singleton abstraction function failed"
        | _ -> top_repr (* BitVecDom cannot represent other types  *)

    let gamma_size_constraint (max_size: int) ((s,u,b): t): Exprs.const BatSet.t option =
        try
            let result = ref None in

            begin
            match B.gamma_size_constraint max_size b with
                | None -> begin
                    ()
                end
                | Some x -> begin
                    if BatSet.is_empty x then
                        raise Not_found (* hack *)
                    else begin
                        result := (match !result with
                            | None -> Some x
                            | Some prev -> Some (BatSet.intersect prev x))
                        ;
                        if !result = Some(BatSet.empty) then
                            raise Not_found
                    end
                end
            end;
            
            begin
                match U.gamma_size_constraint max_size u with
                | None -> begin
                    ()
                end
                | Some x ->
                    if BatSet.is_empty x then
                        raise Not_found (* hack *)
                    else begin
                        result := (match !result with
                            | None -> Some x
                            | Some prev -> Some (BatSet.intersect prev x))
                        ;
                        if !result = Some(BatSet.empty) then
                            raise Not_found
                    end
            end;

            begin
                match S.gamma_size_constraint max_size s with
                | None ->
                    ()
                | Some x ->
                    if BatSet.is_empty x then
                        raise Not_found (* hack *)
                    else begin
                        result := (match !result with
                            | None -> Some x
                            | Some prev -> Some (BatSet.intersect prev x))
                        ;
                        if !result = Some(BatSet.empty) then
                            raise Not_found
                    end
            end;

            !result
        with Not_found ->
            Some BatSet.empty
    
    let gamma_if_singleton ((s,u,b): t): Exprs.const option =
        match B.gamma_if_singleton b with
        | Some bc -> Some bc
        | _ -> begin
            match U.gamma_if_singleton u with
            | Some uc -> Some uc
            | _ -> S.gamma_if_singleton s
        end

    let to_string ((s,u,b): t): string =
        Printf.sprintf "(%s,%s,%s)" (S.to_string s) (U.to_string u) (B.to_string b)
    
    let is_bot ((s,u,b): t): bool =
        S.is_bot s || U.is_bot u || B.is_bot b

    let join ((s1,u1,b1): t) ((s2,u2,b2): t): t =
        (S.join s1 s2, U.join u1 u2, B.join b1 b2)

    let meet ((s1,u1,b1): t) ((s2,u2,b2): t): t =
        (S.meet s1 s2, U.meet u1 u2, B.meet b1 b2)

    let leq ((s1,u1,b1): t) ((s2,u2,b2): t): bool =
        S.leq s1 s2 && U.leq u1 u2 && B.leq b1 b2
    
    let reudction_step_u ((s,u,b): t): UnsignedIntv.t =
        let from_b =
            let l = B.unsigned_concretized_min b in
            let r = B.unsigned_concretized_max b in
            U.intv l r
        in
        let from_s = match s with
            | SignedIntv.SIBot -> raise EarlyBotReduction
            | SignedIntv.SIntv (lb, rb) ->
                if I.signed_compare 0L lb <= 0 then
                    U.intv lb rb
                else if I.signed_compare rb 0L < 0 then
                    U.intv lb rb
                else U.top_repr
        in
        U.meet (U.meet u from_b) from_s
    
    let reduction_step_s ((s,u,b): t): SignedIntv.t =
        let from_b =
            let l = B.signed_concretized_min b in
            let r = B.signed_concretized_max b in
            S.intv l r
        in
        let from_u = match u with
            | UnsignedIntv.UIBot -> raise EarlyBotReduction
            | UnsignedIntv.UIntv (lb, rb) ->
                if I.unsigned_compare rb I.signed_max_int <= 0 then
                    S.intv lb rb
                else if I.unsigned_compare I.signed_max_int lb < 0 then
                    S.intv lb rb
                else S.top_repr
        in
        S.meet (S.meet s from_b) from_u

    let reduction_step_b ((s,u,b): t): ABitSeq.t =
        let from_u =
            match u with
            | UnsignedIntv.UIBot -> raise EarlyBotReduction
            | UnsignedIntv.UIntv (l,r) ->
                B.common_prefix_and_tops l r
        in
        let from_s =
            match s with
            | SignedIntv.SIBot -> raise EarlyBotReduction
            | SignedIntv.SIntv (l,r) ->
                if l < 0L && 0L <= r then
                    B.top_repr
                else
                    B.common_prefix_and_tops l r
        in
        B.meet (B.meet b from_u) from_s

    let reduction ((s,u,b): t): t =
        let rec fix t =
            let r = (reduction_step_s t, reudction_step_u t, reduction_step_b t) in
            if r = t then
                t
            else
                fix r
        in
        try
            fix (s,u,b)
        with EarlyBotReduction -> bot_repr

    let sign_split ((s,u,b): t): t * t =
        let (s1,s2) = S.sign_split s in
        let (u1,u2) = U.sign_split u in
        let (b1,b2) = B.sign_split b in
        ((s1,u1,b1) |> reduction, (s2,u2,b2) |> reduction)

    let forward_not ((s,u,b): t): t =
        reduction (S.forward_not s, U.forward_not u, B.forward_not b)

    let forward_and ((_, _, b1): t) ((_, _, b2): t): t =
        let b' = B.forward_and b1 b2 in
        reduction (S.top_repr, U.top_repr, b')

    let forward_or ((_, _, b1): t) ((_, _, b2): t): t =
        let b' = B.forward_or b1 b2 in
        reduction (S.top_repr, U.top_repr, b')

    let forward_xor ((_, _, b1): t) ((_, _, b2): t): t =
        let b' = B.forward_xor b1 b2 in
        reduction (S.top_repr, U.top_repr, b')

    (** TODO: interval can be left shifted (multiply by 2^m...) *)
    let common_forward_shift (shift_type: int) ((_, _, b1): t) ((s2, u2, _): t): t =
        let shifter (b: ABitSeq.t) (lb: int) (ub: int) =
            let get_elem (idx: int) (count: int): (ABitSeq.elem * bool) =
                match shift_type with
                | 0 -> (* ashr *)
                    if idx + count < I.bit_length then (B.get_elem b (idx + count), false)
                    else (B.sign_bit b, true)
                | 1 -> (* lshr *)
                    if idx + count < I.bit_length then (B.get_elem b (idx + count), false)
                    else (B_Zero, true)
                | _ -> (* shl *)
                    if idx - count >= 0 then (B.get_elem b (idx - count), false)
                    else (B_Zero, true)
            in
            let elem_joined (idx: int): ABitSeq.elem =
                let rec worker (acc: ABitSeq.elem) (count: int): ABitSeq.elem =
                    if count <= ub then
                        let (e, stop) = get_elem idx count in
                        match ABitSeq.Elem.join acc e with
                        | ABitSeq.Elem.B_Top -> ABitSeq.Elem.B_Top
                        | acc' ->
                            if stop then acc'
                            else worker acc' (count + 1)
                    else acc
                in
                worker ABitSeq.Elem.B_Bot lb
            in
            B.init elem_joined
        in
        let shift_count_s =
            let c = S.meet (S.intv 0L (Int64.of_int (I.bit_length - 1))) s2 in
            if c = S.bot_repr then S.from_int64 (Int64.of_int I.bit_length) else c
        in
        let shift_count_u =
            let c = U.meet (U.intv 0L (Int64.of_int (I.bit_length - 1))) u2 in
            if c = U.bot_repr then U.from_int64 (Int64.of_int I.bit_length) else c
        in
        (** TODO: better performance algorithm? calculate each bits *)
        let bv_shift_range (b: ABitSeq.t) (l: int64) (r: int64): ABitSeq.t =
            if l = 0L && r = Int64.of_int (I.bit_length - 1) then
                B.top_repr
            else
                shifter b (Int64.to_int l) (Int64.to_int r)
        in
        match shift_count_s, shift_count_u with
        | SignedIntv.SIBot, UnsignedIntv.UIBot -> 
            bot_repr
        | SignedIntv.SIBot, UnsignedIntv.UIntv (l,r) | SignedIntv.SIntv (l,r), UnsignedIntv.UIBot ->
            reduction (S.top_repr, U.top_repr, bv_shift_range b1 l r)
        | SignedIntv.SIntv (ls,rs), UnsignedIntv.UIntv (lu,ru) ->
            reduction (S.top_repr, U.top_repr, bv_shift_range b1 (max ls lu) (min rs ru))

    let forward_ashr (d1: t) (d2: t): t =
        common_forward_shift 0 d1 d2

    let forward_lshr (d1: t) (d2: t): t =
        common_forward_shift 1 d1 d2

    let forward_shl  (d1: t) (d2: t): t =
        common_forward_shift 2 d1 d2

    let forward_neg ((s, u, b): t): t =
        reduction (S.forward_neg s, U.forward_neg u, B.forward_neg b)

    let forward_add ((s1, u1, b1): t) ((s2, u2, b2): t): t =
        reduction (S.forward_add s1 s2, U.forward_add u1 u2, B.forward_add b1 b2)

    let forward_sub ((s1, u1, b1): t) ((s2, u2, b2): t): t =
        reduction (S.forward_sub s1 s2, U.forward_sub u1 u2, B.forward_add b1 (B.forward_neg b2))

    let forward_mul ((s1, u1, b1): t) ((s2, u2, b2): t): t =
        reduction (S.forward_mul s1 s2, U.forward_mul u1 u2, B.forward_mul b1 b2)

    let forward_udiv ((_, u1, _): t) ((_, u2, _): t): t =
        reduction (S.top_repr, U.forward_div u1 u2, B.top_repr)

    let forward_urem ((_, u1, _): t) ((_, u2, _): t): t =
        reduction (S.top_repr, U.forward_rem u1 u2, B.top_repr)

    let forward_sdiv ((s1, _, b1): t) ((s2, _, b2): t): t =
        reduction (S.forward_div s1 s2, U.top_repr, B.top_repr)

    let forward_srem ((s1, _, _): t) ((s2, _, _): t): t =
        reduction (S.forward_rem s1 s2, U.top_repr, B.top_repr)

    let forward_un_op (uop: Operators.bv_un_op) (arg0: t): t =
        let uf = match uop with
            | BV_NOT -> forward_not
            | BV_NEG -> forward_neg
        in
        uf arg0

    let forward_bin_op (bop: Operators.bv_bin_op) (arg0: t) (arg1: t): t =
        let bf = match bop with
            | BV_AND -> forward_and
            | BV_OR -> forward_or
            | BV_XOR -> forward_xor
            | BV_ADD -> forward_add
            | BV_SUB -> forward_sub
            | BV_MUL -> forward_mul
            | BV_UDIV -> forward_udiv
            | BV_UREM -> forward_urem
            | BV_LSHR -> forward_lshr
            | BV_ASHR -> forward_ashr
            | BV_SHL -> forward_shl
            | BV_SDIV -> forward_sdiv
            | BV_SREM -> forward_srem
        in
        bf arg0 arg1

    let backward_not ((post_s,post_u,post_b): t) ((s1,u1,b1): t): t =
        meet (s1,u1,b1) (forward_not (post_s,post_u,post_b)) |> reduction

    let backward_and ((_,_,post_b): t) ((s1,u1,b1): t) ((s2,u2,b2): t): (t * t) =
        let (b1', b2') =
        (*
            p = (0,1) : e1 = (0,1)
            p = (0,0) & e2 = (0,1) => e1 = (0,0)
            o.w (1,1)
            
            ! (!pm & (pv | (!e2m & e2v)))
            e1m == pm | (!pv & (e2m | !e2v)) (* p가 bottop 이거나, 아니면 p가 0인데 b2가 bottop이거나 zero면 top *)
            e1v == pm | pv | e2m | !e2v (* p가 0은 아니면서 b2가 bottop이거나 0이면 1 *)
        *)
        (*    let (b1m,b1v) = b1 in
            let (b2m,b2v) = b2 in
            let (pm,pv) = post_b in
            let b1m' = (pm $||$ (~~pv $&&$ (b2m $||$ ~~b2v))) in
            let b1v' = (pm $||$ pv $||$ b2m $||$ ~~b2v) in
            let b2m' = (pm $||$ (~~pv $&&$ (b1m $||$ ~~b1v))) in
            let b2v' = (pm $||$ pv $||$ b1m $||$ ~~b1v) in
            ((b1m',b1v'), (b2m',b2v')) *)
            B.bits_fold_from_high3 (fun post_e e1 e2 (z1,z2) ->
                let e1', e2' = ABitSeq.Elem.backward_and post_e e1 e2 in
                (B.set_bit (B.forward_shift_left z1 1) 0 e1',
                    B.set_bit (B.forward_shift_left z2 1) 0 e2')
            ) post_b b1 b2 (B.zero, B.zero)
        in
        ((s1, u1, B.meet b1 b1') |> reduction, (s2, u2, B.meet b2 b2') |> reduction)

    let backward_or ((_,_,post_b): t) ((s1,u1,b1): t) ((s2,u2,b2): t): (t * t) =
        let (b1', b2') = B.bits_fold_from_high3 (fun post_e e1 e2 (z1,z2) ->
            let e1', e2' = ABitSeq.Elem.backward_or post_e e1 e2 in
            (B.set_bit (B.forward_shift_left z1 1) 0 e1',
                B.set_bit (B.forward_shift_left z2 1) 0 e2')
            ) post_b b1 b2 (B.zero, B.zero)
        in
        ((s1, u1, B.meet b1 b1') |> reduction, (s2, u2, B.meet b2 b2') |> reduction)

    let backward_xor ((post_s,post_u,post_b): t) ((s1,u1,b1): t) ((s2,u2,b2): t): (t * t) =
        let (b1', b2') = B.bits_fold_from_high3 (fun post_e e1 e2 (z1,z2) ->
                let e1', e2' = ABitSeq.Elem.backward_xor post_e e1 e2 in
                (B.set_bit (B.forward_shift_left z1 1) 0 e1',
                    B.set_bit (B.forward_shift_left z2 1) 0 e2')
            ) post_b b1 b2 (B.zero, B.zero)
        in
        ((s1, u1, B.meet b1 b1') |> reduction, (s2, u2, B.meet b2 b2') |> reduction)

    let common_backward_shift (shift_type: int) ((_,_,post_b): t) ((s1, u1, b1): t) ((s2, u2, b2): t): (t * t) =
        let shift_count_cut: int =
            let count_prefix_until (break_cond: ABitSeq.elem -> bool) (b: ABitSeq.t): int =
                let rec worker cnt =
                    if cnt < I.bit_length then
                        if break_cond (B.get_elem b ((I.bit_length - 1) - cnt)) then cnt
                        else worker (cnt + 1)
                    else cnt
                in
                worker 0
            in
            match shift_type with
            | 0 -> (* ashr *) begin
                let post_sign = B.sign_bit post_b in
                let first_const_bit = ref None in
                (*
                sign = top 일때: first bit flip (sign bit이 뭔진 알 수 없음)
                *)
                let cnt = count_prefix_until (fun (e: ABitSeq.elem) -> match post_sign, !first_const_bit, e with
                    | ABitSeq.Elem.B_Zero, _, ABitSeq.Elem.B_One -> true
                    | ABitSeq.Elem.B_One, _, ABitSeq.Elem.B_Zero -> true
                    | ABitSeq.Elem.B_Top, None, ABitSeq.Elem.B_Zero
                    | ABitSeq.Elem.B_Top, None, ABitSeq.Elem.B_One ->
                        first_const_bit := Some e;
                        false
                    | ABitSeq.Elem.B_Top, Some prev, ABitSeq.Elem.B_Zero
                    | ABitSeq.Elem.B_Top, Some prev, ABitSeq.Elem.B_One ->
                        prev <> e
                    | _, _, _ -> false) post_b in
                if cnt = I.bit_length then cnt
                else cnt - 1
            end
            | 1 -> (* lshr *) begin
                count_prefix_until (fun (e: ABitSeq.elem) -> match e with
                    | ABitSeq.Elem.B_One -> true
                    | _ -> false) post_b
            end
            | _ -> (* shl *) begin
                let rec worker idx =
                    if idx < I.bit_length then
                        match B.get_elem post_b idx with
                        | ABitSeq.Elem.B_One -> idx
                        | _ -> worker (idx + 1)
                    else idx
                in
                worker 0
            end
        in
        let reverse_shifter (b: ABitSeq.t) (lb: int) (ub: int) =
            let get_elem_reversed (idx: int) (count: int): (ABitSeq.elem * bool) =
                match shift_type with
                | 0 -> (* ashr *)
                    if idx - count >= 0 then (B.get_elem b (idx - count), false)
                    else (ABitSeq.Elem.B_Top, true)
                | 1 -> (* lshr *)
                    if idx - count >= 0 then (B.get_elem b (idx - count), false)
                    else (ABitSeq.Elem.B_Top, true)
                | _ -> (* shl *)
                    if idx + count < I.bit_length then (B.get_elem b (idx + count), false)
                    else (ABitSeq.Elem.B_Top, true)
            in
            let elem_joined (idx: int): ABitSeq.elem =
                let rec worker (acc: ABitSeq.elem) (count: int): ABitSeq.elem =
                    if count <= ub then
                        let (e, stop) = get_elem_reversed idx count in
                        match ABitSeq.Elem.join acc e with
                        | ABitSeq.Elem.B_Top -> ABitSeq.Elem.B_Top
                        | acc' ->
                            if stop then acc'
                            else worker acc' (count + 1)
                    else acc
                in
                worker ABitSeq.Elem.B_Bot lb
            in
            B.init elem_joined
        in
        let shift_count_s =
            let c = S.meet (S.intv 0L (Int64.of_int (I.bit_length - 1))) s2 in
            if c = S.bot_repr then S.from_int64 (Int64.of_int I.bit_length) else c
        in
        let shift_count_u =
            let c = U.meet (U.intv 0L (Int64.of_int (I.bit_length - 1))) u2 in
            if c = U.bot_repr then U.from_int64 (Int64.of_int I.bit_length) else c
        in
        let reverese_shift_range (b: ABitSeq.t) (l: int64) (r: int64): ABitSeq.t =
            if l = 0L && r = Int64.of_int (I.bit_length - 1) then
                B.top_repr
            else
                reverse_shifter b (Int64.to_int l) (Int64.to_int r)
        in
        let b1' = match shift_count_s, shift_count_u with
            | SignedIntv.SIBot, UnsignedIntv.UIBot -> 
                b1
            | SignedIntv.SIBot, UnsignedIntv.UIntv (l,r) | SignedIntv.SIntv (l,r), UnsignedIntv.UIBot ->
                reverese_shift_range post_b l r |> B.meet b1
            | SignedIntv.SIntv (ls,rs), UnsignedIntv.UIntv (lu,ru) ->
                reverese_shift_range post_b (max ls lu) (min rs ru) |> B.meet b1
        in
        let cut_s2 = S.meet s2 (S.intv 0L (Int64.of_int shift_count_cut)) in
        let cut_u2 = U.meet u2 (U.intv 0L (Int64.of_int shift_count_cut)) in
        (reduction (s1, u1, b1'),
            reduction
                (cut_s2,
                cut_u2,
                b2))

    let backward_ashr ((post_s,post_u,post_b): t) ((s1,u1,b1): t) ((s2,u2,b2): t): (t * t) =
        (* d1 >> d2 = post *)
        common_backward_shift 0 (post_s,post_u,post_b) (s1,u1,b1) (s2,u2,b2)

    let backward_lshr ((post_s,post_u,post_b): t) ((s1,u1,b1): t) ((s2,u2,b2): t): (t * t) =
        (* d1 >>> d2 = post *)
        common_backward_shift 1 (post_s,post_u,post_b) (s1,u1,b1) (s2,u2,b2)

    let backward_shl ((post_s,post_u,post_b): t) ((s1,u1,b1): t) ((s2,u2,b2): t): (t * t) =
        (* d1 << d2 = post *)
        common_backward_shift 2 (post_s,post_u,post_b) (s1,u1,b1) (s2,u2,b2)

    let backward_neg ((post_s,post_u,post_b): t) ((s1,u1,b1): t): t =
        meet (s1,u1,b1) (forward_neg (post_s,post_u,post_b)) |> reduction

    let backward_add (post: t) (d1: t) (d2: t): (t * t) =
        let d1' = forward_sub post d2 in
        let d2' = forward_sub post d1 in
        (meet d1 d1' |> reduction, meet d2 d2' |> reduction)

    let backward_sub (post: t) (d1: t) (d2: t): (t * t) =
        let d1' = forward_add post d2 in
        let d2' = forward_sub d1 post in
        (meet d1 d1' |> reduction, meet d2 d2' |> reduction)

    (* c * d = p => solve condition of d *)
    let backward_const_mul (c: int64) ((s,u,b) as d: t) (post: int64): t =
        if c = 0L then
            if post = 0L then d (* any d possible *)
            else bot_repr (* impossible *)
        else
            let split_postfix_zeros (i: int64): int64 * int =
                let rec aux (i: int64) (zeros: int): int64 * int =
                    if i $&&$ 1L = 0L then
                        aux (i %>>>% 1) (zeros + 1)
                    else (i, zeros)
                in
                aux i 0
            in
            let (odd, zero_cnt) = split_postfix_zeros c in
            let post_reduced = post %>>>% zero_cnt in
            if I.shift_left post_reduced zero_cnt <> post then
                (* infeasible case *)
                bot_repr
            else
                let b' =
                    if zero_cnt = 0 then
                        I.mul (mult_inverse_int64 odd) post |> B.from_int64
                    else
                        let mod_factor = I.shift_left 1L (I.bit_length - zero_cnt) in
                        let inverse = mult_inverse_ext_euclidean odd mod_factor in
                        let less_d = I.mul post_reduced inverse in
                        let top_mask = postzeros mod_factor in
                        B.join (I.minus_one, top_mask) (B.from_int64 less_d)
                in
                (s, u, B.meet b b') |> reduction

    (*
    post = 1T11TT00000
    b1 = 00011T10T00

    p zeros: 5~7개
    b1 zeros: 2~4개
    b2 zeros: 5~7 - 2~4 = 1~5개

    각각 0 갯수 ~ 1아닌 갯수로 범위 만들고

    p - b1 = b2
    p - b2 = b1

    *)
    let backward_mul ((_,_,post_b) as post_d: t) ((s1,u1,b1) as d1: t) ((s2,u2,b2) as d2: t): (t * t) =
        match gamma_if_singleton post_d, gamma_if_singleton d1, gamma_if_singleton d2 with
        | Some (CBV (_, const_post)), Some (CBV (_, const_d1)), _ ->
            let d2' = backward_const_mul const_d1 d2 const_post in
            (d1, d2')
        | Some (CBV (_, const_post)), _, Some (CBV (_, const_d2)) ->
            let d1' = backward_const_mul const_d2 d1 const_post in
            (d1', d2)
        | _, _, _ ->
            let post_zeros_min_max b =
                let (_, z_min, _, z_max) =
                    B.bits_fold_from_low (fun e (met_not_zero, min, met_one, max) ->
                        match e with
                        | ABitSeq.Elem.B_Zero ->
                            (met_not_zero, (if met_not_zero then min else min + 1), met_one, (if met_one then max else max + 1))
                        | ABitSeq.Elem.B_One ->
                            (true, min, true, max)
                        | _ ->
                            (true, min, met_one, (if met_one then max else max + 1))
                    ) b (false, 0, false, 0)
                in
                (z_min, z_max)
            in
            let (pz_min, pz_max) = post_zeros_min_max post_b in
            let (b1z_min, b1z_max) = post_zeros_min_max b1 in
            let (b2z_min, b2z_max) = post_zeros_min_max b2 in
            (*
            (5,10) - (3,6) = (-1,7) => (0,7)
            (0,0) - (3,6) = (-6,-3) => bot
            *)
            let intv_sub (min1,max1) (min2,max2) =
                let l = min1 - max2 in
                let r = max1 - min2 in
                S.intv (Int64.of_int l) (Int64.of_int r)
            in
            let b1z =
                S.meet (S.intv (Int64.of_int b1z_min) (Int64.of_int b1z_max)) (intv_sub (pz_min,pz_max) (b2z_min,b2z_max))
            in
            let b2z =
                S.meet (S.intv (Int64.of_int b2z_min) (Int64.of_int b2z_max)) (intv_sub (pz_min,pz_max) (b1z_min,b1z_max))
            in
            match b1z, b2z with
            | SignedIntv.SIBot, _ | _, SignedIntv.SIBot ->
                (bot_repr, bot_repr)
            | SignedIntv.SIntv(b1z_min',_), SignedIntv.SIntv(b2z_min', _) ->
                let b1_zero_cnt = Int64.to_int b1z_min' in
                let b2_zero_cnt = Int64.to_int b2z_min' in
                let b1' = B.init (fun idx -> if idx < b1_zero_cnt then ABitSeq.Elem.B_Zero else ABitSeq.Elem.B_Top) in
                let b2' = B.init (fun idx -> if idx < b2_zero_cnt then ABitSeq.Elem.B_Zero else ABitSeq.Elem.B_Top) in
                ((s1, u1, B.meet b1 b1') |> reduction, (s2,u2, B.meet b2 b2') |> reduction)

    (* c / d = post => solve condition of d *)
    let backward_const_udiv (c: int64) (post: int64): UnsignedIntv.t =
        if post = 0L then
            U.top_repr
        else
            let x = I.unsigned_div c post in
            if I.unsigned_compare x post <= 0 then
                U.from_int64 x
            else
                let rp = I.unsigned_rem x post in
                let k =
                    let m = I.sub x rp in
                    let n = I.add post 1L in
                    if I.unsigned_rem m n = 0L then
                        I.sub (I.unsigned_div m n) 1L
                    else
                        I.unsigned_div m n
                in
                U.intv (I.sub x k) x

    let backward_udiv ((_,post_u,_): t) ((s1,u1,b1): t) ((s2,u2,b2): t): (t * t) =
        match post_u with
        | UIBot -> bot_repr, bot_repr
        | UIntv (lp, rp) ->
            let masked_u2 =
                (* d1 / d2 = post, d1 = d2 * post + rem(0 ~ d2-1) *)
                (* we know that d2 * post must not overflow! *)
                if lp = 0L then (* when post = 0, no overflow *)
                    u2
                else
                    let non_overflow_mask = U.intv 0L (I.unsigned_div I.minus_one lp) in
                    U.meet u2 non_overflow_mask
            in
            let u1_from_u2 =
                match masked_u2 with
                | UIBot ->
                    U.bot_repr
                | UIntv (l2,r2) ->
                    if r2 = 0L then (* undefined semantics -> bot *)
                        U.bot_repr
                    else
                        (* d1 / d2 = post, d1 = d2 * post + rem(0 ~ d2-1) *)
                        let m = U.forward_mul masked_u2 post_u in
                        U.forward_add m (U.intv 0L (I.sub r2 1L))
            in
            let u2_from_u1 =
                match u1 with
                | UIBot ->
                    U.bot_repr
                | UIntv (l1,r1) -> begin
                    let lower = backward_const_udiv l1 rp in
                    let upper = backward_const_udiv r1 lp in
                    U.join lower upper
                end
            in
            let u1' = U.meet u1 u1_from_u2 in
            let u2' = U.meet masked_u2 u2_from_u1 in
            ((s1, u1', b1) |> reduction, (s2, u2', b2) |> reduction)

    let try_exact_inverse_rem_d2_opt (post: int64) (c1: int64): t option =
        if c1 = post then
            (* we only know that p < d2 *)
            None
        else if c1 = 0L then
            (* 0 % ? = always 0 *)
            (* here c1 <> post, so it's infeasible *)
            Some bot_repr
        else if I.unsigned_compare I.signed_min_int post <= 0 then
            (* post msb is 1 -> const_1 must equal to const_p *)
            (* why? for post = 1TTTT..T, c1 / c2 = 1 for c1 >= c2 > post, 0 otherwise. *)
            (* for c1 >= c2, post = c1 - c2 without wrapping, but we cannot produce 1TTTT by subtract c2 > post *)
            (* so c1 < c2 and post = c1. *)
            if post = c1 then
                (* we only know that p < d2 *)
                None
            else
                (* infeasible *)
                Some bot_repr
        else if I.unsigned_compare c1 post < 0 then
            (* should be: post <= c1 *)
            Some bot_repr
        else 
            (* here, always post <= c1, c1 - post >= 0 *)
            let diff = I.sub c1 post in
            (*
            * d1 = d2 * K + p   (p < d2)
            * d1 - p = d2 * K
            * d2는 d1 - p의 약수여야함
            * d1 - p 가 소수라면 d2 = d1 - p 일텐데 소수 테스트를 직접 하는 것은 비싸다.
            * d1 - p 가 소수가 아니라면 가장 큰 진약수 X에 대해, X <= p 이면 d2 > p 여야하므로 d2 != X, d2 = d1 - p
            *)
            if I.unsigned_compare (approx_maximum_proper_udivisor diff) post <= 0 then
                if diff = post then
                    Some bot_repr
                else
                    Some (from_int64 diff)
            else
                None

    let backward_urem ((_,post_u,post_b) as post: t) ((s1,u1,b1) as d1: t) ((s2,u2,b2) as d2: t): (t * t) =
        (* d1 % d2 = post, post < d2 *)
        let trial_exact_inverse_d2_opt =
            match gamma_if_singleton post, gamma_if_singleton d1 with
            | Some (CBV (_, const_p)), Some (CBV (_, const_1)) -> begin
                try_exact_inverse_rem_d2_opt const_p const_1
            end
            | _ -> None
        in
        let ((s2,u2,b2) as d2: t) = (* modify baseline *)
            match trial_exact_inverse_d2_opt with
            | Some refined_d2 ->
                refined_d2
            | _ -> d2
        in
        match post_u with
        | UnsignedIntv.UIBot -> (* mostly unreachable *)
            (bot_repr, bot_repr)
        | UnsignedIntv.UIntv (pu_l, pu_u) ->
            let b1' =
                (* 예를 들어 b2 = 10111000으로 나눈 나머지 post가 abcde였다고 가정하면,
                * b1 의 마지막 3비트는 cde 와 같을 것이다. 10진수에서 임의의 1000의 배수로 나눈 나머지에서
                * 마지막 3자리가 그대로 보존되는 것과 같은 원리로.
                * b2로부터 postzeros를 추출하고 이것으로 post의 마지막 유효 자리들을 꺼내서 b1에 적용한다.
                *)
                let top_with_b2_postfix_zeros =
                    let (m2,v2) = b2 in
                    let tmp = I.apply_mask (postzeros (m2 $||$ v2)) in
                    (tmp, tmp)
                in
                B.forward_or post_b top_with_b2_postfix_zeros
            in
            let (reduced_s1', reduced_u1', reduced_b1') as d1' = (s1,u1,B.meet b1 b1') |> reduction in
            let u2' =
                if is_bot (meet d1' post) then
                    (* u1과 post_u 가 절대 같을 수 없다면 u1보다 u2가 작다는 사실을 알 수 있다 *)
                    match reduced_u1' with
                    | UnsignedIntv.UIBot ->
                        U.bot_repr
                    | UnsignedIntv.UIntv (u1l, u1r) ->
                        if I.unsigned_compare pu_l u1r > 0 then U.bot_repr
                        else U.meet (U.intv pu_l u1r) u2
                else
                    if pu_l = I.minus_one then
                        U.bot_repr
                    else
                        U.meet (U.intv (I.add pu_l 1L) I.minus_one) u2
            in
            let u1' =
                if I.unsigned_compare I.signed_min_int pu_l <= 0 then
                    (* post msb is 1 -> const_1 must equal to cont_p *)
                    U.meet post_u reduced_u1'
                else reduced_u1'
            in
            ((reduced_s1', u1', reduced_b1'), (s2,U.meet u2 u2',b2) |> reduction)

    let backward_sdiv ((post_s,_,_) as post: t) ((s1,u1,b1) as d1: t) ((s2,u2,b2) as d2: t): (t * t) =
        let neg_post, pos_post = sign_split post in
        let neg_d1, pos_d1 = sign_split d1 in
        let neg_d2, pos_d2 = sign_split d2 in

        let pos_d1', pos_d2' =
            (* positive post: pos d1 / pos d2 or neg d1 / neg d2 *)
            let pp_d1, pp_d2 = backward_udiv pos_post pos_d1 pos_d2 in
            let nn_d1, nn_d2 = backward_udiv pos_post (forward_neg neg_d1) (forward_neg neg_d2) in
            join pp_d1 (forward_neg nn_d1), join pp_d2 (forward_neg nn_d2)
        in
        let neg_d1', neg_d2' =
            (* negative post: pos d1 / neg d2 or neg d1 / pos d2 *)
            let pn_d1, pn_d2 = backward_udiv (forward_neg neg_post) pos_d1 (forward_neg neg_d2) in
            let np_d1, np_d2 = backward_udiv (forward_neg neg_post) (forward_neg neg_d1) pos_d2 in
            join pn_d1 (forward_neg np_d1), join np_d2 (forward_neg pn_d2)
        in
        let d1', d2' = join pos_d1' neg_d1', join pos_d2' neg_d2' in
        (meet d1 d1' |> reduction, meet d2 d2' |> reduction)

    let backward_srem ((post_s,_,post_b) as post: t) ((s1,u1,b1) as d1: t) ((s2,u2,b2) as d2: t): (t * t) =
        let ((neg_post_s, neg_post_u, neg_post_b) as neg_post), ((pos_post_s, pos_post_u, pos_post_b) as pos_post) = sign_split post in
        let ((neg_s1, neg_u1, neg_b1) as neg_d1), ((pos_s1, pos_u1, pos_b1) as pos_d1) = sign_split d1 in
        let (neg_d2, pos_d2) = sign_split d2 in
        let ((abs_s2, abs_u2, abs_b2) as abs_d2) = forward_neg neg_d2 |> join pos_d2 in
        let (assume_pos_d1', assume_pos_d2') = backward_urem pos_post pos_d1 abs_d2 in
        let (assume_neg_d1', assume_neg_d2') = backward_urem (forward_neg neg_post) (forward_neg neg_d1) abs_d2 in
        let assume_neg_neg_d1' = forward_neg assume_neg_d1' in
        let d2' =
            assume_pos_d2'
            |> join (forward_neg assume_pos_d2')
            |> join assume_neg_d2'
            |> join (forward_neg assume_neg_d2')
        in
        (join assume_pos_d1' assume_neg_neg_d1' |> meet d1 |> reduction,
        d2' |> meet d2 |> reduction)

    let backward_un_op (uop: Operators.bv_un_op) (post: t) (d: t): t =
        let uf =
            match uop with
            | BV_NEG -> backward_neg
            | BV_NOT -> backward_not
        in
        uf post d

    let backward_bin_op (bop: Operators.bv_bin_op) (post: t) (d1: t) (d2: t): t * t =
        let bf = match bop with
            | BV_AND -> backward_and
            | BV_OR -> backward_or
            | BV_XOR -> backward_xor
            | BV_ADD -> backward_add
            | BV_SUB -> backward_sub
            | BV_MUL -> backward_mul
            | BV_UDIV -> backward_udiv
            | BV_UREM -> backward_urem
            | BV_LSHR -> backward_lshr
            | BV_ASHR -> backward_ashr
            | BV_SHL -> backward_shl
            | BV_SDIV -> backward_sdiv
            | BV_SREM -> backward_srem
        in
        bf post d1 d2
end