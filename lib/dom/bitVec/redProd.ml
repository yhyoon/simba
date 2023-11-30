open Common
open Vocab
open Int64Util
open SynthLang
open BitVecCommon

type t = UnsignedIntv.t

module Make(I: MaskedInt64Type) = struct
    module S = SignedIntv.Make(I)
    module U = UnsignedIntv.Make(I)
    module B = ABitSeq.Make(I)

    let bot_repr: t = U.bot_repr

    let top_repr: t = U.top_repr

    let from_int64 (i: int64): t = U.from_int64 i

    let from_const (c: Exprs.const): t = match c with
        | Exprs.CBV (len, bv) ->
            if len = I.bit_length then
                from_int64 bv
            else failwith_bit_length I.bit_length len "singleton abstraction function failed"
        | _ -> top_repr (* BitVecDom cannot represent other types  *)

    let gamma_size_constraint (max_size: int) (u: t): Exprs.const BatSet.t option =
        try
            let result = ref None in


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

            !result
        with Not_found ->
            Some BatSet.empty
    
    let gamma_if_singleton (u: t): Exprs.const option =
        U.gamma_if_singleton u

    let to_string (u: t): string =
        U.to_string u
    
    let is_bot (u: t): bool =
        U.is_bot u

    let join (u1: t) (u2: t): t =
        U.join u1 u2

    let meet (u1: t) (u2: t): t =
        U.meet u1 u2

    let leq (u1: t) (u2: t): bool =
        U.leq u1 u2

    let sign_split (u: t): t * t =
        U.sign_split u

    let forward_not (u: t): t =
        U.forward_not u

    let forward_and (u1: t) (u2: t): t =
        U.top_repr

    let forward_or (u1: t) (u2: t): t =
        U.top_repr

    let forward_xor (u1: t) (u2: t): t =
        U.top_repr

    (** TODO: interval can be left shifted (multiply by 2^m...) *)
    let common_forward_shift (shift_type: int) (u1: t) (u2: t): t =
        U.top_repr

    let forward_ashr (d1: t) (d2: t): t =
        common_forward_shift 0 d1 d2

    let forward_lshr (d1: t) (d2: t): t =
        common_forward_shift 1 d1 d2

    let forward_shl  (d1: t) (d2: t): t =
        common_forward_shift 2 d1 d2

    let forward_neg (u: t): t =
        U.forward_neg u

    let forward_add (u1: t) (u2: t): t =
        U.forward_add u1 u2

    let forward_sub (u1: t) (u2: t): t =
        U.forward_sub u1 u2

    let forward_mul (u1: t) (u2: t): t =
        U.forward_mul u1 u2

    let forward_udiv (u1: t) (u2: t): t =
        U.forward_div u1 u2

    let forward_urem (u1: t) (u2: t): t =
        U.forward_rem u1 u2

    let forward_sdiv (u1: t) (u2: t): t =
        U.top_repr

    let forward_srem (s1: t) (s2: t): t =
        U.top_repr

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

    let forward_operation (op: Operators.op) (args: t list): t =
        match op, args with
        | Operators.BV_OP Operators.BV_UN_OP uop, arg0 :: [] ->
            forward_un_op uop arg0
        | Operators.BV_OP Operators.BV_BIN_OP bop, arg0 :: arg1 :: [] ->
            forward_bin_op bop arg0 arg1
        | _ ->
            failwith (Printf.sprintf "not supported forward operation: operator %s with %d operands"
                (Operators.op_to_string op)
                (BatList.length args)
            )

    let backward_not (post_u: t) (u1: t): t =
        meet u1 (forward_not post_u) 

    let backward_and (post_u: t) (u1: t) (u2: t): (t * t) =
        u1,u2

    let backward_or (post_u: t) (u1: t) (u2: t): (t * t) =
        u1,u2

    let backward_xor (post_u: t) (u1: t) (u2: t): (t * t) =
        u1,u2

    let common_backward_shift (shift_type: int) (post_u: t) (u1: t) (u2: t): (t * t) =
        u1,u2

    let backward_ashr (post_u: t) (u1: t) (u2: t): (t * t) =
        (* d1 >> d2 = post *)
        common_backward_shift 0 post_u u1 u2

    let backward_lshr (post_u: t) (u1: t) (u2: t): (t * t) =
        (* d1 >>> d2 = post *)
        common_backward_shift 1 post_u u1 u2

    let backward_shl (post_u: t) (u1: t) (u2: t): (t * t) =
        (* d1 << d2 = post *)
        common_backward_shift 2 post_u u1 u2

    let backward_neg (post_u: t) (u1: t): t =
        meet u1 (forward_neg post_u) 

    let backward_add (post: t) (d1: t) (d2: t): (t * t) =
        let d1' = forward_sub post d2 in
        let d2' = forward_sub post d1 in
        (meet d1 d1' , meet d2 d2' )

    let backward_sub (post: t) (d1: t) (d2: t): (t * t) =
        let d1' = forward_add post d2 in
        let d2' = forward_sub d1 post in
        (meet d1 d1' , meet d2 d2' )

    (* c * d = p => solve condition of d *)
    let backward_const_mul (c: int64) (u as d: t) (post: int64): t =
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
                u

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
    let backward_mul (post_u as post_d: t) (u1 as d1: t) (u2 as d2: t): (t * t) =
        match gamma_if_singleton post_d, gamma_if_singleton d1, gamma_if_singleton d2 with
        | Some (CBV (_, const_post)), Some (CBV (_, const_d1)), _ ->
            let d2' = backward_const_mul const_d1 d2 const_post in
            (d1, d2')
        | Some (CBV (_, const_post)), _, Some (CBV (_, const_d2)) ->
            let d1' = backward_const_mul const_d2 d1 const_post in
            (d1', d2)
        | _, _, _ ->
            u1,u2

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

    let backward_udiv (post_u: t) (u1: t) (u2: t): (t * t) =
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
            u1', u2'

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

    let backward_urem (post_u as post: t) (u1 as d1: t) (u2 as d2: t): (t * t) =
        (* d1 % d2 = post, post < d2 *)
        let trial_exact_inverse_d2_opt =
            match gamma_if_singleton post, gamma_if_singleton d1 with
            | Some (CBV (_, const_p)), Some (CBV (_, const_1)) -> begin
                try_exact_inverse_rem_d2_opt const_p const_1
            end
            | _ -> None
        in
        let (u2 as d2: t) = (* modify baseline *)
            match trial_exact_inverse_d2_opt with
            | Some refined_d2 ->
                refined_d2
            | _ -> d2
        in
        match post_u with
        | UnsignedIntv.UIBot -> (* mostly unreachable *)
            (bot_repr, bot_repr)
        | UnsignedIntv.UIntv (pu_l, pu_u) ->
            let u2' =
                if is_bot (meet u1 post) then
                    (* u1과 post_u 가 절대 같을 수 없다면 u1보다 u2가 작다는 사실을 알 수 있다 *)
                    match u1 with
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
                    U.meet post_u u1
                else u1
            in
            (u1', U.meet u2 u2')

    let backward_sdiv (post_u as post: t) (u1 as d1: t) (u2 as d2: t): (t * t) =
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
        (meet d1 d1' , meet d2 d2' )

    let backward_srem (post_u as post: t) (u1 as d1: t) (u2 as d2: t): (t * t) =
        let neg_post, pos_post = sign_split post in
        let neg_d1, pos_d1 = sign_split d1 in
        let (neg_d2, pos_d2) = sign_split d2 in
        let (abs_u2 as abs_d2) = forward_neg neg_d2 |> join pos_d2 in
        let (assume_pos_d1', assume_pos_d2') = backward_urem pos_post pos_d1 abs_d2 in
        let (assume_neg_d1', assume_neg_d2') = backward_urem (forward_neg neg_post) (forward_neg neg_d1) abs_d2 in
        let assume_neg_neg_d1' = forward_neg assume_neg_d1' in
        let d2' =
            assume_pos_d2'
            |> join (forward_neg assume_pos_d2')
            |> join assume_neg_d2'
            |> join (forward_neg assume_neg_d2')
        in
        (join assume_pos_d1' assume_neg_neg_d1' |> meet d1 ,
        d2' |> meet d2 )

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