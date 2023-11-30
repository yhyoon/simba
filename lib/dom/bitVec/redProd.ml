open Common
open Vocab
open Int64Util
open SynthLang
open BitVecCommon

type t = SignedIntv.t

module Make(I: MaskedInt64Type) = struct
    module S = SignedIntv.Make(I)
    module U = UnsignedIntv.Make(I)
    module B = ABitSeq.Make(I)

    let bot_repr: t = S.bot_repr

    let top_repr: t = S.top_repr

    let from_int64 (i: int64): t = S.from_int64 i

    let from_const (c: Exprs.const): t = match c with
        | Exprs.CBV (len, bv) ->
            if len = I.bit_length then
                from_int64 bv
            else failwith_bit_length I.bit_length len "singleton abstraction function failed"
        | _ -> top_repr (* BitVecDom cannot represent other types  *)

    let gamma_size_constraint (max_size: int) (s: t): Exprs.const BatSet.t option =
        try
            let result = ref None in

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
    
    let gamma_if_singleton (s: t): Exprs.const option =
        S.gamma_if_singleton s

    let to_string (s: t): string =
        S.to_string s
    
    let is_bot (s: t): bool =
        S.is_bot s

    let join (s1: t) (s2: t): t =
        S.join s1 s2

    let meet (s1: t) (s2: t): t =
        S.meet s1 s2

    let leq (s1: t) (s2: t): bool =
        S.leq s1 s2
    
    let reudction_step_u ((s,u,b)): UnsignedIntv.t =
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
    
    let reduction_step_s ((s,u,b)): SignedIntv.t =
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

    let reduction_step_b ((s,u,b)): ABitSeq.t =
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

    let reduction (s,u,b) =
        let rec fix t =
            let r = (reduction_step_s t, reudction_step_u t, reduction_step_b t) in
            if r = t then
                t
            else
                fix r
        in
        try
            fix (s,u,b)
        with EarlyBotReduction -> S.bot_repr, U.bot_repr, B.bot_repr

    let sign_split (s: t): t * t =
        S.sign_split s

    let forward_not (s: t): t =
        S.forward_not s

    let forward_and (s1: t) (s2: t): t =
        S.top_repr

    let forward_or (s1: t) (s2: t): t =
        S.top_repr

    let forward_xor (s1: t) (s2: t): t =
        S.top_repr

    let forward_ashr (d1: t) (d2: t): t =
        S.top_repr

    let forward_lshr (d1: t) (d2: t): t =
        S.top_repr

    let forward_shl  (d1: t) (d2: t): t =
        S.top_repr

    let forward_neg (s: t): t =
        S.forward_neg s

    let forward_add (s1: t) (s2: t): t =
        S.forward_add s1 s2

    let forward_sub (s1: t) (s2: t): t =
        S.forward_sub s1 s2

    let forward_mul (s1: t) (s2: t): t =
        S.forward_mul s1 s2

    let forward_udiv (s1: t) (s2: t): t =
        S.top_repr

    let forward_urem (s1: t) (s2: t): t =
        S.top_repr

    let forward_sdiv (s1: t) (s2: t): t =
        S.forward_div s1 s2

    let forward_srem (s1: t) (s2: t): t =
        S.forward_rem s1 s2

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

    let backward_not (post_s: t) (s1: t): t =
        meet s1 (forward_not post_s)

    let backward_and (post_s: t) (s1: t) (s2: t): (t * t) =
        s1, s2

    let backward_or (post_s: t) (s1: t) (s2: t): (t * t) =
        s1, s2

    let backward_xor (post_s: t) (s1: t) (s2: t): (t * t) =
        s1, s2

    let backward_ashr (post_s: t) (s1: t) (s2: t): (t * t) =
        (* d1 >> d2 = post *)
        s1, s2

    let backward_lshr (post_s: t) (s1: t) (s2: t): (t * t) =
        (* d1 >>> d2 = post *)
        s1, s2

    let backward_shl (post_s: t) (s1: t) (s2: t): (t * t) =
        (* d1 << d2 = post *)
        s1, s2

    let backward_neg (post_s: t) (s1: t): t =
        meet s1 (forward_neg post_s)

    let backward_add (post: t) (s1: t) (s2: t): (t * t) =
        let s1' = forward_sub post s2 in
        let s2' = forward_sub post s1 in
        (meet s1 s1', meet s2 s2')

    let backward_sub (post: t) (s1: t) (s2: t): (t * t) =
        let s1' = forward_add post s2 in
        let s2' = forward_sub s1 post in
        (meet s1 s1', meet s2 s2')

    (* c * d = p => solve condition of d *)
    let backward_const_mul (c: int64) (s as d: t) (post: int64): t =
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
                let s' =
                    if zero_cnt = 0 then
                        I.mul (mult_inverse_int64 odd) post |> S.from_int64
                    else
                        s
                in
                S.meet s s'

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
    let backward_mul (post_s as post_d: t) (s1 as d1: t) (s2 as d2: t): (t * t) =
        match gamma_if_singleton post_d, gamma_if_singleton d1, gamma_if_singleton d2 with
        | Some (CBV (_, const_post)), Some (CBV (_, const_d1)), _ ->
            let d2' = backward_const_mul const_d1 d2 const_post in
            (d1, d2')
        | Some (CBV (_, const_post)), _, Some (CBV (_, const_d2)) ->
            let d1' = backward_const_mul const_d2 d1 const_post in
            (d1', d2)
        | _, _, _ ->
            (s1, s2)

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

    let backward_udiv (post_s: t) (s1: t) (s2: t): (t * t) =
        match post_s with
        | SignedIntv.SIBot -> bot_repr, bot_repr
        | _ -> s1, s2

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

    let backward_urem (post_s as post: t) (s1 as d1: t) (s2 as d2: t): (t * t) =
        (* d1 % d2 = post, post < d2 *)
        let trial_exact_inverse_d2_opt =
            match gamma_if_singleton post, gamma_if_singleton d1 with
            | Some (CBV (_, const_p)), Some (CBV (_, const_1)) -> begin
                try_exact_inverse_rem_d2_opt const_p const_1
            end
            | _ -> None
        in
        let (s2 as d2: t) = (* modify baseline *)
            match trial_exact_inverse_d2_opt with
            | Some refined_d2 ->
                refined_d2
            | _ -> d2
        in
        match post_s with
        | SignedIntv.SIBot -> (* mostly unreachable *)
            (bot_repr, bot_repr)
        | _ -> s1, s2

    let backward_sdiv (post_s as post: t) (s1 as d1: t) (s2 as d2: t): (t * t) =
        s1, s2

    let backward_srem (post_s as post: t) (s1 as d1: t) (s2 as d2: t): (t * t) =
        s1, s2

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