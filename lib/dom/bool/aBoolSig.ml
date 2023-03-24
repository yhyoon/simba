open Common
open Vocab

open SynthLang
open BitVecCommon

module Elem = ABitSeq.Elem

type t = {
    bits_width: int;
    mask: int array;
    value: int array;
}

let ($&&$) (b1: int array) (b2: int array) = BatArray.map2 (land) b1 b2
let ($||$) (b1: int array) (b2: int array) = BatArray.map2 (lor) b1 b2
let ($^^$) (b1: int array) (b2: int array) = BatArray.map2 (lxor) b1 b2

let length (t: t): int = t.bits_width

let of_list (l: Elem.t list): t =
    let len = BatList.length l in
    let m = ImmBitVec.create_empty_bits len in
    let v = ImmBitVec.create_empty_bits len in
    BatList.iteri (fun i b ->
        match b with
        | Elem.B_Zero ->
            ()
        | Elem.B_One ->
            ImmBitVec.internal_set i len v
        | Elem.B_Bot ->
            ImmBitVec.internal_set i len m
        | Elem.B_Top -> begin
            ImmBitVec.internal_set i len m;
            ImmBitVec.internal_set i len v;
        end
    ) l;
    {
        bits_width = len;
        mask = m;
        value = v;
    }

let fold_elem (f: int -> ABitSeq.Elem.t -> 'a -> 'a) (t: t) (z: 'a): 'a =
    let result = ref z in
    let array_cursor = ref 0 in
    let index = ref 0 in
    while !array_cursor < BatArray.length t.mask do
        let m_elem = t.mask.(!array_cursor) in
        let v_elem = t.value.(!array_cursor) in
        let in_elem_index = ref 0 in
        while !index < t.bits_width && !in_elem_index < Sys.int_size do
            let flag = 1 lsl !in_elem_index in
            let mb = flag land m_elem <> 0 in
            let vb = flag land v_elem <> 0 in
            result := f !index (ABitSeq.Elem.from_bool mb vb) !result;
            incr in_elem_index;
            incr index;
        done;
        incr array_cursor
    done;
    !result

let to_elem_list (t: t): Elem.t list =
    fold_elem (fun idx e l -> e :: l) t [] |> BatList.rev

let to_string (t: t): string =
    fold_elem (fun idx e l -> Elem.to_string e :: l) t [] |> BatList.rev |> (string_of_list identity ~sep:"")

let is_bot (t: t): bool =
    (* check existence of bit with m = 1 & v = 0 *)
    ImmBitVec.count_internal t.bits_width (ImmBitVec.internal_diff t.bits_width t.mask t.value) > 0

let top_repr (len: int): t =
    let full_bits = (ImmBitVec.full_set len).bits in
    {
        bits_width = len;
        mask = full_bits;
        value = full_bits;
    }

let bot_repr (len: int): t = 
    {
        bits_width = len;
        mask = (ImmBitVec.full_set len).bits;
        value = (ImmBitVec.empty_set len).bits;
    }

let join (t1: t) (t2: t): t =
    if t1.bits_width <> t2.bits_width then
        failwith_f "unreachable: signature length mismatch in join: %d, %d" t1.bits_width t2.bits_width
    else
        let (~~) = ImmBitVec.internal_lognot t1.bits_width in
        let (m1,v1) = (t1.mask, t1.value) in
        let (m2,v2) = (t2.mask, t2.value) in
        {t1 with
            mask = (~~ (m1 $||$ v1) $&&$ v2) $||$ ((~~ (m2 $||$ v2) $&&$ v1)) $||$ (m1 $&&$ v1) $||$ (m2 $&&$ v2) $||$ (m1 $&&$ m2);
            value = v1 $||$ v2;
        }

let meet (t1: t) (t2: t): t =
    if t1.bits_width <> t2.bits_width then
        failwith_f "unreachable: signature length mismatch in meet: %d, %d" t1.bits_width t2.bits_width
    else
        let (~~) = ImmBitVec.internal_lognot t1.bits_width in
        let (m1,v1) = (t1.mask, t1.value) in
        let (m2,v2) = (t2.mask, t2.value) in
        {t1 with
            mask = (~~(v1 $||$ m2) $&&$ v2) $||$ (~~(v2 $||$ m1) $&&$ v1) $||$ (m2 $&&$ ~~v2) $||$ (m1 $&&$ ~~v1) $||$ (m1 $&&$ m2);
            value = v1 $&&$ v2;
        }

let leq (t1: t) (t2: t): bool =
    if t1.bits_width <> t2.bits_width then
        failwith_f "unreachable: signature length mismatch in meet: %d, %d" t1.bits_width t2.bits_width
    else
        let (~~) = ImmBitVec.internal_lognot t1.bits_width in
        let (m1,v1) = (t1.mask, t1.value) in
        let (m2,v2) = (t2.mask, t2.value) in
        let each_leq = ~~(v1 $||$ m2 $||$ v2) $||$ (~~m1 $&&$ v1 $&&$ v2) $||$ (m1 $&&$ ~~v1) $||$ (m2 $&&$ v2) in
        BatArray.equal Int.equal each_leq (ImmBitVec.full_set t1.bits_width).bits

let alpha (signature: ImmBitVec.t): t =
    {
        bits_width = signature.bits_width;
        mask = (ImmBitVec.empty_set signature.bits_width).bits;
        value = signature.bits
    }

let gamma_if_singleton (t: t): (int * Exprs.const) list =
    fold_elem (fun idx elem acc_rev ->
        match elem with
        | B_Zero ->
            (idx, Exprs.CBool false) :: acc_rev
        | B_One ->
            (idx, Exprs.CBool true) :: acc_rev
        | _ -> acc_rev
    ) t [] |> BatList.rev

let gamma_size_constraint (max_size: int) (t: t): (int * Exprs.const BatSet.t) list =
    (* ignore size constraint option - ignore B_Top (performance issue) *)
    fold_elem (fun idx elem acc_rev ->
        match elem with
        | B_Bot ->
            (idx, BatSet.empty) :: acc_rev
        | B_Zero ->
            (idx, BatSet.singleton (Exprs.CBool false)) :: acc_rev
        | B_One ->
            (idx, BatSet.singleton (Exprs.CBool true)) :: acc_rev
        | _ -> acc_rev
    ) t [] |> BatList.rev

let forward_not (t: t): t =
    let (~~) = ImmBitVec.internal_lognot t.bits_width in
    {t with
        value = ~~(t.mask $^^$ t.value)
    }

let forward_and (t1: t) (t2: t): t =
    if t1.bits_width <> t2.bits_width then
        failwith_f "unreachable: signature length mismatch in forward_and: %d, %d" t1.bits_width t2.bits_width
    else
        let (~~) = ImmBitVec.internal_lognot t1.bits_width in
        let (m1,v1) = (t1.mask, t1.value) in
        let (m2,v2) = (t2.mask, t2.value) in
        let result =
        {t1 with
            mask = m1 $||$ m2;
            value = (~~m1 $&&$ m2 $&&$ v2) $||$ (~~m2 $&&$ m1 $&&$ v1) $||$ (v1 $&&$ v2);
        }
        in
        (* let _ = Logger.g_debug_f "forward: %s and %s => %s" (to_string t1) (to_string t2) (to_string result) in *)
        result

let forward_or (t1: t) (t2: t): t =
    if t1.bits_width <> t2.bits_width then
        failwith_f "unreachable: signature length mismatch in forward_or: %d, %d" t1.bits_width t2.bits_width
    else
        let (~~) = ImmBitVec.internal_lognot t1.bits_width in
        let (m1,v1) = (t1.mask, t1.value) in
        let (m2,v2) = (t2.mask, t2.value) in
        let result =
        {t1 with
            mask = m1 $||$ m2;
            value = (~~m1 $&&$ v2) $||$ (~~m2 $&&$ v1) $||$ (v1 $&&$ v2);
        }
        in
        (* let _ = Logger.g_debug_f "forward: %s or %s => %s" (to_string t1) (to_string t2) (to_string result) in *)
        result

let forward_xor (t1: t) (t2: t): t =
    if t1.bits_width <> t2.bits_width then
        failwith_f "unreachable: signature length mismatch in forward_xor: %d, %d" t1.bits_width t2.bits_width
    else
        let (~~) = ImmBitVec.internal_lognot t1.bits_width in
        let (m1,v1) = (t1.mask, t1.value) in
        let (m2,v2) = (t2.mask, t2.value) in
        let result =
        {t1 with
            mask = m1 $||$ m2;
            value = (~~(m1 $||$ v1) $&&$ v2) $||$ (~~(m2 $||$ v2) $&&$ v1) $||$ (m1 $&&$ v1 $&&$ v2) $||$ (m2 $&&$ v1 $&&$ v2);
        }
        in
        (* let _ = Logger.g_debug_f "forward: %s xor %s => %s" (to_string t1) (to_string t2) (to_string result) in *)
        result

let forward_un_op (uop: Operators.bool_un_op) (d: t): t =
    let uf =
        match uop with
        | Operators.B_NOT -> forward_not
    in
    uf d

let forward_bin_op (bop: Operators.bool_bin_op) (d1: t) (d2: t): t =
    let bf = match bop with
        | Operators.B_AND -> forward_and
        | Operators.B_OR -> forward_or
        | Operators.B_XOR -> forward_xor
    in
    bf d1 d2

let backward_not (post: t) (d: t): t =
    meet (forward_not post) d

let backward_and (post: t) (t1: t) (t2: t): t * t =
    if post.bits_width <> t1.bits_width || post.bits_width <> t2.bits_width then
        failwith_f "unreachable: signature length mismatch in backward_and: %d, %d, %d" post.bits_width t1.bits_width t2.bits_width
    else
        let (~~) = ImmBitVec.internal_lognot t1.bits_width in
        let (post_m,post_v) = (post.mask, post.value) in
        let (m1,v1) = (t1.mask, t1.value) in
        let (m2,v2) = (t2.mask, t2.value) in
        let result_m =  post_m $||$ (~~ post_v $&&$ (post_v $||$ m1 $||$ ~~v1) $&&$ (post_v $||$ m2 $||$ ~~v2)) in
        let result_v1 = post_m $||$ post_v $||$ m2 $||$ ~~v2 in
        let result_v2 = post_m $||$ post_v $||$ m1 $||$ ~~v1 in
        let result_t1 = meet {t1 with mask = result_m; value = result_v1} t1 in
        let result_t2 = meet {t2 with mask = result_m; value = result_v2} t2 in
        (* let _ =
            Logger.g_debug_f "backward: %s and %s = %s" (to_string t1) (to_string t2) (to_string post);
            Logger.g_debug_f "  result: %s and %s" (to_string result_t1) (to_string result_t2)
        in *)
        (result_t1, result_t2)

let backward_or (post: t) (t1: t) (t2: t): t * t =
    if post.bits_width <> t1.bits_width || post.bits_width <> t2.bits_width then
        failwith_f "unreachable: signature length mismatch in backward_or: %d, %d, %d" post.bits_width t1.bits_width t2.bits_width
    else
        let (~~) = ImmBitVec.internal_lognot t1.bits_width in
        let (post_m,post_v) = (post.mask, post.value) in
        let (m1,v1) = (t1.mask, t1.value) in
        let (m2,v2) = (t2.mask, t2.value) in
        let result_m =  post_m $||$ (post_v $&&$ (m1 $||$ v1) $&&$ (m2 $||$ v2)) in
        let result_v1 = post_m $||$ (post_v $&&$ (m1 $||$ v1)) in
        let result_v2 = post_m $||$ (post_v $&&$ (m2 $||$ v2)) in
        let result_t1 = meet {t1 with mask = result_m; value = result_v1} t1 in
        let result_t2 = meet {t2 with mask = result_m; value = result_v2} t2 in
        (* let _ =
            Logger.g_debug_f "backward: %s or %s = %s" (to_string t1) (to_string t2) (to_string post);
            Logger.g_debug_f "  result: %s or %s" (to_string result_t1) (to_string result_t2)
        in *)
        (result_t1, result_t2)

let backward_xor (post: t) (t1: t) (t2: t): t * t =
    if post.bits_width <> t1.bits_width || post.bits_width <> t2.bits_width then
        failwith_f "unreachable: signature length mismatch in backward_xor: %d, %d, %d" post.bits_width t1.bits_width t2.bits_width
    else
        let (~~) = ImmBitVec.internal_lognot t1.bits_width in
        let (post_m,post_v) = (post.mask, post.value) in
        let (m1,v1) = (t1.mask, t1.value) in
        let (m2,v2) = (t2.mask, t2.value) in
        let d1top = m1 $&&$ v1 in
        let d2top = m2 $&&$ v2 in
        let no_top = ~~ (d1top $||$ d2top) in
        let result_m1 = post_m $||$ (~~d2top $&&$ m2) $||$ (d2top $&&$ m1) in
        let result_m2 = post_m $||$ (~~d1top $&&$ m1) $||$ (d1top $&&$ m2) in
        let result_v1 =
            post_m $||$ (
                (d2top $&&$ v1)
                $||$
                (~~d2top $&&$ (
                    (~~post_v $&&$ v2)
                    $||$
                    (post_v $&&$ ~~(m2 $^^$ v2))
                ))
            )
        in
        let result_v2 =
            post_m $||$ (
                (d1top $&&$ v2)
                $||$
                (~~d1top $&&$ (
                    (~~post_v $&&$ v1)
                    $||$
                    (post_v $&&$ ~~(m1 $^^$ v1))
                ))
            )
        in
        let result_t1 = meet {t1 with mask = result_m1; value = result_v1} t1 in
        let result_t2 = meet {t2 with mask = result_m2; value = result_v2} t2 in
        (* let _ =
            Logger.g_debug_f "backward: %s xor %s = %s" (to_string t1) (to_string t2) (to_string post);
            Logger.g_debug_f "  result: %s xor %s" (to_string result_t1) (to_string result_t2)
        in *)
        (result_t1, result_t2)

let backward_un_op (uop: Operators.bool_un_op) (post: t) (d: t): t =
    let uf =
        match uop with
        | Operators.B_NOT -> backward_not
    in
    uf post d

let backward_bin_op (bop: Operators.bool_bin_op) (post: t) (d1: t) (d2: t): t * t =
    let bf = match bop with
        | Operators.B_AND -> backward_and
        | Operators.B_OR -> backward_or
        | Operators.B_XOR -> backward_xor
    in
    bf post d1 d2

let backward_operation (op: Operators.op) (post: t) (args: t list): t list =
        match op, args with
        | Operators.BOOL_OP Operators.B_UN_OP uop, arg0 :: [] ->
            let post_arg0 = backward_un_op uop post arg0 in
            [post_arg0]
        | Operators.BOOL_OP Operators.B_BIN_OP bop, arg0 :: arg1 :: [] -> begin
            let (post_arg0, post_arg1) = backward_bin_op bop post arg0 arg1 in
            [post_arg0; post_arg1]
        end
        | _ ->
            failwith (Printf.sprintf "not supported backward operation: operator %s with %d operands"
                (Operators.op_to_string op)
                (BatList.length args)
            )