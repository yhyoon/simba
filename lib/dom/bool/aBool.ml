open Common
open Vocab
open Int64Util
open SynthLang
open BitVecCommon

include ABitSeq.Elem

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