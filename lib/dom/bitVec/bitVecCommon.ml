open Common
open Vocab
open Int64Util
open SynthLang

exception BitLengthMismatch of int * int * string
exception EarlyBotReduction

let failwith_bit_length (len1: int) (len2: int) (msg: string): 'a =
    raise (BitLengthMismatch (len1, len2, msg))

let failwith_bit_length_f (len1: int) (len2: int) fmt: 'a =
    Printf.ksprintf (failwith_bit_length len1 len2) fmt

module type AbstBVType = sig
    type t

    val to_string: t -> string
    
    val is_bot: t -> bool
    val top_repr: t

    val join: t -> t -> t
    val meet: t -> t -> t
    val leq: t -> t -> bool

    val from_int64: int64 -> t

    val gamma_if_singleton: t -> Exprs.const option
    val gamma_size_constraint: int -> t -> Exprs.const BatSet.t option

    val forward_un_op: Operators.bv_un_op -> t -> t
    val forward_bin_op: Operators.bv_bin_op -> t -> t -> t
    val backward_un_op: Operators.bv_un_op -> t -> t -> t
    val backward_bin_op: Operators.bv_bin_op -> t -> t -> t -> t * t
end