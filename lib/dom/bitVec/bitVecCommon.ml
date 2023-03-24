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
