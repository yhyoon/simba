open Common
open Vocab
open Int64Util

open SynthLang
open GrammarUtil
open BitVecCommon

module Elem = ABitSeq.Elem

(* predefined domain modules for performance *)
module IntBV64 = MaskedInt64(struct let size = 64 end)
module IntBV32 = MaskedInt64(struct let size = 32 end)

module ABitSeq64 = ABitSeq.Make(IntBV64)
module SignedIntv64 = SignedIntv.Make(IntBV64)
module UnsignedIntv64 = UnsignedIntv.Make(IntBV64)
module RedProd64 = RedProd.Make(IntBV64)

module ABitSeq32 = ABitSeq.Make(IntBV32)
module SignedIntv32 = SignedIntv.Make(IntBV32)
module UnsignedIntv32 = UnsignedIntv.Make(IntBV32)
module RedProd32 = RedProd.Make(IntBV32)

(** Abstracted Signature (from type Exprs.signature) *)
module AbstSig = struct
    type t =
    | Bot                                   (* Empty *)
    | BitVec64 of RedProd.t list            (* BitVec 64 *)
    | BitVec32 of RedProd.t list            (* BitVec 32 *)
    | BitVecGeneral of int * RedProd.t list (* BitVec n  *)
    | Bool of ABoolSig.t                    (* Bool *)
    | Top                                   (* Full *)

    let to_string (t: t): string =
        match t with
        | Bot -> "bot"
        | BitVec64 pl -> string_of_list RedProd64.to_string pl
        | BitVec32 pl -> string_of_list RedProd32.to_string pl
        | BitVecGeneral (len, pl) ->
            let module I = MaskedInt64(struct let size = len end) in
            let module P = RedProd.Make(I) in
            string_of_list P.to_string pl
        | Bool bl -> ABoolSig.to_string bl
        | Top -> "top"

    (* partial order *)
    let bot_repr: t = Bot
    let top_repr: t = Top
    let is_bot (t: t): bool =
        match t with
        | Bot -> true
        | BitVec64 pl -> BatList.exists RedProd64.is_bot pl
        | BitVec32 pl -> BatList.exists RedProd32.is_bot pl
        | BitVecGeneral (len, pl) ->
            let module I = MaskedInt64(struct let size = len end) in
            let module P = RedProd.Make(I) in
            BatList.exists P.is_bot pl
        | Bool bl -> ABoolSig.is_bot bl
        | Top -> false

    let join (t1: t) (t2: t): t =
        match t1, t2 with
        | Bot, _ -> t2
        | _, Bot -> t1
        | Top, _ | _, Top -> Top
        | BitVec64 pl1, BitVec64 pl2 -> BitVec64 (BatList.map2 RedProd64.join pl1 pl2)
        | BitVec32 pl1, BitVec32 pl2 -> BitVec32 (BatList.map2 RedProd32.join pl1 pl2)
        | BitVecGeneral (len1, pl1), BitVecGeneral (len2, pl2) ->
            if len1 = len2 then
                let module I = MaskedInt64(struct let size = len1 end) in
                let module P = RedProd.Make(I) in
                BitVecGeneral (len1, BatList.map2 P.join pl1 pl2)
            else
                Top
        | Bool bl1, Bool bl2 -> 
            Bool (ABoolSig.join bl1 bl2)
        | _ -> Top

    let meet (t1: t) (t2: t): t =
        match t1, t2 with
        | Bot, _ | _, Bot -> Bot
        | Top, _ -> t2
        | _, Top -> t1
        | BitVec64 pl1, BitVec64 pl2 -> BitVec64 (BatList.map2 RedProd64.meet pl1 pl2)
        | BitVec32 pl1, BitVec32 pl2 -> BitVec32 (BatList.map2 RedProd32.meet pl1 pl2)
        | BitVecGeneral (len1, pl1), BitVecGeneral (len2, pl2) ->
            if len1 = len2 then
                let module I = MaskedInt64(struct let size = len1 end) in
                let module P = RedProd.Make(I) in
                BitVecGeneral (len1, BatList.map2 P.meet pl1 pl2)
            else
                Bot
        | Bool bl1, Bool bl2 -> 
            Bool (ABoolSig.meet bl1 bl2)
        | _ -> Bot

    let leq (t1: t) (t2: t): bool =
        match t1, t2 with
        | Bot, _ -> true
        | _, Bot -> false
        | _, Top -> true
        | Top, _ -> false
        | BitVec64 pl1, BitVec64 pl2 ->
            BatList.for_all2 RedProd64.leq pl1 pl2
        | BitVec32 pl1, BitVec32 pl2 ->
            BatList.for_all2 RedProd32.leq pl1 pl2
        | BitVecGeneral (len1, pl1), BitVecGeneral (len2, pl2) ->
            if len1 = len2 then
                let module I = MaskedInt64(struct let size = len1 end) in
                let module P = RedProd.Make(I) in
                BatList.for_all2 P.leq pl1 pl2
            else
                false
        | Bool bl1, Bool bl2 -> 
            ABoolSig.leq bl1 bl2
        | _ -> false

    (* abstraction/concretization/predefined *)
    let alpha (signature: Exprs.signature): t =
        match signature with
        | SigBV (len, il) -> begin
            match len with
            | 64 ->
                BitVec64 (BatList.map RedProd64.from_int64 il)
            | 32 ->
                BitVec32 (BatList.map RedProd32.from_int64 il)
            | _ ->
                let module I = MaskedInt64(struct let size = len end) in
                let module P = RedProd.Make(I) in
                BitVecGeneral (len, (BatList.map P.from_int64 il))
        end
        | SigBool bl ->
            Bool (ABoolSig.alpha bl)
        | _ -> Bot

    let alpha_output_spec (output_specs: Exprs.const_opt list): t =
        match output_specs with
        | [] -> failwith "empty signature"
        | Exprs.CDefined Exprs.CBV (len, _) :: _ | Exprs.CDontCare BV len :: _ -> begin
            match len with
            | 64 ->
                BitVec64 (BatList.map (fun c -> match c with
                        | Exprs.CDefined (Exprs.CBV (_, i)) -> RedProd64.from_int64 i
                        | Exprs.CDontCare _ -> RedProd64.top_repr
                        | _ -> failwith_f "signature_of_const_list(%s in CBV list): kind mismatch" (Exprs.string_of_const_opt c)
                    ) output_specs)
            | 32 ->
                BitVec32 (BatList.map (fun c -> match c with
                        | Exprs.CDefined (Exprs.CBV (_, i)) -> RedProd32.from_int64 i
                        | Exprs.CDontCare _ -> RedProd32.top_repr
                        | _ -> failwith_f "signature_of_const_list(%s in CBV list): kind mismatch" (Exprs.string_of_const_opt c)
                    ) output_specs)
            | _ ->
                let module I = MaskedInt64(struct let size = len end) in
                let module P = RedProd.Make(I) in
                BitVecGeneral (len, BatList.map (fun c -> match c with
                        | Exprs.CDefined (Exprs.CBV (_, i)) -> P.from_int64 i
                        | Exprs.CDontCare _ -> P.top_repr
                        | _ -> failwith_f "signature_of_const_list(%s in CBV list): kind mismatch" (Exprs.string_of_const_opt c)
                    ) output_specs)
        end
        | Exprs.CDefined CBool _ :: _ | Exprs.CDontCare Exprs.Bool :: _ ->
            Bool (ABoolSig.of_list (BatList.map (fun c -> match c with
                    | Exprs.CDefined (Exprs.CBool b) -> Elem.from_bool false b
                    | Exprs.CDontCare _ -> Elem.B_Top
                    | _ -> failwith_f "signature_of_const_list(%s in CBool list): kind mismatch" (Exprs.string_of_const_opt c)
                ) output_specs))
        | _ -> Bot

    let alphas (cl: Exprs.signature list): t =
        BatList.fold_left (fun a c -> join a (alpha c)) Bot cl

    let gamma_if_singleton (t: t): (int * Exprs.const) list =
        match t with
        | Bot -> []
        | BitVec64 pl ->
            BatList.fold_lefti (fun acc_rev idx p ->
                match RedProd64.gamma_if_singleton p with
                | Some c ->
                    (idx, c) :: acc_rev
                | _ -> acc_rev
            ) [] pl |> BatList.rev
        | BitVec32 pl ->
            BatList.fold_lefti (fun acc_rev idx p ->
                match RedProd32.gamma_if_singleton p with
                | Some c ->
                    (idx, c) :: acc_rev
                | _ -> acc_rev
            ) [] pl |> BatList.rev
        | BitVecGeneral (len, pl) ->
            let module I = MaskedInt64(struct let size = len end) in
            let module P = RedProd.Make(I) in
            BatList.fold_lefti (fun acc_rev idx p ->
                match P.gamma_if_singleton p with
                | Some c ->
                    (idx, c) :: acc_rev
                | _ -> acc_rev
            ) [] pl |> BatList.rev
        | Bool bl ->
            ABoolSig.gamma_if_singleton bl
        | Top -> []

    let gamma_size_constraint (max_size: int) (t: t): (int * Exprs.const BatSet.t) list =
        match t with
        | Bot ->
            [(0, BatSet.empty)]
        | BitVec64 pl ->
            BatList.fold_lefti (fun acc_rev idx p ->
                match RedProd64.gamma_size_constraint max_size p with
                | Some set ->
                    (idx, set) :: acc_rev
                | _ -> acc_rev
            ) [] pl |> BatList.rev
        | BitVec32 pl ->
            BatList.fold_lefti (fun acc_rev idx p ->
                match RedProd32.gamma_size_constraint max_size p with
                | Some set ->
                    (idx, set) :: acc_rev
                | _ -> acc_rev
            ) [] pl |> BatList.rev
        | BitVecGeneral (len, pl) ->
            let module I = MaskedInt64(struct let size = len end) in
            let module P = RedProd.Make(I) in
            BatList.fold_lefti (fun acc_rev idx p ->
                match P.gamma_size_constraint max_size p with
                | Some set ->
                    (idx, set) :: acc_rev
                | _ -> acc_rev
            ) [] pl |> BatList.rev
        | Bool bl ->
            ABoolSig.gamma_size_constraint max_size bl
        | Top ->
            []

    exception AllOperandsTop
    exception OperandsBot
    exception OperandsMisType
    exception OperationUnreachable

    let normalize_args (args: (addr * t) list): (addr * t) list =
        let rec find_type_and_dim l =
            match l with
            | [] -> raise AllOperandsTop
            | Bot :: _ -> raise OperandsBot
            | BitVec64 pl :: _ -> (Exprs.BV 64, BatList.length pl)
            | BitVec32 pl :: _ -> (Exprs.BV 32, BatList.length pl)
            | BitVecGeneral (len, pl) :: _ -> (Exprs.BV len, BatList.length pl)
            | Bool bl :: _ -> (Exprs.Bool, ABoolSig.length bl)
            | Top :: tail -> find_type_and_dim tail
        in
        match find_type_and_dim (BatList.map snd args) with
        | (Exprs.BV 64, sig_dim) ->
            BatList.fold_left (fun acc_rev (addr, a) ->
                match a with
                | BitVec64 _  -> (addr, a) :: acc_rev
                | Bot -> raise OperandsBot
                | Top -> (addr, BitVec64 (BatList.make sig_dim RedProd64.top_repr)) :: acc_rev
                | _ -> raise OperandsMisType
                ) [] args |> BatList.rev
        | (Exprs.BV 32, sig_dim) ->
            BatList.fold_left (fun acc_rev (addr, a) ->
                match a with
                | BitVec32 _ -> (addr, a) :: acc_rev
                | Bot -> raise OperandsBot
                | Top -> (addr, BitVec32 (BatList.make sig_dim RedProd32.top_repr)) :: acc_rev
                | _ -> raise OperandsMisType
                ) [] args |> BatList.rev
        | (Exprs.BV general_len, sig_dim) ->
            let module I = MaskedInt64(struct let size = general_len end) in
            let module P = RedProd.Make(I) in
            BatList.fold_left (fun acc_rev (addr, a) ->
                match a with
                | BitVecGeneral (len, x) ->
                    if general_len = len then (addr, a) :: acc_rev
                    else raise OperandsMisType
                | Bot -> raise OperandsBot
                | Top -> (addr, BitVecGeneral (general_len, BatList.make sig_dim P.top_repr)) :: acc_rev
                | _ -> raise OperandsMisType
                ) [] args |> BatList.rev
        | (Exprs.Bool, sig_dim) ->
            BatList.fold_left (fun acc_rev (addr, a) ->
                match a with
                | Bool _ -> (addr, a) :: acc_rev
                | Bot -> raise OperandsBot
                | Top -> (addr, Bool (ABoolSig.top_repr sig_dim)) :: acc_rev
                | _ -> raise OperandsMisType
                ) [] args |> BatList.rev
        | _ -> raise AllOperandsTop

    let forward_bv_un_op (uop: Operators.bv_un_op) (arg0: t): t =
        match arg0 with
        | BitVec64 a0 ->
            BitVec64 (BatList.map (RedProd64.forward_un_op uop) a0)
        | BitVec32 a0 ->
            BitVec32 (BatList.map (RedProd32.forward_un_op uop) a0)
        | BitVecGeneral (len, a0) ->
            let module I = MaskedInt64(struct let size = len end) in
            let module P = RedProd.Make(I) in
            BitVecGeneral (len, BatList.map (P.forward_un_op uop) a0)
        | _ -> Bot (* bad type => empty semantics *)

    let forward_bv_bin_op (bop: Operators.bv_bin_op) (arg0: t) (arg1: t): t =
        match arg0, arg1 with
        | BitVec64 a0, BitVec64 a1 ->
            BitVec64 (BatList.map2 (RedProd64.forward_bin_op bop) a0 a1)
        | BitVec32 a0, BitVec32 a1 ->
            BitVec32 (BatList.map2 (RedProd32.forward_bin_op bop) a0 a1)
        | BitVecGeneral (len, a0), BitVecGeneral (len1, a1) ->
            if len = len1 then
                let module I = MaskedInt64(struct let size = len end) in
                let module P = RedProd.Make(I) in
                BitVecGeneral (len, BatList.map2 (P.forward_bin_op bop) a0 a1)
            else
                raise OperationUnreachable
        | _ -> Bot (* bad type => empty semantics *)
    
    let forward_bool_un_op (uop: Operators.bool_un_op) (arg0: t): t =
        match arg0 with
        | Bool a0 ->
            Bool (ABoolSig.forward_un_op uop a0)
        | _ -> Bot (* bad type => empty semantics *)

    let forward_bool_bin_op (bop: Operators.bool_bin_op) (arg0: t) (arg1: t): t =
        match arg0, arg1 with
        | Bool a0, Bool a1 ->
            Bool (ABoolSig.forward_bin_op bop a0 a1)
        | _ -> Bot (* bad type => empty semantics *)
    
    let fail_not_supported_op_expr (op: Operators.op) (args: t list): 'a =
        failwith (Printf.sprintf "not supported forward operation: operator %s with %d operands"
                (Operators.op_to_string op)
                (BatList.length args)
            )

    let forward_operation (op: Operators.op) (addr: addr) (args: (addr * t) list): t =
        try begin
            match op with
            | Operators.BV_OP Operators.BV_UN_OP uop ->
                let arg0 =
                    match normalize_args args with
                    | (_, arg0) :: [] -> arg0
                    | _ -> fail_not_supported_op_expr op (BatList.map snd args)
                in
                forward_bv_un_op uop arg0
            | Operators.BV_OP Operators.BV_BIN_OP bop ->
                let arg0, arg1 =
                    match normalize_args args with
                    | (_, arg0) :: (_, arg1) :: [] ->
                        (arg0, arg1)
                    | _ -> fail_not_supported_op_expr op (BatList.map snd args)
                in
                forward_bv_bin_op bop arg0 arg1
            | Operators.BOOL_OP Operators.B_UN_OP uop ->
                let arg0 =
                    match normalize_args args with
                    | (_, arg0) :: [] -> arg0
                    | _ -> fail_not_supported_op_expr op (BatList.map snd args)
                in
                forward_bool_un_op uop arg0
            | Operators.BOOL_OP Operators.B_BIN_OP bop ->
                let arg0, arg1 =
                    match normalize_args args with
                    | (_, arg0) :: (_, arg1) :: [] ->
                        (arg0, arg1)
                    | _ -> fail_not_supported_op_expr op (BatList.map snd args)
                in
                forward_bool_bin_op bop arg0 arg1
            | Operators.TRI_OP Operators.ITE ->
                top_repr
            | _ -> fail_not_supported_op_expr op (BatList.map snd args)
        end with
            | OperandsBot -> Bot
            | AllOperandsTop -> Top
            | OperandsMisType -> Bot

    let backward_bv_un_op (uop: Operators.bv_un_op) ((_, post): addr * t) ((addr0, arg0): addr * t): addr * t =
        match post, arg0 with
        | BitVec64 p, BitVec64 a0 ->
            (addr0, BitVec64 (BatList.map2 (RedProd64.backward_un_op uop) p a0))
        | BitVec32 p, BitVec32 a0 ->
            (addr0, BitVec32 (BatList.map2 (RedProd32.backward_un_op uop) p a0))
        | BitVecGeneral (len, p), BitVecGeneral (len1, a0) ->
            if len = len1 then
                let module I = MaskedInt64(struct let size = len end) in
                let module P = RedProd.Make(I) in
                (addr0, BitVecGeneral (len, BatList.map2 (P.backward_un_op uop) p a0))
            else
                raise OperationUnreachable
        | _ ->
            (addr0, bot_repr)

    let backward_bv_bin_op (bop: Operators.bv_bin_op) ((_, post): addr * t) ((addr0, arg0): addr * t) ((addr1, arg1): addr * t): (addr * t) * (addr * t) =
        match post, arg0, arg1 with
        | BitVec64 p, BitVec64 a0, BitVec64 a1 ->
            let (p0, p1) = map3 (RedProd64.backward_bin_op bop) p a0 a1 |> BatList.split in
            ((addr0, BitVec64 p0), (addr1, BitVec64 p1))
        | BitVec32 p, BitVec32 a0, BitVec32 a1 ->
            let (p0, p1) = map3 (RedProd32.backward_bin_op bop) p a0 a1 |> BatList.split in
            ((addr0, BitVec32 p0), (addr1, BitVec32 p1))
        | BitVecGeneral (len, p), BitVecGeneral (len0, a0), BitVecGeneral (len1, a1) ->
            if len = len0 && len0 = len1 then
                let module I = MaskedInt64(struct let size = len end) in
                let module P = RedProd.Make(I) in
                let (p0, p1) = map3 (P.backward_bin_op bop) p a0 a1 |> BatList.split in
                ((addr0, BitVecGeneral (len, p0)), (addr1, BitVecGeneral (len, p1)))
            else
                raise OperationUnreachable
        | _ ->
            (addr0, bot_repr), (addr1, bot_repr)

    let backward_bool_un_op (uop: Operators.bool_un_op) ((addr, post): addr * t) ((addr0, arg0): addr * t): addr * t =
        match post, arg0 with
        | Bool p, Bool a0 ->
            (addr0, Bool (ABoolSig.backward_un_op uop p a0))
        | _ ->
            (addr0, bot_repr)

    let backward_bool_bin_op (bop: Operators.bool_bin_op) ((addr, post): addr * t) ((addr0, arg0): addr * t) ((addr1, arg1): addr * t): (addr * t) * (addr * t) =
        match post, arg0, arg1 with
        | Bool p, Bool a0, Bool a1 ->
            let (p0, p1) = ABoolSig.backward_bin_op bop p a0 a1 in
            ((addr0, Bool p0), (addr1, Bool p1))
        | _ ->
            ((addr0, bot_repr), (addr1, bot_repr))

    let backward_operation (op: Operators.op) (post: addr * t) (args: (addr * t) list): (addr * t) list =
        try begin
            match normalize_args (post :: args) with
            | post :: normalized -> begin
                match op, normalized with
                | Operators.BV_OP Operators.BV_UN_OP uop, arg0 :: [] ->
                    let p0 = backward_bv_un_op uop post arg0 in
                    [p0]
                | Operators.BV_OP Operators.BV_BIN_OP bop, arg0 :: arg1 :: [] ->
                    let (p0, p1) = backward_bv_bin_op bop post arg0 arg1 in
                    [p0; p1]
                | Operators.BOOL_OP Operators.B_UN_OP uop, arg0 :: [] ->
                    let p0 = backward_bool_un_op uop post arg0 in
                    [p0]
                | Operators.BOOL_OP Operators.B_BIN_OP bop, arg0 :: arg1 :: [] ->
                    let (p0, p1) = backward_bool_bin_op bop post arg0 arg1 in
                    [p0; p1]
                | Operators.TRI_OP Operators.ITE, arg0 :: arg1 :: arg2 :: [] ->
                    args
                | _ ->
                    failwith (Printf.sprintf "not supported forward operation: operator %s with %d operands"
                        (Operators.op_to_string op)
                        (BatList.length args)
                    )
            end
            | _ -> raise OperationUnreachable
        end with
            | OperandsBot -> BatList.map (fun (addr, _) -> (addr, Bot)) args
            | AllOperandsTop -> BatList.map (fun (addr, _) -> (addr, Bot)) args
            | OperandsMisType -> BatList.map (fun (addr, _) -> (addr, Bot)) args
end