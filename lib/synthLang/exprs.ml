open Common
open Vocab
open Int64Util
open Operators

exception UndefinedSemantics

type exprtype =
	| Int
	| BV of int
	| String
	| Bool

type const =
	| CInt of int
	| CBV of int * int64
	| CString of string
	| CBool of bool

type const_opt =
	| CDontCare of exprtype
	| CDefined of const

(** program without nonterminal (=complete program) *)
type expr =
	| Param of int * exprtype (* position and type *)
	| Var of string * exprtype (* name and type : only for SMT *)
	| Const of const
	| Function of op * expr list * exprtype

let string_of_type ?(z3=false) ty =
	match ty with
	| Int -> "Int"
	| BV len ->
		Printf.sprintf "(%sBitVec %d)" (if z3 then "_ " else "") len
	| String -> "String"
	| Bool -> "Bool"

let get_param_id (expr: expr): int =
	match expr with
	| Param (i, _) -> i
	| _ -> failwith "get_param_id"

let rec get_params (expr: expr): expr BatSet.t =
	match expr with
	| Param _ -> BatSet.singleton expr 
	| Function (_, exprs, _) ->
		BatList.fold_left (fun acc e -> BatSet.union acc (get_params e)) BatSet.empty exprs 
	| _ -> BatSet.empty

let get_trivial_value (ty: exprtype): const =
	match ty with
	| Int -> CInt 0
	| BV len -> CBV (len, 0L)
	| String -> CString ""
	| Bool -> CBool true

let is_function_expr (expr: expr): bool =
	match expr with
	| Function _ -> true
	| _ -> false

let is_const_expr (expr: expr): bool =
	match expr with
	| Const _ -> true
	| _ -> false

let type_of_const (const: const): exprtype =
	match const with
	| CInt _ -> Int
	| CBV (len, _) -> BV len
	| CString _ -> String
	| CBool _ -> Bool

let type_of_expr (expr: expr): exprtype =
	match expr with
	| Param (_, ty) -> ty
	| Var (_, ty) -> ty
	| Function (_, _, ty) -> ty
	| Const const -> type_of_const const

let _hex_formats: (int64 -> string) array = BatArray.of_list [
	Printf.sprintf "#x%01Lx";
	Printf.sprintf "#x%02Lx";
	Printf.sprintf "#x%03Lx";
	Printf.sprintf "#x%04Lx";
	Printf.sprintf "#x%05Lx";
	Printf.sprintf "#x%06Lx";
	Printf.sprintf "#x%07Lx";
	Printf.sprintf "#x%08Lx";
	Printf.sprintf "#x%09Lx";
	Printf.sprintf "#x%010Lx";
	Printf.sprintf "#x%011Lx";
	Printf.sprintf "#x%012Lx";
	Printf.sprintf "#x%013Lx";
	Printf.sprintf "#x%014Lx";
	Printf.sprintf "#x%015Lx";
	Printf.sprintf "#x%016Lx"
]

let string_of_bv (len: int) (i: int64): string =
	let rec worker (cnt: int) (acc: char list): char list =
		if cnt < len then
			if ((1L %<<% cnt) $&&$ i) = 0L then
				worker (cnt + 1) ('0' :: acc)
			else
				worker (cnt + 1) ('1' :: acc)
		else
			'#' :: 'b' :: acc
	in
	BatString.of_list (worker 0 [])

let string_of_const (const: const): string =
	match const with
	| CInt n -> string_of_int n
	| CBV (len, i) ->
		if len land 3 = 0 then
			_hex_formats.((len asr 2) - 1) i			
		else
			string_of_bv len i
	| CString s -> "\"" ^ s ^ "\""
	| CBool b -> string_of_bool b

let string_of_const_opt (const_opt: const_opt): string =
	match const_opt with
	| CDontCare _ -> "*"
	| CDefined const -> string_of_const const

(* signature = desired input or output list from iospec. e.g.) sig.(0) == a number from first io pair *)
type signature =
	| SigInt of int list
	| SigBV of int * int64 list
	| SigString of string list
	| SigBool of ImmBitVec.t

let sig_of_single_const (c: const): signature =
	match c with
	| CInt i -> SigInt [i]
	| CBV (len, i) -> SigBV (len, [i])
	| CString s -> SigString [s]
	| CBool b -> SigBool (ImmBitVec.of_list [b])

let sig_hd (signature: signature): const =
	match signature with
	| SigInt il -> CInt (BatList.hd il)
	| SigBV (len, il) -> CBV (len, BatList.hd il)
	| SigString sl -> CString (BatList.hd sl)
	| SigBool bl -> CBool (ImmBitVec.mem 0 bl)

let sig_length (signature: signature): int =
	match signature with
	| SigInt il -> BatList.length il
	| SigBV (len, il) -> BatList.length il
	| SigString sl -> BatList.length sl
	| SigBool bl -> ImmBitVec.length bl

let const_list_of_signature (signature: signature): const list =
	match signature with
	| SigInt il -> BatList.map (fun i -> CInt i) il
	| SigBV (len, il) -> BatList.map (fun i -> CBV (len, i)) il
	| SigString sl -> BatList.map (fun s -> CString s) sl
	| SigBool bl -> ImmBitVec.map_as_list (fun _ b -> CBool b) bl

let string_of_signature (signature: signature): string =
	const_list_of_signature signature |> string_of_list string_of_const

let type_of_signature (signature: signature): exprtype =
	match signature with
	| SigInt _ -> Int
	| SigBV (len, _) -> BV len
	| SigString _ -> String
	| SigBool _ -> Bool

let collect_int_list (il: int list) (c: const): int list =
	match c with
	| CInt i -> i :: il
	| _ -> failwith_f "signature_of_const_list(%s in CInt list): kind mismatch" (string_of_const c)

let collect_bv_list (len: int) (il: int64 list) (c: const): int64 list =
	match c with
	| CBV (len', i) ->
		if len = len' then i :: il
		else failwith_f "signature_of_const_list(%d in CBV(%d, _) list: length mismatch" len' len
	| _ -> failwith_f "signature_of_const_list(%s in CInt list): kind mismatch" (string_of_const c)

let collect_str_list (sl: string list) (c: const): string list =
	match c with
	| CString s -> s :: sl
	| _ -> failwith_f "signature_of_const_list(%s in CString list): kind mismatch" (string_of_const c)

let collect_bool_list (bl: bool list) (c: const): bool list =
	match c with
	| CBool b -> b :: bl
	| _ -> failwith_f "signature_of_const_list(%s in CBool list): kind mismatch" (string_of_const c)

let signature_of_const_list (cl: const list): signature =
	match cl with
	| [] -> failwith "empty signature"
	| CInt i :: tail ->
		SigInt (BatList.fold_left collect_int_list [i] tail |> BatList.rev)
	| CBV (len, i) :: tail ->
		SigBV (len, BatList.fold_left (collect_bv_list len) [i] tail |> BatList.rev)
	| CString s :: tail ->
		SigString (BatList.fold_left collect_str_list [s] tail |> BatList.rev)
	| CBool b :: tail ->
		SigBool (BatList.fold_left collect_bool_list [b] tail |> BatList.rev |> ImmBitVec.of_list)

let compare_signature (s1: signature) (s2: signature): int =
	match s1, s2 with
	| SigInt i1, SigInt i2 -> BatList.compare BatInt.compare i1 i2
	| SigInt _, _ -> -1
	| _, SigInt _ -> 1
	| SigBV (len1, b1), SigBV (len2, b2) ->
		let lc = BatInt.compare len1 len2 in
		if lc = 0 then
			BatList.compare BatInt64.compare b1 b2
		else lc
	| SigBV _, _ -> -1
	| _, SigBV _ -> 1
	| SigString s1, SigString s2 -> BatList.compare BatString.compare s1 s2
	| SigString _, _ -> -1
	| _, SigString _ -> 1
	| SigBool b1, SigBool b2 ->
		ImmBitVec.compare b1 b2

module SignatureMap = BatMap.Make(struct
	type t = signature
	let compare = compare_signature
end)

let rec string_of_expr (expr: expr): string =
	match expr with
	| Const const -> string_of_const const
	| Var (id, ty) -> id
	| Param (n, ty) -> Printf.sprintf "arg_%d" n
	| Function (op, exprs, ty) ->
		Printf.sprintf "(%s %s)" (op_to_string op)
			(string_of_list ~first:"" ~last:"" ~sep:" " string_of_expr exprs)

let rec size_of_expr (expr: expr): int =
	match expr with
	| Const _ -> 1
	| Param _ -> 1
	| Var _ -> 1
	| Function (op, exprs, ty) -> List.fold_left (fun size expr -> size + (size_of_expr expr)) 1 exprs

module ExprSigSet = struct
    include BatSet.Make (struct
        type t = expr * signature
        let compare (e1,_) (e2,_) =
            compare e1 e2 (* assumption: e1 = e2 => sig of e1 = sig of e2 *)
    end)

    let to_string ?(first="{") ?(last="}") ?(sep=",") (set: t): string =
        let add_string_of_v (v, _) acc = link_by_sep sep (string_of_expr v) acc in
        first ^ fold add_string_of_v set "" ^ last
end

let expr2const (expr: expr): const =
	match expr with
	| Const const -> const
	| _ -> assert false

let get_op (expr: expr): op =
	match expr with
	| Function(op, _, _) -> op
	| _ -> failwith "get_op"

let get_children (expr: expr): expr list =
	match expr with
	| Function(op, children, _) -> children
	| _ -> failwith "get_children"

let get_bv (const: const): int64 =
	match const with
	| CBV (len, i) -> mask_by_bit_length len i
	| _ -> assert false

let get_string (const: const): string =
	match const with
	| CString s -> s
	| _ -> assert false

let get_int (const: const): int =
	match const with
	| CInt i -> i
	| _ -> assert false

let get_bool (const: const): bool =
	match const with
	| CBool b -> b
	| _ -> assert false

let rec change_param_to_var (param2var: (expr, expr) BatMap.t) (expr: expr): expr =
	match expr with
	| Param _ -> begin
		try
			BatMap.find expr param2var
		with _ ->
			assert false
	end
	| Function (op, exprs, ty) ->
		Function (op, List.map (change_param_to_var param2var) exprs, ty)
	| _ ->
		expr

let sexpstr_of_fun (args_map: (string, expr) BatMap.t) (name: string) (expr: expr): string =
	(* Param _ -> Var _ *)
	let param2var =
		BatMap.foldi (fun id param_expr acc ->
			let ty = type_of_expr param_expr in
			BatMap.add param_expr (Var(id, ty)) acc
		) args_map BatMap.empty
	in
	let expr = change_param_to_var param2var expr in
	let params =
		BatMap.foldi (fun id param_expr acc -> (id, param_expr) :: acc) args_map []
		|> List.sort (fun (_, param_expr1) (_, param_expr2) -> (get_param_id param_expr1) - (get_param_id param_expr2))
		|> List.map (fun (id, param_expr) -> Var(id, type_of_expr param_expr))
	in
	let params_str =
		(List.fold_left (fun acc param ->
			Printf.sprintf "%s (%s %s)" acc (string_of_expr param) (string_of_type (type_of_expr param))
		 ) "" params)
	in
	let ret_type_str = (string_of_type (type_of_expr expr)) in
	Printf.sprintf "(define-fun %s (%s) %s %s)"
		name
		params_str
		ret_type_str
		(string_of_expr expr)

(** helpers for extracting ocaml values from signatures *)
let extract_str_int (values: signature list): (string list * int list) =
	match values with
	| SigString sl :: SigInt il :: _ ->
		(sl, il)
	| _ -> assert false

let extract_str_str (values: signature list): (string list * string list) =
	match values with
	| SigString sl1 :: SigString sl2 :: _ ->
		(sl1, sl2)
	| _ -> assert false

let extract_str_str_int (values: signature list): (string list * string list * int list) = 
	match values with
	| SigString sl1 :: SigString sl2 :: SigInt il :: _ ->
		(sl1, sl2, il)
	| _ -> assert false

let extract_str_int_int (values: signature list): (string list * int list * int list) = 
	match values with
	| SigString sl :: SigInt il1 :: SigInt il2 :: _ ->
		(sl, il1, il2)
	| _ -> assert false

let extract_str_str_str (values: signature list): (string list * string list * string list) = 
	match values with
	| SigString sl1 :: SigString sl2 :: SigString sl3 :: _ ->
		(sl1, sl2, sl3)
	| _ -> assert false

let extract_int_int (values: signature list): (int list * int list) =
	match values with
	| SigInt il1 :: SigInt il2 :: _ ->
		(il1, il2)
	| _ -> assert false

(* string -> signature list -> signature *)
let fun_apply_signature (op: op) (values: signature list): signature =
	match op with
	| GENERAL_FUNC op_str -> begin match op_str with
		(** STRING theory **)
		| "str.len" -> begin
			match values with
			| SigString sl :: _ ->
				SigInt (BatList.map BatString.length sl)
			| _ ->
				assert false
		end
		| "str.to.int" -> begin
			match values with
			| SigString sl :: _ -> begin try
			    SigInt (BatList.map int_of_string sl)
        with Failure _ ->
          raise UndefinedSemantics
        end
			| _ ->
				assert false
		end
		| "int.to.str" -> begin
			match values with
			| SigInt il :: _ ->
				SigString (BatList.map string_of_int il)
			| _ -> assert false	
		end
		| "str.at" -> begin
			let (strs, nums) = extract_str_int values in
			SigString (List.map2 (fun str num ->
					Printf.sprintf
						"%c"
						(if 0 <= num && num < BatString.length str then
							str.[num]
						else
							raise UndefinedSemantics)
				) strs nums)
		end
		| "str.++" -> begin
			let (str1s, str2s) = extract_str_str values in
			SigString (List.map2 (^) str1s str2s) 
		end
		| "str.contains" -> begin
			let (str1s, str2s) = extract_str_str values in
			SigBool (List.map2 BatString.exists str1s str2s |> ImmBitVec.of_list)
		end
		| "str.prefixof" -> begin
			let (str1s, str2s) = extract_str_str values in
			SigBool (List.map2 (BatString.starts_with) str1s str2s |> ImmBitVec.of_list)
		end
		| "str.suffixof" -> begin
			let (str1s, str2s) = extract_str_str values in
			SigBool (List.map2 (BatString.ends_with) str1s str2s |> ImmBitVec.of_list)
		end
		| "str.indexof" -> begin
			let (str1s, str2s, num1s) = extract_str_str_int values in
			SigInt (map3 (fun str1 num1 str2 ->
          try BatString.find_from str1 num1 str2
          with
            | Not_found -> -1
            | Invalid_argument _ -> raise UndefinedSemantics) str1s num1s str2s
      )
		end
		| "str.replace" -> begin
			let (str1s, str2s, str3s) = extract_str_str_str values in
			SigString (map3 (fun str1 str2 str3 -> (Str.replace_first (Str.regexp_string str2) str3 str1)) str1s str2s str3s )
		end
		| "str.substr" -> begin
			let (str1s, num1s, num2s) = extract_str_int_int values in
			SigString (
				map3 (fun str1 num1 num2 ->
          if String.length str1 - num1 < num2 then raise UndefinedSemantics
          else
					  let num2 = min (String.length str1 - num1) num2 in
					  try BatString.sub str1 num1 num2 with Invalid_argument _ -> ""
				) str1s num1s num2s
			)
		end
		(** LIA theory **)
		| "+" ->
			let (num1s, num2s) = extract_int_int values in
			SigInt (List.map2 (+) num1s num2s)
		| "-" ->
			let (num1s, num2s) = extract_int_int values in
			SigInt (List.map2 (-) num1s num2s)
		| "*" ->
			let (num1s, num2s) = extract_int_int values in
			SigInt (List.map2 ( * ) num1s num2s)
		| "/" ->
			let (num1s, num2s) = extract_int_int values in
			SigInt (List.map2 (/) num1s num2s)
		| "%" ->
			let (num1s, num2s) = extract_int_int values in
			SigInt (List.map2 (mod) num1s num2s)
		| _ -> failwith ("not supported operator: " ^ (op_to_string op))
	end
	| TRI_OP ITE -> begin
		match values with
		| SigBool bools :: SigInt sig1 :: SigInt sig2 :: _ ->
			SigInt (map3 (fun bool const1 const2 -> if bool then const1 else const2) (ImmBitVec.to_list bools) sig1 sig2)
		| SigBool bools :: SigBV (len1, sig1) :: SigBV (len2, sig2) :: _ ->
			if len1 = len2 then
				SigBV (len1, map3 (fun bool const1 const2 -> if bool then const1 else const2) (ImmBitVec.to_list bools) sig1 sig2)
			else
				assert false
		| SigBool bools :: SigBool sig1 :: SigBool sig2 :: _ ->
			SigBool (ImmBitVec.logor (ImmBitVec.logand bools sig1) (ImmBitVec.logand (ImmBitVec.lognot bools) sig2))
		| SigBool bools :: SigString sig1 :: SigString sig2 :: _ ->
			SigString (map3 (fun bool const1 const2 -> if bool then const1 else const2) (ImmBitVec.to_list bools) sig1 sig2)
		| _ ->
			assert false
	end
	| GEN_CMP_OP cmp_op -> begin
		match cmp_op with
		| CMP_EQ -> begin
			match values with
			| sig1 :: sig2 :: _ ->
				SigBool (List.map2 (fun const1 const2 -> (Stdlib.compare const1 const2) = 0) (const_list_of_signature sig1) (const_list_of_signature sig2) |> ImmBitVec.of_list)
			| _ ->
				assert false
		end
		| CMP_LT -> begin
			match values with
			| SigInt sig1 :: SigInt sig2 :: _ ->
				SigBool (List.map2 (<) sig1 sig2 |> ImmBitVec.of_list)
			| _ ->
				assert false
		end
		| CMP_GT -> begin
			match values with
			| SigInt sig1 :: SigInt sig2 :: _ ->
				SigBool (List.map2 (>) sig1 sig2 |> ImmBitVec.of_list)
			| _ ->
				assert false
		end
		| CMP_LE -> begin
			match values with
			| SigInt sig1 :: SigInt sig2 :: _ ->
				SigBool (List.map2 (<=) sig1 sig2 |> ImmBitVec.of_list)
			| _ ->
				assert false
		end
		| CMP_GE -> begin
			match values with
			| SigInt sig1 :: SigInt sig2 :: _ ->
				SigBool (List.map2 (>=) sig1 sig2 |> ImmBitVec.of_list)
			| _ ->
				assert false
		end
	end
	(** Bool theory **)
	| BOOL_OP B_BIN_OP B_AND -> begin
		match values with
		| SigBool bools1 :: SigBool bools2 :: _ ->
			SigBool (ImmBitVec.logand bools1 bools2)
		| _ ->
			assert false
	end
	| BOOL_OP B_BIN_OP B_OR -> begin
		match values with
		| SigBool bools1 :: SigBool bools2 :: _ ->
			SigBool (ImmBitVec.logor bools1 bools2)
		| _ ->
			assert false
	end
	| BOOL_OP B_BIN_OP B_XOR -> begin
		match values with
		| SigBool bools1 :: SigBool bools2 :: _ ->
			SigBool (ImmBitVec.logxor bools1 bools2)
		| _ ->
			assert false
	end
	| BOOL_OP B_UN_OP B_NOT -> begin
		match values with
		| SigBool bools1 :: _ ->
			SigBool (ImmBitVec.lognot bools1)
		| _ -> assert false
	end
	(** BV theory **)
	| BV_OP BV_UN_OP bv_un_op -> begin
		let uf bit_length =
			let module I = MaskedInt64(struct let size = bit_length end) in
			match bv_un_op with
			| BV_NEG -> I.neg
			| BV_NOT -> I.lognot
		in
		match values with
		| SigBV (bit_length, s1) :: [] ->
			SigBV (bit_length, BatList.map (uf bit_length) s1)
		| _ -> failwith (Printf.sprintf "bitvec unary operator needs exactly 1 bitvec operand but passed %s" (string_of_list string_of_signature values))
	end
	| BV_OP BV_BIN_OP bv_bin_op -> begin
		let bf bit_length =
			let module I = MaskedInt64(struct let size = bit_length end) in
			match bv_bin_op with
			| BV_ADD -> I.add
			| BV_SUB -> I.sub
			| BV_MUL -> I.mul
			| BV_UDIV -> I.unsigned_div
			| BV_SDIV -> I.signed_div
			| BV_UREM -> I.unsigned_rem
			| BV_SREM -> I.signed_rem
			| BV_AND -> I.logand
			| BV_OR -> I.logor
			| BV_XOR -> I.logxor
			| BV_ASHR -> begin fun num1 num2 ->
				let count = BatOption.default I.bit_length (I.unsigned_to_int num2) in
				if count >= I.bit_length then
					if I.signed_compare num1 0L < 0 then I.minus_one
					else 0L
				else
					I.arith_shift_right num1 count
			end
			| BV_LSHR -> begin fun num1 num2 ->
				let count = BatOption.default I.bit_length (I.unsigned_to_int num2) in
				if count >= I.bit_length then 0L
				else I.logical_shift_right num1 count
			end
			| BV_SHL -> begin fun num1 num2 ->
				let count = BatOption.default I.bit_length (I.unsigned_to_int num2) in
				if count >= I.bit_length then 0L
				else I.shift_left num1 count
			end
		in
		match values with
		| SigBV (len1, s1) :: SigBV (len2, s2) :: [] ->
			if len1 = len2 then
				SigBV (len1, BatList.map2 (bf len1) s1 s2)
			else
				failwith (Printf.sprintf "bv length mismatch: %s bv%d bv%d" (Operators.op_to_string op) len1 len2)
		| _ -> failwith (Printf.sprintf "bitvec binary operator needs exactly 2 bitvec operands but passed %s" (string_of_list string_of_signature values))
	end
	| BV_OP BV_CMP_OP bv_cmp_op -> begin
		let cf len =
			let module I = MaskedInt64(struct let size = len end) in
			match bv_cmp_op with
			| BV_ULE -> fun x y -> I.unsigned_compare x y <= 0
			| BV_ULT -> fun x y -> I.unsigned_compare x y < 0
			| BV_SLE -> fun x y -> I.signed_compare x y <= 0
			| BV_SLT -> fun x y -> I.signed_compare x y < 0
		in
		match values with
		| SigBV (len1, s1) :: SigBV (len2, s2) :: [] ->
			if len1 = len2 then
				SigBool (BatList.map2 (cf len1) s1 s2 |> ImmBitVec.of_list)
			else
				failwith (Printf.sprintf "bv length mismatch: %s bv%d bv%d" (Operators.op_to_string op) len1 len2)
		| _ -> failwith "bitvec comparison operator needs exactly 2 bitvec operands"
	end (* end of BV_OP *)

(* param_valuation: (int, const list) BatMap.t *)
(* ret type: const list *)
let rec evaluate_expr (spec_length: int) (param_valuation: (int, signature) BatMap.t) (expr: expr): signature =
	match expr with 
	| Const const -> begin
		match const with
		| CInt i -> SigInt (BatList.make spec_length i)
		| CBV (len, i) -> SigBV (len, (BatList.make spec_length i))
		| CString s -> SigString (BatList.make spec_length s)
		| CBool b -> SigBool (ImmBitVec.of_list (BatList.make spec_length b))
	end
	| Param (pos, ty) -> begin
		try BatMap.find pos param_valuation with _ -> assert false
	end
	| Function (op, exprs, ty) ->
		let values = List.map (evaluate_expr spec_length param_valuation) exprs in
		fun_apply_signature op values
	| _ ->
		failwith_f "evalute_expr to Var(%s): Var is only for SMT solver" (string_of_expr expr)

let spec_to_param_map (spec: (const list * 'a) list): (int, signature) BatMap.t =
	BatList.map fst spec
	|> BatList.transpose
	|> zip_with_index
	|> BatList.map (map_snd signature_of_const_list)
	|> BatList.to_seq |> BatMap.of_seq

let compute_signature (spec: (const list * 'a) list) (expr: expr): signature =
	try
		evaluate_expr (BatList.length spec) (spec_to_param_map spec) expr
	with _ ->
		raise UndefinedSemantics

