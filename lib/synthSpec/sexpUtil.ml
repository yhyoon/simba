open Sexplib

open Common
open Vocab
open SynthLang

let rec string_of_sexp (sexp: Sexp.t): string = 
	match sexp with
	| Sexp.List sexps ->
        string_of_list ~first:"[" ~sep:" " ~last:"]" string_of_sexp sexps
	| Sexp.Atom s ->
        Sexp.to_string sexp

(* return: (Sexp.t list) list (without the first atom) *)
let filter_sexps_for (tag: string) (sexps: Sexp.t list): Sexp.t list list = 
	BatList.fold_left (fun acc sexp ->
		match sexp with
        | Sexp.List (head :: tail) ->
			if String.equal (Sexp.to_string head) tag then
				tail :: acc
			else
				acc
        | _ -> acc
	) [] sexps |> BatList.rev

let int_of_sexp_opt (sexp: Sexp.t): int option = 
	let s =
		match sexp with
		| Sexp.List sexps -> (* e.g., (- 1) -> List [Atom "-"; Atom "1"] *)
			string_of_list ~sep:"" string_of_sexp sexps
		| Sexp.Atom s ->
		s
	in
	try
		Some (int_of_string s)
	with _ ->
		None

let sexp_to_const (sexp: Sexp.t): Exprs.const =
	match int_of_sexp_opt sexp with 
	| Some n -> CInt n
	| None ->
		let str = Sexp.to_string sexp in 
		if (BatString.equal str "true") then CBool true
		else if (BatString.equal str "false") then CBool false
		else if (BatString.starts_with str "#x") then
			let len = BatString.length str in
			CBV ((len - 2) * 4, Int64.of_string ("0" ^ (BatString.lchop ~n:1 str)))
		else if (BatString.starts_with str "#u") then 
			let len = BatString.length str in
			CBV ((len - 2) * 4, Int64.of_string ("0" ^ (BatString.lchop ~n:1 str)))
		else if (BatString.starts_with str "#b") then 
			let len = BatString.length str in
			CBV (len - 2, Int64.of_string ("0" ^ (BatString.lchop ~n:1 str)))
		else if (str.[0] = '\"') then
			CString (BatString.replace_chars (function '\"' -> "" | ';' -> "" | c -> BatString.make 1 c) str)
		else
			failwith (Printf.sprintf "error : sexp_to_const: %s\n" str)

let sexp_to_type (sexp: Sexp.t): Exprs.exprtype =
	match sexp with
	| Sexp.List (Sexp.Atom "BitVec" :: Sexp.Atom num_str :: [])
	| Sexp.List (_ :: Sexp.Atom "BitVec" :: Sexp.Atom num_str :: []) ->
		BV (int_of_string num_str)
	| Sexp.Atom "Int" -> Int
	| Sexp.Atom "String" -> String
	| Sexp.Atom "Bool" -> Bool
	| _ -> failwith (Printf.sprintf "sexp_to_type " ^ string_of_sexp sexp)