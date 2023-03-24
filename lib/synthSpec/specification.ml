open Sexplib
open Z3

open Common
open Vocab
open SynthLang.Exprs
open SexpUtil

exception UnknownModel
exception SolutionFound of expr 

(* oracle expr with a given function name and quantified variables  *)
let oracle_expr = ref (Const (CInt 0))
(* oracle expr only with sygus builtins and parameter variables  *)
let oracle_expr_resolved = ref (Const (CInt 0))

type one_iospec = const list * const_opt
type iospec = one_iospec list

(* spec for programming-by-example *)
type t = iospec

let is_pbe_only(): bool = Stdlib.compare !oracle_expr (Const (CInt 0)) = 0

let empty_spec = []

let is_full_spec (iospec: iospec) =
	iospec |>
	BatList.map snd |>
	BatList.for_all (function CDefined _ -> true | _ -> false)

let to_verfiable_spec (iospec: iospec): (const list * const) list =
	BatList.filter_map (function
			| (input_spec, CDefined output_spec) ->
				Some (input_spec, output_spec)
			| _ -> None
		) iospec

let add_io_spec (inputs, output) spec = 
	if (List.mem (inputs, output) spec) then spec 
	else 
		spec @ [(inputs, output)]
	(* ((inputs, output) :: spec)  *)

let string_of_io_spec spec = 
	string_of_list (fun (inputs, output) ->
		Printf.sprintf "i:%s -> o:%s"
		(string_of_list string_of_const inputs) 
		(string_of_const_opt output) 
	) spec 

let signature_of_spec spec =
	if is_full_spec spec then
		spec |>
		to_verfiable_spec |>
		BatList.map snd |>
		signature_of_const_list
	else
		invalid_arg "partial spec cannot be signature"

let signature_of_output_spec output_specs =
	output_specs |>
	BatList.map (function Some c -> c | _ -> invalid_arg "partial spec cannot be signature") |>
	signature_of_const_list

(* Using Z3 OCaml API *)
let rec verify (additional_constraints: SpecDiversity.verification_constraints) (sol: expr) (spec: iospec): (one_iospec * SpecDiversity.verification_constraints) option =
	let start = Sys.time () in 
	(* no oracle - pbe *)
	if is_pbe_only() then None
	else
		let params = get_params !oracle_expr_resolved in
		let output_expr_str = string_of_expr !oracle_expr_resolved in
		let params_str_list_rev =
			BatSet.fold (fun param acc_rev ->
				let decl_str = Printf.sprintf "(declare-const %s %s)"
					(string_of_expr param)
					(string_of_type ~z3:true (type_of_expr param))
				in
				decl_str::acc_rev
			) params []
  		in
		let params_str = string_of_list ~first:"" ~last:"" ~sep:"\n" identity (BatList.rev params_str_list_rev) in
		let (diversity_constraint_name_and_str_opt, additional_constraint_str, next_additional_constraints) =
			SpecDiversity.process_verification_constraints additional_constraints (to_verfiable_spec spec) params output_expr_str
		in
		let diversity_constraint_str_opt =
			match diversity_constraint_name_and_str_opt with
			| Some (name, str) -> begin
				Logger.g_info_f "diversity constraint %s applied" name;
				Logger.g_with_increased_depth (fun () ->
					Logger.g_debug str;
				);
				Some str
			end
			| None -> None
		in
		let str =
			Printf.sprintf "%s\n(assert (not (= %s %s)))\n%s"
				params_str
				output_expr_str (string_of_expr sol)
				(string_of_list ~first:"" ~last:"" ~sep:"\n" identity
					((BatOption.map_default (fun x -> [x]) [] diversity_constraint_str_opt) @
						additional_constraint_str))
		in
		let _ =
			Logger.g_debug "query cex to solver:";
			Logger.g_with_increased_depth (fun () ->
				Logger.g_debug str
			)
		in
    	let (q, solver) = Z3interface.smt_check str in
		let _ = 
			Global.tick_solver_call (Sys.time() -. start) Global.t
		in
		match q with
		| UNSATISFIABLE -> begin
			match diversity_constraint_name_and_str_opt with
			| Some (divers_name, divers_str) -> begin
				Logger.g_info_f "used diversity constraint(%s) maybe unavailable, re-verify with next trials" divers_name;
				verify next_additional_constraints sol spec
			end
			| None -> begin
				if next_additional_constraints.avoid_existing then begin
					Logger.g_info "output distinction constraint maybe unavailable, retry with turning off";
					verify {next_additional_constraints with avoid_existing = false} sol spec
				end
				else None
			end
		end
		| UNKNOWN -> raise UnknownModel
		| SATISFIABLE -> begin
			let m = Z3.Solver.get_model solver in
			match m with
			| None -> assert false
			| Some m ->
				let _ = Logger.g_debug_lazy (fun () -> Z3.Model.to_string m) in 
				let decls = Z3.Model.get_decls m in
				let cex_input: const list =
					let m: (string, const) BatMap.t =
						List.fold_left (fun acc decl ->
							let symbol = Z3.FuncDecl.get_name decl in
							let value : const =
							let exp_opt = Z3.Model.get_const_interp m decl in
							match exp_opt with
							| None -> raise UnknownModel
							| Some expr -> sexp_to_const (Sexp.Atom (Z3.Expr.to_string expr))
							in
							BatMap.add (Z3.Symbol.to_string symbol) value acc
						) BatMap.empty decls
					in
					let _ =
						if BatMap.is_empty m then
						failwith "Z3 returns the empty model. Check out if (DY)LD_LIBRARY_PATH includes a path to the Z3 folder."
					in
					let param_ids =
						List.map
							(fun i -> string_of_expr (Param (i, Bool))) (* Bool is dummy (not used in string_of_expr) *)
							(BatList.range 0 `To ((BatMap.cardinal m) - 1))
					in
					List.map (fun x -> try BatMap.find x m with Not_found -> assert false) param_ids
				in
				let sol_output_opt =
					try
						Some (
							(* CInt 0 = placeholder *)
							compute_signature [(cex_input, CInt 0)] sol |> sig_hd
							)
					with UndefinedSemantics -> None
				in
				try
  					let cex_output = compute_signature [(cex_input, CInt 0)] !oracle_expr_resolved |> sig_hd in
					Logger.g_debug_f "sol:%s" (BatOption.map_default string_of_const "N/A" sol_output_opt);
					Logger.g_debug_f "oracle:%s" (string_of_const cex_output);
					Logger.g_debug_f "cex : %s" (string_of_io_spec [(cex_input, CDefined cex_output)]);
					BatOption.may (fun so ->
						if (Stdlib.compare so cex_output) = 0 then
							failwith (Printf.sprintf "solution = oracle: %s = %s" (string_of_const so) (string_of_const cex_output))
						else ()
						) sol_output_opt;
					Some ((cex_input, CDefined cex_output), next_additional_constraints)
				with UndefinedSemantics -> begin
					Logger.g_error_f "Z3 returned invalid cex, add to forbidden list and retry: %s" (string_of_list string_of_const cex_input);
					verify {next_additional_constraints with forbidden_inputs = cex_input :: additional_constraints.forbidden_inputs} sol spec
				end
		end

let add_trivial_examples (grammar: SynthLang.Grammar.grammar) (spec: t): t =
	let _ = assert (is_function_expr !oracle_expr) in
	let _ = assert (is_function_expr !oracle_expr_resolved) in 
	let trivial_sol = 
		Const (get_trivial_value (SynthLang.Grammar.type_of_nt SynthLang.Grammar.start_nt))
		(* List.find (fun (nt, r) ->                                                 *)
		(* 	(SynthLang.Grammar.NTNode.equal SynthLang.Grammar.start_nt nt) && (SynthLang.Grammar.is_param_rule r) *)
		(* ) (SynthLang.Grammar.get_nt_rule_list grammar) |> snd |> SynthLang.Grammar.expr_of_rewrite    *)
	in
	match verify SpecDiversity.empty_verification_constraints trivial_sol spec with 
	| None -> raise (SolutionFound trivial_sol)  
	| Some (cex, _) -> 
		let _ = assert (not (List.mem cex spec)) in  
		(cex :: spec)
	(* let inputs =                                                                     *)
	(* 	let children = get_children !oracle_expr in                                    *)
	(* 	List.map (fun e -> get_trivial_value (type_of_expr e)) children    *)
	(* in                                                                               *)
	(* let output =                                                                     *)
	(* 	compute_signature [(inputs, CInt 0)] !oracle_expr_resolved               *)
	(* in                                                                               *)
	(* ((inputs, List.hd output) :: spec) *)
