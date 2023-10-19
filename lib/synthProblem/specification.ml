(**
	*	Representation of SyGuS Problem - Semantic Part
  *)
open Sexplib
open Z3

open Common
open Vocab
open SynthLang.Exprs
open SexpUtil

exception UnknownModel

(** PBE Part *)
type ex_input = const list
type ex_output = const
type ex_io = ex_input * ex_output

type t = {
	spec_pbe: ex_io list;

	(** oracle condition*)
	spec_oracle_expr: expr option; (* oracle expr with a given function name and quantified variables  *)
	spec_oracle_expr_resolved: expr option; (* oracle expr only with sygus builtins and parameter variables  *)

	(* maybe extended... to logic formula and more *)
}

let is_pbe_only (t: t): bool = BatOption.is_none t.spec_oracle_expr

let empty_spec: t = {
	spec_pbe = [];
	spec_oracle_expr = None;
	spec_oracle_expr_resolved = None;
}

let string_of_ex_io ex_io =
	let (ex_input, ex_output) = ex_io in
	Printf.sprintf "i:%s -> o:%s"
		(string_of_list string_of_const ex_input) 
		(string_of_const ex_output) 

let add_ex_io (ex_input, ex_output) spec = 
	if (List.mem (ex_input, ex_output) spec.spec_pbe) then spec
	else 
		{spec with spec_pbe = spec.spec_pbe @ [(ex_input, ex_output)]}

let string_of_ex_io_list ex_io_list = 
	string_of_list (fun (ex_input, ex_output) ->
		Printf.sprintf "i:%s -> o:%s"
		(string_of_list string_of_const ex_input) 
		(string_of_const ex_output) 
	) ex_io_list

let add_oracle_spec oracle_expr oracle_expr_resolved spec =
	match spec.spec_oracle_expr, spec.spec_oracle_expr_resolved with
	| None, None -> {
		spec with
	    spec_oracle_expr = Some oracle_expr;
			spec_oracle_expr_resolved = Some oracle_expr_resolved;
		}
	| _ -> raise (Invalid_argument "add_oracle_spec: multiple oracle exprs")

type counter_example =
  | CexIO of ex_io
	(* maybe extended input and logical formula... etc. *)

(* Using Z3 OCaml API *)
let rec verify (additional_constraints: SpecDiversity.verification_constraints) (sol: expr) (spec: t): (counter_example * SpecDiversity.verification_constraints) option =
	let start = Sys.time () in 
	(* no oracle - pbe *)
	if is_pbe_only spec then None
	else
		let oracle_expr_resolved = BatOption.get spec.spec_oracle_expr_resolved in
		let params = get_params oracle_expr_resolved in
		let output_expr_str = string_of_expr oracle_expr_resolved in
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
			SpecDiversity.process_verification_constraints additional_constraints spec.spec_pbe params output_expr_str
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
							compute_signature [cex_input] sol |> sig_hd
							)
					with UndefinedSemantics -> None
				in
				try
  				let cex_output = compute_signature [cex_input] (BatOption.get spec.spec_oracle_expr_resolved) |> sig_hd in
					Logger.g_debug_f "sol:%s" (BatOption.map_default string_of_const "N/A" sol_output_opt);
					Logger.g_debug_f "oracle:%s" (string_of_const cex_output);
					Logger.g_debug_f "cex : %s" (string_of_ex_io (cex_input, cex_output));
					BatOption.may (fun so ->
						if (Stdlib.compare so cex_output) = 0 then
							failwith (Printf.sprintf "solution = oracle: %s = %s" (string_of_const so) (string_of_const cex_output))
						else ()
						) sol_output_opt;
					Some (CexIO (cex_input, cex_output), next_additional_constraints)
				with UndefinedSemantics -> begin
					Logger.g_error_f "Z3 returned invalid cex, add to forbidden list and retry: %s" (string_of_list string_of_const cex_input);
					verify {next_additional_constraints with forbidden_inputs = cex_input :: additional_constraints.forbidden_inputs} sol spec
				end
		end
