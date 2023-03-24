open Sexplib
open Z3

open Common
open Vocab
open SynthLang.Exprs
open SexpUtil

let z3_solving_time = ref 0.
let z3_solving_count = ref 0
let attribute_prefix = "__a"

let smt_check ?(timeout_opt: int option = None) (smt_str: string): Solver.status * Solver.solver =
	let ctx =
		Z3.mk_context (
			("model", "true") ::
			("proof", "false") ::
			(match timeout_opt with
				| None -> []
				| Some timeout -> [("timeout", string_of_int timeout)]
			)
		)
	in
	let exprsMT =
		try
			Z3.SMT.parse_smtlib2_string ctx smt_str [] [] [] []
		with Z3.Error msg -> begin
			Logger.g_error_f "Z3 error in generating exprsMT:";
			Logger.g_with_increased_depth (fun () ->
				Logger.g_error smt_str
			);
			raise (Z3.Error msg)
		end
	in
	let sat = Z3.AST.ASTVector.to_expr_list exprsMT in
	let solver = (Z3.Solver.mk_solver ctx None) in
	Z3.Solver.add solver sat;
	let q =
		try
			Z3.Solver.check solver []
		with Z3.Error msg -> begin
			Logger.g_error_f "Z3 error in Z3 solving:";
			Logger.g_with_increased_depth (fun () ->
				Logger.g_error smt_str
			);
			raise (Z3.Error msg)
		end
	in
	(q, solver)

(* return unsat cores as indices of assertions *)
let get_unsat_core ?(timeout: int = 10000) (smt_str: string): int list =
	let start_time = Unix.gettimeofday() in
	let ctx =
		Z3.mk_context [
			("model", "true");
			("proof", "true");
			("unsat_core", "true");
			("timeout", string_of_int timeout)
		]
	in
	let exprsMT = Z3.SMT.parse_smtlib2_string ctx smt_str [] [] [] [] in
	let sat = Z3.AST.ASTVector.to_expr_list exprsMT in
	let solver = (Z3.Solver.mk_solver ctx None) in
	let params =
		List.map (fun i ->
			Z3.Boolean.mk_const_s ctx (Printf.sprintf "%s%d" attribute_prefix i)   
		) (BatList.range 0 `To ((BatList.length sat) - 1))  
	in 
	let _ =
		Z3.Solver.assert_and_track_l solver sat params
	in
  	let q = (Z3.Solver.check solver []) in
	let solving_time = Unix.gettimeofday() -. start_time in
	z3_solving_time := !z3_solving_time +. solving_time;
	incr z3_solving_count;
	Logger.g_debug_lazy (fun () -> (Printf.sprintf "Accumulated Z3 solving time: %f / count: %d = average time: %f" !z3_solving_time !z3_solving_count (!z3_solving_time /. (float_of_int !z3_solving_count))));
	match q with
	| UNSATISFIABLE -> 
		let unsat_core_exprs = Z3.Solver.get_unsat_core solver in 
		BatList.map (fun unsat_core_expr ->
			let expr_str =  Z3.Expr.to_string unsat_core_expr in
			let id = BatString.lchop ~n:(String.length attribute_prefix) expr_str in  
			try int_of_string id 
			with _ -> failwith expr_str 
		) unsat_core_exprs
  | _ -> [] 
