open Sexplib
open Z3
open Unix

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

(* 
sat
(model 
  (define-fun num () (_ BitVec 64)
    #x083126ea6f1a0223)
  (define-fun den () (_ BitVec 64)
    #xffffffffffff8000)
)
*)
let readSMTResult smt_str_for_cli result_lines =
	match result_lines with
	| [] ->
		failwith "Z3 returned empty result"
	| "unsat" :: _ ->
		None
	| _ :: lines ->
		let file' = ".simba_temp" ^ "_" ^ (string_of_int (Random.int 1000)) in
  	let escaped_lines = 
  		BatList.map (fun line -> 
  			BatString.fold_left (fun (opened, acc) c ->
  				if (c = '\"') then
  					if not opened then 
  						(true, acc ^ (BatString.of_char c) ^ ";")
  					else  
  						(false, acc ^ (BatString.of_char c))
  				else 
  					(opened, acc ^ (BatString.of_char c))
  			) (false, "") line |> snd 
  		) lines
  	in
  	let _ = write_lines escaped_lines file' in  
  	let sexps = Sexp.load_sexps file' in
  	let _ = Unix.unlink file' in
		try
			(* [ *)
			(*   [ *)
			(*     [ define-fun arg_1 [] [ _ BitVec 64] #x8000000000000000] *)
			(*     [ define-fun arg_0 [] [ _ BitVec 64] #x8000000000000000]*)
			(*   ] *)
			(* ] *)
			(* let _ = prerr_endline (string_of_sexp (Sexp.List sexps)) in  *)
  		let sexps =
				match (BatList.hd sexps) with 
				| Sexp.List lst -> lst 
				| _ -> assert false 
			in
			(* let _ = prerr_endline (string_of_sexp (Sexp.List sexps)) in *)
  		let maps = filter_sexps_for "define-fun" sexps in 
  		Some 
    		(BatList.fold_left  
    			(fun acc map ->
  					let lv_str = string_of_sexp (BatList.nth map 0) in 
  					let const = sexp_to_const (BatList.nth map 3) in
						BatMap.add lv_str const acc  
  				) BatMap.empty maps 
    		)
		with _ ->
			failwith (Printf.sprintf "WARNING: Errors in the SMT formula!\n%s\n" smt_str_for_cli) 
				
let cli_check_get_model smt_str =
	let smt_str_for_cli =
		smt_str ^ "\n(check-sat)\n(get-model)\n"
	in
	
	let (z3_stdout, z3_stdin) = Unix.open_process (BatOption.default "z3" Global.t.cli_options.z3cli ^ " -smt2 -in") in
	let _ =
		output_string z3_stdin smt_str_for_cli
	in
	let result_lines =
		let rec loop acc =
			try
				let acc = input_line z3_stdout :: acc in
				loop acc
			with End_of_file -> begin
				close_in z3_stdout;
				BatList.rev acc
			end
		in
		loop []
	in
	let proc_status = Unix.close_process (z3_stdout, z3_stdin) in
	match proc_status with
	| WEXITED 127 ->
		failwith "Failed to run Z3. Check out if Z3 is on the working path."
	| WEXITED 0 ->
		readSMTResult smt_str_for_cli result_lines
	| WEXITED err_code ->
		failwith ("Z3 failed with an error code " ^ (string_of_int err_code))
  | WSIGNALED n ->
		failwith ("Z3 was killed by a signal " ^ (string_of_int n))
	| WSTOPPED n ->
		failwith ("Z3 was stopped by a signal " ^ (string_of_int n))
