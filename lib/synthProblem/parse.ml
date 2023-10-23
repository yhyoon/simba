open Sexplib
open Common
open Vocab
open SynthLang
open Operators
open Exprs
open Grammar

type parse_result = {
	macro_instantiator: (op, expr) BatMap.t;
	target_function_name: op;
	args_map: (string, expr) BatMap.t;
	grammar: (non_terminal, rewrite BatSet.t) BatMap.t;
	forall_var_map: (string, expr) BatMap.t;
	spec_total: Specification.t;
}

let debug_string_of_sexp (sexp: Sexp.t): string =
	match sexp with
	| Sexp.List _ ->
		"L" ^ SexpUtil.string_of_sexp sexp
	| Sexp.Atom _ ->
		"A:" ^ SexpUtil.string_of_sexp sexp

let rec sexp_to_expr (sexp: Sexp.t) (args_map: (string, expr) BatMap.t): expr =
	match sexp with
	| Sexp.List sexps' ->
		let _ = assert ((BatList.length sexps') >= 1) in  
		let op = Sexp.to_string (BatList.hd sexps') |> string_to_op in
		let children =
			BatList.map (fun sexp' -> sexp_to_expr sexp' args_map) (BatList.tl sexps')
		in
		let expr_ty =
			ret_type_of_func_rewrite op (BatList.map expr_rewrite children)
		in 
		Function (op, children, expr_ty)
	| Sexp.Atom _ -> begin
		let id = Sexp.to_string sexp in
		try
			BatMap.find id args_map
		with Not_found ->
			Const (SexpUtil.sexp_to_const sexp)
	end

let rec sexp_to_rule (nts: non_terminal BatSet.t) (sexp: Sexp.t) (args_map: (string, expr) BatMap.t): rewrite = 
	match sexp with
	| Sexp.List sexps' ->
		let _ = assert ((BatList.length sexps') >= 1) in  
		let op_str = Sexp.to_string (BatList.hd sexps') in
		let sexps' = BatList.tl sexps' in 
		let children =
			BatList.map (fun sexp' -> sexp_to_rule nts sexp' args_map) sexps'
		in
		normalized_func_rewrite (string_to_op op_str) children
	| Sexp.Atom _ ->
		let id = Sexp.to_string sexp in
		if (BatSet.mem (NT id) nts) then NTRewrite (NT id)
		else if (BatMap.mem id args_map) then ExprRewrite (BatMap.find id args_map) 
		else ExprRewrite (Const (SexpUtil.sexp_to_const sexp))

(* id -> SynthLang.Exprs.Param *)
let get_args_map (args_data: Sexp.t): (string, expr) BatMap.t = 
	let args_map =
		let name_ty_list = 
			match args_data with 
			| Sexp.List sexps -> (* args *)
				BatList.fold_left (fun acc sexp ->
					match sexp with
					| Sexp.List [name_e; ty_e] -> (* one arg = [name, type] *)
						let param_name = Sexp.to_string name_e in
						let param_ty = SexpUtil.sexp_to_type ty_e in
						(param_name, param_ty) :: acc
					| _ -> assert false
				) [] sexps |> BatList.rev
			| _ -> assert false
		in
		let indexed_name_ty_list =
			BatList.combine 
				(BatList.range 0 `To ((BatList.length name_ty_list) - 1))
				name_ty_list
		in
		BatList.fold_left (fun m (i, (param_name, param_ty)) -> 
			BatMap.add param_name (Param(i, param_ty)) m 
		) BatMap.empty indexed_name_ty_list    
	in
	args_map

(* (define-fun ehad ((x (BitVec 64))) (BitVec 64) (bvlshr x #x0000000000000001)) *)
(* L[ A:define-fun A:ehad *)
(* 	 L[ *)
(* 			L[ A:x L[ A:BitVec A:64]]*)
(* 		] *)
(* 	 L[ A:BitVec A:64] *)
(* 	 L[ A:bvlshr A:x A:#x0000000000000001]  *)
(*  ] *)

(* return: (string, SynthLang.Exprs.expr (with Param)) BatMap.t *)
(* TODO: in case where other definitions used in a definition *)
let process_definitions (defs_data: Sexp.t list list): (op, expr) BatMap.t =
	BatList.fold_left (fun m def_data ->
		match def_data with
		| [name_data; args_data; ret_type_data; body_data] ->
			let name = Sexp.to_string name_data in 
			let ret_type = SexpUtil.sexp_to_type ret_type_data in 
			let args_map = get_args_map args_data in 
			let expr = sexp_to_expr body_data args_map in
			let _ =
				if Global.t.cli_options.get_size then 
				begin
					let size = (SynthLang.Exprs.size_of_expr expr) in 
					Logger.g_error_f "%d" size;
					exit size
				end
			in
			(* Logger.g_debug_f "%s -> %s" name (SynthLang.Exprs.string_of_expr expr);  *)
			BatMap.add (string_to_op name) expr m
		| _ -> assert false   
	) BatMap.empty defs_data 	

(* (synth-fun SC ((s (BitVec 4)) (t (BitVec 4))) Bool                          *)
(*     ((Start Bool (true false (not Start) (and Start Start) (or Start Start) *)
(* 		 (= StartBv StartBv) (bvult StartBv StartBv) (bvslt StartBv StartBv) *)
(* 		 (bvuge StartBv StartBv) (bvsge StartBv StartBv)))                            *)
(*     (StartBv (BitVec 4) (s t #x0 #x8 #x7 (bvneg StartBv) (bvnot StartBv) *)
(* 		 (bvadd StartBv StartBv) (bvsub StartBv StartBv) (bvand StartBv StartBv) *)
(* 		 (bvlshr StartBv StartBv) (bvor StartBv StartBv) (bvshl StartBv StartBv))))) *)
	
(* L[ A:synth-fun A:SC *)
(* 	L[ L[ A:s L[ A:BitVec A:4]] L[ A:t L[ A:BitVec A:4]]] A:Bool *)

(* 	L[ L[ A:Start A:Bool *)
(* 				L[ A:true A:false L[ A:not A:Start] L[ A:and A:Start A:Start] *)
(* 				  L[ A:or A:Start A:Start] L[ A:= A:StartBv A:StartBv] *)
(* 				  L[ A:bvult A:StartBv A:StartBv] *)
(* 				  L[ A:bvslt A:StartBv A:StartBv] *)
(* 				  L[ A:bvuge A:StartBv A:StartBv] *)
(* 				  L[ A:bvsge A:StartBv A:StartBv]*)
(*         ]*)
(* 			] *)
(* 		 L[ A:StartBv L[ A:BitVec A:4] *)
(* 				L[ A:s A:t A:#x0 A:#x8 A:#x7 *)
(* 			 	  L[ A:bvneg A:StartBv] *)
(* 		 		  L[ A:bvnot A:StartBv] *)
(* 				  L[ A:bvadd A:StartBv A:StartBv] *)
(* 				  L[ A:bvsub A:StartBv A:StartBv] *)
(* 				  L[ A:bvand A:StartBv A:StartBv] *)
(* 				  L[ A:bvlshr A:StartBv A:StartBv] *)
(* 				  L[ A:bvor A:StartBv A:StartBv] *)
(* 				  L[ A:bvshl A:StartBv A:StartBv]*)
(*         ]*)
(*  		] *)
(* 	 ]*)
(* 	] *)
let process_grammar (args_map: (string, expr) BatMap.t) (ret_type: exprtype) (grammar_data: Sexp.t): (non_terminal, rewrite BatSet.t) BatMap.t =
	(* nt_rule_data: [Non-terminal, type, production_rules ] *)
	let get_nts acc nt_rule_data =
		match nt_rule_data with
		| Sexp.List [nt_data; _; _] ->
			let nt = NT (Sexp.to_string nt_data) in
			BatSet.add nt acc
		| _ -> assert false
	in
	let process_rules nts grammar nt_rule_data =
		match nt_rule_data with
		| Sexp.List [nt_data; nt_type_data; rules_data] ->
			let nt = NT (Sexp.to_string nt_data) in
			let nt_type = SexpUtil.sexp_to_type nt_type_data in
			let _ = SynthLang.Grammar.nt_type_map := BatMap.add nt nt_type !SynthLang.Grammar.nt_type_map in  
			begin match rules_data with
			| Sexp.List prod_rules_data ->
				BatList.fold_left (fun grammar prod_rule_data -> 
					let rule = sexp_to_rule nts prod_rule_data args_map in
					add_rule nt rule grammar 		 
				) grammar prod_rules_data
			| _ -> assert false
			end
		| _ -> assert false
	in
	match grammar_data with 
	| Sexp.List nt_rules_data ->
		let nts = BatList.fold_left get_nts BatSet.empty nt_rules_data in  
		BatList.fold_left (process_rules nts) empty_grammar nt_rules_data   
	| _ -> assert false  

let process_synth_funcs (synth_fun_data: Sexp.t list): op * (string, expr) BatMap.t * grammar =
	match synth_fun_data with
	| [name_data; args_data; ret_type_data; grammar_data] ->
		let name = Sexp.to_string name_data in
		let args_map = get_args_map args_data in  
		let ret_type = SexpUtil.sexp_to_type ret_type_data in
		let grammar = process_grammar args_map ret_type grammar_data in 
		(string_to_op name, args_map, grammar)
	| _ -> assert false

(* return: name -> Var expr *)
let process_forall_vars forall_vars_data =
	BatList.fold_left (fun m forall_var_data ->
		match forall_var_data with
		| [name_data; type_data] ->
			let name = Sexp.to_string name_data in
			let ty = SexpUtil.sexp_to_type type_data in
			(* set up the domain. the range will be determined later *) 
			BatMap.add name (Var(name, ty)) m 
		| _ -> assert false
	) BatMap.empty forall_vars_data    

(* (constraint (= (hd01 x) (f x))) *)
(* [L[ A:= L[ A:hd20 A:x] L[ A:f A:x]]] *)
(* (constraint (= (f #xeed40423e830e30d) #x8895fdee0be78e79)) *)
(* [L[ A:= L[ A:f A:#xeed40423e830e30d] A:#x8895fdee0be78e79]] *) 
(* currently, only for PBE *)
(* return: spec as SynthLang.Exprs.expr *)
let process_constraints
	(grammar: grammar)
	(target_function_name: op)
	(constraints_data: Sexp.t list list)
	(macro_instantiator: (op, expr) BatMap.t)
	(id2var: (string, expr) BatMap.t)
: Specification.t * (string, expr) BatMap.t =
	BatList.fold_left (fun (spec, forall_var_map) constraint_data ->
		let constraint_data =
		  match constraint_data with
		  | h :: _ -> h
		  | _ -> assert false
		in
		(* forall_var_map : variable name -> Var(name, ty) *) 
		let exp = sexp_to_expr constraint_data id2var in
		(* let _ = Logger.g_debug (string_of_expr exp) in *)
		match exp with
		| Function (GEN_CMP_OP CMP_EQ, Const ex_output :: Function (op0, ex_input_expr, _) :: _, Bool)
		| Function (GEN_CMP_OP CMP_EQ, Function (op0, ex_input_expr, _) :: Const ex_output :: _, Bool)
				when op0 = target_function_name && BatList.for_all SynthLang.Exprs.is_const_expr ex_input_expr ->
			let ex_input_const = BatList.map expr2const ex_input_expr in
			(Specification.add_ex_io (ex_input_const, ex_output) spec, forall_var_map)
		| Function (GEN_CMP_OP CMP_EQ, (Function (op0, _, _) as arg0) :: (Function (op1, _, _) as arg1) :: _, Bool)
				when op0 <> op1 && (op0 = target_function_name || op1 = target_function_name) ->
			let oracle_expr, target_expr =
				if get_op arg0 = target_function_name then 
					arg1, arg0
				else arg0, arg1 
			in
			let oracle_name = get_op oracle_expr in   
			let oracle_expr_resolved = try BatMap.find oracle_name macro_instantiator with _ -> assert false in  
			(* let _ = Logger.g_debug_f "(assert (= %s %s))" (SynthLang.Exprs.string_of_expr oracle_expr_resolved) (SynthLang.Exprs.string_of_expr target_expr) in  *)
			let spec = Specification.add_oracle_spec oracle_expr oracle_expr_resolved spec in
			(* forall_var_map : variable name -> Param(int, ty) *)
			let _, forall_var_map = 
				let args = get_children oracle_expr in 
				List.fold_left (fun (i, m) var_expr ->
					let name = SynthLang.Exprs.string_of_expr var_expr in 
					(i + 1, BatMap.add name (Param(i, SynthLang.Exprs.type_of_expr var_expr)) m)  
				) (0, BatMap.empty) args
			in
			(spec, forall_var_map)
		| Function (GEN_CMP_OP CMP_EQ, _, _) ->
			failwith ("Not supported: synth-fun is missing")
		| _ ->
			failwith ("Not supported: not a SyGuS-pbe specification")
	) (Specification.empty_spec, BatMap.empty) constraints_data

let parse (file: string): parse_result = 
	Random.self_init(); 
	let lines = read_lines file in
	let temp_preprocessed_file = file ^ "_" ^ (string_of_int (Random.int 1000)) in
	let lines = 
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
	let _ = write_lines lines temp_preprocessed_file in
	let sexps = Sexp.load_sexps temp_preprocessed_file in
	let _ = Unix.unlink temp_preprocessed_file in
	
	let macro_instantiator: (op, expr) BatMap.t =
		let defs_data = SexpUtil.filter_sexps_for "define-fun" sexps in
			(* BatSet.iter (fun sexp_list ->                                       *)
			(* 	let sexp = Sexp.List ((Sexp.Atom "define-fun") :: sexp_list) in    *)
			(* 	Logger.g_debug (debug_string_of_sexp sexp)                                *)
			(* )  defs_data;                                                       *)
		process_definitions defs_data
	in
	(* BatMap.iter (fun name expr ->               *)
	(* 	Logger.g_debug (sexpstr_of_fun name expr)  *)
	(* ) macro_instantiator;                       *)
	let target_function_name, args_map, grammar =
		match SexpUtil.filter_sexps_for "synth-fun" sexps with
		| [] -> failwith "No target function to be synthesized is given."
		| [singleton] ->
			process_synth_funcs singleton
		| _ -> failwith "Multi-function synthesis is not supported." 
	in 
	(* Logger.g_debug (SynthLang.Grammar.string_of_grammar grammar); *)
	let (spec, forall_var_map) =
		let id2var =
			let forall_vars_data = SexpUtil.filter_sexps_for "declare-var" sexps in
			process_forall_vars forall_vars_data
		in
		let constraints_data = SexpUtil.filter_sexps_for "constraint" sexps in
		(* Logger.g_debug (string_of_list debug_string_of_sexp (BatSet.choose constraints_data)); *)
		process_constraints grammar target_function_name constraints_data macro_instantiator id2var
	in
	Logger.g_debug (Specification.string_of_ex_io_list spec.spec_pbe);
	{
		macro_instantiator = macro_instantiator;
		target_function_name = target_function_name;
		args_map = args_map;
		grammar = grammar;
		forall_var_map = forall_var_map;
		spec_total = spec
	}
