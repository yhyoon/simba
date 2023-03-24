open Common
open Vocab

open SynthLang
open SynthSpec

let forbidden_by_solver: Grammar.rewrite BatSet.t ref = ref BatSet.empty
let forbidden_by_sem: Grammar.rewrite BatSet.t ref = ref BatSet.empty

let template_match (grammar: Grammar.grammar) (spec: Specification.t) (forbidden_templates: Grammar.rewrite BatSet.t) (plugged_rewrite: Grammar.rewrite): bool =
	let rec matching rewrite templ =
		match rewrite, templ with
		| Grammar.FuncRewrite (op, sub_rewrites), Grammar.FuncRewrite (templ_op, templ_sub_rewrites) -> 
			op = templ_op  && List.for_all2 matching sub_rewrites templ_sub_rewrites
		| Grammar.ExprRewrite (Function(op, sub_exprs, _)), Grammar.FuncRewrite (templ_op, templ_sub_rewrites) ->
			op = templ_op && List.for_all2 matching (BatList.map (fun x -> Grammar.ExprRewrite x) sub_exprs) templ_sub_rewrites
		| Grammar.ExprRewrite expr, Grammar.ExprRewrite templ_expr ->
			Exprs.compare_signature (Exprs.compute_signature spec expr) (Exprs.compute_signature spec templ_expr) = 0
		| _, NTRewrite templ_nt ->
			templ_nt = Grammar.reverse_product_rewrite grammar rewrite
		| _, _ -> 
			false
	in
	BatSet.exists (matching plugged_rewrite) forbidden_templates

let get_forbidden_template_by_solver (grammar: Grammar.grammar) (spec: Specification.t) (rewrite: Grammar.rewrite): Grammar.rewrite BatSet.t =
	let smt_string_of_addr (addr: GrammarUtil.addr): string =
		let position_prefix: string = "__p" in
		List.fold_left (^) position_prefix (List.map string_of_int addr)
	in
	(* constraint string * addr list *) 
	let rec get_structure_constraints (addr: GrammarUtil.addr) (rewrite: Grammar.rewrite): (string * GrammarUtil.addr) list =
		let expr_str_opt: string option =
			match rewrite with
			| FuncRewrite (op, sub_rewrites) ->
				let sub_addrs =
					BatList.map (fun i -> addr@[i])
						(BatList.range 0 `To ((List.length sub_rewrites) - 1))	 
				in
				Some (Printf.sprintf "(%s %s)" (Operators.op_to_string op)
					(string_of_list ~first:"" ~last:"" ~sep:" " smt_string_of_addr sub_addrs))
			| NTRewrite nt ->
				None
			| ExprRewrite (Function (op, sub_exprs, _)) ->
				let sub_addrs =
					BatList.map (fun i -> addr@[i])
						(BatList.range 0 `To ((List.length sub_exprs) - 1))	 
				in 
				Some(Printf.sprintf "(%s %s)" (Operators.op_to_string op)
					(string_of_list ~first:"" ~last:"" ~sep:" " smt_string_of_addr sub_addrs))
			| ExprRewrite expr -> Some(Exprs.string_of_expr expr)
		in
		match expr_str_opt with
		| Some expr_str -> begin
			let constraint_str =
				Printf.sprintf "(assert (= %s %s))" (smt_string_of_addr addr) expr_str
			in
			match rewrite with
			| FuncRewrite (_, sub_rewrites) ->
				List.fold_left
					(fun (i, acc) sub_rewrite ->
					let acc = acc @ (get_structure_constraints (addr@[i]) sub_rewrite) in
						(i + 1, acc)
					) (0, [(constraint_str, addr)]) sub_rewrites
				|> snd
			| ExprRewrite (Function (_, sub_exprs, _)) ->
				List.fold_left
					(fun (i, acc) sub_expr ->
					let acc = acc @ (get_structure_constraints (addr@[i]) (ExprRewrite sub_expr)) in
						(i + 1, acc)
					) (0, [(constraint_str, addr)]) sub_exprs
				|> snd
			| _ -> [(constraint_str, addr)] 
		end
		| None -> []
  	in
	let addr_tys =
    	(* addr (int list) * exprs.type BatSet.t *) 
        let rec get_addr_tys (addr: GrammarUtil.addr) (rewrite: Grammar.rewrite): (GrammarUtil.addr * Exprs.exprtype) BatSet.t =
            let ty = Grammar.ret_type_of_rewrite rewrite in 
            let rec get_addr_tys_of_expr (addr: GrammarUtil.addr) (expr: Exprs.expr): (GrammarUtil.addr * Exprs.exprtype) BatSet.t =
                match expr with
                | Function (_, sub_exprs, _) ->
                    List.fold_left
                        (fun (i, acc) sub_expr -> 
                            let acc = BatSet.union acc (get_addr_tys_of_expr (addr@[i]) sub_expr) in 
                            (i + 1, acc)
                        ) (0, (BatSet.singleton (addr, ty))) sub_exprs |> snd
                | _ -> BatSet.singleton (addr, ty)
            in
            match rewrite with
            | FuncRewrite (_, sub_rewrites) ->
                List.fold_left
                        (fun (i, acc) sub_expr -> 
                            let acc = BatSet.union acc (get_addr_tys (addr@[i]) sub_expr) in 
                            (i + 1, acc)
                        ) (0, (BatSet.singleton (addr, ty))) sub_rewrites |> snd
            | ExprRewrite expr -> get_addr_tys_of_expr addr expr
            | _ -> BatSet.singleton (addr, ty)
        in
        get_addr_tys [] rewrite
    in

(* (declare-const x (_ BitVec 64))                               *)
(* (declare-const out (_ BitVec 64))                             *)
(* (declare-const t0 (_ BitVec 64))                              *)
(* (declare-const t1 (_ BitVec 64))                              *)
(* (declare-const t2 (_ BitVec 64))                              *)
(* (declare-const t3 (_ BitVec 64))                              *)
(* (declare-const t4 (_ BitVec 64))                              *)

(* (assert (! (= x #x6000000000000000) :named __in))             *)
(* (assert (! (= out #x4000000000000000)  :named __out))         *)

(* (assert (! (= out (bvmul t4 t1))  :named __a0))               *)
(* (assert (! (= t1 (bvmul t4 t2))  :named __a1))                *)
(* (assert (! (= t2 (bvadd t4 t3))  :named __a2))                *)
(* (assert (! (= t3 (bvadd t4 #x4000000000000000)) :named __a3)) *)
(* (assert (! (= t4 x)  :named __a4))                            *)

	let f forbidden_templates (input_consts, output_const) = 
  		let params =
			BatList.map (fun (i,const) -> 
					Exprs.Param (i, (Exprs.type_of_const const))
				) (zip_with_index input_consts)
		in
		(** Variable declarations *) 
		let var_decls_str =
			(* params + addrs *)
			let params_str =
    		List.fold_left (fun acc param ->
					Printf.sprintf "%s\n(declare-const %s %s)"
						acc
						(Exprs.string_of_expr param)
						(Exprs.string_of_type ~z3:true (Exprs.type_of_expr param))
    			) "" params
			in
			BatSet.fold (fun (addr, ty) acc ->
				Printf.sprintf "%s\n(declare-const %s %s)"
					acc
					(smt_string_of_addr addr)
					(Exprs.string_of_type ~z3:true ty)
			) addr_tys params_str
  		in
		(** Input-output constraint *)
		let io_constrs: string list =
			let out_constr_str = 
  			Printf.sprintf "(assert (= %s %s))" 
  				(smt_string_of_addr [])
  				(Exprs.string_of_const output_const)
			in
			let in_constr_strs =
  			List.map (fun (param, input_const) ->
  				Printf.sprintf "(assert (= %s %s))"
  					(Exprs.string_of_expr param)
  					(Exprs.string_of_const input_const)
  			) (List.combine params input_consts)
			in
			out_constr_str :: in_constr_strs  
		in
  		let structure_constr_addrs = get_structure_constraints [] rewrite in
		let structure_constrs = List.map fst structure_constr_addrs in
		let constrs = io_constrs @ structure_constrs in
		let unsat_core_indices =
			let smt_str: string =
				var_decls_str ^ "\n" ^
				(string_of_list ~first:"" ~last:"" ~sep:"\n" identity constrs)
			in
			try
				Logger.g_debug_lazy (fun () -> (Printf.sprintf "get_unsat_core rewrite: %s" (Grammar.string_of_rewrite rewrite)));
				Logger.g_debug_lazy (fun () -> (Printf.sprintf "SMT: %s" smt_str));
				SynthSpec.Z3interface.get_unsat_core smt_str
			with Z3.Error msg -> begin
				Logger.g_with_increased_depth (fun () ->
					Logger.g_error_f "Z3 error: %s" msg
				);
				[]
			end
		in
		let unsat_cores =
			if not (BatList.is_empty unsat_core_indices) then
				Logger.g_debug_lazy (fun () -> (Printf.sprintf "unsat core indices: %s" (string_of_list string_of_int unsat_core_indices)));
			List.map (fun i -> List.nth constrs i) unsat_core_indices 
		in 
		(* let _ = prerr_endline "unsat cores " in                    *)
		(* let _ = prerr_endline (string_of_list id unsat_cores) in   *)
		let unsat_core_addrs =
			unsat_core_indices
			|> List.map (fun i -> i - (List.length io_constrs))
			|> List.filter (fun i -> i >= 0)
			|> List.map (fun i -> snd (List.nth structure_constr_addrs i))
			|> list2set
		in
		if (BatList.is_empty unsat_cores) || (* UNSAT 이 아님 *) 
			 (BatSet.cardinal unsat_core_addrs) = (List.length structure_constrs) then (* 전체가 unsat core *) 
			 forbidden_templates
		else begin
			let template = Grammar.reverse_product_conditional grammar (fun addr -> not (BatSet.mem addr unsat_core_addrs)) rewrite in
			Logger.g_debug_lazy (fun () ->
				Printf.sprintf "for rewrite=%s, template added=%s" (Grammar.string_of_rewrite rewrite) (Grammar.string_of_rewrite template)
			);
			BatSet.add template forbidden_templates
		end
	in
	List.fold_left f BatSet.empty spec

let try_add_forbidden_template_by_solver (grammar: Grammar.grammar) (spec: Specification.t) (rewrite: Grammar.rewrite): unit =
	let prev_card = BatSet.cardinal !forbidden_by_solver in
	let calculated_forbidden_templates = get_forbidden_template_by_solver grammar spec rewrite in
	let new_forbidden_templates = BatSet.diff calculated_forbidden_templates !forbidden_by_solver in
	forbidden_by_solver :=
		BatSet.union
			!forbidden_by_solver
			calculated_forbidden_templates;
	let next_card = BatSet.cardinal !forbidden_by_solver in
	if next_card > prev_card then begin
		Logger.g_info ("forbidden templates added by solver, count = " ^ string_of_int next_card);
		Logger.g_with_increased_depth (fun () ->
			Logger.g_info (string_of_set Grammar.string_of_rewrite new_forbidden_templates);
		)
	end
