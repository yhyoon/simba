open Common
open Vocab

open SynthLang
open Exprs
open Grammar
open GrammarUtil

(* 
 * in rewrite at addr, revert subtree at to_nt_addr into matching non_terminal.
 * with failure -> raise Not_found
 *)
let try_revert_to_nt_at (grammar: grammar) (to_nt_addr: addr) (addr: addr) (rewrite: rewrite): rewrite =
	let rec try_revert_expr_to_nt_at (addr: addr) (cur_expr: expr): rewrite =
		match compare_addr to_nt_addr addr with
		| ADDR_EQ -> begin
			(* try replace this expr to nt *)
			NTRewrite (reverse_product_expr grammar cur_expr)
		end
		| ADDR_L_DOM (* L_DOM: should be unreachable *)
		| ADDR_NO_ORDER ->
			ExprRewrite cur_expr
		| ADDR_R_DOM -> begin
			(* do more *)
			match cur_expr with
			| Param _ | Var _ | Const _ -> (* should be unreachable *)
				ExprRewrite cur_expr
			| Function (fun_id, sub_exprs, exprtype) -> begin
				let sub_rewrites = BatList.mapi (fun i rewrite -> try_revert_expr_to_nt_at (addr@[i]) rewrite) sub_exprs in
				normalized_func_rewrite fun_id sub_rewrites
			end
		end
	in
	let rec try_revert_rewrite_to_nt_at (addr: addr) (cur_rewrite: rewrite): rewrite =
		match compare_addr to_nt_addr addr with
		| ADDR_EQ -> begin
			(* try replace this rewrite to nt *)
			NTRewrite (reverse_product_rewrite grammar cur_rewrite)
		end
		| ADDR_L_DOM (* L_DOM: should be unreachable *)
		| ADDR_NO_ORDER ->
			cur_rewrite
		| ADDR_R_DOM -> begin
			(* do more *)
			match cur_rewrite with
			| NTRewrite _ -> cur_rewrite (* should be unreachable *)
			| ExprRewrite expr -> try_revert_expr_to_nt_at addr expr
			| FuncRewrite (fun_id, sub_rewrites) ->
				normalized_func_rewrite fun_id (BatList.mapi (fun i rewrite -> try_revert_rewrite_to_nt_at (addr@[i]) rewrite) sub_rewrites)
		end
	in
	try_revert_rewrite_to_nt_at addr rewrite

let is_feasible_by_solver (grammar: Grammar.grammar) (spec: SynthSpec.Specification.t) (rewrite: Grammar.rewrite): bool =
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
	try
		(* find unsat i/o pair *)
		let _ = BatList.find (fun (input_consts, output_const) -> 
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
				let smt_str: string =
					var_decls_str ^ "\n" ^
					(string_of_list ~first:"" ~last:"" ~sep:"\n" identity constrs)
				in
				let (q, solver) = SynthSpec.Z3interface.smt_check smt_str in
				match q with
				| UNSATISFIABLE ->
					true
				| _ ->
					false
			) (SynthSpec.Specification.to_verfiable_spec spec)
		in
		(* found unsat i/o pair -> infeasible *)
		false
	with Not_found ->
		(* all i/o pairs are sat *)
		true