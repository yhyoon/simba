open Common
open Vocab
open Exprs
open Grammar

type addr = int list (* position of a node in an AST *)

let get_holes (rule: rewrite): (addr * non_terminal) list =
	let rec aux (addr: addr) (rule: rewrite) (accum_rev: (addr * non_terminal) list): (addr * non_terminal) list =
		match rule with
	| NTRewrite nt -> (addr, nt) :: accum_rev
	| ExprRewrite _ -> accum_rev
	| FuncRewrite (fun_id, operand_rewrites) ->
		BatList.fold_lefti (fun result idx sub_rewrite -> aux (addr@[idx]) sub_rewrite result) accum_rev operand_rewrites
	in
	aux [] rule [] |> BatList.rev

let count_holes rule =
	let rec count_holes_aux accum rules =
		match rules with
		| [] -> accum
		| NTRewrite _ :: tail -> count_holes_aux (accum + 1) tail
		| ExprRewrite _ :: tail -> count_holes_aux accum tail
		| FuncRewrite (_, operand_rewrites) :: tail ->
			count_holes_aux accum (BatList.rev_append operand_rewrites tail)
	in
	count_holes_aux 0 [rule]

(* maybe used for delta-debugging

let get_active_addrs (rewrite: rewrite) (depth: int): addr list =
	let rec get_active_addrs_expr_aux (cur_addr: addr) (cur_expr: expr) (depth: int): addr list =
		if depth = 0 then
			[cur_addr]
		else if depth = 1 then
			match cur_expr with
			| Function (_, sub_SynthLang.Exprs, _) ->
				BatList.mapi (fun idx sub_expr -> cur_addr@[idx]) sub_SynthLang.Exprs
			| _ -> []
		else
			match cur_expr with
			| Function (_, sub_SynthLang.Exprs, _) ->
				BatList.flatten (BatList.mapi (fun idx sub_expr -> get_active_addrs_expr_aux (cur_addr@[idx]) sub_expr (depth - 1)) sub_SynthLang.Exprs)
			| _ -> []
	in
	let rec get_active_addrs_rewrite_aux (cur_addr: addr) (cur_rewrite: rewrite) (depth: int): addr list =
		if depth = 0 then
			[cur_addr]
		else if depth = 1 then
			match cur_rewrite with
			| NTRewrite nt ->
				[]
			| ExprRewrite expr ->
				get_active_addrs_expr_aux cur_addr expr depth
			| FuncRewrite (op, sub_rewrites) ->
				BatList.mapi (fun idx sub_rewrite -> cur_addr@[idx]) sub_rewrites
		else
			match cur_rewrite with
			| NTRewrite nt ->
				[]
			| ExprRewrite expr ->
				get_active_addrs_expr_aux cur_addr expr depth
			| FuncRewrite (op, sub_rewrites) ->
				BatList.flatten (BatList.mapi (fun idx sub_rewrite -> get_active_addrs_rewrite_aux (cur_addr@[idx]) sub_rewrite (depth - 1)) sub_rewrites)
	in
	get_active_addrs_rewrite_aux [] rewrite depth *)

let plug (rule: rewrite) (instances: (addr * expr) list): expr  =
	let rec plug_sub curr_addr rule instances =
		match rule with
		| NTRewrite nt ->
			(try List.assoc curr_addr instances with Not_found -> assert false) 
		| ExprRewrite expr -> expr
		| FuncRewrite (op, rewrites) ->
			let children : expr list =
				(BatList.mapi (fun i rewrite -> plug_sub (curr_addr@[i]) rewrite instances) rewrites)
			in
			Function (op, children, ret_type_of_func_rewrite op (BatList.map expr_rewrite children))
	in
	plug_sub [] rule instances

(* instances : addr * rewrite list *)
let plug_rewrite (rule: rewrite) (instances: (addr * rewrite) list): rewrite =
	let rec plug_sub curr_addr rule instances =
		match rule with
		| NTRewrite nt ->
			(try List.assoc curr_addr instances with Not_found -> rule)
		| FuncRewrite (op, children) -> begin
			let plugged_children : rewrite list =
				(BatList.mapi (fun i child -> plug_sub (curr_addr@[i]) child instances) children)
			in
			normalized_func_rewrite op plugged_children
		end
		| _ -> rule
	in
	plug_sub [] rule instances	

type addr_order =
    | ADDR_L_DOM
    | ADDR_R_DOM
    | ADDR_EQ
    | ADDR_NO_ORDER

let rec compare_addr (addr1: addr) (addr2: addr): addr_order =
    match addr1, addr2 with
    | [], [] -> ADDR_EQ (* addr1 equals addr2 *)
    | _, [] -> ADDR_R_DOM (* addr2 is prefix of addr1 = addr2 dominates addr1 *)
    | [], _ -> ADDR_L_DOM (* addr1 is prefix of addr2 = addr1 dominates addr2 *)
    | h1::t1, h2::t2 ->
        if h1 = h2 then
            compare_addr t1 t2
        else ADDR_NO_ORDER (* no relation *)

let rec access_addr (addr: addr) (rewrite: rewrite): rewrite =
	match addr, rewrite with
    | [], _ -> rewrite (* found *)
    | h :: _, NTRewrite nt ->
        invalid_arg (Printf.sprintf "expr_of_addr(%d :: _, NTRewrite (%s))" h (string_of_non_terminal nt))
    | h :: _, ExprRewrite e ->
        invalid_arg (Printf.sprintf "expr_of_addr(%d :: _, ExprRewrite (%s))" h (string_of_expr e))
    | h :: t, FuncRewrite (_, operands) ->
        if h < BatList.length operands then
            access_addr t (List.nth operands h)
        else
            invalid_arg (Printf.sprintf "expr_of_addr(%d :: _, FunRewrite (%s))" h (string_of_rewrite rewrite))
