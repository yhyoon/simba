open Common
open Vocab
open Graph
open Exprs
open Operators

type non_terminal = NT of string
type rewrite = 
	| NTRewrite of non_terminal
	| ExprRewrite of expr
	| FuncRewrite of op * rewrite list  

let nt_type_map : (non_terminal, exprtype) BatMap.t ref = ref BatMap.empty 

let type_of_nt nt = try BatMap.find nt !nt_type_map with _ -> failwith "type_of_nt"

let expr_rewrite (expr: expr): rewrite = ExprRewrite expr

type grammar = (non_terminal, rewrite BatSet.t) BatMap.t 

let get_rules: non_terminal -> grammar -> rewrite BatSet.t = BatMap.find   

let rec get_nts (rewrite: rewrite): non_terminal list =
	match rewrite with 
	| FuncRewrite (op, rewrites) ->
		BatList.fold_left (fun acc rewrite' -> acc @ (get_nts rewrite')) [] rewrites
	| NTRewrite nt -> [nt] 
	| _ -> []

let is_nt_rule (rule: rewrite): bool =
	match rule with 
	| NTRewrite _ -> true 
	| _ -> false
	
let is_equal_nt (nt: non_terminal) (nt': non_terminal): bool = 
	match nt, nt' with 
	| NT s, NT s' -> BatString.equal s s'
 
let is_function_rule (rule: rewrite): bool =
	match rule with 
	| FuncRewrite _ -> true 
	| _ -> false 

let is_ite_function_rule (rule: rewrite): bool =
	match rule with
	| FuncRewrite (TRI_OP ITE, _) -> true
	| _ -> false

let is_param_rule (rule: rewrite): bool = 
	match rule with 
	| ExprRewrite (Param _ ) -> true 
	| _ -> false 

let is_constant_rule (rule: rewrite): bool = 
	match rule with 
	| ExprRewrite (Const _ ) -> true 
	| _ -> false

let string_of_non_terminal (NT nt_id) = "N_" ^ nt_id

let rec string_of_rewrite (rewrite: rewrite): string = 
	match rewrite with 
	| NTRewrite (NT nt_id) -> string_of_non_terminal (NT nt_id)
	| ExprRewrite expr -> "E_" ^ string_of_expr expr 
	| FuncRewrite (op, rewrites) -> 
		Printf.sprintf "(%s %s)" (op_to_string op)
			(string_of_list ~first:"" ~last:"" ~sep:" " string_of_rewrite rewrites)  

let string_of_rewritelist rewritelist = 
	string_of_list string_of_rewrite rewritelist

let string_of_rewriteset rewriteset = 
	string_of_set string_of_rewrite rewriteset

let rec size_of_rewrite rewrite = 
	match rewrite with 
	| NTRewrite _ -> 0
	| ExprRewrite expr -> size_of_expr expr
	| FuncRewrite (op, rewrites) -> 
		List.fold_left (fun size rewrite -> size + (size_of_rewrite rewrite)) 1 rewrites  	

let op_of_rule (rule: rewrite): op =
	match rule with
	| FuncRewrite (op, _) | ExprRewrite (Function (op, _, _)) -> op
	| _ -> failwith "op_of_rule"

exception RewriteWithBadType of rewrite
exception RewriteWithUnknownType of rewrite

let _ = Printexc.register_printer (fun exn ->
        match exn with
        | RewriteWithBadType rw -> Some (
            "BadType " ^ string_of_rewrite rw
        )
        | RewriteWithUnknownType rw ->  Some (
			"UnknownType " ^ string_of_rewrite rw
		)
		| _ -> None
    )

let rec ret_type_of_rewrite (rule: rewrite): exprtype =
	match rule with
	| ExprRewrite expr -> type_of_expr expr
	| NTRewrite nt -> type_of_nt nt
	| FuncRewrite (op, children) -> ret_type_of_func_rewrite op children
and extract_eq_children_type (parent: rewrite) (children: rewrite list): exprtype =
	let children_types = BatList.map (fun child ->
			try
				[ret_type_of_rewrite child]
			with RewriteWithUnknownType _ -> []
		) children |> BatList.flatten
	in
	match children_types with
	| [] -> raise (RewriteWithUnknownType parent)
	| h :: t ->
		BatList.fold_left (fun acc x ->
				if acc = x then acc else raise (RewriteWithBadType parent)
			) h t
and ret_type_of_func_rewrite (op: op) (operands: rewrite list): exprtype =
	let func_rewrite = FuncRewrite (op, operands) in
	match op with
	| BV_OP (BV_CMP_OP _) ->
		Bool
	| BV_OP _ ->
		extract_eq_children_type func_rewrite operands
	| TRI_OP ITE -> begin
		match operands with
		| [] -> raise (RewriteWithBadType func_rewrite)
		| _ :: branches -> extract_eq_children_type func_rewrite branches
	end
	| BOOL_OP _ ->
		Bool
	| GEN_CMP_OP _ ->
		Bool
	| INT_OP _ ->
		Int
	| STR_OP S_LEN | STR_OP S_STR_TO_INT | STR_OP S_INDEX_OF ->
		Int
	| STR_OP S_INT_TO_STR | STR_OP S_AT | STR_OP S_CONCAT | STR_OP S_REPLACE | STR_OP S_SUBSTR ->
		String
	| STR_OP S_PREFIX_OF | STR_OP S_SUFFIX_OF | STR_OP S_CONTAINS ->
		Bool
	| GENERAL_FUNC _ ->
		failwith_f "ret_type_of_func_rewrite: GENERAL_FUNC %s" (op_to_string op)

let normalized_func_rewrite (op: op) (children: rewrite list): rewrite =
	let rec expr_children_or_none expr_children unchecked_children =
		match unchecked_children with
		| [] -> Some expr_children
		| ExprRewrite e :: t -> expr_children_or_none (expr_children@[e]) t
		| _ -> None
	in
	match expr_children_or_none [] children with
	| Some expr_children ->
		ExprRewrite (Function (op, expr_children, ret_type_of_func_rewrite op children))
	| None -> FuncRewrite (op, children)

exception Not_expr_rewrite of non_terminal

let rec expr_of_rewrite_exn rewrite =
	match rewrite with
	| FuncRewrite (op, rewrites) ->
		Function (op, List.map expr_of_rewrite_exn rewrites, ret_type_of_func_rewrite op rewrites) 
	| ExprRewrite expr -> expr
	| NTRewrite nt -> raise (Not_expr_rewrite nt)

module NTNode = struct
	type t = non_terminal (* non-terminal *) 
	let compare (NT nt_id1) (NT nt_id2) = String.compare nt_id1 nt_id2
	let equal r1 r2 = (compare r1 r2) = 0  
	let hash = Hashtbl.hash
end

module NTGraph = Persistent.Digraph.ConcreteBidirectional(NTNode) 
module NTTopology = Topological.Make(NTGraph)

(* return a list of pairs of a non-terminal and a production rule*)
(* the list follows the topological order in the graph of non-terminals*)
(* e.g., having a rule N1 -> f(N2), N2 comes before N1 *)
let get_nt_rule_list (grammar: grammar): (non_terminal * rewrite) list =
	let nt_rule_list =
		BatMap.foldi (fun nt rules lst ->
			BatSet.fold (fun rule lst -> (nt, rule) :: lst) rules lst
		) grammar []
	in
	let ntgraph = 
		BatMap.foldi (fun nt rules g ->
			BatSet.fold (fun rule g ->
				let nts = get_nts rule in 
				List.fold_left (fun g nt' ->
					NTGraph.add_edge g nt' nt
				) g nts
			) rules g
		) grammar NTGraph.empty
	in
	let topological_sorted_nts = 
		NTTopology.fold (fun nt lst ->
			if (List.mem nt lst) then lst 
			else lst @ [nt]  
		) ntgraph []
	in
	List.map (fun nt -> 
		List.filter (fun (nt', _) -> is_equal_nt nt nt') nt_rule_list
		(* (try BatMap.find nt grammar with _ -> failwith (string_of_rewrite nt))  *)
		(* |> BatSet.elements                                                      *)
		(* |> List.map (fun rule -> (nt, rule))                                    *)
	) topological_sorted_nts |> List.flatten 


let start_nt: non_terminal = NT "Start"

let add_rule (nt: non_terminal) (rule: rewrite) (grammar: grammar): grammar =
	let rules = try BatMap.find nt grammar with _ -> BatSet.empty in 
	BatMap.add nt (BatSet.add rule rules) grammar   

let empty_grammar: grammar = BatMap.empty 
		
let string_of_grammar (grammar: grammar): string = 
	BatMap.foldi (fun nt rules acc ->
		Printf.sprintf "%s -> %s\n%s" 
			(string_of_non_terminal nt)
			(string_of_rewriteset rules)
			acc  
	) grammar ""

let reverse_product_expr (grammar: grammar) (expr: expr): non_terminal =
	let sub_rules =
		match expr with
		| Param _ | Var _ | Const _ ->
			BatMap.filter (fun nt rule -> 
				BatSet.exists (fun r ->
					match r with
					| ExprRewrite e -> e = expr
					| _ -> false
				) rule
			) grammar
		| Function (fun_id, _, _) ->
			BatMap.filter (fun nt rule -> 
				BatSet.exists (fun r ->
					match r with
					| FuncRewrite (f, _) -> fun_id = f
					| _ -> false
				) rule
			) grammar
	in
	if BatMap.cardinal sub_rules = 1 then
		BatMap.choose sub_rules |> fst
	else raise Not_found

let reverse_product_rewrite (grammar: grammar) (rewrite: rewrite): non_terminal =
	match rewrite with
	| FuncRewrite (fun_id, _) ->
		let sub_rules = BatMap.filter (fun nt rule -> 
			BatSet.exists (fun r ->
				match r with
				| FuncRewrite (f, _) -> fun_id = f
				| _ -> false
			) rule
		) grammar
		in
		if BatMap.cardinal sub_rules = 1 then
			BatMap.choose sub_rules |> fst
		else raise Not_found
	| NTRewrite nt -> nt
	| ExprRewrite expr ->
		reverse_product_expr grammar expr

let reverse_product_conditional (grammar: grammar) (predicate: int list -> bool) (rewrite: rewrite): rewrite =
    let rec reverse_product_aux (addr: int list) (cur_rewrite: rewrite): rewrite =
        if predicate addr then
            NTRewrite (reverse_product_rewrite grammar cur_rewrite)
        else
            match cur_rewrite with
            | FuncRewrite (op, sub_rewrites) ->
                let sub_rewrites' =
                    BatList.map (fun (i,sub_rewrite) ->
                        let addr' = addr@[i] in
                        reverse_product_aux addr' sub_rewrite
                    ) (zip_with_index sub_rewrites)
                in
                normalized_func_rewrite op sub_rewrites'
            | NTRewrite _ -> cur_rewrite
            | ExprRewrite Function (op, sub_exprs, ty) ->
                let sub_rewrites' =
                    BatList.map (fun (i,sub_expr) ->
                        let addr' = addr@[i] in
                        reverse_product_aux addr' (ExprRewrite sub_expr)
                    ) (zip_with_index sub_exprs)
                in
                normalized_func_rewrite op sub_rewrites'
            | _ -> cur_rewrite
    in
    reverse_product_aux [] rewrite

(* let init_grammar =                                                                 *)
(* 	let string_nt_id = "String" in                                                   *)
(*   let string_nt = (NTRewrite string_nt_id) in                                      *)
(*   let int_nt_id = "Int" in                                                         *)
(*   let int_nt = (NTRewrite int_nt_id) in                                            *)
(*   let bool_nt_id = "Bool" in                                                       *)
(*   let bool_nt = (NTRewrite bool_nt_id) in                                          *)
(* 	List.fold_left (fun m (nt,rule) -> add_rule nt rule m) BatMap.empty              *)
(* 	[                                                                                *)
(* 		(* (* String *)                                                             *) *)
(* 		(* (string_nt, ExprRewrite (Const (CString " ")));                          *) *)
(* 		(* (* (string_nt, ExprRewrite (Const (CString "("))); *)                    *) *)
(* 		(* (* (string_nt, ExprRewrite (Const (CString ")"))); *)                    *) *)
(* 		(* (* (string_nt, ExprRewrite (Const (CString "-"))); *)                    *) *)
(* 		(* (string_nt, ExprRewrite (Const (CString ".")));                          *) *)
(* 		(* (* (string_nt, ExprRewrite (Const (CString ","))); *)                    *) *)
(* 		(* (string_nt, FuncRewrite ("charAt", [string_nt; int_nt]));                *) *)
(* 		(* (string_nt, FuncRewrite ("concat", [string_nt; string_nt]));             *) *)
(* 		(* (string_nt, FuncRewrite ("replace", [string_nt; string_nt; string_nt])); *) *)
(* 		(* (string_nt, FuncRewrite ("substr", [string_nt; int_nt; int_nt]));        *) *)
		
(* 		(* Int *)                                                                      *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 0)));        *)                           *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 1)));        *)                           *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 2)));        *)                           *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 3)));        *)                           *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 4)));        *)                           *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 5)));        *)                           *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 6)));        *)                           *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 7)));        *)                           *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 8)));        *)                           *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 9)));        *)                           *)
(* 		(* (int_nt, FuncRewrite ("+", [int_nt; int_nt])); *)                           *)
(* 		(* (int_nt, FuncRewrite ("-", [int_nt; int_nt])); *)                           *)
(* 		(* (int_nt, FuncRewrite ("*", [int_nt; int_nt])); *)                           *)
(* 		(* (int_nt, FuncRewrite ("&", [int_nt; int_nt])); *)                           *)
(* 		(* (int_nt, FuncRewrite ("|", [int_nt; int_nt])); *)                           *)
(* 		(* (int_nt, FuncRewrite ("^", [int_nt; int_nt])); *)                           *)
(* 		(* (int_nt, FuncRewrite ("/", [int_nt; int_nt])); *)                           *)
(* 	]                                                                                *)
	
		