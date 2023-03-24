open Common
open Vocab

open SynthLang
open Components

type aug_rewrite =
	| AugNT of Grammar.non_terminal
	| AugExpr of Exprs.expr * Exprs.signature
	| AugFunc of Operators.op * aug_rewrite list  

let aug_plug (rule: aug_rewrite) (instances: (GrammarUtil.addr * (Exprs.expr * Exprs.signature)) list): Exprs.expr * Exprs.signature  =
	try 
		let rec plug_sub curr_addr rule instances =
			match rule with
			| AugNT nt ->
				(try List.assoc curr_addr instances with Not_found -> assert false) 
			| AugExpr (expr, signature) -> (expr, signature)
			| AugFunc (op, rewrites) ->
				let children : (Exprs.expr * Exprs.signature) list =
					(BatList.mapi (fun i rewrite -> plug_sub (curr_addr@[i]) rewrite instances) rewrites)
				in
				(Exprs.Function (op, BatList.map fst children, Grammar.ret_type_of_func_rewrite op (BatList.map (fun (e, _) -> Grammar.expr_rewrite e) children)),
					Exprs.fun_apply_signature op (BatList.map snd children))
		in
		plug_sub [] rule instances
	with Division_by_zero -> raise Exprs.UndefinedSemantics

let normalized_func_aug_rewrite (op: Operators.op) (children: aug_rewrite list): aug_rewrite =
	let rec expr_children_or_none expr_children unchecked_children =
		match unchecked_children with
		| [] -> Some expr_children
		| AugExpr (e, signature) :: t -> expr_children_or_none (expr_children@[(e, signature)]) t
		| _ -> None
	in
	match expr_children_or_none [] children with
	| Some expr_children ->
		AugExpr (Function (op, BatList.map fst expr_children, Grammar.ret_type_of_func_rewrite op (BatList.map (fun (e, _) -> Grammar.expr_rewrite e) expr_children)),
			Exprs.fun_apply_signature op (BatList.map snd expr_children))
	| None -> AugFunc (op, children)

let aug_plug_rewrite (rule: aug_rewrite) (instances: (GrammarUtil.addr * aug_rewrite) list): aug_rewrite =
	let rec plug_sub curr_addr rule instances =
		match rule with
		| AugNT nt ->
			(try List.assoc curr_addr instances with Not_found -> rule)
		| AugFunc (op, children) -> begin
			let plugged_children : aug_rewrite list =
				(BatList.mapi (fun i child -> plug_sub (curr_addr@[i]) child instances) children)
			in
			normalized_func_aug_rewrite op plugged_children
		end
		| _ -> rule
	in
	plug_sub [] rule instances	

let wrap_aug_rewrite (spec: SynthSpec.Specification.t) (rewrite: Grammar.rewrite): aug_rewrite =
	let rec wrap_aug_rewrite_sub rewrite =
		match rewrite with
		| Grammar.NTRewrite nt -> AugNT nt
		| Grammar.ExprRewrite expr ->
			(* mostly unreachable because this wrapper is called with top-level production rule in most cases *)
			AugExpr (expr, Exprs.compute_signature spec expr)
		| Grammar.FuncRewrite (op, rewrites) -> AugFunc (op, BatList.map wrap_aug_rewrite_sub rewrites)
	in
	wrap_aug_rewrite_sub rewrite

(* ret type: int list list *)
(* e.g., sum{P_i} = 4 where i in {1,2} *)
(* [ [1; 3]; [3; 1]; [2; 2] ] *)
let rec get_size_partitions
	(holes: (GrammarUtil.addr * Grammar.non_terminal) list)
	(target_size: int)
	(components: Components.component_pool)
	: (Grammar.non_terminal * int) list list =
	match holes with 
	| [] -> [[]]
	| (_, nt) :: tl ->
		List.fold_left (fun partitions size ->
			let components_length = Components.get_num_of_sized_components components nt size in
			if components_length > 0 then	
				let rest_partitions = get_size_partitions tl (target_size - size) components in
				(*[[]]*)
				let new_partitions =
					List.filter (fun partition -> 
						(List.length partition) = (List.length holes) && 
						(BatList.sum (BatList.map snd partition)) = target_size
					) (List.map (fun partition -> (nt, size) :: partition) rest_partitions) 
				in
				partitions @ new_partitions 
			else partitions
		) [] (BatList.range 0 `To target_size)

let gen_progress_logger: Logger.periodic_reporter option ref = ref None
let gen_progress_log (s_lazy: unit -> string) =
	match !gen_progress_logger with
	| None -> ()
	| Some p -> Logger.info_period p s_lazy 

(* using components found so far, generate candidates of size `target_size' *)				
let grow (nt: Grammar.non_terminal) (rule: Grammar.rewrite)
	(components: Components.component_pool)
	(desired_sig: Exprs.signature)
	(spec: SynthSpec.Specification.t)
	(target_size: int): unit =
	let start_time = Unix.gettimeofday () in
	let aug_rule = wrap_aug_rewrite spec rule in
	Logger.g_debug_f "grow: target size %d / applying rule %s -> %s"
		target_size
		(Grammar.string_of_non_terminal nt)
		(Grammar.string_of_rewrite rule);
	Logger.g_with_increased_depth (fun () ->
		let holes : (GrammarUtil.addr * Grammar.non_terminal) list = GrammarUtil.get_holes rule in
		if not (BatList.is_empty holes) then begin
			let rule_size = Grammar.size_of_rewrite rule in  
			let size_partitions = get_size_partitions holes (target_size - rule_size) components in
			Logger.g_debug_f "rule_size = %d / size_partitiions = %s" rule_size (string_of_list (string_of_list (fun (n,s) -> Printf.sprintf "%s:%d" (Grammar.string_of_non_terminal n) s)) size_partitions);
			let adder = Components.add_component components nt target_size in
			BatList.iter (fun size_partition ->
				let components_for_holes = BatList.map (fun (sub_nt, size) -> Components.get_sized_components components sub_nt size) size_partition in
				let rec worker (instances: (GrammarUtil.addr * (Exprs.expr * Exprs.signature)) list) (cur_holes: (GrammarUtil.addr * Grammar.non_terminal) list) (cur_components_for_holes: (Exprs.expr * Exprs.signature) list list): unit =
					match cur_holes, cur_components_for_holes with
					| [], [] -> begin
						gen_progress_log (fun () ->
							Printf.sprintf "growing components (target size %d, current total count %d, picked rule = %s)"
								target_size
								(Components.get_num_total_components components)
								(Grammar.string_of_rewrite rule)
						);
						try
							let (new_expr, signature) = aug_plug aug_rule instances in
							if Exprs.compare_signature desired_sig signature = 0 then begin
								Logger.g_info_f "during growing components pool with target size %d, found solution within %d components" target_size (Components.get_num_total_components components);
								raise (SynthSpec.Specification.SolutionFound new_expr)
							end
							else
								adder new_expr signature
						with Exprs.UndefinedSemantics -> ()
					end
					| (addr,nt) :: holes_tail, components_for_hole :: components_for_holes_tail ->
						BatList.iteri (fun component_idx (component, component_signature) ->
							worker (instances @ [(addr,(component, component_signature))]) holes_tail components_for_holes_tail
						) components_for_hole
					| _, _ -> (* unreachable *) begin
						Logger.g_error_f "unreachable in Generator.grow: hole to compos mismatch";
						()
					end
				in
				worker [] holes components_for_holes
			) size_partitions
		end
	);
	let end_time = Unix.gettimeofday () in
	Global.add_compo_gen_time (end_time -. start_time) Global.t

let populate_initial_components (components: Components.component_pool) (desired_sig: SynthLang.Exprs.signature) (spec: SynthSpec.Specification.t)
		(nt_rule_list: (Grammar.non_terminal * Grammar.rewrite) list) (min_size, max_size): unit =
	gen_progress_logger := Some (Logger.create_g_periodic_logger 20000);
	let size_one_processed_components = 
		if min_size = 1 then
			List.iter (fun (nt, rule) ->
				if GrammarUtil.count_holes rule = 0 then
					let adder = Components.add_component components nt 1 in
					(* rule without holes -> terminal, can be computed *)
					try
						let expr = Grammar.expr_of_rewrite_exn rule in
						let signature = Exprs.compute_signature spec expr in
						if Exprs.compare_signature desired_sig signature = 0 then begin
							Logger.g_info_f "During populating size 1 components, found #%d component as solution" (Components.get_num_total_components components);
							raise (SynthSpec.Specification.SolutionFound expr)
						end
						else
							adder expr signature
					with Exprs.UndefinedSemantics -> ()
			) nt_rule_list 
	in
	let rec iter size =
		if (size <= max_size) then begin
			List.iter (fun (nt, rule) ->
				grow nt rule components desired_sig spec size
			) nt_rule_list;
			iter (size + 1)
		end
	in
	iter min_size


let symmetric_addr_of (addr: GrammarUtil.addr) (rewrite: Grammar.rewrite): GrammarUtil.addr option =
	match BatList.rev addr with
	| [] ->
		(* root cannot have sym addr *)
		None
	| last_index :: parent_addr_rev -> begin
		let parent_addr = BatList.rev parent_addr_rev in
		let parent_op = Grammar.op_of_rule (GrammarUtil.access_addr parent_addr rewrite) in
		if Operators.is_commutative_op parent_op then
			Some (BatList.rev ((if last_index = 0 then 1 else 0) :: parent_addr_rev))
		else
			None
	end
