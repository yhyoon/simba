open Common
open Vocab

open SynthLang

open SynthProblem

open SynthBase
open Generator
open Components
open AugSpec

open ComposeCounter

type synth_ctx_main = {
	spec: AugSpec.t;
	subproblem_mode: bool;
	components: Components.component_pool;
	req_comp_size_range: int * int;
	total_sketch_size: int;
	used_sketch_rev: (Grammar.rewrite * Analyzer.AbstState.t) list;
	todo_sketch: (Grammar.rewrite * Analyzer.AbstState.t) list;
}

type synth_ctx_compose = {
	ctx_main: synth_ctx_main;
	min_result_size: int;
	max_result_size: int;
}

type synth_ctx_learn_ite = {
	ctx_main: synth_ctx_main;
	call_depth: int;
	pt_covering_exprs: (int, Exprs.ExprSigSet.t) BatMap.t;
	cond_nt: Grammar.non_terminal;
	then_nt: Grammar.non_terminal;
	else_nt: Grammar.non_terminal;
	less_spec: AugSpec.io_spec list;
	(** nt * index * const |-> ((index * const) list * expr) option
	  * Some (COVERING, EXPR): for nt, index, const -> we found EXPR which covers COVERING
		* None: for nt, index, const -> there is no sub-problem solution for that partial sig
			*)
	nt_subproblem_cache: (Grammar.non_terminal * int * Exprs.const, ((int * Exprs.const) list * Exprs.expr) option) BatMap.t;
}

exception NoSol of string
(* solution * sketch_index * max_term_size *)
exception SolutionFoundInComposer of Exprs.expr * int * int
exception SolutionFoundInSketch of Exprs.expr

let raise_solution_found (ctx_main:synth_ctx_main) (sol: Exprs.expr) =
	if not ctx_main.subproblem_mode then begin
		let s = Components.get_num_total_components ctx_main.components in
		Global.set_component_pool_size_when_sol s Global.t;
		Global.t.summary.final_compo_pool_count <- s;
		Global.t.summary.final_max_compo_size <- Components.max_size ctx_main.components;
	end;
	raise (SolutionFoundInComposer (sol, BatList.length ctx_main.used_sketch_rev, Components.max_size ctx_main.components))

let add_nt_subproblem_sol (ctx_learn_ite: synth_ctx_learn_ite) (nt: Grammar.non_terminal) (less_spec: (int * Exprs.const) list) (sol_opt: Exprs.expr option): synth_ctx_learn_ite =
	let updater (binding: ((int * Exprs.const) list * Exprs.expr) option option) =
			match binding, sol_opt with
			| Some (Some (existing_less_spec, existing_sol)), Some sol when not (helper_less_spec_subset existing_less_spec less_spec) ->
					(** not sure, ignore *)
					binding
			| _, Some sol ->
				  (** new one is definitely better, update *)
					Some (Some (less_spec, sol))
			| Some _, None ->
					(** existing is better, ignore *)
					binding
			| _ ->
					Some None
	in
	{ctx_learn_ite with nt_subproblem_cache =
			BatList.fold_left (fun m (idx, c) ->
							BatMap.update_stdlib (nt, idx, c) updater m
					) ctx_learn_ite.nt_subproblem_cache less_spec
	}

exception NoSolSubProblem of string * int * Exprs.const

(**
 None: dont' know
 Some None: we know no solution with current component pool
 Some Some s: we know a solution s
 *)
let search_nt_subproblem_cache (ctx_learn_ite: synth_ctx_learn_ite) (nt: Grammar.non_terminal) (less_spec: (int * Exprs.const) list): ((int * Exprs.const) list * Exprs.expr) option option =
	let rec aux (less_spec: (int * Exprs.const) list) =
	match less_spec with
	| [] -> None
	| (idx, c) :: tail ->
			let lookup_result = BatMap.find_opt (nt, idx, c) ctx_learn_ite.nt_subproblem_cache in
			match lookup_result with
			| Some (Some (existing_less_spec, sol)) ->
					if helper_less_spec_subset less_spec existing_less_spec then
							lookup_result
					else
							aux tail
			| _ -> None
	in
	aux less_spec

let compose_progress_logger: Logger.periodic_reporter option ref = ref None
let compose_progress_log (s_lazy: unit -> string) =
	match !compose_progress_logger with
	| None -> ()
	| Some p -> Logger.info_period p s_lazy

let get_holes_for_compose (rule: Grammar.rewrite) (sems: Analyzer.AbstState.t): (GrammarUtil.addr * Grammar.non_terminal) list =
	(* with these holes, partial information available * other holes *)
	let rec get_holes_aux (addr: GrammarUtil.addr) (rule: Grammar.rewrite): (GrammarUtil.addr * Grammar.non_terminal) list * (GrammarUtil.addr * Grammar.non_terminal) list =
	match rule with
	| NTRewrite nt -> [(addr, nt)], []
	| ExprRewrite _ -> [], []
	| FuncRewrite (op, operand_rewrites) ->
		let addr0 = addr@[0] in
		match op with
		| Operators.BV_OP (Operators.BV_UN_OP uop) -> begin
			match operand_rewrites with
			| arg0 :: _ ->
				get_holes_aux addr0 arg0
			| _ -> begin
				Logger.g_error_f "invalid operands for %s in %s" (Operators.op_to_string op) (Grammar.string_of_rewrite rule);
				invalid_arg (Printf.sprintf "invalid operands for %s in %s" (Operators.op_to_string op) (Grammar.string_of_rewrite rule))
			end
		end
		| Operators.BV_OP (Operators.BV_BIN_OP bop) -> begin
			let addr1 = addr@[1] in
			match operand_rewrites with
			| arg0 :: arg1 :: _ -> begin
				let (left_holes_high, left_holes_low) = get_holes_aux addr0 arg0 in
				let (right_holes_high, right_holes_low) = get_holes_aux addr1 arg1 in	
				match bop with
				| BV_AND | BV_OR -> (* prioritize partial info of right *)
					(right_holes_high, left_holes_high @ left_holes_low @ right_holes_low)
				| BV_ADD | BV_SUB | BV_XOR -> (* prioritize partial info of both right and left *)
					(right_holes_high @ left_holes_high, left_holes_low @ right_holes_low)
				| BV_MUL
				| BV_LSHR | BV_ASHR | BV_SHL
				| BV_UDIV | BV_SDIV -> (* prioritize full info of right *)
					(right_holes_high @ right_holes_low, left_holes_high @ left_holes_low)
				| BV_UREM | BV_SREM -> (* prioritize fulls info of left *)
					(left_holes_high @ left_holes_low, right_holes_high @ right_holes_low)
			end
			| _ -> begin
				Logger.g_error_f "invalid operands for %s in %s" (Operators.op_to_string op) (Grammar.string_of_rewrite rule);
				invalid_arg (Printf.sprintf "invalid operands for %s in %s" (Operators.op_to_string op) (Grammar.string_of_rewrite rule))
			end
		end
		| _ ->
			(GrammarUtil.get_holes rule, [])
	in
	let (high, low) = get_holes_aux [] rule in
	high @ low

let get_holes_for_compose_tried_idea (rule: Grammar.rewrite) (sems: Analyzer.AbstState.t): (GrammarUtil.addr * Grammar.non_terminal) list =
	let all_holes = GrammarUtil.get_holes rule in
	let all_holes_with_ordering_factor =
		BatList.map (fun (addr, nt) ->
				let index_and_consts =
					Dom.AbstDom.AbstSig.gamma_size_constraint Global.t.cli_options.gamma_size (Analyzer.AbstState.lookup addr sems)
				in
				(addr, nt, BatList.fold_left (fun score (idx, consts) ->
					score *. float_of_int (BatSet.cardinal consts) /. (float_of_int (Global.t.cli_options.gamma_size * 2))) 1.0 index_and_consts)
			) all_holes
	in
	let sorted_holes = BatList.sort (fun (_, _, score1) (_, _, score2) -> BatFloat.compare score1 score2) all_holes_with_ordering_factor in
	BatList.map (fun (addr, nt, _) -> (addr, nt)) sorted_holes

let check_feasibility_general
	(grammar: Grammar.grammar)
    (candidate: Grammar.rewrite)
    (plugged_spot: GrammarUtil.addr)
    (spec: AugSpec.io_spec list)
    (prev_semantics: Analyzer.AbstState.t)
	: Analyzer.Transfer.feasibility =
	match candidate with
	| Grammar.ExprRewrite expr -> begin (* compute exact value *)
	  if AugSpec.is_solution_expr spec expr then begin
			Logger.g_in_debug_lazy (fun () -> Logger.g_debug_f "solution found in checking feasiblity: %s" (SynthLang.Exprs.string_of_expr expr));
			Analyzer.Transfer.DesiredExpr expr
		end
		else
			Analyzer.Transfer.NotDesiredExpr
	end
	| _ -> begin
		let check_start_time = Unix.gettimeofday() in
		let result =
			match Global.t.cli_options.pruning_mode with
			| "bruteforce" ->
				Analyzer.Transfer.DoBruteForce
			| "solver" -> begin
				let feasible = BidirectionalUtils.is_feasible_by_solver grammar spec candidate in
				let result =
					if feasible then
						Analyzer.Transfer.DoBruteForce
					else begin
						Analyzer.Transfer.Infeasible
					end
				in
				Global.add_prune_trial_time (Unix.gettimeofday() -. check_start_time) Global.t;
				result
			end
			| _ -> begin (* abstsem *)
				let result =
					Analyzer.Transfer.check_feasibility candidate plugged_spot spec prev_semantics
				in
				Global.add_prune_trial_time (Unix.gettimeofday() -. check_start_time) Global.t;
				result
			end
		in
		begin match result with
			| Analyzer.Transfer.Infeasible ->
				Global.tick_infeasible Global.t
			| _ -> ()
		end;
		result
	end

type prune_info =
	| PRUNE_NO
	| PRUNE_CONCRETE_SEARCH of int * int

let prefered_operator_group = [
	[Operators.BV_NOT; Operators.BV_NEG] |> BatList.map (fun x -> Operators.BV_UN_OP x);
	[Operators.BV_SHL; Operators.BV_LSHR; Operators.BV_ASHR] |> BatList.map (fun x -> Operators.BV_BIN_OP x);
	[Operators.BV_AND; Operators.BV_OR] |> BatList.map (fun x -> Operators.BV_BIN_OP x);
	[Operators.BV_XOR; Operators.BV_ADD; Operators.BV_SUB; Operators.BV_MUL] |> BatList.map (fun x -> Operators.BV_BIN_OP x);
	[Operators.BV_UDIV; Operators.BV_UREM; Operators.BV_SDIV; Operators.BV_SREM] |> BatList.map (fun x -> Operators.BV_BIN_OP x);
]

let operator_order_map =
	BatList.fold_lefti (fun m outer_idx l ->
			BatList.fold_lefti (fun m inner_idx op ->
					BatMap.add op (outer_idx, inner_idx) m
				) m l
		) BatMap.empty prefered_operator_group

let op_ordering op1 op2 =
	try
		let v1 = BatMap.find op1 operator_order_map in
		let v2 = BatMap.find op2 operator_order_map in
		compare v1 v2
	with Not_found -> compare op1 op2

let topdown_expand
	(grammar: (Grammar.non_terminal, Grammar.rewrite BatSet.t) BatMap.t)
	(spec: AugSpec.io_spec list)
	((sketch_rule, sketch_sem): Grammar.rewrite * Analyzer.AbstState.t)
	(attach_to_rev: (Grammar.rewrite * Analyzer.AbstState.t) list)
	: (Grammar.rewrite * Analyzer.AbstState.t) list
=
	(* pick one closer to root, leftmost one *)
	let holes = GrammarUtil.get_holes sketch_rule in
	let (addr, nt) =
		List.sort (fun (addr1,_) (addr2,_) ->
			let len1 = List.length addr1 in
			let len2 = List.length addr2 in
			if (len1 <> len2) then len1 - len2 
			else compare addr1 addr2    
		) holes
		|> List.hd
	in
	let rules =
		let natural_order_list = Grammar.get_rules nt grammar |> BatSet.to_list in
		(* BatList.sort (fun r1 r2 ->
				match r1, r2 with
				| FuncRewrite(op_str1, _), FuncRewrite(op_str2, _) -> begin
					let op1 = Operators.string_to_bv_op op_str1 in
					let op2 = Operators.string_to_bv_op op_str2 in
					op_ordering op1 op2
				end
				| FuncRewrite _, _ -> 1
				| _, FuncRewrite _ -> -1
				| _, _ -> compare r1 r2
			) natural_order_list *)
		let ite_list, non_ite_list =
			BatList.partition (fun r ->
				match r with
				| Grammar.FuncRewrite(TRI_OP ITE, _) -> true
				| _ -> false
			) natural_order_list
		in
		natural_order_list
	in
	List.fold_left (fun result_rev rule ->
		let n' = GrammarUtil.plug_rewrite sketch_rule [(addr, rule)] in
		let _ =
			Global.top_tick_candidate_cur_iter (GrammarUtil.count_holes n') Global.t
		in
		match check_feasibility_general grammar n' [] spec sketch_sem with
		| Analyzer.Transfer.DesiredExpr sol -> begin
			raise (SolutionFoundInSketch sol)
		end
		| Analyzer.Transfer.Infeasible -> begin (* only for logger *)
			Logger.g_debug_f "infeasible cand at top(skip queue): %s" (Grammar.string_of_rewrite n');
			result_rev
		end
		| Analyzer.Transfer.NotDesiredExpr -> begin (* only for logger *)
			Logger.g_debug_f "not a desired expr at top(skip queue): %s" (Grammar.string_of_rewrite n');
			result_rev
		end
		| Analyzer.Transfer.NeedMoreAnalysis post_sems ->
			(n', post_sems) :: result_rev
		| Analyzer.Transfer.DoBruteForce ->
			(n', sketch_sem) :: result_rev
	) attach_to_rev rules

(* just one-level topdown *)
let topdown_sketches_depth1
	?(start_symbol: Grammar.non_terminal = Grammar.start_nt)
	(grammar: (Grammar.non_terminal, Grammar.rewrite BatSet.t) BatMap.t)
	(spec: AugSpec.io_spec list)
	: (Grammar.rewrite * Analyzer.AbstState.t) list
=
	let (root_rule, root_sem) =
		(Grammar.NTRewrite start_symbol,
			Analyzer.AbstState.update_value [] (AugSpec.alpha_output_spec (BatList.map snd spec)) Analyzer.AbstState.empty)
	in
	topdown_expand grammar spec (root_rule, root_sem) [] |> BatList.rev

(* just two-level topdown *)
let topdown_sketches_depth2
	?(start_symbol: Grammar.non_terminal = Grammar.start_nt)
	(grammar: (Grammar.non_terminal, Grammar.rewrite BatSet.t) BatMap.t)
	(spec: AugSpec.io_spec list)
	: (Grammar.rewrite * Analyzer.AbstState.t) list
=
	let base = topdown_sketches_depth1 ~start_symbol:start_symbol grammar spec in
	BatList.fold_left (fun acc_rev (sketch, sem) ->
			topdown_expand grammar spec (sketch, sem) acc_rev
		) [] base |> BatList.rev

(* expand selective *)
let topdown_sketches_selective
	?(start_symbol: Grammar.non_terminal = Grammar.start_nt)
	(grammar: (Grammar.non_terminal, Grammar.rewrite BatSet.t) BatMap.t)
	(spec: AugSpec.io_spec list)
	: (Grammar.rewrite * Analyzer.AbstState.t) list
=
	let base = topdown_sketches_depth1 ~start_symbol:start_symbol grammar spec in
	BatList.fold_left (fun acc_rev (sketch, sem) ->
		let do_not_expand = (sketch, sem) :: acc_rev in
		match sketch with
		| Grammar.FuncRewrite(op, _) -> begin
			match op with
			| Operators.BV_OP Operators.BV_UN_OP _ ->
				do_not_expand
			| Operators.BV_OP Operators.BV_BIN_OP bop -> begin
				match bop with
				| Operators.BV_AND | Operators.BV_OR
				| Operators.BV_SHL | Operators.BV_ASHR | Operators.BV_LSHR
				| Operators.BV_ADD | Operators.BV_SUB | Operators.BV_XOR | Operators.BV_MUL ->
					(* expand 'analyzer is good at' ops *)
					topdown_expand grammar spec (sketch, sem) acc_rev
				| _ ->
					do_not_expand
			end
			| _ ->
				do_not_expand
		end
		| _ ->
			do_not_expand
		) [] base |> BatList.rev

let topdown_sketches_hole_count
	?(start_symbol: Grammar.non_terminal = Grammar.start_nt)
	(grammar: (Grammar.non_terminal, Grammar.rewrite BatSet.t) BatMap.t)
	(spec: AugSpec.io_spec list)
	(dest_hole_count: int)
	: (Grammar.rewrite * Analyzer.AbstState.t) list
=
	let (root_rule, root_sem) =
		(Grammar.NTRewrite start_symbol,
			Analyzer.AbstState.update_value [] (AugSpec.alpha_output_spec (BatList.map snd spec)) Analyzer.AbstState.empty)
	in
	let rec aux gen =
		match BatList.find_opt (fun (skel, _) -> GrammarUtil.count_holes skel >= dest_hole_count) gen with
		| Some (found, _) -> begin
			Logger.g_debug_f "%s has enough (%d) holes >= %d, stop expansion" (Grammar.string_of_rewrite found) (GrammarUtil.count_holes found) dest_hole_count;
			gen
		end
		| None ->
			let step =
				BatList.fold_left (fun acc_rev (sketch, sem) ->
					topdown_expand grammar spec (sketch, sem) acc_rev
				) [] gen |> BatList.rev
			in
			if BatSet.equal (BatSet.of_list gen) (BatSet.of_list step) then begin
				Logger.g_info_f "topdown: expansion step did not make change, stop topdown expansion";
				step
			end else
				aux step
	in
	aux [(root_rule, root_sem)]

let topdown_by_option (grammar: Grammar.grammar) (spec: AugSpec.io_spec list): (Grammar.rewrite * Analyzer.AbstState.t) list =
	match Global.t.cli_options.topdown with
	| "depth1" -> begin
		Logger.g_debug_f "topdown strategy: depth1";
		topdown_sketches_depth1 grammar spec
	end
	| "depth2" ->
		Logger.g_debug_f "topdown strategy: depth2";
		topdown_sketches_depth2 grammar spec
	| topdown_name ->
		if BatString.starts_with topdown_name "hole" then
			let count_string = BatString.sub topdown_name 4 (BatString.length topdown_name - 4) in
			match int_of_string_opt count_string with
			| Some count -> begin
				Logger.g_debug_f "topdown strategy: hole-count %d" count;
				topdown_sketches_hole_count grammar spec count
			end
			| _ -> begin
				Logger.g_error_f "invalid count after hole: %s => use default(hole2)" topdown_name;
				topdown_sketches_hole_count grammar spec 2
			end
		else begin
			(* use default *)
			Logger.g_error_f "unknown topdown name: %s => use default(hole2)" topdown_name;
			topdown_sketches_hole_count grammar spec 2
		end

let log_component_sizes (grammar: Grammar.grammar) (components: component_pool): unit =
	Logger.g_info_f "************ components nt -> exprs ************";
	Logger.g_with_increased_depth (fun () ->
		BatMap.iter (fun nt _ ->
			let count = get_num_of_components components nt in
			Logger.g_info_f "%s -> (%d)" (Grammar.string_of_non_terminal nt) count;
			let rec by_size (size: int): unit =
				if size <= Components.max_size components + 2 then begin
					let sub_count = Components.get_num_of_sized_components components nt size in
					if sub_count > 0 then begin
						Logger.g_info_f "size %d -> (%d)" size sub_count
					end;
					by_size (size + 1)
				end
				else ()
			in
			Logger.g_with_increased_depth (fun () ->
				by_size 1
			)
		) grammar
	)

(** spec helper: extract interested signature as (idx * c) list *)
let make_partial_output_sig (pts: int list) (spec: AugSpec.io_spec list): (int * Exprs.const) list =
	list_sub_sparse (zip_with_index (BatList.map snd spec)) pts
		|> BatList.filter_map (function
			| (idx, AugSpec.OConcrete c) -> Some (idx, c)
			| (_, AugSpec.ODontCare _) -> None
			| (_, AugSpec.OAbstract _) -> None)

(** spec helper: turn non-alive index to doncare *)
let turn_dontcare (spec: AugSpec.io_spec list) (alive_idx: int list): AugSpec.io_spec list =
	BatList.map (fun (idx, (inputs, const_opt)) ->
		if BatList.mem idx alive_idx then
			(idx, (inputs, const_opt))
		else
			match const_opt with
			| AugSpec.ODontCare ty ->
				(idx, (inputs, const_opt))
			| _ ->
				(idx, (inputs, AugSpec.ODontCare (AugSpec.type_of_output_spec const_opt)))
	) (zip_with_index spec) |> BatList.map snd

let covering_expr_set
	(ctx_learn_ite: synth_ctx_learn_ite)
	(partial_spec: (int * Exprs.const) list)
: Exprs.ExprSigSet.t =
  let full_spec = ctx_learn_ite.ctx_main.spec.sem_spec.spec_cex in
	let nt = ctx_learn_ite.then_nt in
	let components = ctx_learn_ite.ctx_main.components in
	let r =
		Components.find_exprs_of_nt_partial_sig
			components
			nt
			(make_partial_output_sig (BatList.map fst partial_spec) full_spec)
	in
	match search_nt_subproblem_cache ctx_learn_ite nt partial_spec with
	| Some (Some (covering_pts, expr))
			when Components.helper_less_spec_subset partial_spec covering_pts ->
		Exprs.ExprSigSet.add (expr, Exprs.compute_signature (BatList.map fst full_spec) expr) r
	| _ ->
		r

(* fill non-covered pts by solve sub-problem *)
let compute_entropy (pt_covering_exprs: (int, Exprs.ExprSigSet.t) BatMap.t) (pred_partial: (int * Exprs.const) list): float =
	let exprs =
		BatList.fold_left (fun s (idx, _) ->
			Exprs.ExprSigSet.union s (BatMap.find idx pt_covering_exprs)
			) Exprs.ExprSigSet.empty pred_partial
	in
	let cover_pts_map =
		Exprs.ExprSigSet.fold (fun (_, expr_signature) cover_pts_map ->
			let indexed_sig = zip_with_index (Exprs.const_list_of_signature expr_signature) in
			let covered_pts =
				list_sub_sparse indexed_sig (BatList.map fst pred_partial)
			in
			Exprs.SignatureMap.add expr_signature covered_pts cover_pts_map
		) exprs Exprs.SignatureMap.empty
	in
	Exprs.ExprSigSet.fold (fun (expr, expr_signature) acc_expr ->
			let pts_covered_by_expr = Exprs.SignatureMap.find expr_signature cover_pts_map in
			BatList.fold_left (fun acc_pts (idx, c) ->
					let ent_by_pt =
						(* 이 부품이 커버하는 점의 수 / 이 점이 커버하는 부품들이 커버하는 점의 수의 합 *)
						let fast_dt_divisor() = 
							(* 이 점이 커버하는 부품의 수 *)
							BatMap.find idx pt_covering_exprs |> Exprs.ExprSigSet.cardinal |> float_of_int
						in
						let normal_dt_divisor() =
							let exprs = BatMap.find idx pt_covering_exprs in
							Exprs.ExprSigSet.fold (fun (_, expr_signature) sum ->
									sum +
										BatList.length (Exprs.SignatureMap.find expr_signature cover_pts_map)
								) exprs 0
							|> float_of_int
						in
						let divisor =
							match Global.t.cli_options.dt_predicate_order with
							| Global.NormalEntropy ->
								normal_dt_divisor()
							| _ ->
								fast_dt_divisor()
						in
						(BatList.length pts_covered_by_expr |> float_of_int)
						/. divisor
					in
					acc_pts +. ent_by_pt
				) acc_expr pts_covered_by_expr
		) exprs 0.0

let rec compose_for_sketch
	(synth_ctx_compose: synth_ctx_compose)
	(compose_counter: compose_counter)
	(intermediate: Grammar.rewrite)
	(sems: Analyzer.AbstState.t)
	(enums: (GrammarUtil.addr * CompEnum.t) list)
	(chosen_components: (Exprs.expr * int) list)
	(holes: (GrammarUtil.addr * Grammar.non_terminal) list)
: unit =
	match holes with
	| [] -> begin
		match intermediate with
		| ExprRewrite expr ->
			if AugSpec.is_solution_expr synth_ctx_compose.ctx_main.spec.sem_spec.spec_cex expr then
				raise_solution_found synth_ctx_compose.ctx_main expr
			else tick_compose_counter compose_counter CC_COMPLETE
		| _ -> begin
			Logger.g_error_f "non_expr result is generated in bidirectional emumeration: %s" (Grammar.string_of_rewrite intermediate);
			failwith "non_expr result is generated in bidirectional emumeration"
		end
	end
	| (addr, nt) :: holes_tail ->
		let _ =
			compose_progress_log (fun () ->
				let enum_states: string list =
					BatList.map (fun (enum_addr, enum) ->
						Printf.sprintf "  enum by %s for addr %s -> remain %d/%d"
							(CompEnum.string_of_iter_type (CompEnum.iter_type enum))
							(string_of_list string_of_int enum_addr)
							(CompEnum.count enum)
							(CompEnum.initial_count enum)
					) enums
				in
				Printf.sprintf "  progress: intermediate %s /: filling addr %s\n%s"
					(Grammar.string_of_rewrite intermediate) (string_of_list string_of_int addr)
					(string_of_list ~first:"  " ~last:"" ~sep:"\n  " identity enum_states)
			)
		in
		let (prune_info, components_for_cur_hole) =
			let (min_cur_compo_size, max_cur_compo_size) =
				let max_component_size = SynthBase.Components.max_size synth_ctx_compose.ctx_main.components in
				let compo_size_range_from_result_size =
					let l = (synth_ctx_compose.min_result_size
						- Grammar.size_of_rewrite intermediate
						- max_component_size * BatList.length holes_tail)
					in
					let r =
						(synth_ctx_compose.max_result_size
						- Grammar.size_of_rewrite intermediate
						- BatList.length holes_tail)
					in
					(l,r)
				in
				let compo_size_range_from_neccessary_cond =
					let (l,r) = synth_ctx_compose.ctx_main.req_comp_size_range in
					if BatList.is_empty holes_tail &&
						not (
							BatList.exists (fun (_, size) -> l <= size && size <= r) chosen_components
						)
					then
						synth_ctx_compose.ctx_main.req_comp_size_range
					else
						(1, max_component_size)
				in
				(max (fst compo_size_range_from_result_size) (fst compo_size_range_from_neccessary_cond),
				min (snd compo_size_range_from_result_size) (snd compo_size_range_from_neccessary_cond))
			in
			if min_cur_compo_size > max_cur_compo_size then
				(PRUNE_NO, CompEnum.empty())
			else
				let index_and_consts =
						Dom.AbstDom.AbstSig.gamma_size_constraint Global.t.cli_options.gamma_size (Analyzer.AbstState.lookup addr sems)
				in
				(* let _ =
					let from_normal_gamma = Dom.AbstDom.AbstSig.gamma_size_constraint Global.t.cli_options.gamma_size (Analyzer.AbstState.lookup addr sems) in
					let worse =
						let rec loop l1 l2 =
							match l1, l2 with
							| [], [] | _, [] -> false
							| [], _ -> true
							| (i1, c1) :: t1, (i2, c2) :: t2 ->
								if i1 < i2 then
									loop t1 l2
								else if i1 = i2 then
									if BatSet.subset c1 c2 then
										loop t1 t2
									else
										true
								else
									true
						in
						loop index_and_consts from_normal_gamma
					in
					if worse then begin
						Logger.g_error_f "new gamma is worse than old for %s: %s vs %s"
							(Dom.AbstDom.AbstSig.to_string (Analyzer.AbstState.lookup addr sems))
							(string_of_list (fun (i, consts) -> Printf.sprintf "(%d, %s)" i (string_of_set Exprs.string_of_const consts)) index_and_consts)
							(string_of_list (fun (i, consts) -> Printf.sprintf "(%d, %s)" i (string_of_set Exprs.string_of_const consts)) from_normal_gamma);
					end
				in *)
				let elem_wise_fold (f: (int * Exprs.const) list -> 'a -> 'a) (index_set: (int * Exprs.const BatSet.t) list) (z: 'a): 'a =
					let rec aux (f: (int * Exprs.const) list -> 'a -> 'a) (index_set: (int * Exprs.const BatSet.t) list) (inter_rev: (int * Exprs.const) list) (z: 'a): 'a =
						match index_set with
						| [] ->
							f (BatList.rev inter_rev) z
						| (idx, set) :: t ->
							BatSet.fold (fun c z ->
									aux f t ((idx, c) :: inter_rev) z
								) set z
					in
					aux f index_set [] z
				in
				let expected_no_prune_enum_size() =
					BatEnum.range ~until:max_cur_compo_size min_cur_compo_size
					|> BatEnum.fold (fun sum cs -> Components.get_num_of_sized_components synth_ctx_compose.ctx_main.components nt cs + sum) 0
				in
				let without_constant_enum() =
					let default_ranged_enum() =
						CompEnum.make_ranged min_cur_compo_size max_cur_compo_size synth_ctx_compose.ctx_main.components nt
					in
					match symmetric_addr_of addr intermediate with
					| None ->
						default_ranged_enum()
					| Some sym_addr -> begin
						try
							let already_iterating_at_symmetric = BatList.assoc sym_addr enums in
							if CompEnum.iter_type already_iterating_at_symmetric = CompEnum.IterSymmBreak then
								(* 이 경우 바로 아래의 빈칸이 두개 남은 케이스로 인해 neccessary_compo_size_range 부터 사용중이므로 여기선 symmetric break을 더 활용할 수 없고 전체를 순회해야함 *)
								default_ranged_enum()
							else
								CompEnum.clone_ranged ~iter_type:(Some CompEnum.IterSymmBreak) min_cur_compo_size max_cur_compo_size already_iterating_at_symmetric
						with Not_found -> begin
							match holes_tail with
							| (last_hole, _) :: [] ->
								if last_hole = sym_addr then (* 현재 구멍이 두 개만 남았고, 그 구멍은 (symm_op [addr] [sym_addr]) 과 같은 형태로 존재할 때 *)
									let (l,r) = synth_ctx_compose.ctx_main.req_comp_size_range in
									if not (
										(* 이미 빈칸에 채운 부품 중에 꼭 넣어야할 크기 부품이 아직 포함되지 않았다면 *)
										BatList.exists (fun (_, size) -> l <= size && size <= r) chosen_components
									) then
										(* 어차피 꼭 넣어야할 크기 부품이 두 구멍 중 한 칸에는 꼭 들어가야하므로 그것을 이번 구멍에 먼저 채워버린다 *)
										CompEnum.make_ranged ~iter_type:(Some CompEnum.IterSymmBreak) l r synth_ctx_compose.ctx_main.components nt
									else
										default_ranged_enum()
								else
									default_ranged_enum()
							| _ ->
								default_ranged_enum()
						end
					end
				in
				if BatList.length index_and_consts = BatList.length synth_ctx_compose.ctx_main.spec.sem_spec.spec_cex then
					(* use full signature *)
					let sig_matching_exprs =
						elem_wise_fold (fun indexed_sig (cnt, acc) ->
								let signature = BatList.map snd indexed_sig |> Exprs.signature_of_const_list in
								try
									let expr = find_expr_of_nt_sig synth_ctx_compose.ctx_main.components nt signature in
									let size = Exprs.size_of_expr expr in
									if min_cur_compo_size <= size && size <= max_cur_compo_size then
										(cnt + 1, Exprs.ExprSigSet.add (expr, signature) acc)
									else
										(cnt + 1, acc)
								with Not_found ->
									(cnt + 1, acc)
							) index_and_consts (0, Exprs.ExprSigSet.empty) |> snd
					in
					let cardinal = Exprs.ExprSigSet.cardinal sig_matching_exprs in
					Logger.g_debug_lazy (fun () ->
						let single = BatList.for_all BatSet.is_singleton (BatList.map snd index_and_consts) in
						Printf.sprintf "composing %s in %s / using full constant%s %s%s for %d io pairs, iter for %d compos instead of %d"
							(string_of_list string_of_int addr)
							(Grammar.string_of_rewrite intermediate)
							(if single then "" else "s")
							(if single then "" else "(mutliple="^string_of_int cardinal^")")
							(string_of_list (fun (_,cs) ->
								if BatSet.is_singleton cs then Exprs.string_of_const (BatSet.choose cs)
								else string_of_set Exprs.string_of_const cs)
								index_and_consts
							)
							(BatList.length synth_ctx_compose.ctx_main.spec.sem_spec.spec_cex)
							cardinal
							(get_num_of_components synth_ctx_compose.ctx_main.components nt));
					(PRUNE_CONCRETE_SEARCH (cardinal, expected_no_prune_enum_size()), CompEnum.from_set sig_matching_exprs)
				else if not (BatList.is_empty index_and_consts) then
					(* use partial signature *)
					let exprs =
						elem_wise_fold (fun indexed_sig (cnt, acc) ->
								let found = find_exprs_of_nt_partial_sig ~expr_size_range_opt:(Some(min_cur_compo_size, max_cur_compo_size)) synth_ctx_compose.ctx_main.components nt indexed_sig in
								(cnt + 1, Exprs.ExprSigSet.union found acc)
							) index_and_consts (0, Exprs.ExprSigSet.empty) |> snd
					in
					let cardinal = Exprs.ExprSigSet.cardinal exprs in
					Logger.g_debug_lazy (fun () -> Printf.sprintf "composing %s in %s / using partial constants %s for %d io pairs, iter for %d compos instead of %d"
							(string_of_list string_of_int addr)
							(Grammar.string_of_rewrite intermediate)
							(string_of_list (fun (idx,cs) ->
								Printf.sprintf "(%d,%s)"
									idx
									(if BatSet.is_singleton cs then Exprs.string_of_const (BatSet.choose cs)
									else string_of_set Exprs.string_of_const cs)
								) index_and_consts
							)
							(BatList.length synth_ctx_compose.ctx_main.spec.sem_spec.spec_cex)
							cardinal
							(get_num_of_components synth_ctx_compose.ctx_main.components nt));
					(PRUNE_CONCRETE_SEARCH (cardinal, expected_no_prune_enum_size()), CompEnum.from_set exprs)
				else (PRUNE_NO, without_constant_enum())
		in (* end of components_for_cur_hole *)
		let _ = (* handle pruning counter *)
			match prune_info with
			| PRUNE_CONCRETE_SEARCH (less, full) ->
				if full > 0 && less < full then begin
					let _ = (* primary counter *)
						if less = 0 then
							tick_compose_counter compose_counter CC_INFEAS_SEARCH
						else
							tick_compose_counter compose_counter CC_LESS_ITER
					in
					(* secondary counter - estimated future effect *)
					let remain_nt_compo_counts = BatList.map (fun (_, remain_nt) -> Components.get_num_of_components synth_ctx_compose.ctx_main.components remain_nt) holes_tail |> BatList.rev in
					match remain_nt_compo_counts with
					| [] ->
						add_compose_counter compose_counter CC_PRUNE_COMPLETE (Int64.of_int (full - less))
					| last_pang :: mid ->
						let approx_inter = BatList.fold_left (fun sum64 i -> Int64.mul sum64 (Int64.of_int i)) (Int64.of_int (full - less)) mid in
						add_compose_counter compose_counter CC_PRUNE_INTER approx_inter;
						add_compose_counter compose_counter CC_PRUNE_COMPLETE (Int64.mul approx_inter (Int64.of_int last_pang))
				end
				else (* no exprs in size *)
					()
			| _ -> ()
		in
		CompEnum.iter (fun (expr, expr_signature, expr_size) ->
			let plugged_rewrite = GrammarUtil.plug_rewrite intermediate [(addr, ExprRewrite expr)] in
			let _ =
				let plugged_hole_count = GrammarUtil.count_holes plugged_rewrite in
				let cc_item =
					if plugged_hole_count = 0 then
						CC_COMPLETE
					else
						CC_INTER
				in
				tick_compose_counter compose_counter cc_item;
				Global.sub_tick_candidate_cur_iter plugged_hole_count Global.t;
			in
			let feasiblity =
				check_feasibility_general
					synth_ctx_compose.ctx_main.spec.syn_spec.grammar
					plugged_rewrite
					addr
					synth_ctx_compose.ctx_main.spec.sem_spec.spec_cex sems
			in
			match feasiblity with
			| Analyzer.Transfer.DesiredExpr sol -> begin
				raise_solution_found synth_ctx_compose.ctx_main sol
			end
			| Analyzer.Transfer.NotDesiredExpr -> begin
				Logger.g_in_debug_lazy (fun () ->
					if GrammarUtil.count_holes plugged_rewrite = 0 then begin (* debug logger only *)
						Logger.g_debug_f "  not a desired expression %s" (Grammar.string_of_rewrite plugged_rewrite)
					end
				)
			end
			| Analyzer.Transfer.Infeasible -> begin
				tick_compose_counter compose_counter CC_INFEAS;
				(
					(* secondary counter - estimated future effect *)
					let remain_nt_compo_counts = BatList.map (fun (_, remain_nt) -> Components.get_num_of_components synth_ctx_compose.ctx_main.components remain_nt) holes_tail |> BatList.rev in
					match remain_nt_compo_counts with
					| [] -> (* unreachable...? *)
						add_compose_counter compose_counter CC_PRUNE_COMPLETE 1L
					| last_pang :: mid ->
						let approx_inter = BatList.fold_left (fun sum64 i -> Int64.mul sum64 (Int64.of_int i)) 1L mid in
						add_compose_counter compose_counter CC_PRUNE_INTER approx_inter;
						add_compose_counter compose_counter CC_PRUNE_COMPLETE (Int64.mul approx_inter (Int64.of_int last_pang))
				);
				Logger.g_in_debug_lazy (fun () ->
					if GrammarUtil.count_holes plugged_rewrite > 0 then begin (* debug logger only *)
						Logger.g_debug_f "  infeasible intermediate %s" (Grammar.string_of_rewrite plugged_rewrite)
					end
				);
			end
			| Analyzer.Transfer.NeedMoreAnalysis post_sems -> begin
				compose_for_sketch synth_ctx_compose compose_counter plugged_rewrite post_sems ((addr, components_for_cur_hole) :: enums) ((expr, expr_size) :: chosen_components) holes_tail
			end
			| Analyzer.Transfer.DoBruteForce -> begin
				compose_for_sketch synth_ctx_compose compose_counter plugged_rewrite sems ((addr, components_for_cur_hole) :: enums) ((expr, expr_size) :: chosen_components) holes_tail
			end
		) components_for_cur_hole
 
and learn_ite
	(ctx_learn_ite: synth_ctx_learn_ite)
: Exprs.expr option
=
	let components = ctx_learn_ite.ctx_main.components in
	let _ =
		if ctx_learn_ite.call_depth = 0 then
			Logger.g_debug_f "learn_ite for spec %s" (string_of_list AugSpec.string_of_io_spec ctx_learn_ite.less_spec)
	in
	let indexed_partial_desired_sig =
		zip_with_index (BatList.map snd ctx_learn_ite.less_spec)
		|> BatList.filter_map (function
			| (idx, AugSpec.OConcrete c) -> Some (idx, c)
			| (_, AugSpec.ODontCare _) -> None
			| (_, AugSpec.OAbstract _) -> None)
	in
	let pts = BatList.map fst indexed_partial_desired_sig in
	let full_covering_exprs = covering_expr_set ctx_learn_ite indexed_partial_desired_sig in
	if not (Exprs.ExprSigSet.is_empty full_covering_exprs) then begin
		(* fit component without ite! Done *)
		Logger.g_debug_lazy (fun () -> Printf.sprintf "found fit exprs: %d" (Exprs.ExprSigSet.cardinal full_covering_exprs));
		Exprs.ExprSigSet.enum full_covering_exprs
		|> BatEnum.arg_min (fun (e, _) -> Exprs.size_of_expr e)
		|> fst |> BatOption.some
	end
	else if BatList.length indexed_partial_desired_sig <= 1 then begin
		Logger.g_debug "indexed partial desired sig length is less than 2, give up";
		(* give up *)
		None
	end
	else begin
		(* build decision tree *)
		let (covered, ctx_learn_ite) =
			if ctx_learn_ite.call_depth = 0 then begin
				(* fill non-covered pts by solve sub-problem *)
				let need_cover_partial_sig =
					BatList.filter (fun (idx, c) ->
							covering_expr_set ctx_learn_ite [(idx, c)] |> Exprs.ExprSigSet.is_empty
						) indexed_partial_desired_sig
				in
				Logger.g_debug_lazy (fun () ->
					Printf.sprintf "need cover partial sig: %s"
						(string_of_list
							(fun (idx, c) ->
								Printf.sprintf "%d:%s" idx (Exprs.string_of_const c))
							need_cover_partial_sig
						)
				);
				let rec fill_not_covered_pts ctx_learn_ite ps =
					match ps with
					| [] -> begin
						(* build pt covering table *)
						let pt_covering_exprs =
							BatList.enum indexed_partial_desired_sig
							|> BatEnum.map (fun (idx, c) -> (idx, covering_expr_set ctx_learn_ite [(idx, c)]))
							|> BatMap.of_enum
						in
						(true, {ctx_learn_ite with pt_covering_exprs = pt_covering_exprs})
					end
					| (idx, c) :: ps_tail -> begin
						try begin
							(* 여기선 일반 component 는 찾을 필요가 없다. 거기 없었어서 지금 이 계산을 하고 있는 것이기 때문. *)
							match search_nt_subproblem_cache ctx_learn_ite ctx_learn_ite.then_nt [(idx, c)] with
							| Some (Some (_, e)) -> begin
								Logger.g_debug "re-visited subproblem, get from cache";
								(* subproblem 이므로 기록은 필요 없지만 같은 인터페이스 사용하기로 *)
								raise_solution_found ctx_learn_ite.ctx_main e
							end
							| Some None -> begin
								Logger.g_debug "re-visited subproblem with no sol, give up";
								raise (NoSol "re-visited subproblem with no sol")
							end
							| None ->
								let less_spec =
									turn_dontcare ctx_learn_ite.less_spec [idx]
								in
								let topdowns: (Grammar.rewrite * Analyzer.AbstState.t) list =
								  (* 매번 새로 sketch 만드는 이유: less_spec 기준으로 분석해야하기 때문 *)
									topdown_sketches_hole_count
										~start_symbol:ctx_learn_ite.then_nt
										ctx_learn_ite.ctx_main.spec.syn_spec.grammar
										less_spec
										2
								in
								Logger.g_with_increased_depth (fun () ->
									Logger.g_info_f "start to solve subproblem for %d:%s" idx (Exprs.string_of_const c);
									main_loop {ctx_learn_ite.ctx_main with
											subproblem_mode=true;
											spec={ctx_learn_ite.ctx_main.spec with
											  sem_spec = {ctx_learn_ite.ctx_main.spec.sem_spec with
													spec_cex=less_spec
												}
											}
											;
											req_comp_size_range=(1, Components.max_size components);
											total_sketch_size=BatList.length topdowns;
											used_sketch_rev=[];
											todo_sketch=topdowns;
										};
									Logger.g_info_f "unreachable: main did not throw";
								);
								invalid_arg "unreachable: main did not throw"
							end
						with
						| NoSol s as exn -> begin
							Logger.g_info_f "subproblem NoSol %s" s;
							raise (NoSolSubProblem (s, idx, c))
						end
						| SolutionFoundInComposer (e, _, _) -> begin
							let s = Exprs.compute_signature (BatList.map fst ctx_learn_ite.less_spec) e in
							let cl = Exprs.const_list_of_signature s |> zip_with_index in
							let covered =
								BatList.filter_map (fun (x,y) ->
									if BatList.mem (x,y) indexed_partial_desired_sig
									then Some x
									else None
								) cl
							in
							let ps_tail' =
								BatList.filter (fun x -> not (BatList.mem x cl)) ps_tail
							in
							Logger.g_debug_lazy (fun () -> Printf.sprintf "attached subproblem solution to terms: %s" (Exprs.string_of_expr e));
							fill_not_covered_pts (add_nt_subproblem_sol ctx_learn_ite ctx_learn_ite.then_nt (make_partial_output_sig covered ctx_learn_ite.less_spec) (Some e)) ps_tail'
						end
					end
				in
				try
					fill_not_covered_pts ctx_learn_ite need_cover_partial_sig
				with
				| NoSolSubProblem (_, idx, c) -> begin
					Logger.g_info_f "fail to solve subproblem";
					(false, add_nt_subproblem_sol ctx_learn_ite ctx_learn_ite.then_nt [(idx, c)] None)
				end
			end
			else (true, ctx_learn_ite) (* current ctx is not top_call -> already covered in top_call *)
		in
		if not covered then
			None
		else
			(* ready to do recursion *)
			let nt_sig_to_expr = components.Components.nt_sig_to_expr in
			let cond_sig_to_expr = BatMap.find ctx_learn_ite.cond_nt nt_sig_to_expr in
			let pt_to_expr_set: (int * Exprs.const * Exprs.ExprSigSet.t) list =
				BatList.map (fun (pt, c) ->
					(pt, c, covering_expr_set ctx_learn_ite [(pt, c)])
				) indexed_partial_desired_sig
			in
			let predicates =
				let target_predicates =
					(* predicate signatures which altering true/false *)
					Exprs.SignatureMap.bindings cond_sig_to_expr
					|> BatList.filter_map (fun (signature, expr) ->
						let const_list = Exprs.const_list_of_signature signature in
						let partial_const_list = BatList.combine pts (list_sub_sparse const_list pts) in
						let (then_partial, else_partial) =
							BatList.partition (function
								| (idx, Exprs.CBool true) -> true
								| (idx, _) -> false
							) partial_const_list
						in
						if BatList.is_empty then_partial || BatList.is_empty else_partial then None
						else
							let then_covered =
								covering_expr_set ctx_learn_ite then_partial
								|> Exprs.ExprSigSet.is_empty |> not
							in
							let else_covered =
								covering_expr_set ctx_learn_ite then_partial
								|> Exprs.ExprSigSet.is_empty |> not
							in
							(* then branch example number * then branch is easily covered * else branch... * predicate sig and expr *)
							Some (then_partial, then_covered, else_partial, else_covered, signature, expr)
					)
				in
				let ordering =
					match Global.t.cli_options.dt_predicate_order with
					| Global.HeuristicScore1 -> begin
						fun predicates ->
							let sort =
								BatList.stable_sort (fun (then1, then1_covered, else1, else1_covered, _, e1) (then2, then2_covered, else2, else2_covered, _, e2) ->
									if then1_covered && else1_covered then
										(* easy cover both = most priority *)
										-1
									else if then2_covered && else2_covered then
										(* easy cover both = most priority *)
										1
									else
										let longer_first =
											[(then1, then1_covered, 0); (else1, else1_covered, 1); (then2, then2_covered, 2); (else2, else2_covered, 3)]
											|> BatList.sort (fun (a,_,_) (b,_,_) -> (BatList.length b) - (BatList.length a))
										in
										let best = BatList.find_opt (fun (partial_pred_sig, covered, code) ->
												(* choose predicate with a branch covering many io examples *)
												covered
											) longer_first
										in
										match best with
										| Some (_, _, 0) | Some (_, _, 1) -> -1
										| Some (_, _, 2) | Some (_, _, 3) -> 1
										| _ ->
											BatList.length then1 * BatList.length else1 - BatList.length then2 * BatList.length else2
								)
							in
							sort predicates
					end
					| _ -> begin (* entropy *)
						fun predicates ->
							let scoring =
								BatList.map (fun ((then_partial, then_covering_exprs, else_partial, else_covering_exprs, e_sig, e) as el) ->
									let then_entropy = compute_entropy ctx_learn_ite.pt_covering_exprs then_partial in
									let else_entropy = compute_entropy ctx_learn_ite.pt_covering_exprs else_partial in
									let score =
										(float_of_int (BatList.length then_partial)) /. (float_of_int (BatList.length pts)) *. then_entropy +. 
										(float_of_int (BatList.length else_partial)) /. (float_of_int (BatList.length pts)) *. else_entropy
									in
									(el, score)
								)
							in
							let sort =
								BatList.stable_sort (fun ((_, then1_covered, _, else1_covered, _, _) as el1, score1) ((_, then2_covered, _, else2_covered, _, _) as el2, score2) ->
									if then1_covered && else1_covered then
										(* easy cover both = most priority *)
										-1
									else if then2_covered && else2_covered then
										(* easy cover both = most priority *)
										1
									else
										Float.compare score2 score1
								)	
							in
							scoring predicates |> sort |> BatList.map fst
					end
				in
				ordering target_predicates
			in
			Logger.g_debug_lazy (fun () -> Printf.sprintf "useful predicates from |%d| components: %s"
				(Exprs.SignatureMap.cardinal cond_sig_to_expr)
				(string_of_list (fun (a,b,c,d,e,f) -> Exprs.string_of_expr f) predicates)
			);
			let predicates =
				BatList.take 1 predicates
			in
			let rec try_predicates
				(remaining_predicates:
					((int * Exprs.const) list * bool *
					(int * Exprs.const) list * bool *
					Exprs.signature * Exprs.expr) list) =
				match remaining_predicates with
				| [] -> None
				| (then_partial_sig, then_covering_exprs, else_partial_sig, else_covering_exprs, pred_sig, pred) :: tail ->
					let (then_pts, else_pts) =
						(BatList.map fst then_partial_sig, BatList.map fst else_partial_sig)
					in
					let then_branch_opt =
						Logger.g_with_increased_depth (fun () -> 
							learn_ite {ctx_learn_ite with
								call_depth=succ ctx_learn_ite.call_depth;
								less_spec=turn_dontcare ctx_learn_ite.less_spec then_pts;
							}	
						)
					in
					let else_branch_opt =
						Logger.g_with_increased_depth (fun () ->
							learn_ite {ctx_learn_ite with
								call_depth=succ ctx_learn_ite.call_depth;
								less_spec=turn_dontcare ctx_learn_ite.less_spec else_pts;
							}
						)
					in
					match then_branch_opt, else_branch_opt with
					| Some then_expr, Some else_expr -> begin
						Logger.g_debug_lazy (fun () -> Printf.sprintf "learned both of branches! if %s then %s else %s"
							(Exprs.string_of_expr pred)
							(Exprs.string_of_expr then_expr)
							(Exprs.string_of_expr else_expr)
						);
						let ite = Exprs.Function (TRI_OP ITE, [pred; then_expr; else_expr], Exprs.type_of_expr then_expr) in
						if AugSpec.is_solution_expr ctx_learn_ite.less_spec ite then
							Some ite
						else begin
							Logger.g_info_f "bad learn ite(bad solution is found): %s" (Exprs.string_of_expr ite);
							invalid_arg "bad"
						end
					end
					| _ ->
						try_predicates tail
			in
			try_predicates predicates
	end

and main_loop
	(synth_ctx_main: synth_ctx_main)
: unit =
	let components = synth_ctx_main.components in
	match synth_ctx_main.todo_sketch, synth_ctx_main.used_sketch_rev with
	| [], [] ->
		raise (NoSol "end of top-down")
	| [], _ -> begin
		if synth_ctx_main.subproblem_mode then
			raise (NoSol "exhausted in sub problem")
		else begin
			(* do component population *)
			Logger.g_info_f "growing component... cur max term size = %d"
				(Components.max_size components);
			let prev_compo_max_size = Components.max_size components in
			let rec force_progress (growing_cs: Components.component_pool) (next_target_size: int) =
				if next_target_size <= Global.t.cli_options.max_comp_size then begin
					let prev_compo_count = Components.get_num_total_components growing_cs in
					let next_compo =
						Logger.g_with_increased_depth (fun () ->
							List.fold_left (fun growing_cs (nt, rule) ->
								let target_size =
									if BatSet.mem nt growing_cs.predicate_nts then
										next_target_size + 2
									else
										next_target_size
									in
								grow nt rule growing_cs synth_ctx_main.spec.sem_spec target_size
							) growing_cs synth_ctx_main.spec.syn_spec.nt_rule_list_wo_ite;
						)
					in
					let after_compo_count = Components.get_num_total_components next_compo in
					if after_compo_count = prev_compo_count then begin
						let forced_next_target_size = succ next_target_size in
						Logger.g_info_f "component count is not grown (%d), increase target size to %d and retry" prev_compo_count
							forced_next_target_size;
						force_progress next_compo forced_next_target_size
					end
					else next_compo
				end
				else begin (* give up *)
					Logger.g_error_f "growing target size exceeded maximum component size option(%d), synthesis is terminatated." Global.t.cli_options.max_comp_size;
					Logger.g_debug_f "************ final components status ************";
					Logger.g_in_debug_lazy (fun () ->
						Logger.g_with_increased_depth (fun () ->
							Logger.g_debug_f "*** all components by size ***";
							BatMap.iter (fun nt _ ->
								let count = get_num_of_components components nt in
								Logger.g_debug_f "%s -> (%d)" (Grammar.string_of_non_terminal nt) count;
								let rec by_size (size: int): unit =
									if size <= Components.max_size components then begin
										let sized_compos = Components.get_sized_components components nt size in
										if BatList.is_empty sized_compos then ()
										else begin
											Logger.g_debug_f "size %d -> " size;
											Logger.g_with_increased_depth (fun () ->
												BatList.iter (fun (c, _) ->
													Logger.g_debug_f "%s" (Exprs.string_of_expr c)
												) sized_compos;
											);
											by_size (size + 1)
										end
									end
									else ()
								in
								Logger.g_with_increased_depth (fun () ->
									by_size 1
								)
							) synth_ctx_main.spec.syn_spec.grammar
						)
					);
					raise (NoSol "hit bottom-up limit")
				end
			in
			let grown_components = force_progress components (succ prev_compo_max_size) in
			log_component_sizes synth_ctx_main.spec.syn_spec.grammar grown_components;
			(* TODO: apply next topdown? *)
			(* restart with grown component pool *)
			main_loop {synth_ctx_main with
					components = grown_components;
					req_comp_size_range=(
						prev_compo_max_size + 1,
						Components.max_size grown_components
					);
					used_sketch_rev=[];
					todo_sketch=BatList.rev synth_ctx_main.used_sketch_rev;
				}
		end
	end
	| (picked_partial, picked_sem) :: remains, _ -> begin
		let index_in_topdown = BatList.length synth_ctx_main.used_sketch_rev in
		let _ = Logger.g_info_f "Chosen [%d/%d]: %s" index_in_topdown synth_ctx_main.total_sketch_size (Grammar.string_of_rewrite picked_partial) in
		let sketch_start_time = Unix.gettimeofday() in
		begin match picked_partial with
		| FuncRewrite (TRI_OP ITE, NTRewrite cond_nt :: NTRewrite then_nt :: NTRewrite else_nt :: _) -> begin
			if synth_ctx_main.subproblem_mode then
				Logger.g_info_f "skipping ITE in subproblem"
			else
				let learn_result =
					learn_ite {
						ctx_main = synth_ctx_main;
						call_depth=0;
						pt_covering_exprs=BatMap.empty;
						cond_nt=cond_nt;
						then_nt=then_nt;
						else_nt=else_nt;
						less_spec=synth_ctx_main.spec.sem_spec.spec_cex;
						nt_subproblem_cache=BatMap.empty
					}
				in
				Logger.g_info_f "elapsed %.2f sec" (Unix.gettimeofday() -. sketch_start_time);
				match learn_result with
				| Some found ->
					raise_solution_found synth_ctx_main found
				| None -> ()
		end
		| _ ->
			Logger.g_with_increased_depth (fun () ->
				let holes : (GrammarUtil.addr * Grammar.non_terminal) list = get_holes_for_compose picked_partial picked_sem in
				begin
					if BatList.is_empty holes then
						(* sketch = program *)
						let expr = Grammar.expr_of_rewrite_exn picked_partial in
						if AugSpec.is_solution_expr synth_ctx_main.spec.sem_spec.spec_cex expr then
							raise_solution_found synth_ctx_main expr
						else
							()
					else
						(* compose components into picked sketch *)
						let _ =
							BatList.iter (fun (idx, io) ->
									Logger.g_in_debug_lazy (fun () -> Logger.g_debug_f "[%d] inputs %s -> output %s," idx (string_of_list Exprs.string_of_const (fst io)) (AugSpec.string_of_output_spec (snd io)));
								) (zip_with_index synth_ctx_main.spec.sem_spec.spec_cex);
							Logger.g_in_debug_lazy (fun () -> Logger.g_debug_f " semantics: %s" (Analyzer.AbstState.to_string picked_partial picked_sem));
						in
						let compose_counter = create_counter() in
						try
							compose_for_sketch {
								ctx_main=synth_ctx_main;
								min_result_size=Components.min_size components;
								max_result_size=Components.max_size components * BatList.length holes + 1}
								compose_counter
								picked_partial picked_sem [] [] holes;
							log_and_record_counter compose_counter;
							Logger.g_info_f "no solution with current component set. elapsed %.2f sec" (Unix.gettimeofday() -. sketch_start_time);
							()
						with SolutionFoundInComposer (_, _, _) as exn -> begin
							log_and_record_counter compose_counter;
							Logger.g_info_f "found solution. elapsed %.2f sec" (Unix.gettimeofday() -. sketch_start_time);
							raise exn
						end
				end;
			);
		end;
		(* goto next todo sketch *)
		main_loop
			{synth_ctx_main with
				used_sketch_rev=((picked_partial, picked_sem) :: synth_ctx_main.used_sketch_rev);
				todo_sketch=remains;
			}
	end

(** Main algorithm *)
let synthesis_pbe
	?(jump_to_prev_iter: (int * int) option = None)
	(spec: AugSpec.t)
: Exprs.expr * (int * int) option = (** (solution, (index_in_sketch, max_term_size) option) *)
  let empty_components = create_empty spec.syn_spec.grammar spec.sem_spec.spec_cex in
	compose_progress_logger := Some (Logger.create_g_periodic_logger 20000);
	try
		let first_topdown_sketches =
			topdown_by_option spec.syn_spec.grammar spec.sem_spec.spec_cex
		in
		let (used_sketch_rev, todo_sketch, init_comp_size) =
			match jump_to_prev_iter with
			| None ->
				([], first_topdown_sketches, Global.t.cli_options.init_comp_size)
			| Some (sketch_index, max_term_size) -> begin
				Logger.g_info_f "jump to search point of previous iteration: %d/%d sketch with component size %d" sketch_index (BatList.length first_topdown_sketches) max_term_size;
				let (used_sketch, todo_sketch) =
					BatList.split_at sketch_index first_topdown_sketches
				in
				(BatList.rev used_sketch, todo_sketch, max_term_size)
			end
		in
		Logger.g_info_f "populate inital component pool upto size %d" init_comp_size;
		let initial_components = Logger.g_with_increased_depth (fun () ->
				populate_initial_components
					empty_components
					spec.sem_spec
					spec.syn_spec.nt_rule_list_wo_ite
					init_comp_size
			)
		in
		log_component_sizes spec.syn_spec.grammar initial_components;
		begin
			main_loop {
					spec=spec;
					subproblem_mode=false;
					components=initial_components;
					req_comp_size_range=(1, Components.max_size initial_components);
					total_sketch_size=BatList.length first_topdown_sketches;
					used_sketch_rev=used_sketch_rev;
					todo_sketch=todo_sketch;
				}
		end;
		raise (NoSol "unreachable code")
	with
	| SolutionFoundInSketch sol ->
		(sol, None)
	| Generator.SolutionFoundInGenerator (max_size, total_count, sol) -> begin
		Global.set_component_pool_size_when_sol total_count Global.t;
		Global.t.summary.final_compo_pool_count <- total_count;
		Global.t.summary.final_max_compo_size <- max_size;
		(sol, None)
	end
	| SolutionFoundInComposer (sol, sketch_index, max_term_size) -> begin
		(sol, Some (sketch_index, max_term_size))
	end
