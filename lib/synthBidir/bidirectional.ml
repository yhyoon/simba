open Common
open Vocab

open SynthLang

open SynthSpec

open SynthBase
open Generator
open Components

exception NoSol of string

let is_solution desired_sig spec expr =
	try 
		let signature = Exprs.compute_signature spec expr in
		(Exprs.compare_signature desired_sig signature) = 0
	with Exprs.UndefinedSemantics -> false

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

type compose_spec = { (* fixed parameters during composing one sketch *)
	grammar: Grammar.grammar;
	components: component_pool;
	spec: Specification.iospec;
	desired_sig: Exprs.signature;
	neccessary_compo_size_range: int * int;
	min_result_size: int;
	max_result_size: int;
}

type compose_counter_item =
	| CC_COMPLETE
	| CC_INTER
	| CC_INFEAS
	| CC_INFEAS_SEARCH
	| CC_LESS_ITER
	| CC_PRUNE_COMPLETE
	| CC_PRUNE_INTER

let compose_counter_item_index_map: (compose_counter_item, int) BatMap.t =
	BatMap.empty
	|> BatMap.add CC_COMPLETE 		0 (* 실제 만든 완성 프로그램 수 *)
	|> BatMap.add CC_INTER 			1 (* 탑레벨 뼈대 제외 실제 만든 미완성 프로그램 수 *)
	|> BatMap.add CC_INFEAS 		2 (* 탑레벨 뼈대 포함 미완성 프로그램 중 bottom infeasible 한 수 *)
	|> BatMap.add CC_INFEAS_SEARCH 	3 (* 탑레벨 뼈대 포함 미완성 프로그램 중 search infeasible 한 수 *)
	|> BatMap.add CC_LESS_ITER 		4 (* 탑레벨 뼈대 포함 미완성 프로그램 중 search less iter 성공한 수 *)
	|> BatMap.add CC_PRUNE_COMPLETE 5 (* pruning으로 덜 만들어본 완성 프로그램 수 *)
	|> BatMap.add CC_PRUNE_INTER 	6 (* pruning으로 덜 만들어본 미완성 프로그램 수 *)

let compose_counter_item_index (i: compose_counter_item): int = BatMap.find i compose_counter_item_index_map

type compose_counter = Int64.t array

let create_counter() = BatArray.init (BatMap.cardinal compose_counter_item_index_map) (fun _ -> 0L)

let get_counter (c: compose_counter) (item: compose_counter_item): int64 = c.(compose_counter_item_index item)

let add_compose_counter (c: compose_counter) (item: compose_counter_item) (i: int64): unit =
	c.(compose_counter_item_index item) <- Int64.add i c.(compose_counter_item_index item)

let tick_compose_counter (c: compose_counter) (item: compose_counter_item): unit = add_compose_counter c item 1L

let log_and_record_counter(counter: compose_counter) =
	let (remain_cnt, cut_ratio, no_matching_component_ratio, less_ratio, remain_ratio) =
		let remain_cnt =
			get_counter counter CC_INTER
			|> Int64.add (Int64.neg (get_counter counter CC_INFEAS))
			|> Int64.add (Int64.neg (get_counter counter CC_INFEAS_SEARCH))
			|> Int64.add (Int64.neg (get_counter counter CC_LESS_ITER))
		in
		if get_counter counter CC_INTER > 0L then
			let inter_float = Int64.to_float (get_counter counter CC_INTER) in
			(remain_cnt,
			Int64.to_float (get_counter counter CC_INFEAS) /. inter_float,
			Int64.to_float (get_counter counter CC_INFEAS_SEARCH) /. inter_float,
			Int64.to_float (get_counter counter CC_LESS_ITER) /. inter_float,
			Int64.to_float remain_cnt /. inter_float)
		else (remain_cnt, 0.0, 0.0, 0.0, 0.0)
	in
	let _ =
		Global.add_search_infeasible (get_counter counter CC_INFEAS_SEARCH) Global.t;
		Global.add_search_useful (get_counter counter CC_LESS_ITER) Global.t;
		Global.add_reduced_inter (get_counter counter CC_PRUNE_INTER) Global.t;
		Global.add_reduced_complete (get_counter counter CC_PRUNE_COMPLETE) Global.t;
	in
	Logger.g_with_increased_depth (fun () ->
		Logger.g_info_f "created %Ld intermediates with holes (reduced by %Ld)" (get_counter counter CC_INTER) (get_counter counter CC_PRUNE_INTER);
		Logger.g_with_increased_depth (fun () ->
			if get_counter counter CC_INFEAS > 0L then Logger.g_info_f "%Ld (%2.2f %%) intermediates passed by bottom semantics" (get_counter counter CC_INFEAS) (cut_ratio *. 100.0);
			if get_counter counter CC_INFEAS_SEARCH > 0L then Logger.g_info_f "%Ld (%2.2f %%) intermediates passed by concretization-based component search" (get_counter counter CC_INFEAS_SEARCH) (no_matching_component_ratio *. 100.0);
			if get_counter counter CC_LESS_ITER > 0L then Logger.g_info_f "%Ld (%2.2f %%) intermediates less iteration by concretization-based component search" (get_counter counter CC_LESS_ITER) (no_matching_component_ratio *. 100.0);
			if remain_cnt > 0L then Logger.g_info_f "        %Ld (%2.2f %%) intermediates needed full search" remain_cnt (remain_ratio *. 100.0);
		);
		Logger.g_info_f "created %Ld complete programs (reduced by %Ld)" (get_counter counter CC_COMPLETE) (get_counter counter CC_PRUNE_COMPLETE);
	)

let check_feasibility_general
	(grammar: Grammar.grammar)
    (candidate: Grammar.rewrite)
    (plugged_spot: GrammarUtil.addr)
    (spec: SynthSpec.Specification.iospec)
    (prev_semantics: Analyzer.AbstState.t)
	: Analyzer.Transfer.feasibility =
	match candidate with
	| Grammar.ExprRewrite expr -> begin (* compute exact value *)
		try
			let desired_sig = List.map snd spec |> Exprs.signature_of_const_list in
			let signature = Exprs.compute_signature spec expr in
			if Exprs.compare_signature desired_sig signature = 0 then begin
				Logger.g_in_debug_lazy (fun () -> Logger.g_debug_f "solution found in checking feasiblity: %s" (SynthLang.Exprs.string_of_expr expr));
				raise (SynthSpec.Specification.SolutionFound expr)
			end
			else begin
				(* Logger.g_debug_lazy (fun () -> Printf.sprintf "thrown by exact calculation: %s" (SynthLang.Exprs.string_of_expr expr)); *)
				Analyzer.Transfer.NotDesiredExpr
			end
		with Exprs.UndefinedSemantics -> begin
			Logger.g_in_debug_lazy (fun () -> Logger.g_debug_f "thrown by undefined semantics: %s" (SynthLang.Exprs.string_of_expr expr));
			Analyzer.Transfer.NotDesiredExpr
		end
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

let rec compose_for_sketch
	(compose_spec: compose_spec)
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
			if is_solution compose_spec.desired_sig compose_spec.spec expr then
				raise (Specification.SolutionFound expr)
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
				let max_component_size = SynthBase.Components.max_size compose_spec.components in
				let compo_size_range_from_result_size =
					let l = (compose_spec.min_result_size
						- Grammar.size_of_rewrite intermediate
						- max_component_size * BatList.length holes_tail)
					in
					let r =
						(compose_spec.max_result_size
						- Grammar.size_of_rewrite intermediate
						- BatList.length holes_tail)
					in
					(l,r)
				in
				let compo_size_range_from_neccessary_cond =
					let (l,r) = compose_spec.neccessary_compo_size_range in
					if BatList.is_empty holes_tail &&
						not (
							BatList.exists (fun (_, size) -> l <= size && size <= r) chosen_components
						)
					then
						compose_spec.neccessary_compo_size_range
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
					if Global.t.cli_options.search2 then
						match Analyzer.AbstState.lookup addr sems with
						| Bool bl ->
							Dom.ABoolSig.gamma_size_constraint Global.t.cli_options.gamma_size bl
						| Bot ->
							[(0, BatSet.empty)]
						| Top ->
							[]
						| bv ->
							SigSearch.consts_matching_bv_partial_sig
								(BatMap.find nt compose_spec.components.nt_sig_search)
								(min_cur_compo_size, max_cur_compo_size)
								Global.t.cli_options.gamma_size
								bv
					else
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
					|> BatEnum.fold (fun sum cs -> Components.get_num_of_sized_components compose_spec.components nt cs + sum) 0
				in
				let without_constant_enum() =
					let default_ranged_enum() =
						CompEnum.make_ranged min_cur_compo_size max_cur_compo_size compose_spec.components nt
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
									let (l,r) = compose_spec.neccessary_compo_size_range in
									if not (
										(* 이미 빈칸에 채운 부품 중에 꼭 넣어야할 크기 부품이 아직 포함되지 않았다면 *)
										BatList.exists (fun (_, size) -> l <= size && size <= r) chosen_components
									) then
										(* 어차피 꼭 넣어야할 크기 부품이 두 구멍 중 한 칸에는 꼭 들어가야하므로 그것을 이번 구멍에 먼저 채워버린다 *)
										CompEnum.make_ranged ~iter_type:(Some CompEnum.IterSymmBreak) l r compose_spec.components nt
									else
										default_ranged_enum()
								else
									default_ranged_enum()
							| _ ->
								default_ranged_enum()
						end
					end
				in
				if BatList.length index_and_consts = Exprs.sig_length compose_spec.desired_sig then
					(* use full signature *)
					let sig_matching_exprs =
						elem_wise_fold (fun indexed_sig (cnt, acc) ->
								let signature = BatList.map snd indexed_sig |> Exprs.signature_of_const_list in
								try
									let expr = find_expr_of_nt_sig compose_spec.components nt signature in
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
							(Exprs.sig_length compose_spec.desired_sig)
							cardinal
							(get_num_of_components compose_spec.components nt));
					(PRUNE_CONCRETE_SEARCH (cardinal, expected_no_prune_enum_size()), CompEnum.from_set sig_matching_exprs)
				else if not (BatList.is_empty index_and_consts) then
					(* use partial signature *)
					let exprs =
						elem_wise_fold (fun indexed_sig (cnt, acc) ->
								let found = find_exprs_of_nt_partial_sig ~expr_size_range_opt:(Some(min_cur_compo_size, max_cur_compo_size)) compose_spec.components nt indexed_sig in
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
							(Exprs.sig_length compose_spec.desired_sig)
							cardinal
							(get_num_of_components compose_spec.components nt));
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
					let remain_nt_compo_counts = BatList.map (fun (_, remain_nt) -> Components.get_num_of_components compose_spec.components remain_nt) holes_tail |> BatList.rev in
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
			let feasiblity = check_feasibility_general compose_spec.grammar plugged_rewrite addr compose_spec.spec sems in
			match feasiblity with
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
					let remain_nt_compo_counts = BatList.map (fun (_, remain_nt) -> Components.get_num_of_components compose_spec.components remain_nt) holes_tail |> BatList.rev in
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
				compose_for_sketch compose_spec compose_counter plugged_rewrite post_sems ((addr, components_for_cur_hole) :: enums) ((expr, expr_size) :: chosen_components) holes_tail
			end
			| Analyzer.Transfer.DoBruteForce -> begin
				compose_for_sketch compose_spec compose_counter plugged_rewrite sems ((addr, components_for_cur_hole) :: enums) ((expr, expr_size) :: chosen_components) holes_tail
			end
		) components_for_cur_hole

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
	(spec: Specification.t)
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
		natural_order_list
	in
	List.fold_left (fun result_rev rule ->
		let n' = GrammarUtil.plug_rewrite sketch_rule [(addr, rule)] in
		let _ =
			Global.top_tick_candidate_cur_iter (GrammarUtil.count_holes n') Global.t
		in
		match check_feasibility_general grammar n' [] spec sketch_sem with
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
	(grammar: (Grammar.non_terminal, Grammar.rewrite BatSet.t) BatMap.t)
	(spec: Specification.t)
	: (Grammar.rewrite * Analyzer.AbstState.t) list
=
	let (root_rule, root_sem) =
		(Grammar.NTRewrite Grammar.start_nt,
			Analyzer.AbstState.update_value [] (Dom.AbstDom.AbstSig.alpha (Specification.signature_of_spec spec)) Analyzer.AbstState.empty)
	in
	topdown_expand grammar spec (root_rule, root_sem) [] |> BatList.rev

(* just two-level topdown *)
let topdown_sketches_depth2
	(grammar: (Grammar.non_terminal, Grammar.rewrite BatSet.t) BatMap.t)
	(spec: Specification.t)
	: (Grammar.rewrite * Analyzer.AbstState.t) list
=
	let base = topdown_sketches_depth1 grammar spec in
	BatList.fold_left (fun acc_rev (sketch, sem) ->
			topdown_expand grammar spec (sketch, sem) acc_rev
		) [] base |> BatList.rev

(* expand selective *)
let topdown_sketches_selective
	(grammar: (Grammar.non_terminal, Grammar.rewrite BatSet.t) BatMap.t)
	(spec: Specification.t)
	: (Grammar.rewrite * Analyzer.AbstState.t) list
=
	let base = topdown_sketches_depth1 grammar spec in
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
	(grammar: (Grammar.non_terminal, Grammar.rewrite BatSet.t) BatMap.t)
	(spec: Specification.t)
	(dest_hole_count: int)
	: (Grammar.rewrite * Analyzer.AbstState.t) list
=
	let (root_rule, root_sem) =
		(Grammar.NTRewrite Grammar.start_nt,
			Analyzer.AbstState.update_value [] (Dom.AbstDom.AbstSig.alpha (Specification.signature_of_spec spec)) Analyzer.AbstState.empty)
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

let log_component_sizes (grammar: Grammar.grammar) (components: component_pool): unit =
	Logger.g_info_f "************ components nt -> exprs ************";
	Logger.g_with_increased_depth (fun () ->
		BatMap.iter (fun nt _ ->
			let count = get_num_of_components components nt in
			Logger.g_info_f "%s -> (%d)" (Grammar.string_of_non_terminal nt) count;
			let rec by_size (size: int): unit =
				if size <= Components.max_size components then begin
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

(** Main algorithm *)						
let synthesis
	(problem: Parse.parse_result)
	(spec: Specification.t)
=
	let grammar = problem.grammar in
	let components = create_empty grammar spec in
	(* signatures: outputs of enumerated expressions *)
	let desired_sig = Specification.signature_of_spec spec in
	(* sorted list of grammar rule *)
	let nt_rule_list = Grammar.get_nt_rule_list grammar in
	try
		compose_progress_logger := Some (Logger.create_g_periodic_logger 20000);
		Logger.g_info_f "populate inital component pool upto size %d" Global.t.cli_options.init_comp_size;
		Logger.g_with_increased_depth (fun () ->
			populate_initial_components components desired_sig spec nt_rule_list (1, Global.t.cli_options.init_comp_size)
		);
		log_component_sizes grammar components;
		let first_topdown_sketches =
			match Global.t.cli_options.topdown with
			| "depth1" -> begin
				Logger.g_info_f "topdown strategy: depth1";
				topdown_sketches_depth1 grammar spec
			end
			| "depth2" ->
				Logger.g_info_f "topdown strategy: depth2";
				topdown_sketches_depth2 grammar spec
			| topdown_name ->
				if BatString.starts_with topdown_name "hole" then
					let count_string = BatString.sub topdown_name 4 (BatString.length topdown_name - 4) in
					match int_of_string_opt count_string with
					| Some count -> begin
						Logger.g_info_f "topdown strategy: hole-count %d" count;
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
		in
		let rec main_loop
			(neccessary_compo_size_range: int * int)
			(index_in_topdown: int)
			(total_cnt: int)
			(used_rev: (Grammar.rewrite * Analyzer.AbstState.t) list)
			(todo: (Grammar.rewrite * Analyzer.AbstState.t) list): unit =
			if BatList.is_empty used_rev && BatList.is_empty todo then
				raise (NoSol "end of top-down")
			else
				match todo with
				| [] -> begin
					(* do component population *)
					Logger.g_info_f "growing component... cur max size = %d" (Components.max_size components);
					let prev_compo_count = Components.get_num_total_components components in
					let prev_compo_max_size = Components.max_size components in
					let rec force_progress next_target_size =
						if next_target_size > Global.t.cli_options.max_comp_size then begin
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
									) grammar
								)
							);
							raise (NoSol "hit bottom-up limit")
						end
						else
							let prev_compo_count = Components.get_num_total_components components in
							Logger.g_with_increased_depth (fun () ->
								List.iter (fun (nt, rule) ->
									grow nt rule components desired_sig spec next_target_size
								) nt_rule_list;
							);
							let after_compo_count = Components.get_num_total_components components in
							if after_compo_count = prev_compo_count then begin
								Logger.g_info_f "component count is not grown (%d), increase target size to %d and retry" prev_compo_count (next_target_size + 1);
								force_progress (next_target_size + 1)
							end
					in
					force_progress ((Components.max_size components) + 1);
					log_component_sizes grammar components;
					(* TODO: apply next topdown? *)
					main_loop (prev_compo_max_size + 1, Components.max_size components) 0 (BatList.length used_rev) [] (BatList.rev used_rev)
				end
				| (n, sems) :: remains -> begin
					let _ = Logger.g_info_f "Chosen [%d/%d]: %s" index_in_topdown total_cnt (Grammar.string_of_rewrite n) in
					let sketch_start_time = Unix.gettimeofday() in
					Logger.g_with_increased_depth (fun () ->
						let holes : (GrammarUtil.addr * Grammar.non_terminal) list = get_holes_for_compose n sems in
						begin
							if BatList.is_empty holes then
								(* sketch = program *)
								let expr = Grammar.expr_of_rewrite_exn n in
								if is_solution desired_sig spec expr then
									raise (Specification.SolutionFound expr)
								else
									()
							else
								(* compose components into picked sketch *)
								let _ =
									BatList.iter (fun (idx, io) ->
											Logger.g_in_debug_lazy (fun () -> Logger.g_debug_f "[%d] inputs %s -> output %s," idx (string_of_list Exprs.string_of_const (fst io)) (Exprs.string_of_const (snd io)));
										) (zip_with_index spec);
									Logger.g_in_debug_lazy (fun () -> Logger.g_debug_f " semantics: %s" (Analyzer.AbstState.to_string n sems));
								in
								let compose_counter = create_counter() in
								try
									compose_for_sketch {
										grammar=grammar;
										components=components;
										spec=spec;
										desired_sig=desired_sig;
										neccessary_compo_size_range=neccessary_compo_size_range;
										min_result_size=Components.max_size components + 1;
										max_result_size=Components.max_size components * BatList.length holes + 1}
										compose_counter
										n sems [] [] holes;
									log_and_record_counter compose_counter;
									Logger.g_info_f "elapsed %.2f sec" (Unix.gettimeofday() -. sketch_start_time);
									()
								with (Specification.SolutionFound sol) as thrown -> begin
									log_and_record_counter compose_counter;
									Logger.g_info_f "elapsed %.2f sec" (Unix.gettimeofday() -. sketch_start_time);
									raise thrown
								end
						end;
					);
					main_loop neccessary_compo_size_range (succ index_in_topdown) total_cnt ((n, sems) :: used_rev) remains
				end
		in
		main_loop (1, Components.max_size components) 0 (BatList.length first_topdown_sketches) [] first_topdown_sketches; Exprs.Const (CInt 0) (* just a placeholder for type checking *)
	with Specification.SolutionFound sol -> begin
		let s = Components.get_num_total_components components in
		Global.set_component_pool_size_when_sol s Global.t;
		Global.t.summary.final_compo_pool_count <- s;
		Global.t.summary.final_max_compo_size <- Components.max_size components;
		sol 
	end
