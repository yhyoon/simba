open Common
open Vocab

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

