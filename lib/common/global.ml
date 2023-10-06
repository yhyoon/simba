open Vocab
open Yojson

type t = {
    mutable version: string;
    mutable start_time: float;
    mutable end_time: float;
    mutable input_path: string;
    mutable problem_name: string;
    cli_options: cli_options;
    summary: synth_summary;
}
and cli_options = {
    mutable debug               : bool;
    mutable exn_trace           : bool;
    mutable ex_all              : bool option;
    mutable ex_cut              : int option;
    mutable init_comp_size      : int;
    mutable max_comp_size       : int;
    mutable gamma_size          : int;
    mutable topdown             : string;
    mutable get_size            : bool;
    mutable pruning_mode        : string;
    mutable cegis_jump          : bool option;
    mutable dt_predicate_order  : dt_predicate_order;
    mutable no_backward         : bool;
    mutable search2             : bool;
    mutable z3_seed             : int;
    mutable force_full_analysis : bool;
    mutable z3cli               : string option;
    mutable record_prune_count  : bool; (* Not implemented *)
    mutable diversity_names     : string;
    mutable report_json         : string option;
    mutable log_mode            : log_mode;
    mutable find_all            : bool; (* Deprecated *)
}
and log_mode =
    | LogSilence
    | LogStdout
    | LogStderr
    | LogFile of string
and synth_summary = {
    mutable compo_gen_time: float;
    mutable search_table_build_time: float;
    mutable cegis_solver_call_cnt: int;
    mutable cegis_solver_call_time: float;
    mutable cegis_iters: cegis_iter_info list;
    mutable final_io_pairs: int;
    mutable final_compo_pool_count: int;
    mutable final_max_compo_size: int;
    mutable found_solution_and_size: (string * int) option;
    mutable not_found_reason: string option;
    prune_trial_info: prune_trial_info;
}
and cegis_iter_info = {
    count_top: holes_to_counts;
    count_sub: holes_to_counts;
    compo_pool_size: int
}
and holes_to_counts = (int, int64) BatMap.t
and prune_trial_info = {
    mutable trial_count: int64;
    mutable trial_time: float;
    mutable trial_infeasible: int64;
    mutable trial_search_infeasible: int64;
    mutable trial_search_useful: int64;
    mutable trial_reduced_inter: int64;
    mutable trial_reduced_complete: int64;
}
and dt_predicate_order =
    | NormalEntropy
    | FastEntropy
    | HeuristicScore1

let cegis_iter_initial = {count_top=BatMap.empty; count_sub=BatMap.empty; compo_pool_size=0}

let t: t = {
    version = "n/a";
    start_time = 0.0;
    end_time = 0.0;
    input_path = "";
    problem_name = "";
    cli_options = {
        debug               = false;
        exn_trace           = false;
        ex_all              = None;
        ex_cut              = None;
        init_comp_size      = 1;
        max_comp_size       = 128;
        gamma_size          = 8;
        topdown             = "hole2";
        get_size            = false;
        pruning_mode        = "abstsem";
        cegis_jump          = None;
        no_backward         = false;
        search2             = false;
        z3_seed             = 0;
        force_full_analysis = false;
        z3cli               = None;
        record_prune_count  = false; (* Not implemented *)
        diversity_names     = "";
        report_json         = None;
        log_mode            = LogSilence;
        find_all            = false; (* Deprecated *)
        dt_predicate_order  = HeuristicScore1;
    };
    summary = {
        compo_gen_time = 0.0;
        search_table_build_time = 0.0;
        cegis_solver_call_cnt = 0;
        cegis_solver_call_time = 0.0;
        cegis_iters = [];
        final_io_pairs = 0;
        final_compo_pool_count = 0;
        final_max_compo_size = 0;
        found_solution_and_size = None;
        not_found_reason = None;
        prune_trial_info = {
            trial_count = 0L;
            trial_time = 0.0;
            trial_infeasible = 0L;
            trial_search_infeasible = 0L;
            trial_search_useful = 0L;
            trial_reduced_inter = 0L;
            trial_reduced_complete = 0L;
        };
    }
}

let parse_log_mode (s: string): log_mode =
    if BatString.equal s "stdout" then
        LogStdout
    else if BatString.equal s "stderr" then
        LogStderr
    else
        LogFile s

let string_of_dt_predicate_order (o: dt_predicate_order): string =
    match o with
    | NormalEntropy -> "entropy"
    | FastEntropy -> "fast_dt"
    | HeuristicScore1 -> "own_heuristic"

let cli_options_to_json(t: t): Safe.t =
    let l: (string * string) list =
        [
            ("debug", string_of_bool t.cli_options.debug);
            ("init_comp_size", string_of_int t.cli_options.init_comp_size);
            ("max_comp_size", string_of_int t.cli_options.max_comp_size);
            ("gamma_size", string_of_int t.cli_options.gamma_size);
            ("topdown", t.cli_options.topdown);
            ("pruning", t.cli_options.pruning_mode);
            ("cegis_jump", string_of_bool (BatOption.default true t.cli_options.cegis_jump));
            ("no_backward", string_of_bool t.cli_options.no_backward);
            ("force_full_analysis", string_of_bool t.cli_options.force_full_analysis);
            ("dt_predicate_order", string_of_dt_predicate_order t.cli_options.dt_predicate_order)
        ]
    in
    `List (BatList.map (fun pair -> `List [`String (fst pair) ; `String (snd pair)]) l)

let begin_new_cegis_iter (t: t): unit =
    t.summary.cegis_iters <- cegis_iter_initial :: t.summary.cegis_iters

let add_by_holes (hole_count: int) (adder: int64) (m: holes_to_counts): holes_to_counts =
    let incred =
        try
            Int64.add adder (BatMap.find hole_count m)
        with Not_found -> adder
    in
    BatMap.add hole_count incred m

let tick_by_holes (hole_count: int) (m: holes_to_counts): holes_to_counts =
    add_by_holes hole_count 1L m

let merge_by_holes (m1: holes_to_counts) (m2: holes_to_counts): holes_to_counts =
    BatMap.foldi add_by_holes m1 m2

let top_tick_candidate_cur_iter (holes_length: int) (t: t): unit =
    match t.summary.cegis_iters with
    | [] -> ()
    | cur :: tail -> t.summary.cegis_iters <- {cur with count_top = tick_by_holes holes_length cur.count_top} :: tail

let sub_tick_candidate_cur_iter (holes_length: int) (t: t): unit =
    match t.summary.cegis_iters with
    | [] -> ()
    | cur :: tail -> t.summary.cegis_iters <- {cur with count_sub = tick_by_holes holes_length cur.count_sub} :: tail

let set_component_pool_size_when_sol (pool_size: int) (t: t): unit =
    match t.summary.cegis_iters with
    | [] -> ()
    | cur :: tail -> t.summary.cegis_iters <- {cur with compo_pool_size = pool_size} :: tail

let tick_infeasible (t: t): unit = t.summary.prune_trial_info.trial_infeasible <- Int64.succ t.summary.prune_trial_info.trial_infeasible
let add_search_infeasible (i: int64) (t: t): unit = t.summary.prune_trial_info.trial_search_infeasible <- Int64.add i t.summary.prune_trial_info.trial_search_infeasible
let add_search_useful (i: int64) (t: t): unit = t.summary.prune_trial_info.trial_search_useful <- Int64.add i t.summary.prune_trial_info.trial_search_useful
let add_reduced_inter (i: int64) (t: t): unit = t.summary.prune_trial_info.trial_reduced_inter <- Int64.add i t.summary.prune_trial_info.trial_reduced_inter
let add_reduced_complete (i: int64) (t: t): unit = t.summary.prune_trial_info.trial_reduced_complete <- Int64.add i t.summary.prune_trial_info.trial_reduced_complete

let add_prune_trial_time (stride: float) (t: t): unit = begin
    t.summary.prune_trial_info.trial_count <- Int64.succ t.summary.prune_trial_info.trial_count;
    t.summary.prune_trial_info.trial_time <- t.summary.prune_trial_info.trial_time +. stride
end

let tick_solver_call (stride: float) (t: t): unit = begin
    t.summary.cegis_solver_call_cnt <- t.summary.cegis_solver_call_cnt + 1;
    t.summary.cegis_solver_call_time <- t.summary.cegis_solver_call_time +. stride
end

let add_compo_gen_time (stride: float) (t: t): unit = begin
    t.summary.compo_gen_time <- t.summary.compo_gen_time +. stride
end

let add_search_tbl_build_time (stride: float) (t: t): unit = begin
    t.summary.search_table_build_time <- t.summary.search_table_build_time +. stride
end