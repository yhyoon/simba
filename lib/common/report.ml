open Vocab
open Yojson

exception Report_not_available of string

let format_tm (tm: Unix.tm): string =
    Printf.sprintf "%02d.%02d.%02d.%02d:%02d:%02d"
        (tm.tm_year mod 100)
        (tm.tm_mon + 1)
        tm.tm_mday
        tm.tm_hour
        tm.tm_min
        tm.tm_sec

let hc_to_json (m: Global.holes_to_counts): Safe.t =
    let l = BatMap.foldi (fun holes counts acc -> (holes, counts) :: acc) m [] in
    let sorted = BatList.sort (fun e1 e2 -> compare (fst e1) (fst e2)) l in
    `List (BatList.map (fun (hole_count, cut_count) -> `List ([`Int hole_count; `Intlit (Int64.to_string cut_count)])) sorted)

let total_composed (t: Global.t): Safe.t =
    if BatList.is_empty t.summary.cegis_iters then
        `List []
    else
        BatList.reduce Global.merge_by_holes (BatList.map (fun e -> Global.merge_by_holes e.Global.count_top e.Global.count_sub) t.summary.cegis_iters)
        |> hc_to_json

let to_json (t: Global.t): Safe.t =
    `Assoc ([
        ("input_path", `String t.input_path);
        ("problem_name", `String t.problem_name);
        ("start_time", `String (format_tm (Unix.localtime t.start_time)));
        ("total_time", `Float (t.end_time -. t.start_time));
        ("options", Global.cli_options_to_json t);
        ("cegis_solver_count",`Int t.summary.cegis_solver_call_cnt);
        ("cegis_solver_call_time", `Float t.summary.cegis_solver_call_time);
        ("cegis_iters", `List (
            BatList.map (fun it -> `Assoc [
                ("created_top", hc_to_json it.Global.count_top);
                ("created_sub", hc_to_json it.Global.count_sub);
                ("created_components", `Int it.Global.compo_pool_size);
            ]) t.summary.cegis_iters)
        );
        ("final_io_pairs", `Int t.summary.final_io_pairs);
        ("final_max_component_size", `Int t.summary.final_max_compo_size);
        ("final_component_count", `Int t.summary.final_compo_pool_count)
    ] @ (match t.summary.found_solution_and_size, t.summary.not_found_reason with
        | Some (sol, size), _ ->
            [
                ("found_solution", `String sol);
                ("solution_size", `Int size);
            ]
        | None, Some msg->
            [
                ("not_found", `String msg)
            ]
        | _ ->
            []
    ) @ [
        ("total_composed", total_composed t);
        ("component_generation_time", `Float Global.t.summary.compo_gen_time);
        ("component_search_table_build_time", `Float Global.t.summary.search_table_build_time);
        ("prune", `Assoc [
            ("method", `String Global.t.cli_options.pruning_mode);
            ("count", `Intlit (Int64.to_string Global.t.summary.prune_trial_info.trial_count));
            ("time", `Float Global.t.summary.prune_trial_info.trial_time);
            ("infeasible", `Intlit (Int64.to_string Global.t.summary.prune_trial_info.trial_infeasible));
            ("search_infeasible", `Intlit (Int64.to_string Global.t.summary.prune_trial_info.trial_search_infeasible));
            ("search_useful", `Intlit (Int64.to_string Global.t.summary.prune_trial_info.trial_search_useful));
            ("approx_reduced_incomplete", `Intlit (Int64.to_string Global.t.summary.prune_trial_info.trial_reduced_inter));
            ("approx_reduced_complete", `Intlit (Int64.to_string Global.t.summary.prune_trial_info.trial_reduced_complete));
        ]);
    ])

let export (printer: string -> unit) (t: Global.t): unit =
    let json = to_json t in
    let json_string = Yojson.Safe.pretty_to_string ~std:true json in
    printer json_string

let export_to_file (filename: string) (t: Global.t): unit =
    let oc = open_out filename in
    export (output_string oc) t;
    close_out oc
