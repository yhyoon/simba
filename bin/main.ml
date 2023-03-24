open Common
open Vocab

open Options

open SynthLang
open SynthSpec
open SynthBidir

let process_cli_options (): unit =
	let usage = Printf.sprintf "Usage: %s <options> <file>" Sys.argv.(0) in
	let _ =
		Global.t.version <-
			match Build_info.V1.version() with
			| None -> "n/a"
			| Some v -> Build_info.V1.Version.to_string v
	in
    let _ =
		Arg.parse options (fun x ->
			if Sys.file_exists x then begin
				Global.t.input_path <- x;
				Global.t.problem_name <- (Filename.basename x |> Filename.remove_extension);
			end
			else raise (Arg.Bad (x ^ ": No files given"))
		) usage
    in
	if Global.t.input_path = "" then begin
		Arg.usage options usage;
		exit(-1)
	end

let init_logger(): unit =
	if Global.t.cli_options.log_silence then
		Logger.activate_global Logger.null_handle
	else
		match Global.t.cli_options.log_file_name with
		| None ->
			Logger.activate_global (Logger.init_by_channel Global.t.start_time Global.t.cli_options.debug stderr)
		| Some file ->
			Logger.activate_global (Logger.init_by_file Global.t.start_time Global.t.cli_options.debug file)

let set_seed(): unit =
	if Global.t.cli_options.z3_seed <> 0 then begin
		Z3.set_global_param "sat.random_seed" (string_of_int Global.t.cli_options.z3_seed);
		Logger.g_info_f "Set Z3 global parameter sat.random_seed to %d" Global.t.cli_options.z3_seed;
	end

let ready_global_variables(): unit = begin
	(if Global.t.cli_options.exn_trace || Global.t.cli_options.debug then Printexc.record_backtrace true);
	Global.t.start_time <- Unix.gettimeofday();
	init_logger();
	set_seed();
end

let rec cegis problem spec additional_constraints =
	Global.begin_new_cegis_iter Global.t;
	Global.t.summary.final_io_pairs <- List.length spec;
	Logger.g_info_f "CEGIS iter: %d" (BatList.length Global.t.summary.cegis_iters);
	Logger.g_with_increased_depth (fun () ->
		BatList.iter (fun (inputs, output) ->
			Logger.g_info_f "i:%s -> o:%s"
				(string_of_list Exprs.string_of_const inputs) 
				(Exprs.string_of_const output) 
		) spec
	);
	let proposed_sol =
		Bidirectional.synthesis problem spec
	in
	Logger.g_info_f "** Proposed candidate: %s **" (Exprs.string_of_expr proposed_sol);
	(* spec' = spec + first mismatched input-output examples *)
	let mismatched_opt =
		BatList.find_opt (fun (inputs_from_problem, desired_output_from_problem) ->
				try
					let proposed_signature = Exprs.compute_signature [(inputs_from_problem, desired_output_from_problem)] proposed_sol in
					Exprs.compare_signature proposed_signature (Exprs.sig_of_single_const desired_output_from_problem) <> 0
				with Exprs.UndefinedSemantics ->
					true
			) problem.io_spec_total
	in
	match mismatched_opt with
	| Some mismatched ->
		cegis problem (mismatched :: spec) additional_constraints
	| None ->
		match Specification.verify additional_constraints proposed_sol spec with
		| None -> begin
			Global.t.summary.final_io_pairs <- List.length spec;
			proposed_sol
		end
		| Some (cex, next_constraints) ->
			Logger.g_info_f "add counter example: %s" (Specification.string_of_io_spec [cex]); 
			let _ = assert (not (List.mem cex spec)) in  
			cegis problem (cex :: spec) next_constraints

let report_result () =
	(* detail in json *)
	let _ =
		match Global.t.cli_options.report_json with
		| None ->
			if not Global.t.cli_options.log_silence then
				Report.export Logger.g_info Global.t
		| Some filename ->
			Report.export_to_file filename Global.t		
	in

	(* always print summary message to stderr *)
	let head_msg, size_msg_opt =
		match Global.t.summary.found_solution_and_size with
		| Some (sol_str, sol_size) -> begin
			sol_str, Some (Printf.sprintf "size : %d" sol_size)
		end
		| None -> begin
			match Global.t.summary.not_found_reason with
			| Some msg ->
				"Solution Not Found: "^msg, None
			| None ->
				failwith_f "no sol and no failure reason"
		end
	in
	Printf.fprintf stderr "%s\n" head_msg;
	Printf.fprintf stderr "****************** statistics *******************\n";
	BatOption.may prerr_endline size_msg_opt;
	Printf.fprintf stderr "time : %.2f sec\n" (Global.t.end_time -. Global.t.start_time);
	Printf.fprintf stderr "final max component size : %d\n" Global.t.summary.final_max_compo_size;
	Printf.fprintf stderr "final component pool size : %d\n" Global.t.summary.final_compo_pool_count;
	Printf.fprintf stderr "**************************************************\n";
	()

let main () =
	process_cli_options();
	ready_global_variables();
	let diversity_constraints =
		SpecDiversity.verification_constraints_from_names Global.t.cli_options.diversity_names
	in
	let problem = Parse.parse Global.t.input_path in

	(* CEGIS loop *)
	let _ = assert ((List.length problem.io_spec_total) > 0) in 
	let _ =
		try
			let starting_spec =
				if BatOption.default (not (Specification.is_pbe_only())) Global.t.cli_options.ex_all then
					problem.io_spec_total
				else
					(* get first one *)
					[BatList.hd problem.io_spec_total]
			in
			let sol = cegis problem starting_spec diversity_constraints in
			Global.t.summary.found_solution_and_size <- Some (
				Exprs.sexpstr_of_fun problem.args_map (Operators.op_to_string problem.target_function_name) sol,
				Exprs.size_of_expr sol
			)
		with Bidirectional.NoSol msg -> begin
			Global.t.summary.not_found_reason <- Some msg
		end
	in
	Global.t.end_time <- Unix.gettimeofday();
	report_result();
	Logger.g_close();
	()

let _ = main ()
