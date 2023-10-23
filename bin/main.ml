open Common
open Vocab

open Options

open SynthLang
open SynthProblem
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
	match Global.t.cli_options.log_mode with
	| Global.LogSilence ->
		Logger.activate_global Logger.null_handle
	| Global.LogStdout ->
		Logger.activate_global (Logger.init_by_channel Global.t.start_time Global.t.cli_options.debug stdout)
	| Global.LogStderr ->
		Logger.activate_global (Logger.init_by_channel Global.t.start_time Global.t.cli_options.debug stderr)
	| Global.LogFile file ->
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

let rec cegis
	?(jump_to_prev_iter: (int * int) option = None)
	(spec: SynthBase.AugSpec.t)
	(forbidden_inputs: Exprs.const list list)
: Exprs.expr =
	Global.begin_new_cegis_iter Global.t;
	Global.t.summary.final_io_pairs <- List.length spec.sem_spec.spec_cex;

	Logger.g_info_f "CEGIS iter: %d" (BatList.length Global.t.summary.cegis_iters);
	Logger.g_with_increased_depth (fun () ->
		BatList.iter (fun (inputs, output) ->
			Logger.g_info_f "i:%s -> o:%s"
				(string_of_list Exprs.string_of_const inputs) 
				(SynthBase.AugSpec.string_of_output_spec output) 
		) spec.sem_spec.spec_cex
	);
	let (proposed_sol, jump_to_opt) =
		Bidirectional.synthesis_pbe ~jump_to_prev_iter:jump_to_prev_iter spec
	in

	Logger.g_info_f "** Proposed candidate: %s **" (Exprs.string_of_expr proposed_sol);
	(* spec' = spec + first mismatched input-output examples *)
	let mismatched_opt =
		BatList.find_opt (function
				| (inputs, desired_output) -> begin
					try
						let proposed_signature = Exprs.compute_signature [inputs] proposed_sol in
						Exprs.compare_signature proposed_signature (Exprs.sig_of_single_const desired_output) <> 0
					with Exprs.UndefinedSemantics ->
						true
					end
			) spec.sem_spec.original_spec.spec_pbe
	in

	match mismatched_opt with
	| Some mismatched ->
		(* cex from pbe spec *)
		let augmented_mismatched = SynthBase.AugSpec.aug_ex_io mismatched in
		Logger.g_info_f "add counter example: %s" (Specification.string_of_ex_io mismatched); 
		if BatOption.default true Global.t.cli_options.cegis_jump then
			cegis ~jump_to_prev_iter:jump_to_opt (SynthBase.AugSpec.add_cex_spec augmented_mismatched spec) forbidden_inputs
		else
			cegis (SynthBase.AugSpec.add_cex_spec augmented_mismatched spec) forbidden_inputs
	| None ->
		match Specification.verify forbidden_inputs false spec.syn_spec.target_function_id spec.syn_spec.args_list proposed_sol spec.sem_spec.original_spec with
		| Some (cex, forbidden_inputs) -> begin
			let aug_cex = match cex with
				| CexIO ex_io ->
					SynthBase.AugSpec.aug_ex_io ex_io
				| CexPred pred ->
					SynthBase.AugSpec.alpha_predicate_constraint pred spec
		  in
			(* cex(input-output pair) from constraint verifier(solver) *)
			Logger.g_info_f "add counter example: %s" (SynthBase.AugSpec.string_of_io_spec aug_cex); 
			let _ = assert (not (List.mem aug_cex (spec.sem_spec.spec_cex))) in
			if BatOption.default true Global.t.cli_options.cegis_jump then begin
				cegis ~jump_to_prev_iter:jump_to_opt (SynthBase.AugSpec.add_cex_spec aug_cex spec) forbidden_inputs
			end
			else
				cegis (SynthBase.AugSpec.add_cex_spec aug_cex spec) forbidden_inputs
		end
		| None -> begin
			(* no more constraint -> found final solution *)
			Global.t.summary.final_io_pairs <- List.length (spec.sem_spec.spec_cex);
			proposed_sol
		end

let report_result () =
	(* detail in json *)
	let _ =
		match Global.t.cli_options.report_json with
		| None ->
			if not (Global.t.cli_options.log_mode = LogSilence) then
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
	let problem = Parse.parse Global.t.input_path in
	let problem =
		(* cli optionex_cut: modify given problem *)
		match Global.t.cli_options.ex_cut with
		| None -> problem
		| Some n ->
			{problem with spec_total =
				{problem.spec_total with spec_pbe =
					BatList.take n problem.spec_total.spec_pbe
				}
			}
	in
	let spec =
		try
			SynthBase.AugSpec.problem_to_spec problem
		with SynthBase.AugSpec.SolutionFoundTrivial sol -> begin
			Logger.g_info_f "Trivial solution found: %s" (Exprs.string_of_expr sol);
			Global.t.end_time <- Unix.gettimeofday();
			report_result();
			Logger.g_close();
			exit 0
		end
	in
	(* CEGIS loop *)
	let _ = assert (List.length spec.sem_spec.spec_cex > 0) in 
	let _ =
		try
			let sol = cegis spec [] in
			Global.t.summary.found_solution_and_size <- Some (
				Exprs.sexpstr_of_fun problem.args_map (Operators.op_to_string problem.target_function_id) sol,
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
