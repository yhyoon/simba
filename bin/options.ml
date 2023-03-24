open Common.Global

let o = t.cli_options

let allowed_pruning_options = ["abstsem"; "bruteforce"; "solver"]

let options = [
	(* ("-fastdt", Arg.Set fast_dt, "Use a heuristic to compute entropies faster (may generate larger solutions)"); *)
	(* ("-all", Arg.Set find_all, "Find all solutions and pick the smallest one");	 *)
	("-version", Arg.Unit (fun () ->
			Printf.fprintf stdout "%s\n" Common.Global.t.version;
			exit(-1)
		), "Print version info and exit");
	("-ex_all", Arg.Bool (fun b -> o.ex_all <- Some b), "Provide all the IO examples upfront (default=true)");
	("-get_size", Arg.Unit (fun () -> o.get_size <- true), "Get size of an expression");
	("-debug", Arg.Unit (fun () -> o.debug <- true), "print info for debugging");
	("-exn_trace", Arg.Unit (fun () -> o.exn_trace <- true), "print stack trace for uncaught exception");
	("-init_comp_size", Arg.Int (fun n -> o.init_comp_size <- n), "set the initial size of each component (default=1)");
	("-max_comp_size", Arg.Int (fun n -> o.max_comp_size <- n), "set the maximum size of each component (default=128)");
	("-gamma_size", Arg.Int (fun n -> o.gamma_size <- n), "set the maximum size of size-constrainted concretization(default=4)");
	("-topdown", Arg.String (fun s -> o.topdown <- s), "set top-down strategey(example: depth1, depth2, holeN) (default=hole2)");
	("-pruning", Arg.String (fun s -> if BatList.mem s allowed_pruning_options then o.pruning_mode <- s), "select one of pruning method(abstsem, bruteforce, solver) (default=abstsem)");
	("-no_backward", Arg.Unit (fun () -> o.no_backward <- true), "Disable backward analysis and do only forward analysis in pruning abstsem mode(only for experiment)");
	("-search2", Arg.Unit (fun () -> o.search2 <- true), "Do concretization refereing component signatures (experimental, default=false)");
	("-z3_seed", Arg.Int (fun n -> o.z3_seed <- n), "Set random seed of Z3 SAT solver (default=0)");
	("-force_full_analysis", Arg.Unit (fun () -> o.force_full_analysis <- true), "Do not reuse prev analysis result in static analysis (only for experiment)");
	("-record_prune_count", Arg.Unit (fun () -> o.record_prune_count <- true), "Count approximated iterations pruned by concretization-based component pick(only for experiment)");
	("-diversity", Arg.String (fun s -> o.diversity_names <- s), "Comma-separated sequence of diversity constraint strategy names(special keyword 'defaut'=force_ubig,force_pos_sbig,force_neg_odd,force_even,force_minus_one)");
	("-log_silence", Arg.Unit (fun () -> o.log_silence <- true), "ignore log_file option and do not print any log");
	("-log_file", Arg.String (fun s -> o.log_file_name <- Some s), "print log to named file (default: use stderr)");
	("-report_json", Arg.String (fun s -> o.report_json <- Some s), "Report result to json file");
]