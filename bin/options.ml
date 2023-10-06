open Common.Global

let o = t.cli_options

let allowed_pruning_options = ["abstsem"; "bruteforce"; "solver"]

let options = [
	(* ("-all", Arg.Set find_all, "Find all solutions and pick the smallest one");	 *)
	("-version", Arg.Unit (fun () ->
			Printf.fprintf stdout "%s\n" Common.Global.t.version;
			exit(-1)
		), "Print version info and exit");
	("-ex_all", Arg.Bool (fun b -> o.ex_all <- Some b), "Provide all the IO examples upfront (default=true)");
	("-ex_cut", Arg.Int (fun n -> o.ex_cut <- Some n), "in pbe mode, give upperbound to given example counts(only for experiment, default=None)");
	("-get_size", Arg.Unit (fun () -> o.get_size <- true), "Get size of an expression");
	("-debug", Arg.Unit (fun () -> o.debug <- true), "print info for debugging");
	("-exn_trace", Arg.Unit (fun () -> o.exn_trace <- true), "print stack trace for uncaught exception");
	("-init_comp_size", Arg.Int (fun n -> o.init_comp_size <- n), "set the initial size of each component (default=1)");
	("-max_comp_size", Arg.Int (fun n -> o.max_comp_size <- n), "set the maximum size of each component (default=128)");
	("-gamma_size", Arg.Int (fun n -> o.gamma_size <- n), "set the maximum size of size-constrainted concretization(default=8)");
	("-topdown", Arg.String (fun s -> o.topdown <- s), "set top-down strategey(example: depth1, depth2, holeN) (default=hole2)");
	("-pruning", Arg.String (fun s -> if BatList.mem s allowed_pruning_options then o.pruning_mode <- s), "select one of pruning method(abstsem, bruteforce, solver) (default=abstsem)");
	("-cegis_jump", Arg.Bool (fun b -> o.cegis_jump <- Some b), "Jump to previous iteration progress point in CEGIS (default=true)");
	("-dt_pred", Arg.String (fun s ->
		o.dt_predicate_order <-
			match s with
			| "ent1" -> NormalEntropy
			| "ent2" -> FastEntropy
			| _ -> HeuristicScore1
		), "How to ordering predicates in dt learning(ent1: normal entropy, ent2: heuristic entropy, heu1: heuristic score) (default: heu1)");
	("-no_backward", Arg.Unit (fun () -> o.no_backward <- true), "Disable backward analysis and do only forward analysis in pruning abstsem mode(only for experiment)");
	("-search2", Arg.Unit (fun () -> o.search2 <- true), "Do concretization refereing component signatures (experimental, default=false)");
	("-z3_seed", Arg.Int (fun n -> o.z3_seed <- n), "Set random seed of Z3 SAT solver (default=0)");
	("-force_full_analysis", Arg.Unit (fun () -> o.force_full_analysis <- true), "Do not reuse prev analysis result in static analysis (only for experiment)");
	("-record_prune_count", Arg.Unit (fun () -> o.record_prune_count <- true), "Count approximated iterations pruned by concretization-based component pick(only for experiment)");
	("-diversity", Arg.String (fun s -> o.diversity_names <- s), "Comma-separated sequence of diversity constraint strategy names(special keyword 'defaut'=force_ubig,force_pos_sbig,force_neg_odd,force_even,force_minus_one)");
	("-z3cli", Arg.String (fun s -> o.z3cli <- Some s), "Use Z3 via command line interface(instead of ocamlbinding library)");
	("-log", Arg.String (fun s ->
		o.log_mode <- parse_log_mode s), "Set log mode. stdout: print to standard output, stderr: print to standard error, otherwise: given argument will be log file name(default=do not print log)");
	("-report_json", Arg.String (fun s -> o.report_json <- Some s), "Report result to json file");
]