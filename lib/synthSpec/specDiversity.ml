open BatPervasives

open Common
open Vocab
open Int64Util
open SynthLang.Exprs

type one_iospec = const list * const
type iospec = one_iospec list

type diversity_constr_required =
	| RequiredFromWhole of (iospec -> bool)
	| RequiredFromEachOutput of (const -> bool)

type diversity_constraint = {
	diversity_name: string;
	check_unsat_constraint: diversity_constr_required;
	output_constraint_gen: string -> string;
}

let is_required (dc: diversity_constraint) (spec: iospec): bool =
	match dc.check_unsat_constraint with
	| RequiredFromWhole check -> check spec
	| RequiredFromEachOutput check_each ->
		BatList.for_all check_each (BatList.map snd spec)

let rec process_diversity (dcs: diversity_constraint list) (output_expr_string: string) (spec: iospec): ((string * string) option * diversity_constraint list) =
	match dcs with
	| [] ->
		(None, [])
	| candidate_rule :: rules_tail ->
		if is_required candidate_rule spec then
			(Some (candidate_rule.diversity_name, Printf.sprintf "(assert %s)" (candidate_rule.output_constraint_gen output_expr_string)), rules_tail)
		else begin
			Logger.g_info_f "discard diversity constraint %s (already satisfied)" candidate_rule.diversity_name;
			process_diversity rules_tail output_expr_string spec
		end

(* let force_neg: diversity_constraint = {
	diversity_name="force_negative";
	check_unsat_constraint=RequiredFromEachOutput (fun output -> 
		match output with
		| CBV (len, b) ->
			let module I = MaskedInt64(struct let size = len end) in
			(b $&&$ I.msb_marker ) = 0L
		| _ -> false
	);
	output_constraint_gen=fun output_expr_string ->
		let msb_mask = Int64.shift_left 1L 63 in
		Printf.sprintf "(= (bvand %s %s) %s)"
			output_expr_string (string_of_const (CBV msb_mask)) (* TODO: apply I modules... *)
			(string_of_const (CBV msb_mask))
}

let force_pos: diversity_constraint = {
	diversity_name="force_positive";
	check_unsat_constraint=RequiredFromEachOutput (fun output ->
		match output with
		| CBV b ->
			let msb_mask = Int64.shift_left 1L 63 in
			(b $&&$ msb_mask) = msb_mask
		| _ -> false
	);
	output_constraint_gen=fun output_expr_string ->
		let msb_mask = Int64.shift_left 1L 63 in
		Printf.sprintf "(= (bvand %s %s) %s)"
			output_expr_string (string_of_const (CBV msb_mask))
			(string_of_const (CBV 0L))
}

let force_odd: diversity_constraint = {
	diversity_name="force_odd";
	check_unsat_constraint=RequiredFromEachOutput (fun output ->
		match output with
		| CBV b ->
			let lsb_mask = 1L in
			(b $&&$ lsb_mask) = 0L
		| _ -> false
	);
	output_constraint_gen=fun output_expr_string ->
		let lsb_mask = 1L in
		Printf.sprintf "(= (bvand %s %s) %s)"
			output_expr_string (string_of_const (CBV lsb_mask))
			(string_of_const (CBV lsb_mask))
}

let force_even: diversity_constraint = {
	diversity_name="force_even";
	check_unsat_constraint=RequiredFromEachOutput (fun output ->
		match output with
		| CBV b ->
			let lsb_mask = 1L in
			(b $&&$ lsb_mask) = lsb_mask
		| _ -> false
	);
	output_constraint_gen=fun output_expr_string ->
		let lsb_mask = 1L in
		Printf.sprintf "(= (bvand %s %s) %s)"
			output_expr_string (string_of_const (CBV lsb_mask))
			(string_of_const (CBV 0L))
}

let merge_diversity_constraint (c1: diversity_constraint) (c2: diversity_constraint): diversity_constraint = {
	diversity_name=c1.diversity_name ^ "_" ^ c2.diversity_name;
	check_unsat_constraint=begin
		match c1.check_unsat_constraint, c2.check_unsat_constraint with
		| RequiredFromEachOutput check1, RequiredFromEachOutput check2 ->
			RequiredFromEachOutput (fun c -> check1 c || check2 c)
		| _ ->
			RequiredFromWhole (fun spec -> is_required c1 spec && is_required c2 spec)
	end;
	output_constraint_gen=fun output_expr ->
		Printf.sprintf "(and %s %s)" (c1.output_constraint_gen output_expr) (c2.output_constraint_gen output_expr)
}

let force_neg_odd: diversity_constraint = merge_diversity_constraint force_neg force_odd

let force_minus_one: diversity_constraint = {
	diversity_name="force_minus_one";
	check_unsat_constraint=RequiredFromEachOutput (fun output ->
		match output with
		| CBV b ->
			b <> (-1L)
		| _ -> false
	);
	output_constraint_gen=fun output_expr_string ->
		Printf.sprintf "(= %s %s)"
			output_expr_string (string_of_const (CBV (-1L)))
}

let force_ubig: diversity_constraint = {
	diversity_name="force_unsigned_big";
	check_unsat_constraint=RequiredFromEachOutput (fun output ->
		match output with
		| CBV b ->
			let mask = Int64.shift_left 3L 62 in
			(b $&&$ mask) = 0L
		| _ -> false
	);
	output_constraint_gen=fun output_expr_string ->
		let mask = Int64.shift_left 3L 62 in
		Printf.sprintf "(= (bvand %s %s) %s)"
			output_expr_string (string_of_const (CBV mask))
			(string_of_const (CBV mask))
}

let force_pos_sbig: diversity_constraint = {
	diversity_name="force_signed_positive_big";
	check_unsat_constraint=RequiredFromEachOutput (fun output ->
		match output with
		| CBV b ->
			let mask = Int64.shift_left 3L 62 in
			let required = Int64.shift_left 1L 62 in
			(b $&&$ mask) <> required
		| _ -> false
	);
	output_constraint_gen=fun output_expr_string ->
		let mask = Int64.shift_left 3L 62 in
		let required = Int64.shift_left 1L 62 in
		Printf.sprintf "(= (bvand %s %s) %s)"
			output_expr_string (string_of_const (CBV mask))
			(string_of_const (CBV required))
}

let all = [
	force_neg; force_pos; force_odd; force_even; force_neg_odd; force_minus_one; force_ubig; force_pos_sbig
]

let all_map = BatList.fold_left (fun m r -> BatMap.add r.diversity_name r m) BatMap.empty all
*)
type verification_constraints = {
	diversity_trials: diversity_constraint list;
	forbidden_inputs: const list list;
	avoid_existing: bool;
}

let default_verification_constraints = {
	diversity_trials=[] (* [force_ubig; force_pos_sbig; force_neg_odd; force_even; force_minus_one] *);
	forbidden_inputs=[];
	avoid_existing=true;
}

let empty_verification_constraints = {
	diversity_trials=[];
	forbidden_inputs=[];
	avoid_existing=false;
}

let verification_constraints_from_names (names: string): verification_constraints =
	let name_list = BatString.split_on_char ',' names |> BatList.filter (BatString.is_empty %> BatBool.neg) in
	let trials_rev =
		BatList.fold_left (fun trials_rev name ->
			try	BatMap.find name BatMap.empty (* all_map *)  :: trials_rev
			with Not_found -> begin
				if name = "default" then
					BatList.rev_append default_verification_constraints.diversity_trials trials_rev
				else if name = "no" then
					[]
				else begin
					Logger.g_error_f "ignore invalid diversity constraint name: %s" name;
					trials_rev
				end
			end
		) [] name_list
	in
	{
		diversity_trials=BatList.rev trials_rev;
		forbidden_inputs=[];
		avoid_existing=false;
	}

let process_verification_constraints
	(additional_constraints: verification_constraints)
	(spec: iospec)
	(params: expr BatSet.t)
	(output_expr_string: string)
: ((string * string) option * string list * verification_constraints) =
	let params_forbidden_str_list =
		BatSet.fold (fun param forbidden_constr_rev ->
			let forbidden_constr_rev' =
				match param with
				| Param(nth, _) ->
					BatList.fold_left (fun constrs input ->
							match BatList.at_opt input nth with
							| Some const ->
								Printf.sprintf "(assert (not (= %s %s)))" (string_of_expr param) (string_of_const const) :: forbidden_constr_rev
							| None -> forbidden_constr_rev
						) forbidden_constr_rev additional_constraints.forbidden_inputs
				| _ -> forbidden_constr_rev
			in
			forbidden_constr_rev' |> BatList.rev
		) params []
	in
	let avoid_existing_strs =
		if additional_constraints.avoid_existing then
			BatList.map (fun (_, existing_output) ->
					Printf.sprintf "(assert (not (= %s %s)))" output_expr_string (string_of_const existing_output)
				) spec
		else []
	in
	let (diversity_name_and_str_opt, next_diversity_trials) =
		process_diversity additional_constraints.diversity_trials output_expr_string spec
	in
	(* let diversity_strs = BatOption.map_default (fun x -> [x]) [] diversity_str_opt in *)
	(diversity_name_and_str_opt, params_forbidden_str_list @ avoid_existing_strs, {additional_constraints with diversity_trials = next_diversity_trials})
