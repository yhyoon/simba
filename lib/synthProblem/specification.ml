(**
    *    Representation of SyGuS Problem - Semantic Part
  *)
open Sexplib
open Z3

open Common
open Vocab
open SynthLang.Exprs
open SexpUtil

exception UnknownModel

(** PBE Part *)
type ex_input = const list
type ex_output = const
type ex_io = ex_input * ex_output

type spec_oracle_function = {
    oracle_name: string;
    oracle_params: (string * exprtype) list;
    oracle_function_body: expr;
}

type spec_logic =
  | SpecOracle of spec_oracle_function (* oracle function - verify by equality check *)
  | SpecGeneral of expr list (* list of predicates *)

type t = {
    spec_pbe: ex_io list;
    spec_logic: spec_logic option;
}

let empty_spec: t = {
    spec_pbe = [];
    spec_logic = None;
}

let string_of_ex_io ex_io =
    let (ex_input, ex_output) = ex_io in
    Printf.sprintf "i:%s -> o:%s"
        (string_of_list string_of_const ex_input) 
        (string_of_const ex_output) 

let add_ex_io (ex_input, ex_output) spec = 
    if (List.mem (ex_input, ex_output) spec.spec_pbe) then spec
    else 
        {spec with spec_pbe = spec.spec_pbe @ [(ex_input, ex_output)]}

let string_of_ex_io_list ex_io_list = 
    string_of_list (fun (ex_input, ex_output) ->
        Printf.sprintf "i:%s -> o:%s"
        (string_of_list string_of_const ex_input) 
        (string_of_const ex_output) 
    ) ex_io_list

let add_oracle_spec oracle_name oracle_params oracle_function_body spec =
    match spec.spec_logic with
    | None -> {
        spec with spec_logic = Some (SpecOracle {
            oracle_name = oracle_name;
            oracle_params = oracle_params;
            oracle_function_body = oracle_function_body;
        })
    }
    | _ -> raise (Invalid_argument "add_oracle_spec: multiple oracle exprs")

let add_logic_spec exp spec =
    if type_of_expr exp = Bool then
        match spec.spec_logic with
        | None ->
            {spec with spec_logic = Some (SpecGeneral [exp])}
        | Some (SpecGeneral exps) ->
            {spec with spec_logic = Some (SpecGeneral (exp::exps))}
        | Some (SpecOracle _) -> (* oracle spec has higher priority *)
        failwith "add_logic_spec: oracle spec already exists"
    else
        failwith "add_logic_spec: not a boolean constraint"

let need_solver_check (t: t): bool =
    BatOption.is_some t.spec_logic

type counter_example =
  | CexIO of ex_io
  | CexPred of ex_input * expr  (* inputs and predicate which holds for that inputs *)
    (* maybe extended more ... *)

let process_verification_constraints
	?(output_expr_string_for_avoid_existing: string option=None)
	(forbidden_inputs: const list list)
	(ex_output_list: const list)
	(params: expr BatSet.t)
: string list =
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
						) forbidden_constr_rev forbidden_inputs
				| _ -> forbidden_constr_rev
			in
			forbidden_constr_rev' |> BatList.rev
		) params []
	in
	let avoid_existing_strs =
		match output_expr_string_for_avoid_existing with
		| Some output_expr_string ->
			BatList.map (fun existing_output ->
					Printf.sprintf "(assert (not (= %s %s)))" output_expr_string (string_of_const existing_output)
				) ex_output_list
		| None -> []
	in
	params_forbidden_str_list @ avoid_existing_strs

(* Using Z3 OCaml API *)
let rec verify (forbidden_inputs: const list list) (avoid_existing: bool) (target_function_id: SynthLang.Operators.op) (args_list: (string * expr) list) (sol: expr) (spec: t): (counter_example * const list list) option =
    let start = Sys.time () in
    match spec.spec_logic with
    | Some spec_logic -> begin
        let params = args_list |> BatList.map snd |> BatSet.of_list in
        let additional_constraint_str =
            process_verification_constraints forbidden_inputs (BatList.map snd spec.spec_pbe) params
            (* process_verification_constraints ~output_expr_string_for_avoid_existing:(Some oracle_expr_smt_repr) forbidden_inputs (BatList.map snd spec.spec_pbe) params *)
        in
        let query_smt_repr =
            let decl_params_smt_repr_list =
                BatSet.fold (fun param acc_rev ->
                    let decl_str = Printf.sprintf "(declare-const %s %s)"
                        (string_of_expr param)
                        (string_of_type ~z3:true (type_of_expr param))
                    in
                    decl_str::acc_rev
                ) params []
                |> BatList.rev
            in
            let main_constraint_smt_repr =
                match spec_logic with
                | SpecOracle oracle_function ->
                    Printf.sprintf "(assert (not (= %s %s)))"
                        (string_of_expr oracle_function.oracle_function_body)
                        (string_of_expr sol)
                | SpecGeneral predicate -> begin
                    match predicate with
                    | [] -> failwith "empty predicate"
                    | first_predicate :: predicate_tail ->
                        let concat = BatList.fold_left (fun acc p ->
                            Printf.sprintf "(and %s %s)" acc (string_of_expr p)
                            ) (string_of_expr first_predicate) predicate_tail
                        in
                        Printf.sprintf "(assert (not %s))" concat
                end
            in
            let lines =
                decl_params_smt_repr_list @ main_constraint_smt_repr :: additional_constraint_str
            in
            string_of_list ~first:"" ~last:"" ~sep:"\n" identity lines
        in
        let _ =
            Logger.g_debug "query cex to solver:";
            Logger.g_with_increased_depth (fun () ->
                Logger.g_debug query_smt_repr
            )
        in
        let (q, solver) = Z3interface.smt_check query_smt_repr in
        let _ = 
            Global.tick_solver_call (Sys.time() -. start) Global.t
        in
        match q with
        | UNSATISFIABLE -> begin
            if avoid_existing then begin
                Logger.g_info "output distinction constraint maybe unavailable, retry with turning off";
                verify forbidden_inputs false target_function_id args_list sol spec
            end
            else None
        end
        | UNKNOWN -> raise UnknownModel
        | SATISFIABLE -> begin
            let m = Z3.Solver.get_model solver in
            match m with
            | None -> assert false
            | Some model ->
                let _ = Logger.g_debug_lazy (fun () -> Z3.Model.to_string model) in 
                let decls = Z3.Model.get_decls model in
                let var_map: (string, const) BatMap.t =
                    List.fold_left (fun acc decl ->
                        let symbol = Z3.FuncDecl.get_name decl in
                        let value : const =
                            let exp_opt = Z3.Model.get_const_interp model decl in
                            match exp_opt with
                            | None -> raise UnknownModel
                            | Some expr -> sexp_to_const (Sexp.Atom (Z3.Expr.to_string expr))
                        in
                        BatMap.add (Z3.Symbol.to_string symbol) value acc
                    ) BatMap.empty decls
                in
                let cex_input: const list =
                    let _ =
                        if BatMap.is_empty var_map then
                        failwith "Z3 returns the empty model. Check out if (DY)LD_LIBRARY_PATH includes a path to the Z3 folder."
                    in
                    let param_ids = BatList.map snd args_list |> BatList.map string_of_expr in
                    List.map (fun x -> try BatMap.find x var_map with Not_found -> assert false) param_ids
                in
                let sol_output_opt =
                    try
                        Some (compute_signature [cex_input] sol |> sig_hd)
                    with UndefinedSemantics -> None
                in
                match spec_logic with
                | SpecOracle oracle_function -> begin
                    try
                        let cex_output = compute_signature [cex_input] oracle_function.oracle_function_body |> sig_hd in
                        Logger.g_debug_f "sol:%s" (BatOption.map_default string_of_const "N/A" sol_output_opt);
                        Logger.g_debug_f "oracle:%s" (string_of_const cex_output);
                        Logger.g_debug_f "cex : %s" (string_of_ex_io (cex_input, cex_output));
                        BatOption.may (fun so ->
                                if (Stdlib.compare so cex_output) = 0 then
                                    failwith (Printf.sprintf "solution = oracle: %s = %s" (string_of_const so) (string_of_const cex_output))
                                else ()
                            ) sol_output_opt;
                        Some (CexIO (cex_input, cex_output), forbidden_inputs)
                    with UndefinedSemantics -> begin
                        Logger.g_error_f "Z3 returned invalid cex, add to forbidden list and retry: %s" (string_of_list string_of_const cex_input);
                        verify (cex_input :: forbidden_inputs) avoid_existing target_function_id args_list sol spec
                    end
                end 
                | SpecGeneral predicates -> begin
                    let subst_map =
                        BatMap.foldi (fun id c m -> BatMap.add (Var(id, SynthLang.Exprs.type_of_const c)) (Const c) m) var_map BatMap.empty
                    in
                    let subst p = SynthLang.Exprs.change_var_to_expr subst_map p in
                    let cex_predicates =
                        BatList.fold_left (fun acc predicate ->
                                let assigned = subst predicate in
                                Function (SynthLang.Operators.BOOL_OP (SynthLang.Operators.B_BIN_OP SynthLang.Operators.B_AND), [acc; assigned], Bool)
                            ) (BatList.hd predicates |> subst) (BatList.tl predicates)
                    in
                    Some (CexPred (cex_input, cex_predicates), forbidden_inputs)
                end 
        end
    end
    | None -> None