(**
  * Augmented Synthesis Specification Used in Runtime
  *)

open Common
open Vocab

open SynthLang

open SynthProblem

type ex_input = Specification.ex_input

type output_spec =
    | CDontCare of Exprs.exprtype
    | CConcrete of Exprs.const
    | CAbstract of Dom.AbstDom.AbstSig.t
(* TODO: | CLogic... *)

type io_spec = ex_input * output_spec

exception SolutionFoundTrivial of Exprs.expr

let string_of_output_spec (output_spec: output_spec): string =
    match output_spec with
    | CDontCare _ -> "*"
    | CConcrete const -> Exprs.string_of_const const
    | CAbstract abst_sig -> Dom.AbstDom.AbstSig.to_string abst_sig

let string_of_io_spec (io_spec: io_spec): string =
    let (input, output) = io_spec in
    Printf.sprintf "i:%s -> o:%s"
        (string_of_list Exprs.string_of_const input) 
        (string_of_output_spec output) 

let aug_output_spec (c: Specification.ex_output): output_spec = CConcrete c

let aug_ex_io (ex_io: Specification.ex_io): io_spec =
    map_snd aug_output_spec ex_io

let de_aug_spec (spec_list: io_spec list): Specification.ex_io list =
    BatList.map (function
    | (ex_input, CConcrete ex_output) ->
        (ex_input, ex_output)
    | _ ->
        failwith "de_aug_spec: non-concrete output cannot be de-augmented"
    ) spec_list

let signature_of_ex_outputs (spec: io_spec list): Exprs.signature =
    de_aug_spec spec |>
    BatList.map snd |>
    Exprs.signature_of_const_list

type t = {
    syn_spec: syn_spec;
    sem_spec: sem_spec;
}

and syn_spec = {
    grammar: Grammar.grammar;                                               (* given grammar *)
    nt_rule_list: (Grammar.non_terminal * Grammar.rewrite) list;            (* easy access to grammar rules *)
    nt_rule_list_wo_ite: (Grammar.non_terminal * Grammar.rewrite) list;     (* preprocessed rules - remove branch expression *)
}

and sem_spec = {
    original_spec: Specification.t;                     (* specification from given problem *)
    spec_cex: (ex_input * output_spec) list;      (* whole counter examples *)
    desired_output_signature: Exprs.signature;            (* output signature of whole counter examples *)
}

let augment_grammar (grammar: Grammar.grammar): syn_spec =
	let nt_rule_list = Grammar.get_nt_rule_list grammar in
	let nt_rule_list_wo_ite = BatList.filter (fun (nt, rule) -> not (Grammar.is_ite_function_rule rule)) nt_rule_list in
	{
		grammar=grammar;
		nt_rule_list=nt_rule_list;
		nt_rule_list_wo_ite=nt_rule_list_wo_ite;
	}

let add_cex_spec (inputs, output_spec) spec =
    if (List.mem (inputs, output_spec) spec.sem_spec.spec_cex) then
        spec
    else
        {spec with
            sem_spec = {spec.sem_spec with
                spec_cex = spec.sem_spec.spec_cex @ [(inputs, output_spec)]
            };
        }

let get_trivial_examples (grammar: SynthLang.Grammar.grammar) (spec: Specification.t): io_spec list =
    let _ = assert (Exprs.is_function_expr (BatOption.get spec.spec_oracle_expr)) in
    let _ = assert (Exprs.is_function_expr (BatOption.get spec.spec_oracle_expr_resolved)) in 
    let trivial_sol = 
        Exprs.Const (Exprs.get_trivial_value (SynthLang.Grammar.type_of_nt SynthLang.Grammar.start_nt))
    in
    match Specification.verify SpecDiversity.empty_verification_constraints trivial_sol spec with 
    | None -> raise (SolutionFoundTrivial trivial_sol)  
    | Some (CexIO cex, _) ->
        let _ = assert (not (List.mem cex spec.spec_pbe)) in  
        [aug_ex_io cex]

let augment_contraints (grammar: SynthLang.Grammar.grammar) (spec: Specification.t): sem_spec =
    let io_spec_list =
        if BatList.is_empty spec.spec_pbe then
            get_trivial_examples grammar spec
        else
            if BatOption.default (not (Specification.is_pbe_only spec)) Global.t.cli_options.ex_all then
                BatList.map aug_ex_io spec.spec_pbe
            else
                (* get first one *)
                [aug_ex_io (BatList.hd spec.spec_pbe)]
    in
    let augmented_spec = io_spec_list in
    {
        original_spec=spec;
        spec_cex=io_spec_list;
        desired_output_signature=signature_of_ex_outputs augmented_spec;
    }

let problem_to_spec (problem: Parse.parse_result): t =
    let sem_spec = augment_contraints problem.grammar problem.spec_total in
    let syn_spec = augment_grammar problem.grammar in
    {
        syn_spec=syn_spec;
        sem_spec=sem_spec;
    }