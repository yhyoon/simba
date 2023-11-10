(**
  * Augmented Synthesis Specification Used in Runtime
  *)

open Common
open Vocab

open SynthLang

open SynthProblem

open Dom.AbstDom

type ex_input = Specification.ex_input

(**
  ODontCare: 일부 입출력만 고려하는 문제를 풀고 싶을 때, 나머지를 ODontCare로 전환하면 된다. OAbstract에 top을 준 것과 같은 효과.
  OConcrete: 일반적인 PBE 문제의 입출력 스펙.
  OAbstract: 출력의 요약값으로 주어진 스펙.
  *)
type output_spec =
    | ODontCare of Exprs.exprtype
    | OConcrete of Exprs.const
    | OAbstract of abst_output_spec
(* maybe extended to OLogicForm...? etc... *)

(* type of output spec is always known -> we don't need general top/bot. see AbstSig.t *)
and abst_output_spec =
    | AOBV64 of RedProd.t
    | AOBV32 of RedProd.t
    | AOBV of int * RedProd.t
    | AOInt of RedProd.t
    | AOBool of Dom.ABitSeq.Elem.t

type io_spec = ex_input * output_spec

exception SolutionFoundTrivial of Exprs.expr

let string_of_output_spec (output_spec: output_spec): string =
    match output_spec with
    | ODontCare _ -> "*"
    | OConcrete const -> Exprs.string_of_const const
    | OAbstract AOBV64 r ->
        RedProd64.to_string r
    | OAbstract AOBV32 r ->
        RedProd32.to_string r
    | OAbstract AOBV (len, r) ->
        let module I = Int64Util.MaskedInt64(struct let size = len end) in
        let module P = RedProd.Make(I) in
        P.to_string r
    | OAbstract AOInt r ->
        RedProd64.to_string r
    | OAbstract AOBool b ->
        Dom.ABitSeq.Elem.to_string b

let string_of_io_spec (io_spec: io_spec): string =
    let (input, output) = io_spec in
    Printf.sprintf "i:%s -> o:%s"
        (string_of_list Exprs.string_of_const input)
        (string_of_output_spec output)

let type_of_output_spec (output_spec: output_spec): Exprs.exprtype =
    match output_spec with
    | ODontCare _ -> failwith "type_of_output_spec: ODontCare"
    | OConcrete const -> Exprs.type_of_const const
    | OAbstract AOBV64 r -> Exprs.BV 64
    | OAbstract AOBV32 r -> Exprs.BV 32
    | OAbstract AOBV (len, r) -> Exprs.BV len
    | OAbstract AOInt r -> Exprs.Int
    | OAbstract AOBool b -> Exprs.Bool

let alpha_output_spec (output_specs: output_spec list): AbstSig.t =
    match output_specs with
    | [] -> failwith "empty signature"
    | OConcrete Exprs.CBV (len, _) :: _ | ODontCare BV len :: _ -> begin
        match len with
        | 64 ->
            BitVec64 (BatList.map (fun c -> match c with
                    | OConcrete (Exprs.CBV (_, i)) -> RedProd64.from_int64 i
                    | ODontCare _ -> RedProd64.top_repr
                    | OAbstract AOBV64 x -> x
                    | _ -> failwith_f "signature_of_const_list(%s in CBV list): kind mismatch" (string_of_output_spec c)
                ) output_specs)
        | 32 ->
            BitVec32 (BatList.map (fun c -> match c with
                    | OConcrete (Exprs.CBV (_, i)) -> RedProd32.from_int64 i
                    | ODontCare _ -> RedProd32.top_repr
                    | OAbstract AOBV32 x -> x
                    | _ -> failwith_f "signature_of_const_list(%s in CBV list): kind mismatch" (string_of_output_spec c)
                ) output_specs)
        | _ ->
            let module I = Int64Util.MaskedInt64(struct let size = len end) in
            let module P = RedProd.Make(I) in
            BitVecGeneral (len, BatList.map (fun c -> match c with
                    | OConcrete (Exprs.CBV (_, i)) -> P.from_int64 i
                    | ODontCare _ -> P.top_repr
                    | OAbstract AOBV (len', x) when len = len' -> x
                    | _ -> failwith_f "signature_of_const_list(%s in CBV list): kind mismatch" (string_of_output_spec c)
                ) output_specs)
    end
    | OConcrete Exprs.CInt _ :: _ | ODontCare Int :: _ ->
        Int (BatList.map (fun c -> match c with
                | OConcrete (Exprs.CInt i) -> RedProd64.from_int64 (Int64.of_int i)
                | ODontCare _ -> RedProd64.top_repr
                | OAbstract AOInt x -> x
                | _ -> failwith_f "signature_of_const_list(%s in CInt list): kind mismatch" (string_of_output_spec c)
            ) output_specs)
    | OConcrete CBool _ :: _ | ODontCare Exprs.Bool :: _ ->
        Bool (Dom.ABoolSig.of_list (BatList.map (fun c -> match c with
                | OConcrete (Exprs.CBool b) -> Elem.from_bool false b
                | ODontCare _ -> Elem.B_Top
                | OAbstract AOBool b -> b
                | _ -> failwith_f "signature_of_const_list(%s in CBool list): kind mismatch" (string_of_output_spec c)
            ) output_specs))
    | _ -> Bot

let is_solution_sig (io_spec: io_spec list) (signature: Exprs.signature): bool =
    let abst_desired_sig = alpha_output_spec (BatList.map snd io_spec) in
    let abst_signature = Dom.AbstDom.AbstSig.alpha signature in
    Dom.AbstDom.AbstSig.leq abst_signature abst_desired_sig

let is_solution_expr (io_spec: io_spec list) (expr: Exprs.expr): bool =
    try
        is_solution_sig io_spec (Exprs.compute_signature (BatList.map fst io_spec) expr)
    with Exprs.UndefinedSemantics -> false

let aug_output_spec (c: Specification.ex_output): output_spec = OConcrete c

let aug_ex_io (ex_io: Specification.ex_io): io_spec =
    map_snd aug_output_spec ex_io

let de_aug_spec (spec_list: io_spec list): Specification.ex_io list =
    BatList.map (function
    | (ex_input, OConcrete ex_output) ->
        (ex_input, ex_output)
    | _ ->
        failwith "de_aug_spec: non-concrete output cannot be de-augmented"
    ) spec_list

type t = {
    syn_spec: syn_spec;
    sem_spec: sem_spec;
}

and syn_spec = {
    grammar: Grammar.grammar;                                               (* given grammar *)
    target_function_id: Operators.op;                                       (* target function id *)
    args_list: (string * Exprs.expr) list;                                  (* argument list *)
    nt_rule_list: (Grammar.non_terminal * Grammar.rewrite) list;            (* easy access to grammar rules *)
    nt_rule_list_wo_ite: (Grammar.non_terminal * Grammar.rewrite) list;     (* preprocessed rules - remove branch expression *)
}

and sem_spec = {
    original_spec: Specification.t;                     (* specification from given problem *)
    spec_cex: (ex_input * output_spec) list;            (* whole counter examples *)
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

(* pred 가 true 가 된다는 사실로부터 적절히 input-output spec 을 생성한다. 구현에 따라선 여러개 일수도...?
   (ex_input, OAbstract xxx) 형태가 될 것임.
   *)
let alpha_predicate_constraint (pred: Exprs.expr) (spec: t): io_spec list =
    failwith_f "Not Implemented: alpha_predicate_constraint %s" (Exprs.string_of_expr pred)

let add_trivial_example (spec: t): t =
    let trivial_sol =
        Exprs.Const (Exprs.get_trivial_value (SynthLang.Grammar.type_of_nt SynthLang.Grammar.start_nt))
    in
    match Specification.verify [] false spec.syn_spec.target_function_id spec.syn_spec.args_list trivial_sol spec.sem_spec.original_spec with 
    | None ->
        raise (SolutionFoundTrivial trivial_sol)  
    | Some (CexIO cex, _) ->
        let _ = assert (not (List.mem cex spec.sem_spec.original_spec.spec_pbe)) in  
        add_cex_spec (aug_ex_io cex) spec
    | Some (CexPred pred, _) ->
        BatList.fold_left (fun acc s -> add_cex_spec s acc) spec (alpha_predicate_constraint pred spec)

let augment_contraints (spec: Specification.t): sem_spec =
    let io_spec_list =
        if BatList.is_empty spec.spec_pbe then
            []
        else
            if BatOption.default (Specification.need_solver_check spec) Global.t.cli_options.ex_all then
                BatList.map aug_ex_io spec.spec_pbe
            else
                (* get first one *)
                [aug_ex_io (BatList.hd spec.spec_pbe)]
    in
    {
        original_spec=spec;
        spec_cex=io_spec_list;
    }

let problem_to_spec (problem: Parse.parse_result): t =
    let nt_rule_list = Grammar.get_nt_rule_list problem.grammar in
	let nt_rule_list_wo_ite = BatList.filter (fun (nt, rule) -> not (Grammar.is_ite_function_rule rule)) nt_rule_list in
    let syn_spec = {
        grammar=problem.grammar;
        target_function_id=problem.target_function_id;
        args_list=problem.args_list;
        nt_rule_list=nt_rule_list;
        nt_rule_list_wo_ite=nt_rule_list_wo_ite;
    }
    in
    let spec = {
        syn_spec=syn_spec;
        sem_spec= augment_contraints problem.spec_total;
    }
    in
    if not (BatList.is_empty spec.sem_spec.spec_cex) then
        spec
    else
        add_trivial_example spec
