open Common
open Vocab
open SynthLang.Exprs
open SynthLang.Grammar
open SynthBase.BidirectionalUtils

(* nt_sigs: signatures of the nonterminal of which desired output is to be derived *)
(* arg_sigs: desired signatures of the previous arguments *)
(* return: desired signatures of the nonterminal of the current argument *)
let witness available_height nt_sigs (int_sigs, bv_sigs, string_sigs, bool_sigs) rule output_sig arg_sigs =
	let op = SynthLang.Grammar.op_of_rule rule in  
	(** Theory agnostic *)
	if (String.compare op "=") = 0 then
		if (type_of_signature output_sig) <> Bool then assert false
		else
		if (BatList.length arg_sigs) = 0 then nt_sigs
		else 
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					(is_abstract_bool output_const) || (* for learn_ite *)
					(let output_v = get_concrete_bool output_const in
					 ((Stdlib.compare arg0_const arg1_const) = 0) = output_v)
				) (BatList.combine arg0_sig arg1_sig) output_sig 
			) nt_sigs
	else
		let witness_fun = 
			match ret_type_of_rewrite rule with
			| String -> WitnessSTR.witness
			| Bool -> WitnessSAT.witness
			| BV _ -> WitnessBV.witness
			| Int -> WitnessLIA.witness
  		in
		witness_fun available_height nt_sigs (int_sigs, bv_sigs, string_sigs, bool_sigs) rule output_sig arg_sigs
		 
