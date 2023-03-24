open Common
open Vocab
open Int64Util
open SynthLang
open BitVecCommon
open ABitSeq

let bit_and (m1,v1) (m2,v2) =
    match (m1, v1), (m2, v2) with
    | (0,0), (0,0) -> (0,0)
    | (0,0), (0,1) -> (0,0)
    | (0,0), (1,0) -> (1,0)
    | (0,0), (1,1) -> (1,1)
    
    | (0,1), (0,0) -> (0,0)
    | (0,1), (0,1) -> (0,1)
    | (0,1), (1,0) -> (1,0)
    | (0,1), (1,1) -> (1,1)
    
    | (1,0), (0,0) -> (1,0)
    | (1,0), (0,1) -> (1,0)
    | (1,0), (1,0) -> (1,0)
    | (1,0), (1,1) -> (1,0)
    
    | (1,1), (0,0) -> (1,1)
    | (1,1), (0,1) -> (1,1)
    | (1,1), (1,0) -> (1,0)
    | (1,1), (1,1) -> (1,1)
    
    | _ -> (0,0)

let bit_or (m1,v1) (m2,v2) =
    match (m1,v1), (m2,v2) with
    | (0,0), (0,0) -> (0,0)
    | (0,0), (0,1) -> (0,1)
    | (0,0), (1,0) -> (1,0)
    | (0,0), (1,1) -> (1,1)
    
    | (0,1), (0,0) -> (0,1)
    | (0,1), (0,1) -> (0,1)
    | (0,1), (1,0) -> (1,0)
    | (0,1), (1,1) -> (1,1)
    
    | (1,0), (0,0) -> (1,0)
    | (1,0), (0,1) -> (1,0)
    | (1,0), (1,0) -> (1,0)
    | (1,0), (1,1) -> (1,0)

    | (1,1), (0,0) -> (1,1)
    | (1,1), (0,1) -> (1,1)
    | (1,1), (1,0) -> (1,0)
    | (1,1), (1,1) -> (1,1)

    | _ -> 0,1

let bit_xor (m1,v1) (m2,v2) =
    match (m1,v1), (m2,v2) with
    | (0,0), (0,0) -> (0,0)
    | (0,0), (0,1) -> (0,1)
    | (0,0), (1,0) -> (1,0)
    | (0,0), (1,1) -> (1,1)
    
    | (0,1), (0,0) -> (0,1)
    | (0,1), (0,1) -> (0,0)
    | (0,1), (1,0) -> (1,0)
    | (0,1), (1,1) -> (1,1)
    
    | (1,0), (0,0) -> (1,0)
    | (1,0), (0,1) -> (1,0)
    | (1,0), (1,0) -> (1,0)
    | (1,0), (1,1) -> (1,0)
    
    | (1,1), (0,0) -> (1,1)
    | (1,1), (0,1) -> (1,1)
    | (1,1), (1,0) -> (1,0)
    | (1,1), (1,1) -> (1,1)

    | _ -> (0,1)

let bit_join (m1,v1) (m2,v2): int * int =
    match (m1,v1), (m2,v2) with
    | (0,0), (0,0) -> (0,0)
    | (0,0), (0,1) -> (1,1)
    | (0,0), (1,0) -> (0,0)
    | (0,0), (1,1) -> (1,1)

    | (0,1), (0,0) -> (1,1)
    | (0,1), (0,1) -> (0,1)
    | (0,1), (1,0) -> (0,1)
    | (0,1), (1,1) -> (1,1)

    | (1,0), (0,0) -> (0,0)
    | (1,0), (0,1) -> (0,1)
    | (1,0), (1,0) -> (1,0)
    | (1,0), (1,1) -> (1,1)
    
    | (1,1), (0,0) -> (1,1)
    | (1,1), (0,1) -> (1,1)
    | (1,1), (1,0) -> (1,1)
    | (1,1), (1,1) -> (1,1)

    | _ -> (1,1)

let bit_meet (m1,v1) (m2,v2) =
    match (m1,v1), (m2,v2) with
    | (0,0), (0,0) -> (0,0)
    | (0,0), (0,1) -> (1,0)
    | (0,0), (1,0) -> (1,0)
    | (0,0), (1,1) -> (0,0)
    
    | (0,1), (0,0) -> (1,0)
    | (0,1), (0,1) -> (0,1)
    | (0,1), (1,0) -> (1,0)
    | (0,1), (1,1) -> (0,1)
    
    | (1,0), (0,0) -> (1,0)
    | (1,0), (0,1) -> (1,0)
    | (1,0), (1,0) -> (1,0)
    | (1,0), (1,1) -> (1,0)
    
    | (1,1), (0,0) -> (0,0)
    | (1,1), (0,1) -> (0,1)
    | (1,1), (1,0) -> (1,0)
    | (1,1), (1,1) -> (1,1)
    
    | _ -> (1,0)

let bit_leq (m1,v1) (m2,v2) =
    match (m1,v1), (m2,v2) with
    | (0,0), (0,0) -> 1
    | (0,0), (0,1) -> 0
    | (0,0), (1,0) -> 0
    | (0,0), (1,1) -> 1

    | (0,1), (0,0) -> 0
    | (0,1), (0,1) -> 1
    | (0,1), (1,0) -> 0
    | (0,1), (1,1) -> 1
    
    | (1,0), (0,0) -> 1
    | (1,0), (0,1) -> 1
    | (1,0), (1,0) -> 1
    | (1,0), (1,1) -> 1

    | (1,1), (0,0) -> 0
    | (1,1), (0,1) -> 0
    | (1,1), (1,0) -> 0
    | (1,1), (1,1) -> 1
    
    | _ -> 0

let backward_and (post: t) (e1: t) (e2: t): t * t =
    match post, e1, e2 with
    | B_One, _, _ -> (B_One, B_One)
    | B_Zero, B_One, _ -> (B_One, B_Zero)
    | B_Zero, _, B_One -> (B_Zero, B_One)
    | _, _, _ -> (B_Top, B_Top)

let bit_back_and (post_m,post_v) (m1,v1) (m2,v2) =
    match post_m,post_v, m1,v1, m2,v2 with
    | 0, 1, _, _, _, _ -> (0, 1), (0, 1)
    | 0, 0, 0, 1, _, _ -> (0, 1), (0, 0)
    | 0, 0, _, _, 0, 1 -> (0, 0), (0, 1)
    | _, _, _, _, _, _ -> (1, 1), (1, 1)

let bit_back_and2 (post_m,post_v) (m1,v1) (m2,v2) =
    let result_m =  post_m || (not post_v && (post_v || m1 || not v1) && (post_v || m2 || not v2)) in
    let result_v1 = post_m || post_v || m2 || not v2 in
    let result_v2 = post_m || post_v || m1 || not v1 in
    (result_m, result_v1), (result_m, result_v2)

(* result_m1 = result_m2
    = not (not post_m && (post_v || (not post_v && not m1 && v1) || (not post_v && not m2 && v2)))
    = post_m || (not post_v && not (not post_v && not m1 && v1) && not (not post_v && not m2 && v2)))
    = post_m || (not post_v && (post_v || m1 || not v1) && (post_v || m2 || not v2))

result_v1 = ~~(~~post_m $&&$ ~~post_v $&&$ ~~m2 $&&$ v2)
    = post_m $||$ post_v $||$ m2 $||$ ~~v2
result_v2 = ~~(~~post_m $&&$ ~~post_v $&&$ ~~m1 $&&$ v1)
    = = post_m $||$ post_v $||$ m1 $||$ ~~v1 *)

let bit_back_or (post_m,post_v) (m1,v1) (m2,v2) =
    match post_m,post_v, m1,v1, m2,v2 with
    | 0, 0, _, _, _, _ -> (0, 0), (0, 0)
    | 0, 1, 0, 0, _, _ -> (0, 0), (0, 1)
    | 0, 1, _, _, 0, 0 -> (0, 1), (0, 0)
    | _, _, _, _, _, _ -> (1, 1), (1, 1)

let bit_back_or2 (post_m,post_v) (m1,v1) (m2,v2) =
    let result_m =  post_m || (post_v && (not post_v || m1 || v1) && (not post_v || m2 || v2)) in
    let result_v1 = post_m || (post_v && (m1 || v1)) in
    let result_v2 = post_m || (post_v && (m2 || v2)) in
    (result_m, result_v1), (result_m, result_v2)

(* result_m1 = result_m2
    = not (not post_m && (not post_v || (post_v && not m1 && not v1) || (post_v && not m2 && not v2)))
    = (post_m || (post_v && not (post_v && not m1 && not v1) && not (post_v && not m2 && not v2)))
    = (post_m || (post_v && (not post_v || m1 || v1) && (not post_v || m2 || v2)))

result_v1 = not (not post_m && (not post_v || (not m1 && not v1)))
    = (post_m || not (not post_v || (not m1 && not v1)))
    = (post_m || (post_v && (m1 || v1)))
*)

let bit_back_xor (post_m,post_v) (m1,v1) (m2,v2) =
    match post_m,post_v, m1,v1, m2,v2 with
    | 0, 0, 1, 1, _, _ -> (m2, v2), (m2, v2)
    | 0, 0, _, _, 1, 1 -> (m1, v1), (m1, v1)
    | 0, 0, _, _, _, _ -> (m2, v2), (m1, v1)
    | 0, 1, 1, 1, _, _ -> (m2, not (m2 <> v2)), (m2, v2)
    | 0, 1, _, _, 1, 1 -> (m1, v1), (m1, not (m1 <> v1))
    | 0, 1, _, _, _, _ -> (m2, not (m2 <> v2)), (m1, not (m1 <> v1))
    | _, _, _, _, _, _ -> (1, 1), (1, 1)

let bit_bac_xor2 (post_m,post_v) (m1,v1) (m2,v2) =
    let d1top = m1 && v1 in
    let d2top = m2 && v2 in
    let no_top = not (d1top || d2top) in
    let result_m1 = post_m || (not d2top && m2) || (d2top && m1) in
    let result_m2 = post_m || (not d1top && m1) || (d1top && m2) in
    let result_v1 =
        post_m || (
            (d2top && v1)
            ||
            (not d2top && (
                (not post_v && v2)
                ||
                (post_v && not (m2 <> v2))
            ))
        )
    in
    let result_v2 =
        post_m || (
            (d1top && v2)
            ||
            (not d1top && (
                (not post_v && v1)
                ||
                (post_v && not (m1 <> v1))
            ))
        )
    in
    ((result_m1, result_v1), (result_m2, result_v2))

(*
result_v1 =
    post_m || (
        (d2top && v1)
        ||
        (not d2top && (
            (not post_v && v2)
            ||
            (post_v && not (m2 <> v2)
        ))
    )
*)