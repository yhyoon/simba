open Common
open Vocab
open Int64Util
open SynthLang
open BitVecCommon

exception SInvalid_boundary of int * int64 * int64

let _ = Printexc.register_printer (fun exn ->
        match exn with
        | SInvalid_boundary(b,l,r) ->
            Some(Printf.sprintf "Signed_invalid_boundary(%Ld,%Ld) in %d bits" l r b)
        | _ -> None
    )

let invalid_boundary (bit_length: int) (lb: int64) (rb: int64): 'a =
    raise (SInvalid_boundary (bit_length, lb, rb))

type t = SIBot | SIntv of int64 * int64

module Make(I: MaskedInt64Type) = struct
    let lbound_min: int64 = I.signed_min_int
    let rbound_max: int64 = I.signed_max_int

    let bot_repr: t = SIBot

    let top_repr: t = SIntv (lbound_min, rbound_max)

    let from_int64 (i: int64): t =
        SIntv (I.apply_mask i, I.apply_mask i)
    
    let zero: t = SIntv (0L, 0L)

    let intv (lb: int64) (rb: int64): t =
        if I.signed_compare lb rb > 0 then
            invalid_boundary I.bit_length lb rb
        else SIntv (lb, rb)

    let gamma_size_constraint (max_size: int) (t: t): Exprs.const BatSet.t option =
        match t with
        | SIBot -> Some BatSet.empty
        | SIntv (l, u) ->
            if t = top_repr then None
            else
                let width = I.add (I.sub u l) 1L in
                if Int64.unsigned_compare width (Int64.of_int max_size) <= 0 then
                    let rec worker c s =
                        let cmp = I.signed_compare c u in
                        if cmp < 0 then
                            worker (I.add c 1L) (BatSet.add (Exprs.CBV (I.bit_length, c)) s)
                        else if cmp = 0 then
                            BatSet.add (Exprs.CBV (I.bit_length, c)) s
                        else s
                    in
                    Some (worker l BatSet.empty)
                else None
    
    let gamma_if_singleton (t: t): Exprs.const option =
        match t with
        | SIBot -> None
        | SIntv (lb,rb) -> if lb = rb then Some (Exprs.CBV (I.bit_length, lb)) else None

    (* split domain into (negative_range, non_negative_range) *)
    let sign_split (t: t): t * t =
        match t with
        | SIBot -> (SIBot, SIBot)
        | SIntv (l,r) ->
            if I.signed_compare r 0L < 0 then
                (t, SIBot)
            else if I.signed_compare l 0L < 0 then
                (intv l I.minus_one, intv 0L r)
            else (SIBot, t)

    (* split domain into (signed_min_int_singleton, non_signed_min_int negative_range, zero, positive_range) *)
    let sign_split_more (t: t): t * t * t * t =
        match t with
        | SIBot -> (SIBot, SIBot, SIBot, SIBot)
        | SIntv (l,r) ->
            let (neg, non_neg) = sign_split t in
            let (smi, neg') = match neg with
                | SIBot -> (SIBot, SIBot)
                | SIntv (l,r) ->
                    let (smi, l') =
                        if I.signed_compare l I.signed_min_int = 0 then
                            (from_int64 I.signed_min_int, I.add l 1L)
                        else (SIBot, l)
                    in
                    if I.signed_compare I.signed_min_int r < 0 then
                        (smi, intv l' r)
                    else (smi, SIBot)
            in
            let (zero, pos) = match non_neg with
                | SIBot -> (SIBot, SIBot)
                | SIntv (l,r) ->
                    let (zero, l') =
                        if I.signed_compare l 0L = 0 then
                            (from_int64 0L, I.add l 1L)
                        else
                            (SIBot, l)
                    in
                    if I.signed_compare 0L r < 0 then
                        (zero, intv l' r)
                    else (zero, SIBot)
            in
            (smi, neg', zero, pos)
    
    let to_string (t: t): string = match t with
        | SIBot -> "[]"
        | SIntv (l,r) -> if t = top_repr then "T" else Printf.sprintf "[%#Li,%#Li]" (I.extend_msb l) (I.extend_msb r)
    
    let is_bot (t: t): bool =
        match t with
        | SIBot -> true
        | _ -> false

    let join (t1: t) (t2: t): t =
        match t1, t2 with
        | SIBot, _ -> t2
        | _, SIBot -> t1
        | SIntv (l1,r1), SIntv(l2,r2) ->
            SIntv (I.signed_min l1 l2, I.signed_max r1 r2)
    
    let meet (t1: t) (t2: t): t =
        match t1, t2 with
        | SIBot, _ -> SIBot
        | _, SIBot -> SIBot
        | SIntv (l1,r1), SIntv(l2,r2) ->
            let l = I.signed_max l1 l2 in
            let r = I.signed_min r1 r2 in
            if I.signed_compare l r > 0 then SIBot
            else SIntv (l,r)
    
    let leq (t1: t) (t2: t): bool =
        match t1, t2 with
        | SIBot, _ -> true
        | _, SIBot -> false
        | SIntv(l1,r1), SIntv(l2,r2) ->
            I.signed_compare l2 l1 <= 0 && I.signed_compare r1 r2 <= 0
    
    (** forward operations *)

    (*
    100000 -> 0111111 : min_int -> max_int
    100001 -> 0111110 : min_int + 1 -> max_int - 1
    000000 -> 1111111 : 0 -> -1
    000001 -> 1111110 : 1 -> -2
    011111 -> 1000000 : max_int -> min_int
    *)
    let forward_not (t: t): t =
        match t with
        | SIBot -> bot_repr
        | SIntv (l,r) -> intv (I.lognot r) (I.lognot l)
    
    let forward_neg (t: t): t =
        match t with
        | SIBot -> bot_repr
        | SIntv (l,r) ->
            if l = lbound_min then
                if r = lbound_min then
                    intv lbound_min lbound_min
                else top_repr
            else
                let l' = I.neg r in
                let r' = if l = I.signed_min_int then I.signed_max_int else I.neg l in
                if I.signed_compare l' r' <= 0 then intv l' r'
                else failwith_f "forward_neg %s -> invalid result (%Ld, %Ld)" (to_string t) l' r'
    
    let forward_add (t1: t) (t2: t): t =
        match t1, t2 with
        | SIBot, _ | _, SIBot -> bot_repr
        | SIntv (l1,r1), SIntv (l2,r2) ->
            let l = I.add l1 l2 in
            let r = I.add r1 r2 in
            let overflow =
                (I.signed_compare l1 0L >= 0 && I.signed_compare l2 0L >= 0 && I.signed_compare l 0L < 0) ||
                (I.signed_compare l1 0L < 0 && I.signed_compare l2 0L <  0 && I.signed_compare l 0L >=  0) ||
                (I.signed_compare r1 0L >= 0 && I.signed_compare r2 0L >= 0 && I.signed_compare r 0L < 0) ||
                (I.signed_compare r1 0L < 0 && I.signed_compare r2 0L < 0 && I.signed_compare r 0L >= 0)
            in
            if overflow then
                top_repr
            else
            intv l r

    let forward_sub (t1: t) (t2: t): t =
        match t1, t2 with
        | SIBot, _ | _, SIBot -> bot_repr
        | SIntv (l1,r1), SIntv (l2,r2) ->
            let l = I.sub l1 r2 in
            let r = I.sub r1 l2 in
            let overflow =
                (I.signed_compare l1 0L >= 0 && I.signed_compare r2 0L < 0 && I.signed_compare l 0L < 0) ||
                (I.signed_compare l1 0L < 0 && I.signed_compare r2 0L >= 0 && I.signed_compare l 0L >= 0) ||
                (I.signed_compare r1 0L >= 0 && I.signed_compare l2 0L < 0 && I.signed_compare r 0L < 0) ||
                (I.signed_compare r1 0L < 0 && I.signed_compare l2 0L >= 0 && I.signed_compare r 0L >= 0)
            in
            if overflow then
                top_repr
            else
                intv l r
    
    let forward_mul (t1: t) (t2: t): t =
        match t1, t2 with
        | SIBot, _ | _, SIBot -> bot_repr
        | SIntv (l1,r1), SIntv (l2,r2) ->
            let i1 = I.mul l1 l2 in
            let i2 = I.mul l1 r2 in
            let i3 = I.mul r1 l2 in
            let i4 = I.mul r1 r2 in
            let overflow =
                (l1 <> 0L && (I.signed_div i1 l1 <> l2 ||
                I.signed_div i2 l1 <> r2)) ||
                (r1 <> 0L && (I.signed_div i3 r1 <> l2 ||
                I.signed_div i4 r1 <> r2))
            in
            if overflow then
                top_repr
            else
                intv (BatList.reduce I.signed_min [i1;i2;i3;i4]) (BatList.reduce I.signed_max [i1;i2;i3;i4])
    
    let div_aux (t1: t) (t2: t): t =
        (* warning!! : t1, t2 must be in positive range (except for I.signed_min_int) *)
        match t1, t2 with
        | SIBot, _ | _, SIBot -> bot_repr
        | SIntv (l1,r1), SIntv (l2,r2) ->
            if r2 = 0L then (* l2 = 0L, too -> definitely divide by zero -> undefined semantics *)
                bot_repr
            else
                if r1 = I.signed_min_int then (* l1 = r1 = I.signed_min_int *)
                    if r2 = I.signed_min_int then (* l2 = r2 = I.signed_min_int *)
                        intv 1L 1L
                    else
                        let l = I.unsigned_div I.signed_min_int r2 in
                        let r = I.unsigned_div I.signed_min_int l2 in
                        if r = I.signed_min_int then
                            if l = I.signed_min_int then
                                intv l r
                            else
                                top_repr
                        else if I.signed_compare l r <= 0 then
                            intv l r
                        else
                            failwith_f "div_aux: unreachable with intv %Ld %Ld from div %s %s" l r (to_string t1) (to_string t2)
                else if r2 = I.signed_min_int then
                    intv 0L 0L
                else if t1 = top_repr then
                    if leq (intv 1L 1L) t2 then
                        (* any value can be here *)
                        top_repr
                    else
                        (* 1 is not in t2 => can do something*)
                        let l = 0L in
                        let r = I.unsigned_div I.signed_min_int r2 in
                        intv l r
                else
                    let l = if r2 = 0L then l1 else I.unsigned_div l1 r2 in
                    let r = if l2 = 0L then r1 else I.unsigned_div r1 l2 in
                    if r = I.signed_min_int then
                        if l = I.signed_min_int then
                            intv l r
                        else
                            top_repr
                    else if I.signed_compare l r <= 0 then
                        intv l r
                    else begin
                        failwith_f "div_aux: unreachable with intv %Ld %Ld from div %s %s" l r (to_string t1) (to_string t2)
                    end

    let forward_div (t1: t) (t2: t): t =
        match t1, t2 with
        | SIBot, _ | _, SIBot -> bot_repr
        | SIntv _, SIntv _ ->
            let (min1, neg1, zero1, pos1) = sign_split_more t1 in
            let (min2, neg2, _, pos2) = sign_split_more t2 in
            let non_neg1 = join zero1 pos1 in
            let abs_neg1 = forward_neg neg1 in
            let abs_neg2 = forward_neg neg2 in
            let pp =
                div_aux non_neg1 pos2
            in
            let np =
                let p_normal = div_aux abs_neg1 pos2 in
                let p_min = div_aux min1 pos2 in
                (join (forward_neg p_normal) (forward_neg p_min))
            in
            let pn =
                let p_normal = div_aux non_neg1 abs_neg2 in
                let p_min = div_aux non_neg1 min2 in
                (join (forward_neg p_normal) (forward_neg p_min))
            in
            let nn =
                let case_nn = div_aux abs_neg1 abs_neg2 in
                let case_nm = div_aux abs_neg1 min2 in
                let case_mn = div_aux min1 abs_neg2 in
                let case_mm = div_aux min1 min2 in
                join case_nn (join case_nm (join case_mn case_mm))
            in
            join pp np |> join pn |> join nn

    let forward_rem (t1: t) (t2: t): t =
        let rem_aux (t1: t) (t2: t): t =
            (* warning!! : t1, t2 must be in positive range (except for Int64.min_int) *)
            match t1, t2 with
            | SIBot, _ | _, SIBot -> bot_repr
            | SIntv (l1,r1), SIntv (l2,r2) ->
                if r2 = 0L then (* l2 = 0L, too *)
                    (* undefined semantics *)
                    bot_repr
                else
                    if r1 = I.signed_min_int then
                        if r2 = I.signed_min_int then
                            intv 0L 0L
                        else
                            intv 0L (I.signed_min (I.sub (I.logical_shift_right I.signed_min_int 1) 1L) (I.sub r2 1L))
                    else if r2 = I.signed_min_int then
                        t1
                    else intv 0L (I.signed_min r1 r2)
        in
        match t1, t2 with
        | SIBot, _ | _, SIBot -> bot_repr
        | SIntv _, SIntv _ ->
            let (neg1, pos1) = sign_split t1 in
            let (neg2, pos2) = sign_split t2 in
            let p_neg1 = forward_neg neg1 in
            let p_neg2 = forward_neg neg2 in
            let pp =
                rem_aux pos1 pos2
            in
            let np =
                let p = rem_aux p_neg1 pos2 in
                forward_neg p
            in
            let pn = rem_aux pos1 p_neg2 in
            let nn = forward_neg (rem_aux p_neg1 p_neg2) in
            join pp np |> join pn |> join nn
end