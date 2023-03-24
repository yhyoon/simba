open Common
open Vocab
open Int64Util
open SynthLang
open BitVecCommon

exception UInvalid_boundary of int * int64 * int64

let _ = Printexc.register_printer (fun exn ->
        match exn with
        | UInvalid_boundary(b,l,r) ->
            Some(Printf.sprintf "Unsigned_invalid_boundary(%Lx,%Lx) in %d bits" l r b)
        | _ -> None
    )

let invalid_boundary (bit_length: int) (lb: int64) (rb: int64): 'a =
    raise (UInvalid_boundary (bit_length, lb, rb))

type t = UIBot | UIntv of int64 * int64

module Make(I: MaskedInt64Type) = struct
    let lbound_min: int64 = 0L
    let rbound_max: int64 = I.minus_one

    let bot_repr: t = UIBot
    let top_repr: t = UIntv (0L, I.minus_one)

    let from_int64 (i: int64): t =
        UIntv(i, i)
    
    let zero: t =
        UIntv(0L, 0L)

    let gamma_size_constraint (max_size: int) (t: t): Exprs.const BatSet.t option =
        match t with
        | UIBot -> Some BatSet.empty
        | UIntv (l, u) ->
            if t = top_repr then None
            else
                let width = I.add (I.sub u l) 1L in
                if Int64.unsigned_compare width (Int64.of_int max_size) <= 0 then
                    let rec worker c s =
                        let cmp = I.unsigned_compare c u in
                        if cmp < 0 then
                            worker (I.add c 1L) (BatSet.add (Exprs.CBV (I.bit_length, c)) s)
                        else if cmp = 0 then
                            BatSet.add (Exprs.CBV (I.bit_length, c)) s
                        else s
                    in
                    Some(worker l BatSet.empty)
                else None
    
    let gamma_if_singleton (t: t): Exprs.const option =
        match t with
        | UIBot -> None
        | UIntv (lb,rb) -> if lb = rb then Some (Exprs.CBV (I.bit_length, lb)) else None

    let sign_split (t: t): t * t =
        match t with
        | UIBot -> UIBot, UIBot
        | UIntv (l, u) ->
            if I.unsigned_compare u I.signed_min_int < 0 then (* pos only *)
                UIBot, t
            else if I.unsigned_compare I.signed_min_int l <= 0 then (* neg only *)
                t, UIBot
            else (* both *)
                UIntv (I.signed_min_int, u), UIntv (l, I.signed_max_int)


    let intv (lb: int64) (rb: int64): t =
        if I.unsigned_compare lb rb > 0 then invalid_boundary I.bit_length lb rb
        else UIntv (lb, rb)

    let to_string (t: t): string = match t with
        | UIBot -> "[]"
        | UIntv (l,r) -> if t = top_repr then "T" else Printf.sprintf "[0x%Lx,0x%Lx]" l r

    let is_bot (t: t): bool =
        match t with
        | UIBot -> true
        | _ -> false
    
    let join (t1: t) (t2: t): t =
        match t1, t2 with
        | UIBot, _ -> t2
        | _, UIBot -> t1
        | UIntv (l1,r1), UIntv(l2,r2) ->
            let l = 
                if I.unsigned_compare l1 l2 <= 0 then l1
                else l2
            in
            let r =
                if I.unsigned_compare r1 r2 <= 0 then r2
                else r1
            in
            UIntv (l,r)

    let meet (t1: t) (t2: t): t =
        match t1, t2 with
        | UIBot, _ -> UIBot
        | _, UIBot -> UIBot
        | UIntv (l1,r1), UIntv(l2,r2) ->
            let l = I.unsigned_max l1 l2 in
            let r = I.unsigned_min r1 r2 in
            if I.unsigned_compare l r > 0 then UIBot
            else UIntv (l,r)

    let leq (t1: t) (t2: t): bool =
        match t1, t2 with
        | UIBot, _ -> true
        | _, UIBot -> false
        | UIntv(l1,r1), UIntv(l2,r2) ->
            I.unsigned_compare l2 l1 <= 0 && I.unsigned_compare r1 r2 <= 0

    (** forward operations *)

    (*
    000000 -> 1111111 : 0 -> max
    011111 -> 1000000
    100000 -> 0111111
    111111 -> 0000000 : max -> 0
    *)
    let forward_not (t: t): t =
        match t with
        | UIBot -> bot_repr
        | UIntv (l, r) -> intv (I.lognot r) (I.lognot l)    

    let forward_neg (t: t): t =
        match t with
        | UIBot -> bot_repr
        | UIntv (l, r) ->
            (* 00....00 -> 0000...00 *)
            (* 00....01 -> 1111...11 *)
            (* 00....10 -> 1111...10 *)
            (* 10000..1 -> 0111...11 *)
            (* 10000..0 -> 1000....0 *)
            (* 0111...1 -> 1000....1 *)
            if l = 0L then
                if r = 0L then intv 0L 0L
                else top_repr
            else
                let l' = I.neg r in
                let r' = I.neg l in
                if I.unsigned_compare l' r' <= 0 then intv l' r'
                else top_repr

    let forward_add (t1: t) (t2: t): t =
        match t1, t2 with
        | UIBot, _ | _, UIBot -> bot_repr
        | UIntv (l1,r1), UIntv (l2,r2) ->
            let l = I.add l1 l2 in
            let r = I.add r1 r2 in
            let overflow =
                I.unsigned_compare l l1 < 0 || I.unsigned_compare l l2 < 0 ||
                I.unsigned_compare r r1 < 0 || I.unsigned_compare r r2 < 0
            in
            if overflow then
                top_repr
            else
                intv l r

    let forward_sub (t1: t) (t2: t): t =
        match t1, t2 with
        | UIBot, _ | _, UIBot -> bot_repr
        | UIntv (l1,r1), UIntv (l2,r2) ->
            if I.unsigned_compare l1 r2 < 0 || I.unsigned_compare r1 l2 < 0 then
                top_repr
            else
                let l = I.sub l1 r2 in
                let r = I.sub r1 l2 in
                intv l r
    
    let forward_mul (t1: t) (t2: t): t =
        match t1, t2 with
        | UIBot, _ | _, UIBot -> bot_repr
        | UIntv (l1,r1), UIntv (l2,r2) ->
            let i1 = I.mul l1 l2 in
            let i2 = I.mul l1 r2 in
            let i3 = I.mul r1 l2 in
            let i4 = I.mul r1 r2 in
            let overflow =
                (l1 <> 0L && (I.unsigned_div i1 l1 <> l2 ||
                I.unsigned_div i2 l1 <> r2)) ||
                (r1 <> 0L && (I.unsigned_div i3 r1 <> l2 ||
                I.unsigned_div i4 r1 <> r2))
            in
            if overflow then
                top_repr
            else
                let l' = BatList.reduce I.unsigned_min [i1;i2;i3;i4] in
                let r' = BatList.reduce I.unsigned_max [i1;i2;i3;i4] in
                let _ =
                    if l' = I.minus_one && r' = 0L then begin
                        Logger.g_error_f "bad in mul(%s, %s) - boundary candidates =" (to_string t1) (to_string t2);
                        BatList.iter (fun i -> Logger.g_debug_f "  %Ld" i) [i1;i2;i3;i4]
                    end
                in
                intv l' r'

    let forward_div (t1: t) (t2: t): t =
        match t1, t2 with
        | UIBot, _ | _, UIBot -> bot_repr
        | UIntv (l1,r1), UIntv (l2,r2) ->
            if r2 = 0L then (* l2 = 0L, too -> definitely divide by zero -> undefined semantics *)
                bot_repr
            else
                let l = if r2 = 0L then l1 else I.unsigned_div l1 r2 in
                let r = if l2 = 0L then r1 else I.unsigned_div r1 l2 in
                intv l r

    let forward_rem (t1: t) (t2: t): t =
        match t1, t2 with
        | UIBot, _ | _, UIBot -> bot_repr
        | UIntv (l1,r1), UIntv (l2,r2) ->
            if r2 = 0L then
                bot_repr
            else
                intv 0L (I.unsigned_min r1 r2)
end