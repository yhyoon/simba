open Common
open Vocab

(** specialized map with Generator.addr key *)

type 'a addr_map =
    | AddrNode of 'a option * 'a addr_map list

type 'a t = 'a addr_map

let empty: 'a addr_map = AddrNode (None, [])

let string_of_addr_map (str: 'a -> string) (m: 'a addr_map): string =
    let rec string_of_map_aux (k: int list) (indent: string) (m: 'a addr_map): string list =
        match m with
        | AddrNode (None, nl) ->
        (indent ^ string_of_list string_of_int k ^ " |/") ::
            (BatList.mapi (fun idx sub -> string_of_map_aux (k@[idx]) (indent ^ " ") sub) nl |> BatList.flatten)
        | AddrNode (Some nv, nl) ->
            (indent ^ string_of_list string_of_int k ^ " |-> " ^ str nv) ::
                (BatList.mapi (fun idx sub -> string_of_map_aux (k@[idx]) (indent ^ " ") sub) nl |> BatList.flatten)
    in
    string_of_list ~first:"" ~sep:"\n" ~last:"" identity (string_of_map_aux [] "" m)

let is_pure_empty (m: 'a addr_map): bool = match m with
    | AddrNode (None, []) -> true
    | _ -> false

let is_empty (m: 'a addr_map): bool = is_pure_empty m

let add (k: int list) (v: 'a) (m: 'a addr_map): 'a addr_map =
    let rec add_aux k m =
        match k, m with
        | [], AddrNode (_, nl) ->
            AddrNode (Some v, nl)
        | h :: t, AddrNode (nv, nl) -> begin
            let nl_len = BatList.length nl in
            if h < nl_len then
                AddrNode (nv, BatList.modify_at h (fun old -> add_aux t old) nl)
            else
                let need_more = h - nl_len in
                AddrNode (nv,
                    nl @
                    BatList.init (need_more + 1)
                        (fun idx ->
                            if idx < need_more then empty
                            else add_aux t empty))
        end
    in
    add_aux k m

let find (k: int list) (m: 'a addr_map): 'a =
    let rec find_aux k m =
        match k, m with
        | [], AddrNode (Some v, _) -> v
        | [], AddrNode (None, _) -> raise Not_found
        | h :: t, AddrNode (_, nl) ->
            if h < BatList.length nl then
                find_aux t (BatList.nth nl h)
            else raise Not_found
    in
    find_aux k m

let mem (k: int list) (m: 'a addr_map): bool =
    let rec mem_aux k m =
        match k, m with
        | [], AddrNode (Some _, _) -> true
        | [], AddrNode (None, _) -> false
        | h :: t, AddrNode (_, nl) ->
            if h < BatList.length nl then
                mem_aux t (BatList.nth nl h)
            else false
    in
    mem_aux k m

let remove (k: int list) (m: 'a addr_map): 'a addr_map =
    let compacted_list (target_idx: int) (new_val: 'a addr_map) (l: 'a addr_map list): 'a addr_map list =
        let rec compacted_aux cur_idx rev_l inserted =
            match rev_l with
            | [] -> begin
                assert (cur_idx = -1);
                []
            end
            | h :: t ->
                let h', inserted' =
                    if cur_idx = target_idx then (new_val, true)
                    else (h, inserted)
                in
                if is_pure_empty h' then
                    compacted_aux (cur_idx - 1) t inserted'
                else
                    if inserted' then
                        BatList.rev (h' :: t)
                    else
                        BatList.modify_at target_idx (fun _ -> new_val) (BatList.rev rev_l)
        in
        compacted_aux (BatList.length l - 1) (BatList.rev l) false
    in
    let rec remove_aux k m =
        match k, m with
        | [], AddrNode (Some _, nl) ->
            (true, AddrNode (None, nl))
        | [], AddrNode (None, _) ->
            (false, m)
        | n :: t, AddrNode (nv, nl) ->
            if n < BatList.length nl then
                let (is_removed, new_nth) = remove_aux t (BatList.nth nl n) in
                if is_removed then
                    (true, AddrNode (nv, compacted_list n new_nth nl))
                else
                    (false, m)
            else (false, m)
    in
    remove_aux k m |> snd

let size (m: 'a addr_map): int =
    let rec size_aux m =
        match m with
        | AddrNode (Some _, nl) ->
            BatList.fold_left (fun acc sub -> acc + size_aux sub) 1 nl
        | AddrNode (None, nl) ->
            BatList.fold_left (fun acc sub -> acc + size_aux sub) 0 nl
    in
    size_aux m

let keys (m: 'a addr_map): int list BatEnum.t =
    let bound_key_list =
        let rec collect addr m acc =
            match m with
            | AddrNode (Some _, nl) ->
                BatList.fold_lefti (fun acc' i n -> collect (addr@[i]) n acc') (addr :: acc) nl
            | AddrNode (None, nl) ->
                BatList.fold_lefti (fun acc' i n -> collect (addr@[i]) n acc') acc nl
        in
        collect [] m []
    in
    BatList.enum (BatList.rev bound_key_list)

let values (m: 'a addr_map): 'a BatEnum.t =
    let bound_value_list =
        let rec collect m acc =
            match m with
            | AddrNode (Some nv, nl) ->
                BatList.fold_left (fun acc' n -> collect n acc') (nv :: acc) nl
            | AddrNode (None, nl) ->
                BatList.fold_left (fun acc' n -> collect n acc') acc nl
        in
        collect m []
    in
    BatList.enum (BatList.rev bound_value_list)
