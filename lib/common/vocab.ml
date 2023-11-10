let identity: 'a -> 'a = BatPervasives.identity
let flip: ('a -> 'b -> 'c) -> 'b -> 'a -> 'c = BatPervasives.flip
let cond (c: bool) (f: 'a -> 'b) (g: 'a -> 'b) (x: 'a): 'b = if c then f x else g x
let opt (c: bool) (f: 'a -> 'a) (x: 'a): 'a = if c then f x else x
let tuple (x: 'a): 'a * 'a = (x, x)
let map3 (f: 'a -> 'b -> 'c -> 'd) (l1: 'a list) (l2: 'b list) (l3: 'c list): 'd list =
	  (* try *)
	  let lst = List.combine l1 (List.combine l2 l3) in 
	  List.map (fun (e1, (e2, e3)) -> f e1 e2 e3) lst
	  (* with _ ->                                                                                        *)
	  (* 	failwith (Printf.sprintf "map3: %d %d %d" (List.length l1) (List.length l2) (List.length l3))  *)
let map_fst (f: 'a -> 'c) ((a,b): 'a * 'b): 'c * 'b =
    (f a, b)

let map_snd (f: 'b -> 'c) ((a,b): 'a * 'b): 'a * 'c =
    (a, f b)

(* formatted fail message exception *)
let failwith_f fmt = Printf.ksprintf failwith fmt

let failcond_f failcond fmt =
    if failcond then
        Printf.ksprintf failwith fmt
    else
        Printf.ksprintf ignore fmt

(* use array as immutable-like *)
(** append element to copied array *)
let arr_copy_add (e: 'a) (arr: 'a array): 'a array =
    let l = BatArray.length arr in
    BatArray.init (l + 1) (fun idx -> if idx < l then arr.(idx) else e)

(**
arr_copy_set idx new_elem arr -> updated_arr.

If idx < len(arr) and arr.(idx) <> e (not same obj in memory), copy arr and set arr.(idx) = e and return copied array.
Otherwise, do nothing and just return arr
    *)
let arr_copy_set (idx: int) (e: 'a) (arr: 'a array): 'a array =
    if idx < BatArray.length arr && arr.(idx) != e then
        BatArray.init (BatArray.length arr) (fun i -> if i = idx then e else arr.(i))
    else
        arr

(**
arr_copy_update idx elem_updater arr -> updated_arr.

If idx < len(arr) and arr.(idx) <> f e (not same obj in memory), copy arr and set copied_arr.(idx) = f e and return copied array.
Otherwise, do nothing and just return arr
*)
let arr_copy_update (idx: int) (f: 'a -> 'a) (arr: 'a array): 'a array =
    if idx < BatArray.length arr then
        let e' = f (arr.(idx)) in
        if arr.(idx) != e' then
            BatArray.init (BatArray.length arr) (fun i -> if i = idx then e' else arr.(i))
        else
            arr
    else
        arr

(**
arr_copy_set_extend idx e default arr -> updated_arr.

If idx < len(arr) and arr.(idx) <> e (not same obj in memory), copy arr and set copied_arr.(idx) = e and return copied array.
If idx >= len(arr), copy arr with extended length to contain idx with default value and set arr.(idx) = e and return copied array.
Otherwise, do nothing and just return arr
    *)
let arr_copy_set_extend (idx: int) (e: 'a) (default: 'a) (arr: 'a array): 'a array =
    if idx >= BatArray.length arr then
        BatArray.init (idx + 1) (fun i -> if i = idx then e else if i < BatArray.length arr then arr.(i) else default)
    else if arr.(idx) != e then
        BatArray.init (BatArray.length arr) (fun i -> if i = idx then e else arr.(i))
    else
        arr

(**
arr_copy_set_extend idx elem_updater default arr -> updated_arr.

If idx < len(arr) and arr.(idx) <> f e (not same obj in memory), copy arr and set copied_arr.(idx) = f e and return copied array.
If idx >= len(arr), copy arr with extended length to contain idx with default value and set copied_arr.(idx) = f default and return copied array.
Otherwise, do nothing and just return arr
    *)
let arr_copy_update_extend (idx: int) (f: 'a -> 'a) (default: 'a) (arr: 'a array): 'a array =
    let e' =
        if idx < BatArray.length arr then
            f (arr.(idx))
        else
            f default
    in
    if idx >= BatArray.length arr then
        BatArray.init (idx + 1) (fun i ->
            if i = idx then e' else if i < BatArray.length arr then arr.(i) else default
        )
    else if arr.(idx) != e' then
        BatArray.init (BatArray.length arr) (fun i -> if i = idx then e' else arr.(i))
    else
        arr 

let read_lines (filename: string) : string list =
    let ic = open_in filename in
    let try_read () =
        try Some (input_line ic) with End_of_file -> None in
    let rec loop acc = match try_read () with
        | Some s -> loop (s :: acc)
        | None -> close_in ic; List.rev acc in
    loop []

let write_lines (lines: string list) (filename: string): unit = 
    let oc = open_out filename in
    List.iter (fun line -> Printf.fprintf oc "%s\n" line) lines; 
    close_out oc

let set_map (f: 'a -> 'b) (set: 'a BatSet.t): 'b BatSet.t = 
	  BatSet.fold (fun elt acc -> BatSet.add (f elt) acc) set BatSet.empty 

let list2set (lst: 'a list): 'a BatSet.t = 
	  List.fold_left (fun set elt -> BatSet.add elt set) BatSet.empty lst 

let zip_with_index (lst: 'a list): (int * 'a) list =
    BatList.combine (BatList.init (BatList.length lst) BatPervasives.identity) lst

let iter_with_index (lst: 'a list) (f: int -> 'a -> unit): unit =
    let idx = ref 0 in
    BatList.iter (fun e -> f !idx e; incr idx) lst

let insert_to_sorted_set (l: 'a list) (new_elem: 'a) (cmp: 'a -> 'a -> int): 'a list =
    let rec insert_aux (passed_rev: 'a list) (remain: 'a list) : 'a list =
        match remain with
        | [] -> BatList.rev (new_elem :: passed_rev)
        | h :: tail ->
            let c = cmp new_elem h in
            if c < 0 then BatList.rev_append passed_rev (new_elem :: remain)
            else if c = 0 then BatList.rev_append passed_rev remain
            else insert_aux (h :: passed_rev) tail
    in
    insert_aux [] l

(** assumption: l1 and l2 is sorted and no duplication *)
let intersect_sorted_set ?(cmp: 'a -> 'a -> int = Stdlib.compare) (l1: 'a list) (l2: 'a list): 'a list =
    let rec loop (l1: 'a list) (l2: 'a list) (acc_rev: 'a list): 'a list =
        match l1, l2 with
        | [], _ | _, [] -> BatList.rev acc_rev
        | h1 :: t1, h2 :: t2 ->
            let c = cmp h1 h2 in
            if c < 0 then loop t1 l2 acc_rev
            else if c > 0 then loop l1 t2 acc_rev
            else loop t1 t2 (h1 :: acc_rev)
    in
    loop l1 l2 []

let add_set_map (k: 'a) (v: 'b) (k_vset_map: ('a, 'b BatSet.t) BatMap.t): ('a, 'b BatSet.t) BatMap.t =
	  let new_set =
        try
          BatMap.find k k_vset_map |> BatSet.add v
        with Not_found -> BatSet.singleton v
    in
	  BatMap.add k new_set k_vset_map

let set_flat_option_map (f: 'a -> 'b option) (set: 'a BatSet.t): 'b BatSet.t =
    BatSet.fold (fun e acc -> BatOption.map_default (fun x -> BatSet.add x acc) acc (f e)) set BatSet.empty

let set_flat_map (f: 'a -> 'b BatSet.t) (set: 'a BatSet.t): 'b BatSet.t =
    BatSet.fold (fun e acc -> BatSet.union (f e) acc) set BatSet.empty

let option_or (x: 'a option) (y: 'a option): 'a option =
    match x, y with
    | Some x', _ -> Some x'
    | None, Some y' -> Some y'
    | _, _ -> None

let (|??) (x: 'a option) (y: unit -> 'a option): 'a option =
    match x with
    | Some x' -> Some x'
    | None -> y ()

let (|?!) (x: 'a option) (y: unit -> 'a): 'a =
    match x with
    | Some x' -> x'
    | None -> y ()

let common_prefix ?(is_equal:'a -> 'a -> bool = fun x y -> x = y) (l1: 'a list) (l2: 'a list): 'a list =
    let rec aux l1 l2 acc =
        match l1, l2 with
        | h1 :: t1, h2 :: t2 ->
            if is_equal h1 h2 then
                aux t1 t2 (h1 :: acc)
            else
                BatList.rev acc
        | _ ->
            BatList.rev acc
    in
    aux l1 l2 []

(** This applies [List.fold_left], but the argument type is the same with
    [PSet.fold].  *)
let list_fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
= fun f list init ->
    List.fold_left (flip f) init list

let list_sub_sparse : 'a list -> int list -> 'a list
= fun l ids ->
    let rec aux idx l ids acc =
        match l, ids with
        | [], _ | _, [] -> BatList.rev acc
        | h :: t, id :: ids_tail ->
            if id = idx then
                aux (succ idx) t ids_tail (h :: acc)
            else
                aux (succ idx) t ids acc
    in
    aux 0 l ids []

let link_by_sep sep s acc = if acc = "" then s else acc ^ sep ^ s

let bin_string_of_int ?(min_length: int=0) (i: int): string =
    let rec aux i min_length acc =
        if i = 0 then
            if min_length <= 0 then
                if BatList.is_empty acc then ['0']
                else acc
            else
                aux i (min_length - 1) ('0' :: acc)
        else
            if (i land 1) = 0 then
                aux (i lsr 1) (min_length - 1) ('0' :: acc)
            else
                aux (i lsr 1) (min_length - 1) ('1' :: acc)
    in
    aux i min_length [] |> BatString.of_list

let string_of_list ?(first="[") ?(last="]") ?(sep=";"): ('a -> string) -> ('a list) -> string
= fun string_of_v list ->
    let add_string_of_v v acc = link_by_sep sep (string_of_v v) acc in
    first ^ list_fold add_string_of_v list "" ^ last

let string_of_array ?(first="{") ?(last="}") ?(sep=";"): ('a -> string) -> ('a BatArray.t) -> string
= fun string_of_v arr ->
    let add_string_of_v v acc = link_by_sep sep (string_of_v v) acc in
    first ^ BatArray.fold_right add_string_of_v arr "" ^ last 

let string_of_set ?(first="{") ?(last="}") ?(sep=","): ('a -> string) -> ('a BatSet.t) -> string
= fun string_of_v set ->
    let add_string_of_v v acc = link_by_sep sep (string_of_v v) acc in
    first ^ BatSet.fold add_string_of_v set "" ^ last

let string_of_map ?(first="{") ?(last="}") ?(sep=",\n") ?(indent=""): ('a -> string) -> ('b -> string) -> (('a, 'b) BatMap.t) -> string
= fun string_of_k string_of_v map ->
    let add_string_of_k_v k v acc =
        let str = string_of_k k ^ " -> " ^ string_of_v v in
        link_by_sep (sep^indent) str acc in
    if BatMap.is_empty map then "empty"
    else indent ^ first ^ BatMap.foldi add_string_of_k_v map "" ^ last

let bm_key_set (m: ('a,_) BatMap.t) : 'a BatSet.t = BatMap.foldi (fun k _ s -> BatSet.add k s) m BatSet.empty

let diff_time_float_hms (t_before: float) (t_after: float): (int * int * int) =
    let diff = t_after -. t_before in
    let diff_tm = Unix.gmtime diff in
    let h = (diff_tm.Unix.tm_mday - 1) * 24 + diff_tm.Unix.tm_hour in
    let m = diff_tm.Unix.tm_min in
    let s = diff_tm.Unix.tm_sec in
    (h, m, s)
