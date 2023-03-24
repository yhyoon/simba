open Common
open Vocab

(** specialized map with Generator.addr key *)

type 'a addr_map = (int list, 'a) BatMap.t

type 'a t = 'a addr_map

let empty: 'a addr_map = BatMap.empty

let is_pure_empty (m: 'a addr_map): bool = BatMap.is_empty m

let is_empty (m: 'a addr_map): bool = is_pure_empty m

let add (k: int list) (v: 'a) (m: 'a addr_map): 'a addr_map =
    BatMap.add k v m

let find (k: int list) (m: 'a addr_map): 'a =
    BatMap.find k m

let mem (k: int list) (m: 'a addr_map): bool =
    BatMap.mem k m

let remove (k: int list) (m: 'a addr_map): 'a addr_map =
    BatMap.remove k m

let size (m: 'a addr_map): int = BatMap.cardinal m

let keys (m: 'a addr_map): int list BatEnum.t = BatMap.keys m

let values (m: 'a addr_map): 'a BatEnum.t = BatMap.values m