open Common
open Vocab

type bv_un_op =
    | BV_NOT | BV_NEG

type bv_bin_op =
    | BV_AND | BV_OR | BV_XOR
    | BV_ADD | BV_SUB | BV_MUL
    | BV_UDIV | BV_UREM
    | BV_LSHR | BV_ASHR | BV_SHL
    | BV_SDIV | BV_SREM

type bv_cmp_op =
    | BV_ULE | BV_ULT
    | BV_SLE | BV_SLT

type bv_op =
    | BV_BIN_OP of bv_bin_op
    | BV_CMP_OP of bv_cmp_op
    | BV_UN_OP of bv_un_op

type tri_op =
    | ITE

type bool_bin_op =
    | B_AND | B_OR | B_XOR | B_IMPLIES

type bool_un_op =
    | B_NOT

type bool_op =
    | B_BIN_OP of bool_bin_op
    | B_UN_OP of bool_un_op

type int_op =
    | I_ADD
    | I_SUB
    | I_MUL
    | I_DIV
    | I_MOD

type cmp_op =
    | CMP_EQ | CMP_LT | CMP_LE | CMP_GT | CMP_GE

type op =
    | BV_OP of bv_op
    | BOOL_OP of bool_op
    | INT_OP of int_op
    | TRI_OP of tri_op
    | GEN_CMP_OP of cmp_op
    | GENERAL_FUNC of string

let bv_bin_table: (string * bv_bin_op) BatSeq.t = BatList.to_seq [
    ("bvand", BV_AND);
    ("bvor", BV_OR);
    ("bvxor", BV_XOR);
    ("bvadd", BV_ADD);
    ("bvsub", BV_SUB);
    ("bvmul", BV_MUL);
    ("bvudiv", BV_UDIV);
    ("bvurem", BV_UREM);
    ("bvlshr", BV_LSHR);
    ("bvashr", BV_ASHR);
    ("bvshl", BV_SHL);
    ("bvsdiv", BV_SDIV);
    ("bvsrem", BV_SREM)
]

let bv_cmp_table: (string * bv_cmp_op) BatSeq.t = BatList.to_seq [
    ("bvule", BV_ULE);
    ("bvult", BV_ULT);
    ("bvsle", BV_SLE);
    ("bvslt", BV_SLT)
]

let bv_un_table: (string * bv_un_op) BatSeq.t = BatList.to_seq [
    ("bvnot", BV_NOT);
    ("bvneg", BV_NEG);
]

let bool_un_table: (string * bool_un_op) BatSeq.t = BatList.to_seq [
    ("not", B_NOT);
]

let bool_bin_table: (string * bool_bin_op) BatSeq.t = BatList.to_seq [
    ("and", B_AND);
    ("or", B_OR);
    ("xor", B_XOR);
    ("=>", B_IMPLIES);
]

let cmp_table: (string * cmp_op) BatSeq.t = BatList.to_seq [
    ("=", CMP_EQ);
    ("<", CMP_LT);
    (">", CMP_GT);
    ("<=", CMP_LE);
    (">=", CMP_GE);
]

let bv_table: (string * bv_op) BatSeq.t =
    BatSeq.append
        (bv_bin_table |> (BatSeq.map (fun (s,o) -> (s, BV_BIN_OP o))))
        (BatSeq.append
            (bv_un_table |> (BatSeq.map (fun (s,o) -> (s, BV_UN_OP o))))
            (bv_cmp_table |> (BatSeq.map (fun (s,o) -> (s, BV_CMP_OP o))))
        )

let tri_table: (string * tri_op) BatSeq.t = BatList.to_seq [
    ("ite", ITE)
]

let bool_table: (string * bool_op) BatSeq.t =
    BatSeq.append
        (bool_bin_table |> (BatSeq.map (fun (s,o) -> (s, B_BIN_OP o))))
        (bool_un_table  |> (BatSeq.map (fun (s,o) -> (s, B_UN_OP o))))

let int_table: (string * int_op) BatSeq.t = BatList.to_seq [
    ("+", I_ADD);
    ("-", I_SUB);
    ("*", I_MUL);
    ("/", I_DIV);
    ("%", I_MOD);
]

let all_table: (string * op) BatSeq.t =
    (bv_table |> BatSeq.map (fun (s,o) -> (s, BV_OP o)))
    |> BatSeq.append (bool_table |> BatSeq.map (fun (s,o) -> (s, BOOL_OP o)))
    |> BatSeq.append (int_table |> BatSeq.map (fun (s,o) -> (s, INT_OP o)))
    |> BatSeq.append (tri_table |> BatSeq.map (fun (s,o) -> (s, TRI_OP o)))
    |> BatSeq.append (cmp_table |> BatSeq.map (fun (s,o) -> (s, GEN_CMP_OP o)))

let bv_bin_map: (string, bv_bin_op) BatMap.t =
    bv_bin_table |> BatMap.of_seq

let bv_un_map: (string, bv_un_op) BatMap.t =
    bv_un_table |> BatMap.of_seq

let bv_map: (string, bv_op) BatMap.t =
    BatMap.of_seq bv_table

let tri_map: (string, tri_op) BatMap.t =
    BatMap.of_seq tri_table

let bool_bin_map: (string, bool_bin_op) BatMap.t =
    BatMap.of_seq bool_bin_table

let bool_un_map: (string, bool_un_op) BatMap.t =
    BatMap.of_seq bool_un_table

let bool_map: (string, bool_op) BatMap.t =
    BatMap.of_seq bool_table

let int_map: (string, int_op) BatMap.t =
    BatMap.of_seq int_table

let all_map: (string, op) BatMap.t =
    BatMap.of_seq all_table

let rev_all_map: (op, string) BatMap.t =
    BatMap.of_seq (BatSeq.map (fun (a,b) -> (b,a)) all_table)

(** raise Not_found if unknown id is passed *)
let string_to_bv_op (id: string): bv_op = BatMap.find id bv_map

let string_to_op (id: string): op =
    try BatMap.find id all_map
    with Not_found -> GENERAL_FUNC id

let op_to_string (op: op): string =
    try BatMap.find op rev_all_map
    with Not_found -> begin
        match op with
        | GENERAL_FUNC s -> s
        | _ -> failwith "op_to_string: not_in_table"
    end

let comm_bv_bin_op: bv_bin_op BatSet.t =
    [BV_AND; BV_OR; BV_XOR; BV_ADD; BV_MUL] |> BatSet.of_list

let comm_bool_bin_op: bool_bin_op BatSet.t =
    [B_AND; B_OR; B_XOR] |> BatSet.of_list

let comm_int_op: op BatSet.t =
    [INT_OP I_ADD; INT_OP I_MUL] |> BatSet.of_list

let comm_all_op: op BatSet.t =
    comm_int_op
    |> BatSet.union (BatSet.map (fun boolbin -> BOOL_OP (B_BIN_OP boolbin)) comm_bool_bin_op) 
    |> BatSet.union (BatSet.map (fun bvbin -> BV_OP (BV_BIN_OP bvbin)) comm_bv_bin_op)
    |> BatSet.add (GEN_CMP_OP CMP_EQ)

let is_commutative_bv_bin_op (bo: bv_bin_op): bool = BatSet.mem bo comm_bv_bin_op

let is_commutative_bool_bin_op (bo: bool_bin_op): bool = BatSet.mem bo comm_bool_bin_op

let is_commutative_op (op: op): bool = BatSet.mem op comm_all_op

let is_str_op (op: op): bool = match op with
    | GENERAL_FUNC op_str ->
        (BatString.starts_with op_str "str.") ||
            (BatString.ends_with op_str ".str")
    | _ -> false
