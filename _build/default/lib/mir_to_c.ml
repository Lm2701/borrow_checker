(* filepath: /workspaces/borrow_checker/lib/mir_to_c.ml *)

open Minimir
open Ast

(* Helper function to convert a type to C syntax *)
let rec typ_to_c typ =
  match typ with
  | Ti32 -> "int"
  | Tbool -> "bool"
  | Tunit -> "void"
  | Tborrow (_, Mut, t) -> (typ_to_c t)^ "*"
  | Tborrow (_, NotMut, t) -> "const"^(typ_to_c t)^"*"
  | Tstruct (sid, _) -> Printf.sprintf "struct %s" sid

let local_to_c loc = 
  match loc with
  | Lparam s -> s
  | Lvar n -> Printf.sprintf "lvar_%d" n
  | Lret -> "ret"

let rec place_to_c pl =
  match pl with
  | PlLocal l -> local_to_c l
  | PlField (pl, field) -> Printf.sprintf "%s.%s" (place_to_c pl) field
  | PlDeref pl -> Printf.sprintf "*%s" (place_to_c pl)

let string_of_const c =
  match c with
    | Ci32 s -> s
    | Cbool true -> "true"
    | Cbool false -> "false"

let string_of_binop op = 
  match op with
  | Badd -> "+"
  | Bsub -> "-"
  | Bmul -> "*" 
  | Bdiv -> "\\" 
  | Bmod -> "mod"
  | Beqeq -> "=="
  | Bneq -> "!=" 
  | Blt -> "<" 
  | Ble -> "<="
  | Bgt -> ">"
  | Bge -> ">="
let string_of_unop op = 
  match op with
  | Uneg -> ""
  | Unot -> "not"
(* Convert a single MIR instruction to C syntax *)
let instr_to_c instr =
  match instr with
  | Iassign (pl, RVconst c, _) ->
      Printf.sprintf "%s = %s;" (place_to_c pl) (string_of_const c)
  | Iassign (pl, RVplace pl2, _) ->
      Printf.sprintf "%s = %s;" (place_to_c pl) (place_to_c pl2)
  | Iassign (pl, RVbinop (op, pl1, pl2), _) ->
      Printf.sprintf "%s = %s %s %s;" (place_to_c pl) (place_to_c pl1) (string_of_binop op) (place_to_c pl2)
  | Iassign (pl, RVunop (op, pl1), _) ->
      Printf.sprintf "%s = %s%s;" (place_to_c pl) (string_of_unop op) (place_to_c pl1)
  | Iassign (pl, RVmake (sid, pls), _) ->
      let fields = String.concat ", " (List.map place_to_c pls) in
      Printf.sprintf "%s = (%s){%s};" (place_to_c pl) sid fields
  | Icall (fn, args, retpl, _) ->
      let args_str = String.concat ", " (List.map place_to_c args) in
      Printf.sprintf "%s = %s(%s);" (place_to_c retpl) fn args_str
  | Ideinit (l, _) ->
      Printf.sprintf "// Deinitialize %s;" (local_to_c l)
  | Igoto lbl ->
      Printf.sprintf "goto label_%d;" lbl
  | Ireturn ->
      "return ret;"
  | _ -> failwith "Unsupported instruction"

(* Convert the entire MIR to C syntax *)
let mir_to_c mir =
  let buf = Buffer.create 1024 in
  (* Generate variable declarations *)
  Hashtbl.iter
    (fun loc typ ->
      Buffer.add_string buf (Printf.sprintf "%s %s;\n" (typ_to_c typ) (local_to_c loc)))
    mir.mlocals;

  (* Generate instructions *)
  Array.iteri
    (fun lbl (instr, _) ->
      Buffer.add_string buf (Printf.sprintf "label_%d:\n" lbl);
      Buffer.add_string buf (Printf.sprintf "  %s\n" (instr_to_c instr)))
    mir.minstrs;

  Buffer.contents buf