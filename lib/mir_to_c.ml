(* filepath: /workspaces/borrow_checker/lib/mir_to_c.ml *)

open Minimir
open Type
open Ast

(* Helper function to convert a type to C syntax *)
let rec typ_to_c typ =
  match typ with
  | Tint -> "int"
  | Tbool -> "bool"
  | Tunit -> "void"
  | Tborrow (_, Mut, t) -> (typ_to_c t)^ "*"
  | Tborrow (_, NotMut, t) -> "const"^(typ_to_c t)^"*"
  | Tstruct (sid, _) -> Printf.sprintf "struct %s" sid
  | _ -> failwith "Unsupported type"

let local_to_c loc = 
  match loc with
  | Lparam s -> s
  | Lvar n -> Printf.sprintf "lvar_%d" n
  | Lret -> "ret"
in
let rec place_to_c pl =
  match pl with
  | PlLocal l -> local_to_c l
  | PlField (pl, field) -> Printf.sprintf "%s.%s" (place_to_c pl) field
  | PlDeref pl -> Printf.sprintf "*%s" (place_to_c pl)

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
      Printf.sprintf "// Deinitialize %s;" l
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
    (fun name typ ->
      Buffer.add_string buf (Printf.sprintf "%s %s;\n" (typ_to_c typ) name))
    mir.mlocals;

  (* Generate instructions *)
  Array.iteri
    (fun lbl (instr, _) ->
      Buffer.add_string buf (Printf.sprintf "label_%d:\n" lbl);
      Buffer.add_string buf (Printf.sprintf "  %s\n" (instr_to_c instr)))
    mir.minstrs;

  Buffer.contents buf