(* Once you are done writing the code, remove this directive,
   whose purpose is to disable several warnings. *)
[@@@warning "-26-27"]

open Type
open Minimir
open Active_borrows


let dummy_loc = (Lexing.dummy_pos, Lexing.dummy_pos)
(* This function computes the set of alive lifetimes at every program point. *)
let compute_lft_sets prog mir : lifetime -> PpSet.t =

  (* The [outlives] variable contains all the outlives relations between the
    lifetime variables of the function. *)
  let outlives = ref LMap.empty in

  (* Helper functions to add outlives constraints. *)
  let add_outlives (l1, l2) = outlives := add_outlives_edge l1 l2 !outlives in
  let unify_lft l1 l2 =
    add_outlives (l1, l2);
    add_outlives (l2, l1)
  in

  (* First, we add in [outlives] the constraints implied by the type of locals. *)
  Hashtbl.iter
    (fun _ typ -> outlives := outlives_union !outlives (implied_outlives prog typ))
    mir.mlocals;

  (* Then, we add the outlives relations needed for the instructions to be safe. *)

  (* TODO: generate these constraints by
       - unifying types that need be equal (note that MiniRust does not support subtyping, that is,
         if a variable x: &'a i32 is used as type &'b i32, then this requires that lifetimes 'a and
         'b are equal),
       - adding constraints required by function calls,
       - generating constraints corresponding to reborrows. More precisely, if we create a borrow
         of a place that dereferences  borrows, then the lifetime of the borrow we
         create should be shorter than the lifetimes of the borrows the place dereference.
         For example, if x: &'a &'b i32, and we create a borrow y = &**x of type &'c i32,
         then 'c should be shorter than 'a and 'b.

    SUGGESTION: use functions [typ_of_place], [fields_types_fresh] and [fn_prototype_fresh].
  *)
  let unify_typs typ1 typ2 =
  let lfts1 = LSet.elements (free_lfts typ1) in
  let lfts2 = LSet.elements (free_lfts typ2) in
  List.iter2 unify_lft lfts1 lfts2
  in
  let unify_typs_places pl1 pl2 =
    let typ1 = typ_of_place prog mir pl1 in
    let typ2 = typ_of_place prog mir pl2 in
    unify_typs typ1 typ2
  in

  let subst_lft subst lft =
    match List.assoc_opt lft subst with
    | Some lft' -> lft'
    | None -> lft
  in
  let rec build_lft_subst param_typ arg_typ subst =
    match param_typ, arg_typ with
    | Tborrow (lft1, mut1, t1), Tborrow (lft2, mut2, t2) ->
      let subst = (lft1, lft2) :: subst in
      build_lft_subst t1 t2 subst
    | Tstruct (_, lfts1), Tstruct (_, lfts2) ->
      List.fold_left2 (fun s l1 l2 -> (l1, l2) :: s) subst lfts1 lfts2
    | _ -> subst
  in
  (* Génération des contraintes *)
  Array.iter
    (fun (instr, _loc) ->
      match instr with
      | Iassign (pl, rv, _) -> (
          (* Unification des types du côté droit et gauche *)
          (match rv with
          | RVplace pl2 -> unify_typs_places pl pl2
          | RVbinop (_, pl1, pl2) ->
              unify_typs_places pl pl1;
              unify_typs_places pl pl2
          | RVunop (_, pl1) -> unify_typs_places pl pl1
          | RVmake (s, pls) -> 
            let field_typs, _ = fields_types_fresh prog s in
              List.iter2
                (fun pl2 field_typ ->
                  let typ2 = typ_of_place prog mir pl2 in
                  unify_typs field_typ typ2)
                pls field_typs;
            let typ = typ_of_place prog mir pl in
            unify_typs typ (snd (fields_types_fresh prog s))
          | RVborrow (_, pl2) ->
              (* Reborrow: le lifetime du borrow doit être plus court que le lifetime du borrow du déréférencement *)
              let typ = typ_of_place prog mir pl2 in
              let rec collect_lifetimes t acc =
                match t with
                | Tborrow (lft, _, t') -> collect_lifetimes t' (lft :: acc)
                | _ -> acc
              in
              let lfts = collect_lifetimes typ [] in
              let typ_l = typ_of_place prog mir pl in
              (match typ_l with
              | Tborrow (lft_new, _, _) ->
                  List.iter (fun lft_old -> add_outlives (lft_old, lft_new)) lfts
              | _ -> ())
          | _ -> ())
        )
      | Icall (fn, args, retpl, _) ->
        let param_typs, ret_typ, outlives_list = fn_prototype_fresh prog fn in
        (* Construction de la substitution *)
        let subst =
          List.fold_left2
            (fun s param_typ argpl ->
              let arg_typ = typ_of_place prog mir argpl in
              build_lft_subst param_typ arg_typ s)
            [] param_typs args
        in
        List.iter2
          (fun argpl param_typ ->
            let arg_typ = typ_of_place prog mir argpl in
            unify_typs param_typ arg_typ)
          args param_typs;
        let ret_typ_actual = typ_of_place prog mir retpl in
        unify_typs ret_typ ret_typ_actual;
        (* Ajout des contraintes outlives avec substitution *)
        (* DEBUG: Affichage de la substitution et des contraintes outlives *)
        (*Printf.printf "Substitution lifetimes:@.";
        List.iter (fun (l1, l2) ->
          Printf.printf "  %s -> %s@." (string_of_lft l1) (string_of_lft l2)
        ) subst;
        Printf.printf "Contraintes outlives (après substitution):@.";
        List.iter (fun (l1, l2) ->
          let l1' = subst_lft subst l1 in
          let l2' = subst_lft subst l2 in
          Printf.printf "  %s : %s@. \n" (string_of_lft l1') (string_of_lft l2')
        ) outlives_list;*)
        List.iter (fun (l1, l2) -> add_outlives (subst_lft subst l1, subst_lft subst l2)) outlives_list
      | Ireturn ->
        (match Hashtbl.find_opt mir.mlocals Lret with
          | Some typ_ret ->
              let typ_val = typ_of_place prog mir (PlLocal Lret) in
              (match typ_ret with
                | Tunit -> ()
                | _ -> unify_typs typ_ret typ_val)
          | None -> ())
      | _ -> ()
    )
    mir.minstrs;


  (* The [living] variable contains constraints of the form "lifetime 'a should be
    alive at program point p". *)
  let living : PpSet.t LMap.t ref = ref LMap.empty in

  (* Helper function to add living constraint. *)
  let add_living pp l =
    living :=
      LMap.update l
        (fun s -> Some (PpSet.add pp (Option.value s ~default:PpSet.empty)))
        !living
  in

  (* Run the live local analysis. See module Live_locals for documentation. *)
  let live_locals = Live_locals.go mir in

  (* TODO: generate living constraints:
     - Add living constraints corresponding to the fact that liftimes appearing free
       in the type of live locals at some program point should be alive at that
       program point.
     - Add living constraints corresponding to the fact that generic lifetime variables
       (those in [mir.mgeneric_lfts]) should be alive during the whole execution of the
       function.
  *)

  Array.iteri
    (fun lbl _instr ->
      let ppoint = PpLocal lbl in
      let locals = live_locals lbl in
      LocSet.iter
        (fun l ->
          match Hashtbl.find_opt mir.mlocals l with
          | Some typ ->
            LSet.iter (fun lft -> add_living ppoint lft) (free_lfts typ)
          | None -> ())
        locals
    )
    mir.minstrs;
  
  Array.iteri
    (fun lbl _instr ->
      let ppoint = PpLocal lbl in
      List.iter (fun lft -> add_living ppoint lft) mir.mgeneric_lfts
    )
    mir.minstrs;
  

  (* If [lft] is a generic lifetime, [lft] is always alive at [PpInCaller lft]. *)
  List.iter (fun lft -> add_living (PpInCaller lft) lft) mir.mgeneric_lfts;

  (* Now, we compute lifetime sets by finding the smallest solution of the constraints, using the
    Fix library. *)
  let module Fix = Fix.Fix.ForType (struct type t = lifetime end) (Fix.Prop.Set (PpSet))
  in
  Fix.lfp (fun lft lft_sets ->
      LSet.fold
        (fun lft acc -> PpSet.union (lft_sets lft) acc)
        (Option.value ~default:LSet.empty (LMap.find_opt lft !outlives))
        (Option.value ~default:PpSet.empty (LMap.find_opt lft !living)))

let borrowck prog mir =
  (* We check initializedness requirements for every instruction. *)
  let uninitialized_places = Uninitialized_places.go prog mir in
  Array.iteri
    (fun lbl (instr, loc) ->
      let uninit : PlaceSet.t = uninitialized_places lbl in

      let check_initialized pl =
        if PlaceSet.exists (fun pluninit -> is_subplace pluninit pl) uninit then
          Error.error loc "Use of a place which is not fully initialized at this point."
      in

      (match instr with
      | Iassign (pl, _, _) | Icall (_, _, pl, _) -> (
          match pl with
          | PlDeref pl0 ->
              if PlaceSet.mem pl0 uninit then
                Error.error loc "Writing into an uninitialized borrow."
          | PlField (pl0, _) ->
              if PlaceSet.mem pl0 uninit then
                Error.error loc "Writing into a field of an uninitialized struct."
          | _ -> ())
      | _ -> ());

      match instr with
      | Iassign (_, RVplace pl, _) | Iassign (_, RVborrow (_, pl), _) ->
          check_initialized pl
      | Iassign (_, RVbinop (_, pl1, pl2), _) ->
          check_initialized pl1;
          check_initialized pl2
      | Iassign (_, RVunop (_, pl), _) | Iif (pl, _, _) -> check_initialized pl
      | Iassign (_, RVmake (_, pls), _) ->
        let state = ref uninit in
        List.iter (fun pl ->
          if PlaceSet.exists (fun pluninit -> is_subplace pluninit pl) !state then
            Error.error loc "Use of a place which is not fully initialized at this point.";
          let typ = typ_of_place prog mir pl in
          if not (typ_is_copy prog typ) then
            state := PlaceSet.union !state (PlaceSet.singleton pl)
        ) pls
      | Icall (_, pls, _, _) ->
        List.iter check_initialized pls
      | Ireturn -> 
        (match Hashtbl.find_opt mir.mlocals Lret with
          | Some typ_ret ->
              (match typ_ret with
              | Tunit -> ()
              | _ -> check_initialized (PlLocal Lret))
          | None -> ())
      | Iassign (_, (RVunit | RVconst _), _) | Ideinit _ | Igoto _ -> ())
    mir.minstrs;

  (* We check the code honors the non-mutability of shared borrows. *)
  Array.iteri
    (fun _ (instr, loc) ->
      let check_write pl =
        if not ((place_mut prog mir pl) = Mut) then
          Error.error loc "Cannot write to a place behind a shared borrow."
      in
      let check_mut_borrow pl =
        if not (place_mut prog mir pl = Mut) then
          Error.error loc "Cannot create a mutable borrow below a shared borrow."
      in
      match instr with
      | Iassign (_, RVborrow (Mut, pl), _) ->
          check_mut_borrow pl
      | Iassign (pl, _, _) | Icall (_, _, pl, _) ->
          check_write pl
      | _ -> ()
    )
    mir.minstrs;

  let lft_sets = compute_lft_sets prog mir in

  (* TODO: check that outlives constraints declared in the prototype of the function are
    enough to ensure safety. I.e., if [lft_sets lft] contains program point [PpInCaller lft'], this
    means that we need that [lft] be alive when [lft'] dies, i.e., [lft'] outlives [lft]. This relation
    has to be declared in [mir.outlives_graph]. *)

  let lft_sets_map =
    List.fold_left
      (fun acc lft -> LMap.add lft (lft_sets lft) acc)
      LMap.empty
      mir.mgeneric_lfts
  in
  let rec outlives_transitive ?(visited=LSet.empty) lft' lft =
    if lft' = lft then true
    else if LSet.mem lft' visited then false
    else
      match LMap.find_opt lft' mir.moutlives_graph with
      | Some s when LSet.mem lft s -> true
      | Some s ->
          LSet.exists (fun lft'' -> outlives_transitive ~visited:(LSet.add lft' visited) lft'' lft) s
      | None -> false
  in
  
  LMap.iter
    (fun lft ppset ->
      PpSet.iter
        (function
          | PpInCaller lft' ->
              let declared = outlives_transitive lft lft' in
              if not declared then
                Error.error
                  dummy_loc
                  "Missing outlives constraint in function prototype: '%s : '%s"
                  (string_of_lft lft') (string_of_lft lft)
          | _ -> ())
        ppset)
    lft_sets_map;

  (* We check that we never perform any operation which would conflict with an existing
    borrows. *)
  let bor_active_at = Active_borrows.go prog lft_sets mir in
  Array.iteri
    (fun lbl (instr, loc) ->
      (* The list of bor_info for borrows active at this instruction. *)
      let active_borrows_info : bor_info list =
        List.map (get_bor_info prog mir) (BSet.to_list (bor_active_at lbl))
      in

      (* Does there exist a borrow of a place pl', which is active at program point [lbl],
        such that a *write* to [pl] conflicts with this borrow?

         If [pl] is a subplace of pl', then writing to [pl] is always conflicting, because
        it is aliasing with the borrow of pl'.

         If pl' is a subplace of [pl], the situation is more complex:
           - if pl' involves as many dereferences as [pl] (e.g., writing to [x.f1] while
            [x.f1.f2] is borrowed), then the write to [pl] will overwrite pl', hence this is
            conflicting.
           - BUT, if pl' involves more dereferences than [pl] (e.g., writing to [x.f1] while
            [*x.f1.f2] is borrowed), then writing to [pl] will *not* modify values accessible
            from pl'. Hence, subtlely, this is not a conflict. *)
      let conflicting_borrow_no_deref pl =
        List.exists
          (fun bi -> is_subplace pl bi.bplace || is_subplace_no_deref bi.bplace pl)
          active_borrows_info
      in

      (match instr with
      | Iassign (pl, _, _) | Icall (_, _, pl, _) ->
          if conflicting_borrow_no_deref pl then
            Error.error loc "Assigning a borrowed place."
      | Ideinit (l, _) ->
          if conflicting_borrow_no_deref (PlLocal l) then
            Error.error loc
              "A local declared here leaves its scope while still being borrowed."
      | Ireturn ->
          Hashtbl.iter
            (fun l _ ->
              match l with
              | Lparam p ->
                  if conflicting_borrow_no_deref (PlLocal l) then
                    Error.error loc
                      "When returning from this function, parameter `%s` is still \
                       borrowed."
                      p
              | _ -> ())
            mir.mlocals
      | _ -> ());


      (* Variant of [conflicting_borrow_no_deref]: does there exist a borrow of a place pl',
        which is active at program point [lbl], such that a *read* to [pl] conflicts with this
        borrow? In addition, if parameter [write] is true, we consider an operation which is
        both a read and a write. *)
      let conflicting_borrow write pl =
        List.exists
          (fun bi ->
            (bi.bmut = Mut || write)
            && (is_subplace pl bi.bplace || is_subplace bi.bplace pl))
          active_borrows_info
      in

      (* Check a "use" (copy or move) of place [pl]. *)
      let check_use pl =
        let consumes = not (typ_is_copy prog (typ_of_place prog mir pl)) in
        if conflicting_borrow consumes pl then
          Error.error loc "A borrow conflicts with the use of this place.";
        if consumes && contains_deref_borrow pl then
          Error.error loc "Moving a value out of a borrow."
      in

      match instr with
      | Iassign (_, RVunop (_, pl), _) -> check_use pl
      | Iassign (_, RVborrow (mut, pl), _) ->
          if conflicting_borrow (mut = Mut) pl then
            Error.error loc "There is a borrow conflicting this borrow."
      | Iassign (_, RVmake (_, pls), _) ->
        List.iter check_use pls
      | Iassign (_, RVplace pl, _) ->
        check_use pl
      | Iassign (_, RVbinop (_, pl1, pl2), _) ->
        check_use pl1;
        check_use pl2
      | Icall (_, pls, _, _) ->
        List.iter check_use pls
      | Ireturn ->
        (match Hashtbl.find_opt mir.mlocals Lret with
          | Some typ_ret ->
              (match typ_ret with
              | Tunit -> ()
              | _ -> check_use (PlLocal Lret))
          | None -> ())
      | _ -> () 
    )
    mir.minstrs
