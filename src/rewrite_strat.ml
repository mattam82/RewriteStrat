(**********************************************************************)
(* Strategical Rewriting                                              *)
(* Copyright (c) 2016 Matthieu Sozeau <matthieu.sozeau@inria.fr>      *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Rewrite_strat_common

open Names
open Pp
open CErrors
open Util
open Nameops
open Namegen
open Term
open Vars
open Tacticals
open Tacmach
open Tactics
open Pretype_errors
open Typeclasses
open Classes
open Constrexpr
open Globnames
open Evd
open Misctypes
open Locus
open Locusops
open Decl_kinds
open Elimschemes
open Environ
open Termops
open Libnames
open Sigma.Notations
open Proofview.Notations
open Context.Named.Declaration

type relation_carrier =
  | Homogeneous of constr
  | Heterogeneous of constr * constr

type rewrite_proof =
  | RewPrf of constr * constr
  (** A Relation (R : rew_car -> rew_car -> Prop) and a proof of R rew_from rew_to *)
  | RewCast of cast_kind
  (** A proof of convertibility (with casts) *)
  | RewEq of constr * types * constr * constr * constr * types * types
  (** A predicate with one free variable P[x] and its type,
      a proof of [t], [u], a proof of [t = u]
      and its underlying relation [@eq] and [ty],
      such that [rew_from] is convertible to P[t] and
      [rew_to] is convertible to P[u] *)

type evars = evar_map * Evar.Set.t (* goal evars, constraint evars *)

type rewrite_result_info = {
  rew_car : relation_carrier;
  (** Two types, for heterogeneous relations *)
  rew_from : constr ;
  (** A term of type rew_car_from *)
  rew_to : constr ;
  (** A term of type rew_car_to *)
  rew_prf : rewrite_proof ;
  (** A proof of rew_from == rew_to *)
  rew_evars : evars;
  (** The updated map of evars *)
  rew_decls : (Id.t * constr * constr) list;
  (** A new set of declarations (for [set]) *)
  rew_local : bool;
  (** Is the successful rewrite only a rewrite of local hypotheses *)
}

let map_carrier f = function
  | Homogeneous c -> Homogeneous (f c)
  | Heterogeneous (c, c') -> Heterogeneous (f c, f c')

let subst_proof subst prf =
  match prf with
  | RewCast _ -> prf
  | RewPrf (c, c') -> RewPrf (substl subst c, substl subst c')
  | RewEq (x, y, z, w, a, b, c) ->
     RewEq (substl subst x, substl subst y, substl subst z,
            substl subst w, substl subst a, substl subst b,
            substl subst c)
                        
let subst_rewrite_result subst r =
  { rew_from = substl subst r.rew_from;
    rew_to = substl subst r.rew_to;
    rew_car = map_carrier (substl subst) r.rew_car;
    rew_prf = subst_proof subst r.rew_prf;
    rew_evars = r.rew_evars;
    rew_decls = r.rew_decls;
    rew_local = r.rew_local }

(** Typeclass-based generalized rewriting. *)

(** Constants used by the tactic. *)

let plugin = "RewriteStrat"
    
let classes_dirpath =
  Names.DirPath.make (List.map Id.of_string ["Classes";"Coq"])

let init_relation_classes () =
  if is_dirpath_prefix_of classes_dirpath (Lib.cwd ()) then ()
  else Coqlib.check_required_library ["Coq";"Classes";"RelationClasses"]

let init_setoid () =
  if is_dirpath_prefix_of classes_dirpath (Lib.cwd ()) then ()
  else Coqlib.check_required_library ["Coq";"Setoids";"Setoid"]

let make_dir l = DirPath.make (List.rev_map Id.of_string l)

let try_find_global_reference dir s =
  let sp = Libnames.make_path (make_dir dir) (Id.of_string s) in
    try Nametab.global_of_path sp
    with Not_found ->
      anomaly (str "Global reference " ++ str s ++ str " not found in generalized rewriting")

let find_reference dir s =
  let gr = lazy (try_find_global_reference dir s) in
    fun () -> Lazy.force gr

let find_global dir s =
  let gr = lazy (try_find_global_reference dir s) in
    fun (evd,cstrs) ->
      let sigma = Sigma.Unsafe.of_evar_map evd in
      let Sigma (c, sigma, _) = Evarutil.new_global sigma (Lazy.force gr) in
      let evd = Sigma.to_evar_map sigma in
	(evd, cstrs), c

(** Utility for dealing with polymorphic applications *)

(** Global constants. *)

let coq_eq_ref = find_reference ["Coq"; "Init"; "Logic"] "eq"
let coq_eq = find_global ["Coq"; "Init"; "Logic"] "eq"
let coq_f_equal = find_global ["Coq"; "Init"; "Logic"] "f_equal"
let coq_all = find_global ["Coq"; "Init"; "Logic"] "all"

let equality_mod = [plugin; "Equality"]
let coq_eq_rew = find_global equality_mod "eq_rew"
let coq_eq_rew_inv = find_global equality_mod "eq_rew_inv"
let coq_full_relation = find_global equality_mod "full_relation"

let impl = find_global ["Coq"; "Program"; "Basics"] "impl"

(** Bookkeeping which evars are constraints so that we can
    remove them at the end of the tactic. *)

let goalevars evars = fst evars
let cstrevars evars = snd evars

let nf_zeta =
  Reductionops.clos_norm_flags (CClosure.RedFlags.mkflags [CClosure.RedFlags.fZETA])

let get_type_of_env env evars arg =
  Retyping.get_type_of env (goalevars evars) arg

let get_type_of env envprf evars arg =
  Retyping.get_type_of (Environ.push_rel_context envprf env) (goalevars evars) arg

let string_of_constr_env env evars c =
  Pp.string_of_ppcmds (Printer.pr_constr_env env (goalevars evars) c)

let string_of_constr envprf env evars c =
  Pp.string_of_ppcmds
    (Printer.pr_constr_env (Environ.push_rel_context envprf env)
                           (goalevars evars) c)

let new_goal_evar env (evd,cstrs) t =
  let s = Typeclasses.set_resolvable Evd.Store.empty false in
  let evd = Sigma.Unsafe.of_evar_map evd in
  let Sigma (t, evd', _) = Evarutil.new_evar ~store:s env evd t in
  let evd' = Sigma.to_evar_map evd' in
  (evd', cstrs), t

let new_cstr_evar env (evd,cstrs) t =
  let (evd', cstrs), t = new_goal_evar env (evd,cstrs) t in
  let ev, _ = destEvar t in
    (evd', Evar.Set.add ev cstrs), t

let new_cstr_type_evar env (evd,cstrs) =
  let evd = Sigma.Unsafe.of_evar_map evd in
  let Sigma (t, evd', _) = Evarutil.new_type_evar env evd Evd.univ_flexible in
  let evd' = Sigma.to_evar_map evd' in
    (evd', cstrs), fst t

(** Building or looking up instances. *)
let e_new_cstr_evar env evars t =
  let evd', t = new_cstr_evar env !evars t in evars := evd'; t

(** Building or looking up instances. *)

let extends_undefined evars evars' =
  let f ev evi found = found || not (Evd.mem evars ev)
  in fold_undefined f evars' false

let app_poly_check env evars f args =
  let (evars, cstrs), fc = f evars in
  let evdref = ref evars in
  let t = Typing.e_solve_evars env evdref (mkApp (fc, args)) in
    (!evdref, cstrs), t

let app_poly_nocheck env evars f args =
  let evars, fc = f evars in
    evars, mkApp (fc, args)

let app_poly_sort b =
  if b then app_poly_nocheck
  else app_poly_check

let find_class_proof proof_type proof_method env evars carrier relation =
  try
    let evars, goal = app_poly_check env evars proof_type [| carrier ; relation |] in
    let evars', c = Typeclasses.resolve_one_typeclass env (goalevars evars) goal in
      if extends_undefined (goalevars evars) evars' then raise Not_found
      else app_poly_check env (evars',cstrevars evars) proof_method [| carrier; relation; c |]
  with e when Logic.catchable_exception e -> raise Not_found


let make_eq () =
(*FIXME*) Universes.constr_of_global (Coqlib.build_coq_eq ())
let make_eq_refl () =
(*FIXME*) Universes.constr_of_global (Coqlib.build_coq_eq_refl ())
let make_eq_congr () =
(*FIXME*) Universes.constr_of_global (Coqlib.build_coq_eq_data ()).Coqlib.congr

let eq_abs_id = Id.of_string "__abs__"
let is_eq_abs t =
  match kind_of_term t with
  | Var id -> Id.equal eq_abs_id id
  | _ -> false

let get_rew_car = function
  | Homogeneous c -> c
  | Heterogeneous (c, c') -> c
                                     
let get_rew_prf r = match r.rew_prf with
  | RewPrf (rel, prf) -> rel, prf
  | RewCast c ->
    let rel = mkApp (make_eq (), [| get_rew_car r.rew_car |]) in
      rel, mkCast (mkApp (make_eq_refl (), [| get_rew_car r.rew_car; r.rew_from |]),
		   c, mkApp (rel, [| r.rew_from; r.rew_to |]))
  | RewEq (p, pty, t1, t2, c, rel, car) ->
     if is_eq_abs p then mkApp (rel, [| car |]), c
     else
       let pred = mkNamedLambda eq_abs_id car (lift 1 p) in
       let prf = mkApp (make_eq_congr (),
			[| car; pty; pred; t1; t2; c |])
       in (mkApp (rel, [| pty |])), prf
                                                  
(** Utility functions *)

module GlobalBindings (M : sig
  val relation_classes : string list
  val morphisms : string list
  val relation : string list * string
  val app_poly : env -> evars -> (evars -> evars * constr) -> constr array -> evars * constr
  val arrow : evars -> evars * constr
end) = struct
  open M
  open Context.Rel.Declaration
  let relation : evars -> evars * constr = find_global (fst relation) (snd relation)

  let reflexive_type = find_global relation_classes "Reflexive"
  let reflexive_proof = find_global relation_classes "reflexivity"

  let symmetric_type = find_global relation_classes "Symmetric"
  let symmetric_proof = find_global relation_classes "symmetry"

  let transitive_type = find_global relation_classes "Transitive"
  let transitive_proof = find_global relation_classes "transitivity"

  let forall_relation = find_global morphisms "forall_relation"
  let pointwise_relation = find_global morphisms "pointwise_relation"

  let forall_relation_ref = find_reference morphisms "forall_relation"
  let pointwise_relation_ref = find_reference morphisms "pointwise_relation"

  let respectful = find_global morphisms "respectful"
  let respectful_ref = find_reference morphisms "respectful"

  let respectfulh = find_global morphisms "respectful_hetero"
  let respectfulh_ref = find_reference morphisms "respectful_hetero"

  let default_relation = find_global ["Coq"; "Classes"; "SetoidTactics"] "DefaultRelation"

  let coq_forall = find_global morphisms "forall_def"

  let subrelation = find_global relation_classes "subrelation"
  let hsubrelation = find_global relation_classes "hsubrelation"
  let do_subrelation = find_global morphisms "do_subrelation"
  let apply_subrelation = find_global morphisms "apply_subrelation"

  let rewrite_relation_class = find_global relation_classes "RewriteRelation"

  let proper_class = lazy (class_info (try_find_global_reference morphisms "Proper"))
  let proper_proxy_class = lazy (class_info (try_find_global_reference morphisms "ProperProxy"))

  let related_class = lazy (class_info (try_find_global_reference morphisms "Related"))
  let related_proxy_class =
    lazy (class_info (try_find_global_reference morphisms "RelatedProxy"))
                                
  let proper_proj = lazy (mkConst (Option.get (pi3 (List.hd (Lazy.force proper_class).cl_projs))))

  let glob_cl cl =
    let l = lazy (Lazy.force cl).cl_impl in
      fun (evd,cstrs) ->
        let sigma = Sigma.Unsafe.of_evar_map evd in
        let Sigma (c, sigma, _) = Evarutil.new_global sigma (Lazy.force l) in
        let evd = Sigma.to_evar_map sigma in
	  (evd, cstrs), c
                         
  let proper_type = glob_cl proper_class
  let proper_proxy_type = glob_cl proper_proxy_class
  let related_type = glob_cl related_class
  let related_proxy_type = glob_cl related_proxy_class
                             
  let proper_proof env evars carrier relation x =
    let evars, goal = app_poly env evars proper_proxy_type [| carrier ; relation; x |] in
      new_cstr_evar env evars goal
                          
  let related_proof env evars carrier carrier' relation x y =
    let evars, goal =
      app_poly env evars related_proxy_type [| carrier ; carrier'; relation; x; y |]
    in
      new_cstr_evar env evars goal

  let get_carrier = function
    | Homogeneous car -> car, car
    | Heterogeneous (car, car') -> car, car'

  let mk_related env evars car relation x y =
    let car, car' = get_carrier car in
    app_poly env evars related_type [| car; car'; relation; x; y |]
                    
  let related_proof env evars car relation x =
    match car with
    | Homogeneous car -> proper_proof env evars car relation x
    | Heterogeneous (ty, ty') -> related_proof env evars ty ty' relation x x
                    
  let get_reflexive_proof env = find_class_proof reflexive_type reflexive_proof env
  let get_symmetric_proof env = find_class_proof symmetric_type symmetric_proof env
  let get_transitive_proof env = find_class_proof transitive_type transitive_proof env

  let mk_relation env evd a =
    app_poly env evd relation [| a |]

  let mk_hrelation env evd a b =
    evd, mkProd (Anonymous, a, mkProd (Anonymous, lift 1 b, mkProp))
             
  let new_relation_evar env evd a =
    let evars, ty = mk_relation env evd a in
    new_cstr_evar env evars ty

  let new_hrelation_evar env evd a a' =
    if eq_constr a a' then new_relation_evar env evd a
    else 
      let evars, ty = mk_hrelation env evd a a' in
      new_cstr_evar env evars ty
		  
  let mk_relation_carrier env evd = function
    | Heterogeneous (from, to_) -> mk_hrelation env evd from to_
    | Homogeneous car -> mk_relation env evd car

  let mk_relation_carrier_evar env evd car =
    let evd, rel = mk_relation_carrier env evd car in
    new_cstr_evar env evd rel
                                    
  (** Build an infered signature from constraints on the arguments and expected output
      relation *)

  let build_signature evars env m mty (cstrs : (constr * constr * types option) option list)
      (finalcstr : (types * types option) option) =
    let mk_relty newenv evars ty obj =
      match obj with
      | None ->
	 let evars, relty = mk_relation_carrier env evars ty in
	 if closed0 relty then
	   let env' =
             Environ.reset_with_named_context (Environ.named_context_val env) env in
	   new_cstr_evar env' evars relty, relty
	 else new_cstr_evar newenv evars relty, relty
      | Some rel ->
         (evars, rel), get_type_of_env env evars rel
    in
    let rec aux env evars m m' ty ty' l =
      (* Printf.printf "build_signature: aux %s %s\n%!" *)
      (*               (string_of_constr_env env evars ty) *)
      (*               (string_of_constr_env env evars ty'); *)

      let t = whd_all env (goalevars evars) ty in
      let t' = whd_all env (goalevars evars) ty' in
	match kind_of_term t, kind_of_term t', l with
	| Prod (na, ty, b), Prod (na', ty', b'), obj :: cstrs ->
          let b = Reductionops.nf_betaiota (goalevars evars) b in
          let b' = Reductionops.nf_betaiota (goalevars evars) b' in
	  let ty = Reductionops.nf_betaiota (goalevars evars) ty in
	  let ty' = Reductionops.nf_betaiota (goalevars evars) ty' in
          let _car =
            if eq_constr ty ty' then Homogeneous ty else Heterogeneous (ty, ty') in
	  (* if noccurn 1 b (\* non-dependent product *\) then *)
	  (*   let (evars, b', arg, cstrs) = aux env evars (subst1 mkProp b) (subst1 mkProp b') cstrs in *)
	  (*   let (evars, relty), _ = mk_relty env evars car obj in *)
	  (*   let evars, newarg = *)
          (*     app_poly env evars respectful [| ty ; b' ; relty ; arg |] in *)
	  (*     evars, mkProd(na, ty, b), newarg, (ty, Some relty) :: cstrs *)
	  (* else *)
            (* (match obj with *)
            (* | None ->  *)
	    (*    let (evars, b, arg, cstrs) = *)
            (*      aux (Environ.push_rel (LocalAssum (na, ty)) env) *)
            (*          evars b b' cstrs *)
            (*    in *)
            (*    let pred = mkLambda (na, ty, b) in *)
	    (*    let liftarg = mkLambda (na, ty, arg) in *)
            (*    let evars, arg' = *)
            (*      app_poly env evars forall_relation [| ty ; pred ; liftarg |] in *)
            (*    evars, mkProd(na, ty, b), arg', (ty, None) :: cstrs *)
            (* | Some rel -> *)
          let evars, rel =
            match obj with
            | Some (from, to_, Some rel) ->
               evars, rel
            | _ ->
               new_hrelation_evar env evars ty ty' in
          let na = match na with
               | Anonymous ->
                 Tactics.fresh_id_in_env [] (Id.of_string "H") env
              | Name na -> na
            in
            let na' =
              Tactics.fresh_id_in_env [na] na env
            in
            let decls = LocalAssum (Name na', lift 1 ty') :: LocalAssum (Name na, ty) :: [] in
            let decls = LocalAssum (Name (Id.of_string "H"),
                                    mkApp (lift 2 rel, [| mkRel 2; mkRel 1|])) :: decls in
            let (evars, b'', arg, cstrs) =
              aux (push_rel_context decls env) evars (mkApp (m, [|mkRel 3|])) (mkApp (m', [|mkRel 2|]))
                  (lift 2 b) (liftn 1 3 (lift 1 b'))
                  cstrs
            in
            let preda = mkLambda (Name na, ty, b) in
            let predb = mkLambda (Name na, ty', b') in
	    let liftarga = it_mkLambda_or_LetIn arg decls in
            let evars, arg' =
              app_poly env evars respectfulh [| ty; ty'; preda; predb;
                                                rel; liftarga |] in
            evars, mkProd (Name na, ty, b), arg', (ty, None) :: cstrs
          (* if Option.is_empty obj then *)
	    (* else *)
            (*   (let (evars, relty), reltype = mk_relty evars env ty obj in *)
            (*   *)
            (*    error "build_signature: no constraint can apply on a dependent argument") *)
	| _, _, obj :: _ -> anomaly ~label:"build_signature" (Pp.str "not enough products")
	| _, _, [] ->
	  (match finalcstr with
	  | None | Some (_, None) ->
	    let t = Reductionops.nf_betaiota (fst evars) ty in
	    let (evars, rel), _ = mk_relty env evars (Homogeneous t) None in
	      evars, t, rel, [t, Some rel]
	  | Some (t, Some rel) -> evars, t, rel, [t, Some rel])
    in
    Printf.printf "build_signature: %s\n%!" (string_of_constr_env env evars m);
    let (evars, b, arg, cstrs as res) = aux env evars m m mty mty cstrs in
    Printf.printf "build_signature gives: %s, %s\n%!" (string_of_constr_env env evars b)
                  (string_of_constr_env env evars arg);
    res

  (* let build_apprel evars env m mty args args' *)
  (*                  (finalcstr : (types * types option) option) = *)
  (*   let rec aux i env evars m m' ty ty' = *)
  (*     Printf.printf "build_apprel: aux %s %s %s %s\n%!" *)
  (*                   (string_of_constr_env env evars m) *)
  (*                   (string_of_constr_env env evars m') *)
  (*                   (string_of_constr_env env evars ty) *)
  (*                   (string_of_constr_env env evars ty'); *)
  (*     if i = Array.length args then *)
  (*       let ty = Reductionops.nf_betaiota (fst evars) ty in *)
  (*       let ty' = Reductionops.nf_betaiota (fst evars) ty' in *)
  (*       let car = (Heterogeneous (ty, ty')) in *)
  (*       let car' = map_carrier (lift len) car in *)
  (*       let evars, rel = *)
  (*         match finalcstr with *)
  (*         | None | Some (_, None) -> *)
  (*            mk_relation_carrier_evar env' evars car' *)
  (*         | Some (t, Some rel) -> evars, lift len rel *)
  (*       in *)
  (*       let evars, goal = mk_related env' evars car' rel (lift len m) (lift len m') in *)
  (*       let () = Printf.printf "build_signature finished: %s\n%!" *)
  (*                              (string_of_constr_env env' evars goal) in *)
  (*       let env' = *)
  (*         let dosub, appsub = do_subrelation, apply_subrelation in *)
  (*         let id = *)
  (*           Tactics.fresh_id_in_env [] (Id.of_string "do_subrelation") env' *)
  (*         in *)
  (*         Environ.push_named *)
  (*           (LocalDef (id, *)
  (*                      snd (app_poly env' evars dosub [||]), *)
  (*                      snd (app_poly_nocheck env' evars appsub [||]))) *)
  (*           env' *)
  (*       in *)
  (*       let evars, prf = new_cstr_evar env' evars goal in *)
  (*       evars, it_mkLambda_or_LetIn prf hyps, car, *)
  (*       nf_zeta env (goalevars evars) (it_mkLambda_or_LetIn rel hyps), m, m' *)
  (*     else  *)
  (*       let t = Reductionops.whd_betadeltaiota env (goalevars evars) ty in *)
  (*       let t' = Reductionops.whd_betadeltaiota env (goalevars evars) ty' in *)
  (*       let (na, ty, b), (na', ty', b') = destProd t, destProd t' in *)
  (*       let b = Reductionops.nf_betaiota (goalevars evars) b in *)
  (*       let b' = Reductionops.nf_betaiota (goalevars evars) b' in *)
  (*       let ty = Reductionops.nf_betaiota (goalevars evars) ty in *)
  (*       let ty' = Reductionops.nf_betaiota (goalevars evars) ty' in *)
  (*       let _car = *)
  (*         if eq_constr ty ty' then Homogeneous ty else Heterogeneous (ty, ty') in *)
  (*       let evars, from, to_, hyps = *)
  (*         match args'.(i) with *)
  (*         | Some r -> *)
  (*            (\* let rel, prf = get_rew_prf r in *\) *)
  (*            (\* let evars, rel' = *\) *)
  (*            (\*   mk_related env evars r.rew_car rel r.rew_from r.rew_to in *\) *)
  (*            (\* let len = List.length hyps in *\) *)
  (*            (\* let hyps = LocalDef (Anonymous, lift len prf, lift len rel') :: hyps in *\) *)
  (*            (\* Printf.printf "build_signature arg: %s -> %s car: %s prf: %s rel: %s\n%!" *\) *)
  (*            (\*               (string_of_constr_env env evars r.rew_from) *\) *)
  (*            (\*               (string_of_constr_env env evars r.rew_to) *\) *)
  (*            (\*               (string_of_constr_env env evars (get_rew_car r.rew_car)) *\) *)
  (*            (\*               (string_of_constr_env env evars prf) *\) *)
  (*            (\*               (string_of_constr_env env evars rel) *\) *)
  (*            (\* ; *\) *)
  (*            evars, r.rew_from, r.rew_to, hyps *)
  (*         | None -> evars, args.(i), args.(i), hyps *)
  (*            (\* let evars, rel = mk_relation_carrier_evar env evars car in *\) *)
  (*            (\* let evars, prf = related_proof env evars car rel args.(i) in *\) *)
  (*            (\* evars, args.(i), args.(i), car, (mkApp (rel, [| args.(i); args.(i) |]), prf) *\) *)
  (*       in *)
  (*       aux (succ i) env evars (mkApp (m, [|from|])) (mkApp (m', [|to_|])) *)
  (*           hyps (subst1 from b) (subst1 to_ b') *)
  (*   in *)
  (*   Printf.printf "build_signature: %s\n%!" (string_of_constr_env env evars m); *)
  (*   let (evars, prf, car, rel, from, to_ as res) = aux 0 env evars m m [] mty mty in *)
  (*   Printf.printf "build_signature gives: %s\n%!" (string_of_constr_env env evars prf); *)
  (*   res *)
      
  (** Folding/unfolding of the tactic constants. *)

  let unfold_impl t =
    match kind_of_term t with
    | App (arrow, [| a; b |])(*  when eq_constr arrow (Lazy.force impl) *) ->
      mkProd (Anonymous, a, lift 1 b)
    | _ -> assert false

  let unfold_all t =
    match kind_of_term t with
    | App (id, [| a; b |]) (* when eq_constr id (Lazy.force coq_all) *) ->
      (match kind_of_term b with
      | Lambda (n, ty, b) -> mkProd (n, ty, b)
      | _ -> t)
    | _ -> t

  let unfold_forall t =
    match kind_of_term t with
    | App (id, [| a; b |]) (* when eq_constr id (Lazy.force coq_all) *) ->
      (match kind_of_term b with
      | Lambda (n, ty, b) -> mkProd (n, ty, b)
      | _ -> assert false)
    | _ -> assert false

  let arrow_morphism env evd ta tb a b =
    let ap = is_Prop ta and bp = is_Prop tb in
      if ap && bp then app_poly env evd impl [| a; b |], unfold_impl
      else if ap then (* Domain in Prop, CoDomain in Type *)
	(app_poly env evd arrow [| a; b |]), unfold_impl
	(* (evd, mkProd (Anonymous, a, b)), (fun x -> x) *)
      else if bp then (* Dummy forall *)
	(app_poly env evd coq_all [| a; mkLambda (Anonymous, a, lift 1 b) |]), unfold_forall
      else (* None in Prop, use arrow *)
	(app_poly env evd arrow [| a; b |]), unfold_impl

  let rec decomp_pointwise n c =
    if Int.equal n 0 then c
    else
      match kind_of_term c with
      | App (f, [| a; b; relb |]) when Globnames.is_global (pointwise_relation_ref ()) f ->
	decomp_pointwise (pred n) relb
      | App (f, [| a; b; rela; relb |]) when Globnames.is_global (respectful_ref ()) f ->
	decomp_pointwise (pred n) relb
      | App (f, [| a; b; c; d; rela; relb |]) when Globnames.is_global (respectfulh_ref ()) f ->
         let _, relb = decompose_lam_n 3 relb in
	 decomp_pointwise (pred n) relb
      | App (f, [| a; b; arelb |]) when Globnames.is_global (forall_relation_ref ()) f ->
	decomp_pointwise (pred n) (Reductionops.beta_applist (arelb, [mkRel 1]))
      | _ -> invalid_arg "decomp_pointwise"

  let rec apply_pointwise env evd rel prf = function
    | arg :: args ->
      (match kind_of_term rel with
      | App (f, [| a; b; relb |]) when Globnames.is_global (pointwise_relation_ref ()) f ->
	apply_pointwise env evd relb (mkApp(prf, [| arg |])) args
      | App (f, [| a; b; rela; relb |]) when Globnames.is_global (respectful_ref ()) f ->
	 let evd, aprf = proper_proof env evd a rela arg in
	 let prf' = mkApp (prf, [| arg; arg; aprf |]) in
	 apply_pointwise env evd relb prf' args
      | App (f, [| a; b; arelb |]) when Globnames.is_global (forall_relation_ref ()) f ->
	 let rel = Reductionops.beta_applist (arelb, [arg]) in
	apply_pointwise env evd rel (mkApp (prf, [| arg |])) args
      | Evar f ->
         let concl = Evd.evar_concl (Evd.find (fst evd) (fst f)) in
         if !Flags.debug then
           Printf.printf "apply_pointwise on evar %s\n" (Pp.string_of_ppcmds (Printer.pr_constr_env env (goalevars evd) concl));
         let a, b =
           match kind_of_term concl with
           | App (rel, [| ty |]) ->
              (match kind_of_term ty with
               | Prod (_, a, b) -> a, subst1 mkProp b
               | _ -> assert false)
           | _ -> assert false
         in
         let evd, rela = new_relation_evar env evd a in
         let evd, relb = new_relation_evar env evd b in
         let evd, resp = app_poly env evd respectful [| a; b; rela; relb |] in
         let evars = Evd.define (fst f) resp (fst evd) in
	 let evd, aprf = proper_proof env (evars, snd evd) a rela arg in
         let prf' = mkApp (prf, [| arg; arg; aprf |]) in
	 apply_pointwise env evd relb prf' args
      | _ ->
         if !Flags.debug then
           Printf.printf "apply_pointwise on %s\n" (Pp.string_of_ppcmds (Printer.pr_constr_env env (goalevars evd) rel));
         invalid_arg "apply_pointwise")
    | [] -> evd, rel, prf

  let pointwise_or_dep_relation pointwise env evd n t t' trel car rel =
    (* if noccurn 1 car && noccurn 1 rel then *)
      (* if pointwise then *)
      (*   app_poly env evd pointwise_relation [| t; lift (-1) car; lift (-1) rel |] *)
      (* else *)
      (*   if eq_constr t t' then *)
      (*     app_poly env evd respectful [| t; lift (-1) car; lift (-1) trel; lift (-1) rel |] *)
      (*   else *)
          let car, car' = 
            match car with
            | Heterogeneous (car, car') -> car, car'
            | Homogeneous car -> car, car
          in
          app_poly env evd respectfulh [| t; t'; mkLambda (n, t, car);
                                          mkLambda (n, t', car');
                                          trel; rel |]                      
    (* else *)
    (*   app_poly env evd forall_relation *)
    (*     [| t; mkLambda (n, t, car); mkLambda (n, t, rel) |] *)

  let lift_cstr env evars (args : constr list) c ty cstr =
    let start evars env car cstr =
      match cstr with
      | None | Some (_, None) ->
	let evars, rel = mk_relation env evars car in
	  new_cstr_evar env evars rel
      | Some (ty, Some rel) -> evars, rel
    in
    let rec aux evars env prod n =
      if Int.equal n 0 then start evars env prod cstr
      else
	match kind_of_term (Reduction.whd_all env prod) with
	| Prod (na, ty, b) ->
	  if noccurn 1 b then
	    let b' = lift (-1) b in
	    let evars, rty = start evars env ty None in
	    let evars, rb = aux evars env b' (pred n) in
	      app_poly env evars respectful [| ty; b'; rty; rb |]
	  else
	    let evars, rb = aux evars (Environ.push_rel (LocalAssum (na, ty)) env) b (pred n) in
	      app_poly env evars forall_relation
		[| ty; mkLambda (na, ty, b); mkLambda (na, ty, rb) |]
	| _ -> raise Not_found
    in
    let rec find env c ty = function
      | [] -> None
      | arg :: args ->
	try let evars, found = aux evars env ty (succ (List.length args)) in
	      Some (evars, found, c, ty, arg :: args)
	with Not_found ->
	  let ty = Reduction.whd_all env ty in
	  find env (mkApp (c, [| arg |])) (prod_applist ty [arg]) args
    in find env c ty args

  let unlift_cstr env sigma = function
    | None -> None
    | Some codom -> Some (decomp_pointwise 1 codom)

  (** Looking up declared rewrite relations (instances of [RewriteRelation]) *)
  let is_applied_rewrite_relation env sigma rels t =
    match kind_of_term t with
    | App (c, args) when Array.length args >= 2 ->
      let head = if isApp c then fst (destApp c) else c in
	if Globnames.is_global (coq_eq_ref ()) head then None
	else
	  (try
	   let params, args = Array.chop (Array.length args - 2) args in
	   let env' = Environ.push_rel_context rels env in
	   let sigma = Sigma.Unsafe.of_evar_map sigma in
	   let Sigma ((evar, _), evars, _) = Evarutil.new_type_evar env' sigma Evd.univ_flexible in
	   let evars = Sigma.to_evar_map evars in
	   let evars, inst = 
	     app_poly env (evars,Evar.Set.empty)
	       rewrite_relation_class [| evar; mkApp (c, params) |] in
	   let _ = Typeclasses.resolve_one_typeclass env' (goalevars evars) inst in
	     Some (it_mkProd_or_LetIn t rels)
	   with e when CErrors.noncritical e -> None)
  | _ -> None


end

(* let my_type_of env evars c = Typing.e_type_of env evars c *)
(* let mytypeofkey = Profile.declare_profile "my_type_of";; *)
(* let my_type_of = Profile.profile3 mytypeofkey my_type_of *)


let type_app_poly env evd f args =
  let evars, c = app_poly_nocheck env evd f args in
  let evd', t = Typing.type_of env (goalevars evars) c in
    (evd', cstrevars evars), c

module PropGlobal = struct
  module Consts =
  struct
    let relation_classes = ["Coq"; "Classes"; "RelationClasses"]
    let morphisms = [plugin; "Morphisms"]
    let relation = ["Coq"; "Relations";"Relation_Definitions"], "relation"
    let app_poly = app_poly_nocheck
    let arrow = find_global ["Coq"; "Program"; "Basics"] "arrow"
    let coq_inverse = find_global ["Coq"; "Program"; "Basics"] "flip"
  end

  module G = GlobalBindings(Consts)

  include G
  include Consts
  let inverse env evd car rel =
    type_app_poly env evd coq_inverse [| car ; car; mkProp; rel |]
      (* app_poly env evd coq_inverse [| car ; car; mkProp; rel |] *)

end

module TypeGlobal = struct
  module Consts =
    struct
      let relation_classes = ["Coq"; "Classes"; "CRelationClasses"]
      let morphisms = [plugin; "CMorphisms"]
      let relation = relation_classes, "crelation"
      let app_poly = app_poly_check
      let arrow = find_global ["Coq"; "Classes"; "CRelationClasses"] "arrow"
      let coq_inverse = find_global ["Coq"; "Classes"; "CRelationClasses"] "flip"
    end

  module G = GlobalBindings(Consts)
  include G
  include Consts


  let inverse env (evd,cstrs) car rel =
    let sigma = Sigma.Unsafe.of_evar_map evd in
    let Sigma (sort, sigma, _) = Evarutil.new_Type ~rigid:Evd.univ_flexible env sigma in
    let evd = Sigma.to_evar_map sigma in
      app_poly_check env (evd,cstrs) coq_inverse [| car ; car; sort; rel |]

end

let sort_of_rel env evm rel =
  Reductionops.sort_of_arity env evm (Retyping.get_type_of env evm rel)

let is_applied_rewrite_relation = PropGlobal.is_applied_rewrite_relation

(* let _ = *)
(*   Hook.set Equality.is_applied_rewrite_relation is_applied_rewrite_relation *)

let split_head = function
    hd :: tl -> hd, tl
  | [] -> assert(false)

let evd_convertible env evd x y =
  try
    let evd = Evarconv.the_conv_x env x y evd in
    (* Unfortunately, the_conv_x might say they are unifiable even if some
        unsolvable constraints remain, so we check them here *)
    let evd = Evarconv.consider_remaining_unif_problems env evd in
    let () = Evarconv.check_problems_are_solved env evd in
    Some evd
  with e when noncritical e -> None

let convertible env evd x y =
  Reductionops.is_conv_leq env evd x y

type hypinfo = {
  prf : constr;
  car : relation_carrier;
  rel : constr;
  sort : bool; (* true = Prop; false = Type *)
  c1 : constr;
  c2 : constr;
  holes : Clenv.hole list;
}

let get_symmetric_proof b =
  if b then PropGlobal.get_symmetric_proof else TypeGlobal.get_symmetric_proof

let error_no_relation () = error "Cannot find a relation to rewrite."

let rec decompose_app_rel env evd t =
  (** Head normalize for compatibility with the old meta mechanism *)
  let t = Reductionops.whd_betaiota evd t in
  match kind_of_term t with
  | App (f, [||]) -> assert false
  | App (f, [|arg|]) ->
    let (f', argl, argr) = decompose_app_rel env evd arg in
    let ty = Typing.unsafe_type_of env evd argl in
    let f'' = mkLambda (Name default_dependent_ident, ty,
      mkLambda (Name (Id.of_string "y"), lift 1 ty,
        mkApp (lift 2 f, [| mkApp (lift 2 f', [| mkRel 2; mkRel 1 |]) |])))
    in (f'', argl, argr)
  | App (f, args) ->
    let len = Array.length args in
    let fargs = Array.sub args 0 (Array.length args - 2) in
    let rel = mkApp (f, fargs) in
    rel, args.(len - 2), args.(len - 1)
  | _ -> error_no_relation ()

let decompose_app_rel env evd t =
  let (rel, t1, t2) = decompose_app_rel env evd t in
  let ty = Retyping.get_type_of env evd rel in
  let () = if not (Reduction.is_arity env ty) then error_no_relation () in
  (rel, t1, t2)

let decompose_applied_relation env sigma (c,l) =
  let open Context.Rel.Declaration in
  let ctype = Retyping.get_type_of env sigma c in
  let find_rel ty =
    let sigma, cl = Clenv.make_evar_clause env sigma ty in
    let sigma = Clenv.solve_evar_clause env sigma true cl l in
    let { Clenv.cl_holes = holes; Clenv.cl_concl = t } = cl in
    let (equiv, c1, c2) = decompose_app_rel env sigma t in
    let ty1 = Retyping.get_type_of env sigma c1 in
    let ty2 = Retyping.get_type_of env sigma c2 in
    let sort = sort_of_rel env sigma equiv in
    let args = Array.map_of_list (fun h -> h.Clenv.hole_evar) holes in
    let value = mkApp (c, args) in
    let car =
      match evd_convertible env sigma ty1 ty2 with
      | None -> Heterogeneous (ty1, ty2)
      | Some sigma -> Homogeneous ty1
    in
    if !Flags.debug then Printf.printf "decompose_applied_relation: car:  %s\n"
                                       (string_of_constr_env env (sigma,Evar.Set.empty) ty1);
    Some (sigma, { prf=value;
                   car=car; rel = equiv; sort = Sorts.is_prop sort;
                   c1=c1; c2=c2; holes })
  in
    match find_rel ctype with
    | Some c -> c
    | None ->
	let ctx,t' = Reductionops.splay_prod env sigma ctype in (* Search for underlying eq *)
	match find_rel (it_mkProd_or_LetIn t' (List.map (fun (n,t) -> LocalAssum (n, t)) ctx)) with
	| Some c -> c
	| None -> error "Cannot find an homogeneous relation to rewrite."

let rewrite_db = "rewrite"

let conv_transparent_state = (Id.Pred.empty, Cpred.full)

let _ =
  Hints.add_hints_init
    (fun () ->
       Hints.create_hint_db false rewrite_db conv_transparent_state true)

let rewrite_transparent_state () =
  Hints.Hint_db.transparent_state (Hints.searchtable_map rewrite_db)

let rewrite_core_unif_flags = {
  Unification.modulo_conv_on_closed_terms = None;
  Unification.use_metas_eagerly_in_conv_on_closed_terms = true;
  Unification.use_evars_eagerly_in_conv_on_closed_terms = true;
  Unification.modulo_delta = empty_transparent_state;
  Unification.modulo_delta_types = full_transparent_state;
  Unification.check_applied_meta_types = true;
  Unification.use_pattern_unification = true;
  Unification.use_meta_bound_pattern_unification = true;
  Unification.frozen_evars = Evar.Set.empty;
  Unification.restrict_conv_on_strict_subterms = false;
  Unification.modulo_betaiota = false;
  Unification.modulo_eta = true;
}

(* Flags used for the setoid variant of "rewrite" and for the strategies
   "hints"/"old_hints"/"terms" of "rewrite_strat", and for solving pre-existing
   evars in "rewrite" (see unify_abs) *)
let rewrite_unif_flags =
  let flags = rewrite_core_unif_flags in {
  Unification.core_unify_flags = flags;
  Unification.merge_unify_flags = flags;
  Unification.subterm_unify_flags = flags;
  Unification.allow_K_in_toplevel_higher_order_unification = true;
  Unification.resolve_evars = true
  }

let rewrite_core_conv_unif_flags = {
  rewrite_core_unif_flags with
    Unification.modulo_conv_on_closed_terms = Some conv_transparent_state;
    Unification.modulo_delta_types = conv_transparent_state;
    Unification.modulo_betaiota = true
}

(* Fallback flags for the setoid variant of "rewrite" *)
let rewrite_conv_unif_flags =
  let flags = rewrite_core_conv_unif_flags in {
  Unification.core_unify_flags = flags;
  Unification.merge_unify_flags = flags;
  Unification.subterm_unify_flags = flags;
  Unification.allow_K_in_toplevel_higher_order_unification = true;
  Unification.resolve_evars = true
  }

(* Flags for "setoid_rewrite c"/"rewrite_strat -> c" *)
let general_rewrite_unif_flags () =
  let ts = rewrite_transparent_state () in
  let core_flags =
    { rewrite_core_unif_flags with
      Unification.modulo_conv_on_closed_terms = Some ts;
      Unification.use_evars_eagerly_in_conv_on_closed_terms = false;
      Unification.modulo_delta = ts;
      Unification.modulo_delta_types = ts;
      Unification.modulo_betaiota = true }
  in {
    Unification.core_unify_flags = core_flags;
    Unification.merge_unify_flags = core_flags;
    Unification.subterm_unify_flags = { core_flags with Unification.modulo_delta = empty_transparent_state };
    Unification.allow_K_in_toplevel_higher_order_unification = true;
    Unification.resolve_evars = true
  }

let refresh_hypinfo env sigma (is, cb) =
  let sigma, cbl = Tacinterp.interp_open_constr_with_bindings is env sigma cb in
  let sigma, hypinfo = decompose_applied_relation env sigma cbl in
  let { c1; c2; car; rel; prf; sort; holes } = hypinfo in
  sigma, (car, rel, prf, c1, c2, holes, sort)

(** FIXME: write this in the new monad interface *)
let solve_remaining_by env sigma holes by =
  match by with
  | None -> sigma
  | Some tac ->
    let map h =
      if h.Clenv.hole_deps then None
      else
        let (evk, _) = destEvar (h.Clenv.hole_evar) in
        Some evk
    in
    (** Only solve independent holes *)
    let indep = List.map_filter map holes in
    let ist = { Geninterp.lfun = Id.Map.empty; extra = Geninterp.TacStore.empty } in
    let solve_tac = match tac with
    | Genarg.GenArg (Genarg.Glbwit tag, tac) ->
      Ftactic.run (Geninterp.interp tag ist tac) (fun _ -> Proofview.tclUNIT ())
    in
    let solve_tac = Tacticals.New.tclCOMPLETE solve_tac in
    let solve sigma evk =
      let evi =
        try Some (Evd.find_undefined sigma evk)
        with Not_found -> None
      in
      match evi with
      | None -> sigma
        (** Evar should not be defined, but just in case *)
      | Some evi ->
        let env = Environ.reset_with_named_context evi.evar_hyps env in
        let ty = evi.evar_concl in
        let c, sigma = Pfedit.refine_by_tactic env sigma ty solve_tac in
        Evd.define evk c sigma
    in
    List.fold_left solve sigma indep

let no_constraints cstrs =
  fun ev _ -> not (Evar.Set.mem ev cstrs)

let all_constraints cstrs =
  fun ev _ -> Evar.Set.mem ev cstrs

let poly_inverse sort =
  if sort then PropGlobal.inverse else TypeGlobal.inverse

type rewrite_result =
| Fail
| Identity
| Success of rewrite_result_info

type 'a strategy_input =
  { state : 'a ; (* a parameter: for instance, a state *)
    env : Environ.env ;
    envprf : Context.Rel.t;
    unfresh : Id.t list ; (* Unfresh names *)
    carrier : relation_carrier ; (* type of the rewriting *)
    term1 : constr ; (* first term (convertible to rew_from) *)
    term2 : constr ; (* second term, can be an evar or a constructed term *)
    cstr : (bool (* prop *) * constr option) ;
    evars : evars }
    
type 'a pure_strategy = { strategy :
  'a strategy_input ->
  'a * rewrite_result (* the updated state and the "result" *) }

type strategy = unit pure_strategy

(** From a proof of R from to derive R to from *)
let symmetry env sort rew =
  let { rew_evars = evars; rew_car } = rew in
  let (rew_car, rew_evars, rew_prf) = match rew_car, rew.rew_prf with
  | _, RewCast _ -> (rew_car, rew.rew_evars, rew.rew_prf)
  | Homogeneous _, RewEq (p, pty, x, y, c, rel, car) ->
     let evars, csym = get_symmetric_proof sort env evars car (mkApp (rel, [|car|])) in
     let csym = mkApp (csym, [| x; y; c |]) in
     (rew_car, evars, RewEq (p, pty, y, x, csym, rel, car))
  | Homogeneous car, RewPrf (rel, prf) ->
     (try
        let evars, symprf = get_symmetric_proof sort env evars car rel in
        let prf = mkApp (symprf, [| rew.rew_from ; rew.rew_to ; prf |]) in
        (rew_car, evars, RewPrf (rel, prf))
      with Not_found ->
           let evars, rel = poly_inverse sort env evars car rel in
           (rew_car, evars, RewPrf (rel, prf)))
  | Heterogeneous (car, car'), RewPrf (rel, prf) ->
     let evars, rel = poly_inverse sort env evars car rel in
     (Heterogeneous (car', car), evars, RewPrf (rel, prf))
   | Heterogeneous _, _ -> assert false
  in
  { rew with rew_car; rew_from = rew.rew_to;
             rew_to = rew.rew_from; rew_prf; rew_evars; }
	 
let keyed_unify env evd kop = 
  match kop with 
  | None -> fun _ -> true
  | Some kop ->
     fun cl ->
       let kc = Keys.constr_key cl in
       match kc with
       | None -> false
       | Some kc -> Keys.equiv_keys kop kc

let unify flags env sigma l r =
  let kop = Keys.constr_key l in
  if Unification.is_keyed_unification () then
    if keyed_unify env sigma kop r then
      let f1, l1 = decompose_app_vect l in
      let f2, l2 = decompose_app_vect r in
      let f1, l1, f2, l2 = adjust_app_array_size f1 l1 f2 l2 in
      let sigma = Unification.w_unify ~flags env sigma Reduction.CONV f1 f2 in
      Array.fold_left2 (fun sigma -> Unification.w_unify ~flags env sigma Reduction.CONV)
                       sigma l1 l2
    else raise Reduction.NotConvertible
  else
    Unification.w_unify ~flags env sigma Reduction.CONV l r
                        
(* Matching/unifying the rewriting rule against [t] *)
let unify_eqn (car, rel, prf, c1, c2, holes, sort)
              l2r flags env (sigma, cstrs) by t =
  try
    let left = if l2r then c1 else c2 in
    let () =
      if !Flags.debug then Printf.printf "unify_eqn %s with %s\n"
    			   (Pp.string_of_ppcmds (Printer.pr_constr_env env sigma left))
    			   (Pp.string_of_ppcmds (Printer.pr_constr_env env sigma t))
    in
    let sigma = unify flags env sigma left t in
    let sigma = Typeclasses.resolve_typeclasses ~filter:(no_constraints cstrs)
      ~fail:true env sigma in
    let evd = solve_remaining_by env sigma holes by in
    let nf c = Evarutil.nf_evar evd (Reductionops.nf_meta evd c) in
    let c1 = nf c1 and c2 = nf c2
    and rew_car = map_carrier nf car and rel = nf rel
    and prf = nf prf in
    let ty1 = Retyping.get_type_of env evd c1 in
    let ty2 = Retyping.get_type_of env evd c2 in
    let () = if not (convertible env evd ty2 ty1) then raise Reduction.NotConvertible in
    let rew_evars = evd, cstrs in
    let rew_prf =
      let hd, args = decompose_app rel in
      if is_global (Lazy.force Coqlib.coq_eq_ref) hd then
        RewEq (mkVar eq_abs_id, ty1, c1, c2, prf, hd, List.hd args)
      else RewPrf (rel, prf) in
    let rew =
      { rew_evars; rew_prf; rew_car; rew_from = c1; rew_to = c2;
        rew_decls = []; rew_local = false } in
    let rew = if l2r then rew else symmetry env sort rew in
    Some rew
  with
  | e when Class_tactics.catchable e -> None
  | Reduction.NotConvertible -> None

let unify_abs (car, rel, prf, c1, c2) l2r sort env envprf (sigma, cstrs) t =
  try
    let env = push_rel_context envprf env in
    let left = if l2r then c1 else c2 in
    (* The pattern is already instantiated, so the next w_unify is
       basically an eq_constr, except when preexisting evars occur in
       either the lemma or the goal, in which case the eq_constr also
       solved this evars *)
    let sigma = Unification.w_unify ~flags:rewrite_unif_flags env sigma
                                    Reduction.CONV left t in
    let rew_evars = sigma, cstrs in
    let rew_prf = RewPrf (rel, lift (List.length envprf) prf) in
    let rew = { rew_car = car; rew_from = c1; rew_to = c2; rew_prf; rew_evars;
                rew_decls = []; rew_local = false } in
    let rew = if l2r then rew else symmetry env sort rew in
    Some rew
  with
  | e when Class_tactics.catchable e -> None
  | Reduction.NotConvertible -> None

type rewrite_flags = { under_lambdas : bool; on_morphisms : bool }

let default_flags = { under_lambdas = true; on_morphisms = true; }

let get_opt_rew_rel = function RewPrf (rel, prf) -> Some rel | _ -> None

let poly_subrelation sort =
  if sort then PropGlobal.subrelation else TypeGlobal.subrelation

let poly_hsubrelation sort =
  if sort then PropGlobal.hsubrelation else TypeGlobal.hsubrelation

let make_subrelation env res sort car rel rel' =
  match car with
  | Homogeneous car ->
     app_poly_check env res.rew_evars (poly_subrelation sort) [|car; rel; rel'|]
  | Heterogeneous (car, car') ->
     app_poly_check env res.rew_evars (poly_hsubrelation sort) [|car; car'; rel; rel'|]
  
let resolve_subrelation env avoid car rel sort prf rel' res =
  if eq_constr rel rel' then res
  else
    let evars, app = make_subrelation env res sort car rel rel' in
    let evars, subrel = new_cstr_evar env evars app in
    let appsub = mkApp (subrel, [| res.rew_from ; res.rew_to ; prf |]) in
      { res with
	rew_prf = RewPrf (rel', appsub);
	rew_evars = evars }

(* let resolve_morphism env envprf avoid oldt m args args' (b,cstr) evars = *)
(*   let evars, morph_instance, proj, sigargs, m', args, args' = *)
(*     let first = match (Array.findi (fun _ b -> not (Option.is_empty b)) args') with *)
(*     | Some i -> i *)
(*     | None -> invalid_arg "resolve_morphism" in *)
(*     let morphargs, morphobjs = Array.chop first args in *)
(*     let morphargs', morphobjs' = Array.chop first args' in *)
(*     let appm = mkApp(m, morphargs) in *)
(*     let env = Environ.push_rel_context envprf env in *)
(*     let appmtype = Typing.unsafe_type_of env (goalevars evars) appm in *)
(*     (\* Desired signature *\) *)
(*     let evars, appmtype', signature, sigargs = *)
(*       if b then PropGlobal.build_si evars env appm morphobjs morphobjs' *)
(*                                            appmtype cstr *)
(*       else TypeGlobal.build_apprel evars env appm morphobjs morphobjs' *)
(*                                       appmtype cstr *)
(*     in *)
(*       (\* Actual signature found *\) *)
(*     let cl_args = [| appmtype' ; signature ; appm |] in *)
(*     let evars, app = *)
(*       app_poly_sort b env evars *)
(*                     (if b then PropGlobal.proper_type else TypeGlobal.proper_type) *)
(*       cl_args in *)
(*     let env' = *)
(*       let dosub, appsub = *)
(* 	if b then PropGlobal.do_subrelation, PropGlobal.apply_subrelation *)
(* 	else TypeGlobal.do_subrelation, TypeGlobal.apply_subrelation *)
(*       in *)
(*       let id = *)
(*         Tactics.fresh_id_in_env avoid (Id.of_string "do_subrelation") env *)
(*       in *)
(* 	Environ.push_named *)
(* 	  (LocalDef (id, *)
(* 	             snd (app_poly_sort b env evars dosub [||]), *)
(* 	             snd (app_poly_nocheck env evars appsub [||]))) *)
(* 	  env *)
(*     in *)
(*     let evars, morph = new_cstr_evar env' evars app in *)
(*       evars, morph, morph, sigargs, appm, morphobjs, morphobjs' *)
(*   in *)
(*   let projargs, subst, evars, respars, typeargs = *)
(*     Array.fold_left2 *)
(*       (fun (acc, subst, evars, sigargs, typeargs') x y -> *)
(* 	let (carrier, relation), sigargs = split_head sigargs in *)
(* 	match relation with *)
(* 	| Some relation -> *)
(* 	   (match y with *)
(* 	    | None -> *)
(* 	       let carrier = substl subst carrier *)
(* 	       and relation = substl subst relation in *)
(*                let env = *)
(*                  if noccur_between 0 (List.length envprf) x then env *)
(*                  else (Environ.push_rel_context envprf env) *)
(*                in *)
(* 	       let evars, proof = *)
(* 		 (if b then PropGlobal.proper_proof else TypeGlobal.proper_proof) *)
(* 		   env evars carrier relation x in *)
(* 	       [ proof ; x ; x ] @ acc, subst, evars, sigargs, x :: typeargs' *)
(* 	    | Some r -> *)
(* 	       [ snd (get_rew_prf r); r.rew_to; x ] @ acc, subst, evars, *)
(* 	       sigargs, r.rew_to :: typeargs') *)
(* 	| None -> *)
(*            match y with *)
(* 	   | None -> x :: acc, x :: subst, evars, sigargs, x :: typeargs' *)
(*            | Some r -> *)
(* 	      [ snd (get_rew_prf r); r.rew_to; x ] @ acc, subst, evars, *)
(* 	      sigargs, r.rew_to :: typeargs') *)
(*       (\* if not (Option.is_empty y) then *\) *)
(*       (\* error "Cannot rewrite inside dependent arguments of a function") *\) *)
(*       ([], [], evars, sigargs, []) args args' *)
(*   in *)
(*   let proof = applistc proj (List.rev projargs) in *)
(*   let newt = applistc m' (List.rev typeargs) in *)
(*     match respars with *)
(* 	[ a, Some r ] -> evars, proof, substl subst a, substl subst r, oldt, newt *)
(*       | _ -> assert(false) *)


(* let resolve_morphism env envprf avoid oldt m args args' (b,cstr) evars = *)
(*   let first = match (Array.findi (fun _ b -> not (Option.is_empty b)) args') with *)
(*     | Some i -> i *)
(*     | None -> invalid_arg "resolve_morphism" in *)
(*   let morphargs, morphobjs = Array.chop first args in *)
(*   let morphargs', morphobjs' = Array.chop first args' in *)
(*   let appm = mkApp(m, morphargs) in *)
(*   let env = Environ.push_rel_context envprf env in *)
(*   let appmtype = Typing.unsafe_type_of env (goalevars evars) appm in *)
(*     if b then PropGlobal.build_apprel evars env appm appmtype *)
(*                                       morphobjs morphobjs' cstr *)
(*     else TypeGlobal.build_apprel evars env appm appmtype morphobjs morphobjs' cstr *)
  
      
let coerce env avoid cstr res =
  match snd cstr with
  | None -> res
  | Some r ->
     let rel, prf = get_rew_prf res in
     resolve_subrelation env avoid res.rew_car rel (fst cstr) prf r res

let apply_rule unify loccs : int pure_strategy =
  let (nowhere_except_in,occs) = convert_occs loccs in
  let is_occ occ =
    if nowhere_except_in
    then List.mem occ occs
    else not (List.mem occ occs)
  in
  { strategy = fun { state = occ; env ; envprf ; unfresh ;
		   carrier = ty ; term1 = t ; term2 = t'; cstr ; evars } ->
      let unif =
	if isEvar t then None else unify env envprf evars t in
	match unif with
	| None -> (occ, Fail)
        | Some rew ->
	   let occ = succ occ in
	    if not (is_occ occ) then (occ, Fail)
	    else if eq_constr t rew.rew_to then (occ, Identity)
	    else
	      let res = Success (coerce env unfresh cstr rew) in
              (occ, res)
    }

let set_rule unify n loccs : int pure_strategy =
  let (nowhere_except_in,occs) = convert_occs loccs in
  let is_occ occ =
    if nowhere_except_in
    then List.mem occ occs
    else not (List.mem occ occs)
  in
  { strategy = fun { state = occ; env ; envprf ; unfresh ;
		     term1 = t ; carrier = ty ; cstr ; evars } ->
      let unif =
	if isEvar t then None else unify (push_rel_context envprf env) evars t in
	match unif with
	| None -> (occ, Fail)
        | Some rew ->
	   let occ = succ occ in
	    if not (is_occ occ) then (occ, Fail)
	    else
              let decl = (n, rew.rew_from, get_rew_car ty) in
	      let res = { rew with rew_to = mkVar n; rew_prf = RewCast DEFAULTcast;
                                   rew_decls = [decl] } in
              (occ, Success res)
    }

let e_app_poly env evars f args =
  let evars', c = app_poly_nocheck env !evars f args in
    evars := evars';
    c

let make_leibniz_proof env c ty r =
  let evars = ref r.rew_evars in
  let prf =
    match r.rew_car, r.rew_prf with
    | Homogeneous car, RewPrf (rel, prf) ->
	let rel = e_app_poly env evars coq_eq [| ty |] in
	let prf =
	  e_app_poly env evars coq_f_equal
		[| car; ty;
		   mkLambda (Anonymous, car, c);
		   r.rew_from; r.rew_to; prf |]
	in RewPrf (rel, prf)
    | Homogeneous _, RewCast k -> r.rew_prf
    | Homogeneous _, RewEq _ ->
       let rel, prf = get_rew_prf r in
       RewPrf (rel, prf)
    | Heterogeneous _, _ -> assert false
  in
    { rew_car = Homogeneous ty; rew_evars = !evars;
      rew_from = subst1 r.rew_from c; rew_to = subst1 r.rew_to c; rew_prf = prf;
      rew_decls = []; rew_local = false }

let reset_env env =
  let env' = Global.env_of_context (Environ.named_context_val env) in
    Environ.push_rel_context (Environ.rel_context env) env'

let fold_match ?(force=false) env sigma c =
  let (ci, p, c, brs) = destCase c in
  let cty = Retyping.get_type_of env sigma c in
  let dep, pred, exists, (sk,eff) =
    let env', ctx, body =
      let ctx, pred = decompose_lam_assum p in
      let env' = Environ.push_rel_context ctx env in
	env', ctx, pred
    in
    let sortp = Retyping.get_sort_family_of env' sigma body in
    let sortc = Retyping.get_sort_family_of env sigma cty in
    let dep = not (noccurn 1 body) in
    let pred = if dep then p else
	it_mkProd_or_LetIn (subst1 mkProp body) (List.tl ctx)
    in
    let sk =
      if sortp == InProp then
	if sortc == InProp then
	  if dep then case_dep_scheme_kind_from_prop
	  else case_scheme_kind_from_prop
	else (
	  if dep
	  then case_dep_scheme_kind_from_type_in_prop
	  else case_scheme_kind_from_type)
      else ((* sortc <> InProp by typing *)
	if dep
	then case_dep_scheme_kind_from_type
	else case_scheme_kind_from_type)
    in
    let exists = Ind_tables.check_scheme sk ci.ci_ind in
      if exists || force then
	dep, pred, exists, Ind_tables.find_scheme sk ci.ci_ind
      else raise Not_found
  in
  let app =
    let ind, args = Inductive.find_rectype env cty in
    let pars, args = List.chop ci.ci_npar args in
    let meths = List.map (fun br -> br) (Array.to_list brs) in
      applist (mkConst sk, pars @ [pred] @ meths @ args @ [c])
  in
    sk, (if exists then env else reset_env env), app, eff

let unfold_match env sigma sk app =
  match kind_of_term app with
  | App (f', args) when eq_constant (fst (destConst f')) sk ->
      let v = Environ.constant_value_in (Global.env ()) (sk,Univ.Instance.empty)(*FIXME*) in
	Reductionops.whd_beta sigma (mkApp (v, args))
  | _ -> app

let new_relation_evar prop env evd ty =
  let f = if prop then PropGlobal.new_relation_evar else TypeGlobal.new_relation_evar in
  f env evd ty

let new_hrelation_evar prop env evd ty =
  let f = if prop then PropGlobal.new_hrelation_evar
          else TypeGlobal.new_hrelation_evar in
  f env evd ty

let mk_related prop =
  if prop then PropGlobal.mk_related
          else TypeGlobal.mk_related

let mk_relation_carrier_evar prop =
  if prop then PropGlobal.mk_relation_carrier_evar
          else TypeGlobal.mk_relation_carrier_evar
    
let is_rew_prf = function RewPrf _ -> true | _ -> false
let is_rew_eq = function RewEq _ -> true | _ -> false

let mkProd_car n t = map_carrier (fun car -> mkProd (n, t, car))

(** Requires transitivity of the rewrite step, if not a reduction.
    Not tail-recursive. *)

let get_right_rew_car = function
  | Homogeneous c -> c
  | Heterogeneous (c, c') -> c'
                                 
let transitivity state env envprf unfresh prop (res : rewrite_result_info) (next : 'a pure_strategy) :
      'a * rewrite_result =
  let car = (get_right_rew_car res.rew_car) in
  (* let evars, term2 = new_cstr_evar env res.rew_evars car in *)
  let state, nextres =
    next.strategy { state ; env ; envprf ; unfresh ;
		    term1 = res.rew_to ; carrier = Homogeneous car ;
                    term2 = res.rew_to ;
		    cstr = (prop, get_opt_rew_rel res.rew_prf) ;
		    evars = res.rew_evars }
  in
  let res =
    match nextres with
    | Fail -> Fail
    | Identity -> Success res
    | Success res' ->
      match res.rew_prf with
      | RewCast c -> Success { res' with rew_from = res.rew_from;
                                        rew_local = res.rew_local && res'.rew_local}
      | _ ->
	match res'.rew_prf with
	| RewCast _ -> Success { res with rew_to = res'.rew_to }
	| _ ->
	   match res.rew_prf, res'.rew_prf with
	   | RewEq (p, pty, t1, t2, c, rel, car),
	     RewEq (p', pty', t1', t2', c', rel', car') when eq_constr c c' ->
	      let prf' = RewEq (p, pty, t1, t2, c, rel, car) in
	      let res' = { res with rew_to = res'.rew_to; rew_prf = prf';
                                    rew_local = res.rew_local && res'.rew_local} in
	      Success res'
	   | _ ->
	      let rew_rel, rew_prf = get_rew_prf res in
	      let (res'_rel, res'_prf) = get_rew_prf res' in
	      let trans =
		if prop then PropGlobal.transitive_type
		else TypeGlobal.transitive_type
	      in
	      let evars, prfty =
		app_poly_sort prop env res'.rew_evars trans
                              [| (*FIXME *) get_rew_car res.rew_car; rew_rel |]
	      in
	      let evars, prf = new_cstr_evar env evars prfty in
	      let prf = mkApp (prf, [|res.rew_from; res'.rew_from; res'.rew_to;
				      rew_prf; res'_prf |])
	      in Success { res' with rew_from = res.rew_from;
				     rew_evars = evars;
                                     rew_prf = RewPrf (res'_rel, prf);
                                     rew_local = res.rew_local && res'.rew_local}
  in state, res

(** Rewriting strategies.

    Inspired by ELAN's rewriting strategies:
    http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.21.4049
*)

module Strategies =
  struct

    let fail : 'a pure_strategy =
      { strategy = fun { state } -> state, Fail }

    let id : 'a pure_strategy =
      { strategy = fun { state } -> state, Identity }

    let refl : 'a pure_strategy =
      { strategy =
	fun { state ; env ;
	      term1 = t ; carrier ;
	      cstr = (prop,cstr) ; evars } ->
        let ty = get_rew_car carrier in
	let evars, rel = match cstr with
	  | None ->
	    let mkr = if prop then PropGlobal.mk_relation else TypeGlobal.mk_relation in
	    let evars, rty = mkr env evars ty in
	      new_cstr_evar env evars rty
	  | Some r -> evars, r
	in
	let evars, proof =
	  let proxy =
	    if prop then PropGlobal.proper_proxy_type
	    else TypeGlobal.proper_proxy_type
	  in
	  let evars, mty = app_poly_sort prop env evars proxy [| ty ; rel; t |] in
	    new_cstr_evar env evars mty
	in
	let res = Success { rew_car = Homogeneous ty; rew_from = t; rew_to = t;
			    rew_prf = RewPrf (rel, proof); rew_evars = evars;
                            rew_decls = []; rew_local = false }
	in state, res
      }

    let progress (s : 'a pure_strategy) : 'a pure_strategy = { strategy =
      fun input ->
	let state, res = s.strategy input in
	  match res with
	  | Fail -> state, Fail
	  | Identity -> state, Fail
	  | Success r -> state, Success r
							     }

    let seq first snd : 'a pure_strategy = { strategy =
      fun ({ env ; envprf; unfresh ; cstr } as input) ->
	let state, res = first.strategy input in
	  match res with
	  | Fail -> state, Fail
	  | Identity -> snd.strategy { input with state }
	  | Success res -> transitivity state env envprf unfresh (fst cstr) res snd
					   }

    let choice fst snd : 'a pure_strategy = { strategy =
      fun input ->
	let state, res = fst.strategy input in
	  match res with
	  | Fail -> snd.strategy { input with state }
	  | Identity | Success _ -> state, res
					    }

    let try_ str : 'a pure_strategy = choice str id

    let check_interrupt str input =
      Control.check_for_interrupt ();
      str input

    let fix (f : 'a pure_strategy -> 'a pure_strategy) : 'a pure_strategy =
      let rec aux input = (f { strategy = fun input -> check_interrupt aux input }).strategy input in
      { strategy = aux }

    let repeat (s : 'a pure_strategy) : 'a pure_strategy =
      fix (fun any -> try_ (seq s any))

    let many (s : 'a pure_strategy) : 'a pure_strategy =
      seq s (repeat s)
          
    let lemmas f cs : 'a pure_strategy =
      List.fold_left (fun tac (l,l2r,by) ->
	choice tac (f true l2r rewrite_unif_flags (fun env -> l) by AllOccurrences))
	fail cs

    let inj_open hint = (); fun sigma ->
      let ctx = Evd.evar_universe_context_of hint.Autorewrite.rew_ctx in
      let sigma = Evd.merge_universe_context sigma ctx in
      (sigma, (hint.Autorewrite.rew_lemma, NoBindings))

    let old_hints f (db : string) : 'a pure_strategy =
      let rules = Autorewrite.find_rewrites db in
	lemmas f
	  (List.map (fun hint -> (inj_open hint, hint.Autorewrite.rew_l2r,
				  hint.Autorewrite.rew_tac)) rules)

    let hints f (db : string) : 'a pure_strategy = { strategy =
      fun ({ term1 = t } as input) ->
      let rules = Autorewrite.find_matches db t in
      let lemma hint = (inj_open hint, hint.Autorewrite.rew_l2r,
			hint.Autorewrite.rew_tac) in
      let lems = List.map lemma rules in
      (lemmas f lems).strategy input
						 }

    let reduce (r : Redexpr.red_expr) : 'a pure_strategy = { strategy =
	fun { state = state ; env = env ; term1 = t ; carrier ; cstr = cstr ; evars = evars } ->
          let rfn, ckind = Redexpr.reduction_of_red_expr env r in
          let sigma = Sigma.Unsafe.of_evar_map (goalevars evars) in
	  let Sigma (t', sigma, _) = rfn.Reductionops.e_redfun env sigma t in
	  let evars' = Sigma.to_evar_map sigma in
	    if eq_constr t' t then
	      state, Identity
	    else
	      state, Success { rew_car = carrier; rew_from = t; rew_to = t';
			       rew_prf = RewCast ckind;
			       rew_evars = evars', cstrevars evars;
                               rew_decls = []; rew_local = false } }

    let fold_glob c : 'a pure_strategy = { strategy =
      fun { state ; env ; term1 = t ; carrier ; cstr ; evars } ->
(* 	let sigma, (c,_) = Tacinterp.interp_open_constr_with_bindings is env (goalevars evars) c in *)
	let sigma, c = Pretyping.understand_tcc env (goalevars evars) c in
	let unfolded =
	  try Tacred.try_red_product env sigma c
	  with e when noncritical e ->
            error "fold: the term is not unfoldable !"
	in
	  try
	    let sigma = Unification.w_unify env sigma Reduction.CONV ~flags:(Unification.elim_flags ()) unfolded t in
	    let c' = Evarutil.nf_evar sigma c in
	      state, Success { rew_car = carrier; rew_from = t; rew_to = c';
			       rew_prf = RewCast DEFAULTcast;
			       rew_evars = (sigma, snd evars);
                               rew_decls = []; rew_local = false }
	  with e when noncritical e -> state, Fail
					 }
                                          
    let pattern_of_constr_pattern pat hd : 'a pure_strategy =
      { strategy =
	fun { state; env; term1 = t; carrier; evars } ->
        let sigma = fst evars in
        let () =
          if !Flags.debug then
            Printf.printf "pattern matching: %s and %s\n"
	    		  (Pp.string_of_ppcmds (Printer.pr_constr_pattern_env env sigma pat))
	    		  (Pp.string_of_ppcmds (Printer.pr_constr_env env sigma t)) in
	try let _map = Constr_matching.matches env (fst evars) pat t in
	    state, Identity
	with Constr_matching.PatternMatchingFailure ->
          try (* Check for canonical structure solution *)
            match hd with
            | None -> state, Fail
            | Some gr ->
               let cspat, _, _ = Recordops.cs_pattern_of_constr t in
               let _ = Recordops.lookup_canonical_conversion (gr, cspat) in
               state, Identity
          with Not_found -> state, Fail }

    let pattern_of_constr env sigma c : 'a pure_strategy =
      let pat = Patternops.pattern_of_constr env sigma c in
      let globhead =
        try
          let gr = global_of_constr (fst (destApp c)) in
          let _ = Recordops.find_projection gr in
          Some gr
        with Not_found -> None
      in pattern_of_constr_pattern pat globhead

    let pattern p : 'a pure_strategy =
      let sigma, env = Lemmas.get_current_context () in
      let sigma, c = Pretyping.understand_tcc env sigma p in
      pattern_of_constr env sigma c
end

let decompose_app_n i c =
  let hd, args = decompose_app_vect c in
  assert(Array.length args >= i);
  mkApp (hd, Array.sub args 0 (Array.length args - i))

let decompose_app_evar env evars m ty args term =
  let hd, _ = decompose_app term in
  match kind_of_term hd with
  | Evar _ ->
     let (evars, args', ty') =
       Array.fold_left (fun (evars, args', ty') a ->
           let na, dom, codom = destProd ty' in
           let evars, arg' = new_cstr_evar env evars dom in
           (evars, arg' :: args', subst1 arg' codom))
                       (evars, [], ty) args
     in
     let newt = mkApp (m, Array.rev_of_list args') in
     evars, newt, ty'
  | _ -> evars, term, get_type_of_env env evars term

let make_carrier t t' =
  if eq_constr t t' then Homogeneous t
  else Heterogeneous (t, t')

let is_homogeneous = function
  | Homogeneous _ -> true
  | Heterogeneous _ -> false
                     
let rec subterm all flags (s : 'a pure_strategy) : 'a pure_strategy =
  let rec aux { state ; env ; envprf; unfresh;
		term1 = t ; term2; carrier ; cstr = (prop, cstr) ; evars } =
    let cstr' = Option.map (fun c -> ((*FIXME*) get_rew_car carrier, Some c)) cstr in
    if !Flags.debug then
      (Printf.printf "subterm on %s\n%!" (Pp.string_of_ppcmds (Printer.pr_constr_env (Environ.push_rel_context envprf env) (goalevars evars) t));
       Printf.printf "rel_context: %s\n%!" (Pp.string_of_ppcmds (Printer.pr_rel_context env (goalevars evars) envprf)));
    let rel n =
      if n <= List.length envprf then
        try
          let decl = Context.Rel.lookup (n - 2) envprf in
          let relty = decompose_app_n 2 (Context.Rel.Declaration.get_type decl) in
          let prf = RewPrf (lift (n - 2) relty, mkRel (n - 2)) in
          state, Success { rew_from = mkRel n; rew_to = mkRel (n - 1);
        		   rew_prf = prf; rew_car = carrier;
                           rew_decls = []; rew_evars = evars; rew_local = true }
        with e (* decompose_app failed *) -> state, Fail
      else state, Fail
    in
    let app m args =
      let mty = get_type_of env envprf evars m in
      let rewrite_arg (state, (acc, evars, envprf, lifti, unfresh, appm, appm',
                               ty, ty', progress))
                      arg =
        let deprew, progress = progress in
        let env' = push_rel_context envprf env in
        let na, carrier, ty, ty' =
          let ty = whd_all env' (goalevars evars) ty in
          let ty' = whd_all env' (goalevars evars) ty' in
          match kind_of_term ty, kind_of_term ty' with
          | Prod (na, t, b), Prod (na', t', b') ->
             na, make_carrier t t', b, b'
          | _ -> assert false
        in
        let arg' = lift (snd lifti) arg in
        let same progress =
          let (evars, arg2), deprew =
            match carrier with
            | Homogeneous car -> (evars, arg'), deprew
            | Heterogeneous (car, car') ->
               new_goal_evar env evars car', true
          in
          (None :: acc, evars, envprf, lifti, unfresh,
           mkApp (appm, [| arg' |]), mkApp (appm', [| arg2 |]),
           subst1 arg' ty, subst1 arg2 ty', (deprew, progress))
        in
	if not (Option.is_empty progress) && not all then
	  state, same progress
	else
	  let state, res = s.strategy { state ; env ; envprf ;
					unfresh ;
					term1 = arg' ;
                                        term2 = arg' ;
                                        carrier;
					cstr = (prop,None) ;
					evars = evars } in
	  let res' =
	    match res with
	    | Fail -> same progress
	    | Identity ->
	       let progress =
                 if Option.is_empty progress then Some false else progress in
               same progress
	    | Success r ->
               (* if noccurn 1 ty && is_homogeneous carrier && not deprew then *)
               (*   (\* Fast path: no dependency *\) *)
               (*   (Some r :: acc, evars, envprf, lifti, unfresh, *)
               (*    appm, appm', subst1 mkProp ty, subst1 mkProp ty', *)
               (*    (deprew, Some true)) *)
               (* else *)
                 let rel, prf = get_rew_prf r in
                 let evars, rel' =
                   mk_related prop env r.rew_evars r.rew_car rel r.rew_from r.rew_to in
                 let name =
                   let id = match na with Anonymous -> Id.of_string "H" | Name na -> na in
                   Tactics.fresh_id_in_env unfresh (add_suffix id "_rew") env in
                 let unfresh = name :: unfresh in
                 let hyp = Context.Rel.Declaration.LocalDef (Name name, prf, rel') in
                 let envprf = hyp :: envprf in
                 let subst, lifti = lifti in
                 let subst = substl subst prf :: subst in
	         (Some r :: acc, evars, envprf, (subst, succ lifti), unfresh,
                  lift 1 (mkApp (appm, [| r.rew_from |])),
                  lift 1 (mkApp (appm', [| r.rew_to |])),
                  lift 1 (subst1 r.rew_from ty), lift 1 (subst1 r.rew_to ty'),
                  (not (noccurn 1 ty) || deprew, Some true))
	  in state, res'
      in
      let args_progress args' =
        Array.fold_left
	  (fun acc r ->
	    match acc with
	    | None ->
               (match r with
                | None -> acc
                | Some r -> Some (r.rew_local, r.rew_prf))
	    | Some (local, (RewPrf _ as prf)) -> 
               (match r with
                | None -> acc
                | Some r -> Some (local && r.rew_local, prf))
            | Some (local, RewCast _) ->
               (match r with
                | None -> acc
                | Some r -> Some (local && r.rew_local, r.rew_prf))
	    | Some (local, (RewEq (_, _, _, _, c, _, _) as prf)) ->
	       (match r with
		| None -> acc
		| Some res ->
		   (match res.rew_prf with
		    | RewPrf _ as x -> Some (local && res.rew_local, x)
		    | RewCast _ -> Some (local && res.rew_local, prf)
		    | RewEq (_, _, _, _, c', _, _) ->
		       if eq_constr c c' then acc
		       else let c, rel = get_rew_prf res in
                            Some (local && res.rew_local, RewPrf (c, rel)))))
	  None args'
      in
      let treat_args (args', evars', envprf', lifti, unfresh',
                      appm, appm', ty, ty', (deprew, progress)) =
	match progress with
	| None -> Fail
	| Some false -> Identity
	| Some true ->
	   let args' = Array.of_list (List.rev args') in
	   match args_progress args', deprew with
	   | None, _ -> Identity
	   | Some (local, RewPrf _), _
           | Some (local, RewEq _), true ->
	      if !Flags.debug then
                Printf.printf "app: %s -> %s \n%!" (string_of_constr envprf env evars' appm)
                              (string_of_constr envprf env evars' appm');  
              let env' = push_rel_context envprf' env in
              let appcar = make_carrier ty ty' in
              let subst, lifti = lifti in
	      let evars', prf, car, rel, c1, c2 =
	        let evars, rel =
                  match cstr' with
	          | None | Some (_, None) ->
                     mk_relation_carrier_evar prop env' evars' appcar
	          | Some (t, Some rel) -> evars', lift lifti rel
                in
                let evars, goal = mk_related prop env' evars appcar rel appm appm' in
                let () =
                  if !Flags.debug then
                    Printf.printf "build_signature finished: %s\n%!"
                                  (string_of_constr_env env' evars goal) in
                let env' =
                  let dosub, appsub =
	            if prop then PropGlobal.do_subrelation, PropGlobal.apply_subrelation
	            else TypeGlobal.do_subrelation, TypeGlobal.apply_subrelation
                  in
                  let id =
                    Tactics.fresh_id_in_env [] (Id.of_string "do_subrelation") env'
                  in
	          Environ.push_named
	            (LocalDef (id,
	                       snd (app_poly_sort prop env' evars dosub [||]),
	                       snd (app_poly_nocheck env' evars appsub [||])))
	            env'
                in
                let evars, prf = new_cstr_evar env' evars goal in
                evars, substl subst prf, map_carrier (substl subst) appcar,
                substl subst rel, substl subst appm, substl subst appm'
	      in       
	      if !Flags.debug then
                Printf.printf "resolved proof: %s, car: %s, rel %s, from: %s to %s\n"
                              (string_of_constr envprf env evars' prf)
                              (string_of_constr envprf env evars' (get_rew_car car))
                              (string_of_constr envprf env evars' rel)
                              (string_of_constr envprf env evars' c1)
                              (string_of_constr envprf env evars' c2)
              ;
	      let res = { rew_car = car; rew_from = c1;
			  rew_to = c2; rew_prf = RewPrf (rel, prf);
			  rew_evars = evars'; rew_decls = []; rew_local = local }
	      in Success res
	   | Some (local, r), _ ->
	      if !Flags.debug then
                Printf.printf "app: %s ty: %s \n" (string_of_constr envprf env evars' appm) (string_of_constr envprf env evars ty);
	      let args'' = Array.map2
			     (fun aorig anew ->
			       match anew with None -> aorig
					     | Some r -> r.rew_to) args args'
	      in
	      let rew_prf =
		match r with
		| RewEq (_, _, t1, t2, c, rel, ty') ->
		   let predargs = Array.map2
		      		    (fun orig anew ->
		      		      match anew with
		      		      | None -> orig
		      		      | Some r ->
		      			 match r.rew_prf with
		      			 | RewEq (p, ty, _, _, c, rel, _) -> p
		      			 | RewPrf _ -> assert false
		      			 | RewCast _ -> r.rew_to)
		      		    args args'
		   in
  		   let pred = mkApp (m, predargs) in
		   RewEq (pred, ty, t1, t2, c, rel, ty')
		| RewCast _ -> RewCast DEFAULTcast
		| _ -> assert false
	      in
              let to_ = mkApp (m, args'') in
	      let res = { rew_car = (* Equality case *) Homogeneous ty;
                          rew_from = t;
			  rew_to = to_; rew_prf;
			  rew_evars = evars'; rew_decls = [];
                          rew_local = local}
	      in Success res
      in
      let rewrite_args state m' mty' success =
        (* let evars, term2, ty2 = decompose_app_evar env evars m ty args term2 in *)
	let state, argsres =
	  Array.fold_left rewrite_arg
	                  (state, ([], evars, envprf, ([], 0), unfresh,
                                   m, m', mty, mty', (false, success)))
                          args
	in
        state, treat_args argsres
      in
      if flags.on_morphisms then
	let evars, cstr', m, mty, argsl, args =
	  let argsl = Array.to_list args in
	  let lift = if prop then PropGlobal.lift_cstr else TypeGlobal.lift_cstr in
	  match lift env evars argsl m mty None with
	  | Some (evars, cstr', m, mty, args) ->
	     evars, Some cstr', m, mty, args, Array.of_list args
	  | None -> evars, None, m, mty, argsl, args
	in
        (* let rew_evars, mty' = new_cstr_type_evar env evars in *)
        (* let rew_evars, m' = new_cstr_evar env evars mty' in *)
	let state, m' = s.strategy { state ; env ; envprf; unfresh ;
				     term1 = m ; carrier = Homogeneous mty;
                                     term2 = m;
				     cstr = (prop, cstr') ; evars } in
	match m' with
	| Fail -> rewrite_args state m mty None (* Standard path, try rewrite on arguments *)
	| Identity -> rewrite_args state m mty (Some false)
	| Success r ->
	   (* We rewrote the function and get a proof of pointwise rel
               for the arguments. We just apply it. 
               TODO: might be a respectful proof, check *)
	   let evars, prf = match r.rew_prf with
	     | RewPrf (rel, prf) ->
		let app = if prop then PropGlobal.apply_pointwise
			  else TypeGlobal.apply_pointwise
		in
                let env =
                  (Environ.push_rel_context envprf env)
                in
		let evars, rel, prf = app env r.rew_evars rel prf argsl in
		evars, RewPrf (rel, prf)
	     | x -> r.rew_evars, x
	   in
           let rew_car = get_rew_car r.rew_car in
           let car' = Reductionops.hnf_prod_appvect env (goalevars evars) rew_car args in
	   let res =
	     { rew_car = Homogeneous car';
	       rew_from = mkApp(r.rew_from, args); rew_to = mkApp(r.rew_to, args);
	       rew_prf = prf; rew_evars = evars; rew_decls = [];
               rew_local = r.rew_local }
	   in
	   let res =
	     match prf with
	     | RewPrf (rel, prf) ->
		Success (coerce env unfresh (prop,cstr) res)
	     | _ -> Success res
	   in state, res
      else rewrite_args state m mty None
    in
    let prod n dom codom =
      let pointwise = noccurn 1 codom in
      let (evars', app), unfold =
        if pointwise then
          let codom = subst1 mkProp codom in
          let tdom = get_type_of env envprf evars dom in
          let tcodom = get_type_of env envprf evars codom in
          let arr =
            if eq_constr tdom mkProp then PropGlobal.arrow_morphism
            else TypeGlobal.arrow_morphism
          in arr env evars tdom tcodom dom codom
        else
          let lam = mkLambda (n, dom, codom) in
	  if eq_constr (get_rew_car carrier) mkProp then
	    let evars, app = app_poly_sort prop env evars coq_all [| dom; lam |] in
            (evars, app), TypeGlobal.unfold_all
	  else
	    let forall =
              if prop then PropGlobal.coq_forall else TypeGlobal.coq_forall in
            let evars, app = app_poly_sort prop env evars forall [| dom; lam |] in
            (evars, app), TypeGlobal.unfold_forall
      in
      let state, res = aux { state ; env ; envprf; unfresh ;
			     term1 = app ; carrier;
                             term2 = app ;
			     cstr = (prop,cstr) ; evars = evars' } in
      let res =
	match res with
	| Success r -> Success { r with rew_to = unfold r.rew_to }
	| Fail | Identity -> res
      in state, res
    in
    let lambda n t b =
      let _pointwise = noccurn 1 b in
      let prfenv = push_rel_context envprf env in
      let evars, t', b' =
        match carrier with
        | Homogeneous car -> evars, t, b
        | Heterogeneous (car, car') ->
           (* let n', t', b' = destLambda term2 in (\* FIXME can fail *\) *)
           let n', t', b' = destProd car' in (* FIXME can fail *)
           evars, t', b'
      in
      let n = match n with
        | Anonymous -> Tactics.fresh_id_in_env unfresh (Id.of_string "H") prfenv
        | Name id -> id
      in
      let unfresh = n :: unfresh in
      let n' = Tactics.fresh_id_in_env unfresh n prfenv in
      let unfresh = n' :: unfresh in
      let n'' = Tactics.fresh_id_in_env unfresh n prfenv in
      let unfresh = n'' :: unfresh in
      let open Context.Rel.Declaration in
      let relctx = [LocalAssum (Name n'', lift 1 t'); LocalAssum (Name n', t)] in
      let evars, relt, relty =
        (* Make the relation typeable in env, if the type is not
           too dependent *)
        let len = List.length envprf in
        let car = get_rew_car carrier in
        let codom =
          try pi3 (destProd car)
          with e -> get_type_of env (LocalAssum (Name n, t) :: envprf) evars b in 
        let env, lifti =
          if noccur_between 1 (len + 1) codom then env, len + 2
          else prfenv, 2
        in
        let evars, relt = new_hrelation_evar prop env evars t t' in
        evars, relt, lift lifti relt in
      let relty = mkApp (relty, [|mkRel 2; mkRel 1|]) in
      let rname = Tactics.fresh_id_in_env unfresh (Id.of_string "R") env in
      let unfresh = rname :: unfresh in
      let relname = Name rname in
      let relctx = LocalAssum (relname, relty) :: relctx in
      let envprf' = relctx @ envprf in
      let b = lift 2 b in
      let b' = liftn 1 2 (lift 1 b) in
      let bty = get_type_of env envprf' evars b in
      let bty' = get_type_of env envprf' evars b' in
      let carrier = make_carrier bty bty' in
      let unlift = if prop then PropGlobal.unlift_cstr else TypeGlobal.unlift_cstr in

      let rec guarded_rew called =
        { strategy = fun ({ state; term1; evars; env; envprf } as input) ->
                     if !Flags.debug then
                       (let env = Environ.push_rel_context envprf env in
                        Printf.printf "guarded rewrite in %s for %s\n%!"
                                      (Pp.string_of_ppcmds
                                         (Printer.pr_constr_env env (goalevars evars)
                                                                term1))
                                      (Id.to_string n));
                     if called || not (noccurn 3 term1) then
                       (subterm true flags (guarded_rew true)).strategy input
                     else state, Identity}
      in
      let input =
        { state ; env ; envprf = envprf'; unfresh ;
	  carrier ; term1 = b ; term2 = b'; 
	  cstr = (prop, unlift env evars cstr) ; evars }
      in
      let state', b' = (Strategies.seq s (guarded_rew false)).strategy input in
      match b' with
      | Fail | Identity -> state', b'
      | Success r when r.rew_local && Context.Rel.length envprf == 0 ->
         (* If we only rewrote with the local proofs, ignore *)
         state, Identity
      | Success r ->
         let rew_from = mkLambda(Name n, t, substl [mkRel 1; mkRel 1] r.rew_from) in
         let rew_to = mkLambda(Name n, t', substl [mkRel 1; mkRel 1] r.rew_to) in
         let rew_car = 
           match r.rew_car with
           | Homogeneous c ->
              if eq_constr t t' then Homogeneous (mkProd (Name n, t, c))
              else Heterogeneous (mkProd (Name n, t, c),
                                  mkProd (Name n, t', c))
           | Heterogeneous (c, c') -> Heterogeneous (mkProd (Name n, t, c),
                                                    mkProd (Name n, t', c'))
         in
	 (match r.rew_prf with
	  | RewPrf _
	    | RewEq _ ->
	     let (rel, prf) = get_rew_prf r in
             let rel = it_mkLambda_or_LetIn rel relctx in
	     let point =
	       if prop then PropGlobal.pointwise_or_dep_relation false
	       else TypeGlobal.pointwise_or_dep_relation false
	     in
	     let evars, rel =
               point env r.rew_evars (Name n') t t' relt r.rew_car rel in
             let env = Environ.push_rel_context envprf env in
             let prf = it_mkLambda_or_LetIn prf relctx in
             if !Flags.debug then
               (Printf.printf "is_pointwise: old rew_to: %s\n%!"
                              (Pp.string_of_ppcmds
                                 (Printer.pr_constr_env env (goalevars evars)
                                                        r.rew_to));
                Printf.printf "is_pointwise: rew_prf: %s, rel : %s\n%!"
                              (Pp.string_of_ppcmds
                                 (Printer.pr_constr_env env (goalevars evars)
                                                        prf))
                              (string_of_constr_env env evars rel));
	     state', Success { r with rew_from; rew_to; rew_car;
                                      rew_prf = RewPrf (rel, prf);
                                      rew_evars = evars }
	  | x ->
             state', Success { r with rew_car; rew_from; rew_to })
    in
    let case ci p c brs =
      let cty = get_type_of env envprf evars c in
      let evars', eqty = app_poly_sort prop env evars coq_eq [| cty |] in
      let cstr' = Some eqty in
      let ty = (get_rew_car carrier) in
      (* let evars', term2 = new_cstr_evar env evars ty in *)
      let state, c' = s.strategy { state ; env ; envprf; unfresh ;
				   carrier = Homogeneous cty;
                                   term1 = c ; term2 = c;
				   cstr = (prop, cstr') ; evars = evars' } in
      let state, res =
	match c' with
	| Success r ->
	   let case = mkCase (ci, lift 1 p, mkRel 1, Array.map (lift 1) brs) in
	   let res = make_leibniz_proof env case ty r in
	   state, Success (coerce env unfresh (prop,cstr) res)
	| Fail | Identity ->
	   if Array.for_all (Int.equal 0) ci.ci_cstr_ndecls then
	     let evars', eqty = app_poly_sort prop env evars coq_eq [| ty |] in
	     let cstr = Some eqty in
	     let state, found, brs' =
               Array.fold_left
		 (fun (state, found, acc) br ->
		   if not (Option.is_empty found) then
		     (state, found, fun x -> lift 1 br :: acc x)
		   else
		     let state, res = s.strategy { state ; env ; envprf; unfresh ;
						   term1 = br ; term2 = br;
                                                   carrier = Homogeneous ty ;
						   cstr = (prop,cstr) ; evars } in
		     match res with
		     | Success r -> (state, Some r, fun x -> mkRel 1 :: acc x)
		     | Fail | Identity -> (state, None, fun x -> lift 1 br :: acc x))
		 (state, None, fun x -> []) brs
	     in
	     match found with
	     | Some r ->
		let ctxc = mkCase (ci, lift 1 p, lift 1 c, Array.of_list (List.rev (brs' c'))) in
		state, Success (make_leibniz_proof env ctxc ty r)
	     | None -> state, c'
	   else
	     match try Some (fold_match env (goalevars evars) t) with Not_found -> None with
	     | None -> state, c'
	     | Some (cst, _, t', eff (*FIXME*)) ->
		let state, res = aux { state ; env ; envprf; unfresh ;
				       carrier = Homogeneous ty ;
                                       term1 = t' ; term2 = t';
				       cstr = (prop,cstr) ; evars } in
		let res =
		  match res with
		  | Success prf ->
		     Success { prf with
		               rew_from = t;
		               rew_to = unfold_match env (goalevars evars) cst prf.rew_to }
		  | x' -> c'
		in state, res
      in
      let res =
	match res with
	| Success r ->
	   Success (coerce env unfresh (prop,cstr) r)
	| Fail | Identity -> res
      in state, res
    in
    match kind_of_term t with
    | Rel n -> rel n
    | App (m, args) -> app m args
    | Prod (n, dom, codom) -> prod n dom codom
    | Lambda (n, t, b) when flags.under_lambdas -> lambda n t b              
    | Case (ci, p, c, brs) -> case ci p c brs
    | _ -> state, Fail
  in { strategy = aux }

    (* | Prod (n, x, b) when  -> *)
    (*    let tx = get_type_of env envprf evars x in *)
    (*    let tb = get_type_of env envprf' evars b in *)
    (*    let arr = if prop then PropGlobal.arrow_morphism *)
    (*              else TypeGlobal.arrow_morphism *)
    (*    in *)
    (*    let (evars', mor), unfold = arr env evars tx tb x b in *)
    (*    let state, res = aux { state ; env ; envprf; unfresh ; *)
    (*     		      term1 = mor ; ty1 = ty ; *)
    (*     		      cstr = (prop,cstr) ; evars = evars' } in *)
    (*    let res = *)
    (*      match res with *)
    (*      | Success r -> Success { r with rew_to = unfold r.rew_to } *)
    (*      | Fail | Identity -> res *)
    (*    in state, res *)
       
                     (* let evars, rel = app_poly_check env r.rew_evars coq_eq [| t |] in *)
		     (* let ev = destEvar relt in *)
                     (* (Evd.define (fst ev) rel (goalevars evars), cstrevars r.rew_evars)) *)

       	          (* Printf.printf "rel_context: %s\n" (Pp.string_of_ppcmds (Printer.pr_rel_context env (goalevars evars) relprf')); *)
                  
	          (* Printf.printf "rew_from: %s\n" (Pp.string_of_ppcmds (Printer.pr_constr_env (Environ.push_rel_context relprf' env) (goalevars evars) rew_from)); *)
	          (* Printf.printf "rew_to: %s\n" (Pp.string_of_ppcmds (Printer.pr_constr_env (Environ.push_rel_context relprf' env) (goalevars evars) rew_to)); *)

                           
                  (* let related = *)
                  (*   if prop then PropGlobal.related_proof *)
                  (*   else TypeGlobal.related_proof *)
                  (* in *)
                  (* let evars, prf = *)
                  (*   let carl, carr = *)
                  (*     match car with *)
                  (*     | Homogeneous x -> x, x *)
                  (*     | Heterogeneous (x, y) -> x, y *)
                  (*   in *)
                  (*   related env evars carl carr rel rew_from rew_to *)
                  (* in evars, prf *)
                  
                  (* if is_pointwise && not (noccurn 3 r.rew_to) then *)
                  (*   let rew_to = r.rew_to in  *)
                  (*   let subst = Context.Rel.to_extended_list 3 (snd envprf) in *)
                  (*   let subst = mkProp :: mkRel 1 :: mkRel 1 :: List.rev subst in *)
                  (*   let rew_to' = substl subst rew_to in *)
                  (*   let prf' = *)
                  (*     let rel, prf = get_rew_prf r in *)
	          (*     let pred = *)
                  (*       mkLambda (n, t, *)
                  (*                 mkApp (rel, [| lift 1 r.rew_from; liftn 1 2 rew_to' |])) *)
                  (*     in *)
	          (*     let (evars, _), eq_rew = *)
                  (*       app_poly_sort prop env evars coq_eq_rew_inv [||] *)
                  (*     in *)
	          (*     mkApp (eq_rew, [| t; pred; mkRel 2; mkRel 3; mkRel 1; *)
                  (*                       prf |]) *)
                  (*   in *)
	          (*   Printf.printf "is_pointwise: new rew_to: %s\n" (Pp.string_of_ppcmds (Printer.pr_constr_env (Environ.push_rel_context relprf' env) (goalevars evars) rew_to')); *)
                  (*   prf' *)

let all_subterms = subterm true default_flags
let one_subterm = subterm false default_flags
                          
let bu (s : 'a pure_strategy) : 'a pure_strategy =
  let open Strategies in
  fix (fun s' -> seq (choice (progress (all_subterms s')) s) (try_ s'))
      
let td (s : 'a pure_strategy) : 'a pure_strategy =
  let open Strategies in
  fix (fun s' -> seq (choice s (progress (all_subterms s'))) (try_ s'))
      
let innermost (s : 'a pure_strategy) : 'a pure_strategy =
  let open Strategies in
  fix (fun ins -> choice (one_subterm ins) s)
      
let outermost (s : 'a pure_strategy) : 'a pure_strategy =
  let open Strategies in
  fix (fun out -> choice s (one_subterm out))
      
let inorder (s : 'a pure_strategy) : 'a pure_strategy =
  let open Strategies in
  fix (fun ord -> choice s (all_subterms (try_ ord)))
    
(** The strategy for a single rewrite, dealing with occurrences. *)

(** A dummy initial clauseenv to avoid generating initial evars before
    even finding a first application of the rewriting lemma, in setoid_rewrite
    mode *)

let rewrite_with l2r flags c occs : strategy = { strategy =
  fun ({ state = () } as input) ->
  let unify env envprf evars t =
    let env = push_rel_context envprf env in
    let (sigma, cstrs) = evars in
    let ans =
      try Some (refresh_hypinfo env sigma c)
      with e when Class_tactics.catchable e -> None
    in
    match ans with
    | None -> None
    | Some (sigma, rew) ->
       unify_eqn rew l2r flags env (sigma, cstrs) None t
  in
  let app = apply_rule unify occs in
  let strat =
    Strategies.fix (fun aux ->
	Strategies.choice app (subterm true default_flags aux))
  in
  let _, res = strat.strategy { input with state = 0 } in
  ((), res)
					       }

let apply_strategy (s : strategy) env unfresh concl (prop, cstr) evars =
  let envprf = [] in
  let ty = get_type_of env envprf evars concl in
  let _, res = s.strategy { state = () ; env ; envprf; unfresh ;
			    carrier = Homogeneous ty ; term1 = concl ;
                            term2 = concl ;
			    cstr = (prop, Some cstr) ; evars } in
  res

let solve_constraints env (evars,cstrs) =
  let filter = all_constraints cstrs in
    Typeclasses.resolve_typeclasses env ~filter ~split:false ~fail:true
      (Typeclasses.mark_resolvables ~filter evars)

exception RewriteFailure of Pp.std_ppcmds

type result = (evar_map * constr option * types) option option

let cl_rewrite_clause_aux ?(abs=None) debug strat env avoid sigma concl is_hyp
    : result =
  let evdref = ref sigma in
  let sort = Typing.e_sort_of env evdref concl in
  let evars = (!evdref, Evar.Set.empty) in
  let evars, cstr =
    let prop, (evars, arrow) =
      if is_prop_sort sort then true, app_poly_sort true env evars impl [||]
      else false, app_poly_sort false env evars TypeGlobal.arrow [||]
    in
      match is_hyp with
      | None ->
	let evars, t = poly_inverse prop env evars (mkSort sort) arrow in
	  evars, (prop, t)
      | Some _ -> evars, (prop, arrow)
  in
  let eq = apply_strategy strat env avoid concl cstr evars in
    match eq with
    | Fail -> None
    | Identity -> Some None
    | Success res ->
      let (_, cstrs) = res.rew_evars in
      let evars' =
        if debug then fst res.rew_evars
        else solve_constraints env res.rew_evars
      in
      let newt = Evarutil.nf_evar evars' res.rew_to in
      let evars = (* Keep only original evars (potentially instantiated) and goal evars,
		     the rest has been defined and substituted already. *)
	if not debug then
          Evar.Set.fold
	    (fun ev acc ->
	      if not (Evd.is_defined acc ev) then
	        errorlabstrm "rewrite"
			     (str "Unsolved constraint remaining: " ++ spc () ++
			        Evd.pr_evar_info (Evd.find acc ev))
	      else Evd.remove acc ev)
	    cstrs evars'
        else evars'
      in
      let evars, res = match res.rew_prf with
        | RewCast c -> evars, None
	| RewEq (p, pty, t1, t2, c, crel, cty) ->
	   let pred = mkNamedLambda eq_abs_id cty (lift 1 p) in
	   let (evars, _), eq_rew = app_poly_sort (fst cstr) env (evars, Evar.Set.empty) coq_eq_rew [||] in
	   let prf = mkApp (eq_rew, [| cty; pred; t1; t2; c |]) in
	   evars, Some (Evarutil.nf_evar evars prf)
	| RewPrf (rel, p) ->
	  let p = nf_zeta env evars' (Evarutil.nf_evar evars' p) in
	  let term =
	    match abs with
	    | None -> p
	    | Some (t, ty) ->
              let t = Evarutil.nf_evar evars' t in
              let ty = Evarutil.nf_evar evars' ty in
		mkApp (mkLambda (Name (Id.of_string "lemma"), ty, p), [| t |])
	  in
          let term = if not debug then Tacred.simpl env evars' term else term in
	  let proof = match is_hyp with
            | None -> term
            | Some id -> mkApp (term, [| mkVar id |])
          in evars, Some proof
      in Some (Some (evars, res, newt))

(** Insert a declaration after the last declaration it depends on *)
let rec insert_dependent env decl accu hyps = match hyps with
| [] -> List.rev_append accu [decl]
| ndecl :: rem ->
  if occur_var_in_decl env (get_id ndecl) decl then
    List.rev_append accu (decl :: hyps)
  else
    insert_dependent env decl (ndecl :: accu) rem

let assert_replacing id newt tac =
  let prf = Proofview.Goal.nf_enter { enter = begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    let env = Proofview.Goal.env gl in
    let ctx = Environ.named_context env in
    let after, before = List.split_when (Id.equal id % get_id) ctx in
    let nc = match before with
    | [] -> assert false
    | d :: rem -> insert_dependent env (LocalAssum (get_id d, newt)) [] after @ rem
    in
    let env' = Environ.reset_with_named_context (val_of_named_context nc) env in
    Refine.refine ~unsafe:false { run = begin fun sigma ->
      let Sigma (ev, sigma, p) = Evarutil.new_evar env' sigma concl in
      let Sigma (ev', sigma, q) = Evarutil.new_evar env sigma newt in
      let map d =
        let n = get_id d in
        if Id.equal n id then ev' else mkVar n
      in
      let (e, _) = destEvar ev in
      Sigma (mkEvar (e, Array.map_of_list map nc), sigma, p +> q)
    end }
  end } in
  Proofview.tclTHEN prf (Proofview.tclFOCUS 2 2 tac)

let newfail n s =
  Proofview.tclZERO (Refiner.FailError (n, lazy s))

let cl_rewrite_clause_newtac ?abs ?origsigma debug ~progress strat clause =
  let open Proofview.Notations in
  let treat sigma res =
    match res with
    | None -> newfail 0 (str "Nothing to rewrite")
    | Some None -> if progress then newfail 0 (str"Failed to progress")
		   else Proofview.tclUNIT ()
    | Some (Some res) ->
        let (undef, prf, newt) = res in
        let fold ev _ accu = if Evd.mem sigma ev then accu else ev :: accu in
        let gls = List.rev (Evd.fold_undefined fold undef []) in
	match clause, prf with
	| Some id, Some p ->
           let tac = Refine.refine
                       ~unsafe:false
                       { run = fun h ->
                               Sigma (p, h, Sigma.refl) }
		     <*> Proofview.Unsafe.tclNEWGOALS gls in
            Proofview.Unsafe.tclEVARS undef <*>
	    assert_replacing id newt tac
	| Some id, None ->
            Proofview.Unsafe.tclEVARS undef <*>
            convert_hyp_no_check (LocalAssum (id, newt))
	| None, Some p ->
            Proofview.Unsafe.tclEVARS undef <*>
            Proofview.Goal.enter { enter = begin fun gl ->
            let env = Proofview.Goal.env gl in
            let make = { run = begin fun sigma ->
              let Sigma (ev, sigma, q) = Evarutil.new_evar env sigma newt in
              Sigma (mkApp (p, [| ev |]), sigma, q)
            end } in
            Refine.refine ~unsafe:false make <*> Proofview.Unsafe.tclNEWGOALS gls
            end }
	| None, None ->
            Proofview.Unsafe.tclEVARS undef <*>
            convert_concl_no_check newt DEFAULTcast
  in
  let beta_red _ sigma c = Reductionops.nf_betaiota sigma c in
  let beta = Tactics.reduct_in_concl (beta_red, DEFAULTcast) in
  let opt_beta = match clause with
  | None -> Proofview.tclUNIT ()
  | Some id -> Tactics.reduct_in_hyp beta_red (id, InHyp)
  in
  Proofview.Goal.nf_enter { enter = begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let ty = match clause with
    | None -> concl
    | Some id -> Environ.named_type id env
    in
    let env = match clause with
    | None -> env
    | Some id ->
      (** Only consider variables not depending on [id] *)
      let ctx = Environ.named_context env in
      let filter decl = not (occur_var_in_decl env id decl) in
      let nctx = List.filter filter ctx in
      Environ.reset_with_named_context (Environ.val_of_named_context nctx) env
    in
    try
      let res =
        cl_rewrite_clause_aux ?abs debug strat env [] sigma ty clause
      in
      let sigma = match origsigma with None -> sigma | Some sigma -> sigma in
      treat sigma res <*>
      (** For compatibility *)
        beta <*> opt_beta <*>
        (if not debug then Proofview.shelve_unifiable else Tacticals.New.tclIDTAC)
    with
    | PretypeError (env, evd, (UnsatisfiableConstraints _ as e)) ->
      raise (RewriteFailure (Himsg.explain_pretype_error env evd e))
  end }

let cl_rewrite_clause_strat debug progress strat clause =
  ((if progress then tclWEAK_PROGRESS else fun x -> x)
   (fun gl ->
     try Proofview.V82.of_tactic
           (cl_rewrite_clause_newtac debug ~progress strat clause) gl
    with RewriteFailure e ->
	 errorlabstrm "" (str"rewrite failed: " ++ e)
       | Refiner.FailError (n, pp) ->
	  tclFAIL n (str"rewrite failed: " ++ Lazy.force pp) gl))

type debug_flag = bool
  
(** Setoid rewriting when called with "setoid_rewrite" *)
let cl_rewrite_clause debug l left2right occs clause gl =
  let strat = rewrite_with left2right (general_rewrite_unif_flags ()) l occs in
    cl_rewrite_clause_strat debug true strat clause gl

(** Setoid rewriting when called with "rewrite_strat" *)
let cl_rewrite_clause_strat debug strat clause =
  cl_rewrite_clause_strat debug false strat clause

let apply_lemma_ai inferpat l2r flags oc by loccs : strategy = { strategy =
  fun ({ state = () ; env ; term1 = t ; evars = (sigma, cstrs) } as input) ->
    let sigma, c = oc env sigma in
    let sigma, hypinfo = decompose_applied_relation env sigma c in
    let { c1; c2; car; rel; prf; sort; holes } = hypinfo in
    let rew = (car, rel, prf, c1, c2, holes, sort) in
    let evars = (sigma, cstrs) in
    let unify env envprf evars t =
      let env = push_rel_context envprf env in
      unify_eqn rew l2r flags env evars by t
    in
    let strat = apply_rule unify loccs in
    let ipat =
      if inferpat then
        Strategies.pattern_of_constr env sigma (if l2r then c1 else c2)
      else Strategies.id
    in
    let _, res = (Strategies.seq ipat strat).strategy { input with
						      state = 0 ;
						      evars }
    in (), res  }

let apply_lemma_aofi inferpat l2r flags oc by loccs : strategy =
  let state = ref None in
  let get_rew env sigma =
    match !state with
    | Some (r, pat) ->
       sigma, r, pat
    | None ->
       let sigma, c = oc env sigma in
       (* let () = Printf.printf "apply_lemma_aofi: %s\n" (Pp.string_of_ppcmds (Printer.pr_constr_env env sigma (fst c))) in *)
       let sigma, hypinfo = decompose_applied_relation env sigma c in
       let { c1; c2; car; rel; prf; sort; holes } = hypinfo in
       let pat =
	 if inferpat then
           let term = if l2r then c1 else c2 in
	   Strategies.pattern_of_constr env sigma term
	 else Strategies.id
       in
       let rew = (car, rel, prf, c1, c2, holes, sort) in
       sigma, rew, pat
  in
  { strategy =
  fun ({ state = () ; env ; term1 = t ; evars = (sigma, cstrs) } as input) ->
    let sigma, rew, pat = get_rew env sigma in
    let evars = (sigma, cstrs) in
    let unify env envprf evars t =
      let env = push_rel_context envprf env in
      match unify_eqn rew l2r flags env evars by t with
      | Some info ->
	 (match !state with
	 | None ->
	    let rel, prf = match info.rew_prf with
	    | RewPrf (rel, prf) -> rel, prf
	    | RewCast ck -> assert false
	    | RewEq (p, pty, t, u, prf, rel, car) -> mkApp (rel, [| car |]), prf
	    in
	    let (_, _, _, _ , _, holes, sort) = rew in
	    let from, to_ =
	      if l2r then info.rew_from, info.rew_to
	      else info.rew_to, info.rew_from
	    in
	    state := Some ((info.rew_car, rel, prf, from, to_, holes, sort), pat);
	    Some info
	 | Some r -> Some info)
      | None -> None
    in
    let strat = apply_rule unify loccs in
    let _, res = (Strategies.seq pat strat).strategy { input with
						      state = 0 ;
						      evars }
    in (), res }

let apply_lemma ai =
  if ai then apply_lemma_ai else apply_lemma_aofi

let apply_hint_lemma ai =
  if ai then apply_lemma_ai false else apply_lemma_aofi false

let apply_glob_constr is c l2r ai inferpat occs =
  let c env sigma =
    Tacinterp.interp_open_constr_with_bindings is env sigma c
  in
  let flags = general_rewrite_unif_flags () in
  let instrat = apply_lemma ai inferpat l2r flags c None occs in
  instrat

let set_glob_constr is n c occs =
  let c env sigma =
    Tacinterp.interp_open_constr_with_bindings is env sigma c
  in
  let flags = general_rewrite_unif_flags () in
  (* TODO *)
  let instrat = apply_lemma true true true flags c None occs in
  instrat
    
let interp_glob_constr_list is env =
  let make c = (); fun sigma ->
    let sigma, c = Pretyping.understand_tcc env sigma c in
    (sigma, (c, NoBindings))
  in
  List.map (fun c -> make c, true, None)

(* Syntax for rewriting with strategies *)

type unary_strategy =
    Subterms | Subterm | Innermost | Outermost | InOrder
  | Bottomup | Topdown | Progress | Try | Many | Repeat

type binary_strategy =
  | Compose | Choice

type ('constr,'redexpr) strategy_ast =
  | StratId | StratFail | StratRefl
  | StratUnary of unary_strategy * ('constr,'redexpr) strategy_ast
  | StratBinary of binary_strategy
    * ('constr,'redexpr) strategy_ast * ('constr,'redexpr) strategy_ast
  | StratConstr of 'constr * bool * bool * bool
  | StratPattern of 'constr
  | StratTerms of 'constr list
  | StratSet of Id.t * 'constr
  | StratHints of bool * string
  | StratEval of 'redexpr
  | StratFold of 'constr

let rec map_strategy (f : 'a -> 'a2) (g : 'b -> 'b2) : ('a,'b) strategy_ast -> ('a2,'b2) strategy_ast = function
  | StratId | StratFail | StratRefl as s -> s
  | StratUnary (s, str) -> StratUnary (s, map_strategy f g str)
  | StratBinary (s, str, str') -> StratBinary (s, map_strategy f g str, map_strategy f g str')
  | StratConstr (c, b, b', b'') -> StratConstr (f c, b, b', b'')
  | StratPattern p -> StratPattern (f p)
  | StratTerms l -> StratTerms (List.map f l)
  | StratSet (id, c) -> StratSet (id, f c)
  | StratHints (b, id) -> StratHints (b, id)
  | StratEval r -> StratEval (g r)
  | StratFold c -> StratFold (f c)

let rec strategy_of_ast is = function
  | StratId -> Strategies.id
  | StratFail -> Strategies.fail
  | StratRefl -> Strategies.refl
  | StratUnary (f, s) ->
    let s' = strategy_of_ast is s in
    let f' = match f with
      | Subterms -> all_subterms
      | Subterm -> one_subterm
      | Innermost -> innermost
      | Outermost -> outermost
      | Bottomup -> bu
      | Topdown -> td
      | InOrder -> inorder
      | Progress -> Strategies.progress
      | Try -> Strategies.try_
      | Many -> Strategies.many
      | Repeat -> Strategies.repeat
    in f' s'
  | StratBinary (f, s, t) ->
    let s' = strategy_of_ast is s in
    let t' = strategy_of_ast is t in
    let f' = match f with
      | Compose -> Strategies.seq
      | Choice -> Strategies.choice
    in f' s' t'
  | StratConstr (c, b, b', b'') ->
     apply_glob_constr is c b b' b'' AllOccurrences
  | StratPattern p -> Strategies.pattern (fst (fst p))
  | StratSet (id, p) -> set_glob_constr is id p AllOccurrences
  | StratHints (old, id) -> if old then Strategies.old_hints apply_hint_lemma id
			    else Strategies.hints apply_hint_lemma id
  | StratTerms l -> { strategy =
    (fun ({ state = () ; env } as input) ->
     let l' = interp_glob_constr_list is env (List.map (fun x -> fst (fst x)) l) in
     (Strategies.lemmas apply_hint_lemma l').strategy input) }
  | StratEval r -> { strategy =
    (fun ({ state = () ; env ; evars } as input) ->
     let (sigma,r_interp) = Tacinterp.interp_redexp env (goalevars evars) r in
     (Strategies.reduce r_interp).strategy { input with
					     evars = (sigma,cstrevars evars) }) }
  | StratFold c -> Strategies.fold_glob (fst (fst c))


(* By default the strategy for "rewrite_db" is top-down *)

(** Bind to "rewrite" too *)

(** Taken from original setoid_replace, to emulate the old rewrite semantics where
    lemmas are first instantiated and then rewrite proceeds. *)

let check_evar_map_of_evars_defs evd =
 let metas = Evd.meta_list evd in
 let check_freemetas_is_empty rebus =
  Evd.Metaset.iter
   (fun m ->
     if Evd.meta_defined evd m then () else
      raise
	(Logic.RefinerError (Logic.UnresolvedBindings [Evd.meta_name evd m])))
 in
  List.iter
   (fun (_,binding) ->
     match binding with
        Evd.Cltyp (_,{Evd.rebus=rebus; Evd.freemetas=freemetas}) ->
         check_freemetas_is_empty rebus freemetas
      | Evd.Clval (_,({Evd.rebus=rebus1; Evd.freemetas=freemetas1},_),
                 {Evd.rebus=rebus2; Evd.freemetas=freemetas2}) ->
         check_freemetas_is_empty rebus1 freemetas1 ;
         check_freemetas_is_empty rebus2 freemetas2
   ) metas

(* Find a subterm which matches the pattern to rewrite for "rewrite" *)
let unification_rewrite l2r c1 c2 sigma prf car rel but env =
  let (sigma,c') =
    try
      (* ~flags:(false,true) to allow to mark occurrences that must not be
         rewritten simply by replacing them with let-defined definitions
         in the context *)
      Unification.w_unify_to_subterm
       ~flags:rewrite_unif_flags
        env sigma ((if l2r then c1 else c2),but)
    with
    | ex when Pretype_errors.precatchable_exception ex ->
	(* ~flags:(true,true) to make Ring work (since it really
           exploits conversion) *)
      Unification.w_unify_to_subterm
        ~flags:rewrite_conv_unif_flags
        env sigma ((if l2r then c1 else c2),but)
  in
  let nf c = Evarutil.nf_evar sigma c in
  let c1 = if l2r then nf c' else nf c1
  and c2 = if l2r then nf c2 else nf c'
  and car = map_carrier nf car and rel = nf rel in
  check_evar_map_of_evars_defs sigma;
  let prf = nf prf in
  let prfty = nf (Retyping.get_type_of env sigma prf) in
  let sort = sort_of_rel env sigma but in
  let abs = prf, prfty in
  let prf = prf in (* FIXME changes the proof term *)
  let res = (car, rel, prf, c1, c2) in
  abs, sigma, res, Sorts.is_prop sort

let get_hyp gl (c,l) clause l2r =
  let evars = project gl in
  let env = pf_env gl in
  let sigma, hi = decompose_applied_relation env evars (c,l) in
  let but = match clause with
    | Some id -> pf_get_hyp_typ gl id
    | None -> Evarutil.nf_evar evars (pf_concl gl)
  in
  unification_rewrite l2r hi.c1 hi.c2 sigma hi.prf hi.car hi.rel but env

let general_rewrite_flags = { under_lambdas = false; on_morphisms = true }

(* let rewriteclaustac_key = Profile.declare_profile "cl_rewrite_clause_tac";; *)
(* let cl_rewrite_clause_tac = Profile.profile5 rewriteclaustac_key cl_rewrite_clause_tac *)

(** Setoid rewriting when called with "rewrite" *)
let general_s_rewrite cl l2r occs (c,l) ~new_goals gl =
  let abs, evd, res, sort = get_hyp gl (c,l) cl l2r in
  let unify env envprf evars t = unify_abs res l2r sort env envprf evars t in
  let app = apply_rule unify occs in
  let recstrat aux = Strategies.choice app (subterm true general_rewrite_flags aux) in
  let substrat = Strategies.fix recstrat in
  let strat = { strategy = fun ({ state = () } as input) ->
    let _, res = substrat.strategy { input with state = 0 } in
    (), res
	      }
  in
  let origsigma = project gl in
  init_setoid ();
    try
      tclWEAK_PROGRESS
	(tclTHEN
           (Refiner.tclEVARS evd)
	   (Proofview.V82.of_tactic
	      (cl_rewrite_clause_newtac ~progress:true ~abs:(Some abs)
                                        ~origsigma false strat cl))) gl
    with RewriteFailure e ->
      tclFAIL 0 (str"rewrite failed: " ++ e) gl

let general_s_rewrite_clause x =
  match x with
    | None -> general_s_rewrite None
    | Some id -> general_s_rewrite (Some id)

let general_s_rewrite_clause x y z w ~new_goals =
  Proofview.V82.tactic (general_s_rewrite_clause x y z w ~new_goals)

(* let _ = Hook.set Equality.general_setoid_rewrite_clause general_s_rewrite_clause *)

let get_lemma_proof f env evm x y =
  let (evm, _), c = f env (evm,Evar.Set.empty) x y in
    evm, c

let get_reflexive_proof =
  get_lemma_proof PropGlobal.get_reflexive_proof

let get_symmetric_proof =
  get_lemma_proof PropGlobal.get_symmetric_proof

let get_transitive_proof =
  get_lemma_proof PropGlobal.get_transitive_proof
       
