(**********************************************************************)
(* Strategical Rewriting                                              *)
(* Copyright (c) 2016 Matthieu Sozeau <matthieu.sozeau@inria.fr>      *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "rewrite_strat_plugin"

open Rewrite_strat_common
open Rewrite_strat

(* Syntax for rewriting with strategies *)

open Names
open Misctypes
open Locus
open Constrexpr
open Glob_term
open Geninterp
open Extraargs
open Tacmach
open Tacticals
open Stdarg
open Constrarg
open Pcoq.Prim
open Pcoq.Constr
open Pcoq.Tactic

type constr_expr_with_bindings = constr_expr with_bindings
type glob_constr_with_bindings = Tacexpr.glob_constr_and_expr with_bindings
type glob_constr_with_bindings_sign = interp_sign * Tacexpr.glob_constr_and_expr with_bindings

let pr_glob_constr_with_bindings_sign _ _ _ (ge : glob_constr_with_bindings_sign) = Printer.pr_glob_constr (fst (fst (snd ge)))
let pr_glob_constr_with_bindings _ _ _ (ge : glob_constr_with_bindings) = Printer.pr_glob_constr (fst (fst ge))
let pr_constr_expr_with_bindings prc _ _ (ge : constr_expr_with_bindings) = prc (fst ge)
let interp_glob_constr_with_bindings ist gl c = Tacmach.project gl , (ist, c)
let glob_glob_constr_with_bindings ist l = Tacintern.intern_constr_with_bindings ist l
let subst_glob_constr_with_bindings s c =
  Tacsubst.subst_glob_with_bindings s c

ARGUMENT EXTEND rew_glob_constr_with_bindings
    PRINTED BY pr_glob_constr_with_bindings_sign

    INTERPRETED BY interp_glob_constr_with_bindings
    GLOBALIZED BY glob_glob_constr_with_bindings
    SUBSTITUTED BY subst_glob_constr_with_bindings

    (* RAW_TYPED AS constr_expr_with_bindings *)
    
    RAW_PRINTED BY pr_constr_expr_with_bindings

    (* GLOB_TYPED AS glob_constr_with_bindings *)
    GLOB_PRINTED BY pr_glob_constr_with_bindings

   [ constr_with_bindings(bl) ] -> [ bl ]
END

open Genarg

let pr_all_or_first _prc _prlc _prt = function
  | false -> Pp.str "fi:"
  | true -> Pp.str ""

ARGUMENT EXTEND rew_all_or_first TYPED AS bool PRINTED BY pr_all_or_first
| [ "fi:" ] -> [ false ]
| [ "ai:" ] -> [ true ]
| [ ] -> [ true ]
END

let pr_infer_pat _prc _prlc _prt = function
  | true -> Pp.str "ipat:"
  | false -> Pp.str ""

ARGUMENT EXTEND rew_infer_pat TYPED AS bool PRINTED BY pr_infer_pat
| [ "ipat:" ] -> [ true ]
| [ ] -> [ false ]
END

let pr_debug_flag _prc _prlc _prt = function
  | true -> Pp.str "debug"
  | false -> Pp.str ""

ARGUMENT EXTEND rew_debug_flag TYPED AS bool PRINTED BY pr_debug_flag
| [ "debug" ] -> [ true ]
| [ ] -> [ false ]
END


type raw_strategy = (constr_expr Misctypes.with_bindings, Tacexpr.raw_red_expr) strategy_ast
type glob_strategy = (Tacexpr.glob_constr_and_expr Misctypes.with_bindings, Tacexpr.raw_red_expr) strategy_ast

let interp_strategy ist gl s = 
  let sigma = project gl in
  sigma, strategy_of_ast ist s

let glob_strategy ist s =
  map_strategy (Tacintern.intern_constr_with_bindings ist)
               (fun c -> c) s

let subst_strategy s str = str

let pr_strategy _ _ _ (s : strategy) = Pp.str "<strategy>"
let pr_raw_strategy _ _ _ (s : raw_strategy) = Pp.str "<strategy>"
let pr_glob_strategy _ _ _ (s : glob_strategy) = Pp.str "<strategy>"

ARGUMENT EXTEND rew_strategy
    PRINTED BY pr_strategy

    INTERPRETED BY interp_strategy
    GLOBALIZED BY glob_strategy
    SUBSTITUTED BY subst_strategy

    (* RAW_TYPED AS raw_strategy *)
    RAW_PRINTED BY pr_raw_strategy

    (* GLOB_TYPED AS glob_strategy *)
    GLOB_PRINTED BY pr_glob_strategy

    [ orient(o) rew_all_or_first(fi) rew_infer_pat(ip) rew_glob_constr_with_bindings(c) ] ->
    [ StratConstr (c, o, fi, ip) ]
  | [ "subterms" rew_strategy(h) ] -> [ StratUnary (Subterms, h) ]
  | [ "subterm" rew_strategy(h) ] -> [ StratUnary (Subterm, h) ]
  | [ "innermost" rew_strategy(h) ] -> [ StratUnary(Innermost, h) ]
  | [ "outermost" rew_strategy(h) ] -> [ StratUnary(Outermost, h) ]
  | [ "bottomup" rew_strategy(h) ] -> [ StratUnary(Bottomup, h) ]
  | [ "topdown" rew_strategy(h) ] -> [ StratUnary(Topdown, h) ]
  | [ "inorder" rew_strategy(h) ] -> [ StratUnary(InOrder, h) ]
  | [ "id" ] -> [ StratId ]
  | [ "fail" ] -> [ StratFail ]
  | [ "refl" ] -> [ StratRefl ]
  | [ "set" ident(id) rew_glob_constr_with_bindings(c) ] -> [ StratSet (id, c) ]
  | [ "pattern" rew_glob_constr_with_bindings(c) ] -> [ StratPattern (c) ]
  | [ "progress" rew_strategy(h) ] -> [ StratUnary (Progress, h) ]
  | [ "try" rew_strategy(h) ] -> [ StratUnary (Try, h) ]
  | [ "many" rew_strategy(h) ] -> [ StratUnary (Many, h) ]
  | [ "repeat" rew_strategy(h) ] -> [ StratUnary (Repeat, h) ]
  | [ rew_strategy(h) ";" rew_strategy(h') ] -> [ StratBinary (Compose, h, h') ]
  | [ "(" rew_strategy(h) ")" ] -> [ h ]
  | [ "choice" rew_strategy(h) rew_strategy(h') ] -> [ StratBinary (Choice, h, h') ]
  | [ "old_hints" preident(h) ] -> [ StratHints (true, h) ]
  | [ "hints" preident(h) ] -> [ StratHints (false, h) ]
  | [ "terms" rew_glob_constr_with_bindings_list(h) ] -> [ StratTerms h ]
  | [ "eval" red_expr(r) ] -> [ StratEval r ]
  | [ "fold" rew_glob_constr_with_bindings(c) ] -> [ StratFold c ]
END

(* By default the strategy for "rewrite_db" is top-down *)

let db_strat db = StratUnary (Topdown, StratHints (false, db))
let cl_rewrite_clause_db db =
  cl_rewrite_clause_strat false
    (strategy_of_ast (Tacinterp.default_ist ()) (db_strat db))

let cl_rewrite_clause_db = 
  if Flags.profile then
    let key = Profile.declare_profile "cl_rewrite_clause_db" in
      Profile.profile3 key cl_rewrite_clause_db
  else cl_rewrite_clause_db

TACTIC EXTEND rew_strat
| [ "rew_strat" rew_debug_flag(d) rew_strategy(s) "in" hyp(id) ] -> [ Proofview.V82.tactic (cl_rewrite_clause_strat d s (Some id)) ]
| [ "rew_strat" rew_debug_flag(d) rew_strategy(s) ] -> [ Proofview.V82.tactic (cl_rewrite_clause_strat d s None) ]
| [ "rew_db" preident(db) "in" hyp(id) ] -> [ Proofview.V82.tactic (cl_rewrite_clause_db db (Some id)) ]
| [ "rew_db" preident(db) ] -> [ Proofview.V82.tactic (cl_rewrite_clause_db db None) ]
END

(* let clsubstitute o c = *)
(*   let is_tac id = match fst (fst (snd c)) with GVar (_, id') when Id.equal id' id -> true | _ -> false in *)
(*     Tacticals.onAllHypsAndConcl *)
(*       (fun cl -> *)
(*         match cl with *)
(*           | Some id when is_tac id -> tclIDTAC *)
(*           | _ -> cl_rewrite_clause false c o AllOccurrences cl) *)

(* TACTIC EXTEND substitute *)
(* | [ "substitute" orient(o) glob_constr_with_bindings(c) ] -> [ Proofview.V82.tactic (clsubstitute o c) ] *)
(* END *)

(** TODO backport to Coq *)

open Proofview.Notations

let refine_tac ist simple flags c =
  let open Proofview in
  Goal.nf_enter { Goal.enter = begin fun gl ->
    let concl = Goal.concl gl in
    let env = Goal.env gl in
    let expected_type = Pretyping.OfType concl in
    let c = Pretyping.type_uconstr ~flags ~expected_type ist c in
    let update = { Sigma.run = fun sigma -> c.Pretyping.delayed env sigma } in
    let refine = Refine.refine ~unsafe:false update in
    if simple then refine
    else refine <*>
           Tactics.New.reduce_after_refine <*>
           Proofview.shelve_unifiable
  end }

TACTIC EXTEND simple_refine_notc
| [ "simple" "refine" "noclass" uconstr(c) ] -> [
    let flags = Pretyping.no_classes_no_fail_inference_flags in
    refine_tac ist true flags c ]
END

let solve_constraints_tac ist =
  Proofview.Goal.enter { enter = begin fun gl ->
    let env = Proofview.Goal.env gl in
    let evd = Proofview.Goal.sigma gl in
    let evd = Sigma.to_evar_map evd in
    let evd = Evarconv.consider_remaining_unif_problems env evd in
    try Evarconv.check_problems_are_solved env evd;
        Proofview.Unsafe.tclEVARS evd
    with e -> Proofview.tclZERO e
  end }

TACTIC EXTEND solve_constraints
| [ "resolve_constraints" ] -> [
    solve_constraints_tac ist ]
END
