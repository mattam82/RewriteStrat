(**********************************************************************)
(* Strategical Rewriting                                              *)
(* Copyright (c) 2016 Matthieu Sozeau <matthieu.sozeau@inria.fr>      *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Rewrite_strat_common

open Names
open Constr
open Environ
open Constrexpr
open Tacexpr
open Misctypes
open Evd
open Proof_type
open Tacinterp

(** TODO: document and clean me! *)

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
  | StratConstr of 'constr * bool (* direction *) * bool
  (* all instances (true) or all occurrences of the first instance (false, rewrite like) *)
		   * bool (* Infer pattern from left-hand-side *)
  | StratPattern of 'constr
  | StratTerms of 'constr list
  | StratSet of Id.t * 'constr
  | StratHints of bool * string
  | StratEval of 'redexpr 
  | StratFold of 'constr

type evars = evar_map * Evar.Set.t (* goal evars, constraint evars *)

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

type rewrite_result =
| Fail
| Identity
| Success of rewrite_result_info

type strategy

val strategy_of_ast : interp_sign -> (glob_constr_and_expr Misctypes.with_bindings, raw_red_expr) strategy_ast -> strategy

val map_strategy : ('a -> 'b) -> ('c -> 'd) ->
  ('a, 'c) strategy_ast -> ('b, 'd) strategy_ast

type debug_flag = bool

(** Entry point for user-level "rewrite_strat" *)
val cl_rewrite_clause_strat : debug_flag -> strategy -> Id.t option -> tactic

val apply_strategy :
  strategy ->
  Environ.env ->
  Names.Id.t list ->
  Term.constr ->
  bool * Term.constr ->
  evars -> rewrite_result
