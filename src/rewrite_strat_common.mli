(**********************************************************************)
(* Strategical Rewriting                                              *)
(* Copyright (c) 2016 Matthieu Sozeau <matthieu.sozeau@inria.fr>      *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

val make_ref : string list -> string -> Globnames.global_reference

val with_rollback : ('a -> 'b) -> 'a -> 'b

val whd_all : Reductionops.contextual_reduction_function

val new_evar : Environ.env ->
               Evd.evar_map ->
               ?store:Evd.Store.t ->
               Term.types -> Evd.evar_map * Term.constr

val new_type_evar : Environ.env ->
                    Evd.evar_map ->
                    Evd.evar_map * (Term.constr * Term.sorts)

val new_global : Evd.evar_map -> Globnames.global_reference -> Evd.evar_map * Term.constr

val e_solve_evars : Environ.env ->
                    Evd.evar_map ref ->
                    Term.constr -> Term.constr

val e_sort_of : Environ.env ->
                Evd.evar_map ref ->
                Term.constr -> Term.sorts

val make_assum_decl : ('a * Term.types) ->
                      ('a * Term.constr option * Term.types)

val make_def_decl : ('a * Term.constr * Term.types) ->
                    ('a * Term.constr option * Term.types)

module Sigma : sig
  module Unsafe : sig
    val of_evar_map : Evd.evar_map -> Evd.evar_map
  end

  val to_evar_map : Evd.evar_map -> Evd.evar_map
end

module CErrors = Errors
module CClosure = Closure
module Refine = Proofview.Refine
                      
