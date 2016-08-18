(**********************************************************************)
(* Strategical Rewriting                                              *)
(* Copyright (c) 2016 Matthieu Sozeau <matthieu.sozeau@inria.fr>      *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** The set of libraries required to run the rewrite plugin with all features. *)

Require Export RewriteStrat.Init. (* Exports the [rew_strat] tactic *)
Require RewriteStrat.Equality.
Require RewriteStrat.Morphisms.
Require RewriteStrat.CMorphisms.
