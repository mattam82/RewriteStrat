(**********************************************************************)
(* Strategical Rewriting                                              *)
(* Copyright (c) 2016 Matthieu Sozeau <matthieu.sozeau@inria.fr>      *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "rewrite_strat_plugin"

open Extraargs
open Eauto
open Locusops
open Term
open Names
open Tactics
open Pp
open Nameops
open Refiner
open Errors
open Constrexpr

open Rewrite_strat_common
open Rewrite_strat
