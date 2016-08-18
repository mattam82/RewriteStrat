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
