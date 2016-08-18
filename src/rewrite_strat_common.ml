(**********************************************************************)
(* Strategical Rewriting                                              *)
(* Copyright (c) 2016 Matthieu Sozeau <matthieu.sozeau@inria.fr>      *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

let contrib_name = "Rewrite"
let init_reference dir s = Coqlib.find_reference contrib_name dir s
let gen_constant dir s = Coqlib.gen_constant "rewrite" dir s

let make_ref dir s = Coqlib.gen_reference contrib_name dir s

let with_rollback f x =
  States.with_state_protection_on_exception f x
