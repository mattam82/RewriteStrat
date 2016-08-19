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

(** Compatibility *)
let whd_all =
  Reductionops.whd_betadeltaiota

let new_evar env sigma ?store concl = Evarutil.new_evar env sigma ?store concl
let new_type_evar env sigma = Evarutil.new_type_evar env sigma Evd.univ_flexible
let new_global evd g = Evarutil.new_global evd g
  
let e_solve_evars env evdref t = Typing.solve_evars env evdref t
let e_sort_of = Typing.sort_of
let make_assum_decl (n, t) = (n, None, t)
let make_def_decl (n, b, t) = (n, Some b, t)


module Sigma = struct
  module Unsafe = struct
    let of_evar_map x = x
  end

  let to_evar_map x = x
end

module CErrors = Errors
module CClosure = Closure
module Refine = Proofview.Refine
                                
