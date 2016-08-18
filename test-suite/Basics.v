(**********************************************************************)
(* Strategical Rewriting                                              *)
(* Copyright (c) 2016 Matthieu Sozeau <matthieu.sozeau@inria.fr>      *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

From RewriteStrat Require Import RewriteStrat.

(* Some algebraic theory *)
Module Al.
  Axiom A : Type.
  Axiom u : A.
  Axiom op : A -> A -> A.

  Axiom leftu : forall x, op u x = x.
  
  Goal forall x y, x = y -> op u x = op u y.
  Proof.
    intros.
    now rew_strat debug (topdown H).
  Qed.
End Al.
