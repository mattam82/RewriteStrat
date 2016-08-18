(**********************************************************************)
(* Strategical Rewriting                                              *)
(* Copyright (c) 2016 Matthieu Sozeau <matthieu.sozeau@inria.fr>      *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** A helper constant when doing rewriting with leibniz equality *)

Definition eq_rew (A : Type) (P : A -> Type) (x y : A) (e : x = y) : P y -> P x :=
  match e with eq_refl => fun x => x end.

Definition eq_rew_inv (A : Type) (P : A -> Type) (x y : A) (e : y = x) : P y -> P x :=
  match e with eq_refl => fun x => x end.

Definition full_relation (A : Type) (B : Type) : A -> B -> Prop :=
  fun x y => True.
