(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Typeclass-based morphism definition and standard, minimal instances

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.RelationClasses.

Require Import RewriteStrat.Init.

Generalizable Variables A eqA B C D R RA RB RC m f x y.
Local Obligation Tactic := simpl_relation.

Tactic Notation "refinetc" uconstr(u) :=
  simple refine noclass u; shelve_unifiable.

(** * Morphisms.

   We now turn to the definition of [Proper] and declare standard instances.
   These will be used by the [setoid_rewrite] tactic later. *)

(** A morphism for a relation [R] is a proper element of the relation.
   The relation [R] will be instantiated by [respectful] and [A] by an arrow
   type for usual morphisms. *)

Class Related {A B} (R : A -> B -> Prop) (m : A) (n : B) : Prop :=
  related_prf : R m n.

Notation Proper R m := (Related R m m).
Notation " '@' 'Proper' A R m " := (@Related A A R m m) (at level 10, A at next level,
                                                        R at next level, m at next level, only parsing).

Section Proper.
  Context {A : Type}.

  (** Every element in the carrier of a reflexive relation is a morphism
   for this relation.  We use a proxy class for this case which is used
   internally to discharge reflexivity constraints.  The [Reflexive]
   instance will almost always be used, but it won't apply in general to
   any kind of [Proper (A -> B) _ _] goal, making proof-search much
   slower. A cleaner solution would be to be able to set different
   priorities in different hint bases and select a particular hint
   database for resolution of a type class constraint. *)

  Lemma eq_proper (x : A) : Proper (@eq A) x.
  Proof. firstorder. Defined.
  
  Lemma reflexive_proper `(Reflexive A R) (x : A) : Proper R x.
  Proof. red. apply H. Defined.

  (** Respectful morphisms. *)
  
  (** The fully dependent version of respectfulness. *)
  
  Definition respectful_hetero
  (A B : Type)
  (C : A -> Type) (D : B -> Type)
  (R : A -> B -> Prop)
  (R' : forall (x : A) (y : B), R x y -> C x -> D y -> Prop) :
    (forall x : A, C x) -> (forall x : B, D x) -> Prop :=
    fun f g => forall x y (H : R x y), R' x y H (f x) (g y).

  Definition pointwise_relation_hetero
             (A B : Type)
             (C : A -> Type) (D : B -> Type)
             (R : forall (x : A) (y : B), C x -> D y -> Prop) :
    (forall x : A, C x) -> (forall x : B, D x) -> Prop :=
    fun f g => forall x y, R x y (f x) (g y).
  
  (** The non-dependent version is an instance where we forget dependencies. *)
  
  Definition respectful A' (R : relation A) (R' : relation A') : relation (A -> A') :=
    Eval compute in @respectful_hetero A A (fun _ => _) (fun _ => _) R (fun _ _ _ => R').

End Proper.

Arguments eq_proper /.
Arguments reflexive_proper /.

(** We favor the use of Leibniz equality or a declared reflexive relation 
  when resolving [Proper], otherwise, if the relation is given (not an evar),
  we fall back to [Related]. *)
Hint Extern 1 (Proper _ _) => 
  class_apply @eq_proper ||
  class_apply @reflexive_proper : typeclass_instances.

(** Notations reminiscent of the old syntax for declaring morphisms. *)
Delimit Scope signature_scope with signature.

Arguments respectful_hetero {_ _ _ _ _} R'%signature _ _.
Arguments pointwise_relation_hetero {_ _ _ _} R%signature _ _.

Module ProperNotations.

  Notation " R ++> R' " := (@respectful _ _ (R%signature) (R'%signature))
    (right associativity, at level 55) : signature_scope.

  Notation " R ==> R' " := (@respectful _ _ (R%signature) (R'%signature))
    (right associativity, at level 55) : signature_scope.

  Notation " R --> R' " := (@respectful _ _ (flip (R%signature)) (R'%signature))
    (right associativity, at level 55) : signature_scope.

  Notation "∀  α : R v1 v2 , S" :=
    (respectful_hetero (R := R) (fun v1 v2 α => S))
      (at level 200, α ident, R at level 7, v1 ident, v2 ident, right associativity)
    : signature_scope.
  
  Notation "∀  α : R , S" := (respectful_hetero (R := R) (fun _ _ α => S))
    (at level 200, α ident, R at level 7, right associativity)
    : signature_scope.

  Notation "∀  α , R" := (respectful_hetero (fun _ _ α => R))
    (at level 200, α ident, right associativity)
    : signature_scope.

  Notation "'λ'  v1 v2 , S " := (pointwise_relation_hetero (fun v1 v2 => S))
    (at level 55, v1 ident, v2 ident, right associativity)
    : signature_scope.
  
End ProperNotations.

Arguments respectful {A A'}%type (R R')%signature _ _.

Export ProperNotations.

Local Open Scope signature_scope.

(** [solve_proper] try to solve the goal [Proper (?==> ... ==>?) f]
    by repeated introductions and setoid rewrites. It should work
    fine when [f] is a combination of already known morphisms and
    quantifiers. *)

Ltac solve_respectful t :=
 match goal with
   | |- respectful _ _ _ _ =>
     let H := fresh "H" in
     intros ? ? H; solve_respectful ltac:(rew_strat (* FIXME *) H; t)
   | _ => t; reflexivity
 end.

Ltac solve_proper := unfold Related; solve_respectful ltac:(idtac).

(** [f_equiv] is a clone of [f_equal] that handles setoid equivalences.
    For example, if we know that [f] is a morphism for [E1==>E2==>E],
    then the goal [E (f x y) (f x' y')] will be transformed by [f_equiv]
    into the subgoals [E1 x x'] and [E2 y y'].
*)

Ltac f_equiv :=
 match goal with
  | |- ?R (?f ?x) (?f' _) =>
    let T := type of x in
    let Rx := fresh "R" in
    evar (Rx : relation T);
    let H := fresh in
    assert (H : (Rx==>R)%signature f f');
    unfold Rx in *; clear Rx; [ f_equiv | apply H; clear H; try reflexivity ]
  | |- ?R ?f ?f' =>
    solve [change (Proper R f); eauto with typeclass_instances | reflexivity ]
  | _ => idtac
 end.

Definition hrel A B := A -> B -> Prop.

Class hsubrelation (A : Type) (B : Type) (R : hrel A B) (R' : hrel A B) : Prop :=
  is_hsubrelation : forall (x : A) (y : B), R x y -> R' x y.

Section Relations.
  Let U := Type.
  Context {A B : U} (P : A -> U).

  (** [forall_def] reifies the dependent product as a definition. *)
  
  Definition forall_def : Type := forall x : A, P x.
  
  (** Dependent pointwise lifting of a relation on the range. *)
  
  Definition forall_relation 
             (sig : forall a, relation (P a)) : relation (forall x, P x) :=
    fun f g => forall a, sig a (f a) (g a).
    
  (** Non-dependent pointwise lifting *)
  Definition pointwise_relation (R : relation B) : relation (A -> B) :=
    fun f g => forall a, R (f a) (g a).

  Lemma pointwise_pointwise (R : relation B) :
    relation_equivalence (pointwise_relation R) (@eq A ==> R).
  Proof. intros. split; reduce; subst; firstorder. Qed.
  
  (** Subrelations induce a morphism on the identity. *)
  
  Global Instance subrelation_id_proper `(subrelation A RA RA') : Proper (RA ==> RA') id.
  Proof. firstorder. Qed.

  (** The subrelation property goes through products as usual. *)
  
  Lemma subrelation_respectful `(subl : subrelation A RA' RA, subr : subrelation B RB RB') :
    subrelation (RA ==> RB) (RA' ==> RB').
  Proof. unfold subrelation in *; firstorder. Defined.
  
  (** And of course it is reflexive. *)
  
  Lemma subrelation_refl R : @subrelation A R R.
  Proof. unfold subrelation; trivial. Defined.
  
  (** [Proper] is itself a covariant morphism for [subrelation].
   We use an unconvertible premise to avoid looping.
   *)
  
  Lemma subrelation_proper `(mor : Related A A R' m m) 
        `(unc : Unconvertible (relation A) R R')
        `(sub : subrelation A R' R) : Proper R m.
  Proof.
    intros. apply sub. apply mor.
  Defined.

  Global Instance proper_subrelation_proper :
    Proper (subrelation ++> eq ==> eq ==> impl) (@Related A A).
  Proof. reduce. subst. firstorder. Qed.

  Global Instance pointwise_subrelation `(sub : subrelation B R R') :
    subrelation (pointwise_relation R) (pointwise_relation R') | 4.
  Proof. reduce. unfold pointwise_relation in *. apply sub. apply H. Defined.
  
  (** For dependent function types. *)
  Lemma forall_subrelation (R S : forall x : A, relation (P x)) :
    (forall a, subrelation (R a) (S a)) -> subrelation (forall_relation R) (forall_relation S).
  Proof. reduce. apply H. apply H0. Qed.
End Relations.

Arguments subrelation_respectful /.
Arguments subrelation_refl /.
Arguments subrelation_proper /.
Arguments pointwise_subrelation /.

Typeclasses Opaque respectful pointwise_relation forall_relation.
Arguments forall_relation {A P}%type sig%signature _ _.
Arguments pointwise_relation A%type {B}%type R%signature _ _.
  
Hint Unfold Reflexive : core.
Hint Unfold Symmetric : core.
Hint Unfold Transitive : core.

(** Resolution with subrelation: favor decomposing products over applying reflexivity
  for unconstrained goals. *)

Ltac has_concrete_value t :=
  lazymatch t with
  | respectful ?from ?to =>
    (tryif is_evar from then has_concrete_value to else idtac)
  | _ => tryif is_evar t then fail else idtac
 end.

Ltac subrelation_respectful :=
  lazymatch goal with
  |- subrelation (?lhs ==> ?rhs)%signature (?lhs' ==> ?rhs')%signature =>
  (tryif has_concrete_value lhs; has_concrete_value lhs' then
     class_apply @subrelation_respectful
   else class_apply @subrelation_respectful; cycle 1)
  | |- _ => class_apply @subrelation_respectful
  end.

Ltac subrelation_tac T U :=
  (is_ground T ; is_ground U ; class_apply @subrelation_refl) ||
  ltac:(repeat subrelation_respectful) || class_apply @subrelation_refl.

Hint Extern 3 (@subrelation _ ?T ?U) => subrelation_tac T U : typeclass_instances.

CoInductive apply_subrelation : Prop := do_subrelation.

Ltac proper_subrelation :=
  match goal with
    [ H : apply_subrelation |- _ ] => clear H ; class_apply @subrelation_proper
  end.

Hint Extern 5 (@Proper _ ?H _) => proper_subrelation : typeclass_instances.

(** Essential subrelation instances for [iff], [impl] and [pointwise_relation]. *)

Instance iff_impl_subrelation : subrelation iff impl | 4.
Proof. firstorder. Qed.

Instance iff_flip_impl_subrelation : subrelation iff (flip impl) | 4.
Proof. firstorder. Qed.

(** We use an extern hint to help unification. *)

Hint Extern 4 (subrelation (@forall_relation ?A ?B ?R) (@forall_relation _ _ ?S)) =>
  apply (@forall_subrelation A B R S) ; intro : typeclass_instances.

Section GenericInstances.
  (* Share universes *)
  Let U := Type.
  Context {A B C : U}.

  (** We can build a PER on the Coq function space if we have PERs on the domain and
   codomain. *)
  
  Program Instance respectful_per `(PER A R, PER B R') : PER (R ==> R').

  Next Obligation.
  Proof with auto.
    assert(R x0 x0).
    transitivity y0... symmetry...
    transitivity (y x0)... 
  Qed.

  (** The complement of a relation conserves its proper elements. *)
  
  Program Definition complement_proper `(RA : A -> A -> Prop)
          `(mR : Proper (RA ==> RA ==> iff) R) :
    Proper (RA ==> RA ==> iff) (complement R) := _.
  
  Next Obligation.
  Proof.
    unfold complement.
    pose (mR x y H x0 y0 H0).
    intuition.
  Qed.
 
  (** The [flip] too, actually the [flip] instance is a bit more general. *)

  Definition flip_proper (RA : relation A) (RB : relation B) (RC : relation C)
          `(mor : Proper (RA ==> RB ==> RC) f) :
    Proper (RB ==> RA ==> RC) (flip f).
  Proof. reduce. apply mor ; auto. Defined.


  (** Every Transitive relation gives rise to a binary morphism on [impl],
   contravariant in the first argument, covariant in the second. *)
  
  Global Program 
  Instance trans_contra_co_morphism
    `(Transitive A R) : Proper (R --> R ++> impl) R.
  
  Next Obligation.
  Proof with auto.
    transitivity x...
    transitivity x0...
  Qed.

  (** Proper declarations for partial applications. *)

  Global Program 
  Instance trans_contra_inv_impl_morphism
  `(Transitive A R) : Proper (R --> flip impl) (R x) | 3.

  Next Obligation.
  Proof with auto.
    transitivity y...
  Qed.

  Global Program 
  Instance trans_co_impl_morphism
    `(Transitive A R) : Proper (R ++> impl) (R x) | 3.

  Next Obligation.
  Proof with auto.
    transitivity x0...
  Qed.

  Global Program 
  Instance trans_sym_co_inv_impl_morphism
    `(PER A R) : Proper (R ++> flip impl) (R x) | 3.

  Next Obligation.
  Proof with auto.
    transitivity y... symmetry...
  Qed.

  Global Program Instance trans_sym_contra_impl_morphism
    `(PER A R) : Proper (R --> impl) (R x) | 3.

  Next Obligation.
  Proof with auto.
    transitivity x0... symmetry...
  Qed.

  Global Program Instance per_partial_app_morphism
  `(PER A R) : Proper (R ==> iff) (R x) | 2.

  Next Obligation.
  Proof with auto.
    split. intros ; transitivity x0...
    intros.
    transitivity y...
    symmetry...
  Qed.

  (** Every Transitive relation induces a morphism by "pushing" an [R x y] on the left of an [R x z] proof to get an [R y z] goal. *)

  Global Program 
  Instance trans_co_eq_inv_impl_morphism
  `(Transitive A R) : Proper (R ==> (@eq A) ==> flip impl) R | 2.

  Next Obligation.
  Proof with auto.
    transitivity y...
  Qed.

  (** Every Symmetric and Transitive relation gives rise to an equivariant morphism. *)

  Global Program 
  Instance PER_morphism `(PER A R) : Proper (R ==> R ==> iff) R | 1.

  Next Obligation.
  Proof with auto.
    split ; intros.
    transitivity x0... transitivity x... symmetry...

    transitivity y... transitivity y0... symmetry...
  Qed.

  Lemma symmetric_equiv_flip `(Symmetric A R) : relation_equivalence R (flip R).
  Proof. firstorder. Qed.

  Global Program Instance compose_proper RA RB RC :
    Proper ((RB ==> RC) ==> (RA ==> RB) ==> (RA ==> RC)) (@compose A B C).

  Next Obligation.
  Proof.
    simpl_relation.
    unfold compose. apply H. apply H0. apply H1.
  Qed.

  (** Coq functions are morphisms for Leibniz equality,
     applied only if really needed. *)

  Global Instance reflexive_eq_dom_reflexive `(Reflexive B R') :
    Reflexive (@Logic.eq A ==> R').
  Proof. simpl_relation. Qed.

  (** [respectful] is a morphism for relation equivalence. *)
  
  Global Instance respectful_morphism :
    Proper (relation_equivalence ++> relation_equivalence ++> relation_equivalence) 
           (@respectful A B).
  Proof.
    reduce.
    unfold respectful, relation_equivalence, predicate_equivalence in * ; simpl in *.
    split ; intros.

    apply H0.
    apply H1.
    apply H.
    assumption.
    
    apply H0.
    apply H1.
    apply H.
    assumption.
  Qed.

  (** [R] is Reflexive, hence we can build the needed proof. *)

  Lemma Reflexive_partial_app_morphism A' (R : relation A) (R' : relation A')
        `(Proper (R ==> R') m, Proper R x) :
    Proper R' (m x).
  Proof. simpl_relation. Qed.
  
  Lemma flip_respectful (R : relation A) (R' : relation B) :
    relation_equivalence (flip (R ==> R')) (flip R ==> flip R').
  Proof.
    intros.
    unfold flip, respectful.
    split ; intros ; intuition.
  Qed.

  (** Treating flip: can't make them direct instances as we
   need at least a [flip] present in the goal. *)
  
  Lemma flip1 `(subrelation A R' R) : subrelation (flip (flip R')) R.
  Proof. firstorder. Defined.
  
  Lemma flip2 `(subrelation A R R') : subrelation R (flip (flip R')).
  Proof. firstorder. Defined.
  
  (** That's if and only if *)
  
  Lemma eq_subrelation `(Reflexive A R) : subrelation (@eq A) R.
  Proof. simpl_relation. Qed.

  (** Once we have normalized, we will apply this instance to simplify the problem. *)
  
  Definition proper_flip_proper `(mor : Proper (R : relation A) m) : Proper (flip R) m := mor.
  
End GenericInstances.

Arguments flip1 /.
Arguments flip2 /.
Arguments flip_proper /.

Class PartialApplication.

CoInductive normalization_done : Prop := did_normalization.

Class Params {A : Type} (of : A) (arity : nat).

Ltac partial_application_tactic :=
  let rec do_partial_apps H m cont := 
    match m with
      | ?m' ?x => class_apply @Reflexive_partial_app_morphism ; 
        [(do_partial_apps H m' ltac:(idtac))|clear H]
      | _ => cont
    end
  in
  let rec do_partial H ar m := 
    match ar with
      | 0%nat => do_partial_apps H m ltac:(fail 1)
      | S ?n' =>
        match m with
          ?m' ?x => do_partial H n' m'
        end
    end
  in
  let params m sk fk :=
    (let m' := fresh in head_of_constr m' m ;
     let n := fresh in evar (n:nat) ;
     let v := eval compute in n in clear n ;
      let H := fresh in
        assert(H:Params m' v) by (subst m'; typeclasses eauto) ;
          let v' := eval compute in v in subst m';
            (sk H v' || fail 1))
    || fk
  in
  let on_morphism m cont :=
    params m ltac:(fun H n => do_partial H n m)
      ltac:(cont)
  in
  match goal with
    | [ _ : normalization_done |- _ ] => fail 1
    | [ _ : @Params _ _ _ |- _ ] => fail 1
    | [ |- @Proper ?T _ (?m ?x) ] =>
      match goal with
        | [ H : PartialApplication |- _ ] =>
          class_apply @Reflexive_partial_app_morphism; [|clear H]
        | _ => on_morphism (m x)
          ltac:(class_apply @Reflexive_partial_app_morphism)
      end
  end.

(** Bootstrap !!! *)

Instance proper_proper : Proper (relation_equivalence ==> eq ==> eq ==> iff) (@Related A A).
Proof.
  simpl_relation.
  reduce in H.
  split ; red ; intros; firstorder.
Qed.

(* Ltac proper_reflexive := *)
(*   match goal with *)
(*     | [ _ : normalization_done |- _ ] => fail 1 *)
(*     | _ => class_apply proper_eq || class_apply @reflexive_proper *)
(*   end. *)
(* Hint Extern 7 (@Proper _ _ _) => proper_reflexive  *)
(*   : typeclass_instances. *)


Hint Extern 1 (subrelation (flip _) _) => class_apply @flip1 : typeclass_instances.
Hint Extern 1 (subrelation _ (flip _)) => class_apply @flip2 : typeclass_instances.

Hint Extern 1 (Proper _ (complement _)) => apply @complement_proper 
  : typeclass_instances.
Hint Extern 1 (Proper _ (flip _)) => apply @flip_proper 
  : typeclass_instances.
Hint Extern 2 (@Proper _ (flip _) _) => class_apply @proper_flip_proper 
  : typeclass_instances.
Hint Extern 4 (@Proper _ _ _) => partial_application_tactic 
  : typeclass_instances.

(** Related theory *)

Hint Extern 0 (Related _ _ _) =>
match goal with
  |- let _ := _ in _ => let hyp := fresh in intros hyp
end : typeclass_instances.

(* Instance proper_proxy_related_proxy A (R : relation A) m : *)
(*   ProperProxy R m -> RelatedProxy R m m := fun x => x. *)

(* Instance related_proxy_related A (R : relation A) m m' : *)
(*   Related R m m' -> RelatedProxy R m m' := fun x => x. *)

(** Applications *)

Lemma related_app A (R : relation A) B (S : relation B) f f' a a' :
  Related (R ==> S)%signature f f' -> Related R a a' ->
  Related S (f a) (f' a').
Proof. intros H; intros H'. apply H. apply H'. Defined.
Arguments related_app /.

Lemma related_app_dep {A A'} (R : A -> A' -> Prop)
      {B : A -> Type} {B' : A' -> Type} (S : forall x y, R x y -> B x -> B' y -> Prop)
      (f : forall x : A, B x) (f' : forall x : A', B' x) a a' :
  Related (∀ H : R a a', S a a' H)%signature f f' ->
  forall H : Related R a a',
    Related (S a a' H) (f a) (f' a').
Proof. intros H; intros H'. apply H. Defined.
Arguments related_app_dep /.

Lemma related_app_nodep {A A'}
      {B : A -> Type} {B' : A' -> Type} (S : forall x y, B x -> B' y -> Prop)
      (f : forall x : A, B x) (f' : forall x : A', B' x) (t : A) (u : A') :
  Related (pointwise_relation_hetero (fun a a' => S a a'))%signature f f' ->
  Related (S t u) (f t) (f' u).
Proof. intros H'. apply H'. Defined.
Arguments related_app_nodep /.

Hint Extern 3 (Related (∀ _ : ?R x y, ?S) ?s _) =>
  progress change (Proper (R ==> S) s) : typeclass_instances.

Ltac is_indep ty :=
  let hty := eval hnf in ty in
  match hty with
  | forall _ : _, ?B => idtac
  end.

Ltac related_app_tac :=
  match goal with
  | |- Related ?S (?f ?a) (?f' ?a') =>
    lazymatch goal with
    | [ H : Related ?R a a' |- _ ] =>
      (* idtac "Found matching argument"; *)
      let fty := type of f in
      let fty' := type of f' in
      tryif once (is_indep fty; unify fty fty')
      then
        (* idtac "Applying non-dependent congruence"; *)
        once (refinetc (@related_app _ _ _ _ f f' a a' _ H); clear H)
        (* idtac "Applied non-dependent congruence"; show_goal *)
      else
        (pattern a, a', H;
         (* show_goal; *)
         let pred :=
             match goal with
               |- (fun xa xa' H => Related (@?Q xa xa' H) _ _) _ _ _ => constr:(Q)
             end
         in
        match pred with
        | (fun xa xa' H => @?Q xa xa' H) =>
          (* idtac "Found dependent predicate"; *)
            cbv beta;
            let newpred := constr:(fun xa xa' H => pred xa xa' H) in
            refinetc (@related_app_dep _ _ R _ _ newpred f f' a a' _ H); cbv beta;
            clear H
                                                                                       
        | (fun xa xa' _ => @?Q xa xa') => 
          (* idtac "Found non-dependent predicate" Q; *)
            refinetc (@related_app_nodep _ _ _ _ Q f f' a a' _); cbv beta
        end)
    | _ =>
      let fty := type of f in
      let fty' := type of f' in
      tryif once (is_indep fty; unify fty fty') then
        once (refinetc (@related_app _ _ _ _ f f' a a' _ _))
      else
        ((* idtac "No matching argument"; *)
          pattern a, a';
        (* show_goal; *)
        let pred :=
            match goal with
              |- (fun xa xa' => Related (@?Q xa xa') _ _) _ _ => constr:(Q)
            end
        in simpl;
          match pred with
          | _ =>
            (* idtac "applying nodep"; *)
            refinetc (@related_app _ _ _ _ f f' a _ _ _) ||
            refinetc (@related_app_nodep _ _ _ _ pred f f' a a' _); cbv beta
        | (fun xa xa' => @?Q xa xa') =>
          let tya := type of a in
          let tya' := type of a' in
          let id := fresh in 
          evar(id : tya -> tya' -> Prop);
          let newrel := constr:(fun xa xa' (H : id xa xa') => pred xa xa') in
            (* cbv beta bug , no subst in evars! *) simpl;
          (* show_goal; *)
            (* idtac "newpred" newpred; *)
          refinetc (@related_app_dep _ _ id _ _ newrel f f' a a' _ _); subst id;
          cbv beta
        end)
    | _ =>
      refinetc (@related_app _ _ _ S f f' a _ _ _) ||
      refinetc (@related_app_dep _ _ _ _ _ _ f f' a _ _ _)
    end
  end.

Hint Extern 3 (Related _ (_ _) (_ _)) => related_app_tac : typeclass_instances.

(** Abstractions *)

Instance related_lambda {A A' : Type} (B : A -> Type) (B' : A' -> Type)
         (b : forall x : A, B x) (b' : forall y : A', B' y)
         (R : hrel A A') (S : forall x y (α : R x y), B x -> B' y -> Prop) :
  (forall x y (α : Related R x y), Related (S x y α) (b x) (b' y)) ->
  Related (∀ α : R x y, S x y α) (fun x => b x) (fun y => b' y).
Proof. intros H f g. apply H. Defined.
Arguments related_lambda /.

(** Subrelations *)

Instance related_subrelation {A B} (R S : hrel A B) x y :
  Related R x y -> hsubrelation _ _ R S -> Related S x y | 10.
Proof. firstorder. Defined.
Hint Cut [_* related_subrelation related_subrelation] : typeclass_instances.
Arguments related_subrelation /.

Local Open Scope signature_scope.
Arguments hsubrelation {A B} _ _.

(* Instance hetero_subrel {A B} (R R' : A -> B -> Prop) {C D} (S S' : C -> D -> Prop) : *)
(*   subrelation_h _ _ R' R -> subrelation_h _ _ S S' -> *)
(*   subrelation_h _ _ (∀ _ : R, S) (∀ _ : R', S'). *)
(* Proof. firstorder. Defined. *)

Instance hsubrelation_resp {A} (R R' : A -> A -> Prop) {C} (S S' : C -> C -> Prop) :
  hsubrelation R' R -> hsubrelation S S' ->
  hsubrelation (∀ _ : R, S) (R' ==> S').
Proof. firstorder. Defined.
Arguments hsubrelation_resp /. 

Instance hsubrelation_respectful_hetero {A B} {C D} R R' S S' :
  forall subRR' : hsubrelation R' R,
    (forall x y (H : R' x y), hsubrelation (S x y (subRR' x y H)) (S' x y H)) ->
    hsubrelation (@respectful_hetero A B C D R S)
                 (∀ H : R' x y, S' x y H).
Proof.
  intros subRR' subSS' f g Sfg x y R'xy.
  apply subSS'. apply Sfg.
Defined.
Arguments hsubrelation_respectful_hetero /.

Lemma hsubrelation_refl {A B} (R : hrel A B) : hsubrelation R R.
Proof. firstorder. Defined.
Arguments hsubrelation_refl /.

Hint Extern 4 (hsubrelation _ _) =>
  solve [ eapply hsubrelation_refl ] : typeclass_instances.

Instance subrelation_hsubrelation A (R S : hrel A A) :
  subrelation R S -> hsubrelation R S | 1000 := fun x => x.
Instance hsubrelation_subrelation A (R S : hrel A A) :
  hsubrelation R S -> subrelation R S | 1000 := fun x => x.
Hint Cut [_* subrelation_hsubrelation (_*) hsubrelation_subrelation]
  : typeclass_instances.
Hint Cut [_* hsubrelation_subrelation (_*) subrelation_hsubrelation]
  : typeclass_instances.
Arguments subrelation_hsubrelation /.
Arguments hsubrelation_subrelation /.

Class NotArrow {A B : Type} (R : hrel A B).
Hint Extern 0 (NotArrow ?R) =>
  match R with
  | @respectful_hetero _ _ _ _ _ _ => fail 1
  | respectful _ _ => fail 1
  | pointwise_relation _ _ _ => fail 1
  | _ => split
  end : typeclass_instances.

Instance related_refl {A} (R : relation A)
         (NA : NotArrow R) (** Prevents finding eq ==> eq to be reflexive! *)
         (HR : Reflexive R) (m : A) :
  Related R m m | 2.
Proof. red. reflexivity. Defined.
Arguments related_refl /.
Hint Cut [_* related_subrelation related_refl] : typeclass_instances.

(** Special-purpose class to do normalization of signatures w.r.t. flip. *)

Section Normalize.
  Context (A : Type).

  Class Normalizes (m : relation A) (m' : relation A) : Prop :=
    normalizes : relation_equivalence m m'.
  
  (** Current strategy: add [flip] everywhere and reduce using [subrelation]
   afterwards. *)

  Lemma proper_normalizes_proper (R1 : relation A)
        `(Normalizes R0 R1, Proper R1 m) : Proper R0 m.
  Proof.
    red in H, Proper0.
    apply H. 
    assumption.
  Qed.

  Lemma flip_atom R : Normalizes R (flip (flip R)).
  Proof.
    firstorder.
  Qed.

End Normalize.

Lemma flip_arrow {A : Type} {B : Type}
      `(NA : Normalizes A R (flip R'''), NB : Normalizes B R' (flip R'')) :
  Normalizes (A -> B) (R ==> R') (flip (R''' ==> R'')%signature).
Proof. 
  (* FIXME should be a rewrite *)
  unfold Normalizes in *. intros.
  unfold relation_equivalence in *. 
  unfold predicate_equivalence in *. simpl in *.
  unfold respectful. unfold flip in *. firstorder auto.
  apply NB. apply H. apply NA. apply H0.
  apply NB. apply H. apply NA. apply H0.
Qed.

Ltac normalizes :=
  match goal with
    | [ |- Normalizes _ (respectful _ _) _ ] => class_apply @flip_arrow
    | _ => class_apply @flip_atom
  end.

Ltac proper_normalization :=
  match goal with
    | [ _ : normalization_done |- _ ] => fail 1
    | [ _ : apply_subrelation |- @Proper _ ?R _ ] => 
      let H := fresh "H" in
      set(H:=did_normalization) ; class_apply @proper_normalizes_proper
  end.

Hint Extern 1 (Normalizes _ _ _) => normalizes : typeclass_instances.
Hint Extern 6 (@Proper _ _ _) => proper_normalization 
  : typeclass_instances.
