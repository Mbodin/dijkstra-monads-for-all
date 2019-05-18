(* -*- coding: utf-8;  -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Typeclass-based morphism definition and standard, minimal instances

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

From Coq Require Import Program.Basics.
From Coq Require Import Program.Tactics.
From Mon Require Export SRelation.SRelationClasses.

Generalizable Variables A eqA B C D R RA RB RC m f x y.
Local Obligation Tactic := simpl_srelation.

(** * Morphisms.

   We now turn to the definition of [SProper] and declare standard instances.
   These will be used by the [setoid_rewrite] tactic later. *)

(** A morphism for a srelation [R] is a proper element of the srelation.
   The srelation [R] will be instantiated by [srespectful] and [A] by an arrow
   type for usual morphisms. *)
Section SProper.
  Let U := Type.
  Context {A B : U}.

  Class SProper (R : srelation A) (m : A) : SProp :=
    proper_prf : R m m.

  (** Every element in the carrier of a reflexive srelation is a morphism
   for this srelation.  We use a proxy class for this case which is used
   internally to discharge reflexivity constraints.  The [Reflexive]
   instance will almost always be used, but it won't apply in general to
   any kind of [SProper (A -> B) _ _] goal, making proof-search much
   slower. A cleaner solution would be to be able to set different
   priorities in different hint bases and select a particular hint
   database for resolution of a type class constraint. *)

  Class SProperProxy (R : srelation A) (m : A) : SProp :=
    proper_proxy : R m m.

  Lemma eq_proper_proxy (x : A) : SProperProxy (@sEq A) x.
  Proof. firstorder. Qed.
  
  Lemma reflexive_proper_proxy `(Reflexive A R) (x : A) : SProperProxy R x.
  Proof. firstorder. Qed.

  Lemma proper_proper_proxy x `(SProper R x) : SProperProxy R x.
  Proof. firstorder. Qed.

  (** SRespectful morphisms. *)
  
  (** The fully dependent version, not used yet. *)
  
  Definition srespectful_hetero
  (A B : Type)
  (C : A -> Type) (D : B -> Type)
  (R : A -> B -> SProp)
  (R' : forall (x : A) (y : B), C x -> D y -> SProp) :
    (forall x : A, C x) -> (forall x : B, D x) -> SProp :=
    fun f g => forall x y, R x y -> R' x y (f x) (g y).

  (** The non-dependent version is an instance where we forget dependencies. *)
  
  Definition srespectful (R : srelation A) (R' : srelation B) : srelation (A -> B) :=
    Eval compute in @srespectful_hetero A A (fun _ => B) (fun _ => B) R (fun _ _ => R').

End SProper.

(** We favor the use of Leibniz equality or a declared reflexive srelation 
  when resolving [SProperProxy], otherwise, if the srelation is given (not an evar),
  we fall back to [SProper]. *)
Hint Extern 1 (SProperProxy _ _) => 
  class_apply @eq_proper_proxy || class_apply @reflexive_proper_proxy : typeclass_instances.

Hint Extern 2 (SProperProxy ?R _) => 
  not_evar R; class_apply @proper_proper_proxy : typeclass_instances.

(** Notations reminiscent of the old syntax for declaring morphisms. *)
Delimit Scope signature_scope with signature.

Module SProperNotations.

  Notation " R s++> R' " := (@srespectful _ _ (R%signature) (R'%signature))
    (right associativity, at level 55) : signature_scope.

  Notation " R s==> R' " := (@srespectful _ _ (R%signature) (R'%signature))
    (right associativity, at level 55) : signature_scope.

  Notation " R s--> R' " := (@srespectful _ _ (flip (R%signature)) (R'%signature))
    (right associativity, at level 55) : signature_scope.

End SProperNotations.

Arguments SProper {A}%type R%signature m.
Arguments srespectful {A B}%type (R R')%signature _ _.

Export SProperNotations.

Local Open Scope signature_scope.

(** [solve_proper] try to solve the goal [SProper (?==> ... ==>?) f]
    by repeated introductions and setoid rewrites. It should work
    fine when [f] is a combination of already known morphisms and
    quantifiers. *)

Ltac solve_srespectful t :=
 match goal with
   | |- srespectful _ _ _ _ =>
     let H := fresh "H" in
     intros ? ? H; solve_srespectful ltac:(setoid_rewrite H; t)
   | _ => t; reflexivity
 end.

Ltac solve_proper := unfold SProper; solve_srespectful ltac:(idtac).

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
    evar (Rx : srelation T);
    let H := fresh in
    assert (H : (Rx s==>R)%signature f f');
    unfold Rx in *; clear Rx; [ f_equiv | apply H; clear H; try reflexivity ]
  | |- ?R ?f ?f' =>
    solve [change (SProper R f); eauto with typeclass_instances | reflexivity ]
  | _ => idtac
 end.

Section Srelations.
  Let U := Type.
  Context {A B : U} (P : A -> U).

  (** [forall_def] reifies the dependent product as a definition. *)
  
  Definition forall_def : Type := forall x : A, P x.
  
  (** Dependent pointwise lifting of a srelation on the range. *)
  
  Definition forall_srelation 
             (sig : forall a, srelation (P a)) : srelation (forall x, P x) :=
    fun f g => forall a, sig a (f a) (g a).

  (** Non-dependent pointwise lifting *)
  Definition pointwise_srelation (R : srelation B) : srelation (A -> B) :=
    fun f g => forall a, R (f a) (g a).

  Lemma pointwise_pointwise (R : srelation B) :
    srelation_equivalence (pointwise_srelation R) (@sEq A s==> R).
  Proof. split ; reduce ; intros ;  subst_sEq ; firstorder. Qed.
  
  (** Subsrelations induce a morphism on the identity. *)
  
  Global Instance subsrelation_id_proper `(subsrelation A RA RA') : SProper (RA s==> RA') id.
  Proof. firstorder. Qed.

  (** The subsrelation property goes through products as usual. *)
  
  Lemma subsrelation_srespectful `(subl : subsrelation A RA' RA, subr : subsrelation B RB RB') :
    subsrelation (RA s==> RB) (RA' s==> RB').
  Proof. unfold subsrelation in *; firstorder. Qed.

  (** And of course it is reflexive. *)
  
  Lemma subsrelation_refl R : @subsrelation A R R.
  Proof. unfold subsrelation; firstorder. Qed.

  (** [SProper] is itself a covariant morphism for [subsrelation].
   We use an unconvertible premise to avoid looping.
   *)
  
  Lemma subsrelation_proper `(mor : SProper A R' m) 
        `(unc : Unconvertible (srelation A) R R')
        `(sub : subsrelation A R' R) : SProper R m.
  Proof.
    intros. apply sub. apply mor.
  Qed.

  Global Instance proper_subsrelation_proper :
    SProper (subsrelation s++> sEq s==> s_impl) (@SProper A).
  Proof. reduce. subst_sEq. firstorder. Qed.

  Global Instance pointwise_subsrelation `(sub : subsrelation B R R') :
    subsrelation (pointwise_srelation R) (pointwise_srelation R') | 4.
  Proof. reduce. unfold pointwise_srelation in *. apply sub. apply H. Qed.
  
  (** For dependent function types. *)
  Lemma forall_subsrelation (R S : forall x : A, srelation (P x)) :
    (forall a, subsrelation (R a) (S a)) -> subsrelation (forall_srelation R) (forall_srelation S).
  Proof. reduce. apply H. apply H0. Qed.
End Srelations.


Typeclasses Opaque srespectful pointwise_srelation forall_srelation.
Arguments forall_srelation {A P}%type sig%signature _ _.
Arguments pointwise_srelation A%type {B}%type R%signature _ _.

Notation "X ⇢ R" := (pointwise_srelation X R) (at level 60).
  
Hint Unfold Reflexive : core.
Hint Unfold Symmetric : core.
Hint Unfold Transitive : core.

(** Resolution with subsrelation: favor decomposing products over applying reflexivity
  for unconstrained goals. *)
Ltac subsrelation_tac T U :=
  (is_ground T ; is_ground U ; class_apply @subsrelation_refl) ||
    class_apply @subsrelation_srespectful || class_apply @subsrelation_refl.

Hint Extern 3 (@subsrelation _ ?T ?U) => subsrelation_tac T U : typeclass_instances.

CoInductive apply_subsrelation : SProp := do_subsrelation.

Ltac proper_subsrelation :=
  match goal with
    [ H : apply_subsrelation |- _ ] => clear H ; class_apply @subsrelation_proper
  end.

Hint Extern 5 (@SProper _ ?H _) => proper_subsrelation : typeclass_instances.

(** Essential subsrelation instances for [iff], [impl] and [pointwise_srelation]. *)

Instance iff_impl_subsrelation : subsrelation siff s_impl | 2.
Proof. firstorder. Qed.

Instance iff_flip_impl_subsrelation : subsrelation siff (flip s_impl) | 2.
Proof. firstorder. Qed.

(** We use an extern hint to help unification. *)

Hint Extern 4 (subsrelation (@forall_srelation ?A ?B ?R) (@forall_srelation _ _ ?S)) =>
  apply (@forall_subsrelation A B R S) ; intro : typeclass_instances.

Section GenericInstances.
  (* Share universes *)
  Let U := Type.
  Context {A B C : U}.

  (** We can build a PER on the Coq function space if we have PERs on the domain and
   codomain. *)
  
  Program Instance srespectful_per `(PER A R, PER B R') : PER (R s==> R').

  Next Obligation.
  Proof with auto.
    assert(R x0 x0).
    stransitivity y0... ssymmetry...
    stransitivity (y x0)...
  Qed.

  (** The complement of a srelation conserves its proper elements. *)
  
  Program Definition complement_proper
          `(mR : SProper (A -> A -> SProp) (RA s==> RA s==> siff) R) :
    SProper (RA s==> RA s==> siff) (complement R) := _.
  
  Next Obligation.
  Proof.
    unfold complement.
    destruct (mR x y H x0 y0 H0).
    intuition ; auto.
  Qed.
 
  (** The [flip] too, actually the [flip] instance is a bit more general. *)

  Program Definition flip_proper
          `(mor : SProper (A -> B -> C) (RA s==> RB s==> RC) f) :
    SProper (RB s==> RA s==> RC) (flip f) := _.
  
  Next Obligation.
  Proof.
    apply mor ; auto.
  Qed.


  (** Every Transitive srelation gives rise to a binary morphism on [impl],
   contravariant in the first argument, covariant in the second. *)
  
  Global Program 
  Instance trans_contra_co_morphism
    `(Transitive A R) : SProper (R s--> R s++> s_impl) R.
  
  Next Obligation.
  Proof with auto.
    stransitivity x...
    stransitivity x0...
  Qed.

  (** SProper declarations for partial applications. *)

  Global Program 
  Instance trans_contra_inv_impl_morphism
  `(Transitive A R) : SProper (R s--> flip s_impl) (R x) | 3.

  Next Obligation.
  Proof with auto.
    stransitivity y...
  Qed.

  Global Program 
  Instance trans_co_impl_morphism
    `(Transitive A R) : SProper (R s++> s_impl) (R x) | 3.

  Next Obligation.
  Proof with auto.
    stransitivity x0...
  Qed.

  Global Program 
  Instance trans_sym_co_inv_impl_morphism
    `(PER A R) : SProper (R s++> flip s_impl) (R x) | 3.

  Next Obligation.
  Proof with auto.
    stransitivity y... ssymmetry...
  Qed.

  Global Program Instance trans_sym_contra_impl_morphism
    `(PER A R) : SProper (R s--> s_impl) (R x) | 3.

  Next Obligation.
  Proof with auto.
    stransitivity x0... ssymmetry...
  Qed.

  Global Program Instance per_partial_app_morphism
  `(PER A R) : SProper (R s==> siff) (R x) | 2.

  Next Obligation.
  Proof with auto.
    split. intros ; stransitivity x0...
    intros.
    stransitivity y...
    ssymmetry...
  Qed.

  (** Every Transitive srelation induces a morphism by "pushing" an [R x y] on the left of an [R x z] proof to get an [R y z] goal. *)

  Global Program 
  Instance trans_co_eq_inv_impl_morphism
  `(Transitive A R) : SProper (R s==> (@sEq A) s==> flip s_impl) R | 2.

  Next Obligation.
  Proof with auto.
    subst_sEq ; stransitivity y...
  Qed.

  (** Every Symmetric and Transitive srelation gives rise to an equivariant morphism. *)

  Global Program 
  Instance PER_morphism `(PER A R) : SProper (R s==> R s==> siff) R | 1.

  Next Obligation.
  Proof with auto.
    split ; intros.
    stransitivity x0... stransitivity x... ssymmetry...
    
    stransitivity y... stransitivity y0... ssymmetry...
  Qed.

  Lemma symmetric_equiv_flip `(Symmetric A R) : srelation_equivalence R (flip R).
  Proof. firstorder. Qed.

  Global Program Instance compose_proper RA RB RC :
    SProper ((RB s==> RC) s==> (RA s==> RB) s==> (RA s==> RC)) (@compose A B C).

  Next Obligation.
  Proof.
    simpl_srelation.
    unfold compose. apply H. apply H0. apply H1.
  Qed.

  (** Coq functions are morphisms for Leibniz equality,
     applied only if really needed. *)

  Global Instance reflexive_eq_dom_reflexive `(Reflexive B R') :
    Reflexive (@sEq A s==> R').
  Proof. simpl_srelation. subst_sEq. auto. Qed.

  (** [srespectful] is a morphism for srelation equivalence. *)
  
  Global Instance srespectful_morphism :
    SProper (srelation_equivalence s++> srelation_equivalence s++> srelation_equivalence) 
           (@srespectful A B).
  Proof.
    reduce.
    unfold srespectful, srelation_equivalence, spredicate_equivalence in * ; simpl in *.
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

  Lemma Reflexive_partial_app_morphism `(SProper (A -> B) (R s==> R') m, SProperProxy A R x) :
    SProper R' (m x).
  Proof. simpl_srelation. Qed.
  
  Lemma flip_srespectful (R : srelation A) (R' : srelation B) :
    srelation_equivalence (flip (R s==> R')) (flip R s==> flip R').
  Proof.
    intros.
    unfold flip, srespectful.
    split ; intros ; intuition.
  Qed.

  
  (** Treating flip: can't make them direct instances as we
   need at least a [flip] present in the goal. *)
  
  Lemma flip1 `(subsrelation A R' R) : subsrelation (flip (flip R')) R.
  Proof. firstorder. Qed.
  
  Lemma flip2 `(subsrelation A R R') : subsrelation R (flip (flip R')).
  Proof. firstorder. Qed.
  
  (** That's if and only if *)
  
  Lemma eq_subsrelation `(Reflexive A R) : subsrelation (@sEq A) R.
  Proof. simpl_srelation ; subst_sEq ; auto. Qed.

  (** Once we have normalized, we will apply this instance to simplify the problem. *)
  
  Definition proper_flip_proper `(mor : SProper A R m) : SProper (flip R) m := mor.
  
  (** Every reflexive srelation gives rise to a morphism, 
  only for immediately solving goals without variables. *)
  
  Lemma reflexive_proper `{Reflexive A R} (x : A) : SProper R x.
  Proof. firstorder. Qed.
  
  Lemma proper_eq (x : A) : SProper (@sEq A) x.
  Proof. reduce_goal. apply reflexive_proper. Qed.
  
End GenericInstances.

Class PartialApplication.

CoInductive normalization_done : SProp := did_normalization.

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
    lazymatch ar with
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
        assert(H:Params m' v) by (subst m'; once typeclasses eauto) ;
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
    | [ |- @SProper ?T _ (?m ?x) ] =>
      match goal with
        | [ H : PartialApplication |- _ ] =>
          class_apply @Reflexive_partial_app_morphism; [|clear H]
        | _ => on_morphism (m x)
          ltac:(class_apply @Reflexive_partial_app_morphism)
      end
  end.

(** Bootstrap !!! *)

Instance sproper_proper : SProper (srelation_equivalence s==> sEq s==> siff) (@SProper A).
Proof.
  simpl_srelation.
  reduce in H.
  split ; red ; intros.
  apply H.
  subst_sEq.
  assumption.
  subst_sEq.
  apply H.
  assumption.
Qed.

Ltac proper_reflexive :=
  match goal with
    | [ _ : normalization_done |- _ ] => fail 1
    | _ => class_apply proper_eq || class_apply @reflexive_proper
  end.


Hint Extern 1 (subsrelation (flip _) _) => class_apply @flip1 : typeclass_instances.
Hint Extern 1 (subsrelation _ (flip _)) => class_apply @flip2 : typeclass_instances.

Hint Extern 1 (SProper _ (complement _)) => apply @complement_proper 
  : typeclass_instances.
Hint Extern 1 (SProper _ (flip _)) => apply @flip_proper 
  : typeclass_instances.
Hint Extern 2 (@SProper _ (flip _) _) => class_apply @proper_flip_proper 
  : typeclass_instances.
Hint Extern 4 (@SProper _ _ _) => partial_application_tactic 
  : typeclass_instances.
Hint Extern 7 (@SProper _ _ _) => proper_reflexive 
  : typeclass_instances.

(** Special-purpose class to do normalization of signatures w.r.t. flip. *)

Section Normalize.
  Context (A : Type).

  Class Normalizes (m : srelation A) (m' : srelation A) : SProp :=
    normalizes : srelation_equivalence m m'.
  
  (** Current strategy: add [flip] everywhere and reduce using [subsrelation]
   afterwards. *)

  Lemma proper_normalizes_proper `(Normalizes R0 R1, SProper A R1 m) : SProper R0 m.
  Proof.
    red in H, H0.
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
  Normalizes (A -> B) (R s==> R') (flip (R''' s==> R'')%signature).
Proof. 
  unfold Normalizes in *. intros.
  unfold srelation_equivalence in *. 
  unfold spredicate_equivalence in *. simpl in *.
  unfold srespectful. unfold flip in *. firstorder.
  apply NB. apply H. apply NA. apply H0.
  apply NB. apply H. apply NA. apply H0.
Qed.

Ltac normalizes :=
  match goal with
    | [ |- Normalizes _ (srespectful _ _) _ ] => class_apply @flip_arrow
    | _ => class_apply @flip_atom
  end.

Ltac proper_normalization :=
  match goal with
    | [ _ : normalization_done |- _ ] => fail 1
    | [ _ : apply_subsrelation |- @SProper _ ?R _ ] => 
      let H := fresh "H" in
      set(H:=did_normalization) ; class_apply @proper_normalizes_proper
  end.

Hint Extern 1 (Normalizes _ _ _) => normalizes : typeclass_instances.
Hint Extern 6 (@SProper _ _ _) => proper_normalization 
  : typeclass_instances.

(** When the srelation on the domain is symmetric, we can
    flip the srelation on the codomain. Same for binary functions. *)

Lemma proper_sym_flip :
 forall `(Symmetric A R1)`(SProper (A->B) (R1 s==>R2) f),
 SProper (R1 s==>flip R2) f.
Proof.
intros A R1 Sym B R2 f Hf.
intros x x' Hxx'. apply Hf, Sym, Hxx'.
Qed.

Lemma proper_sym_flip_2 :
 forall `(Symmetric A R1)`(Symmetric B R2)`(SProper (A->B->C) (R1 s==>R2 s==>R3) f),
 SProper (R1 s==>R2 s==>flip R3) f.
Proof.
intros A R1 Sym1 B R2 Sym2 C R3 f Hf.
intros x x' Hxx' y y' Hyy'. apply Hf; auto.
Qed.

(** When the srelation on the domain is symmetric, a spredicate is
  compatible with [iff] as soon as it is compatible with [impl].
  Same with a binary srelation. *)

Lemma proper_sym_impl_iff : forall `(Symmetric A R)`(SProper _ (R s==>s_impl) f),
 SProper (R s==>siff) f.
Proof.
intros A R Sym f Hf x x' Hxx'. repeat red in Hf. split; eauto.
Qed.

Lemma proper_sym_impl_iff_2 :
 forall `(Symmetric A R)`(Symmetric B R')`(SProper _ (R s==>R' s==>s_impl) f),
 SProper (R s==>R' s==>siff) f.
Proof.
intros A R Sym B R' Sym' f Hf x x' Hxx' y y' Hyy'.
repeat red in Hf. split; eauto.
Qed.

(** A [PartialOrder] is compatible with its underlying equivalence. *)

Instance PartialOrder_proper `(PartialOrder A eqA R) :
  SProper (eqA s==>eqA s==>siff) R.
Proof.
intros.
apply proper_sym_impl_iff_2; auto with *.
intros x x' Hx y y' Hy Hr.
stransitivity x.
generalize (partial_order_equivalence x x'); compute; intuition.
stransitivity y; auto.
generalize (partial_order_equivalence y y'); compute; intuition.
Qed.

(** From a [PartialOrder] to the corresponding [StrictOrder]:
     [lt = le /\ ~eq].
    If the order is total, we could also say [gt = ~le]. *)

Lemma PartialOrder_StrictOrder `(PartialOrder A eqA R) :
  StrictOrder (srelation_conjunction R (complement eqA)).
Proof.
split; compute.
intros x (_,Hx). apply Hx, Equivalence_Reflexive.
intros x y z (Hxy,Hxy') (Hyz,Hyz'). split.
apply PreOrder_Transitive with y; assumption.
intro Hxz.
apply Hxy'.
apply partial_order_antisym; auto.
apply H in Hxz ; destruct Hxz ; stransitivity z ; assumption.
Qed.


(** From a [StrictOrder] to the corresponding [PartialOrder]:
     [le = lt \/ eq].
    If the order is total, we could also say [ge = ~lt]. *)

Lemma StrictOrder_PreOrder
 `(Equivalence A eqA, StrictOrder A R, SProper _ (eqA s==>eqA s==>siff) R) :
 PreOrder (srelation_disjunction R eqA).
Proof.
split.
intros x. right. sreflexivity.
intros x y z [Hxy|Hxy] [Hyz|Hyz].
left. stransitivity y; auto.
left. apply (H1 _ _ ltac:(sreflexivity) _ _ Hyz) ; assumption.
left. apply (H1 _ _ Hxy _ _ ltac:(sreflexivity)) ; assumption.
right. stransitivity y; auto.
Qed.

Hint Extern 4 (PreOrder (srelation_disjunction _ _)) => 
  class_apply StrictOrder_PreOrder : typeclass_instances.

Lemma StrictOrder_PartialOrder
  `(Equivalence A eqA, StrictOrder A R, SProper _ (eqA s==>eqA s==>siff) R) :
  PartialOrder eqA (srelation_disjunction R eqA).
Proof.
  intros. intros x y. compute. intuition.
  elim (StrictOrder_Irreflexive x).
  stransitivity y; auto.
Qed.

Hint Extern 4 (StrictOrder (srelation_conjunction _ _)) => 
  class_apply PartialOrder_StrictOrder : typeclass_instances.

Hint Extern 4 (PartialOrder _ (srelation_disjunction _ _)) => 
  class_apply StrictOrder_PartialOrder : typeclass_instances.
