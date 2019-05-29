(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Typeclass-based relations, tactics and standard instances

   This is the basic theory needed to formalize morphisms and setoids.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

From Coq Require Export Classes.Init.
From Coq Require Import Program.Basics.
From Coq Require Import Program.Tactics.
From Coq Require List.
(* Dangerous... we are redefining quite a lot of the same thing *)
From Coq Require Export Classes.RelationClasses.
From Coq Require Import Logic.StrictProp.
From Mon Require Export sprop.SPropBase.
From Mon Require Export SRelation.SRelation_Definitions.

Generalizable Variables A B C D R S T U l eqA eqB eqC eqD.

(** We allow to unfold the [relation] definition while doing morphism search. *)

Section Defs.
  Context {A : Type}.

  (** We rebind srelational properties in separate classes to be able to overload each proof. *)

  Class Reflexive (R : srelation A) : SProp :=
    reflexivity : forall x : A, R x x.

  Definition complement (R : srelation A) : srelation A := fun x y => R x y -> sEmpty.

  (** Opaque for proof-search. *)
  Typeclasses Opaque complement.
  
  (** These are convertible. *)
  Lemma complement_inverse R : complement (flip R) = flip (complement R).
  Proof. reflexivity. Qed.

  Class Irreflexive (R : srelation A) : SProp :=
    irreflexivity : Reflexive (complement R).

  Class Symmetric (R : srelation A) : SProp :=
    symmetry : forall {x y}, R x y -> R y x.
  
  Class Asymmetric (R : srelation A) : SProp :=
    asymmetry : forall {x y}, R x y -> R y x -> sEmpty.
  
  Class Transitive (R : srelation A) : SProp :=
    transitivity : forall {x y z}, R x y -> R y z -> R x z.

  (** Various combinations of reflexivity, symmetry and transitivity. *)
  
  (** A [PreOrder] is both Reflexive and Transitive. *)
  
  Class PreOrder (R : srelation A) : SProp := {
    PreOrder_Reflexive :> Reflexive R | 2 ;
    PreOrder_Transitive :> Transitive R | 2 }.

  (** A [StrictOrder] is both Irreflexive and Transitive. *)

  Class StrictOrder (R : srelation A) : SProp := {
    StrictOrder_Irreflexive :> Irreflexive R ;
    StrictOrder_Transitive :> Transitive R }.

  (** By definition, a strict order is also asymmetric *)
  Global Instance StrictOrder_Asymmetric `(StrictOrder R) : Asymmetric R.
  Proof. firstorder. Qed.

  (** A partial equivalence srelation is Symmetric and Transitive. *)
  
  Class PER (R : srelation A) : SProp := {
    PER_Symmetric :> Symmetric R | 3 ;
    PER_Transitive :> Transitive R | 3 }.

  (** Equivalence srelations. *)

  Class Equivalence (R : srelation A) : SProp := {
    Equivalence_Reflexive :> Reflexive R ;
    Equivalence_Symmetric :> Symmetric R ;
    Equivalence_Transitive :> Transitive R }.

  (** An Equivalence is a PER plus reflexivity. *)
  
  Global Instance Equivalence_PER {R} `(E:Equivalence R) : PER R | 10 :=
    { }. 

  (** An Equivalence is a PreOrder plus symmetry. *)

  Global Instance Equivalence_PreOrder {R} `(E:Equivalence R) : PreOrder R | 10 :=
    { }.

  (** We can now define antisymmetry w.r.t. an equivalence srelation on the carrier. *)
  
  Class Antisymmetric eqA `{equ : Equivalence eqA} (R : srelation A) : SProp :=
    antisymmetry : forall {x y}, R x y -> R y x -> eqA x y.

  Class subsrelation (R R' : srelation A) : SProp :=
    is_subsrelation : forall {x y}, R x y -> R' x y.
  
  (** Any symmetric srelation is equal to its inverse. *)
  
  Lemma subsrelation_symmetric R `(Symmetric R) : subsrelation (flip R) R.
  Proof. hnf. intros. red in H0. apply symmetry. assumption. Qed.

  Section flip.
  
    Lemma flip_Reflexive `{Reflexive R} : Reflexive (flip R).
    Proof. tauto. Qed.
    
    Program Definition flip_Irreflexive `(Irreflexive R) : Irreflexive (flip R) :=
      irreflexivity (R:=R).
    
    Program Definition flip_Symmetric `(Symmetric R) : Symmetric (flip R) :=
      fun x y H => symmetry (R:=R) H.
    
    Program Definition flip_Asymmetric `(Asymmetric R) : Asymmetric (flip R) :=
      fun x y H H' => asymmetry (R:=R) H H'.
    
    Program Definition flip_Transitive `(Transitive R) : Transitive (flip R) :=
      fun x y z H H' => transitivity (R:=R) H' H.

    Program Definition flip_Antisymmetric `(Antisymmetric eqA R) :
      Antisymmetric eqA (flip R).
    Proof. firstorder. Qed.

    (** Inversing the larger structures *)

    Lemma flip_PreOrder `(PreOrder R) : PreOrder (flip R).
    Proof. firstorder. Qed.

    Lemma flip_StrictOrder `(StrictOrder R) : StrictOrder (flip R).
    Proof. firstorder. Qed.

    Lemma flip_PER `(PER R) : PER (flip R).
    Proof. firstorder. Qed.

    Lemma flip_Equivalence `(Equivalence R) : Equivalence (flip R).
    Proof. firstorder. Qed.

  End flip.

  Section complement.

    Definition complement_Irreflexive `(Reflexive R)
      : Irreflexive (complement R).
    Proof. firstorder. Qed.

    Definition complement_Symmetric `(Symmetric R) : Symmetric (complement R).
    Proof. firstorder. Qed.
  End complement.


  (** Rewrite srelation on a given support: declares a srelation as a rewrite
   srelation for use by the generalized rewriting tactic.
   It helps choosing if a rewrite should be handled
   by the generalized or the regular rewriting tactic using leibniz equality.
   Users can declare an [RewriteSrelation A RA] anywhere to declare default
   srelations. This is also done automatically by the [Declare Srelation A RA]
   commands. *)

  Class RewriteSrelation (RA : srelation A).

  (** Any [Equivalence] declared in the context is automatically considered
   a rewrite srelation. *)
    
  Global Instance equivalence_rewrite_srelation `(Equivalence eqA) :
      RewriteSrelation eqA.
  Proof. Defined.

  (** Leibniz equality. *)
  Section Leibniz.
    Global Instance eq_Reflexive : Reflexive (@sEq A) := @sEq_refl A.
    Global Instance eq_Symmetric : Symmetric (@sEq A) := @sEq_sym A.
    Global Instance eq_Transitive : Transitive (@sEq A) := @sEq_trans A.
    
    (** Leibinz equality [eq] is an equivalence srelation.
        The instance has low priority as it is always applicable
        if only the type is constrained. *)
    
    Global Program Instance eq_equivalence : Equivalence (@sEq A) | 10.
  End Leibniz.
  
End Defs.

(* TODO : Is the Transitive class in Coq.Classes.Relation
      hardcoded in the transitivity tactic ? *)
Ltac sreflexivity := apply reflexivity.
Ltac stransitivity x := apply (@transitivity _ _ _ _ x).
Ltac estransitivity := eapply (@transitivity _ _ _ _ _ _).
Ltac ssymmetry := apply symmetry.


(** Default rewrite srelations handled by [setoid_rewrite]. *)
Instance: RewriteSrelation s_impl. Proof. Defined.
Instance: RewriteSrelation siff. Proof. Defined.

(** Hints to drive the typeclass resolution avoiding loops
 due to the use of full unification. *)
Hint Extern 1 (Reflexive (complement _)) => class_apply @irreflexivity : typeclass_instances.
Hint Extern 3 (Symmetric (complement _)) => class_apply complement_Symmetric : typeclass_instances.
Hint Extern 3 (Irreflexive (complement _)) => class_apply complement_Irreflexive : typeclass_instances.

Hint Extern 3 (Reflexive (flip _)) => apply flip_Reflexive : typeclass_instances.
Hint Extern 3 (Irreflexive (flip _)) => class_apply flip_Irreflexive : typeclass_instances.
Hint Extern 3 (Symmetric (flip _)) => class_apply flip_Symmetric : typeclass_instances.
Hint Extern 3 (Asymmetric (flip _)) => class_apply flip_Asymmetric : typeclass_instances.
Hint Extern 3 (Antisymmetric (flip _)) => class_apply flip_Antisymmetric : typeclass_instances.
Hint Extern 3 (Transitive (flip _)) => class_apply flip_Transitive : typeclass_instances.
Hint Extern 3 (StrictOrder (flip _)) => class_apply flip_StrictOrder : typeclass_instances.
Hint Extern 3 (PreOrder (flip _)) => class_apply flip_PreOrder : typeclass_instances.

Hint Extern 4 (subsrelation (flip _) _) => 
  class_apply @subsrelation_symmetric : typeclass_instances.

Arguments irreflexivity {A R Irreflexive} [x] _.
Arguments symmetry {A} {R} {_} [x] [y] _.
Arguments asymmetry {A} {R} {_} [x] [y] _ _.
Arguments transitivity {A} {R} {_} [x] [y] [z] _ _.
Arguments Antisymmetric A eqA {_} _.

Hint Resolve irreflexivity : ord.

Unset Implicit Arguments.

(** A HintDb for srelations. *)

Ltac solve_srelation :=
  match goal with
  | [ |- ?R ?x ?x ] => sreflexivity
  | [ H : ?R ?x ?y |- ?R ?y ?x ] => ssymmetry ; exact H
  end.

Hint Extern 4 => solve_srelation : srelations.

(** We can already dualize all these properties. *)

(** * Standard instances. *)

Ltac reduce_hyp H :=
  match type of H with
    | context [ _ <-> _ ] => fail 1
    | _ => red in H ; try reduce_hyp H
  end.

Ltac reduce_goal :=
  match goal with
    | [ |- _ <-> _ ] => fail 1
    | _ => red ; intros ; try reduce_goal
  end.

Tactic Notation "reduce" "in" hyp(Hid) := reduce_hyp Hid.

Ltac reduce := reduce_goal.

Tactic Notation "apply" "*" constr(t) :=
  first [ refine t | refine (t _) | refine (t _ _) | refine (t _ _ _) | refine (t _ _ _ _) |
    refine (t _ _ _ _ _) | refine (t _ _ _ _ _ _) | refine (t _ _ _ _ _ _ _) ].

Ltac simpl_srelation :=
  unfold flip, impl, arrow ; try reduce ; program_simpl ;
    try ( solve [ dintuition ]).

Local Obligation Tactic := simpl_srelation.

(** Logical implication. *)

Program Instance impl_Reflexive : Reflexive s_impl.
Program Instance impl_Transitive : Transitive s_impl.

(** Logical equivalence. *)

Instance iff_Reflexive : Reflexive siff.
Proof. intro ; split ; trivial. Qed.

Instance iff_Symmetric : Symmetric siff.
Proof. intros ? ? [] ; split ; assumption. Qed.

Instance iff_Transitive : Transitive siff.
Proof. intros ? ? ? [] [] ; split ; auto. Qed.

(** Logical equivalence [iff] is an equivalence srelation. *)

Program Instance iff_equivalence : Equivalence siff.


(** order on nat is a PreOrder *)

Instance sle_Reflexive : Reflexive Sle.
Proof. cbv ; apply sle_refl. Qed.

Instance sle_Transitive : Transitive Sle.
Proof. cbv ; apply sle_trans. Qed.

Program Instance sle_PreOrder : PreOrder Sle.

(** We now develop a generalization of results on srelations for arbitrary predicates.
   The resulting theory can be applied to homogeneous binary srelations but also to
   arbitrary n-ary predicates. *)

Local Open Scope list_scope.

(** A compact representation of non-dependent arities, with the codomain singled-out. *)

(* Note, we do not use [list Type] because it imposes unnecessary universe constraints *)
(* Specialize it for SProp, so we can revert to list  *)
Definition Slist : Type := list SProp.
Local Infix "::" := Tcons.
Definition Slist_to_Tlist (l:Slist) : Tlist :=
  List.fold_right (fun (P:SProp) tl => Tcons (Box P) tl) Tnil l.

Definition sarrows (l : Slist) (r : SProp) : SProp :=
  List.fold_right (fun (P r:SProp) => P -> r) r l.

Definition sarrows_to_arrows (l:Slist) (r:SProp) (f : sarrows l r)
           : arrows (Slist_to_Tlist l) (Box r).
Proof. induction l ; simpl in *; [|intros []] ; try constructor ; auto. Defined.

(** We define n-ary [predicate]s as functions into [SProp]. *)

Notation spredicate l := (arrows l SProp).

(** Unary predicates, or sets. *)

Definition unary_predicate A := spredicate (A::Tnil).

(** Homogeneous binary srelations, equivalent to [srelation A]. *)

Definition binary_srelation A := spredicate (A::A::Tnil).

(** We can close a predicate by universal or existential quantification. *)
Section PredicateQuantifiers.
  Import SPropNotations.
  Fixpoint predicate_all (l : Tlist) : spredicate l -> SProp :=
    match l with
      | Tnil => fun f => f
      | A :: tl => fun f => forall x : A, predicate_all tl (f x)
    end.

  Fixpoint predicate_exists (l : Tlist) : spredicate l -> SProp :=
    match l with
      | Tnil => fun (f: arrows Tnil SProp) => f
      | A :: tl => fun f => s∃ x : A, predicate_exists tl (f x)
    end.
End PredicateQuantifiers.



(** Pointwise lifting, equivalent to doing [pointwise_extension] and closing using [predicate_all]. *)

Fixpoint pointwise_lifting (op : binary_srelation SProp)  (l : Tlist) : binary_srelation (spredicate l) :=
  match l with
    | Tnil => fun R R' => op R R'
    | A :: tl => fun R R' =>
      forall x, pointwise_lifting op tl (R x) (R' x)
  end.

(** The n-ary equivalence srelation, defined by lifting the 0-ary [iff] srelation. *)

Definition spredicate_equivalence {l : Tlist} : binary_srelation (spredicate l) :=
  pointwise_lifting siff l.

(** The n-ary implication srelation, defined by lifting the 0-ary [impl] srelation. *)

Definition spredicate_implication {l : Tlist} :=
  pointwise_lifting s_impl l.

(** Notations for pointwise equivalence and implication of predicates. *)

Infix "s<∙>" := spredicate_equivalence (at level 95, no associativity) : predicate_scope.
Infix "s-∙>" := spredicate_implication (at level 70, right associativity) : predicate_scope.

Local Open Scope predicate_scope.

(** The pointwise liftings of conjunction and disjunctions.
   Note that these are [binary_operation]s, building new srelations out of old ones. *)

Definition spredicate_intersection := pointwise_extension sand.
Definition spredicate_union := pointwise_extension sor.

Infix "s/∙\" := spredicate_intersection (at level 80, right associativity) : predicate_scope.
Infix "s\∙/" := spredicate_union (at level 85, right associativity) : predicate_scope.

(** The always [True] and always [False] predicates. *)

Fixpoint true_spredicate {l : Tlist} : spredicate l :=
  match l with
    | Tnil => sUnit
    | A :: tl => fun _ => @true_spredicate tl
  end.

Fixpoint false_spredicate {l : Tlist} : spredicate l :=
  match l with
    | Tnil => sEmpty
    | A :: tl => fun _ => @false_spredicate tl
  end.

Notation "s∙⊤∙" := true_spredicate : predicate_scope.
Notation "s∙⊥∙" := false_spredicate : predicate_scope.

(** Predicate equivalence is an equivalence, and predicate implication defines a preorder. *)

Program Instance spredicate_equivalence_equivalence : 
  Equivalence (@spredicate_equivalence l).

  Next Obligation.
    induction l ; firstorder.
  Qed.
  Next Obligation.
    induction l ; firstorder.
  Qed.
  Next Obligation.
    fold pointwise_lifting.
    induction l. firstorder.
    intros. simpl in *. pose (IHl (x x0) (y x0) (z x0)).
    firstorder.
  Qed.

Program Instance spredicate_implication_preorder :
  PreOrder (@spredicate_implication l).
  Next Obligation.
    induction l ; firstorder.
  Qed.
  Next Obligation.
    induction l. firstorder.
    unfold predicate_implication in *. simpl in *.
    intro. pose (IHl (x x0) (y x0) (z x0)). firstorder.
  Qed.

(** We define the various operations which define the algebra on binary srelations,
   from the general ones. *)

Section Binary.
  Context {A : Type}.

  Definition srelation_equivalence : srelation (srelation A) :=
    @spredicate_equivalence (_::_::Tnil).

  Global Instance: RewriteSrelation srelation_equivalence. Proof. Defined.
  
  Definition srelation_conjunction (R : srelation A) (R' : srelation A) : srelation A :=
    @spredicate_intersection (A::A::Tnil) R R'.

  Definition srelation_disjunction (R : srelation A) (R' : srelation A) : srelation A :=
    @spredicate_union (A::A::Tnil) R R'.
  
  (** Srelation equivalence is an equivalence, and subsrelation defines a partial order. *)

  Global Instance srelation_equivalence_equivalence :
    Equivalence srelation_equivalence.
  Proof. exact (@spredicate_equivalence_equivalence (A::A::Tnil)). Qed.
  
  Global Instance srelation_implication_preorder : PreOrder (@subsrelation A).
  Proof. exact (@spredicate_implication_preorder (A::A::Tnil)). Qed.

  (** *** Partial Order.
   A partial order is a preorder which is additionally antisymmetric.
   We give an equivalent definition, up-to an equivalence srelation
   on the carrier. *)

  Class PartialOrder eqA `{equ : Equivalence A eqA} R `{preo : PreOrder A R} : SProp :=
    partial_order_equivalence : srelation_equivalence eqA (srelation_conjunction R (flip R)).
  
  (** The equivalence proof is sufficient for proving that [R] must be a
   morphism for equivalence (see Morphisms).  It is also sufficient to
   show that [R] is antisymmetric w.r.t. [eqA] *)

  Global Instance partial_order_antisym `(PartialOrder eqA R) : Antisymmetric A eqA R.
  Proof with auto.
    reduce_goal.
    pose proof partial_order_equivalence as poe. do 3 red in poe.
    apply poe. firstorder.
  Qed.


  Lemma PartialOrder_inverse `(PartialOrder eqA R) : PartialOrder eqA (flip R).
  Proof. firstorder. Qed.
End Binary.

Hint Extern 3 (PartialOrder (flip _)) => class_apply PartialOrder_inverse : typeclass_instances.

(** The partial order defined by subsrelation and srelation equivalence. *)

Program Instance subsrelation_partial_order :
  PartialOrder (@srelation_equivalence A) subsrelation.

Next Obligation.
Proof.
  unfold srelation_equivalence in *. compute; firstorder.
Qed.

Typeclasses Opaque spredicate_implication spredicate_equivalence
            srelation_equivalence pointwise_lifting.
