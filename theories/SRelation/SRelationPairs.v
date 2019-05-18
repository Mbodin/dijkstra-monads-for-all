(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Relations over pairs *)


(* Require Import SetoidList. *)
From Coq.Logic Require Import StrictProp.
From Mon.SRelation Require Import SRelations SMorphisms.
(* NB: This should be system-wide someday, but for that we need to
    fix the simpl tactic, since "simpl fst" would be refused for
    the moment.

Arguments fst {A B}.
Arguments snd {A B}.
Arguments pair {A B}.

/NB *)

Local Notation Fst := (@fst _ _).
Local Notation Snd := (@snd _ _).

Arguments relation_conjunction A%type (R R')%signature _ _.
Arguments relation_equivalence A%type (_ _)%signature.
Arguments subrelation A%type (R R')%signature.
Arguments Reflexive A%type R%signature.
Arguments Irreflexive A%type R%signature.
Arguments Symmetric A%type R%signature.
Arguments Transitive A%type R%signature.
Arguments PER A%type R%signature.
Arguments Equivalence A%type R%signature.
Arguments StrictOrder A%type R%signature.

Generalizable Variables A B RA RB Ri Ro f.

(** Any function from [A] to [B] allow to obtain a relation over [A]
    out of a relation over [B]. *)

Definition SRelCompFun {A} {B : Type}(R:srelation B)(f:A->B) : srelation A :=
 fun a a' => R (f a) (f a').

(** Instances on RelCompFun must match syntactically *)
Typeclasses Opaque SRelCompFun. 

Infix "s@@" := (@SRelCompFun _ _) (at level 30, right associativity) : signature_scope.

Notation "R s@@1" := (R s@@ Fst)%signature (at level 30) : signature_scope.
Notation "R s@@2" := (R s@@ Snd)%signature (at level 30) : signature_scope.

(** We declare measures to the system using the [Measure] class.
   Otherwise the instances would easily introduce loops,
   never instantiating the [f] function.  *)

Class Measure {A B} (f : A -> B).

(** Standard measures. *)

Instance fst_measure : @Measure (A * B) A Fst. Proof. Defined.
Instance snd_measure : @Measure (A * B) B Snd. Proof. Defined.

(** We define a product relation over [A*B]: each components should
    satisfy the corresponding initial relation. *)

Definition SRelProd {A : Type} {B : Type} (RA:srelation A)(RB:srelation B) : srelation (A*B) :=
 srelation_conjunction (@SRelCompFun (A * B) A RA fst) (SRelCompFun RB Snd).

Typeclasses Opaque SRelProd.

Infix "*" := SRelProd : signature_scope.

Section SRelCompFun_Instances.
  Context {A : Type} {B : Type} (R : srelation B).

  Global Instance SRelCompFun_Reflexive
    `(Measure A B f, Reflexive _ R) : Reflexive (R s@@f).
  Proof. firstorder. Qed.

  Global Instance SRelCompFun_Symmetric
    `(Measure A B f, Symmetric _ R) : Symmetric (R s@@f).
  Proof. firstorder. Qed.

  Global Instance SRelCompFun_Transitive
    `(Measure A B f, Transitive _ R) : Transitive (R s@@f).
  Proof. firstorder. Qed.

  Global Instance SRelCompFun_Irreflexive
    `(Measure A B f, Irreflexive _ R) : Irreflexive (R s@@f).
  Proof. firstorder. Qed.

  Global Program Instance SRelCompFun_Equivalence
    `(Measure A B f, Equivalence _ R) : Equivalence (R s@@f).

  Global Program Instance SRelCompFun_StrictOrder
    `(Measure A B f, StrictOrder _ R) : StrictOrder (R s@@f).

End SRelCompFun_Instances.

Section SRelProd_Instances.

  Context {A : Type} {B : Type} (RA : srelation A) (RB : srelation B).

  Global Instance SRelProd_Reflexive `(Reflexive _ RA, Reflexive _ RB) : Reflexive (RA*RB).
  Proof. firstorder. Qed.

  Global Instance SRelProd_Symmetric `(Symmetric _ RA, Symmetric _ RB)
  : Symmetric (RA*RB).
  Proof. firstorder. Qed.

  Global Instance SRelProd_Transitive 
           `(Transitive _ RA, Transitive _ RB) : Transitive (RA*RB).
  Proof. firstorder. Qed.

  Global Program Instance SRelProd_Equivalence 
          `(Equivalence _ RA, Equivalence _ RB) : Equivalence (RA*RB).

  Lemma FstRel_ProdRel :
    srelation_equivalence (SRelCompFun RA fst) (RA*(fun _ _ : B => sUnit))%signature.
  Proof. firstorder. Qed.
  
  Lemma SndRel_ProdRel :
    srelation_equivalence (SRelCompFun RB snd) ((fun _ _ : A => sUnit) * RB)%signature.
  Proof. firstorder. Qed.
  
  Global Instance FstRel_sub :
    subsrelation (RA*RB)%signature (SRelCompFun RA fst).
  Proof. firstorder. Qed.

  Global Instance SndRel_sub :
    subsrelation (RA*RB)%signature (SRelCompFun RB snd).
  Proof. firstorder. Qed.
  
  Global Instance pair_compat :
    SProper (RA s==>RB s==> RA*RB)%signature (@pair _ _).
  Proof. firstorder. Qed.
  
  Global Instance fst_compat :
    SProper (RA*RB s==> RA)%signature Fst.
  Proof.
    intros (x,y) (x',y') (Hx,Hy); compute in *; auto.
  Qed.

  Global Instance snd_compat :
    SProper (RA*RB s==> RB) Snd.
  Proof.
    intros (x,y) (x',y') (Hx,Hy); compute in *; auto.
  Qed.

  Global Instance SRelCompFun_compat (f:A->B)
           `(SProper _ (Ri s==>Ri s==>Ro) RB) :
    SProper (Ri s@@f s==> Ri s@@f s==>Ro) (RB s@@f)%signature.
  Proof. unfold SRelCompFun; firstorder. Qed.
End SRelProd_Instances.

Hint Unfold SRelProd SRelCompFun.
Hint Extern 2 (SRelProd _ _ _ _) => split.

