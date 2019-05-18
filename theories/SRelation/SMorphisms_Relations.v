(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Morphism instances for relations.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

From Coq Require Import Program.Program.
From Mon Require Import SRelation.SRelation_Definitions.
From Mon Require Import SRelation.SMorphisms.

Generalizable Variables A l.

(** Morphisms for relations *)

Instance srelation_conjunction_morphism : SProper (srelation_equivalence (A:=A) s==>
  srelation_equivalence s==> srelation_equivalence) srelation_conjunction.
  Proof. firstorder. Qed.

Instance srelation_disjunction_morphism : SProper (srelation_equivalence (A:=A) s==>
  srelation_equivalence s==> srelation_equivalence) srelation_disjunction.
  Proof. firstorder. Qed.

(* Predicate equivalence is exactly the same as the pointwise lifting of [iff]. *)

Lemma spredicate_equivalence_pointwise (l : Tlist) :
  SProper (@spredicate_equivalence l s==> pointwise_lifting siff l) id.
Proof. do 2 red. unfold spredicate_equivalence. auto. Qed.

Lemma spredicate_implication_pointwise (l : Tlist) :
  SProper (@spredicate_implication l s==> pointwise_lifting s_impl l) id.
Proof. do 2 red. unfold spredicate_implication. auto. Qed.

(** The instantiation at relation allows rewriting applications of relations
    [R x y] to [R' x y]  when [R] and [R'] are in [relation_equivalence]. *)

Instance srelation_equivalence_pointwise :
  SProper (srelation_equivalence s==> pointwise_srelation A (pointwise_srelation A siff)) id.
Proof. intro. apply (spredicate_equivalence_pointwise (Tcons A (Tcons A Tnil))). Qed.

Instance subsrelation_pointwise :
  SProper (subsrelation s==> pointwise_srelation A (pointwise_srelation A s_impl)) id.
Proof. intro. apply (spredicate_implication_pointwise (Tcons A (Tcons A Tnil))). Qed.


Lemma flip_pointwise_srelation A (R : srelation A) :
  srelation_equivalence (pointwise_srelation A (flip R)) (flip (pointwise_srelation A R)).
Proof. intros. split; firstorder. Qed.
