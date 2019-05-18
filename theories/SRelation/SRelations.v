(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Mon Require Export sprop.SPropBase.
From Mon Require Export SRelation.SRelation_Definitions.
From Mon Require Export SRelation.SRelation_Operators.
From Mon Require Export SRelation.SRelation_Operators_Properties.

Lemma inverse_image_of_equivalence :
  forall (A B:Type) (f:A -> B) (r:srelation B),
    equivalence B r -> equivalence A (fun x y:A => r (f x) (f y)).
Proof.
  intros; split; elim H; red; auto.
  intros _ equiv_trans _ x y z H0 H1; apply equiv_trans with (f y); assumption.
Qed.

Lemma inverse_image_of_Eq :
  forall (A B:Type) (f:A -> B), equivalence A (fun x y:A => sEq (f x) (f y)).
Proof.
  split; red;
    [  (* reflexivity *) reflexivity
      |  (* transitivity *) intros; transitivity (f y); assumption
      |  (* symmetry *) intros; symmetry ; assumption ].
Qed.

