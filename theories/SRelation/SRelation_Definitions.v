(** Stolen from Coq StdLib and adapted to SProp *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Mon Require Import sprop.SPropBase.

Set Primitive Projections.

Section Srelation_Definition.
  Import SPropNotations.

  Variable A : Type.

  Definition srelation := A -> A -> SProp.

  Variable R : srelation.


  Section General_Properties_of_Srelations.

    Definition reflexive : SProp := forall x:A, R x x.
    Definition transitive : SProp := forall x y z:A, R x y -> R y z -> R x z.
    Definition symmetric : SProp := forall x y:A, R x y -> R y x.
    Definition antisymmetric : SProp := forall x y:A, R x y -> R y x -> x ≡ y.

  End General_Properties_of_Srelations.


  Section Sets_of_Srelations.

    Record preorder : SProp :=
      { preord_refl : reflexive; preord_trans : transitive}.

    Record order : SProp :=
      { ord_refl : reflexive;
	      ord_trans : transitive;
	      ord_antisym : antisymmetric}.

    Record equivalence : SProp :=
      { equiv_refl : reflexive;
	      equiv_trans : transitive;
	      equiv_sym : symmetric}.

    Record PER : SProp :=  {per_sym : symmetric; per_trans : transitive}.

  End Sets_of_Srelations.


  Section Srelations_of_Srelations.

    Definition inclusion (R1 R2:srelation) : SProp :=
      forall x y:A, R1 x y -> R2 x y.

    Definition same_srelation (R1 R2:srelation) : SProp :=
      inclusion R1 R2 s/\ inclusion R2 R1.

    Definition commut (R1 R2:srelation) : SProp :=
      forall x y:A, R1 y x -> forall z:A, R2 z y ->  s∃ y', R2 y' x s/\ R1 z y'.

  End Srelations_of_Srelations.


End Srelation_Definition.

Hint Unfold reflexive transitive antisymmetric symmetric: sets.

Hint Resolve Build_preorder Build_order Build_equivalence Build_PER
  preord_refl preord_trans ord_refl ord_trans ord_antisym equiv_refl
  equiv_trans equiv_sym per_sym per_trans: sets.

Hint Unfold inclusion same_srelation commut: sets.
