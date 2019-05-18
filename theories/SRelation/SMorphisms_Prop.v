(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * [Proper] instances for propositional connectives.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

From Coq Require Import Program.Basics.
From Coq Require Import Program.Tactics.
From Mon Require Import SRelation.SMorphisms.

Local Obligation Tactic := try solve [simpl_relation | firstorder auto].

(** Standard instances for [not], [iff] and [impl]. *)

(** Logical negation. *)

Program Instance snot_s_impl_morphism :
  SProper (s_impl s--> s_impl) snot | 1.

Program Instance snot_siff_morphism :
  SProper (siff s++> siff) snot.

(** Logical conjunction. *)

Program Instance ssand_s_s_impl_morphism :
  SProper (s_impl s==> s_impl s==> s_impl) sand | 1.

Program Instance ssand_ssiff_morphism :
  SProper (siff s==> siff s==> siff) sand.

(** Logical disjunction. *)

Program Instance sor_s_impl_morphism :
  SProper (s_impl s==> s_impl s==> s_impl) sor | 1.

Program Instance sor_siff_morphism :
  SProper (siff s==> siff s==> siff) sor.

(** Logical s_implication [s_impl] is a morphism for logical equivalence. *)

Program Instance siff_siff_siff_s_impl_morphism : SProper (siff s==> siff s==> siff) s_impl.

(** Morphisms for quantifiers *)

Program Instance ex_siff_morphism {A : Type} : SProper (pointwise_srelation A siff s==> siff) (@Ex A).

Program Instance ex_s_impl_morphism {A : Type} :
  SProper (pointwise_srelation A s_impl s==> s_impl) (@Ex A) | 1.

Program Instance ex_flip_s_impl_morphism {A : Type} :
  SProper (pointwise_srelation A (flip s_impl) s==> flip s_impl) (@Ex A) | 1.

Program Instance all_siff_morphism {A : Type} :
  SProper (pointwise_srelation A siff s==> siff) (@All A).

Program Instance all_s_impl_morphism {A : Type} :
  SProper (pointwise_srelation A s_impl s==> s_impl) (@All A) | 1.

Program Instance all_flip_s_impl_morphism {A : Type} :
  SProper (pointwise_srelation A (flip s_impl) s==> flip s_impl) (@All A) | 1.

(* Acc Lemmas removed since Acc is not in SProp *)
