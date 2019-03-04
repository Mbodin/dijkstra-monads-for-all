From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Basic_Cons.CCC.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.

Program Instance unit_Type_term : (𝟙_ Type_Cat)%object :=
{
  terminal := unit;
  t_morph := fun _ _=> tt
}.

Next Obligation. (* t_morph_unique *)
Proof.
  extensionality x.
  destruct (f x); destruct (g x); reflexivity.
Qed.


Local Notation "A × B" := (@Product Type_Cat A B) : object_scope.

(** The cartesian product of types is the categorical notion of products in
    category of types. *)
(* Program Definition prod_Product (A B : Type) : (A × B)%object := *)
(* {| *)
(*   product := (A * B)%type; *)
(*   Pi_1 := fst; *)
(*   Pi_2 := snd; *)
(*   Prod_morph_ex := fun p x y z => (x z, y z) *)
(* |}. *)

(* Next Obligation. (* Prod_morph_unique *) *)
(* Proof. *)
(*   extensionality x. *)
(*   repeat *)
(*     match goal with *)
(*       [H : _ = _ |- _] => *)
(*       apply (fun p => equal_f p x) in H *)
(*     end. *)
(*   basic_simpl.   *)
(*   destruct (f x); destruct (g x); cbn in *; subst; trivial. *)
(* Qed. *)

Record npair (A B : Type) := { nfst : A ; nsnd : B }.
Arguments nfst {_ _} _.
Arguments nsnd {_ _} _.
Notation "⟨ u , v ⟩" := (Build_npair _ _ u v).

Program Definition prod_Product (A B : Type) : (A × B)%object :=
{|
  product := npair A B;
  Pi_1 := nfst;
  Pi_2 := nsnd;
  Prod_morph_ex := fun p x y z => ⟨x z, y z⟩
|}.

Next Obligation. (* Prod_morph_unique *)
Proof.
  extensionality x.
  repeat
    match goal with
      [H : _ = _ |- _] =>
      apply (fun p => equal_f p x) in H
    end.
  basic_simpl.  
  destruct (f x); destruct (g x); cbn in *; subst; trivial.
Qed.



Program Instance Type_Cat_Has_Products : Has_Products Type_Cat := prod_Product.

(** The function type in coq is the categorical exponential in the category of
    types. *)
Program Definition fun_exp (A B : Type_Cat) : (A ⇑ B)%object :=
{|
  exponential := A -> B;
  eval := fun x => (nfst x) (nsnd x);
  Exp_morph_ex := fun h z u v=>  z ⟨u, v⟩
|}.

Next Obligation. (* Exp_morph_unique *)
Proof.
  extensionality a; extensionality x.
  repeat
    match goal with
      [H : _ = _ |- _] =>
      apply (fun p => equal_f p ⟨a, x⟩) in H
    end.
  transitivity (f ⟨a, x⟩); auto.
Qed.

(* fun_exp defined *)

Program Instance Type_Cat_Has_Exponentials : Has_Exponentials Type_Cat := fun_exp.

(* Category of Types is cartesian closed *)

Program Instance Type_Cat_CCC : CCC Type_Cat.
