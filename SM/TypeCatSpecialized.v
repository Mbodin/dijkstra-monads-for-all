From Categories Require Essentials.Notations.
From Categories Require Export Essentials.Types.
From Categories Require Export Essentials.Facts_Tactics.
From Categories Require Category.Main.
From Categories Require Functor.Main.
From Categories Require NatTrans.Main.
From Categories Require Export Monad.Main.
From Categories.Basic_Cons Require Export Product.
From Categories.Coq_Cats.Type_Cat Require Export Type_Cat CCC.

From SM Require Import Base.

(* In order to deal with the incompatibility of
   the notation for ∘ with Program.Basics, the modules
   exporting ∘ are not re-exported directly *)
Module CategoryBasics.
  Export Essentials.Notations.
  Export Category.Main.
  Export Functor.Main.
  Export NatTrans.Main.
End CategoryBasics.


Set Implicit Arguments.

Ltac apply_to_eq k t :=
  let ty0 := type of t in 
  let ty := eval cbn in ty0 in 
  match ty with
  | ?x = ?y => k t
  | forall (x : ?A), ?B =>
    exact(fun x => ltac:(apply_to_eq k (t x))) 
  end.

Ltac pointwise t :=
  let t' :=
      eval cbn in ltac:(let k t :=
                            let t1 := eval cbn in (equal_f t) in
                            exact t1 in apply_to_eq k t)
  in exact t'.

Existing Instance Type_Cat.

Section Functor.
  Import Essentials.Notations.
  Import Functor.Main.
  Context (F : (Type_Cat –≻ Type_Cat)%functor).

  Definition F_id := ltac:(pointwise (F_id F)).
  Definition F_compose := ltac:(pointwise (@F_compose _ _ F)).
End Functor.

Section Naturality.
  Import Essentials.Notations.
  Import Functor.Main.
  Import NatTrans.Main.
  Context {F1 F2 : (Type_Cat –≻ Type_Cat)%functor}.
  Context (ν:NatTrans F1 F2).
  Context {A B} (f : A -> B).

  Definition natural := ltac:(pointwise (Trans_com ν f)).
End Naturality.

Notation KleisliMonad := (@KleisliMonad Type_Cat).
Notation bind := (@bind Type_Cat _ _ _ _).
Notation ret := (@ret Type_Cat _ _ _).

Let unitl0 := ltac:(pointwise (Kleisli_Monad_Left_Unit (C:=Type_Cat))).
Notation unitl := (unitl0 _ _).
Check unitl.

Let unitr0 := ltac:(pointwise (Kleisli_Monad_Right_Unit (C:=Type_Cat))).
Notation unitr := (unitr0 _ _).
Check unitr.

Let assoc0 := ltac:(pointwise (Kleisli_Monad_Associativity (C:=Type_Cat))).
Notation assoc := (assoc0 _ _).
Check assoc.


Notation trans := (@NatTrans.NatTrans.Trans Type_Cat Type_Cat _ _).
Notation trans_monad θ :=  (NatTrans.NatTrans.Trans (monad_morph _ _ θ)).

Ltac trans_pointwise t :=
  let t' :=
      eval cbn in
  ltac:(let k t := exact (fun c => equal_f (f_equal (fun h => NatTrans.NatTrans.Trans h c) t)) in
        apply_to_eq k t)
  in exact t'.

Let mmorph_unit0 := ltac:(trans_pointwise Monad_Unit_com).
Notation mmorph_unit := (mmorph_unit0).
Check mmorph_unit.

Let mmorph_bind0 := ltac:(pointwise MonadMorphismBind).
Notation mmorph_bind := (mmorph_bind0).
Check mmorph_bind.

Section MMorphBind'.
  Import CategoryBasics.
  Existing Instance KleisliMonadFromMonad.
  Let mmorph_bind'_t := forall (T1 T2 : (Type_Cat –≻ Type_Cat)%functor) `{@Monad _ T1} `{@Monad _ T2} (θ : MonadMorphism T1 T2) (A B:Type)  (m:FO T1 A)(f : A -> FO T1 B), trans_monad θ B (bind f m) = bind (fun x => trans_monad θ B (f x)) (trans_monad θ A m) .
  Let mmorph_bind'0 := ltac:(pointwise MonadMorphismBind').
  Definition mmorph_bind' : mmorph_bind'_t.
  Proof. red ; intros ** ; cbv ; rewrite (mmorph_bind'0 θ) ; reflexivity. Qed.
End MMorphBind'.

Check mmorph_bind'.

Section MonadMorphism.
  Context {F1 F2}
          `{Monad (C:=Type_Cat) F1}
          `{Monad (C:=Type_Cat) F2}
          `(θ : MonadMorphism (C:=Type_Cat) F1 F2).

  Definition mmorph_map {c c'} := ltac:(pointwise (@NatTrans.NatTrans.Trans_com _ _ _ _ (monad_morph _ _ θ))) c c'.

  Check (mmorph_map).

End MonadMorphism.

Section Algebra.
  Context (M: Type -> Type) `{KleisliMonad M}.
  Definition Algebra := Algebra (TF M).
End Algebra.
Arguments Algebra _ {_}.
Notation AlgStruct := (AlgebraStructure (C:=Type_Cat)).
Notation alg_struct := (alg_structure (C:=Type_Cat) _ _).

Let alg_unit0 := ltac:(pointwise (alg_unit (C:=Type_Cat))).
Notation alg_unit := (alg_unit0).

Let alg_mult0 := ltac:(pointwise (alg_mult (C:=Type_Cat))).
Notation alg_mult := (alg_mult0).

Let alg_ret0 := ltac:(pointwise (alg_ret (C:=Type_Cat))).
Notation alg_ret := (alg_ret0).

Let alg_bind0 := ltac:(pointwise (alg_bind (C:=Type_Cat))).
Notation alg_bind := alg_bind0.

Section Map.
  Import Essentials.Notations.
  Import Functor.Main.
  Definition map {T} `{KleisliMonad T} {A B} (f : A -> B) (x:T A) :=
  (TF T _a f x)%morphism.
End Map.


Module MonadNotations.
  (* This prevent giving explicitly the type, to do so use Monad.ret/bind *)
  Notation "m ≫= f" := (bind f m) (at level 60, right associativity) .
  Notation "( m ≫=)" := (fun f => bind f m) (only parsing) .
  Notation "(≫= f )" := (bind f) (only parsing) .
  Notation "(≫=)" := (fun m f => bind f m) (only parsing) .

  Notation "x ← y ; z" := (y ≫= (fun x : _ => z))
    (at level 20, y at level 100, z at level 200, only parsing) .

  Notation "f <$> x" := (map f x) (at level 60).
End MonadNotations.

