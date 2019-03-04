From Coq Require Import List.
From SM Require Import TypeCatSpecialized Base.
From SM Require Import SMSyntax.
From SM Require Import SMDenotations.
From SM Require Import SMExamplesGenerated.

Import CategoryBasics.

Definition st_icmonad S := Eval cbv in
      {|
        icM := icM (st_icmonad S) ;
        icRet A := icterm_eval 10 (icRet (st_icmonad S) A) ;
        icBind A B := icterm_eval 10 (icBind (st_icmonad S) A B)
      |}.


Definition MonadCat := @TripleCat Type_Cat.

Record MonadTransformer :=
  {
    transformer : (MonadCat –≻ MonadCat)%functor ;
    lift : (Functor_id MonadCat –≻ transformer)%nattrans
  }.


Ltac solve_cov := cbv ; trivial.

Definition val_cov M (c:ctype) := ⦑ c | M ⦒ × covariant c.

Section ICBindCtx.
  Context (c:icmonad).
  Import ListNotations.
  Context (A B : Type).
  Let Γ := [A ~> icM c B ; icM c A].
  Definition icBindCtx : icterm Γ  (icM c B) :=
    ICApp isArrCPf
          (ICApp isArrCPf (weaken _ _ (weaken _ _ (icBind c A B)))
                 (@ICVar Γ 1 (inhabit_infer 1 Γ)))
          (@ICVar Γ 0 (inhabit_infer 0 Γ)).

End ICBindCtx.


Transparent weaken0.
Transparent Substitution.dlookup.
Transparent Substitution.dmap.

Definition StT (S:Type) : (MonadCat –≻ MonadCat)%functor.
Proof.
  pose (St := icM (st_icmonad S)).
  unshelve econstructor.
  - intros [M KlM].
    exists (fun X => ⦑St X|M⦒).
    exists (fun A => icterm_to_term M (icRet (st_icmonad S) A) Substitution.dNil)
      (fun A B f m => icterm_to_term M (icBind (st_icmonad S) A B) Substitution.dNil m f).
    all: abstract(
      intros ; cbn; extensionality x0 ; extensionality x1 ;
      (rewrite unitl + rewrite unitr + rewrite TypeCatSpecialized.assoc) ;
      reflexivity).

  - intros [T1 KlT1] [T2 KlT2] [θ θ_unit θ_bind] ; simpl in *.
    exists (fun X => to_function _ _ θ (St X) ltac:(solve_cov)).

   abstract exact (fun A => icterm_to_fun_witness _ _
                                     θ (fun A => equal_f (θ_unit A))
                                     (fun A B m f => equal_f (θ_bind A B f) m) 
                                        (icRet (st_icmonad S) A)
                                        ltac:(cbv ; trivial) Substitution.dNil).
   abstract (intros A B f ; extensionality m;
      pose (σ :=
              @Substitution.dCons (val_cov T1) (A ~> St B) _
                                  ltac:(split ; [exact f| cbv ; trivial])
              (@Substitution.dCons (val_cov T1) (St A) _
                                  ltac:(idtac ; split ; [exact m | cbv ; trivial])
                      Substitution.dNil));
      exact (icterm_to_fun_witness _ _
                                   θ (fun A => equal_f (θ_unit A))
                                   (fun A B m f => equal_f (θ_bind A B f) m) 
                                   (icBindCtx (st_icmonad S) A B)
                                   ltac:(cbv ; trivial) σ)).
    - abstract (intros [M KlM] ; apply TripleMorphism_eq_simplify ; simpl ;
      extensionality A ; extensionality m ; extensionality s ;
      reflexivity).
    - abstract (intros [M1 KlM1] [M2 KlM2] [M3 KlM3] [] [] ; apply TripleMorphism_eq_simplify ; simpl;
      extensionality A ; extensionality m ; extensionality s;
      reflexivity).
Defined.

Definition IdObj : MonadCat := existT _ Id IdentityTriple.

(* Unfinished : the category library should be extended to provide
   a simpler way to define a natural transformation between 2 triples *)
Definition lift_St_statement S : Type := (Functor_id MonadCat –≻ StT S)%nattrans.
