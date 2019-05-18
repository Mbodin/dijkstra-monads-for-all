From Coq Require Import List  ssreflect ssrfun. 
From Mon Require Import Base.
From Mon.sprop Require Import SPropBase SPropMonadicStructures.
From Mon.SM Require Import SMSyntax SMDenotations.
From Equations Require Import Equations.


(** From a monad in SM (icmonad) we define :   *)
(** - a mapping (CMonad) from monads to monads *)
(** - a lift from the source monad to CMonad   *)
(** - under the hypothesis that the resulting
      bind is a homomorphism (HBindHomo), the
      lift is a monad morphism                 *)
(** - under the hypothesis that the SM monad is
      covariant, there is a functorial action
      on monad morphism CMonadMorph, and the
      lift defines a natural transformation
      from the identity to CMonad              *)



Set Universe Polymorphism.
Set Primitive Projections.

Record MonadUnder (M:Monad) :=
  mkMonadUnder {
    mu_carrier :> Monad ;
    mu_lift : MonadMorphism M mu_carrier
  }.


Section ToMonad.
  Context (M : Monad) (C : icmonad).
  Let CM := icM C.

  Definition carrier (X:Type) : Type := ⦑CM X|M⦒.
  Definition ret' A :=
    icterm_to_term M (icRet C A) Substitution.dNil.
  Definition bind' A B m f :=
      icterm_to_term M (icBind C A B) Substitution.dNil m f.

  Definition MonadFromEqns pf1 pf2 pf3 : Monad :=
    @mkMonad carrier ret' bind' pf1 pf2 pf3.

  Import Substitution.

  Program Definition CMonad : Monad := MonadFromEqns _ _ _.
  Next Obligation.
    pose (fun f => iceq_to_eq M (icRetBind C A B a) (dCons f dNil)).
    specialize (e (dpair _ ⟨f, f⟩ eq_refl)).

    simpl in e.
    rewrite (dlookup_equation_2 _ _ _ _ _ _) in e.
    rewrite !to_term_weaken in e.
    exact e.
  Qed.

  Next Obligation.
    pose (fun c => iceq_to_eq M (icBindRet C A) (dCons c dNil)).
    specialize (e (dpair _ ⟨c, c⟩ eq_refl)).
    simpl in e.
    rewrite !to_term_weaken in e.
    rewrite (dlookup_equation_2 _ _ _ _ _ _) in e.
    exact e.
  Qed.

  Next Obligation.
    pose (fun c f g => iceq_to_eq M (icAssoc C A B C0) (dCons c (dCons f (dCons g dNil)))).
    specialize (e (dpair _ ⟨c, c⟩ eq_refl)).
    specialize (e (dpair _ ⟨f, f⟩ eq_refl)).
    specialize (e (dpair _ ⟨g, g⟩ eq_refl)).
    simpl in e.
    rewrite !to_term_weaken in e.
    rewrite (dlookup_equation_2 _ _ _ _ _ _) in e.
    exact e.
  Qed.

  Definition homomorphism c1 c2 (f : ⦑c1|M⦒ -> ⦑c2|M⦒) :=
      let α1 := ctype_alg M c1 in
      let α2 := ctype_alg M c2 in
      forall m, f (α1 m) = α2 (f <$> m).

  (* Should be obtained as a consequence of the syntactic linearity condition on bind *)
  Context (HBindHomo : forall A B, homomorphism _ ((_ ~> _) ~~> _)
                       ⦑ icBind C A B | dNil | M ⦒).

  Definition lift_carrier {pf1 pf2 pf3} A (m : M A) : MonadFromEqns pf1 pf2 pf3 A :=
    ctype_alg M (icM C A) (bind m (fun a => ret (ret' A a))).


  Definition MonadUnderFromEqns {pf1 pf2 pf3 pf4 pf5} :=
    mkMonadUnder M (MonadFromEqns pf1 pf2 pf3)
                 (@mkMorphism M _ lift_carrier pf4 pf5).


  Import FunctionalExtensionality.

  Program Definition lift_monad_morph : MonadMorphism M CMonad :=
  @mkMorphism M CMonad lift_carrier _ _.
  Next Obligation.
    unfold lift_carrier.
    unfold bind.
    unfold ret.
    rewrite monad_law1.
    rewrite algstr_ret.
    reflexivity.
  Qed.
  Next Obligation.
    unfold lift_carrier.
    unfold bind'.
    rewrite HBindHomo.
    intro_map.
    rewrite map_functorial.
    replace (fun x : A => ⦑ icBind C A B | dNil | M ⦒ (ret' A x)) with
        (fun (x:A) (f : A -> carrier B) => f x).
    2:{ extensionality a. extensionality f0.
        pose (@monad_law1 CMonad). simpl in e. unfold bind' in e. rewrite e. reflexivity. }
    rewrite map_bind.
    simpl.
    rewrite bind_map.
    rewrite algstr_bind.
    reflexivity.
  Qed.


End ToMonad.

Section ToMonadMorphism.
  Context (C:icmonad) (Hcov : forall A, covariant (icM C A))
          (M1 M2 : Monad) (θ : MonadMorphism M1 M2).

  Definition mmorph_carrier A := to_function _ _ θ (icM C A) (Hcov A).

  Import Substitution.
  Definition val_cov M (c:ctype) := ⦑ c | M ⦒ × covariant c.

  Program Definition CMonadMorph : MonadMorphism (CMonad M1 C) (CMonad M2 C) :=
    @mkMorphism _ _ mmorph_carrier _ _.
  Next Obligation.
    simple refine (icterm_to_fun_witness _ _ θ
                                         (mon_morph_ret θ)
                                         (mon_morph_bind θ)
                                         (icRet C A @ a) _ dNil).
  Qed.
  Next Obligation.
    unshelve epose (σ := @dCons (val_cov M1) (A ~> icM C B) _ ⟨f, fun _ => Hcov B⟩
                       (@dCons (val_cov M1) (icM C A) _ ⟨m, Hcov A⟩ dNil)).
    pose (Hbind := (↑↑ icBind C A B ) @c ↑vz @c vz).
    move: (icterm_to_fun_witness _ _
                                θ (mon_morph_ret θ)
                                (mon_morph_bind θ)
                                Hbind
                                (Hcov B) σ) => /=.
    rewrite !(to_term_weaken _).
    do 4 (simpl ; simp_dlookup) => //.
  Qed.


End ToMonadMorphism.


Section ToMonadMorphismIdentity.
  Context (C:icmonad) (Hcov : forall A, covariant (icM C A)) (M1 : Monad). 

  Lemma mmorph_preserves_id :
    forall A m, CMonadMorph C Hcov M1 M1 (identity_monad_morphism M1) A m = m.
  Proof.
    intros. unfold CMonadMorph. simpl. unfold mmorph_carrier.
    apply to_function_id.
  Qed.

  Context (M2 M3 : Monad) (f12 : MonadMorphism M1 M2) (f23 : MonadMorphism M2 M3).

  Lemma mmorph_preserves_comp :
    forall A m, CMonadMorph C Hcov M2 M3 f23 A (CMonadMorph C Hcov M1 M2 f12 A m) =
           CMonadMorph C Hcov M1 M3 (comp_monad_morphism f12 f23) A m.
  Proof.
    intros. unfold CMonadMorph. simpl. unfold mmorph_carrier.
    apply to_function_comp.
  Qed.

End ToMonadMorphismIdentity.


Section LiftNatural.
  Context (C:icmonad) (Hcov:forall A, covariant (icM C A))
          (M1 M2:Monad) (θ : MonadMorphism M1 M2).

  Import FunctionalExtensionality.
  Lemma monad_morphism_natural : forall A B f m, f <$> (θ A m) = θ B (f <$> m).
  Proof.
    intros. cbv. rewrite mon_morph_bind. cbv ; f_equal.
    extensionality a. rewrite mon_morph_ret ; reflexivity.
  Qed.

  Lemma mon_morph_alg (c:ctype) c_cov :
    let θ' := to_function M1 M2 θ c c_cov in
    forall m, θ' (ctype_alg M1 c m) = ctype_alg M2 c (θ' <$> θ _ m).
  Proof.
    induction c ; simpl.
    - intros ; rewrite mon_morph_bind. cbv.
      rewrite monad_law3. f_equal. extensionality a.
      rewrite monad_law1. reflexivity.
    - intros m ; destruct c_cov ; f_equal;
      rewrite map_functorial ; simpl;
      rewrite monad_morphism_natural;
      [rewrite <- (map_functorial nfst); rewrite (IHc1 c (nfst <$> _))
      |rewrite <- (map_functorial nsnd); rewrite (IHc2 _ (nsnd <$> _))];
      rewrite monad_morphism_natural;
      reflexivity.
    -  intros m ; extensionality x.
       rewrite (H x).
       f_equal.
       (* rewrite monad_morphism_natural. *)
       rewrite bind_map.
       rewrite mon_morph_bind.
       rewrite map_bind.
       f_equal.
       extensionality f.
       rewrite monad_morphism_natural /map /bind
               /ret monad_law1 mon_morph_ret //.
     - inversion c_cov.
   Qed.

  Lemma lift_natural :
    forall A m, lift_carrier M2 C A (θ A m) = CMonadMorph C Hcov M1 M2 θ A (lift_carrier M1 C A m). 
  Proof.
    unfold lift_carrier.
    intro_map.
    intros. rewrite monad_morphism_natural.
    replace (ret' M2 C A) with (fun a => CMonadMorph C Hcov M1 M2 θ A (ret' M1 C A a)).
    2:{ extensionality a.
        pose (mon_morph_ret (CMonadMorph C Hcov M1 M2 θ)).
        simpl in e |- *.
        apply e. }
    unfold CMonadMorph. simpl. unfold mmorph_carrier.
    rewrite mon_morph_alg. f_equal.
    rewrite monad_morphism_natural.
    rewrite map_functorial.
    reflexivity.
  Qed.
End LiftNatural.