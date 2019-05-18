From Coq Require Import List  ssreflect ssrfun. 
From Mon Require Import Base.
From Mon.sprop Require Import SPropBase SPropMonadicStructures.
From Mon.SRelation Require Import SRelationClasses SMorphisms.
From Mon.SM Require Import SMSyntax SMDenotationsMonotonic.
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



Section ToOrderedMonad.
  Context (M : OrderedMonad) (C : icmonad).
  Let CM := icM C.

  Definition carrier (X:Type) : Type := ⦑CM X|M⦒.
  Definition ret' A :=
    icterm_to_term M (icRet C A) Substitution.dNil.
  Definition bind' A B m f :=
      Spr1 (Spr1 (icterm_to_term M (icBind C A B) Substitution.dNil) m) f.

  Definition MonadFromEqns pf1 pf2 pf3 : Monad :=
    @mkMonad carrier ret' bind' pf1 pf2 pf3.

  Program Definition OrderedMonadFromEqns pf1 pf2 pf3 : OrderedMonad :=
    @mkOrderedMonad (MonadFromEqns pf1 pf2 pf3) (fun X => to_ord M (CM X)) _ _.
  Next Obligation.
    rewrite /bind'.
    estransitivity.
    move: (Spr2 (icterm_to_term M (icBind C A B) Substitution.dNil) x y H x0) => /= w1 ; exact w1.
    apply (Spr2 (Spr1 (icterm_to_term M (icBind C A B) Substitution.dNil) y) x0 y0 H0).
  Qed.

  Import Substitution.

  Program Definition CMonad : OrderedMonad := OrderedMonadFromEqns _ _ _.
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
      let α1 := wit (ctype_alg M c1) in
      let α2 := wit (ctype_alg M c2) in
      forall m, f (α1 m) = α2 (f <$> m).

  (* Should be obtained as a consequence of the syntactic linearity condition on bind *)
  Context (HBindHomo : forall A B, homomorphism _ ((_ ~> _) ~~> _)
                        (Spr1 (icterm_to_term M (icBind C A B) dNil))).

  Definition lift_carrier {pf1 pf2 pf3} A (m : M A) :
    OrderedMonadFromEqns pf1 pf2 pf3 A :=
    wit (ctype_alg M (icM C A)) (bind m (fun a => ret (ret' A a))).

  Lemma lift_carrier_monotonic {pf1 pf2 pf3} A
        (lift:=@lift_carrier pf1 pf2 pf3 A) :
    SProper (@omon_rel M A s==> @omon_rel (OrderedMonadFromEqns pf1 pf2 pf3) A)
            (lift_carrier A).
  Proof.
    move=> ? ? ?.
    simpl.
    unfold lift_carrier.
    rewrite <- (pf (ctype_alg M (icM C A))).
    apply oalgstr_mon.
    red. move=> R Hret Hmon Hbind.
    apply Hmon.
    apply omon_bind.
    assumption.
    sreflexivity.
  Qed.

  Program Definition OrderedMonadUnderFromEqns {pf1 pf2 pf3 pf4 pf5} :=
    @mkMonadUnder M (OrderedMonadFromEqns pf1 pf2 pf3)
                  (@mkMonMorphism _ _
                                  (@mkMorphism M _ lift_carrier pf4 pf5)
                                  lift_carrier_monotonic).

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
    unfold lift_carrier ; rewrite /bind' HBindHomo /=.
    intro_map.
    rewrite !map_functorial.
    match goal with
    | [|- _ = _ ((fun x => ?f ?arg) <$> _)] =>
      replace (fun x => f arg) with (fun x => arg x)
    end.
    (* replace (fun x : A => ⦑ icBind C A B | dNil | M ⦒ (ret' A x)) with *)
    (*     (fun (x:A) (f : A -> carrier B) => f x). *)
    2:{ extensionality a.
        move: (@monad_law1 CMonad) ; rewrite /= /bind' ; move=> -> //.
    }
    rewrite map_bind algstr_bind //.
  Qed.

  Definition lift_monmon : MonotonicMonadMorphism M CMonad :=
    @mkMonMorphism _ _ lift_monad_morph lift_carrier_monotonic.

  Definition CMonadUnder : OrderedMonadUnder M :=
    @mkMonadUnder _ CMonad lift_monmon.

End ToOrderedMonad.

Section ToMonadMorphism.
  Context (C:icmonad) (Hcov : forall A, covariant (icM C A))
          (M1 M2 : OrderedMonad) (θ : MonotonicMonadMorphism M1 M2).

  Definition mmorph_carrier A := to_function _ _ θ (icM C A) (Hcov A).

  Context pf1 pf2 pf3 (CM1 := OrderedMonadFromEqns M1 C pf1 pf2 pf3).
  Context pf1' pf2' pf3' (CM2 := OrderedMonadFromEqns M2 C pf1' pf2' pf3').

  Lemma mmorph_carrier_mon A
    : SProper (@omon_rel CM1 A s==> @omon_rel CM2 A) (mmorph_carrier A).
  Proof.
    move=> /= ? ? ?; apply to_function_monotonic ; intuition ; apply monmon_monotonic.
  Qed.

  Import Substitution.
  Definition val_cov M (c:ctype) := ⦑ c | M ⦒ × covariant c.

  Program Definition CMonadMorph : MonotonicMonadMorphism CM1 CM2 :=
    @mkMonMorphism _ _ (@mkMorphism _ _ mmorph_carrier _ _) mmorph_carrier_mon.
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

Section ToMonadMorphismMonotonic.
  Context (C:icmonad) (Hcov : forall A, covariant (icM C A))
          (M1 M2 : OrderedMonad) (θ θ' : MonotonicMonadMorphism M1 M2)
          (refineθ : monad_morph_refines θ θ')
          (θmon : forall A, SProper (@omon_rel M1 A s==> @omon_rel M2 A) (θ A)).
          (* (θmon : forall A, SProper (@omon_rel M1 A s==> @omon_rel M2 A) (θ A)). *)

  Context pf1 pf2 pf3 pf1' pf2' pf3'
          (ϕ := CMonadMorph C Hcov M1 M2 θ pf1 pf2 pf3 pf1' pf2' pf3')
          (ϕ' := CMonadMorph C Hcov M1 M2 θ' pf1 pf2 pf3 pf1' pf2' pf3').

  Lemma mmorph_refines : monad_morph_refines ϕ ϕ'.
  Proof.
    move=> ? ?. rewrite /ϕ /ϕ'. unfold CMonadMorph.
    unfold mmorph_carrier. simpl.
    apply to_function_monotonic.
    intros. stransitivity (θ A x1').
    apply θmon. assumption.
    apply refineθ. sreflexivity.
  Qed.
End ToMonadMorphismMonotonic.

Section ToMonadMorphismIdentity.
  Context (C:icmonad) (Hcov : forall A, covariant (icM C A)) (M1 : OrderedMonad). 

  Context  pf1 pf2 pf3 (ϕ := CMonadMorph C Hcov M1 M1 (identity_monmon M1) pf1 pf2 pf3 pf1 pf2 pf3).

  Lemma mmorph_preserves_id : forall A m, ϕ A m = m.
  Proof.
    intros. unfold CMonadMorph. simpl. unfold mmorph_carrier.
    apply to_function_id.
  Qed.

  Context (M2 M3 : OrderedMonad)
          (f12 : MonotonicMonadMorphism M1 M2) (f23 : MonotonicMonadMorphism M2 M3).

  Context  pf1' pf2' pf3' (ϕ12 := CMonadMorph C Hcov M1 M2 f12 pf1 pf2 pf3 pf1' pf2' pf3').
  Context  pf1'' pf2'' pf3'' (ϕ23 := CMonadMorph C Hcov M2 M3 f23 pf1' pf2' pf3' pf1'' pf2'' pf3'').
  Let ϕ13 := CMonadMorph C Hcov M1 M3 (comp_monmon f12 f23) pf1 pf2 pf3 pf1'' pf2'' pf3''.

  Lemma mmorph_preserves_comp :
    forall A m, ϕ23 A (ϕ12 A m) = ϕ13 A m.
  Proof.
    intros. unfold CMonadMorph. simpl. unfold mmorph_carrier.
    apply to_function_comp.
  Qed.

End ToMonadMorphismIdentity.


Section LiftNatural.
  Context (C:icmonad) (Hcov:forall A, covariant (icM C A))
          (M1 M2:OrderedMonad) (θ : MonotonicMonadMorphism M1 M2).

  Import FunctionalExtensionality.
  Lemma mon_morph_alg (c:ctype) c_cov :
    let θ' := to_function M1 M2 θ c c_cov in
    forall m, θ' (wit (ctype_alg M1 c) m) = wit (ctype_alg M2 c) (θ' <$> θ _ m).
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

  Context  pf1 pf2 pf3 pf1' pf2' pf3' (ϕ := CMonadMorph C Hcov M1 M2 θ
                                                        pf1 pf2 pf3
                                                        pf1' pf2' pf3').
  Lemma lift_natural :
    forall A m, lift_carrier M2 C A (θ A m) = ϕ A (lift_carrier M1 C A m). 
  Proof.
    unfold lift_carrier.
    intro_map.
    intros. rewrite monad_morphism_natural.
    replace (ret' M2 C A) with (fun a => ϕ A (ret' M1 C A a)).
    2:{ extensionality a.
        move: (mon_morph_ret ϕ) => /= Hret ; apply Hret.
    }
    unfold CMonadMorph. simpl. unfold mmorph_carrier.
    rewrite mon_morph_alg. f_equal.
    rewrite monad_morphism_natural.
    rewrite map_functorial.
    reflexivity.
    simpl.
    rewrite monad_morphism_natural map_functorial //.
  Qed.
End LiftNatural.

Definition CMonadTransformer C Hbind Hcov : OrderedMonadTransformer :=
  @mkOrderedMonadTransformer
    (fun M => CMonadUnder M C (Hbind M))
    (fun M1 M2 θ => CMonadMorph C Hcov M1 M2 θ _ _ _ _ _ _)
    (fun M => mmorph_preserves_id C Hcov M _ _ _)
    (fun M1 M2 M3 θ12 θ23 => mmorph_preserves_comp C Hcov M1 _ _ _ M2 M3 θ12 θ23 _ _ _ _ _ _)
    (fun M1 M2 θ A m => eq_sym (lift_natural C Hcov M1 M2 θ _ _ _ _ _ _ A m)).


Section ToMonadicRelation.
  Context (C:icmonad) (M0:Monad) (M1:=DiscreteMonad M0) (M2 : OrderedMonad)
          (R : MonadIdeal M1 M2).

  Definition mrel_carrier A := to_srel M1 M2 R (icM C A).

  Context pf1 pf2 pf3 (CM1 := OrderedMonadFromEqns M1 C pf1 pf2 pf3).
  Context pf1' pf2' pf3' (CM2 := OrderedMonadFromEqns M2 C pf1' pf2' pf3').

  Import Substitution.

  Program Definition CMonadRel : MonadRelation CM1 CM2 :=
    @mkMonadRelation CM1 CM2 mrel_carrier _ _.
  Next Obligation.
    simple refine (icterm_to_srel_witness M1 M2 R (icRet C A @ a) dNil).
  Qed.
  Next Obligation.
    unshelve epose (σ := dCons (MkSRelVal M1 M2 R (A ~> icM C B) f g H0)
                         (dCons (MkSRelVal _ _ _ (icM C A) m w H) dNil)).
    pose (Hbind := (↑↑ icBind C A B ) @c ↑vz @c vz).
    move: (icterm_to_srel_witness M1 M2 R Hbind σ) => /=.
    rewrite !(to_term_weaken _).
    do 4 (simpl ; simp_dlookup) => //.
  Qed.

  Program Definition CMonadIdeal : MonadIdeal CM1 CM2 :=
    @mkMonadIdeal _ _ CMonadRel _.
  Next Obligation.
    move: H0 ; apply to_srel_mon.
    cbv ; intros ; subst_sEq ; move : H2. apply mid_upper_closed ; assumption.
    sreflexivity.
    assumption.
  Qed.
End ToMonadicRelation.