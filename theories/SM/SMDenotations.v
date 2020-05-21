From Coq Require Import List ssreflect.
From Mon Require Import Base.
From Mon.SM Require Export SMSyntax.
From Mon.sprop Require Import SPropBase SPropMonadicStructures.
From Equations Require Equations.


(******************************************************************************)
(**                                                                           *)
(**              Denotation from SM to Gallina                                *)
(**                                                                           *)
(******************************************************************************)

(** Denotation of types (discrete order case) *)

Section ToType.
  Context (M:Type -> Type).

  Fixpoint to_type (c:ctype) {struct c} : Type :=
    match c with
    | CM A => M A
    | CProd C1 C2 => to_type C1 × to_type C2
    | @CArr A C => forall (x:A), to_type (C x)
    | CArrC C1 C2 => to_type C1 -> to_type C2
    end.
End ToType.

Notation "⦑ C | M ⦒" := (to_type M C).


Section ICTermToTerm.
  Context (M:Monad).

  Definition icterm_to_term {Γ c} (ct : icterm Γ c) :
    substitution (to_type M) Γ -> ⦑ c |M⦒.
  Proof.
    induction ct ; intro σ.
    exact ret.
    exact (bind (IHct2 σ) (IHct1 σ)). 
    exact (npair (IHct1 σ) (IHct2 σ)).
    destruct c ; inversion H ; exact (nfst (IHct σ)).
    destruct c ; inversion H ; exact (nsnd (IHct σ)).
    intro v ; apply (X v σ).
    destruct c ; inversion H ; exact (IHct σ v).
    exact (Substitution.dlookup _ _ σ H).
    intro x ; exact (IHct (ConsSubst x σ)).
    destruct c ; inversion H ; exact (IHct1 σ (IHct2 σ)).
  Defined.

End ICTermToTerm.

Notation "⦑ t | σ | M ⦒" := (icterm_to_term M t σ).



(** Denotation commutes to substitution *)

Section ICTermToTermSubst.
  Import DepElim.
  Context (M:Monad).

  Lemma map_subst_comp : forall {Γ var1 var2 var3} (σ : substitution var1 Γ) (f : forall c, var1 c -> var2 c) (g: forall c, var2 c -> var3 c),
      map_subst g (map_subst f σ) = map_subst (fun c x => g c (f c x)) σ.
  Proof.
    unfold map_subst.
    intros.
    rewrite <- Substitution.dmap_compose.
    reflexivity.
  Qed.

  (* Lemma to_term_weaken0 {Γ1 Γ2 c} (t:icterm (Γ1++Γ2) c) : *)
  (*   forall c0 (x:⦑c0|M⦒) (σ1 : substitution (to_type M) Γ1) *)
  (*     (σ2 : substitution (to_type M) Γ2), *)
  (*     ⦑ rename0 t (weaken_renaming c0) | appSubst σ1 (ConsSubst x σ2) |M⦒ *)
  (*     = ⦑ t | appSubst σ1 σ2 |M⦒. *)
  Import Equations.
  Import EqNotations.
  Import Substitution.

  Import FunctionalExtensionality.
  Lemma to_term_rename {Γ1 c} (t:icterm Γ1 c) :
    forall Γ2 (σ : substitution (to_type M) Γ2) (ρ : irenaming Γ2 Γ1),
      ⦑ rename0 t ρ | σ |M⦒ = ⦑ t | renaming_subst_act ρ σ  |M⦒.
  Proof.
    induction t ; intros Γ2 σ ρ ; simpl.
    reflexivity.
    f_equal ; [apply IHt2 | apply IHt1].
    f_equal ; [apply IHt1 | apply IHt2].
    destruct c ; inversion H ; destruct H ; erewrite IHt ; reflexivity.
    destruct c ; inversion H ; destruct H ; erewrite IHt ; reflexivity.
    extensionality v ; apply H.
    destruct c ; inversion H ; destruct H ; erewrite IHt ; reflexivity.
    rewrite dlookup_renaming_subst_act.
    set (z := dlookup n Γ ρ H).
    destruct z as [n' [Hn Hlkp]].
    simpl.
    symmetry.
    change (rew ?H in ?x = ?y) with (x =⟨H⟩ y).
    apply (fun_app_above ctype _ _ Hlkp (icterm Γ2) (to_type M)(fun c ct => @icterm_to_term M Γ2 c ct σ) (ICVar n' (StrictProp.unbox Hn))).
    extensionality x.
    move: renaming_weaken (IHt  _ (ConsSubst x σ) (cons_renaming c1 ρ)).
    unfold renaming_subst_act ; unfold cons_renaming.
    simp dmap; unfold lkp_tyvar_subst ; simp_dlookup.
    move=> -> //.
    destruct c ; inversion H ; destruct H; erewrite IHt1 ; erewrite IHt2 ; reflexivity.
    Qed.
    
  Lemma to_term_weaken {Γ c} (t:icterm Γ c) :
  forall c0 (x:⦑c0|M⦒) (σ : substitution (to_type M) Γ),
    ⦑ ↑ t | ConsSubst x σ |M⦒ = ⦑ t |σ  |M⦒.
  Proof.
    intros ;
      move: (to_term_rename t (c0::Γ) (ConsSubst x σ)
                            (@weaken_renaming c0 nil _)) ;
      unfold weaken_renaming=> //.
    rewrite renaming_weaken renaming_subst_act_id //.
  Qed.

  Import FunctionalExtensionality.
  Lemma to_term_isubst {Γ c} (t:icterm Γ c) :
    forall Γ' (σ : substitution (to_type M) Γ') (ρ : isubstitution Γ' Γ),
      ⦑ isubst t ρ | σ |M⦒ = ⦑ t | map_subst (fun c m => ⦑ m | σ |M⦒) ρ |M⦒.
  Proof.
    induction t ; simpl ; intros Γ' σ ρ.
    reflexivity.
    f_equal ; auto.
    f_equal ; auto.
    destruct c ; destruct H ; rewrite IHt ; reflexivity.
    destruct c ; destruct H ; rewrite IHt ; reflexivity.
    extensionality x ; auto.
    destruct c ; destruct H ; rewrite IHt ; reflexivity.
    rewrite dlookup_dmap ; reflexivity.
    extensionality x; rewrite IHt; simpl;
      rewrite map_subst_comp; unfold ConsSubst ;
        do 2 f_equal ; unfold map_subst; apply dmap_ext=> // ? ?;
        rewrite to_term_weaken; reflexivity.
    destruct c ; destruct H ; rewrite IHt1; rewrite IHt2; reflexivity.
  Qed.

End ICTermToTermSubst.


(** Denotation preserves the equational theory *)

Section ICeqToEq.
  Import DepElim.
  Context (M:Monad).

  Let var_eq c := {p:⦑c |M⦒ × ⦑c|M⦒ ⫳ nfst p = nsnd p}.
  Let efst c (m:var_eq c) := nfst (dfst m).
  Let esnd c (m:var_eq c) := nsnd (dfst m).
  (* Let eeq c (m:var_eq c) := dsnd m. *)

  Import FunctionalExtensionality.
  Definition icterm_diagonal {Γ c} (ct : icterm Γ c) : forall (σ : substitution var_eq Γ), ⦑ct | map_subst efst σ |M⦒ = ⦑ ct | map_subst esnd σ |M⦒.
  Proof.
    induction ct ; simpl ; intros σ.
    reflexivity.
    f_equal ; auto.
    f_equal ; auto.
    destruct c ; destruct H ; erewrite IHct ; [reflexivity|..] ; eassumption.
    destruct c ; destruct H ; erewrite IHct ; [reflexivity|..] ; eassumption.
    extensionality v ; auto.
    destruct c ; destruct H ; simpl;
      erewrite IHct ; [reflexivity|..] ; eassumption.
    rewrite !Substitution.dlookup_dmap ; exact (dsnd (Substitution.dlookup n Γ σ H)).
    extensionality x;
      exact (IHct (ConsSubst (dpair _ ⟨x, x⟩ eq_refl) σ)).
    destruct c ; destruct H ; rewrite IHct1 ; rewrite IHct2 ; reflexivity.
  Qed.

  Import Substitution.
  Lemma map_subst_id Γ σ :
    map_subst (fun c m => @icterm_to_term M Γ c m σ) (id_isubst Γ) = σ.
  Proof.
    apply (dlist_extensionality _ _ _ eq_refl _) => n.
    revert Γ σ; induction n; move=> ? σ H ; dependent elimination σ ; simp_dlookup.
    simp dmap ; simp_dlookup; by [].
    simpl in IHn |- *.
    rewrite dlookup_dmap. simp_dlookup.
    rewrite <- IHn.
    rewrite !dlookup_dmap. apply to_term_weaken.
  Qed.

  Definition iceq_to_eq {Γ c} {ct1 ct2 : icterm Γ c} (Heq : ct1 ≅ ct2) :
    forall (σ : substitution var_eq Γ),
      ⦑ct1 | map_subst efst σ |M⦒ = ⦑ ct2 | map_subst esnd σ |M⦒.
  Proof.
    induction Heq ; simpl ; intros σ.
    1-3:unfold bind ; unfold ret.
    rewrite monad_law1 ; rewrite icterm_diagonal ; reflexivity.
    rewrite monad_law2 ; rewrite icterm_diagonal ; reflexivity.
    rewrite monad_law3 ; rewrite 3!icterm_diagonal ; reflexivity.
    f_equal ; auto.
    destruct H ; apply icterm_diagonal.
    destruct H ; apply icterm_diagonal.
    destruct H ; rewrite icterm_diagonal ; reflexivity.
    f_equal ; auto.
    destruct c ; destruct H ; rewrite IHHeq ; reflexivity.
    destruct c ; destruct H ; rewrite IHHeq ; reflexivity.
    destruct H ; rewrite icterm_diagonal ; reflexivity.
    destruct H ; extensionality v ; rewrite icterm_diagonal; reflexivity.
    extensionality v ; auto.
    destruct c ; destruct H ; dependent destruction Heq ; rewrite IHHeq ; reflexivity.
    destruct H ; unfold isubst_one; rewrite to_term_isubst; simpl; rewrite map_subst_id;
      pose (hd := dpair _
                        ⟨⦑ct2 | map_subst efst σ |M⦒, ⦑ct2 | map_subst esnd σ |M⦒⟩
                        (icterm_diagonal ct2 σ) : var_eq _);
      apply (icterm_diagonal ct1 (ConsSubst hd σ)).

    destruct H ; extensionality x; cbn; rewrite to_term_weaken; rewrite icterm_diagonal; reflexivity.
    extensionality x; apply (IHHeq (ConsSubst (dpair _ ⟨x,x⟩ eq_refl) σ)).
    destruct c ; destruct H ; rewrite IHHeq1 ; rewrite IHHeq2 ; reflexivity.
    apply icterm_diagonal.
    symmetry ; rewrite icterm_diagonal ; rewrite <- (icterm_diagonal ct1) ; apply IHHeq.
    transitivity ⦑ ct2 | map_subst esnd σ |M⦒ ; [|rewrite <- (icterm_diagonal ct2)] ; auto.
  Qed.
End ICeqToEq.




(******************************************************************************)
(**                                                                           *)
(**              Logical relation on the denotation                           *)
(**                                                                           *)
(******************************************************************************)

(** Relational interpretation of types *)

Section ToRel.
  Context (M1 M2 : Type -> Type).
  Context (R : forall A, M1 A -> M2 A -> Type).

  Fixpoint to_rel (c:ctype) : ⦑ c |M1⦒ -> ⦑ c |M2⦒ -> Type :=
    match c with
    | CM A => R A
    | CProd c1 c2 =>
      fun '⟨x11, x21⟩ '⟨x12, x22⟩ => to_rel c1 x11 x12 × to_rel c2 x21 x22
    | CArr c => fun f1 f2 => forall x, to_rel (c x) (f1 x) (f2 x)
    | CArrC c1 c2 => fun f1 f2 => forall x1 x2, to_rel c1 x1 x2 -> to_rel c2 (f1 x1) (f2 x2)
    end.

End ToRel.

(** Covariance restriction on SM types *)

Fixpoint covariant (c:ctype) : Prop :=
  match c with
  | CM _ => True
  | CProd c1 c2 => covariant c1 /\ covariant c2
  | CArr Cs => forall x, covariant (Cs x)
  | CArrC _ _ => False
  end.


(** (Functional) Special case when the SM type is covariant *)

Section ToFunction.
  Context (M1 M2 : Type -> Type).
  Context (θ : forall A, M1 A -> M2 A).
  Context (c:ctype) (c_cov : covariant c).

  Definition to_function : ⦑ c |M1⦒ -> ⦑ c |M2⦒.
  Proof.
    induction c as [A| | |].
    exact (θ A).
    intros [] ; destruct c_cov ; simpl ; intuition ; auto.
    intros ? x ; simpl in c_cov ; specialize c_cov with x; auto.
    contradiction c_cov.
  Defined.

End ToFunction.

Section ToFunctionLemmas.
  Context (M1 M2 M3 : Type -> Type).
  Context (c:ctype) (c_cov : covariant c).

  Import FunctionalExtensionality.
  Lemma to_function_id : forall m, to_function M1 M1 (fun A => id) c c_cov m = m.
  Proof.
    induction c ; simpl.
    intros ; reflexivity.
    intros [? ?] ; destruct c_cov ; f_equal ; auto.
    intros ? ; extensionality x; auto.
    inversion c_cov.
  Qed.

  Context (f : forall A, M1 A -> M2 A) (g: forall A, M2 A -> M3 A).
    
  Lemma to_function_comp :
    forall m, to_function M2 M3 g c c_cov (to_function M1 M2 f c c_cov m) = to_function M1 M3 (fun _ x => g _ (f _ x)) c c_cov m.
  Proof.
    induction c ; simpl.
    intros ; reflexivity.
    intros [? ?] ; destruct c_cov ; f_equal ; auto.
    intros ? ; extensionality x; auto.
    inversion c_cov.
  Qed.

End ToFunctionLemmas.



(** Compatibility of the special case to the general case *)

Section ToRelToFunction.
  Context (M1 M2 : Type -> Type).
  Context (θ : forall A, M1 A -> M2 A).

  Let R := fun A (m1: M1 A) (m2 : M2 A) => θ A m1 = m2.

  Import FunctionalExtensionality.

  Fixpoint to_rel_to_function (c:ctype) : forall (c_cov : covariant c) x1 x2,
      to_rel M1 M2 R c x1 x2 -> to_function M1 M2 θ c c_cov x1 = x2
  with to_function_to_rel (c:ctype) : forall (c_cov : covariant c) x1 x2,
      to_function M1 M2 θ c c_cov x1 = x2 -> to_rel M1 M2 R c x1 x2.
  Proof.
    all:destruct c ; simpl.
    intros ? ? ? ; trivial.
    intros [] [] [] [] ; f_equal ; auto.
    intros ? ? ? ? ; extensionality x ; auto.
    intros [].

    intros ? ? ? ; trivial.
    intros [] [] [] H ; injection H ; clear H ; intros ? ? ; split ;
      eapply to_function_to_rel ; eassumption.
    intros ? ? ? H ? ; apply (f_equal (fun f => f x)) in H;
      eapply to_function_to_rel; eassumption.
    intros [].
  Defined.

End ToRelToFunction.


(** Relational interpretation of terms
    (aka. fundamental lemma of logical relations)*)

Section ICTermToRel.
  Import DepElim.
  Context (M1 M2 : Monad).
  Context (R : forall A, M1 A -> M2 A -> Prop).
  Context (Runit : forall A (x:A), R A (ret x) (ret x)).
  Context (Rbind : forall A B (m1 : M1 A) (m2 : M2 A) (f1 : A -> M1 B) (f2 : A -> M2 B), R A m1 m2 -> (forall x:A, R B (f1 x) (f2 x)) -> R B (bind m1 f1) (bind m2 f2)).

  Let MR := to_rel M1 M2 R.
  Record rel_val (c:ctype) :=
    MkRelVal { fst : to_type M1 c ; snd : to_type M2 c ; rel : MR c fst snd }.

  Definition icterm_to_rel_witness {Γ c} (ct:icterm Γ c) :
    forall σ : substitution rel_val Γ,
      to_rel M1 M2 R c ⦑ ct | map_subst fst σ |M1⦒ ⦑ ct | map_subst snd σ |M2⦒. 
  Proof.
    induction ct ; simpl.
    - intros ? ; apply Runit.
    - intros σ ; apply Rbind ; [ apply IHct2 | apply IHct1 ].
    - intro σ ; constructor; [apply IHct1| apply IHct2].
    - intro σ; destruct c ; destruct H ; exact (nfst (IHct σ)).
    - intro σ; destruct c ; destruct H ; exact (nsnd (IHct σ)).
    - intros σ x ; apply (X x).
    - intro σ.
      destruct c ; destruct H ; apply (IHct σ).
    - intros σ ; rewrite /map_subst ;
        erewrite 2!Substitution.dlookup_dmap ;
          apply rel.
    - intros σ x1 x2 r.
      apply (IHct (ConsSubst (MkRelVal c1 x1 x2 r) σ)).
    - intros σ; destruct c ; destruct H ; apply IHct1; apply IHct2.
  Defined.

End ICTermToRel.

(** Functional interpretation of terms
    (in the special case where our types are covariant) *)

Section ICTermToFunction.
  Context (M1 M2 : Monad).
  Context (F : forall A, M1 A -> M2 A).
  Context (Funit : forall A (x:A), F A (ret x) = (ret x)).
  Context (Fbind : forall A B (m : M1 A) (f : A -> M1 B),
              F B (bind m f) = bind (F A m) (fun x => F B (f x))).

  Let R := fun A (m1 : M1 A) (m2: M2 A) => F A m1 = m2.
  Let MF := to_function M1 M2 F.
  Let val_cov (c:ctype) :=to_type M1 c × covariant c.

  Definition val_cov_to_rel_val (c:ctype) (p : val_cov c) : rel_val M1 M2 R c
    := MkRelVal M1 M2 R c (nfst p) (MF c (nsnd p) (nfst p))
                (to_function_to_rel M1 M2 F c (nsnd p) _ _ eq_refl).

  Import FunctionalExtensionality.

  Program Definition icterm_to_fun_witness {Γ c} (ct:icterm Γ c) (Hcov : covariant c)  :=
    fun (σ : substitution val_cov Γ) =>
      let ρ := map_subst val_cov_to_rel_val σ in
      to_rel_to_function M1 M2 F c Hcov _ _ (icterm_to_rel_witness M1 M2 R (Funit) _ ct ρ).
  Next Obligation.
    assert ((fun x => F _ (f1 x)) = f2) as <- by (extensionality x ; apply H0).
    apply Fbind.
  Qed.

  Eval cbn in icterm_to_fun_witness.

  (* TODO : give the following type to icterm_to_fun_witness *)
    (* forall (σ : substitution val_cov Γ), *)
    (*   MF c Hcov ⦑ ct [map_subst (fun c => nfst) σ] |M1⦒ = *)
    (*   ⦑ ct [map_subst (fun c p => MF c (nsnd p) (nfst p)) σ] |M2⦒. *)

End ICTermToFunction.



(******************************************************************************)
(**                                                                           *)
(**              Algebra structure on the denotation                          *)
(**                                                                           *)
(******************************************************************************)

(** Special case for the algebra structure on the dependent product
    that was not given in general *)
Set Primitive Projections.

Section AlgStruct.
  Context (M:Monad).
  Record AlgStruct A :=
    mkAlgStruct
      { algstr_map :> M A -> A
      ; algstr_ret : forall a, algstr_map (monad_ret M a) = a
      ; algstr_bind : forall X (m : M X) f,
          algstr_map (monad_bind m (fun x => monad_ret _ (algstr_map (f x)))) = algstr_map (monad_bind m f)
      }.

  Definition homomorphism {A B}
           (αA : AlgStruct A) (αB : AlgStruct B) (f : A -> B) :=
    forall m, f (αA m) = αB (f <$> m).

  Lemma homormorphism_comp {A B C} (HA : AlgStruct A) (HB : AlgStruct B) (HC : AlgStruct C) (f : A -> B) (g: B -> C) (Hf : homomorphism HA HB f) (Hg : homomorphism HB HC g) : homomorphism HA HC (fun x => g (f x)).
  Proof. move=> m ; rewrite Hf Hg map_functorial //. Qed.

  Lemma homomorphism_id {A} (HA:AlgStruct A) : homomorphism HA HA id.
  Proof. move=> m ; rewrite map_id //. Qed.
End AlgStruct.


Section FreeAlgStruct.
  Context (M:Monad).
  Import FunctionalExtensionality.
  Program Definition freeAlgStruct A : AlgStruct M (M A) :=
    mkAlgStruct _ _ (fun mm => bind mm id) _ _.
  Next Obligation. cbv ; rewrite monad_law1 ; reflexivity. Qed.
  Next Obligation.
    cbv. rewrite !monad_law3.
    f_equal ; extensionality x. rewrite monad_law1 ; reflexivity.
  Qed.

  Section Homomorphism.
    Context {A B} (αB : AlgStruct M B) (f: A -> B).
    Definition free_extension (m:M A) : B := αB (f <$> m).
    Lemma free_extension_homomorphism :
      homomorphism M (freeAlgStruct A) αB free_extension.
    Proof.
      move=> m /=. rewrite /free_extension /map /bind monad_law3 algstr_bind //.
    Qed.
  End Homomorphism.
End FreeAlgStruct.

Section NProductAlgStruct.
  Context M A B (HA : AlgStruct M A) (HB : AlgStruct M B).
  Import FunctionalExtensionality.


  Program Definition nprodAlgStruct : AlgStruct M (A × B) :=
    mkAlgStruct _ _ (fun m => npair (HA (nfst <$> m)) (HB (nsnd <$> m))) _ _.
  Next Obligation.
    cbv ; destruct a ; f_equal ; rewrite monad_law1 ; rewrite algstr_ret ; reflexivity.
  Qed.

  Next Obligation.
   f_equal ;
   cbv ; rewrite !monad_law3 ;
    match goal with
    | [|- _ = ?t ] =>
      match t with
      | context c [monad_bind m ?f] => rewrite <- (algstr_bind _ _ _ _ _ f)
      end
    end ;
    do 2 f_equal ; extensionality x ; rewrite monad_law1 ; reflexivity.
  Qed.

  Lemma proj1_homomorphism : homomorphism M nprodAlgStruct HA nfst.
  Proof.
    move=> m ; rewrite /nprodAlgStruct //.
  Qed.

  Lemma proj2_homomorphism : homomorphism M nprodAlgStruct HB nsnd.
  Proof.
    move=> m ; rewrite /nprodAlgStruct //.
  Qed.

  Section PairingHomomorphism.
    Context {C} (HC : AlgStruct M C) (fA : C -> A) (fB : C -> B)
            (HfA : homomorphism M HC HA fA)
            (HfB : homomorphism M HC HB fB).
    Definition pairing (c:C) : A × B := ⟨fA c, fB c⟩.
    Lemma pairing_homomorphism : homomorphism M HC nprodAlgStruct pairing.
    Proof.
      move=> m. rewrite /pairing /nprodAlgStruct /= 2!map_functorial HfA HfB //.
    Qed.
  End PairingHomomorphism.

End NProductAlgStruct.

Section DependentProductAlgebra.
  Context (M:Monad) A B (HB : forall a:A, AlgStruct M (B a)).

  Import FunctionalExtensionality.
  Program Definition DepProdAlg : AlgStruct M (forall a, B a) :=
    mkAlgStruct _ _ (fun m x => HB x (bind m (fun f => ret (f x)))) _ _.
  Next Obligation.
    intros ; simpl; extensionality x.
    cbv ; rewrite monad_law1. rewrite algstr_ret. reflexivity.
  Qed.
  Next Obligation.
    intros ; extensionality a.
    cbv; rewrite !monad_law3.
    match goal with
    | [|- _ = ?t ] =>
      match t with
      | context c [monad_bind m ?f] => rewrite <- (algstr_bind _ _ _ _ _ f)
      end
    end.
    f_equal. f_equal. extensionality x.
    cbv. rewrite monad_law1. reflexivity.
  Qed.

  Section EvalHomomorphism.
    Context (a:A).
    Definition eval (f:forall a, B a) : B a := f a.
    Lemma eval_homorphism : homomorphism M DepProdAlg (HB a) eval.
    Proof. move=> ? //. Qed.
  End EvalHomomorphism.

  Section AbsHomomorphism.
    Context {C} (HC : AlgStruct M C) (f : forall a, C -> B a)
            (Hf : forall a, homomorphism M HC (HB a) (f a)).
    Lemma abs_homomorphism : homomorphism M HC DepProdAlg (fun c a => f a c).
    Proof.
      move=> x ; rewrite /homomorphism /DepProdAlg /= ;
              extensionality a; rewrite (Hf a) /map /bind monad_law3.
      do 2 f_equal ; extensionality a0 ; rewrite monad_law1 //.
    Qed.
  End AbsHomomorphism.

End DependentProductAlgebra.


(** Algebra structure on the denotation *)

Section ToAlgebra.
  Context (M:Monad) (c : ctype).

  Definition ctype_alg : AlgStruct M ⦑ c  |M⦒.
  Proof.
    induction c as [A| c1 IHc1 c2 IHc2 | |].
    apply freeAlgStruct.
    apply (nprodAlgStruct _ _ _ IHc1 IHc2).
    apply (DepProdAlg _ _ _ X).
    apply (DepProdAlg _ _ _ (fun _ => IHc0_2)).
  Defined.

End ToAlgebra.



