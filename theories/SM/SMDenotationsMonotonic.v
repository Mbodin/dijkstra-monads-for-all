From Coq Require Import List ssreflect ssrfun.
From Mon Require Import Base.
From Mon.SM Require Export SMSyntax.
From Mon.sprop Require Import SPropBase SPropMonadicStructures.
From Mon.SRelation Require Import SRelationClasses SMorphisms.
From Equations Require Equations.
From Coq.Logic Require Import StrictProp.

(******************************************************************************)
(**                                                                           *)
(**              Denotation from SM to Gallina                                *)
(**                                                                           *)
(******************************************************************************)

(** Denotation of types (discrete order case) *)


Section ToPreorder.
  Context (M:OrderedMonad).

  Let Mrel := @omon_rel M.
  Import SPropNotations.

  Definition to_preord (c:ctype) : { I : Type ⫳ I -> I -> SProp }.
  Proof.
    induction c as [A| | | ].
    exists (M A) ; exact (Mrel A).
    exists (dfst IHc1 × dfst IHc2). intros [x1 x2] [y1 y2].
    exact (dsnd IHc1 x1 y1 s/\ dsnd IHc2 x2 y2).
    exists (forall a, dfst (X a)). intros f1 f2 ; exact (forall a, dsnd (X a) (f1 a) (f2 a)).
    exists ({ f : dfst IHc1 -> dfst IHc2 ≫
        forall x1 x2, dsnd IHc1 x1 x2 -> dsnd IHc2 (f x1) (f x2)}).
    intros [f1 ?] [f2 ?] ; exact (forall x, dsnd IHc2 (f1 x) (f2 x)).
  Defined.

  (* Global Instance PreOrderOn_preorder A : PreOrder (@omon_order M A). *)
  (* Proof. *)
  (*   constructor. intros ? ; apply preo_refl. *)
  (*   intros ? ? ? ? ?. eapply preo_trans ; eassumption. *)
  (* Qed. *)

  Notation to_type := (fun c => dfst (to_preord c)).
  Notation to_ord := (fun c => dsnd (to_preord c)). 

  Global Instance to_preord_preorder (c:ctype) : PreOrder (to_ord c).
  Proof.
    induction c ; simpl.
    - typeclasses eauto.
    - constructor.
      + constructor ; sreflexivity.
      + intros ? y ? [] [] ; split ; estransitivity ; eassumption.
    - constructor. intros ? ? ; sreflexivity.
      intros ? ? ? ? ? ? ; estransitivity ; eauto.
    - constructor. intros ? ? ; sreflexivity.
      intros ? ? ? ? ? ? ; estransitivity ; eauto.
    Qed.

End ToPreorder.

Notation to_type := (fun M c => dfst (to_preord M c)).
Notation to_ord := (fun M c => dsnd (to_preord M c)). 

Notation "⦑ C | M ⦒" := (to_type M C).

(** Denotation of terms (discrete order case) *)
Section SubstitutionOrder.
  Context (M:OrderedMonad).

  Let sub := substitution (to_type M).

  Import Equations.
  Import Substitution.
  Import SPropNotations. 

  Definition subst_rel {Γ} (s1 s2 : sub Γ) : SProp :=
    forall n H, to_ord M _ (dlookup n _ s1 H) (dlookup n _ s2 H).

  Global Instance subst_rel_preorder Γ : PreOrder (@subst_rel Γ).
  Proof.
    constructor.
    intros ? ? ?; sreflexivity.
    intros ? ? ? ? ? ? ? ; estransitivity ; eauto.
  Qed.

  Lemma dCons_subst_rel {c Γ} (x1 x2 : to_type M c) (s1 s2 : sub Γ) :
    to_ord M _ x1 x2 -> subst_rel s1 s2 -> subst_rel (dCons x1 s1) (dCons x2 s2).
  Proof.
    move=> ? H [|?] ? ; do 2 simp_dlookup. assumption. refine (H _ _).
  Qed.

End SubstitutionOrder.

Section ICTermToTerm.
  Context (M:OrderedMonad).

  Import SPropNotations.

  Definition icterm_to_monotonic_term {Γ c} (ct : icterm Γ c) :
    { f : substitution (to_type M) Γ -> to_type M c
    ≫ forall s1 s2, subst_rel M s1 s2 -> to_ord M c (f s1) (f s2)}.
  Proof.
    induction ct ; (unshelve econstructor ; [intro σ | intros s1 s2 Hs]).
    - exact ret.
    - abstract sreflexivity.
    - exact (bind (Spr1 IHct2 σ) (Spr1 IHct1 σ)).
    - abstract (apply omon_bind ; [apply (Spr2 IHct2 _ _ Hs)
                                  |intros a ; apply (Spr2 IHct1 _ _ Hs a)]).
    - exact (npair (Spr1 IHct1 σ) (Spr1 IHct2 σ)).
    - abstract (split ; [apply (Spr2 IHct1 _ _ Hs) | apply (Spr2 IHct2 _ _ Hs)]).
    - destruct c ; inversion H ; exact (nfst (Spr1 IHct σ)).
    - abstract (destruct c ; inversion H ; destruct (Spr2 IHct _ _ Hs) ;
        destruct H ; assumption).
    - destruct c ; inversion H ; exact (nsnd (Spr1 IHct σ)).
    - abstract (destruct c ; inversion H ; destruct (Spr2 IHct _ _ Hs) ;
        destruct H ; assumption).
    - intro v ; apply (Spr1 (X v) σ).
    - abstract (intros a ; apply (Spr2 (X a) _ _ Hs)).
    - destruct c ; inversion H ; exact (Spr1 IHct σ v).
    - abstract (destruct c ; inversion H ; destruct H ; exact (Spr2 IHct _ _ Hs v)).
    - exact (Substitution.dlookup _ _ σ H).
    - abstract (simpl; auto).
    - exists (fun x => Spr1 IHct (ConsSubst x σ)).
      intros x1 x2 H. simple refine (Spr2 IHct (Substitution.dCons x1 σ)
                                        (Substitution.dCons x2 σ) _).
      apply dCons_subst_rel. assumption. sreflexivity.
    - abstract (intros ? ; simple refine (Spr2 IHct _ _ _);
                apply dCons_subst_rel ;
                 [sreflexivity | assumption]).
    - destruct c ; inversion H ; exact (Spr1 (Spr1 IHct1 σ) (Spr1 IHct2 σ)).
    - abstract
        (destruct c ; inversion H ; destruct H ;
         estransitivity ;
         [simple refine (Spr2 IHct1 _ _ Hs _) |
          apply (Spr2 (Spr1 IHct1 s2)); apply (Spr2 IHct2 _ _ Hs)]).
  Defined.
  
  Definition icterm_to_term {Γ c} (ct : icterm Γ c) :
    substitution (to_type M) Γ -> ⦑ c |M⦒ :=
    Spr1 (icterm_to_monotonic_term ct).

End ICTermToTerm.

Notation "⦑ t | σ | M ⦒" := (Spr1 (icterm_to_monotonic_term M t) σ).

(** Denotation commutes to substitution *)

Section ICTermToTermSubst.
  Import DepElim.
  Context (M:OrderedMonad).

  Lemma map_subst_comp : forall {Γ var1 var2 var3} (σ : substitution var1 Γ) (f : forall c, var1 c -> var2 c) (g: forall c, var2 c -> var3 c),
      map_subst g (map_subst f σ) = map_subst (fun c x => g c (f c x)) σ.
  Proof.
    unfold map_subst.
    intros.
    rewrite <- Substitution.dmap_compose.
    reflexivity.
  Qed.

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
    apply Ssig_eq. extensionality x.
    move: renaming_weaken (IHt  _ (ConsSubst x σ) (cons_renaming c1 ρ)).
    unfold renaming_subst_act ; unfold cons_renaming.
    simp dmap; unfold lkp_tyvar_subst ; simp_dlookup.
    move=> -> //.
    destruct c ; inversion H ; destruct H; erewrite IHt1 ; erewrite IHt2 ; reflexivity.
    Qed.

  Lemma to_term_weaken {Γ c} (t:icterm Γ c) :
    forall c0 (x:⦑c0|M⦒) (σ : substitution (to_type M) Γ),
      ⦑ weaken c0 t | ConsSubst x σ |M⦒ = ⦑ t |σ  |M⦒.
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
    extensionality x ; apply H.
    destruct c ; destruct H ; rewrite IHt ; reflexivity.
    rewrite Substitution.dlookup_dmap ; reflexivity.
    apply Ssig_eq.
    extensionality x. simpl. rewrite IHt; simpl.
    rewrite map_subst_comp; unfold ConsSubst.
    do 2 f_equal; apply Substitution.dmap_ext=> // ? ? ;
    apply to_term_weaken.
    destruct c ; destruct H. rewrite IHt1; rewrite IHt2; reflexivity.
  Qed.

End ICTermToTermSubst.


(** Denotation preserves the equational theory *)

Section ICeqToEq.
  Import DepElim.
  Context (M:OrderedMonad).

  Let var_eq c := {p:⦑c |M⦒ × ⦑c|M⦒ ⫳ nfst p = nsnd p}.
  Let efst c (m:var_eq c) := nfst (dfst m).
  Let esnd c (m:var_eq c) := nsnd (dfst m).

  Import FunctionalExtensionality.
  Definition icterm_diagonal {Γ c} (ct : icterm Γ c) : forall (σ : substitution var_eq Γ), ⦑ct | map_subst efst σ |M⦒ = ⦑ ct | map_subst esnd σ |M⦒.
  Proof.
    induction ct ; unfold icterm_to_term in *; simpl ; intros σ.
    reflexivity.
    f_equal ; auto.
    f_equal ; auto.
    destruct c ; destruct H ; erewrite IHct ; [reflexivity|..] ; eassumption.
    destruct c ; destruct H ; erewrite IHct ; [reflexivity|..] ; eassumption.
    extensionality v ; auto.
    destruct c ; destruct H ; simpl;
      erewrite IHct ; [reflexivity|..] ; eassumption.
    rewrite !Substitution.dlookup_dmap ; exact (dsnd (Substitution.dlookup n Γ σ H)).
    apply Ssig_eq.
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

    destruct H. apply Ssig_eq. extensionality x; cbn; rewrite to_term_weaken; rewrite icterm_diagonal; reflexivity.
    apply Ssig_eq. extensionality x; apply (IHHeq (ConsSubst (dpair _ ⟨x,x⟩ eq_refl) σ)).
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
  Context (M1 M2 : OrderedMonad).
  Context (R : forall A, M1 A -> M2 A -> Type).

  Definition to_rel (c:ctype) : ⦑ c |M1⦒ -> ⦑ c |M2⦒ -> Type.
  Proof.
    induction c ; simpl.
    apply R.
    intros [x1 x2] [x1' x2'] ; exact (IHc1 x1 x1' × IHc2 x2 x2').
    intros f f' ; exact (forall (x:A), X x (f x) (f' x)).
    intros f f' ; exact (forall x x', IHc1 x x' -> IHc2 (Spr1 f x) (Spr1 f' x')).
  Defined.

End ToRel.

Section ToSRel.
  Context (M1 M2 : OrderedMonad).
  Context (R : forall A, M1 A -> M2 A -> SProp).
  Import SPropNotations.

  Definition to_srel (c:ctype) : ⦑ c |M1⦒ -> ⦑ c |M2⦒ -> SProp.
  Proof.
    induction c ; simpl.
    apply R.
    intros [x1 x2] [x1' x2'] ; exact (IHc1 x1 x1' s/\ IHc2 x2 x2').
    intros f f' ; exact (forall (x:A), X x (f x) (f' x)).
    intros f f' ; exact (forall x x', IHc1 x x' -> IHc2 (Spr1 f x) (Spr1 f' x')).
  Defined.

  Context (Rmon : forall A, SProper (@omon_rel M1 A s==> @omon_rel M2 A s==> s_impl) (R A)).

  Lemma to_srel_mon (c:ctype) :
    SProper (to_ord M1 c s==> to_ord M2 c s==> s_impl) (to_srel c).
  Proof.
    induction c ; simpl.
    apply Rmon.
    move=> [? ?] [? ?] [? ?] [? ?] [? ?] [? ?] [H1 H2] ; split.
    move:H1 ; apply IHc1 ; assumption.
    move:H2 ; apply IHc2 ; assumption.
    move=> ? ? ? ? ? ? H0 a; move: (H0 a) ; apply H ; auto.
    move=> ? ? ? ? ? ? H0 ? ? H1; move: (H0 _ _ H1) ; apply IHc2 ; auto.
  Qed.
End ToSRel.

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
  Context (M1 M2 : OrderedMonad).
  Context (θ : forall A, M1 A -> M2 A).
  Context (c:ctype) (c_cov : covariant c).

  Definition to_function : ⦑ c |M1⦒ -> ⦑ c |M2⦒.
  Proof.
    induction c as [A| | |].
    exact (θ A).
    intros [x1 x2] ; destruct c_cov as [cov1 cov2] ; split;
      [exact (IHc0_1 cov1 x1) | exact (IHc0_2 cov2 x2)].
    intros f x ; simpl in c_cov ; specialize c_cov with x; apply (X _ c_cov (f x)).
    contradiction c_cov.
  Defined.


End ToFunction.

Section ToFunctionMonotone.
  Context (M1 M2 : OrderedMonad).
  Context (θ θ' : forall A, M1 A -> M2 A).
  Context (c:ctype) (c_cov : covariant c).
  Context (θmon : forall A (x1 x1' : M1 A), omon_rel x1 x1' -> omon_rel (θ A x1) (θ' A x1')).
  Let f := to_function M1 M2 θ c c_cov.
  Let f' := to_function M1 M2 θ' c c_cov.
  Lemma to_function_monotonic : forall x x', to_ord M1 c x x' -> to_ord M2 c (f x) (f' x').
  Proof.
    induction c.
    apply θmon.
    intros ? ? [H1 H2] ; destruct c_cov as [cov1 cov2] ; split ;
      [apply (IHc0_1 cov1 _ _ H1) | apply (IHc0_2 cov2 _ _ H2)].
    intros ? ? f0 a ; apply (H a (c_cov a) _ _ (f0 a)). 
    inversion c_cov.
  Qed.
End ToFunctionMonotone.

Section ToFunctionLemmas.
  Context (M1 M2 M3 : OrderedMonad).
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
  Context (M1 M2 : OrderedMonad).
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
    intros [] [] [] [] ; f_equal ;apply to_rel_to_function ; assumption.
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
  Context (M1 M2 : OrderedMonad).
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
    - intros σ ; rewrite /map_subst;
        erewrite 2!Substitution.dlookup_dmap ;
          apply rel.
    - intros σ x1 x2 r.
      apply (IHct (ConsSubst (MkRelVal c1 x1 x2 r) σ)).
    - intros σ; destruct c ; destruct H ; apply IHct1; apply IHct2.
  Defined.

End ICTermToRel.

Section ICTermToSRel.
  Import DepElim.
  Context (M1 M2 : OrderedMonad).
  Context (R : MonadRelation M1 M2).
  Context (Rmon : forall A, SProper (@omon_rel M1 A s==> @omon_rel M2 A s==> s_impl) (R A)).

  Let MR := to_srel M1 M2 R.
  Record srel_val (c:ctype) :=
    MkSRelVal { sfst : to_type M1 c ; ssnd : to_type M2 c ; srel : MR c sfst ssnd }.

  Definition icterm_to_srel_witness {Γ c} (ct:icterm Γ c) :
    forall σ : substitution srel_val Γ,
      to_srel M1 M2 R c ⦑ ct | map_subst sfst σ |M1⦒ ⦑ ct | map_subst ssnd σ |M2⦒. 
  Proof.
    induction ct ; simpl.
    - intros ? ; apply mrel_ret.
    - intros σ ; apply mrel_bind ; [ apply IHct2 | apply IHct1 ].
    - intro σ ; constructor; [apply IHct1| apply IHct2].
    - intro σ; destruct c ; destruct H ; destruct (IHct σ) ; assumption.
    - intro σ; destruct c ; destruct H ; destruct (IHct σ) ; assumption.
    - intros σ x ; apply (H x).
    - intro σ.
      destruct c ; destruct H ; apply (IHct σ).
    - intros σ ; rewrite /map_subst;
        erewrite 2!Substitution.dlookup_dmap ;
          apply srel.
    - intros σ x1 x2 r.
      apply (IHct (ConsSubst (MkSRelVal c1 x1 x2 r) σ)).
    - intros σ; destruct c ; destruct H ; apply IHct1; apply IHct2.
  Qed.

End ICTermToSRel.

(** Functional interpretation of terms
    (in the special case where our types are covariant) *)

Section ICTermToFunction.
  Context (M1 M2 : OrderedMonad).
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

End AlgStruct.

Section SubstitutionOrder.
  Context (M:OrderedMonad) A (rel : srelation A) `{PreOrder A rel}.

  Definition ordered_monad_lift_rel : srelation (M A) :=
    fun m1 m2 => forall (R : srelation (M A)),
        (forall a1 a2, rel a1 a2 -> R (ret a1) (ret a2)) ->
        (forall m1 m2, omon_rel m1 m2 -> R m1 m2) ->
        (forall X (m : M X) (f1 f2 : X -> M A),
            (forall x, R (f1 x) (f2 x)) -> R (bind m f1) (bind m f2)) ->
        R m1 m2.

  Lemma rel_to_lift_rel : forall a a', rel a a' -> ordered_monad_lift_rel (ret a) (ret a').
  Proof. intros ? ? Ha R Hret ? ? ; apply (Hret _ _ Ha). Qed.

  Lemma omon_ord_to_lift_rel : forall m m', omon_rel m m' -> ordered_monad_lift_rel m m'.
  Proof. intros ? ? Hm R ? Hord ? ; apply (Hord _ _ Hm). Qed.

  (** TODO : Is this relation a preorder ? it's reflexive but it's not clear to me that it's transitive... what should be its status, apart from making the proofs go through ? *)
  
  (* Global Instance ordered_monad_lift_preorder : PreOrder ordered_monad_lift_rel. *)
  (* Proof. *)
  (*   constructor. *)
  (*   intros x R Hret Hord Hbind. *)
  (*   pose proof (Hbind A x ret ret (fun x => Hret x x ltac:(reflexivity))). *)
  (*   cbv in H0 ; rewrite !monad_law2 in H0 ; assumption. *)
  (*   intros x y z Hxy Hyz R Hret Hord Hbind. *)
  (*   epose proof (Hbind A x ret ret (fun x => Hret x x ltac:(reflexivity))). *)
  (*   pose (R' := fun m1 m2 => ordered_monad_lift_rel m2 z -> R m1 z). *)
  (*   specialize (Hxy R'). apply Hxy. *)
  (*   red. *)
End SubstitutionOrder.

Section OrderedAlgStruct.
  Context (M:OrderedMonad).

  Record OrdAlgStruct A :=
    mkOAlgStruct
      { oalgstr_alg :> AlgStruct M A
      ; oalgstr_rel : srelation A
      ; oalgstr_preord : PreOrder oalgstr_rel
      ; oalgstr_mon : forall m m',
          ordered_monad_lift_rel M A oalgstr_rel m m' ->
          oalgstr_rel (oalgstr_alg m) (oalgstr_alg m')
      }.

  Global Existing Instance oalgstr_preord.
End OrderedAlgStruct.

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
  
End FreeAlgStruct.

Section FreeOAlgStruct.
  Context (M:OrderedMonad).

  Program Definition freeOAlgStruct A : OrdAlgStruct M (M A) :=
    mkOAlgStruct M (M A) (freeAlgStruct M A) (@omon_rel M _) _ _.
  (* Next Obligation. apply omon_bind. assumption. intros ; reflexivity. Qed. *)
  Next Obligation.
    apply H.
    intros ; cbv ; rewrite !monad_law1 ; assumption.
    intros. apply omon_bind. assumption. intros ; sreflexivity.
    intros. cbv ; rewrite !monad_law3. apply omon_bind. sreflexivity.
    red=> ?; apply H0.
  Qed.

End FreeOAlgStruct.

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
End NProductAlgStruct.

Section MapMonotone.
  Context (M:OrderedMonad) {A B} (f: A -> B).
  Lemma map_monotone : forall m m', omon_rel m m' -> @omon_rel M _ (f <$> m) (f <$> m').
  Proof.
    intros ? ? H ; cbv ; apply omon_bind. assumption. intros ; sreflexivity.
  Qed.

  Context relA relB `{PreOrder A relA} `{PreOrder B relB}.
  Context (f_mon : forall (a a' : A), relA a a' -> relB (f a) (f a')).

  Lemma map_lift_monotone : forall m m',
      ordered_monad_lift_rel M A relA m m' ->
      ordered_monad_lift_rel M B relB (f <$> m) (f <$> m').
  Proof.
    intros m m' Hm R Hret Hord Hbind ; apply Hm.
    cbv. intros ; rewrite !monad_law1. apply Hret. apply f_mon. assumption.
    intros ; apply Hord ; apply map_monotone ; assumption.
    intros ; cbv. rewrite !monad_law3. apply Hbind.
    exact H1.
  Qed.
End MapMonotone.

Section NProductOAlgStruct.
  Context M A B (HA : OrdAlgStruct M A) (HB : OrdAlgStruct M B).

  Import SPropNotations.
  Program Definition nprodOAlgStruct : OrdAlgStruct M (A × B) :=
    @mkOAlgStruct _ _ (nprodAlgStruct M A B HA HB)
                  (fun p p' => oalgstr_rel _ _ HA (nfst p) (nfst p')
                            s/\ oalgstr_rel _ _ HB (nsnd p) (nsnd p'))
                  _ _.
  Next Obligation.
    constructor. split ; sreflexivity.
    intros ? ? ? [? ?] [? ?] ; split ; estransitivity ; eassumption.
  Qed.
  Next Obligation.
    split ; apply oalgstr_mon;
      (eapply (map_lift_monotone M); [|exact H] ; intuition).
  Qed.

End NProductOAlgStruct.

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

End DependentProductAlgebra.

Section PointwiseProductMonotone.
  Context (M:OrderedMonad) A B (HB : forall a:A, OrdAlgStruct M (B a)).

  Program Definition DepProdOAlgPointwise : OrdAlgStruct M (forall a, B a) :=
    mkOAlgStruct M _ (DepProdAlg M A B (fun a => HB a))
                 (fun f1 f2 => forall a, oalgstr_rel M _ (HB a) (f1 a) (f2 a)) _ _.
  Next Obligation.
    constructor.
    intros ? ? ; sreflexivity.
    intros ? ? ? ? ? ? ; estransitivity ; eauto.
  Qed.
  Next Obligation.
    apply H.
    intros ; cbv ; rewrite !monad_law1. rewrite !algstr_ret. auto.
    intros. apply oalgstr_mon. intros ? ? Hord ? ; apply Hord.
    apply omon_bind. assumption. intros ; sreflexivity.

    intros.  unfold bind ; rewrite !monad_law3.
    match goal with
    | [|- oalgstr_rel _ _ _ _ (_ _ (_ _ _ _ _ ?t))] =>
      rewrite <- (algstr_bind _ _ _ _ _ t)
    end.
    rewrite <- algstr_bind.
    apply oalgstr_mon.
    intros ? Hret Hord Hbind. apply Hbind. intros; apply Hret.
    apply H0.
    Qed.
End PointwiseProductMonotone.

Section MonotonicProductAlgebra.
  Context (M:OrderedMonad) A B
          relA `{PreOrder A relA}
          relB `{PreOrder B relB}
          (* (HA : OrdAlgStruct M A) *) (HB : OrdAlgStruct M B) (HrelB : oalgstr_rel _ _ HB = relB).

  Import FunctionalExtensionality.
  Import SPropNotations.
  Let mon_prod := {f : A -> B ≫ forall a a', relA a a' -> relB (f a) (f a') }.
  Program Definition MonProdAlg : AlgStruct M mon_prod :=
    mkAlgStruct _ _ (fun m => Sexists _ (fun (a:A) => HB ((fun f => Spr1 f a) <$> m)) _) _ _.
  Next Obligation.
    apply oalgstr_mon. rewrite /map => ? Hret Hord Hbind.
    apply Hbind. intros. apply Hret. apply (Spr2 x). assumption.
  Qed.
  Next Obligation.
    apply Ssig_eq ; simpl ; extensionality x.
    cbv ; rewrite monad_law1. rewrite algstr_ret. reflexivity.
  Qed.
  Next Obligation.
    apply Ssig_eq ; simpl ; extensionality a.
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

  Program Definition MonProdOAlg : OrdAlgStruct M mon_prod :=
    mkOAlgStruct _ _ MonProdAlg
                 (fun f1 f2 => forall a, oalgstr_rel M _ HB (Spr1 f1 a) (Spr1 f2 a)) _ _.
  Next Obligation.
    constructor. intros ? ? ; sreflexivity. intros ? ? ? ? ? ? ; estransitivity ; eauto.
  Qed.
  Next Obligation.
    apply H1.
    intros ; cbv ; rewrite !monad_law1. rewrite !algstr_ret. auto.
    intros. apply oalgstr_mon. intros ? ? Hord ? ; apply Hord.
    apply omon_bind. assumption. intros ; sreflexivity.

    intros. rewrite /map /bind !monad_law3.
    match goal with
    | [|- oalgstr_rel _ _ _ _ (_ _ (_ _ _ _ _ ?t))] =>
      rewrite <- (algstr_bind _ _ _ _ _ t)
    end.
    rewrite <- algstr_bind.
    apply oalgstr_mon.
    intros ? Hret Hord Hbind. apply Hbind. intros; apply Hret.
    apply H2.
    Qed.

End MonotonicProductAlgebra.

(** Algebra structure on the denotation *)

Section ToAlgebra.
  Context (M:OrderedMonad) (c : ctype).

  Import FunctionalExtensionality.
  Import SPropNotations.
  Definition ctype_alg : { alg : OrdAlgStruct M ⦑c|M⦒
                         ∥ oalgstr_rel _ _ alg = to_ord M c}.
  Proof.
    induction c as [A| c1 IHc1 c2 IHc2 | |] ; simple refine (subt _ _ _ _).
    apply freeOAlgStruct.
    cbv ; reflexivity.
    apply (nprodOAlgStruct _ _ _ (wit IHc1) (wit IHc2)).
    simpl ; extensionality p ; extensionality p'.
    rewrite (pf IHc1) (pf IHc2). cbv ; reflexivity.
    apply (DepProdOAlgPointwise _ _ _ (fun a => wit (X a))).
    simpl ; extensionality f1 ; extensionality f2.
    apply SPropAxioms.sprop_ext ; do 2 constructor ;
      intros ; (rewrite (pf (X a)) + rewrite -(pf (X a))) ; auto.
    (* unfold to_type in * . unfold to_ord in *. *)
    simpl.
    apply (MonProdOAlg _ _ _ (to_ord M c0_1) (to_ord M c0_2) (wit IHc0_2)).
    apply (pf (IHc0_2)).
    simpl.
    extensionality f1 ; extensionality f2.
    (* ; extensionality a. *)
    (* unfold to_ord. *) simpl.
    apply SPropAxioms.sprop_ext ; do 2 constructor; move=> H x.
    specialize (H x); rewrite (pf (IHc0_2)) in H; apply H.
    rewrite (pf (IHc0_2)) ; apply H. 
  Defined.

End ToAlgebra.



