From Coq Require Import List.
From SM Require Export SMSyntax.
From SM Require Import TypeCatSpecialized MonadicStructures.
From Equations Require Equations.

Notation "A × B" := (CCC.npair A B) (at level 80) : type_scope.



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


(** Denotation of terms (discrete order case) *)

Section ICTermToTerm.
  Context (M:Type -> Type).
  Context `{KleisliMonad M}. 

  Definition icterm_to_term {Γ c} (ct : icterm Γ c) :
    substitution (to_type M) Γ -> ⦑ c |M⦒.
  Proof.
    induction ct ; intro σ.
    exact (@Monad.ret Type_Cat M _ A).
    exact (@Monad.bind Type_Cat M _ A B (IHct1 σ) (IHct2 σ)). 
    exact (CCC.Build_npair _ _ (IHct1 σ) (IHct2 σ)).
    destruct c ; inversion H ; exact (CCC.nfst (IHct σ)).
    destruct c ; inversion H ; exact (CCC.nsnd (IHct σ)).
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
  Context (M:Type -> Type).
  Context `{KleisliMonad M}. 

  Lemma map_subst_comp : forall {Γ var1 var2 var3} (σ : substitution var1 Γ) (f : forall c, var1 c -> var2 c) (g: forall c, var2 c -> var3 c),
      map_subst g (map_subst f σ) = map_subst (fun c x => g c (f c x)) σ.
  Proof. admit. Admitted.

  Lemma to_term_weaken {Γ c} (t:icterm Γ c) :
    forall c0 (x:⦑c0|M⦒) (σ : substitution (to_type M) Γ),
      ⦑ weaken c0 c t | ConsSubst x σ |M⦒ = ⦑ t |σ  |M⦒.
  Proof. admit. Admitted.

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
    rewrite Substitution.dlookup_dmap ; reflexivity.
    extensionality x; rewrite IHt; simpl;
      rewrite map_subst_comp; unfold ConsSubst; do 3 f_equal;
        extensionality c; extensionality m; rewrite to_term_weaken; reflexivity.
    destruct c ; destruct H ; rewrite IHt1; rewrite IHt2; reflexivity.
  Qed.

End ICTermToTermSubst.


(** Denotation preserves the equational theory *)

Section ICeqToEq.
  Import DepElim.
  Context (M:Type -> Type) `{KleisliMonad M}.

  Let var_eq c := {p:⦑c |M⦒ × ⦑c|M⦒ ⫳ CCC.nfst p = CCC.nsnd p}.
  Let efst c (m:var_eq c) := CCC.nfst (dfst m).
  Let esnd c (m:var_eq c) := CCC.nsnd (dfst m).
  (* Let eeq c (m:var_eq c) := dsnd m. *)

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

  Lemma map_subst_id Γ :
    forall σ, map_subst (fun c m => @icterm_to_term M _ Γ c m σ) (id_isubst Γ) = σ.
  Proof.
    induction Γ as [| ? ? IH]; intros σ ; dependent destruction σ.
    reflexivity.
    simpl ; f_equal ; rewrite (map_subst_comp M) ;
      replace (fun c x => _) with (fun c m => @icterm_to_term M _ Γ c m σ).
    apply IH.
    extensionality c0 ; extensionality m ; rewrite to_term_weaken ; reflexivity.
  Qed.

  Definition iceq_to_eq {Γ c} {ct1 ct2 : icterm Γ c} (Heq : ct1 ≅ ct2) :
    forall (σ : substitution var_eq Γ),
      ⦑ct1 | map_subst efst σ |M⦒ = ⦑ ct2 | map_subst esnd σ |M⦒.
  Proof.
    induction Heq ; simpl ; intros σ.
    rewrite unitl ; rewrite icterm_diagonal ; reflexivity.
    rewrite unitr ; rewrite icterm_diagonal ; reflexivity.
    rewrite assoc ; rewrite 3!icterm_diagonal ; reflexivity.
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


(** Compatibility of the special case to the general case *)

Section ToRelToFunction.
  Context (M1 M2 : Type -> Type).
  Context (θ : forall A, M1 A -> M2 A).

  Let R := fun A (m1: M1 A) (m2 : M2 A) => θ A m1 = m2.

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
  Context (M1 M2 : Type -> Type) `{KleisliMonad M1} `{KleisliMonad M2}.
  Context (R : forall A, M1 A -> M2 A -> Prop).
  Context (Runit : forall A (x:A), R A (ret x) (ret x)).
  Context (Rbind : forall A B (m1 : M1 A) (m2 : M2 A) (f1 : A -> M1 B) (f2 : A -> M2 B), R A m1 m2 -> (forall x:A, R B (f1 x) (f2 x)) -> R B (bind f1 m1) (bind f2 m2)).

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
    - intro σ; destruct c ; destruct H ; exact (CCC.nfst (IHct σ)).
    - intro σ; destruct c ; destruct H ; exact (CCC.nsnd (IHct σ)).
    - intros σ x ; apply (X x).
    - intro σ.
      destruct c ; destruct H ; apply (IHct σ).
    - intros σ ;
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
  Context (M1 M2 : Type -> Type) `{KleisliMonad M1} `{KleisliMonad M2}.
  Context (F : forall A, M1 A -> M2 A).
  Context (Funit : forall A (x:A), F A (ret x) = (ret x)).
  Context (Fbind : forall A B (m : M1 A) (f : A -> M1 B),
              F B (bind f m) = bind (fun x => F B (f x)) (F A m)).

  Let R := fun A (m1 : M1 A) (m2: M2 A) => F A m1 = m2.
  Let MF := to_function M1 M2 F.
  Let val_cov (c:ctype) :=to_type M1 c × covariant c.

  Definition val_cov_to_rel_val (c:ctype) (p : val_cov c) : rel_val M1 M2 R c
    := MkRelVal M1 M2 R c (CCC.nfst p) (MF c (CCC.nsnd p) (CCC.nfst p))
                (to_function_to_rel M1 M2 F c (CCC.nsnd p) _ _ eq_refl).

  Program Definition icterm_to_fun_witness {Γ c} (ct:icterm Γ c) (Hcov : covariant c)  :=
    fun (σ : substitution val_cov Γ) =>
      let ρ := map_subst val_cov_to_rel_val σ in
      to_rel_to_function M1 M2 F c Hcov _ _ (icterm_to_rel_witness M1 M2 R (Funit) _ ct ρ).
  Next Obligation.
    rewrite <- H.
    assert ((fun x => F _ (f1 x)) = f2) as <- by (extensionality x ; apply H0).
    apply Fbind.
  Qed.

  Eval cbn in icterm_to_fun_witness.

  (* TODO : give the following type to icterm_to_fun_witness *)
    (* forall (σ : substitution val_cov Γ), *)
    (*   MF c Hcov ⦑ ct [map_subst (fun c => CCC.nfst) σ] |M1⦒ = *)
    (*   ⦑ ct [map_subst (fun c p => MF c (CCC.nsnd p) (CCC.nfst p)) σ] |M2⦒. *)

End ICTermToFunction.



(******************************************************************************)
(**                                                                           *)
(**              Algebra structure on the denotation                          *)
(**                                                                           *)
(******************************************************************************)

(** Special case for the algebra structure on the dependent product
    that was not given in general *)

Section DependentProductAlgebra.
  Import Essentials.Notations.
  Import Functor.Main.
  Context (T:(Type_Cat –≻ Type_Cat)%functor) `{@Monad _ T}.
  Context (A:Type) (B : A -> Type) (Halg:forall x:A, AlgStruct T (B x)).

  Definition eval {A B} (x:A) (f : forall x:A, B x) : B x := f x.

  Program Definition DepProdAlg : AlgStruct T (forall x:A, B x) :=
    {|
      Algebra.alg_structure m x :=
        alg_struct (Halg x) (T _a (eval x) m)%morphism
    |}.
  Next Obligation.
    extensionality f ; extensionality x.
    rewrite <- (natural η).
    rewrite alg_unit.
    reflexivity.
  Qed.

  Next Obligation.
    extensionality f ; extensionality x ; simpl.
    rewrite <- (natural μ).
    rewrite alg_mult.
    cbn.
    rewrite <- !(TypeCatSpecialized.F_compose T).
    reflexivity.
  Qed.

End DependentProductAlgebra.

(** Special case for the sub-algebra structure
    that was not given in general -- Not used *)

From Coq.Logic Require EqdepFacts.
Section SubAlgebra.
  Import CategoryBasics.
  Import EqdepFacts.
  Context (T:(Type_Cat –≻ Type_Cat)%functor) `{@Monad _ T}.
  Context (A : Algebra.Algebra T).
  Context (p : projT1 A -> Type).
  Context (p_hprop : forall x, forall h1 h2 : p x, h1 = h2).

  Let Ap := {x : projT1 A ⫳ p x}.
  Context (p_stable : forall m, p (alg_struct (projT2 A) (T _a (@dfst _ p) m)%morphism)).
  Program Definition SubAlg : AlgStruct T Ap :=
    {|
      Algebra.alg_structure m := {| dfst := alg_struct (projT2 A) (T _a (@dfst _ p) m)%morphism |}
    |}.
  Next Obligation.
    extensionality x.
    unshelve eapply eq_eq_above_eq_nsigT.
    simpl.
    rewrite <- natural.
    erewrite alg_unit.
    reflexivity.
    apply p_hprop.
  Qed.

  Next Obligation.
    extensionality x.
    unshelve eapply eq_eq_above_eq_nsigT; simpl.
    rewrite <- TypeCatSpecialized.F_compose.
    simpl.
    replace ((T _a)%morphism
       (fun x0 : (T _o)%object Ap =>
          alg_structure _ _ (projT2 A) ((T _a)%morphism dfst x0)) x) with
        ((T _a)%morphism (alg_structure _ _ (projT2 A))
               ((T _a)%morphism (((T _a)%morphism dfst)) x)) by
        (rewrite <- TypeCatSpecialized.F_compose ; reflexivity).
    rewrite <- alg_mult.
    rewrite <- natural.
    reflexivity.
    apply p_hprop.
  Qed.

End SubAlgebra.



(** Algebra structure on the denotation *)

Section ToAlgebra.
  Context (M : Type -> Type).
  Context `{KleisliMonad M}.
  Context (c : ctype).

  Import CategoryBasics.
  Definition ctype_alg : AlgStruct (TF M) ⦑ c  |M⦒.
  Proof.
    induction c as [A| c1 IHc1 c2 IHc2 | |].
    exact (projT2 (@FO _ (AlgebraCat _) (FreeAlgebra (TF M)) A)).
    set (A1 := (existT _ ⦑ c1 |M⦒ IHc1)).
    set (A2 := (existT _ ⦑ c2 |M⦒ IHc2)).
    set (A := (AlgebraCat_product (@TF Type_Cat M _) A1 A2)).
    exact (projT2 (A : AlgebraCat (TF M))).
    apply (DepProdAlg _ _ (fun x => ⦑ _ x | M⦒)); intros ? ; auto.
    apply (DepProdAlg _ ⦑ c0_1 |M⦒ (fun _ => ⦑ c0_2 | M⦒)); intros ? ; auto.
  Defined.

End ToAlgebra.



(******************************************************************************)
(**                                                                           *)
(**              Linear types and linear typing of SM terms                   *)
(**                                                                           *)
(******************************************************************************)



Definition linear_decoration : ctype -> Type  :=
  fix deco (c : ctype) {struct c} :=
    match c with
    | CM _ => unit
    | CProd c1 c2 => deco c1 × deco c2
    | CArr c => forall x, deco (c x)
    | CArrC c1 c2 => option (deco c1 × deco c2)
    end.

Fixpoint trivial_decoration (c:ctype) {struct c} : linear_decoration c :=
  match c with
  | CM A => tt
  | c1 ⨰ c2 => ⟨trivial_decoration c1, trivial_decoration c2⟩
  | CArr c => fun x => trivial_decoration (c x)
  | CArrC c1 c2 => Some ⟨trivial_decoration c1, trivial_decoration c2⟩
  end.

Definition dtype := { c : ctype ⫳ linear_decoration c }.
Definition to_ctx (Γ : list dtype) : ctx := List.map dfst Γ.

Definition prodDecoProj1 {c:ctype} :
  forall H:isProd c, linear_decoration c -> linear_decoration (prodProj1 H).
Proof.
  destruct c ; intros [] d ; exact (nfst d).
Defined.

Definition prodDecoProj2 {c:ctype} :
  forall H:isProd c, linear_decoration c -> linear_decoration (prodProj2 H).
Proof.
  destruct c ; intros [] d ; exact (nsnd d).
Defined.

Definition arrDecoCod {c:ctype} :
  forall H:isArr c, linear_decoration c -> (forall v:arrDom H, linear_decoration (arrCod H v)). 
Proof.
  destruct c ; intros [] d v ; exact (d v).
Defined.

Definition arrCLinear {c:ctype} : forall H :isArrC c, linear_decoration c -> bool.
Proof. destruct c ; intros [] [[]|]; [exact false | exact true]. Defined.

Definition arrCDecoCod {c:ctype} : forall H :isArrC c, linear_decoration c -> linear_decoration (arrCCod H). 
Proof. destruct c ; intros [] [[? d2]|] ; [exact d2 | apply trivial_decoration ]. Defined.

Definition arrCDecoDom {c:ctype} : forall H:isArrC c, linear_decoration c -> linear_decoration (arrCDom H).
Proof. destruct c ; intros [] [[d1]|] ; [exact d1 | apply trivial_decoration]. Defined.

Section ToLinearType.
  Context (M : Type -> Type) `{KleisliMonad M}.

  Definition to_linear_type (c:ctype) : linear_decoration c -> Type. 
  Proof.
    induction c as [A | c1 X1 c2 X2 | A c X | c1 X1 c2 X2].
    intros ; exact ⦑ CM A | M ⦒.
    intros [d1 d2]. exact (X1 d1 × X2 d2).
    intros d ; exact (forall x, X x (d x)).
    intros [[d1 d2]|]. exact (X1 d1 -> X2 d2).
    Import MonadNotations.
    exact { f : ⦑ c1 | M ⦒ -> ⦑ c2 | M ⦒ ∥ forall m, f (alg_struct (ctype_alg M c1) m)= alg_struct (ctype_alg M c2) (f <$> m) }. 
  Defined.

  (* If only we could bypass extensionality, it would compute... *)
  Lemma to_linear_type_trivial_decoration (c:ctype) :
    to_linear_type c (trivial_decoration c) = ⦑ c |M⦒. 
  Proof.
    induction c.
    reflexivity.
    simpl; rewrite IHc1 ; rewrite IHc2 ; reflexivity.
    simpl ; extensionality x ; apply H.
    simpl ; rewrite IHc1 ; rewrite IHc2 ; reflexivity.
  Defined.

  (* Since the equality relies on funext, let's try to provide a bijection that do not depend on it *)
  Fixpoint lt_triv_dec_to_type (c:ctype) : to_linear_type c (trivial_decoration c) -> ⦑ c | M ⦒
  with to_type_lt_triv_dec (c:ctype) : ⦑ c | M⦒ -> to_linear_type c (trivial_decoration c).
  Proof.
    all: destruct c ; simpl ; try trivial.
    1,4:intros [d1 d2] ; split ; auto.
    all: intros f x ; auto.
  Defined.

  Lemma bij1 : forall c x, lt_triv_dec_to_type c (to_type_lt_triv_dec c x) = x.
  Proof.
    induction c ; simpl ; intros ; auto.
    destruct x ; f_equal ; auto.
    extensionality x0; rewrite IHc1; rewrite IHc2 ; reflexivity.
  Qed.

  Lemma bij2: forall c x, to_type_lt_triv_dec c (lt_triv_dec_to_type c x) = x.
  Proof.
    induction c ; simpl ; intros ; auto.
    destruct x ; f_equal ; auto.
    extensionality x0; rewrite IHc1; rewrite IHc2 ; reflexivity.
  Qed.

End ToLinearType.



(* Proof that a variable is not used in a term *)

Fixpoint is_weakened {Γ c} (ct : icterm Γ c) : nat -> Type.
Proof.
  destruct ct ; intro i0.
  exact True.
  exact (is_weakened _ _ ct1 i0 × is_weakened _ _ ct2 i0).
  exact (is_weakened _ _ ct1 i0 × is_weakened _ _ ct2 i0).
  exact (is_weakened _ _ ct i0).
  exact (is_weakened _ _ ct i0).
  exact (forall x, is_weakened _ _ (i x) i0).
  exact (is_weakened _ _ ct i0).
  exact (i0 <> n).
  exact (is_weakened _ _ ct (S i0)).
  exact (is_weakened _ _ ct1 i0 × is_weakened _ _ ct2 i0).
Defined.

Section LinearTyping.
  (** Linear typing derivations should denote homomorphisms between the algebra
  designated by the index in the stoup and the type of the term *)
  (* For this to be reasonable, when there is an index in the stoup, the
  decoration of the type designated by the stoup and the type of the term need
  to have an algebra structure, i.e. a trivial linear decoration... When the
  stoup is empty however, the type of the term might have a non-trivial
  decoration *)
  Reserved Notation "[ dΓ | xopt ⊢ ct :: c | d ]" (at level 30, ct at next level, c at next level).

  Inductive linear_typing :
    forall (dΓ : list dtype) (c : ctype) (d : linear_decoration c),
      option nat -> icterm (to_ctx dΓ) c -> Type :=

  | LTRet : forall dΓ A,
      [dΓ | None ⊢ IMRet A :: A ~> CM A | fun _ => tt]

  | LTBind : forall dΓ A B f m iopt,
      (match iopt with None => True | Some i => is_weakened f i end) ->
      [dΓ | None ⊢ f :: A ~> CM B | fun _ => tt ] ->
      [dΓ | iopt ⊢ m :: CM A | tt ] ->
      [dΓ | iopt ⊢ IMBind f m :: CM B | tt ]

  | LTPair : forall dΓ c1 c2 d1 d2 ct1 ct2 iopt, 
      [dΓ | iopt ⊢ ct1 :: c1 | d1] ->
      [dΓ | iopt ⊢ ct2 :: c2 | d2] ->
      [dΓ | iopt ⊢ IPair ct1 ct2 :: c1 ⨰ c2 | ⟨ d1, d2⟩ ]

  | LTProj1 : forall dΓ c H d ct iopt,
      [dΓ | iopt ⊢ ct :: c | d ] ->
      [dΓ | iopt ⊢ IProj1 H ct :: prodProj1 H | prodDecoProj1 H d ]

  | LTProj2 : forall dΓ c H d ct iopt,
      [dΓ | iopt ⊢ ct :: c | d ] ->
      [dΓ | iopt ⊢ IProj2 H ct :: prodProj2 H | prodDecoProj2 H d ]

  | LTAbs : forall dΓ A c d ct iopt,
      (forall x:A, [dΓ | iopt ⊢ ct x :: c x | d x]) ->
      [dΓ | iopt ⊢ IAbs ct :: CArr c | d]

  | LTApp : forall dΓ c H d ct iopt v,
      [dΓ | iopt ⊢ ct :: c | d] ->
      [dΓ | iopt ⊢ IApp H v ct :: arrCod H v | arrDecoCod H d v]

  | LTCVarLinear : forall dΓ i H d, 
      [dΓ | Some i ⊢ ICVar i H :: lookup H | d]

  | LTCVarNonLinear : forall dΓ i H d, 
      [dΓ | None ⊢ ICVar i H :: lookup H | d]

  | LTCAbsIntroLinear : forall dΓ c1 c2 ct,
      [(dpair _ c1 (trivial_decoration c1)) :: dΓ | Some 0 ⊢ ct :: c2 | trivial_decoration c2] ->
      [dΓ | None ⊢ ICAbs ct :: c1 ~~> c2 | None ]

  | LTCAbs : forall dΓ c1 c2 d1 d2 ct iopt,
      [(dpair _ c1 d1) :: dΓ | iopt ⊢ ct :: c2 | d2] ->
      [dΓ | iopt ⊢ ICAbs ct :: c1 ~~> c2 | Some ⟨d1, d2⟩ ]

  | LTCAppNone : forall dΓ c H d ct1 ct2,
      [dΓ | None ⊢ ct1 :: c | d] ->
      [dΓ | None ⊢ ct2 :: arrCDom H | arrCDecoDom H d] ->
      [dΓ | None ⊢ ICApp H ct1 ct2 :: arrCCod H | arrCDecoCod H d]

  | LTCAppArg : forall dΓ c H d ct1 ct2 i,
      is_weakened ct1 i ->
      arrCLinear H d = true ->
      [dΓ | None ⊢ ct1 :: c | d] ->
      [dΓ | Some i ⊢ ct2 :: arrCDom H | arrCDecoDom H d] ->
      [dΓ | Some i ⊢ ICApp H ct1 ct2 :: arrCCod H | arrCDecoCod H d]

  | LTCAppFun : forall dΓ c H d ct1 ct2 i,
      [dΓ | Some i ⊢ ct1 :: c | d] ->
      is_weakened ct2 i ->
      [dΓ | None ⊢ ct2 :: arrCDom H | arrCDecoDom H d] ->
      [dΓ | Some i ⊢ ICApp H ct1 ct2 :: arrCCod H | arrCDecoCod H d]
  where "[ dΓ | xopt ⊢ ct :: c | d ]" := (linear_typing dΓ c d xopt ct).
End LinearTyping.

Require SM.dlist.
(* TODO : maybe set it in dlist *)
Unset Universe Polymorphism.
Module LinCtx  <: SM.dlist.Ctx.
  Definition A := dtype.
End LinCtx.
Set Universe Polymorphism.

Module LinSubst := SM.dlist.DList LinCtx.

Section ICTermToHomomorphism.
  Notation "[ dΓ | xopt ⊢ ct :: c | d ]" := (linear_typing dΓ c d xopt ct)
                                              (at level 30, dΓ at next level, ct at next level, c at next level) .
  Import MonadNotations.
  Import Equations.
  Context (M:Type -> Type) `{KleisliMonad M}.
  Context {c2 : ctype} (d2 : linear_decoration c2).


  Notation μ := (Monad.bind _ (M _) _ (fun x => x)).
  Ltac intro_map :=
    change (bind (fun x => ret (?f x)) ?a) with (f <$> a).

  Definition homomorphism c1 c2 (f : ⦑c1|M⦒ -> ⦑c2|M⦒) :=
      let α1 := alg_struct (ctype_alg M c1) in
      let α2 := alg_struct (ctype_alg M c2) in
      forall m, f (α1 m) = α2 (f <$> m).

  Let lsubst dΓ := LinSubst.dlist (fun d => to_linear_type M (dfst d) (dsnd d)) dΓ.

  Definition to_homomorphism_statement
             dΓ c d ct iopt (Hlin : [dΓ | iopt ⊢ ct :: c | d])
            : Type := 
    match iopt with
    | None => lsubst dΓ -> to_linear_type M c d
    | Some i => lsubst (LinSubst.remove dΓ i) ->
               forall H:in_ctx i (to_ctx dΓ),
                 let c1 := lookup H in 
                 { f : ⦑c1|M⦒ -> ⦑c|M⦒ ∥ homomorphism c1 c f }
    end.
End ICTermToHomomorphism.




(** Showing that state satisfy the linearity criterion *)

From SM Require Import SMExamplesGenerated.

Section ICMonadmap.
  Context (c:icmonad).
  Import ListNotations.
  Definition icMap A B (f:A -> B) : icterm [icM c A] (icM c B) :=
    ICApp isArrCPf (ICApp isArrCPf (weaken _ _ (icBind c A B))
                 (@ICVar [icM c A] 0 (inhabit_infer 0 [_])))
          (weaken _ _ (IAbs (fun x : A => IApp isArrPf (f x) (icRet c B)))).

End ICMonadmap.


Section TestExample.
  Notation "[ dΓ | xopt ⊢ ct :: c | d ]" := (linear_typing dΓ c d xopt ct)
                                              (at level 30, dΓ at next level, ct at next level, c at next level) .
  Context (S A B : Type) (f : A -> B).
  Let stm := st_icmonad S.
  Let M := icM stm.
  Let SM {A:Type} : linear_decoration (M A) := fun _ => tt.
  Transparent weaken0.
  Definition ct0 := Eval cbv in (icMap stm A B f).
  Transparent Substitution.dlookup.
  Transparent Substitution.dmap.
  Definition ct := Eval compute in icterm_eval 10 ct0.

  Ltac linear_capp_arg :=
    match goal with
    | [ |- [ ?Γ | Some ?i ⊢ ICApp _ ?ct1 ?ct2 :: ?C2 | ?d2]] =>
      unshelve eapply (LTCAppArg Γ (_ ~~> C2) I None ct1 ct2 i) ;
      [try (cbv ; intuition) | try reflexivity | ..]
    end.

  Ltac linear_capp_none :=
    match goal with
    | [ |- [ ?Γ | None ⊢ ICApp _ ?ct1 ?ct2 :: ?C2 | ?d2]] =>
      unshelve eapply (LTCAppNone Γ (_ ~~> C2) I (Some ⟨ _ , d2⟩) ct1 ct2)
      (* ; *)
      (* [ try (cbv ; intuition) | try reflexivity | ..] *)
    end.


  Ltac linear_cvar :=
    match goal with
    | [ |- [ ?Γ | None ⊢ ICVar ?n ?H :: _ | _]] =>
      eapply (LTCVarNonLinear Γ n H)
    | [ |- [ ?Γ | Some ?n ⊢ ICVar ?n ?H :: _ | _]] =>
      eapply (LTCVarLinear Γ n H)
    end.

  Ltac linear_app :=
    match goal with
    | [ |- [ ?Γ | ?iopt ⊢ IApp _ ?v ?ct :: ?C | ?d]] =>
      eapply (LTApp Γ (_ ~> C) I (fun _ => d) ct iopt  v)
    end.


  (* Actually it is enough to show that bind has type
     (A ~> M B) ~~> (M A -o M B)
   *)

  Goal [dpair _ (M A) SM :: nil | Some 0 ⊢ ct (* icMap stm A B f *) :: M B | SM ].
  Proof.
    unfold ct.
    econstructor.
    intros x.
    linear_capp_arg. 
    linear_capp_none. exact (fun _ => tt).
    econstructor.
    econstructor.
    econstructor.
    cbv ; intuition.
    linear_cvar.
    linear_cvar.
    econstructor; intros.
    linear_app.
    linear_app.
    econstructor; intros.
    linear_app.
    econstructor; intros.
    econstructor; intros.
    linear_app.
    econstructor; intros.
    linear_app.
    linear_cvar.
  Defined.
    
End TestExample.






















