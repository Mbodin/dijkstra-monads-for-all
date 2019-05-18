From Coq Require Import List ssreflect.
From Mon Require Import Base.
From Mon.sprop Require Import SPropBase.
From Mon.SM Require Import dlist.
From Equations Require Import Equations.


(**************************************************************************)
(*               Simple types for SM                                      *)
(**************************************************************************)

Inductive ctype : Type :=
| CM : Type -> ctype
| CProd : ctype -> ctype -> ctype
| CArr : forall {A}, (A -> ctype) -> ctype
| CArrC : ctype -> ctype -> ctype
.

Set Universe Polymorphism.


Notation "c1 ⨰ c2" := (CProd c1 c2) (at level 70).
Notation "A ~> c" := (CArr (fun _ : A => c)) (at level 99, right associativity).
Notation "c1 ~~> c2" := (CArrC c1 c2) (at level 99, right associativity).

Definition isProd (c:ctype) : Prop :=
  match c with | _ ⨰ _ => True | _ => False end.
Definition isArr (c:ctype) : Prop :=
  match c with | CArr _ => True | _ => False end.
Definition isArrC (c:ctype) : Prop :=
  match c with | CArrC _ _ => True | _ => False end.

Section CtypeProjectors.
  Ltac arg_false :=
    let H := fresh "H" in
    intro H ; exfalso ; exact H.

  Definition prodProj1 {c:ctype} : isProd c -> ctype.
  Proof.
    destruct c as [| c1 ? | |]. 2:exact (fun _ => c1). all:arg_false.
  Defined.
  Definition prodProj2 {c:ctype} : isProd c -> ctype.
  Proof.
    destruct c as [| ? c2 | |]. 2:exact (fun _ => c2). all:arg_false.
  Defined.

  Definition arrDom {c:ctype} : isArr c -> Type.
  Proof.
    destruct c as [| | A ? |]. 3:exact (fun _ => A). all: arg_false.
  Defined.

  Definition arrCod {c:ctype} : forall (H:isArr c), (arrDom H -> ctype).
  Proof.
    destruct c as [| | ? c |]. 3:exact (fun _ => c). all: arg_false.
  Defined.

  Definition arrCDom {c:ctype} : isArrC c -> ctype.
  Proof.
    destruct c as [| | |c1 ?]. 4:exact (fun _ => c1). all: arg_false.
  Defined.

  Definition arrCCod {c:ctype} : isArrC c -> ctype.
  Proof.
    destruct c as [| | |? c2]. 4:exact (fun _ => c2). all: arg_false.
  Defined.

End CtypeProjectors.

(**************************************************************************)
(*                     PHOAS definition of the term syntax                *)
(**************************************************************************)


Class VarType := var : ctype -> Type.

Section CTerm.
  Context `{VarType}.
  Inductive cterm : ctype -> Type :=
  | MRet : forall A, cterm (A ~> CM A)

  | MBind : forall A B, cterm ((A ~> CM B) ~~> (CM A ~~> CM B))

  | Pair : forall {c1 c2}, cterm (c1 ~~> c2 ~~> c1 ⨰ c2)

  | Proj1 : forall {c1 c2}, cterm(c1 ⨰ c2 ~~> c1)
  | Proj2 : forall {c1 c2}, cterm(c1 ⨰ c2 ~~> c2)

  | Abs : forall A (c:forall x:A, ctype), (forall x:A, cterm (c x)) -> cterm (CArr c)

  | App : forall {A} {c:forall x:A, ctype} (v : A),
      cterm (CArr c) -> cterm (c v)

  | CVar : forall {c:ctype}, var c -> cterm c
  | CAbs : forall (c1:ctype) (c2: ctype),
      (var c1 -> cterm c2) -> cterm (c1 ~~> c2)

  | CApp : forall {c1:ctype} {c2: ctype},
      cterm (c1 ~~> c2) -> cterm c1 ->  cterm c2
  .
End CTerm.

(**************************************************************************)
(*                 Notations for PHOAS                                    *)
(**************************************************************************)

Module SMNotations.
  Notation "λ∘ x : A , t" := (Abs A _ (fun x : A => t))
                                (at level 200, x ident, A at level 200).
  Notation "t @∘ v" := (App v t) (at level 75).
  Notation "λ∙ x : c1 , t" :=
    (CAbs c1 _ (fun z : var c1 => (fun x : cterm c1 => t) (CVar z)))
      (at level 200, x ident, c1 at level 200).

  Notation "t1 @∙ t2" := (CApp t1 t2) (at level 75).

  Notation "≪ t1 , t2 ≫" := (Pair @∙ t1 @∙ t2).
  Notation "'π1' t"  := (Proj1 @∙ t) (at level 99).
  Notation "'π2' t" := (Proj2 @∙ t) (at level 99).

  Section RetBind.
    Context  `{VarType}.

    Definition mret {A:Type} (x:A) := MRet A @∘ x.
    Definition mbind {A B:Type}
              (m:cterm (CM A)) (f : cterm (A ~> CM B)) :=
      MBind A B @∙ f @∙ m.

  End RetBind.

  Notation "x ← m ⊱ t" :=
    (mbind m (λ∘ x : _,  t))
      (at level 20, m at level 100, t at level 200, only parsing).
End SMNotations.


(**************************************************************************)
(*                   Substitutions & lemmas                               *)
(**************************************************************************)

Module CtypeSig <: Ctx.
  Monomorphic Definition A := ctype.
End CtypeSig.

Module Substitution := DList CtypeSig.
(* Set Universe Polymorphism. *)
Definition ctx := list ctype.

Definition substitution (var : VarType) : ctx -> Type := Substitution.dlist var.
Definition NilSubst {var} := @Substitution.dNil var.
Definition ConsSubst {var x xs} y ys := @Substitution.dCons var x xs y ys.

Definition map_subst {var1 var2 : VarType} f {Γ} σ :=
  @Substitution.dmap var1 var2 Γ f σ.

Definition related_substitution {Γ} {var1 var2 : VarType}
         (varR : forall {c}, var1 c -> var2 c -> Type) 
  (ρ : substitution var1 Γ) : substitution var2 Γ ->  Type.
Proof.
  induction ρ.
  intros _ ; exact unit.
  
  intros ρ2.
  dependent elimination ρ2.
  exact ((varR _ y y0) * (IHρ d))%type.
Defined.

Lemma related_substitution_map
      {var1 var2 : VarType} (f : forall c, var1 c -> var2 c) 
      (varR := fun c (x1 : var1 c) (x2: var2 c) => f c x1 = x2)
  : forall Γ (ρ : substitution var1 Γ), related_substitution varR ρ (map_subst f ρ).
Proof.
  intros Γ ρ ; induction ρ.
  constructor.
  cbn. constructor. reflexivity. assumption.
Defined.


Definition valid_term Γ c := forall var, substitution var Γ -> @cterm var c.
Definition closed_cterm (c:ctype) := forall var, @cterm var c.

(**************************************************************************)
(*                   Substituing in PHOAS                                 *)
(**************************************************************************)

Definition flatten {c} `{VarType} : @cterm cterm c -> cterm c. 
Proof.
  induction 1.
  1-7:constructor ; auto.
  exact v.
  (* Set Printing Implicit. *)
  apply CAbs ; intro v ; apply CVar in v;  auto.
  eapply CApp ; eassumption.
Defined.

Definition substitute {c1 c2} (ct1 : forall var, @cterm var c1 -> @cterm var c2)
            (ct2:closed_cterm c1) : closed_cterm c2 :=
  fun var => flatten (ct1 (@cterm var) (ct2 (@cterm var))).

(**************************************************************************)
(*                 Relational & parametricity definitions for PHOAS       *)
(**************************************************************************)

Section CTermRel.
  Context (var1 var2 : VarType) (varR : forall c, var1 c -> var2 c -> Type).
  Import SMNotations.

  Inductive cterm_rel : forall {c}, @cterm var1 c -> @cterm var2 c -> Type :=
  | MRetRel : forall A, cterm_rel (MRet A) (MRet A)
  | MBindRel : forall A B, cterm_rel (MBind A B) (MBind A B)
  | AbsRel : forall {A c ct1 ct2} (cr : forall x:A, @cterm_rel (c x) (ct1 x) (ct2 x)),
      cterm_rel (Abs A c ct1) (Abs A c ct2)
  | AppRel : forall {A c} {ct1 ct2 : cterm (CArr c)} (v:A),
      cterm_rel ct1 ct2 -> cterm_rel (ct1 @∘ v) (ct2 @∘ v)
  | CVarRel : forall {c v1 v2}, varR c v1 v2 -> cterm_rel (CVar v1) (CVar v2)
  | CAbsRel : forall {c1 c2}
                {f1 : var1 c1 -> cterm c2}
                {f2 : var2 c1 -> cterm c2},
                (forall x1 x2, varR c1 x1 x2 -> cterm_rel (f1 x1) (f2 x2)) ->
                cterm_rel (CAbs c1 c2 f1) (CAbs c1 c2 f2)
  | CAppRel : forall {c1 c2} {ct11 ct12 : cterm (c1 ~~> c2)} {ct21 ct22},
      cterm_rel ct11 ct12 -> cterm_rel ct21 ct22 ->
      cterm_rel (ct11 @∙ ct21) (ct12 @∙ ct22).

End CTermRel.

(* This holds meta-theoretically, and we can build a proof of it
   for any instance *)
Definition parametric_closed_cterm {c} (ct : closed_cterm c) :=
  forall (var1 var2 : VarType) (varR : forall {c}, var1 c -> var2 c -> Type),
    cterm_rel var1 var2 (@varR) (ct var1) (ct var2).


Definition parametric_valid_term {Γ c} (ct : valid_term Γ c) :=
  forall (var1 var2 : VarType) (varR : forall {c}, var1 c -> var2 c -> Type)
    (ρ1 : substitution var1 Γ) (ρ2 : substitution var2 Γ),
    related_substitution (@varR) ρ1 ρ2 ->
    cterm_rel var1 var2 (@varR) (ct var1 ρ1) (ct var2 ρ2).

(**************************************************************************)
(*                 Building parametricity witnesses                       *)
(**************************************************************************)

Hint Constructors cterm_rel.

Section BuildParametricityRel.
  Import SMNotations.

  Ltac build_rel :=
    lazymatch goal with
    | [|- cterm_rel _ _ _ (Abs _ _ _) (Abs _ _ _)] => constructor ; intro
    | [|- cterm_rel _ _ _ (CAbs _ _ _) (CAbs _ _ _)] => constructor ; intros
    | [|- cterm_rel ?var1 ?var2 ?varR (?ct1 @∘ ?v) (?ct2 @∘ ?v)] =>
      let H := fresh "H" in
      cut (cterm_rel var1 var2 varR ct1 ct2) ;
        [intros H; apply (AppRel var1 var2 varR v H)|]
    | [|- cterm_rel _ _ _ (CVar _) (CVar _)] => constructor ; assumption
    | [|- cterm_rel _ _ _ _ _] => constructor
    end.

End BuildParametricityRel.


(**************************************************************************)
(*                 DeBruijn term syntax for SM                            *)
(**************************************************************************)


(* Definition in_ctx (n:nat) (Γ : ctx) := n < length Γ. *)
Import SPropNotations.
Definition in_ctx (n:nat) (Γ : ctx) := n  s< length Γ.

Section TyVar.
  Let lookup {Γ n} (H:in_ctx n Γ) := Substitution.lookup H.
  Definition tyvar Γ c := 
    { n : nat ∥ {Hb : Box (in_ctx n Γ) ⫳ lookup (unbox Hb) = c}}.

  Definition mkTyvar {Γ c} n H Heq : tyvar Γ c :=
    subt _ _ n (dpair _ (box H) Heq).
  Definition tyvar_index {Γ c} (v : tyvar Γ c) := wit v.

  Definition irenaming (Γ : ctx) :=
    @substitution (tyvar Γ).

  Program Definition shift {Γ c c'}  (v : tyvar Γ c) : tyvar (c'::Γ) c :=
    mkTyvar (S (wit v)) _ _.
  Next Obligation.
    cbv -[length] ; simpl. constructor.
    exact (unbox (dfst (pf v))).
  Qed.
  Next Obligation.
    exact (dsnd (pf v)).
  Defined.

End TyVar.

Section ICTerm.
  Let lookup {Γ n} (H:in_ctx n Γ) := Substitution.lookup H.

  Inductive icterm : ctx -> ctype -> Type :=
  | IMRet : forall {Γ} A, icterm Γ (A ~> CM A)
  | IMBind : forall {Γ A B},
      icterm Γ (A ~> CM B) ->
      icterm Γ (CM A) ->
      icterm Γ (CM B)

  | IPair : forall {Γ c1 c2}, icterm Γ c1 -> icterm Γ c2 -> icterm Γ (c1 ⨰ c2)
  | IProj1 : forall {Γ c} (H:isProd c), icterm Γ c -> icterm Γ (prodProj1 H)
  | IProj2 : forall {Γ c} (H:isProd c), icterm Γ c -> icterm Γ (prodProj2 H)

  | IAbs : forall {Γ A c}, (forall x:A, icterm Γ (c x)) -> icterm Γ (CArr c)
  | IApp : forall {Γ c} (H:isArr c) (v:arrDom H), icterm Γ c -> icterm Γ (arrCod H v)

  | ICVar : forall {Γ} (n:nat) (H:in_ctx n Γ), icterm Γ (lookup H)
  | ICAbs : forall {Γ c1 c2}, icterm (c1::Γ) c2 -> icterm Γ (c1 ~~> c2)
  | ICApp : forall {Γ c} (H:isArrC c), icterm Γ c -> icterm Γ (arrCDom H) -> icterm Γ (arrCCod H).

  Derive Signature for icterm.

  Definition isubstitution (Γ : ctx) :=
    @substitution (fun c => icterm Γ c).
End ICTerm.

Section Rename.
  Import Substitution.
  Definition push_renaming (c : ctype) {Γ1 Γ2 : ctx}
  : irenaming Γ2 Γ1 -> irenaming (c::Γ2) Γ1 :=
    dmap (fun c => @shift _ c _).

  Program Definition cons_renaming c {Γ1 Γ2} (σ : irenaming Γ2 Γ1)
    : irenaming (c::Γ2) (c::Γ1)
  := dCons (mkTyvar 0 _ _) (push_renaming c σ).
  Next Obligation.
    cbv -[length] ; simpl. do 2 constructor.
  Qed.

  Definition rename0 {Γ1 c} (ct:icterm Γ1 c)
    : forall {Γ2}, irenaming Γ2 Γ1 -> icterm Γ2 c.
  Proof.
    induction ct ; intros Γ2 σ.
    exact (IMRet _).
    exact (IMBind (IHct1 Γ2 σ) (IHct2 Γ2 σ)). 
    exact (IPair (IHct1 Γ2 σ) (IHct2 Γ2 σ)).
    exact (IProj1 _ (IHct Γ2 σ)).
    exact (IProj2 _ (IHct Γ2 σ)).
    exact (IAbs (fun x => X x Γ2 σ)).
    exact (IApp _ _ (IHct Γ2 σ)).
    pose (Substitution.dlookup n Γ σ H) as n0.
    destruct n0 as [n' [H' <-]]; exact (ICVar n' (unbox H')).
    exact (ICAbs (IHct (c1::Γ2) (cons_renaming c1 σ))).
    exact (ICApp _ (IHct1 Γ2 σ) (IHct2 Γ2 σ)).
  Defined.
End Rename.


Section DepEq.
  Import Equations.
  Import EqNotations.
  Import Substitution.

  Definition ap {A B} (f : A -> B) {a1 a2 : A} (H : a1 = a2) : f a1 = f a2.
  Proof. induction H ; reflexivity. Defined.

  Lemma cancel_trans_sym {A} (a1 a2 : A) (H : a1 = a2) :
    eq_trans H (eq_sym H) = eq_refl.
  Proof.
    refine (match H as H0 in (_ = a) return eq_trans H0 (eq_sym H0) = eq_refl with
            | eq_refl => eq_refl
            end).
  Defined.

  Lemma eq_above_trans {A} {B: A -> Type} {a1 a2 a3:A} {Ha12 : a1 = a2} {Ha23 : a2 = a3}
        {b1 : B a1} {b2 b3} (Hb12 : b1 =⟨Ha12⟩ b2) (Hb23 : b2 =⟨Ha23⟩ b3) :
    b1 =⟨eq_trans Ha12 Ha23⟩ b3.
  Proof.
    revert b3 Hb23.
    refine (match Ha23 as H0 in (_ = a) return forall b3 : B a, b2 =⟨H0⟩ b3 -> b1 =⟨eq_trans Ha12 H0⟩ b3 with
           | eq_refl => fun b3 Hb23 => _ end).
    induction Hb23. exact Hb12.
  Defined.

  Lemma eq_above_base {A B} {a1 a2 : A} {b1 : B a1} {b2} (H1 H2 : a1 = a2)
    : b1 =⟨H1⟩ b2 -> H1 = H2 -> b1 =⟨H2⟩ b2.
  Proof. intros Hb H12 ; induction H12 ; exact Hb. Defined.

  Context (A : Type) (a1 a2 : A) (Ha : a1 = a2).
  Context (B C : A -> Type) (f : forall a, B a -> C a).

  Definition fun_app_above : forall (x:B a1), f a1 x =⟨Ha⟩ f a2 (rew [B] Ha in x) :=
      match Ha as H0 in _ = a
            return forall (x:B a1), f a1 x =⟨H0⟩ f a (rew [B] H0 in x) with
      | eq_refl => fun x => eq_refl
      end.

  Lemma rew_app : forall (x:B a1), f a2 (rew [B] Ha in x) = rew [C] Ha in f a1 x.
  Proof.
    intros.
    symmetry.
    change (rew ?H in ?x = ?y) with (x =⟨H⟩ y).
    simple refine (fun_app_above _).
  Defined.
End DepEq.

Section Weaken.
  Import Substitution.

  Fixpoint id_renaming Γ : irenaming Γ Γ :=
    match Γ with
    | nil => dNil
    | c :: Γ => cons_renaming c (id_renaming Γ)
    end.

  Arguments id_renaming : simpl nomatch.

  Lemma dlookup_id_renaming Γ : forall n H,
      dlookup n Γ (id_renaming Γ) H = mkTyvar n H eq_refl.
  Proof.
    induction Γ.
    intros ; simp_dlookup. 
    move=> [|?] ? // ; simp_dlookup;
            [|unfold push_renaming; rewrite dlookup_dmap; rewrite IHΓ];
            cbv ; erewrite box_irr ; reflexivity.
  Qed.

  Import FunctionalExtensionality.
  Lemma rename0_id {Γ c} (t:icterm Γ c) : rename0 t (id_renaming _) = t.
  Proof.
    induction t ; simpl ; f_equal ; auto.
    extensionality x. auto.
    rewrite dlookup_id_renaming ; reflexivity.
  Qed.

  Import EqNotations.

  Definition lkp_tyvar {Γ1 Γ2} (ρ : irenaming Γ2 Γ1) c (x:tyvar Γ1 c)  : tyvar Γ2 c :=
    rew dsnd (pf x) in dlookup (wit x) _ ρ (unbox (dfst (pf x))).

  Lemma lkp_tyvar_shift : forall {c c0 Γ1 Γ2} (ρ:irenaming Γ2 Γ1) (x:tyvar Γ1 c0),
    lkp_tyvar (cons_renaming c ρ) _ (shift x) = shift (lkp_tyvar ρ _ x).
  Proof.
    intros.
    unfold lkp_tyvar.
    unfold cons_renaming. simp_dlookup. rewrite dlookup_dmap.
    rewrite (rew_app _ _ _ _ _ _ (fun _ x => shift x) _) //.
  Qed.
  
  Lemma rename_rename {Γ c} (t:icterm Γ c) :
    forall Γ1 Γ2 (ρ1 : irenaming Γ1 Γ) (ρ2 : irenaming Γ2 Γ1),
    rename0 (rename0 t ρ1) ρ2 = rename0 t (dmap (lkp_tyvar ρ2) ρ1).
  Proof.
    induction t ; simpl ; intros ; f_equal ; auto.
    - extensionality x ; auto.
    - rewrite dlookup_dmap.
      rewrite (rew_app _ _ _ _ (icterm _) (icterm _) (fun _ t => rename0 t ρ2) _).
      unfold lkp_tyvar.
      rewrite (rew_app _ _ _ _ (tyvar _) (icterm _)
                       (fun _ x => rew dsnd (pf x) in ICVar (wit x) (unbox (dfst (pf x)))) _).
      reflexivity.
    - rewrite IHt.
      f_equal.
      eapply (dlist_extensionality _ _ _ eq_refl _).
      move=> [|n] H //.
      simpl. simp_dlookup. simp_dlookup.
      rewrite /push_renaming !dlookup_dmap.
      apply lkp_tyvar_shift.
   Qed.


  Definition weaken_renaming c {Γ1 Γ2} : irenaming (Γ1 ++ c :: Γ2) (Γ1 ++ Γ2).
  Proof.
    induction Γ1.
    apply push_renaming ; apply id_renaming.
    apply cons_renaming ; assumption.
  Defined.

  Definition weaken c0 {Γ c} : icterm Γ c -> icterm (c0 :: Γ) c :=
    fun ct => rename0 ct (@weaken_renaming c0 nil Γ).

  Lemma dlookup_push_renaming c Γ1 Γ2 n H (ρ : irenaming Γ2 Γ1) :
    dlookup n _ (push_renaming c ρ) H = shift (dlookup n _ ρ H).
  Proof.
    unfold push_renaming. rewrite dlookup_dmap. reflexivity.
  Defined.

  Lemma lkp_tyvar_weaken : forall {c c0 Γ1} (x:tyvar Γ1 c0),
    lkp_tyvar (@weaken_renaming c nil _) _ x = shift x.
  Proof.
    intros.
    unfold weaken_renaming ; simpl.
    unfold lkp_tyvar.
    rewrite dlookup_push_renaming dlookup_id_renaming.
    destruct x as [? [? p]]. simpl.
    dependent elimination p. reflexivity.
  Qed.

  Lemma rename_weaken {Γ1 Γ2 c c1} (ρ:irenaming Γ2 Γ1) (ct:icterm Γ1 c) :
    rename0 (weaken _ ct) (cons_renaming c1 ρ) = weaken _ (rename0 ct ρ).
  Proof.
    unfold weaken; rewrite !rename_rename; f_equal.
    apply (dlist_extensionality _ _ _ eq_refl _).
    move=> [|n] ? ; rewrite !dlookup_dmap; simpl ;
            rewrite lkp_tyvar_shift lkp_tyvar_weaken dlookup_id_renaming //.
  Qed.

End Weaken.



Section ISubstitution.
  Import Substitution.

  Definition vz {Γ c} : icterm (c::Γ) c.
  Proof.
    simple refine (ICVar 0 _); do 2 constructor.
  Defined.

  Definition push_isubstitution {Γ1 Γ2 c} (σ : isubstitution Γ1 Γ2) :
    isubstitution (c::Γ1) (c::Γ2).
  Proof.
    constructor. apply vz.
    exact (dmap (@weaken c _) σ).
  Defined.


  Definition isubst {Γ2 c} (t : icterm Γ2 c) :
    forall {Γ1}, isubstitution Γ1 Γ2 -> icterm Γ1 c.
  Proof.
    induction t ; intros Γ1 σ.
    constructor.
    apply (@IMBind _ A B) ; auto.
    constructor ; auto.
    apply IProj1 ; auto.
    apply IProj2 ; auto.
    constructor ; auto.
    apply IApp; apply IHt ; assumption.
    apply (dlookup _ _ σ H).
    apply ICAbs; apply IHt; apply push_isubstitution ; assumption.
    apply ICApp; auto.
  Defined.

  Arguments isubst : simpl nomatch.

  Fixpoint id_isubst Γ  {struct Γ} : isubstitution Γ Γ :=
    match Γ with
    | nil => NilSubst
    | c :: cs => push_isubstitution (id_isubst cs)
    end.

  Arguments id_isubst : simpl nomatch.

  Lemma dlookup_id_isubst Γ : forall n H, ICVar n H = dlookup n Γ (id_isubst Γ) H.
  Proof.
    induction Γ.
    intros; simp_dlookup.
    intros [|n] H; simpl; simp_dlookup.
    apply (sprop_app_irr (ICVar 0)).

    rewrite dlookup_dmap; rewrite <- IHΓ.
    unfold weaken; simpl.
    rewrite dlookup_push_renaming dlookup_id_renaming.
    simpl; apply (sprop_app_irr (ICVar (S _))).
  Qed.

  Import FunctionalExtensionality.

  Lemma isubst_id {Γ c} (t:icterm Γ c) : isubst t (id_isubst _) = t.
  Proof.
    induction t ; simpl ; f_equal ; auto.
    extensionality x. auto.
    symmetry ; apply dlookup_id_isubst.
  Qed.

  Definition isubst_one {Γ c1 c2} (ct1 : icterm (c1 :: Γ) c2) (ct2 : icterm Γ c1) : icterm Γ c2 :=
    let σ : isubstitution Γ (c1 :: Γ) := ConsSubst ct2 (id_isubst Γ) in
    isubst ct1 σ.

  Lemma isubst_vz {c Γ1 Γ2} (x:icterm Γ2 c) (σ:isubstitution Γ2 Γ1)
    : isubst vz (dCons x σ) = x.
  Proof.
    simpl ; simp_dlookup ; by [].
  Qed.

  (* Lemma isubst_weaken { c' Γ0} (t: icterm Γ0 c') : *)
  (*   forall {c Γ Γ1 Γ2} (HΓ : Γ0 = Γ1 ++ Γ2) (x:icterm Γ c) (σ1:isubstitution Γ Γ1) (σ2:isubstitution Γ Γ2) (t':=rew [fun g => icterm g c'] HΓ in t), *)
  (*     isubst (rename0 t' (weaken_renaming c)) (dapp σ1 (dCons x σ2)) = *)
  (*     isubst t' (dapp σ1 σ2). *)
  (* Proof. *)
  (*   induction t; simpl ; intros ; f_equal ; auto. *)

  (* Lemma isubst_weaken {c' Γ} (t: icterm Γ c') : *)
  (*   forall n {c Γ'} (x:icterm Γ' c) (σ:isubstitution Γ' Γ), *)
  (*     isubst (rename0 t (weaken_renaming' n c)) (dinsert n x σ) = *)
  (*     isubst t σ. *)
  (* Proof. *)
  (*   induction t ; simpl ; intros ; f_equal ; auto. *)
  (*   extensionality x0; apply H. *)
  (*   rewrite dlookup_weaken_renaming. *)
  (*   destruct (Compare_dec.le_lt_dec n0 n) ; simpl. *)

  (*   unfold weaken_re. simpl. *)
  (*   rewrite dlookup_push_renaming. *)
  (*   rewrite dlookup_id_renaming. *)
  (*   simpl. *)
  (*   rewrite (dlookup_equation_3 _ _ _ _ _ _ _). *)
  (*   reflexivity. *)

  (*   simpl. *)
  (*   apply IHt. *)
  (*   simpl ; rewrite (dlookup_equation_2 _ _ _ _ _ _) ; reflexivity. *)
  (* Qed. *)

  Import EqNotations.

  Definition lkp_tyvar_subst {Γ vt} (σ : substitution vt Γ) c (x:tyvar Γ c)
    : vt c :=
    rew (dsnd (pf x)) in dlookup (wit x) _ σ _. 

  Lemma lkp_tyvar_subst_shift {Γ c0 vt} (v0 : vt c0)
        (σ : substitution vt Γ) c (x:tyvar Γ c)
    : lkp_tyvar_subst (dCons v0 σ) c (shift x) = lkp_tyvar_subst σ c x.
  Proof.
    unfold lkp_tyvar_subst.
    destruct x as [? [? ?]] ; simpl. simp_dlookup.
    reflexivity.
  Qed.

    Definition renaming_subst_act {Γ1 Γ2 vt} (ρ : irenaming Γ2 Γ1) (σ : substitution vt Γ2) : substitution vt Γ1 := dmap (lkp_tyvar_subst σ) ρ.


  Lemma dlookup_renaming_subst_act Γ : forall vt n Γ' (ρ : irenaming Γ' Γ) (σ:substitution vt Γ') H,
      dlookup n Γ (renaming_subst_act ρ σ) H =
      lkp_tyvar_subst σ _ (dlookup n _ ρ H).
  Proof.
    intros; unfold renaming_subst_act ; rewrite dlookup_dmap //.
  Defined.

  Lemma renaming_subst_act_dmap Γ
    : forall vt vt' Γ' (ρ : irenaming Γ' Γ) (σ:substitution vt Γ') (f: forall c, vt c -> vt' c),
      renaming_subst_act ρ (dmap f σ) = dmap f (renaming_subst_act ρ σ).
  Proof.
    intros ; unfold renaming_subst_act.
    rewrite <- dmap_compose.
    apply dmap_ext=> //.
    intros ; unfold icompose.
    unfold lkp_tyvar_subst.
    rewrite rew_app. rewrite dlookup_dmap //.
  Qed.
    
  Lemma renaming_weaken Γ1 :
    forall c1 vt (x: vt c1) Γ2 ρ σ,
      renaming_subst_act (@push_renaming c1 Γ1 Γ2 ρ) (dCons x σ) =
      renaming_subst_act ρ σ.
  Proof.
    intros ; unfold renaming_subst_act ; simp dmap.
    unfold push_renaming.
    rewrite <- dmap_compose  ; f_equal.
  Qed.

  Lemma isubst_rename {c Γ1} (t:icterm Γ1 c)
    : forall Γ2 Γ3 (ρ : irenaming Γ2 Γ1) (σ : isubstitution Γ3 Γ2),
      isubst (rename0 t ρ) σ = isubst t (renaming_subst_act ρ σ).
  Proof.
    induction t ; intros ; simpl ; f_equal ; auto.
    extensionality x ; auto.
    rewrite dlookup_renaming_subst_act.
    erewrite (rew_app _ _ _ _ (icterm _) _ (fun _ t => isubst t σ) _).
    reflexivity.
    
    erewrite IHt. f_equal.
    unfold cons_renaming.
    unfold renaming_subst_act. simp dmap.
    unfold push_isubstitution. f_equal.
    move: renaming_subst_act_dmap renaming_weaken.
    unfold renaming_subst_act.
    move=> H -> ; apply H.
  Qed.

  Lemma rename_isubst {c Γ1} (t:icterm Γ1 c)
    : forall Γ2 Γ3 (ρ : irenaming Γ3 Γ2) (σ : isubstitution Γ2 Γ1),
      rename0 (isubst t σ) ρ = isubst t (dmap (fun _ t => rename0 t ρ) σ).
  Proof.
    induction t ; intros ; simpl ; f_equal ; auto.
    - extensionality x ; auto.
    - rewrite dlookup_dmap //.
    - erewrite IHt ; clear IHt.
      f_equal.
      unfold push_isubstitution.
      simp dmap.

      simpl. f_equal.
      rewrite <- !dmap_compose.
      apply dmap_ext=> //.
      move=> c ct ; unfold icompose.
      unfold weaken.
      rewrite !rename_rename ; f_equal.

      clear t c ct σ c2 Γ.
      apply (dlist_extensionality _ _ _ eq_refl _).
      move=> [|n] ? ; simpl ; rewrite !dlookup_dmap ;
              rewrite lkp_tyvar_shift lkp_tyvar_weaken ;
              rewrite dlookup_id_renaming //.
  Qed.

  Lemma renaming_subst_act_id Γ1 : forall vt (σ : substitution vt Γ1),
      renaming_subst_act (id_renaming _) σ = σ.
  Proof.
    intros ; apply (dlist_extensionality _ _ _ eq_refl _).
    intros [|?] ? ; simpl ;
      rewrite dlookup_dmap dlookup_id_renaming ;
      unfold lkp_tyvar_subst => //.
  Qed.

  Lemma isubst_isubst Γ1 c (t:icterm Γ1 c)
    : forall Γ2 Γ3 (σ1 : isubstitution Γ2 Γ1) (σ2 : isubstitution Γ3 Γ2),
      isubst (isubst t σ1) σ2 = isubst t (dmap (fun _ t' => isubst t' σ2) σ1). 
  Proof.
    induction t ; simpl ; intros ; f_equal ; auto.
    - extensionality x ; auto.
    - rewrite dlookup_dmap ; reflexivity.
    - erewrite IHt; f_equal.
      unfold push_isubstitution.
      simp dmap.
      rewrite isubst_vz. f_equal.
      rewrite <- !dmap_compose.
      apply dmap_ext=> // ? ?.
      unfold icompose.
      rewrite isubst_rename.
      unfold weaken.
      rewrite rename_isubst.
      f_equal.
      rewrite renaming_weaken.
      simpl. apply renaming_subst_act_id.
  Qed.

  Lemma weaken_contract : forall Γ c c' (t:icterm (c::Γ) c'),
    isubst (rename0 t (cons_renaming c (push_renaming c (id_renaming Γ))))
        (ConsSubst vz (id_isubst (c :: Γ))) = t.
  Proof.
    intros.
    rewrite -{2}(isubst_id t).
    rewrite isubst_rename.
    f_equal.
    apply (dlist_extensionality _ _ _ eq_refl _).
    move=> [|?] ? //. simp_dlookup. simpl.
    rewrite dlookup_dmap.
    unfold push_isubstitution ; simp_dlookup.
    rewrite !dlookup_dmap.
    rewrite 2!lkp_tyvar_subst_shift.
    unfold lkp_tyvar_subst.
    rewrite dlookup_id_renaming.
    rewrite dlookup_dmap.
    reflexivity.
  Qed.

  Lemma isubst_weaken0 : forall Γ1 Γ2 c c' (x:icterm Γ2 c') (t:icterm Γ1 c) (σ : isubstitution Γ2 Γ1),
    isubst (weaken _ t) (ConsSubst x σ) = isubst t σ.
  Proof.
    intros.
    rewrite isubst_rename.
    f_equal.
    apply (dlist_extensionality _ _ _ eq_refl _).
    move=> [|?] ? ;
    rewrite dlookup_dmap; simpl;
    rewrite dlookup_push_renaming lkp_tyvar_subst_shift dlookup_id_renaming //.
  Qed.

  Lemma isubst_weaken {Γ1 Γ2 c c1} (σ:isubstitution Γ2 Γ1) (ct:icterm Γ1 c) :
    isubst (weaken c1 ct) (push_isubstitution σ) = weaken _ (isubst ct σ).
  Proof.
    unfold push_isubstitution ; rewrite isubst_weaken0.
    unfold weaken ; rewrite rename_isubst //.
  Qed.

End ISubstitution.



(**************************************************************************)
(*                 Translation from DeBruijn to PHOAS                     *)
(**************************************************************************)

Section ICTermToCTerm.
  Import SMNotations.

  Definition icterm_to_cterm {Γ c} (t : icterm Γ c) : valid_term Γ c.
  Proof.
    induction t ; intros ? ?.
    constructor.
    eapply mbind ; eauto.
    unshelve eapply (Pair @∙ _ @∙ _) ; eauto.
    destruct c ; try inversion H;
      unshelve eapply (Proj1 @∙ _) ; eauto.
    destruct c ; try inversion H;
      unshelve eapply (@Proj2 _ _ _ @∙ _) ; [|eauto].
    apply Abs ; intros x ;
      match goal with
      | [H : forall x: _, valid_term _ _ |- _] => apply (H x)
      end ; auto.
    destruct c ; try inversion H;
      apply App ; auto.
    apply CVar; apply (Substitution.dlookup _ _ X H).
    apply CAbs ; intros x. unshelve eapply (IHt _ (ConsSubst x _)) ; eauto.
    destruct c ; try inversion H;
      eapply CApp ; auto.
  Defined.
End ICTermToCTerm.

(* For the other way around we need to get access to Coq syntax  -- see SMPHOASToDeBruijn.v *)


(**************************************************************************)
(*                 Equality for PHOAS terms                               *)
(**************************************************************************)

Reserved Notation "x ≅ y" (at level 70).

Section CEquality.
  Context `{VarType}.
  Import SMNotations.

  Inductive ceq : forall {c}, cterm c -> cterm c -> Type :=

  (* ceq is an equivalence relation *)
  | CRefl : forall {c} (ct : cterm c), ct ≅ ct
  | CSym : forall {c} {ct1 ct2 : cterm c}, ct1 ≅ ct2 -> ct2 ≅ ct1
  | CTrans : forall {c} {ct1 ct2 ct3:cterm c}, ct1 ≅ ct2 -> ct2 ≅ ct3 -> ct1 ≅ ct3

  (* mret, mbind verify the monadic equations *)
  | CRetBind : forall {A B} (x:A) (f : cterm (A ~> CM B)),
      mbind (mret x) f ≅ (f @∘ x)
  | CBindRet : forall {A} (m : cterm (CM A)), mbind m (MRet A) ≅ m
  | CBindBind : forall {A B C} (m : cterm (CM A)) (f : cterm (A ~> CM B)) (g : cterm (B ~> CM C)),
      mbind m (λ∘ x:A, mbind (f @∘ x) g) ≅ mbind (mbind m f) g

  (* Equations for the dependent product *)
  | CArrBeta : forall {A c} (ct : forall x:A, cterm (c x)) (v:A),
      ((λ∘ x : A, ct x) @∘ v) ≅ ct v
  | CArrEta : forall {A c} (ct : cterm (@CArr A c)), ct ≅ (λ∘ x:A, ct @∘ x)
  | CAbsCongr : forall {A c} (ct1 ct2 : forall x:A, cterm (c x)),
      (forall x:A, ct1 x ≅ ct2 x) -> (λ∘ x:A, ct1 x) ≅ (λ∘ x:A, ct2 x)
  | CAppCongr : forall {A c} (ct1 ct2 : cterm (@CArr A c)) (v:A),
      ct1 ≅ ct2 -> (ct1 @∘ v) ≅ (ct2 @∘ v)

  | CArrCBeta : forall {c1 c2}
                  (ct1 : forall `{var:VarType}, var c1 -> @cterm var c2)
                  (ct1_rel : forall {var1 var2:VarType} varR arg1 arg2,
                      varR c1 arg1 arg2 ->
                      cterm_rel var1 var2 varR (@ct1 var1 arg1) (@ct1 var2 arg2))
                  (ct2 : cterm c1),
      (CAbs c1 c2 ct1 @∙ ct2) ≅ flatten (@ct1 cterm ct2)
  | CArrCEta : forall {c1 c2} (ct : cterm (c1 ~~> c2)),
      ct ≅ (λ∙ x:c1, ct @∙ x)
  | CCAbsCongr : forall {c1 c2} (ct1 ct2 : cterm c1 -> cterm c2),
      (forall ct, ct1 ct ≅ ct2 ct) -> (λ∙ x : c1, ct1 x) ≅ (λ∙ x : c1, ct2 x)
  | CCAppCongr : forall {c1 c2} (ct11 ct21 : cterm (c1 ~~> c2)) (ct12 ct22 : cterm c1),
      ct11 ≅ ct21 -> ct12 ≅ ct22 -> (ct11 @∙ ct12) ≅ (ct21 @∙ ct22)
  where "x ≅ y" := (ceq x y).

End CEquality.


(**************************************************************************)
(*                 Equality for DeBruijn terms                            *)
(**************************************************************************)

Definition isProdPf {c1 c2 : ctype} : isProd (c1 ⨰ c2) := I.
Definition isArrPf {A} {c : A -> ctype} : isArr (CArr c) := I.
Definition isArrCPf {c1 c2 : ctype} : isArrC (c1 ~~> c2) := I.
Inductive iceq : forall {Γ c}, icterm Γ c -> icterm Γ c -> Type :=

  (* mret, mbind verify the monadic equations *)
  | ICRetBind : forall {Γ A B} (x:A) (f : icterm Γ (A ~> CM B)),
      IMBind f (IApp isArrPf x (IMRet A)) ≅ (IApp isArrPf x f)
  | ICBindRet : forall {Γ A} (m : icterm Γ (CM A)), IMBind (IMRet A) m ≅ m
  | ICBindBind : forall {Γ A B C} (m : icterm Γ (CM A)) (f : icterm Γ (A ~> CM B)) (g : icterm Γ (B ~> CM C)),
      IMBind (IAbs (fun x:A => IMBind g (IApp isArrPf x f))) m ≅ IMBind g (IMBind f m)
  | ICBindCongr : forall {Γ A B} {m m' : icterm Γ (CM A)} {f f' : icterm Γ (A ~> CM B)},
      m ≅ m' -> f ≅ f' -> IMBind f m ≅ IMBind f' m'

  (* Equations for the pairs *)
  | ICProdBeta1 : forall {Γ c1 c2 H} (ct1 : icterm Γ c1) (ct2: icterm Γ c2),
      IProj1 H (IPair ct1 ct2) ≅ ct1
  | ICProdBeta2 : forall {Γ c1 c2 H} (ct1 : icterm Γ c1) (ct2: icterm Γ c2),
      IProj2 H (IPair ct1 ct2) ≅ ct2
  | ICProdEta : forall {Γ c1 c2 H} (ct : icterm Γ (c1 ⨰ c2)),
      IPair (IProj1 H ct) (IProj2 H ct) ≅ ct
  | ICProdPairCongr : forall {Γ c1 c2} {ct1 ct1' : icterm Γ c1} {ct2 ct2' : icterm Γ c2},
      ct1 ≅ ct1' -> ct2 ≅ ct2' -> IPair ct1 ct2 ≅ IPair ct1' ct2'
  | ICProdProj1Congr : forall {Γ c H} {ct ct' : icterm Γ c},
      ct ≅ ct' -> IProj1 H ct ≅ IProj1 H ct'
  | ICProdProj2Congr : forall {Γ c H} {ct ct' : icterm Γ c},
      ct ≅ ct' -> IProj2 H ct ≅ IProj2 H ct'


  (* Equations for the dependent product *)
  | ICArrBeta : forall {Γ A c} {H : isArr (CArr c)} (ct : forall x:A, icterm Γ (c x)) (v:A),
      IApp H v (IAbs ct) ≅ ct v
  | ICArrEta : forall {Γ A c} {H:isArr (CArr c)} (ct : icterm Γ (@CArr A c)),
    ct ≅ IAbs (fun x:A => IApp H x ct)
  | ICAbsCongr : forall {Γ A c} (ct1 ct2 : forall x:A, icterm Γ (c x)),
      (forall x:A, ct1 x ≅ ct2 x) -> IAbs ct1 ≅ IAbs ct2
  | ICAppCongr : forall {Γ c H} (ct1 ct2 : icterm Γ c) (v:arrDom H),
      ct1 ≅ ct2 -> (IApp H v ct1) ≅ (IApp H v ct2)

  (* Equations for the internal arrow *)
  | ICArrCBeta : forall {Γ c1 c2 H}
                  (ct1 :  icterm (c1 :: Γ) c2)
                  (ct2 : icterm Γ c1),
      ICApp H (ICAbs ct1) ct2 ≅ isubst_one ct1 ct2
  | ICArrCEta : forall {Γ c1 c2 H} (ct : icterm Γ (c1 ~~> c2)),
      ct ≅ ICAbs (ICApp H (weaken c1 ct) vz)
  | ICCAbsCongr : forall {Γ c1 c2} (ct1 ct2:icterm (c1 :: Γ) c2),
      ct1 ≅ ct2 -> ICAbs ct1 ≅ ICAbs ct2
  | ICCAppCongr : forall {Γ c H} {ct11 ct21 : icterm Γ c} {ct12 ct22 : icterm Γ (arrCDom H)},
      ct11 ≅ ct21 -> ct12 ≅ ct22 -> (ICApp H ct11 ct12) ≅ (ICApp H ct21 ct22)

  (* ceq is an equivalence relation *)
  | ICRefl : forall {Γ c} (ct : icterm Γ c), ct ≅ ct
  | ICSym : forall {Γ c} {ct1 ct2 : icterm Γ c}, ct1 ≅ ct2 -> ct2 ≅ ct1
  | ICTrans : forall {Γ c} {ct1 ct2 ct3:icterm Γ c}, ct1 ≅ ct2 -> ct2 ≅ ct3 -> ct1 ≅ ct3

  where "x ≅ y" := (iceq x y).


(**************************************************************************)
(*                 Evaluator for DeBruijn terms                           *)
(**************************************************************************)

Definition proj1 {Γ c} (H:isProd c) (t : icterm Γ c) : icterm Γ (prodProj1 H).
Proof.
  destruct t ; try destruct H ; [exact t1|..] ;
    eapply IProj1 ; econstructor ; eassumption.
Defined.

Lemma proj1_sem : forall Γ c (H:isProd c) (t:icterm Γ c), IProj1 H t ≅ proj1 H t.
Proof.
  intros; destruct t ; try destruct H ; [apply ICProdBeta1|..] ; apply ICRefl.
Qed.
  
Definition proj2 {Γ c} (H:isProd c) (t : icterm Γ c) : icterm Γ (prodProj2 H).
Proof.
  destruct t ; try destruct H ; [exact t2|..] ;
    eapply IProj2 ; econstructor ; eassumption.
Defined.

Lemma proj2_sem : forall Γ c (H:isProd c) (t:icterm Γ c), IProj2 H t ≅ proj2 H t.
Proof.
  intros; destruct t ; try destruct H ; [apply ICProdBeta2|..] ; apply ICRefl.
Qed.

Definition apply_val {Γ c} (H:isArr c) (v : arrDom H) (t:icterm Γ c)
  : icterm Γ (arrCod H v).
Proof.
  destruct t ; try destruct H.
  4:{  exact (i v). }
  all: eapply IApp ; econstructor ; eassumption.
Defined.

Lemma apply_val_sem : forall {Γ c} (H:isArr c) (v : arrDom H) (t:icterm Γ c),
   IApp H v t ≅ apply_val H v t.
Proof.
  intros; destruct t ; try destruct H.
  4:{ simpl; apply ICArrBeta. }
  all:apply ICRefl.
Qed.

Definition apply_comp {Γ c} (H:isArrC c) (t2 : icterm Γ (arrCDom H)) (t1:icterm Γ c) : icterm Γ (arrCCod H).
Proof.
  destruct t1 ; try destruct H.
  5:{ exact (isubst_one t1 t2). }
  all: eapply ICApp ; try econstructor ; eassumption.
Defined.

Lemma apply_comp_sem : forall {Γ c} (H:isArrC c) (t2 : icterm Γ (arrCDom H)) (t1:icterm Γ c),
    ICApp H t1 t2 ≅ apply_comp H t2 t1.
Proof.
  intros ; destruct t1 ; try destruct H.
  5:{ apply ICArrCBeta.  }
  all: apply ICRefl.
Qed.

Equations icbeta Γ c (t:icterm Γ c) : icterm Γ c :=
  icbeta ?(Γ) ?(prodProj1 H) (@IProj1 Γ c H t) := proj1 H t ;
  icbeta ?(Γ) ?(prodProj2 H) (@IProj2 Γ c H t) := proj2 H t ;
  icbeta ?(Γ) ?(arrCod H v) (@IApp Γ c H v t) := apply_val H v t ;
  icbeta ?(Γ) ?(arrCCod H) (@ICApp Γ c H t1 t2) := apply_comp H t2 t1 ;
  icbeta _ _ t := t.



Definition SM_bind {c}
  : forall {Γ A} (f : A -> icterm Γ c) (t:icterm Γ (CM A)), icterm Γ c.
Proof.
  induction c ; intros Γ A0 f t.
  exact (IMBind (IAbs f) t).
  constructor ; [eapply IHc1 | eapply IHc2] ; try eassumption ; intros a0.
  exact (IProj1 isProdPf (f a0)).
  exact (IProj2 isProdPf (f a0)).
  constructor ; intro a ; eapply X ; try eassumption ; intro a0.
  exact (IApp isArrPf a (f a0)).
  constructor. eapply IHc2. intros a0.
  exact (ICApp isArrCPf (weaken _ (f a0)) vz).
  exact (weaken _ t).
Defined.

Inductive stack {Γ c} : ctype -> Type :=
| StckNil : stack c
| StckCont : forall A, (A -> icterm Γ c) -> stack (CM A)
| StckProj1 : forall c' (H:isProd c'), stack (prodProj1 H) -> stack c'
| StckProj2 : forall c' (H:isProd c'), stack (prodProj2 H) -> stack c'
| StckArg : forall c' (H:isArr c') (v:arrDom H), stack (arrCod H v) -> stack c'
| StckCArg : forall c' (H:isArrC c'), icterm Γ (arrCDom H) -> stack (arrCCod H) -> stack c'.

Derive NoConfusion for stack.

Definition rebuild Γ {c0 c} (π : @stack Γ c0 c): forall (t:icterm Γ c), icterm Γ c0.
Proof.
  induction π ; intros t.
  exact t.
  exact (SM_bind i t).
  exact (IHπ (IProj1 H t)).
  exact (IHπ (IProj2 H t)).

  destruct t eqn:Ht.
  simpl in π. inversion π.
  2:{ apply X.  simpl in v. exact v. }
  rewrite <- H0. exact (IHπ (IApp H v t)).
  all:try exact (IHπ (IApp H v t)).

  exact (IHπ (ICApp H t i)).
Defined.

Fixpoint is_neutral {Γ c} (t:icterm Γ c) {struct t} : bool :=
  match t with
  | IMRet A => false
  | IMBind t1 t2 => is_neutral t1
  | IPair _ _ => false
  | IProj1 _ t | IProj2 _ t => is_neutral t
  | IAbs _ => false
  | IApp _ _ t => is_neutral t
  | ICVar _ _ => true
  | ICAbs _ => false
  | ICApp _ t _ => is_neutral t
  end.

Definition reduce (Γ0 : ctx) (fuel:nat) :
  forall c0 Γ c (t:icterm Γ c) (π:@stack Γ0 c0 c) (σ : isubstitution Γ0 Γ), icterm Γ0 c0.
Proof.
  induction fuel as [| fuel IH]; intros c0 Γ c t π σ.
  - exact (rebuild Γ0 π (isubst t σ)).
  - destruct t eqn:Ht.
    + exact (rebuild Γ0 π (isubst t σ)).
    + exact (IH _ _ _ i2 (StckCont A (fun a => IH _ _ _ i1 (StckArg (A ~> CM B) isArrPf a π) σ)) σ).
    + inversion π ;
        try (simpl in * ; contradiction).
      rewrite <- H ; exact (rebuild Γ0 π (isubst t σ)).
      exact (IH _ _ _ i1 X σ).
      exact (IH _ _ _ i2 X σ).
    + exact (IH _ _ _ i (StckProj1 _ H π) σ).
    + exact (IH _ _ _ i (StckProj2 _ H π) σ).
    + inversion π ;
        try (simpl in * ; contradiction).
      rewrite <- H ; exact (rebuild Γ0 π (isubst t σ)).
      exact (IH _ _ _ (i v) X σ).
    + exact (IH _ _ _ i (StckArg _ H v π) σ).
    + pose (t0 := (Substitution.dlookup _ _ σ H)) ;
        destruct (is_neutral t0) eqn:Ht0.
      exact (rebuild _ π t0).
      exact (IH _ _ _ t0 π (id_isubst _)).
    + inversion π ; try (simpl in * ; contradiction).
      rewrite <- H ; exact (rebuild Γ0 π (isubst t σ)).
      exact (IH _ _ _ i X0 (ConsSubst X σ)).
    + exact (IH _ _ _ i1 (StckCArg _ H (IH _ _ _ i2 StckNil σ) π) σ).
Defined.


(* Definition icterm_eval (n:nat) : forall {Γ c}, icterm Γ c -> icterm Γ c. *)
(* Proof. *)
(*   induction n as [|n IHn]. *)
(*   intros ? ? t ; exact t. *)
(*   intros ? ? t. *)
(*   assert (t0 : icterm Γ c). *)
(*   destruct t. *)
(*   constructor. *)
(*   unshelve eapply (IMBind (IHn _ _ _) (IHn _ _ _)); assumption. *)
(*   unshelve eapply (IPair (IHn _ _ _) (IHn _ _ _)); assumption. *)
(*   exact (IProj1 _ (IHn _ _ t)). *)
(*   exact (IProj2 _ (IHn _ _ t)). *)
(*   econstructor ; eassumption. *)
(*   exact (IApp _ v (IHn _ _ t)). *)
(*   econstructor ; eassumption. *)
(*   econstructor ; eassumption. *)
(*   exact (ICApp _ (IHn _ _ t1) (IHn _ _ t2)). *)

(*   exact (IHn _ _ (icbeta _ _ t0)). *)
(* Defined. *)




(**************************************************************************)
(*           Specifications of monad operations in PHOAS                  *)
(**************************************************************************)

Record cmonad :=
  MkCMonad {
      cM : Type -> ctype ;
      cRet : forall A `{VarType}, cterm (A ~> cM A) ;
      cBind : forall A B `{VarType}, cterm (cM A ~~> (A ~> cM B) ~~> cM B)
    }.


(**************************************************************************)
(*           Specifications of monad for DeBruijn terms                   *)
(**************************************************************************)

Notation "c1 @c c2" := (@ICApp _ _ (@isArrCPf _ _) c1 c2) (at level 65).
Notation "c1 @ x" := (@IApp _ _ (@isArrPf _ _) x c1) (at level 65).
Notation "c1 @[ c ] x" := (@IApp _ c (@isArrPf _ _) x c1) (at level 65).
Notation "↑ c" := (weaken _ c) (at level 60).

Set Primitive Projections.

Record icmonad :=
  MkICMonad {
      icM : Type -> ctype ;
      icRet : forall A, icterm nil (A ~> icM A) ;
      icBind : forall A B, icterm nil (icM A ~~> (A ~> icM B) ~~> icM B) ;
      icBindRet : forall A, ↑ icBind A A @c vz @c ↑ icRet A ≅ vz ;
      icRetBind : forall A B x,
          (↑ (icBind A B @c (icRet A @ x)) @c @vz _ (A ~> icM B) : icterm _ (icM B)) ≅ vz @[A ~> icM B] x ;
icAssoc : forall A B C (v0 := vz) (v1 := ↑ vz) (v2 := ↑↑ vz),
    (↑↑↑ icBind B C) @c ((↑↑↑ icBind A B) @c v0 @c v1) @c v2
       ≅ 
    (↑↑↑ icBind A C) @c v0 @c IAbs (fun x => (↑↑↑ icBind B C) @c (v1 @ x) @c v2)
}.




(**************************************************************************)
(*           Extensionality lemmas for the equational theory              *)
(**************************************************************************)

Lemma prod_extensionality Γ c0 (H : isProd c0) (t1 t2 : icterm Γ c0)
      (H1 : IProj1 H t1 ≅ IProj1 H t2) (H2 : IProj2 H t1 ≅ IProj2 H t2)
      : t1 ≅ t2.
Proof.
  destruct c0 ; inversion H.
  simple refine (ICTrans (ICSym (ICProdEta t1)) _).
  apply isProdPf.
  simple refine (ICTrans _ (ICProdEta t2)).
  destruct H. cbv.
  apply ICProdPairCongr ; assumption.
Defined.

Lemma arr_extensionality Γ c0 (H:isArr c0) (t1 t2 : icterm Γ c0)
      (H0 : forall (x:arrDom H), IApp H x t1  ≅ IApp H x t2) : t1 ≅ t2.
Proof.
  destruct c0 ; inversion H.
  simple refine (ICTrans (ICArrEta t1) _) ; [apply isArrPf|].
  simple refine (ICTrans _ (ICSym (ICArrEta t2))) ; [| apply isArrPf].
  destruct H ; cbv.
  apply ICAbsCongr ; assumption.
Defined.

Lemma arrC_extensionality Γ c0 (H:isArrC c0) (t1 t2 : icterm Γ c0)
      (H0 : ICApp H (↑t1) vz  ≅ ICApp H (↑t2) vz) : t1 ≅ t2.
Proof.
  destruct c0 ; inversion H.
  simple refine (ICTrans (ICArrCEta t1) _) ; [apply isArrCPf|].
  simple refine (ICTrans _ (ICSym (ICArrCEta t2))) ; [| apply isArrCPf].
  destruct H ; cbv.
  apply ICCAbsCongr ; assumption.
Defined.

Ltac iceq_extensionality :=
  match goal with
  | [|- @iceq ?Γ ?c ?t1 ?t2] =>
    let c0 := eval cbv in c in
    lazymatch c0 with
    | CM _ => idtac
    | CProd _ _ =>
      simple refine (prod_extensionality Γ c0 isProdPf t1 t2 _ _) ;
      iceq_extensionality
    | CArr _ => simple refine (arr_extensionality Γ c0 isArrPf t1 t2 _) ;
                intros ; iceq_extensionality
    | CArrC _ _ => simple refine (arrC_extensionality Γ c0 isArrCPf t1 t2 _) ;
                          iceq_extensionality
    end
  end.

Ltac iceq_congr :=
  (apply ICBindCongr +
  apply ICProdPairCongr +
  apply ICProdProj1Congr +
  simple refine (@ICProdProj1Congr _ _ isProdPf _ _ _) +
  apply ICProdProj2Congr +
  simple refine (@ICProdProj2Congr _ _ isProdPf _ _ _) +
  (apply ICAbsCongr ; intros) +
  apply ICAppCongr (* TODO : maybe have an equality on the arg instead *) +
  simple refine (@ICAppCongr _ _ isArrPf _ _ _ _) +
  apply ICCAbsCongr +
  apply ICCAppCongr +
  simple refine (@ICCAppCongr _ _ isArrCPf _ _ _ _ _ _)
  ) ; try apply ICRefl.

(* Lemma imbind_smbind Γ A B c: *)
(*   forall (t:icterm Γ (CM A)) (f: A -> icterm Γ (CM B)) (g : B -> icterm Γ c), *)
(*     SM_bind (fun a => IMBind g (f a)) t ≅ SM_bind (fun a => IProj1 H (f a)) t. *)
(* Proof. *)
(*   induction c1 ; simpl ; intros ; destruct H ; apply ICProdBeta1. *)
(* Qed. *)

Lemma iproj1_smbind Γ A c1 : forall (t:icterm Γ (CM A)) c2 (H:isProd (c1 ⨰ c2)) (f: A -> icterm Γ (c1 ⨰ c2)),
    IProj1 H (SM_bind f t) ≅ SM_bind (fun a => IProj1 H (f a)) t.
Proof.
  simpl ; intros ; destruct H ; apply ICProdBeta1.
Qed.

Lemma iproj2_smbind Γ A c2 : forall (t:icterm Γ (CM A)) c1 (H:isProd (c1 ⨰ c2)) (f: A -> icterm Γ (c1 ⨰ c2)),
    IProj2 H (SM_bind f t) ≅ SM_bind (fun a => IProj2 H (f a)) t.
Proof.
  simpl ; intros ; destruct H ; apply ICProdBeta2.
Qed.

Import Substitution.
Lemma rename_iceq_ext Γ1 c (t1 t2 : icterm Γ1 c) (H: t1 ≅ t2)
  : forall Γ2 (ρ : irenaming Γ2 Γ1), rename0 t1 ρ ≅ rename0 t2 ρ.
Proof.
  induction H ; intros ; simpl ; constructor ; auto.
  - simple refine (ICTrans _ (ICSym (ICArrCBeta _ _))).
    unfold isubst_one.
    rewrite rename_isubst isubst_rename.
    match goal with
    | [|- ?t1 ≅ ?t2] => enough (t1 = t2) as -> ; [apply ICRefl|]
    end.
    f_equal.
    unfold renaming_subst_act.
    simp dmap. f_equal.
    apply (dlist_extensionality _ _ _ eq_refl _).
    move=> [|n] ? ; rewrite !dlookup_dmap; simpl;
            rewrite lkp_tyvar_subst_shift;
            unfold lkp_tyvar_subst;
            rewrite <- !dlookup_id_isubst ;
            reflexivity.
  - simp_dlookup. simpl.
    rewrite rename_weaken.
    simple refine (ICSym (ICArrCEta _)).
  - apply ICSym ; eapply ICTrans ; eauto.
  Qed.

Lemma weaken_iceq_ext : forall Γ c0 c (t1 t2 : icterm Γ c) ,
    t1 ≅ t2 -> weaken c0 t1 ≅ weaken c0 t2 .
Proof. intros ; unfold weaken ; apply rename_iceq_ext ; assumption. Qed.

Lemma smbind_iceq_ext c :
  forall Γ A (f1 f2 : A -> icterm Γ c) (t1 t2 : icterm Γ (CM A)),
  (forall a, f1 a ≅ f2 a) -> t1 ≅ t2 -> SM_bind f1 t1 ≅ SM_bind f2 t2.
Proof.  
  induction c ; intros ; simpl.
  iceq_congr ; [assumption|] ; iceq_congr ; auto.
  iceq_congr.
  apply IHc1; [| assumption]; intros; iceq_congr; auto.
  apply IHc2; [| assumption]; intros; iceq_congr; auto.
  iceq_congr. apply X ; intros. iceq_congr ;auto. assumption.
  iceq_congr. apply IHc2. intros ; iceq_congr.
  all: apply weaken_iceq_ext; auto.
Qed.

(**************************************************************************)
(*   Correction of the abstract machine wrt to the equational theory      *)
(**************************************************************************)

Lemma iapp_smbind Γ A c (H:isArr _) (t:icterm Γ (CM A)) v (f:A -> icterm Γ c):
      IApp H v (SM_bind f t) ≅ SM_bind (fun (a:A) => IApp H v (f a)) t. 
Proof.
  intros. simpl. destruct c ; inversion H ; destruct H.
  simple refine (ICTrans (ICArrBeta _ _) _) ;
    apply smbind_iceq_ext ; intros ; apply ICRefl.
Qed.


Lemma smbind_imbind c : forall Γ A B
 (t : icterm Γ (CM A))
  (f : A -> icterm Γ (CM B))
  (g : B -> icterm Γ c),
  SM_bind g (IMBind (IAbs f) t) ≅ SM_bind (fun a : A => SM_bind g (f a)) t.
Proof.
  induction c ; simpl ; intros.
  - simple refine (ICTrans (ICSym (ICBindBind _ _ _)) _).
    do 3 iceq_congr. simple refine (ICArrBeta f x).
  - iceq_congr.
    simple refine (ICTrans (IHc1 _ _ _ _ _ _) _).
    apply smbind_iceq_ext ; [|apply ICRefl].
    intros. apply ICSym ; apply ICProdBeta1.

    simple refine (ICTrans (IHc2 _ _ _ _ _ _) _).
    apply smbind_iceq_ext ; [|apply ICRefl].
    intros. apply ICSym ; apply ICProdBeta2.

  - iceq_congr.
    simple refine (ICTrans (X _ _ _ _ _ _ _) _) ;
      apply smbind_iceq_ext; [|apply ICRefl].
    intros ; apply ICSym ; apply @ICArrBeta. 

  - iceq_congr.
    simple refine (ICTrans (IHc2 _ _ _ _ _ _) _) ;
      apply smbind_iceq_ext; [|apply ICRefl].
    intros.
    simpl.
    unfold weaken; simpl.
    simple refine (ICTrans _ (ICSym (@ICArrCBeta _ _ _ _ _ _))).
    unfold isubst_one.
    rewrite weaken_contract. apply ICRefl.
Qed.

Arguments rebuild : simpl nomatch.

Derive NoConfusion for ctype.

Lemma rebuild_iapp Γ c (ct : icterm Γ c) :
  forall c' (H: isArr c) v (π:@stack Γ c' _),
  rebuild Γ π (IApp H v ct) ≅ rebuild Γ (StckArg c H v π) ct.
Proof.
  destruct ct ; intros ; try (simpl ; apply ICRefl).
  dependent elimination π ;
    match goal with
    | [H : isProd _ |- _] => inversion H
    | [H : isArr _ |- _] => inversion H
    | [H : isArrC _ |- _] => inversion H
    end.
  + cbv; apply ICRefl.
  + simpl. cbv -[SM_bind].
    revert Γ i ; induction c' ; intros Γ i ; simpl.
    destruct H; simple refine (ICTrans (ICRetBind _ _) _).
    simple refine (@ICArrBeta _ _ _ _ _ _).
    simple refine (ICTrans _ (ICProdEta _)).
    iceq_congr. simple refine (IHc'1 _ _). simple refine (IHc'2 _ _).
    simple refine (ICTrans _ (ICSym (ICArrEta _))).
    iceq_congr. simple refine (X _ _ _).
    simple refine (ICTrans _ (ICSym (ICArrCEta _))).
    iceq_congr. simple refine (IHc'2 _ _).
  + inversion H3.
Qed.

Lemma rebuild_iceq_ext Γ c0 c (π :@stack Γ c0 c) : forall t1 t2,
    t1 ≅ t2 -> rebuild _ π t1 ≅ rebuild _ π t2.
Proof.
  induction π ; intros.
  assumption.
  apply smbind_iceq_ext. intros ; apply ICRefl. assumption.
  apply IHπ; iceq_congr; assumption.
  apply IHπ; iceq_congr; assumption.
  simple refine (ICTrans (ICSym (rebuild_iapp _ _ _ _ _ _ _)) _).
  simple refine (ICTrans _ (rebuild_iapp _ _ _ _ _ _ _)). 
  apply IHπ. iceq_congr. assumption.
  simpl. apply IHπ. iceq_congr. assumption.
Qed.

Import FunctionalExtensionality.
Lemma isubst_smbind {c} :
  forall {Γ1 Γ2 A} (t:icterm Γ1 (CM A)) (f:A -> icterm Γ1 c) (σ : isubstitution Γ2 Γ1),
    isubst (SM_bind f t) σ = SM_bind (fun a => isubst (f a) σ) (isubst t σ).
Proof.
  induction c ; intros ; simpl; f_equal ; auto.
  apply IHc1.
  apply IHc2.
  extensionality a ; apply H.
  rewrite IHc2.
  f_equal ; [extensionality a |] ; rewrite <- isubst_weaken=> //.
Qed.


Lemma SM_bind_rebuild Γ c1 c2 (π : @stack Γ c2 c1) : forall A (t:icterm Γ (CM A)) (f: A -> icterm Γ c1),
    rebuild _ π (SM_bind f t) ≅ SM_bind (fun a => rebuild _ π (f a)) t.
Proof.
  induction π ; intros ; simpl.
  - apply ICRefl.
  - apply smbind_imbind.
  - destruct c' ; inversion H ; destruct H.
    simple refine (ICTrans (rebuild_iceq_ext _ _ _ _ _ _
                                             (iproj1_smbind _ _ _ _ _ _ f)) _).
    apply IHπ.
  - destruct c' ; inversion H ; destruct H.
    simple refine (ICTrans (rebuild_iceq_ext _ _ _ _ _ _
                                             (iproj2_smbind _ _ _ _ _ _ f)) _).
    apply IHπ.
  - simple refine (ICTrans (ICSym (rebuild_iapp _ _ _ _ _ _ _)) _).
    simple refine (ICTrans (rebuild_iceq_ext _ _ _ _ _ _
                                             (iapp_smbind _ _ c' H _ _ f)
                           ) _).
    simple refine (ICTrans (IHπ _ _ _) _).
    apply smbind_iceq_ext.
    intros. apply rebuild_iapp. apply ICRefl.
  -
    assert (ICApp H (SM_bind f t) i ≅ SM_bind (fun a => ICApp H (f a) i) t)
    as icapp_smbind.
    destruct c' ; inversion H. simpl.
    simple refine (ICTrans (ICArrCBeta _ i) _).
    unfold isubst_one.
    rewrite isubst_smbind.
    simpl. rewrite (Substitution.dlookup_equation_2 _ _ _ _ _ _).
    apply smbind_iceq_ext ; intros; rewrite isubst_weaken0 ; rewrite isubst_id ;
    destruct H ; apply ICRefl.
    
    simple refine (ICTrans (rebuild_iceq_ext _ _ _ _ _ _ icapp_smbind) _).
    apply IHπ.
Qed.


Import FunctionalExtensionality.

Lemma reduce_rebuild (n:nat):
  forall (Γ0 Γ : ctx)(c0 c: ctype) (t:icterm Γ c) (π:stack c) (σ : isubstitution Γ0 Γ),
     reduce Γ0 n c0 Γ c t π σ ≅ rebuild Γ0 π (isubst t σ).
Proof.
  induction n as [|n].
  intros ; apply ICRefl.
  intros ; destruct t.
  - apply ICRefl.
  - simpl.
    simple refine (ICTrans (IHn _ _ _ _ _ _ _) _).
    simpl.
    pose (ICSym (SM_bind_rebuild _ (CM B) _ π _ (isubst t2 σ) (fun a => isubst t1 σ @ a))).
    simpl in i.
    
    simple refine (ICTrans _ (rebuild_iceq_ext _ _ _ _ _ _ _)).
    2: exact (IMBind (IAbs (fun a : A => isubst t1 σ @[ A ~> CM B] a))
                     (isubst t2 σ)).
    simple refine (ICTrans _ i). clear i.
    apply smbind_iceq_ext. intros.
    simple refine (ICTrans (IHn _ _ _ _ _ _ _) _).
    simple refine (ICSym (rebuild_iapp _ _ _ _ _ _ _)).
    apply ICRefl.
    iceq_congr. simple refine (ICSym (ICArrEta _)).
  - simpl. dependent elimination π ; simpl.
    cbv -[isubst]. apply ICRefl.
    cbv -[reduce rebuild isubst].
    simple refine (ICTrans (IHn _ _ _ _ _ _ _) _).
    apply rebuild_iceq_ext.
    apply ICSym. apply ICProdBeta1.
    cbv -[reduce rebuild isubst].
    simple refine (ICTrans (IHn _ _ _ _ _ _ _) _).
    apply rebuild_iceq_ext.
    apply ICSym. apply ICProdBeta2.
    inversion H1.
    inversion H2.
  - simple refine (ICTrans (IHn _ _ _ _ _ _ _) _); apply ICRefl.
  - simple refine (ICTrans (IHn _ _ _ _ _ _ _) _); apply ICRefl.
  - dependent elimination π ; simpl ; cbv -[reduce rebuild isubst].
    apply ICRefl.
    inversion H.
    inversion H0.
    simple refine (ICTrans (IHn _ _ _ _ _ _ _) _).
    apply rebuild_iceq_ext.
    apply ICSym. apply @ICArrBeta.
    inversion H2.
  - simple refine (ICTrans (IHn _ _ _ _ _ _ _) _).
    apply ICSym ; apply rebuild_iapp.
  - simpl. remember (is_neutral (Substitution.dlookup n0 Γ σ H)) as b.
    destruct b. apply ICRefl.
    simple refine (ICTrans (IHn _ _ _ _ _ _ _) _).
    rewrite isubst_id. apply ICRefl.
  - dependent elimination π; simpl;
    cbv -[reduce rebuild isubst push_isubstitution].
    apply ICRefl.
    inversion H.
    inversion H0.
    inversion H1.
    simple refine (ICTrans (IHn _ _ _ _ _ _ _) _).
    apply rebuild_iceq_ext.
    apply ICSym. simple refine (ICTrans (ICArrCBeta _ _) _).
    unfold isubst_one.
    rewrite isubst_isubst.
    unfold push_isubstitution.
    simp dmap.
    simpl.
    rewrite (Substitution.dlookup_equation_2 _ _ _ _ _ _).
    unfold map_subst. rewrite <- Substitution.dmap_compose.
    unfold Substitution.icompose.
    assert ((fun (i : CtypeSig.A) (x : icterm Γ0 i) =>
           isubst (↑ x) (ConsSubst i0 (id_isubst Γ0))) = Substitution.iid).
    extensionality i. extensionality x.
    rewrite isubst_weaken0.
    rewrite isubst_id.
    reflexivity.
    rewrite H.
    rewrite Substitution.dmap_id.
    apply ICRefl.
  - simpl.
    simple refine (ICTrans (IHn _ _ _ _ _ _ _) _).
    simpl.
    apply rebuild_iceq_ext.
    iceq_congr.
    simple refine (ICTrans (IHn _ _ _ _ _ _ _) _).
    apply ICRefl.
Qed.