From Coq Require Import List.
Require Import SM.dlist.
From Equations Require Import Equations.

(* Set Universe Polymorphism. *)

(**************************************************************************)
(*               Simple types for SM                                      *)
(**************************************************************************)

Inductive ctype : Type :=
| CM : Type -> ctype
| CProd : ctype -> ctype -> ctype
| CArr : forall {A}, (A -> ctype) -> ctype
| CArrC : ctype -> ctype -> ctype
.



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
  Definition A := ctype.
End CtypeSig.
Module Substitution := DList CtypeSig.
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
  dependent destruction ρ2.
  exact ((varR _ y y0) * (IHρ ρ2))%type.
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

(* Axiom cterm_parametric : forall c (ct : closed_cterm c), parametric_closed_cterm ct. *)


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


Definition in_ctx (n:nat) (Γ : ctx) := n < length Γ.

Definition lookup {Γ n} (H:in_ctx n Γ) := Substitution.lookup H.


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


From Coq Require micromega.Lia.

Section Weaken.
  Import Coq.micromega.Lia.

  (* Weakening need to compute, in particular the necessary               *)
  (* rewriting in the ICVar case need to reduce to eq_refl on close terms *)
  Equations weaken0 c0 {Γ1 Γ2 c} (t : icterm (Γ1 ++ Γ2) c) : icterm (Γ1 ++ c0 :: Γ2) c :=
    weaken0 c0 (IMRet A) := IMRet A;
    weaken0 c0 (IMBind f m) := IMBind (weaken0 _ f) (weaken0 _ m);
    weaken0 c0 (IPair t1 t2) := IPair (weaken0 _ t1) (weaken0 _ t2) ;
    weaken0 c0 (IProj1 H t) := IProj1 H (weaken0 _ t) ;
    weaken0 c0 (IProj2 H t) := IProj2 H (weaken0 _ t) ;
    weaken0 c0 (IAbs t) := IAbs (fun x => weaken0 _ (t x)) ;
    weaken0 c0 (IApp H v t) := IApp H v (weaken0 _ t) ;
    weaken0 c0 (ICVar n H) := _ ;
    weaken0 c0 (ICAbs t) := ICAbs (@weaken0 c0 (_ :: _) _ _ t) ;
    weaken0 c0 (ICApp H t1 t2) := ICApp H (weaken0 _ t1) (weaken0 _ t2).

  Lemma weaken_in_ctx {Γ1 c Γ2 n} :
    let n' := n + (if Nat.ltb n (length Γ1) then 0 else 1) in
    in_ctx n (Γ1 ++ Γ2) -> in_ctx n' (Γ1 ++ c :: Γ2).
  Proof. 
    unfold in_ctx ; erewrite 2!(app_length) ; simpl.
    rewrite PeanoNat.Nat.add_succ_r.
    destruct (Nat.ltb n (length Γ1)) ;
     [rewrite PeanoNat.Nat.add_0_r ; apply PeanoNat.Nat.lt_lt_succ_r | rewrite PeanoNat.Nat.add_1_r ; apply Lt.lt_n_S].  
  Qed.


  Import EqNotations.
  Definition lookup_nat_eq : forall {Γ n1 n2} (e: n1 = n2) (H : in_ctx n1 Γ),
      lookup H = lookup (rew [fun n => in_ctx n Γ] e in H).
  Proof.
    intros ; apply Substitution.lookup_irr ; assumption.
  Defined.

  Lemma weaken_lookup c Γ1 : forall {Γ2 n H}, lookup H = lookup (@weaken_in_ctx Γ1 c Γ2 n H).
  Proof.
    induction Γ1 ; simpl.
    intros; set (H0 := @weaken_in_ctx nil _ _ _ H).
    rewrite (lookup_nat_eq (PeanoNat.Nat.add_1_r n) H0). 
    simpl; apply Substitution.lookup_irr; reflexivity.

    intros ? [|n] ?; [reflexivity|].
    simpl; rewrite IHΓ1; apply Substitution.lookup_irr; reflexivity.
  Defined.
    
  Next Obligation.
    erewrite weaken_lookup.
    eapply ICVar.
  Defined.


  Definition weaken : forall c0 {Γ} c, icterm Γ c -> icterm (c0 :: Γ) c :=
    fun c0 {Γ} c => @weaken0 c0 nil Γ c.
End Weaken.


Definition vz {Γ c} : icterm (c::Γ) c.
Proof.
  assert (H : in_ctx 0 (c :: Γ)) by apply PeanoNat.Nat.lt_0_succ.
  apply (ICVar 0 H).
Defined.

Definition push_isubstitution {Γ1 Γ2 c} (σ : isubstitution Γ1 Γ2) :
  isubstitution (c::Γ1) (c::Γ2).
Proof.
  constructor. apply vz.
  exact (map_subst (weaken c) σ).
Defined.


Definition isubst {Γ2 c}
           (t : icterm Γ2 c) :
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
  apply (Substitution.dlookup _ _ σ H).
  apply ICAbs; apply IHt; apply push_isubstitution ; assumption.
  apply ICApp; auto.
Defined.


Fixpoint id_isubst Γ  {struct Γ} : isubstitution Γ Γ :=
  match Γ with
  | nil => NilSubst
  | c :: cs =>
    let σ := id_isubst cs in
    ConsSubst vz (map_subst (weaken c) σ)
  end.


Definition isubst_one {Γ c1 c2} (ct1 : icterm (c1 :: Γ) c2) (ct2 : icterm Γ c1) : icterm Γ c2 :=
  let σ : isubstitution Γ (c1 :: Γ) := ConsSubst ct2 (id_isubst Γ) in
  isubst ct1 σ.


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

(* Notation "x ≅ y" := (ceq x y) (at level 70). *)

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
      ct ≅ ICAbs (ICApp H (weaken c1 _ ct) vz)
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

Definition icterm_eval (n:nat) : forall {Γ c}, icterm Γ c -> icterm Γ c.
Proof.
  induction n as [|n IHn].
  intros ? ? t ; exact t.
  intros ? ? t.
  assert (t0 : icterm Γ c).
  destruct t.
  constructor.
  unshelve eapply (IMBind (IHn _ _ _) (IHn _ _ _)); assumption.
  unshelve eapply (IPair (IHn _ _ _) (IHn _ _ _)); assumption.
  exact (IProj1 _ (IHn _ _ t)).
  exact (IProj2 _ (IHn _ _ t)).
  econstructor ; eassumption.
  exact (IApp _ v (IHn _ _ t)).
  econstructor ; eassumption.
  econstructor ; eassumption.
  exact (ICApp _ (IHn _ _ t1) (IHn _ _ t2)).

  exact (IHn _ _ (icbeta _ _ t0)).
Defined.



(**************************************************************************)
(*         Soundness of the evaluator wrt the equational theory           *)
(**************************************************************************)

Lemma isubst_compose {Γ1 Γ2 Γ3 c} (ct : icterm Γ3 c) (σ1 : isubstitution Γ2 Γ3) (σ2 : isubstitution Γ1 Γ2) :
  isubst (isubst ct σ1) σ2 = isubst ct (map_subst (fun _ ct => isubst ct σ2) σ1).
Proof. admit. Admitted.

Lemma isubst_cong {Γ2 c} {ct1 ct2 : icterm Γ2 c} (H : ct1 ≅ ct2) :
  forall {Γ1} {σ : isubstitution Γ1 Γ2}, isubst ct1 σ ≅ isubst ct2 σ.
Proof.
  induction H ; intros ; simpl ; try (constructor ; intros ; auto) ; simpl.
  unfold isubst_one.
  rewrite (isubst_compose ct1 _ σ). simpl.
  admit.
  admit.
  apply (ICTrans (ICSym (IHiceq2 _ _)) (ICSym (IHiceq1 _ _))).
Admitted.


Global Transparent icbeta.
Definition icterm_eval_sound : forall (n:nat) {Γ c} (t:icterm Γ c), t ≅ icterm_eval n t.
Proof.
  intro n ; induction n as [|n IHn] ; intros ; simpl.
  constructor.
  destruct t ; try change (icbeta ?Γ ?c ?t) with t ; try apply IHn.
  all:unshelve eapply (ICTrans _ (IHn _ _ _)).
  1,2: constructor ; apply IHn.
  all:simpl.

  eapply (ICTrans (ICProdProj1Congr (IHn _ _ _))).
  apply proj1_sem.

  eapply (ICTrans (ICProdProj2Congr (IHn _ _ _))).
  apply proj2_sem.

  eapply (ICTrans (ICAppCongr _ _ v (IHn _ _ _))).
  apply apply_val_sem.

  eapply (ICTrans (ICCAppCongr (IHn _ _ _) (IHn _ _ _))).
  apply apply_comp_sem.
Qed.

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

Record icmonad :=
  MkICMonad {
      icM : Type -> ctype ;
      icRet : forall A, icterm nil (A ~> icM A) ;
      icBind : forall A B, icterm nil (icM A ~~> (A ~> icM B) ~~> icM B) ;
      (* icBindRet : forall A m, ICApp (ICApp (icBind A A) m) (icRet A) ≅ m; *)
      (* icRetBind : forall A B f x, ICApp (ICApp (icBind A B) (IApp x (icRet A) eq_refl)) f ≅ IApp x f eq_refl ; *)
      (* icAssoc : forall A B C m f g, *)
      (*     ICApp (ICApp (icBind B C) (ICApp (ICApp (icBind A B) m) f)) g  *)
      (*           ≅ *)

      (*           ICApp (ICApp (icBind A C) m) (IAbs (fun x => (ICApp (ICApp (icBind B C) (IApp x f eq_refl)) g))) *)
    }.
