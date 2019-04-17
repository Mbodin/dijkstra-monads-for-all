Require Import FunctionalExtensionality.
Require Import List.
Require Import Arith.
Require Import ZArith.

(******************************************************************************************)
(* Axioms we use, in addition to functional extensionality                                *)
(******************************************************************************************)
Axiom prop_ext : forall (P Q : Prop), (P <-> Q) -> P = Q.
Axiom proof_irrelevance : forall (P : Prop) (p1 p2:P), p1 = p2.

Lemma sig_eq : forall (A:Type) (P:A -> Prop) (x1 x2: sig P),
  proj1_sig x1 = proj1_sig x2 -> x1 = x2.
Proof.
  intros A P x1 x2 Heq. destruct x1. destruct x2. simpl in Heq.
  revert p p0. rewrite Heq. intros p p0. rewrite (proof_irrelevance _ p p0).
  reflexivity.
Qed.

(******************************************************************************************)
(* Pre orders, for defining ordered monads and ordered monad algebras.                    *)
(******************************************************************************************)
Record PreOrderOn (A : Type) : Type :=
  mkPreOrder
    { preo_order   :> A -> A -> Prop
    ; preo_refl    : forall a, preo_order a a
    ; preo_trans   : forall a b c,
        preo_order a b -> preo_order b c -> preo_order a c
    }.

Definition Prop_op_order : PreOrderOn Prop.
  apply (mkPreOrder Prop (fun p1 p2 => p2 -> p1)); auto.
Defined.

Definition Prop_order : PreOrderOn Prop.
  apply (mkPreOrder Prop (fun p1 p2 => p1 -> p2)); auto.
Defined.

Definition PredOP_order A : PreOrderOn (A -> Prop).
  apply (mkPreOrder (A -> Prop) (fun p1 p2 => forall a, p2 a -> p1 a)); auto.
Defined.

(******************************************************************************************)
(* Monads, in Kleisli triple form                                                         *)
(******************************************************************************************)
Record Monad : Type :=
  mkMonad
    { monad_tyop :> Type -> Type
    ; monad_ret  : forall A, A -> monad_tyop A
    ; monad_bind : forall A B,
        monad_tyop A -> (A -> monad_tyop B) -> monad_tyop B
    ; monad_law1 : forall A B a f, monad_bind A B (monad_ret A a) f = f a
    ; monad_law2 : forall A c, monad_bind A A c (monad_ret A) = c
    ; monad_law3 : forall A B C c f g,
        monad_bind B C (monad_bind A B c f) g
        = monad_bind A C c (fun a => monad_bind B C (f a) g)
    }.

Definition ret {M : Monad} {A} := monad_ret M A.

Definition bind {M : Monad} {A} {B} := monad_bind M A B.

(******************************************************************************************)
(* Ordered Monads, where the bind respects the order                                      *)
(******************************************************************************************)
Record OrderedMonad : Type :=
  mkOrderedMonad
    { omon_monad :> Monad
    ; omon_order : forall {A}, PreOrderOn (omon_monad A)
    ; omon_bind  :
        forall A B (c c' : omon_monad A) (f f' : A -> omon_monad B),
          omon_order c c' ->
          (forall a, omon_order (f a) (f' a)) ->
          omon_order (bind c f) (bind c' f')
    }.

Definition mLE {M : OrderedMonad} {A} := @omon_order M A.

(******************************************************************************************)
(* Monad algebras, and algebras on ordered monads                                         *)
(******************************************************************************************)
Record MonadAlgebra (M : Monad) : Type :=
  mkMonadAlgebra
    { malg_carrier : Type
    ; malg_map     :> M malg_carrier -> malg_carrier
    ; malg_ret     : forall c, malg_map (ret c) = c
    ; malg_bind    : forall X (m : M X) f,
        malg_map (bind m (fun x => ret (malg_map (f x)))) = malg_map (bind m f)
    }.

Record OrderedAlgebra (M : Monad) : Type :=
  mkOrderedAlgebra
    { oalg_alg     :> MonadAlgebra M
    ; oalg_order   : PreOrderOn (malg_carrier _ oalg_alg)
    ; oalg_mono    : forall A (k k' : A -> malg_carrier _ oalg_alg) m,
        (forall a, oalg_order (k a) (k' a)) ->
        oalg_order (oalg_alg (bind m (fun x => ret (k x))))
                   (oalg_alg (bind m (fun x => ret (k' x))))
    }.
Arguments mkOrderedAlgebra [M].

(******************************************************************************************)
(* Monad morphisms                                                                        *)
(******************************************************************************************)
Record MonadMorphism (M W : Monad) : Type :=
  mkMorphism
    { mon_morph :> forall {A}, M A -> W A
    ; mon_morph_ret : forall A (a : A), mon_morph (ret a) = ret a
    ; mon_morph_bind : forall A B (m : M A) (f : A -> M B),
        mon_morph (bind m f) = bind (mon_morph m) (fun a => mon_morph (f a))
    }.


(******************************************************************************************)
(* Monad Relations                                                                        *)
(******************************************************************************************)
Record MonadRelation (M W : Monad) : Type :=
  mkMonadRelation
    { mrel      :> forall A, M A -> W A -> Prop
    ; mrel_ret  : forall A a, mrel A (ret a) (ret a)
    ; mrel_bind : forall A B m w f g,
        mrel A m w -> (forall a, mrel B (f a) (g a)) -> mrel B (bind m f) (bind w g)
    }.

(******************************************************************************************)
(* Dijkstra Monads over specification (i.e. ordered) monads                               *)
(******************************************************************************************)

(* The laws for Dijkstra monads only hold up to the monad laws, so we
   need some utilities to handle equality. *)
Definition coerce {A B} : (B = A) -> A -> B.
  intros [] a. exact a.
Defined.

Lemma substeq {A} {B : A -> Type} {a a' : A} : a = a' -> B a = B a'.
  intros []. reflexivity.
Defined.

Record Dijkstra (W : OrderedMonad) : Type := mkDM
  { dm_tyop :> forall A, W A -> Type
  ; dm_ret  : forall A, forall (a : A), dm_tyop A (monad_ret W A a)
  ; dm_bind : forall A B (w : W A) (f : A -> W B)
                     (d : dm_tyop A w) (g : forall a, dm_tyop B (f a)),
      dm_tyop B (monad_bind W A B w f)
  ; dm_wkn : forall {A} {w w'}, dm_tyop A w -> mLE w w' -> dm_tyop A w'
  ; dm_law1 : forall A B (a : A) (f : A -> W B) (g : forall a, dm_tyop B (f a)),
      dm_bind A B (ret a) f (dm_ret A a) g =
      coerce (substeq (monad_law1 W A B a f)) (g a)
  ; dm_law2 : forall A c m,
      dm_bind A A c ret m (dm_ret A) =
      coerce (substeq (monad_law2 W A c)) m
  ; dm_law3 : forall A B C c f g (m : dm_tyop A c)
                     (f' : forall (a : A), dm_tyop B (f a))
                     (g' : forall (b : B), dm_tyop C (g b)),
      dm_bind B C _ _ (dm_bind A B _ _ m f') g' =
      coerce (substeq (monad_law3 W A B C c f g))
        (dm_bind A C _ _ m (fun a => dm_bind B C _ _ (f' a) g'))
  }.

Definition dret {W} {D : Dijkstra W} {A} := dm_ret W D A.

Definition dbind {W} {D : Dijkstra W} {A} {B} {w} {f} := dm_bind W D A B w f.

Definition wkn {W} {D : Dijkstra W} {A} {w w'} := @dm_wkn W D A w w'.

Notation "x <- m1 ; m2" := (dbind m1 (fun x => m2)) (at level 80, right associativity).

(* A occasionally useful tactic for writing programs that with loose
   specifications. *)
Ltac DPROG p := apply (wkn p); simpl.

(* Generic if-then-else for Dijkstra monads *)
Definition ifTE {A} {W} {D : Dijkstra W} {w1 w2 : W A} :
  forall (b: bool), D A w1 -> D A w2 -> D A (if b then w1 else w2) :=
  fun b tt ff =>
    match b as b return D A (if b then w1 else w2) with
    | true => tt
    | false => ff
    end.


(******************************************************************************************)
(* Deriving Dijkstra Monads from Effect Observations / Monad morphisms                    *)
(******************************************************************************************)
Section OfMorphism.

  Variable M : Monad.
  Variable W : OrderedMonad.
  Variable alpha : MonadMorphism M W.

  Definition Dalpha_carrier A (w : W A) :=
    { m : M A | mLE (alpha A m) w }.

  Definition Dalpha_ret : forall A (a : A), Dalpha_carrier A (ret a).
    intros A a.
    exists (ret a). rewrite  mon_morph_ret. apply preo_refl.
  Defined.

  Definition Dalpha_bind :
    forall A B (w : W A) (f : A -> W B)
           (d : Dalpha_carrier A w) (g : forall a, Dalpha_carrier B (f a)),
      Dalpha_carrier B (bind w f).
    intros A B w f m g.
    exists (bind (proj1_sig m) (fun a => proj1_sig (g a))).
    rewrite mon_morph_bind.
    apply omon_bind.
    + apply (proj2_sig m).
    + intro a. apply (proj2_sig (g a)).
  Defined.

  Definition Dalpha_wkn A w w' : Dalpha_carrier A w -> mLE w w' -> Dalpha_carrier A w'.
    intros [m H] le.
    exists m. eapply preo_trans.
    - apply H.
    - assumption.
  Defined.

  Definition Dalpha : Dijkstra W.
    apply (mkDM W Dalpha_carrier Dalpha_ret Dalpha_bind Dalpha_wkn).
    - intros. apply sig_eq. simpl.
      unfold bind. unfold ret.
      rewrite monad_law1. rewrite monad_law1.
      reflexivity.
    - intros. apply sig_eq. simpl.
      unfold bind. unfold ret.
      rewrite monad_law2. rewrite monad_law2.
      reflexivity.
    - intros. apply sig_eq. simpl.
      unfold bind.
      rewrite monad_law3. rewrite monad_law3.
      reflexivity.
  Defined.

  Definition lift {A} : forall (m : M A), Dalpha A (alpha A m).
    intro m. exists m. apply preo_refl.
  Defined.

End OfMorphism.

(******************************************************************************************)
(* Deriving Dijkstra monads from Monadic Relations                                        *)
(******************************************************************************************)
Section OfRelation.

  Variable M : Monad.
  Variable W : OrderedMonad.
  Variable R : MonadRelation M W.
  Variable R_wkn : forall A (m : M A) (w1 w2 : W A), mLE w1 w2 -> R A m w1 -> R A m w2.

  Definition Drel_carrier A (w : W A) :=
    { m : M A | R A m w }.

  Definition Drel_ret : forall A (a : A), Drel_carrier A (ret a).
    intros A a. exists (ret a). apply mrel_ret.
  Defined.

  Definition Drel_bind :
    forall A B (w : W A) (f : A -> W B)
           (d : Drel_carrier A w) (g : forall a, Drel_carrier B (f a)),
      Drel_carrier B (bind w f).
  intros A B w f m g.
    exists (bind (proj1_sig m) (fun a => proj1_sig (g a))).
    apply mrel_bind.
    + apply (proj2_sig m).
    + intro a. apply (proj2_sig (g a)).
  Defined.

  Definition Drel_wkn A w w' : Drel_carrier A w -> mLE w w' -> Drel_carrier A w'.
    intros [m H] le. exists m. eapply R_wkn; eassumption.
  Defined.

  Definition Drel : Dijkstra W.
    apply (mkDM W Drel_carrier Drel_ret Drel_bind Drel_wkn).
    - intros. apply sig_eq. simpl.
      unfold bind. unfold ret.
      rewrite monad_law1. rewrite monad_law1.
      reflexivity.
    - intros. apply sig_eq. simpl.
      unfold bind. unfold ret.
      rewrite monad_law2. rewrite monad_law2.
      reflexivity.
    - intros. apply sig_eq. simpl.
      unfold bind.
      rewrite monad_law3. rewrite monad_law3.
      reflexivity.
  Defined.

End OfRelation.

(******************************************************************************************)
(* The main useful example of a specification monad: the monotone continuations monad.    *)
(* This is especially useful because the monad laws hold definitionally in Coq.           *)
(******************************************************************************************)
Section MonotoneContinuationsMonad.

  Variable R : Type.
  Variable Rorder : PreOrderOn R.

  Definition MonoContCarrier : Type -> Type :=
    fun X => { f : (X -> R) -> R
             | forall k k', (forall a, Rorder (k a) (k' a)) ->
                            Rorder (f k) (f k') }.

  Definition MonoCont_ret : forall A, A -> MonoContCarrier A.
    intros A a. exists (fun post => post a). eauto.
  Defined.

  Definition MonoCont_bind :
    forall A B, MonoContCarrier A -> (A -> MonoContCarrier B) -> MonoContCarrier B.
  Proof.
    intros A B m f.
    exists (fun post => proj1_sig m (fun a => proj1_sig (f a) post)).
    destruct m. simpl.
    intros. apply p.
    intro a. destruct (f a). simpl. eauto.
  Defined.

  Definition MonoContU : Monad.
    apply (mkMonad MonoContCarrier MonoCont_ret MonoCont_bind);
      intros; apply sig_eq; reflexivity.
  Defined.

  Definition MonoCont_order A : PreOrderOn (MonoContU A).
    apply (mkPreOrder
             _ (fun m1 m2 => forall k, Rorder (proj1_sig m1 k) (proj1_sig m2 k))).
    - intros. apply preo_refl.
    - intros. eauto using preo_trans.
  Defined.

  Definition MonoCont : OrderedMonad.
    apply (mkOrderedMonad MonoContU MonoCont_order).
    - simpl. intros. eapply preo_trans.
      + apply H.
      + apply (proj2_sig c').
        intro a. apply H0.
  Defined.

End MonotoneContinuationsMonad.

(* Generic pre-/post-conditions for the W^Pure specification monad. *)
Definition PrePostSpec {A} (P : Prop) (Q : A -> Prop) :
  MonoContU _ Prop_op_order A.
  exists (fun (Z : A -> Prop) => P /\ forall a, Q a -> Z a).
  simpl. intuition eauto.
Defined.


(******************************************************************************************)
(* Some less useful specification monads, covered in Section 4.1                          *)
(******************************************************************************************)

(** Negative pairs *)
Set Primitive Projections.

Record nprod (A B : Type) := npair { nfst : A ; nsnd : B }.
Arguments npair {_ _} _ _.
Arguments nfst {_ _} _.
Arguments nsnd {_ _} _.

Notation "A × B" := (nprod A B)%type (at level 80) : type_scope.
Notation "⟨ x , y ⟩" := (npair x y).

Unset Primitive Projections.

(* Hoare-style pre- and post- condition *)
Section PrePost.

  Definition PP X := Prop  × (X -> Prop).

  Definition PP_ret : forall A, A -> PP A := fun _ x => ⟨ True, fun y => y = x ⟩.

  Definition PP_bind
    : forall A B, PP A -> (A -> PP B) -> PP B :=
    fun A B m f =>
      ⟨ (nfst m /\ forall x, nsnd m x -> nfst (f x)),
        fun y => exists x, nsnd m x /\ nsnd (f x) y ⟩.

  Program Definition PP_monad : Monad :=
    mkMonad PP PP_ret PP_bind _ _ _.

  Next Obligation.
    change (f ?x) with ⟨nfst (f x), nsnd (f x)⟩.
    cbv; f_equal.
    apply prop_ext.
    intuition. subst ; assumption.
    extensionality y.
    apply prop_ext.
    intuition.
    destruct H as [? [<- ?]] ; assumption.
    eexists ; split ; [| eassumption] ; reflexivity.
  Qed.

  Next Obligation.
    destruct c.
    cbv ; f_equal.
    apply prop_ext ; intuition.
    extensionality y ; apply prop_ext ; intuition.
    destruct H as [? [? <-]] ; eassumption.
    eexists ; split. eassumption. reflexivity.
  Qed.

  Next Obligation.
    cbv ; f_equal ; [|extensionality m] ; apply prop_ext.
    intuition.
    eapply H1. eexists ; split ; eassumption.
    destruct (H1 x H) ; assumption.
    destruct H as [? []]; destruct (H1 x0 H) ; auto.
    split.
    intros [? [[? []]]] ; eexists ; split ; [|eexists;split] ;eassumption.
    intros [? [? [? []]]] ; eexists ; split ; [eexists; split|] ; eassumption.
  Qed.

  Program Definition PP_order A : PreOrderOn (PP A) :=
    mkPreOrder _ (fun m1 m2 => (nfst m1 -> nfst m2) /\ forall x, nsnd m2 x -> nsnd m1 x) _ _.

  Program Definition PPSpecMonad : OrderedMonad :=
    mkOrderedMonad PP_monad PP_order _.
  Next Obligation.
    intuition. destruct (H0 x) ; auto.
    destruct H2 as [x0 []]. destruct (H0 x0) ; eexists ; split ; auto.
    auto.
  Qed.

End PrePost.


(* Forward predicate transformer *)
Section StrongestPostcondition.

  Definition PropOver (p:Prop) := { q : Prop | q -> p }.

  Definition SP X := { f : forall p:Prop, X -> PropOver p |
                       forall (p1 p2 : Prop) x, (p1 -> p2) -> proj1_sig (f p1 x) -> proj1_sig (f p2 x)}.

  Definition prop_over (p q : Prop) (H : q -> p) : PropOver p := exist _ q H.

  Program Definition SP_ret : forall A, A -> SP A :=
    fun A x => exist _ (fun p y => prop_over p (p /\ x = y) _) _.

  Program Definition SP_bind : forall A B, SP A -> (A -> SP B) -> SP B :=
    fun A B m f => exist _ (fun p y => prop_over _ (exists x, proj1_sig (f x (proj1_sig m p x) y)) _) _.

  Next Obligation.
    exact (proj2_sig (proj1_sig m p H) (proj2_sig (proj1_sig (f _) _ _) H0)).
  Qed.

  Next Obligation.
    exists H0 ; apply (proj2_sig (f H0) _ _ _ (proj2_sig m _ _ H0 H)) ; assumption.
  Qed.

  Lemma trivial_eq (p:Prop) {A} (x:A) : p = (p /\ x = x).
  Proof. apply prop_ext ; split ; intuition. Qed.

  Program Definition SP_monad : Monad := mkMonad SP SP_ret SP_bind _ _ _.

  Next Obligation.
    apply sig_eq ; extensionality p ; extensionality y ; apply sig_eq ; apply prop_ext; simpl ; split.
    intros [] ;
      destruct (proj2_sig (proj1_sig (f _) _ _) H) as [_ ->] ;
      rewrite (trivial_eq p x) ; assumption.
    intros H ; exists a; rewrite <- trivial_eq ; assumption.
  Qed.

  Next Obligation.
    apply sig_eq ; extensionality p ; extensionality y ; apply sig_eq ; apply prop_ext; simpl ; split.
    intros [? []] ; subst ; assumption.
    intros H ; eexists ; intuition ; eassumption.
  Qed.

  Next Obligation.
    apply sig_eq ; extensionality p ; extensionality y ; apply sig_eq ; apply prop_ext; simpl ; split.


    intros [x0 H].
    match goal with
    | [ H : proj1_sig ?X |- _] => destruct (proj2_sig X H)as [x1]
    end.
    exists x1 ; exists x0; destruct (g x0); destruct (f x1); simpl in *.
    eapply p0. intro ; assumption. exact H.


    intros [x0 [x H]] ; exists x.
    destruct (g x). simpl in *.
    eapply p0.
    2: eassumption.
    intros ? ; exists x0 ; assumption.
  Qed.

  Program Definition SP_order A : PreOrderOn (SP A) :=
    mkPreOrder _ (fun m1 m2 => forall p x, proj1_sig (proj1_sig m2 p x) -> proj1_sig (proj1_sig m1 p x)) _ _.

  Program Definition ForwardPredTransformer : OrderedMonad :=
    mkOrderedMonad SP_monad SP_order _.
  Next Obligation.
    exists H1. eapply (proj2_sig (f H1)).
    apply H. apply H0 ; eassumption.
  Qed.

End StrongestPostcondition.



(******************************************************************************************)
(* Ordered monad algebras yield morphisms into the monotone continuations monad.          *)
(* This gives a general way of generating many effect observations, as described at the   *)
(* end of Section 4.1                                                                     *)
(******************************************************************************************)
Section Algebra.

  Variable M : Monad.
  Variable alg : OrderedAlgebra M.

  Definition WPSpecMonad := MonoCont _ (oalg_order _ alg).

  Definition mor_underlying : forall X, M X -> WPSpecMonad X.
    intros X m.
    exists (fun post => alg (bind m (fun x => ret (post x)))).
    intros. apply oalg_mono. assumption.
  Defined.

  Definition mor : MonadMorphism M WPSpecMonad.
    apply (mkMorphism _ _ mor_underlying).
    - intros A a. apply sig_eq.
      extensionality post. simpl.
      rewrite monad_law1.
      apply malg_ret.
    - intros A B m f. apply sig_eq.
      extensionality post. simpl.
      rewrite monad_law3.
      rewrite malg_bind.
      reflexivity.
  Defined.

  Definition D_wp := Dalpha _ _ mor.

  Definition underlying {A spec} : D_wp A spec -> M A.
    intros [f _]. exact f.
  Defined.

End Algebra.
Arguments WPSpecMonad [M].
Arguments underlying [M alg A spec].


(******************************************************************************************)
(* The state monad, and the corresponding Weakest Precondition Dijkstra monad.            *)
(******************************************************************************************)
Section State.

  Variable St : Type.

  Definition State : Monad.
    apply (mkMonad (fun X => St -> (X * St))
                   (fun X x s => (x, s))
                   (fun X Y c f s => let (y,s') := c s in f y s')).
    - reflexivity.
    - intros A c. extensionality s. destruct (c s). reflexivity.
    - intros A B C c f g.
      extensionality s.
      destruct (c s).
      destruct (f a s0).
      reflexivity.
  Defined.

  (* The get and put operations *)
  Definition get : State St := fun s => (s,s).
  Definition put : St -> State unit := fun s => fun _ => (tt, s).

  Definition StProp_alg : MonadAlgebra State.
    apply (mkMonadAlgebra State (St -> Prop)
                          (fun c s => let (P,s') := c s in P s')).
    - intros c. simpl. reflexivity.
    - intros X m f. extensionality s.
      simpl. destruct (m s). reflexivity.
  Defined.

  Definition StProp_oalg : OrderedAlgebra State.
    apply (mkOrderedAlgebra StProp_alg (PredOP_order St)).
    simpl. intros A k k' m H s H1. destruct (m s). auto.
  Defined.

  (* Weakest preconditions for specifying stateful operations *)
  Definition StateSpec := WPSpecMonad StProp_oalg.

  (* The Dijkstra monad for state, indexed by predicate transformers. *)
  Definition StateWP : Dijkstra StateSpec := D_wp _ _.

  (* A convienient way to specify stateful computations: using pre and
     post conditions. *)
  Definition PrePostWP (P : St -> Prop) (Q : St -> St -> Prop) : StateSpec unit.
    exists (fun (Z : unit -> St -> Prop) s0 =>
              P s0 /\ forall s1, Q s0 s1 -> Z tt s1).
    simpl. intuition eauto.
  Defined.

  Definition PrePost P (Q : St -> St -> Prop) :=
    StateWP unit (PrePostWP P Q).

  (* Lifting the get and put operations to the Dijkstra monad level;
     Coq automatically works out the predicate transformer lifting. *)
  Definition get' : StateWP _ _ := lift State StateSpec _ get.
  Definition put' (s : St) : StateWP unit _ := lift State StateSpec _ (put s).

  (* A coherence check: if we write a computation in the Dijkstra
     monad for some Pre/Post specification, then the underlying
     computation on states satisfies the usual semantics of a Hoare
     triple.  *)
  Lemma soundness P Q : forall (c : PrePost P Q) s,
      P s -> Q s (snd (underlying c s)).
  Proof.
    destruct c as [f H]. simpl in *.
    intros s pre_ok.
    set (H1:=H (fun _ => Q s) s).
    generalize H1. clear H1.
    destruct (f s). simpl.
    auto.
  Qed.

  (* Example from Section 3.4 *)
  Definition modify (f : St -> St) :=
    x <- get' ; put' (f x).

End State.
Arguments get' [St].
Arguments put' [St].

(* A toy stateful program, from Swamy et al., 2013. *)
Definition incr : PrePost nat
                          (fun _ => True)
                          (fun s0 s1 => s1 > s0).
  DPROG (x <- get' ; put' (S x)).
  intuition eauto.
Defined.



From Coq Require List.
Section WeightedComputations.
  Import List.
  Context (I:Type) (e : I) (m:I -> I -> I).
  Print Grammar constr.
  Notation "x ∗ y" := (m x y) (at level 50).
  Context (lunit : forall x, e ∗ x = x) (runit : forall x, x ∗ e = x) (assoc : forall x y z, x ∗ (y ∗ z) = (x ∗ y) ∗ z).
  Context (comm : forall x y, x ∗ y = y ∗ x).

  Import ListNotations.

  Lemma flat_map_app {A B} l1 : forall l2 (f : A -> list B),
      flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
  Proof.
    induction l1 as [|? ? IHl] ; intros;
      [|simpl; rewrite <- app_assoc; f_equal ; rewrite IHl]; reflexivity.
  Qed.

  Program Definition Wc : Monad :=
    mkMonad (fun X => list (I * X))
            (fun X x => [(e, x)])
            (fun A B m0 f => flat_map (fun p1 => map (fun p2 => (fst p1 ∗ fst p2, snd p2)) (f (snd p1))) m0)
            _ _ _.
  Next Obligation.
    replace (fun p2 : I * B => (e ∗ fst p2, snd p2)) with (fun x : I * B => x).
    rewrite map_id; rewrite app_nil_r; reflexivity.
    extensionality x; destruct x; rewrite lunit; reflexivity.
  Qed.

  Next Obligation.
    induction c as [|[] ? IH]. reflexivity.
    simpl ; rewrite IH ; rewrite runit ; reflexivity.
  Qed.

  Next Obligation.
    induction c as [|[] ? IH]. reflexivity.

    simpl; rewrite flat_map_app; f_equal ; [|exact IH].
    rewrite !flat_map_concat_map.
    rewrite !concat_map; f_equal.
    rewrite !map_map; f_equal.
    extensionality x ; destruct x; rewrite map_map; f_equal.
    extensionality y ; destruct y ; simpl.
    rewrite assoc; reflexivity.
  Qed.

  Lemma Forall_app {A} (f: A -> Prop) l1 : forall l2, Forall f (l1 ++ l2) <-> Forall f l1 /\ Forall f l2.
  Proof.
    induction l1 as [|? ? IH].
    intros ; simpl ; intuition.
    intros ; simpl ; split.
    intros H ; inversion H. apply IH in H3. destruct H3.
    split ; [constructor|] ; assumption.
    intros [H1 H2] ; inversion H1.
    constructor; [|apply IH; split] ; assumption.
  Qed.

  Lemma Forall_map {A B} (f : A -> B) (p : B -> Prop) l :
    Forall p (map f l) <-> Forall (fun x => p (f x)) l.
  Proof.
    induction l as [|? ? IH].
    split ; constructor.
    simpl ; split ; intros H ; inversion H ; constructor ; try (apply IH) ; assumption.
  Qed.

  Lemma in_flat_map {A B} (f : A -> list B) y l : In y (flat_map f l) -> exists x, In x l /\ In y (f x).
  Proof.
    induction l.
    intros [].
    simpl ; intros H%in_app_or. destruct H. exists a ; split ; [left ; reflexivity |
    assumption].
    specialize (IHl H). destruct IHl as [x0 []].
    exists x0 ; split ; [right|] ; assumption.
  Qed.

  Lemma Forall_flat_map {A B} (f : A -> list B) (p : B -> Prop) l :
    Forall p (flat_map f l) <-> (forall x y, In x l -> In y (f x) -> p y).
  Proof.
    induction l.
    simpl ; split. intros ? ? ? []. constructor.
    simpl ; split.
    + intros H%Forall_app. destruct H.
      intros ? ? []. rewrite Forall_forall in H. subst ; apply H.
      rewrite IHl in H0. apply H0. assumption.

    + intros. apply Forall_forall.
      intros y Hy. apply in_app_or in Hy ; destruct Hy. 
      apply (H a). left ; reflexivity. assumption.
      apply in_flat_map in H0. destruct H0 as [x0 []].
      apply (H x0) ; [right|] ; assumption.
  Qed.

  Program Definition WcProp_alg : MonadAlgebra Wc :=
  mkMonadAlgebra Wc (I -> Prop)
                  (fun m r => Forall (fun x => snd x (fst x ∗ r)) m) _ _.

  Next Obligation.
    extensionality x. apply prop_ext ; split.
    intros H ; apply Forall_inv in H ; simpl in H. rewrite lunit in H. assumption.
    constructor.
    simpl. rewrite lunit ; assumption.
    constructor.
  Qed.

  Next Obligation.
    extensionality r. apply prop_ext. rewrite !Forall_flat_map.
    simpl. split. intros.
    apply in_map_iff in H1.
    destruct y.
    destruct H1 as [? []].  subst .
    simpl.
    injection H1 ; intros ; subst.
    rewrite (comm (fst x)). rewrite <- assoc.
    enough (forall x0, In x0 (f (snd x)) -> snd x0 (fst x0 ∗ (fst x ∗ r))).
    exact (H3 x0 H2).
    apply (H x (fst x, fun r => forall x1, In x1 (f (snd x)) -> snd x1 (fst x1 ∗ r))). assumption.
    left. f_equal. rewrite runit. reflexivity.
    extensionality r0. apply prop_ext ; split ; intros Hall.
    rewrite Forall_forall in Hall.
    assumption.
    rewrite Forall_forall.
    assumption.

    intros H x y Hx [H1 | H1]. subst. simpl.
    rewrite Forall_forall. intros.
    rewrite runit. rewrite assoc. rewrite (comm (fst x0)).
    apply (H x (fst x ∗ fst x0, snd x0)).
    assumption.
    change (In _ (map ?f ?l)) with (In (f x0) (map f l)).
    apply in_map.
    assumption.
    contradiction.
  Qed.

  Program Definition WcProp_oalg : OrderedAlgebra Wc :=
    mkOrderedAlgebra WcProp_alg (PredOP_order I) _.
  Next Obligation.
   rewrite Forall_flat_map in H0 |- *.
   intros [] [] Hx [Hy|[]]. injection Hy ; intros ; subst ; simpl.
   apply H. apply (H0 (i,a0) (i ∗ e, k' a0) Hx).
   left ; reflexivity.
  Qed.

  Definition WcSpec := WPSpecMonad WcProp_oalg.

  Definition WcWP : Dijkstra WcSpec := D_wp _ _.

End WeightedComputations.


(******************************************************************************************)
(* Non-determinism, with Angelic and Demonic specifications.                              *)
(******************************************************************************************)
Section NonDeterminism.

  (* Or lists? *)
  Definition ND : Monad.
    apply (mkMonad (fun X => X -> Prop)
                   (fun X x => fun x' => x = x')
                   (fun X Y c f => fun y => exists x, c x /\ f x y)).
    - intros A B a f. extensionality y.
      apply prop_ext. split.
      + intros [x [eq H]]. subst. auto.
      + intro. exists a. auto.
    - intros A c. extensionality a.
      apply prop_ext. split.
      + intros [x [eq H]]. subst. auto.
      + intro. exists a. auto.
    - intros A B C m f g.
      extensionality c.
      apply prop_ext. split.
      + intros [b [[a [H1 H2]] H3]]. eauto.
      + intros [a [H1 [b [H2 H3]]]]. eauto.
  Defined.

  Definition ListM : Monad.
    apply (mkMonad (fun A => list A)
                   (fun A a => a :: nil)
                   (fun A B m f => concat (map f m))).
    - intros A B a f. simpl. apply app_nil_r.
    - intros A m. induction m.
      + reflexivity.
      + simpl. rewrite IHm. reflexivity.
    - intros A B C m f g.
      induction m.
      + reflexivity.
      + simpl. rewrite map_app.
        rewrite concat_app.
        rewrite IHm.
        reflexivity.
  Defined.

  Definition choose {A} (l : list A) : ListM A := l.
  Definition pick : ListM bool := true :: false :: nil.

  Section Angelic.

    Fixpoint or (xs : list Prop) : Prop :=
      match xs with
      | nil => False
      | P :: Ps => P \/ or Ps
      end.

    Lemma or_Exists A (P : A -> Prop) xs : or (map P xs) -> Exists P xs.
      induction xs.
      - simpl. intros [].
      - intros [H|H].
        + constructor. assumption.
        + constructor 2. auto.
    Qed.

    Lemma or_app : forall l1 l2, or (l1 ++ l2) = (or l1 \/ or l2).
    Proof.
      intros l1 l2. apply prop_ext. induction l1; simpl; tauto.
    Qed.

    Lemma or_concat : forall l, or (map or l) = or (concat l).
    Proof.
      induction l.
      - reflexivity.
      - simpl. rewrite IHl. rewrite or_app. reflexivity.
    Qed.

    Lemma concat_map_nil : forall A (l : list A),
      concat (map (fun x => x :: nil) l) = l.
    Proof.
      induction l.
      - reflexivity.
      - simpl. rewrite IHl. reflexivity.
    Qed.

    Definition Angelic_alg : MonadAlgebra ListM.
      apply (mkMonadAlgebra ListM Prop or).
      - intros c. simpl. apply prop_ext. tauto.
      - intros X m f. simpl.
        rewrite <- (@map_map _ _ _ f (fun x => or x :: nil)).
        rewrite <- (@map_map _ _ _ or (fun x => x :: nil)).
        rewrite concat_map_nil.
        apply or_concat.
    Defined.

    Definition Angelic_oalg : OrderedAlgebra ListM.
      apply (mkOrderedAlgebra Angelic_alg Prop_op_order).
      simpl. intros A k k' m H.
      induction m; simpl; intuition eauto.
    Defined.

    Definition AngelicSpec := WPSpecMonad Angelic_oalg.

    Definition Angelic : Dijkstra AngelicSpec := D_wp ListM Angelic_oalg.

    Definition pickA : Angelic bool _ := lift ListM AngelicSpec _ pick.
    Definition chooseA {A} (l : list A) : Angelic A _ :=
      lift ListM AngelicSpec _ (choose l).
    Definition failA {A} : Angelic A _ := chooseA nil.

    Definition PostAngelic {A} (Q : A -> Prop) : AngelicSpec A.
      exists (fun post => forall a, Q a -> post a).
      simpl. auto.
    Defined.

    Definition guardA (b : bool) : Angelic unit _ :=
      ifTE b (dret tt) failA.

    Lemma Angelic_soundness {A} (P : A -> Prop) (Q : AngelicSpec A) (c : Angelic A Q) :
      proj1_sig Q P -> Exists P (underlying c).
    Proof.
      destruct Q. simpl in *.
      destruct c. simpl in *.
      intro.
      apply or_Exists.
      rewrite <- concat_map_nil.
      rewrite map_map.
      apply p0.
      assumption.
    Qed.

    Lemma Angelic_soundness2 {A} (P : A -> Prop) (c : Angelic A (PostAngelic P)) : Exists P (underlying c).
    Proof.
      apply Angelic_soundness. simpl. auto.
    Qed.

  End Angelic.

  Definition test_angelic : Angelic nat (PostAngelic (fun x => x = 5)).
    DPROG (chooseA (2 :: 3 :: 5 :: nil)).
    intros Q H. eauto.
  Defined.

  Definition pytriples : Angelic (nat * nat * nat)%type
                                 (PostAngelic (fun t => match t with (x,y,z) => x*x + y*y = z*z end)).
    DPROG (let l := 1 :: 2 :: 3 :: 4 :: 5 :: nil in
           x <- chooseA l ;
           y <- chooseA l ;
           z <- chooseA l ;
           dret (x, y, z)).
    intros k H. intuition.
  Defined.

  Section Demonic.

    Fixpoint and (xs : list Prop) : Prop :=
      match xs with
      | nil => True
      | P :: Ps => P /\ and Ps
      end.

    Lemma and_app : forall l1 l2, and (l1 ++ l2) = (and l1 /\ and l2).
    Proof.
      intros l1 l2. apply prop_ext. induction l1; simpl; tauto.
    Qed.

    Lemma and_concat : forall l, and (map and l) = and (concat l).
    Proof.
      induction l.
      - reflexivity.
      - simpl. rewrite IHl. rewrite and_app. reflexivity.
    Qed.

    Definition Demonic_alg : MonadAlgebra ListM.
      apply (mkMonadAlgebra ListM Prop and).
      - intros c. simpl. apply prop_ext. tauto.
      - intros X m f. simpl.
        rewrite <- (@map_map _ _ _ f (fun x => and x :: nil)).
        rewrite <- (@map_map _ _ _ and (fun x => x :: nil)).
        rewrite concat_map_nil.
        apply and_concat.
    Defined.

    Definition Demonic_oalg : OrderedAlgebra ListM.
      apply (mkOrderedAlgebra Demonic_alg Prop_op_order).
      simpl. intros A k k' m H.
      induction m; simpl; intuition eauto.
    Defined.

    Definition DemonicSpec := WPSpecMonad Demonic_oalg.

    Definition Demonic : Dijkstra DemonicSpec := D_wp ListM Demonic_oalg.

    Definition pickD : Demonic bool _ := lift ListM DemonicSpec _ pick.
    Definition chooseD {A} (l : list A) : Demonic A _ :=
      lift ListM DemonicSpec _ (choose l).
    Definition failD {A} : Demonic A _ := chooseD nil.

    Definition PostDemonic {A} (Q : A -> Prop) : DemonicSpec A.
      exists (fun post => forall a, Q a -> post a).
      simpl. auto.
    Defined.

    Definition pick_from {A} (l : list A) : Demonic A (PostDemonic (fun a => In a l)).
      refine ((fix pick_from (l : list A) : Demonic A (PostDemonic (fun a => In a l)) :=
                 match l with
                 | nil    => wkn failD _
                 | a :: l => wkn (b <- pickD ; ifTE b (dret a) (pick_from l)) _
                 end) l); simpl; auto.
    Defined.

    Definition guardD (b : bool) : Demonic unit _ :=
      ifTE b (dret tt) failD.

  End Demonic.

  Definition test_demonic : Demonic nat (PostAngelic (fun x => x > 1 /\ x < 6)).
    DPROG (chooseD (2 :: 3 :: 5 :: nil)).
    intros Q H. intuition.
  Defined.

  Definition pytriplesD : Demonic (nat * nat * nat)%type
                                  (PostDemonic (fun t => match t with (x,y,z) => x*x + y*y = z*z end)).
    DPROG (let l := 1 :: 2 :: 3 :: 4 :: 5 :: nil in
           x <- pick_from l ;
           y <- pick_from l ;
           z <- pick_from l ;
           _ <- guardD (Nat.eqb (x*x + y*y) (z*z)) ;
           dret (x, y, z)).
    intros k H. intuition (subst; simpl; auto).
  Defined.

End NonDeterminism.

Section FreeMonad.

  Variable S : Type.
  Variable P : S -> Type.

  Inductive FreeF A : Type :=
  | retFree : A -> FreeF A
  | opr     : forall s, (P s -> FreeF A) -> FreeF A.

  Fixpoint bindFree A B (c : FreeF A) (f : A -> FreeF B) : FreeF B :=
    match c with
    | retFree _ a => f a
    | opr _ s k   => opr _ s (fun p => bindFree _ _ (k p) f)
    end.

  Definition Free : Monad.
    apply (mkMonad FreeF retFree bindFree).
    - reflexivity.
    - induction c.
      + reflexivity.
      + simpl. apply f_equal. extensionality p. apply H.
    - induction c.
      + reflexivity.
      + intros. simpl. apply f_equal. extensionality p. apply H.
  Defined.

  Definition op (s : S) : Free (P s) :=
    opr _ s (retFree _).

  Definition trace := list { s : S & P s }.

  Section History.

    Fixpoint History_alg_U (f : Free (trace -> Prop)) : trace -> Prop :=
      match f with
      | retFree _ P => P
      | opr _ s k => fun t => forall p, History_alg_U (k p) (existT _ s p :: t)
      end.

    Definition History_alg : MonadAlgebra Free.
      apply (mkMonadAlgebra Free (trace -> Prop) History_alg_U).
      - intros c. simpl. reflexivity.
      - intros X m f. induction m.
        + reflexivity.
        + simpl. extensionality t. apply prop_ext. split; intros.
          * rewrite <- H. auto.
          * rewrite H. auto.
    Defined.

    Definition History_oalg : OrderedAlgebra Free.
      apply (mkOrderedAlgebra History_alg (PredOP_order _)).
      simpl. intros A k k' m H. induction m; intros t; simpl; eauto.
    Defined.

    Definition HistorySpec := WPSpecMonad History_oalg.

    Definition FreeHist : Dijkstra HistorySpec := D_wp _ _.

    Definition opHist s : FreeHist (P s) _ := lift Free HistorySpec _ (op s).

  End History.

  Section Future.

    Definition future_op (s : S) (k : P s -> trace -> Prop) (t : trace) : Prop :=
      match t with
      | nil                  => False
      | (existT _ s' p) :: t => exists e : s = s', k (coerce (substeq e) p) t
      end.

    Fixpoint Future_alg_U (f : Free (trace -> Prop)) : trace -> Prop :=
      match f with
      | retFree _ P => P
      | opr _ s k => future_op s (fun p => Future_alg_U (k p))
      end.

    Definition Future_alg : MonadAlgebra Free.
      apply (mkMonadAlgebra Free (trace -> Prop) Future_alg_U).
      - intros c. simpl. reflexivity.
      - intros X m f. induction m.
        + reflexivity.
        + simpl. apply f_equal. extensionality p. apply H.
    Defined.

    Definition Future_oalg : OrderedAlgebra Free.
      apply (mkOrderedAlgebra Future_alg (PredOP_order _)).
      simpl. intros A k k' m H. induction m; intros t.
      - simpl. auto.
      - destruct t as [|[s' p] t]; simpl.
        + auto.
        + intros [e H1]. destruct e. exists eq_refl. apply H0. assumption.
    Defined.

    Definition FutureSpec := WPSpecMonad Future_oalg.

    Definition FreeFuture : Dijkstra FutureSpec := D_wp _ _.

    Definition opFuture s : FreeFuture (P s) _ := lift Free FutureSpec _ (op s).

  End Future.

  Section OperationSpecs.

    Variable OpSpecs : forall s, Prop * (P s -> Prop).

    Fixpoint OpSpec_alg_U (m : Free Prop) : Prop :=
      match m with
      | retFree _ P => P
      | opr _ s k   =>
        fst (OpSpecs s) /\ (forall p, snd (OpSpecs s) p -> OpSpec_alg_U (k p))
      end.

    Definition OpSpec_alg : MonadAlgebra Free.
      apply (mkMonadAlgebra Free Prop OpSpec_alg_U).
      - reflexivity.
      - intros X m f. induction m.
        + reflexivity.
        + simpl. apply prop_ext. split.
          * intuition eauto. rewrite <- H. apply H2. assumption.
          * intuition eauto. rewrite -> H. apply H2. assumption.
    Defined.

    Definition OpSpec_oalg : OrderedAlgebra Free.
      apply (mkOrderedAlgebra OpSpec_alg Prop_op_order).
      simpl. intros A k k' m H. induction m; intros t.
      - simpl. auto.
      - simpl in *. destruct t as [pre H1]. split.
        + assumption.
        + intros p post. apply H0. auto.
    Defined.

    Definition OpSpec := WPSpecMonad OpSpec_oalg.

    Definition OpSpecWP : Dijkstra OpSpec := D_wp _ _.

    Definition PrePostOp {A} (P : Prop) (Q : A -> Prop) :=
      OpSpecWP A (PrePostSpec P Q).

    Definition perform : forall s, PrePostOp (fst (OpSpecs s)) (snd (OpSpecs s)).
      intro s. exists (opr _ s (retFree _)).
      simpl. auto.
    Defined.

    Definition frameConj {A}{Pre}{I}{Q : A -> Prop} :
      PrePostOp Pre Q ->
      PrePostOp (Pre /\ I) (fun a => Q a /\ I).
    Proof.
      intro M. apply (wkn M).
      simpl. intuition eauto.
    Defined.

  End OperationSpecs.

End FreeMonad.
Arguments perform [S P OpSpecs].

(******************************************************************************************)
(* Specialising the Free monad to the IO monad                                            *)
(******************************************************************************************)
Section IO.

  Variable Inp : Type.
  Variable Oup : Type.

  Inductive IOop : Type := read : IOop | write : Oup -> IOop.
  Definition IOop_arity (op : IOop) : Type :=
    match op with
    | read => Inp
    | write _ => unit
    end.

  Definition IOSpec := HistorySpec IOop IOop_arity.
  Definition IO : Dijkstra IOSpec := FreeHist IOop IOop_arity.
  Definition read' : IO Inp _ := opHist _ _ read.
  Definition write' (o : Oup) : IO unit _ := opHist _ _ (write o).

  Definition mustHaveOccurredSpec (o : Oup) : IOSpec unit.
    exists (fun post history => In (existT _ (write o) tt) history /\ post tt history).
    simpl. intuition eauto.
  Defined.

  Definition mustHaveOccurred (o : Oup) : IO unit (mustHaveOccurredSpec o).
    refine (wkn (dret tt) _).
    simpl. intuition eauto.
  Defined.

  Variables oup1 oup2 : Oup.

  Definition print_sequence_spec : IOSpec unit.
    exists (fun post history => post tt (existT _ (write oup2) tt :: existT _ (write oup1) tt :: history)).
    simpl. eauto.
  Defined.

  Definition print_sequence : IO unit print_sequence_spec.
    refine (wkn (x <- write' oup1 ; write' oup2) _).
    simpl. intros k a H [] []. assumption.
  Defined.

  (* Print sequence with an assertion *)
  Program Definition print_sequence' : IO unit print_sequence_spec :=
    wkn (x <- write' oup1 ; y <- mustHaveOccurred oup1; write' oup2) _.
  Next Obligation.
    destruct p. split.
    - left. reflexivity.
    - intros []. assumption.
  Qed.

  (* Print sequence with an assertion and under specified: fails to
     check. *)
  Definition print_sequence_spec'' : IOSpec unit.
    exists (fun post history => forall history, post tt history).
    simpl. eauto.
  Defined.

  (* COrrectly, the proof fails ... 
  Program Definition print_sequence'' : IO unit print_sequence_spec'' :=
    wkn (y <- mustHaveOccurred oup1; write' oup2) _.
  Next Obligation.
    split. (* stuck here *)
   *)

End IO.


(******************************************************************************************)
(* Exceptions (the option monad)                                                          *)
(******************************************************************************************)
Section Exceptions.

  Definition Exc : Monad.
    apply (mkMonad
             (fun A => option A)
             (fun A a => Some a)
             (fun A B m f =>
                match m with
                | None => None
                | Some a => f a
                end)).
    - reflexivity.
    - destruct c; reflexivity.
    - intros. destruct c.
      + destruct (f a); reflexivity.
      + reflexivity.
  Defined.

  Definition throw {A} : Exc A := None.

  Section DoubleBarreled.

    Definition ExnSpecCarrier : Type -> Type :=
      fun X => { f : (option X -> Prop) -> Prop
               | forall (k k' : option X -> Prop), (forall a, k' a -> k a) -> f k' -> f k }.

    Definition ExnSpec_ret : forall A, A -> ExnSpecCarrier A.
      intros A a. exists (fun post => post (Some a)). eauto.
    Defined.

    Definition ExnSpec_bind :
      forall A B, ExnSpecCarrier A -> (A -> ExnSpecCarrier B) -> ExnSpecCarrier B.
    Proof.
      intros A B m f.
      exists (fun post => proj1_sig m (fun a => match a with
                                                | Some a => proj1_sig (f a) post
                                                | None => post None
                                                end)).
      destruct m. simpl. intros.
      apply (p (fun a => match a with Some a0 => proj1_sig (f a0) k | None => k None end)
               (fun a => match a with Some a0 => proj1_sig (f a0) k' | None => k' None end)).
      - intros [a|].
        + simpl. apply (proj2_sig (f a)). assumption.
        + auto.
      - assumption.
    Defined.

    Definition ExnSpecU : Monad.
      apply (mkMonad ExnSpecCarrier ExnSpec_ret ExnSpec_bind);
        intros; apply sig_eq.
      - reflexivity.
      - simpl. extensionality post. apply f_equal. extensionality a. destruct a; reflexivity.
      - simpl. extensionality post. apply f_equal. extensionality a. destruct a; reflexivity.
    Defined.

    Definition ExnSpec_order A : PreOrderOn (ExnSpecU A).
      apply (mkPreOrder
               _ (fun m1 m2 => forall (k : option A -> Prop), (proj1_sig m2 k : Prop) -> proj1_sig m1 k)).
      - intros. assumption.
      - intros. eauto.
    Defined.

    Definition ExnSpec : OrderedMonad.
      apply (mkOrderedMonad ExnSpecU ExnSpec_order).
      - simpl. intros. apply H.
        eapply (proj2_sig c'
                          (fun a => match a with Some a0 => proj1_sig (f a0) k | None => k None end)
                        (fun a => match a with Some a0 => proj1_sig (f' a0) k | None => k None end)).
        + intros [a|].
          * auto.
          * auto.
        + assumption.
    Defined.

    Definition ExnObservation_U A : Exc A -> ExnSpec A.
      intros [a|].
      - exists (fun post => post (Some a)). auto.
      - exists (fun post => post None). auto.
    Defined.

    Definition ExnObservation : MonadMorphism Exc ExnSpec.
      apply (mkMorphism Exc ExnSpec ExnObservation_U).
      - intros. reflexivity.
      - intros A B s f; apply sig_eq. destruct s; reflexivity.
    Defined.

    Definition ExnDB := Dalpha Exc ExnSpec ExnObservation.

  End DoubleBarreled.

  (******************************************************************************************)
  (* This does exceptions with a pre-chosen exceptional post-condition, as in the           *)
  (* discussion at the end of Section 3.2                                                   *)
  (******************************************************************************************)
  Section PureExnSpecs.

    Variable Q_exn : Prop.

    Definition Exc_alg : MonadAlgebra Exc.
      apply (mkMonadAlgebra Exc Prop
                            (fun c => match c with Some p => p | None => Q_exn end)).
      - intros c. simpl. reflexivity.
      - intros X m f. destruct m; simpl.
        + destruct (f x); reflexivity.
        + reflexivity.
    Defined.

    Definition Exc_oalg : OrderedAlgebra Exc.
      apply (mkOrderedAlgebra Exc_alg Prop_op_order).
      simpl. intros A k k' [a|] H H1; auto.
    Defined.

    Definition ExcSpec := WPSpecMonad Exc_oalg.

    Definition ExcWP : Dijkstra ExcSpec := D_wp _ _.

    Definition PrePostExcSpec {A} (P : Prop) (Q : A -> Prop) :
      ExcSpec A.
    Proof.
      exists (fun (Z : A -> Prop) => P /\ forall a, Q a -> Z a).
      simpl. intuition eauto.
    Defined.

    Definition PrePostExc {A} P (Q : A -> Prop) :=
      ExcWP A (PrePostExcSpec P Q).

    Definition throw' {A} : ExcWP A _ :=
      lift Exc ExcSpec _ (@throw A).

    Lemma soundnessExc {A} P Q : forall (c : @PrePostExc A P Q),
        P -> match underlying c with
             | None => Q_exn
             | Some a => Q a
             end.
    Proof.
      destruct c as [f H]. simpl in *.
      intros pre_ok.
      destruct f; apply (H Q); auto.
    Qed.

  End PureExnSpecs.

End Exceptions.

Definition catchSpec {Q_exn'} {A B} :
  forall (P : Prop) (Q : A -> Prop) (Q_exn : Prop),
  (A -> ExcSpec Q_exn' B) ->
  ExcSpec Q_exn' B ->
  ExcSpec Q_exn' B.
Proof.
  intros P Q Q_exn wp_ret wp_exn.
  exists (fun post => P
                      /\ (forall a, Q a -> proj1_sig (wp_ret a) post)
                      /\ (Q_exn -> proj1_sig wp_exn post)).
  intros k k' H.
  simpl in *.
  intros [H1 [H2 H3]]. split; [|split].
  - assumption.
  - intros a. set (H4:=H2 a). generalize H4. clear H4. intro H4. destruct (wp_ret a). simpl in *. eauto.
  - destruct wp_exn. simpl in *. eauto.
Defined.

Definition catch {Q_exn Q_exn'} {A B} {P Q} {wp_success: A -> ExcSpec Q_exn' B} {wp_exn} :
  PrePostExc Q_exn P Q ->
  (forall a, ExcWP Q_exn' B (wp_success a)) ->
  (ExcWP Q_exn' B wp_exn) ->
  ExcWP Q_exn' B (catchSpec P Q Q_exn wp_success wp_exn).
Proof.
  intros M N_ret N_exn.
  destruct M as [[a|] M_spec]; simpl in M_spec.
  - apply (wkn (N_ret a)).
    simpl. intros k [H1 [H2 _]]. apply M_spec. auto.
  - apply (wkn N_exn).
    simpl. intros k [H1 [_ H2]]. apply H2. eauto.
Defined.

Definition catch2 {Q_exn Q_exn'} {A B} {P} {Q : A -> Prop} {R : B -> Prop} :
  PrePostExc Q_exn P Q ->
  (forall a, PrePostExc Q_exn' (Q a) R) ->
  PrePostExc Q_exn' Q_exn R ->
  PrePostExc Q_exn' P R.
Proof.
  intros M H_ret H_exn.
  destruct M as [[a|] M_spec]; simpl in M_spec.
  - apply (wkn (H_ret a)).
    simpl. intros k [H1 H2]. split.
    + apply M_spec. auto.
    + assumption.
  - apply (wkn H_exn).
    simpl. intros k [H1 H2]. split.
    + eauto.
    + assumption.
Defined.


Definition test1 {A B P} {Q : A -> Prop} {Q_exn wp2}
           (c1 : PrePostExc Q_exn P Q)
           (c2 : forall a, ExcWP Q_exn B (wp2 a))
  : ExcWP Q_exn B (bind (PrePostExcSpec Q_exn P Q) wp2).
  DPROG (catch c1 c2 (throw' _)).
  intuition.
Defined.

(******************************************************************************************)
(* An alternative attempt to do Handlers to the one described in the paper                *)
(******************************************************************************************)
Section Handler.

  Variable S : Type.
  Variable P : S -> Type.
  Variable S' : Type.
  Variable P' : S' -> Type.

  Variable Inner : forall s, Prop * (P s -> Prop).
  Variable Outer : forall s, Prop * (P' s -> Prop).

  (* FIXME: does this generalise to more general outer Dijkstra monads? *)
  (* FIXME: does this generalise to when we have some kind of ghost state
     for the handler? *)

  Definition handle {A B}{Pre : Prop}{Q : A -> Prop}{R : B -> Prop}
             (M    : PrePostOp S P Inner Pre Q)
             (Hret : forall a, PrePostOp S' P' Outer (Q a) R)
             (Hops : forall (I : Prop) s,
                 (forall p, PrePostOp S' P' Outer (I /\ snd (Inner s) p) R) ->
                 PrePostOp S' P' Outer (I /\ fst (Inner s)) R)
    : PrePostOp S' P' Outer Pre R.
  Proof.
    destruct M as [comp comp_ok].
    generalize Pre comp_ok. clear Pre comp_ok.
    induction comp; intros Pre comp_ok.
    - DPROG (Hret a).
      intros k [pre_ok H]. split.
      + apply comp_ok. simpl. auto.
      + assumption.
    - simpl in comp_ok.
      refine
        (wkn (Hops Pre s (fun p => wkn (X p (Pre /\ snd (Inner s) p) _) _)) _);
        simpl.
      + intros k [[H1 H2] H3]. apply comp_ok; auto.
      + intros k [[H1 H2] H3]. eauto.
      + intros k [H1 H2]. simpl in comp_ok.
        destruct (comp_ok Q (conj H1 (fun a q => q))).
        intuition eauto.
  Defined.

  (* Post-hoc proof version *)
  Definition handle' {A B}{Pre : Prop}{Q : A -> Prop}{R : B -> Prop}
             (M    : PrePostOp S P Inner Pre Q)
             (Hret : forall a, PrePostOp S' P' Outer (Q a) R)
             (Hops : forall s, (forall (p : P s), Free S' P' B) -> Free S' P' B)
             (Hops' : forall s f,
                 (forall p, mLE (mor _ (OpSpec_oalg S' P' Outer) _ (f p))
                                (PrePostSpec (snd (Inner s) p) R)) ->
                 mLE (mor _ (OpSpec_oalg S' P' Outer) _ (Hops s f))
                     (PrePostSpec (fst (Inner s)) R))
    : PrePostOp S' P' Outer Pre R.
  Proof.
    destruct M as [comp comp_ok].
    exists ((fix handle (m:Free S P A) : Free S' P' B :=
              match m with
              | retFree _ _ _ a => proj1_sig (Hret a)
              | opr _ _ _ s k => Hops s (fun p => handle (k p))
              end) comp).
    simpl.
    intros k [H1 H2].
    generalize k H2. clear k H2.
    induction comp; intros.
    - destruct (Hret a) as [Hret_a Hret_a_ok]. simpl.
      apply Hret_a_ok. apply comp_ok. simpl. eauto.
    - apply Hops'.
      + intros p k0 [H3 H4]. simpl. apply H.
        * simpl. intros k1 H5. apply comp_ok; eauto.
        * assumption.
      + simpl. destruct (comp_ok Q (conj H1 (fun a q => q))). auto.
  Defined.

End Handler.
Arguments handle [S P S' P' Inner Outer A B Pre Q R].

Section FwdHandler.

  Variable S : Type.
  Variable P : S -> Type.

  Variable OpSpec : forall s, Prop * (P s -> Prop).

  Definition all_fwd {A}{Pre : Prop}{Q : A -> Prop}
             (M : PrePostOp S P OpSpec Pre Q)
    : PrePostOp S P OpSpec Pre Q.
    refine (handle M
                   (fun a => wkn (dret a) _)
                   (fun I s resume =>
                      wkn (p <- perform s; resume p) _)).
    - simpl. intuition eauto.
    - simpl. intuition eauto.
  Defined.

End FwdHandler.

Section ExnHandler.

  Inductive exn_op : Type := raise : exn_op.
  Definition exn_ty (op : exn_op) : Type :=
    match op with
    | raise => False
    end.

  Variable Q_exn : Prop.
  Definition exn_spec (op : exn_op) : Prop * (exn_ty op -> Prop) :=
    match op with
    | raise => (Q_exn, fun (emp : False) => match emp with end)
    end.

  Variable S' : Type.
  Variable P' : S' -> Type.
  Variable Outer : forall s, Prop * (P' s -> Prop).

  Definition catch_gen {A B} {Pre} {Q : A -> Prop} {R : B -> Prop}
             (M    : PrePostOp exn_op exn_ty exn_spec Pre Q)
             (Hret : forall a, PrePostOp S' P' Outer (Q a) R)
             (Hexn : PrePostOp S' P' Outer Q_exn R)
    : PrePostOp S' P' Outer Pre R.
  Proof.
    refine (handle M Hret
                   (fun I s resume =>
                      match s with
                      | raise => wkn Hexn _
                      end)).
    - simpl. intuition eauto.
  Defined.

End ExnHandler.

Definition throw'' {A}{P : Prop}{wp} :
  P -> OpSpecWP exn_op exn_ty (exn_spec P) A wp.
Proof.
  intro p. exists (opr _ _ _ raise (fun (x:False) => match x with end)).
  simpl. intuition eauto.
Defined.

Definition div (i j : Z) :
  PrePostOp exn_op exn_ty (exn_spec (j = 0%Z))
            True (fun n => j <> 0%Z /\ n = Zdiv i j).
Proof.
  destruct (Z_eq_dec j 0).
  - apply (throw'' e).
  - refine (wkn (dret (Zdiv i j)) _); simpl.
    simpl. intuition eauto.
Defined.

Definition try_div (i j : Z) :
  PrePostOp exn_op exn_ty (exn_spec False)
            True (fun (n : option Z) => True).
Proof.
  refine (handle (div i j)
                 (fun a => wkn (dret (Some a)) _)
                 (fun I s resume =>
                    wkn (dret None) _)).
  - simpl. intuition eauto.
  - simpl. intuition eauto.
Defined.

Section FwdingExnHandler.

  Variable S : Type.
  Variable P : S -> Type.
  Variable Inner : forall s, Prop * (P s -> Prop).

  Inductive exn' : Type := raise' : exn' | old : S -> exn'.
  Definition exn'_ty (op : exn') : Type :=
    match op with
    | raise' => False
    | old s  => P s
    end.

  Variable Q_exn : Prop.
  Definition exn'_spec (op : exn') : Prop * (exn'_ty op -> Prop) :=
    match op with
    | raise' => (Q_exn, fun (emp : False) => match emp with end)
    | old s  => Inner s
    end.

  Definition catch_fwd {A B} {Pre} {Q : A -> Prop} {R : B -> Prop}
             (M    : PrePostOp exn' exn'_ty exn'_spec Pre Q)
             (Hret : forall a, PrePostOp S P Inner (Q a) R)
             (Hexn : PrePostOp S P Inner Q_exn R)
    : PrePostOp S P Inner Pre R.
  Proof.
    refine (handle M Hret
                   (fun I s =>
                      match s with
                      | raise' => fun resume => wkn Hexn _
                      | old s  => fun resume => wkn (p <- perform s; resume p) _
                      end)).
    - simpl. intuition eauto.
    - simpl. intuition eauto.
  Defined.

End FwdingExnHandler.


Section ConstantChoiceHandler.

  (* A choice handler that always replies 'true', per its spec. *)

  Inductive choice_op : Type := choice : choice_op.
  Definition choice_ty (op : choice_op) :=
    match op with
    | choice => bool
    end.

  Definition choice_spec (op : choice_op) : Prop * (choice_ty op -> Prop) :=
    match op with
    (* Specify that 'choice' always returns 'true' *)
    | choice => (True, fun b => b = true)
    end.

  Variable S' : Type.
  Variable P' : S' -> Type.
  Variable Outer : forall s, Prop * (P' s -> Prop).

  Definition always_true_handler {A}{Pre}{Q : A -> Prop}
             (M : PrePostOp choice_op choice_ty choice_spec Pre Q)
    : PrePostOp S' P' Outer Pre Q.
  Proof.
    refine (handle M
                   (fun a => wkn (dret a) _)
                   (fun I op =>
                      match op with
                      | choice => fun resume =>
                                    wkn (resume true) _
                      end)).
    - simpl. intuition eauto.
    - simpl. intuition eauto.
  Defined.

End ConstantChoiceHandler.

Section StateHandler.

  (* This doesn't work... *)

  Inductive state_op := get_op : state_op | put_op : nat -> state_op.
  Definition state_ty (op : state_op) :=
    match op with
    | get_op   => nat
    | put_op _ => unit
    end.
  Definition state_spec (op : state_op) : Prop * (state_ty op -> Prop) :=
    (True, fun _ => True).

  Variable S' : Type.
  Variable P' : S' -> Type.
  Variable Outer : forall s, Prop * (P' s -> Prop).

  Definition state_handler {A}{Pre}{Q : A -> Prop}
             (M : PrePostOp state_op state_ty state_spec Pre Q)
    : PrePostOp S' P' Outer Pre
                (fun (t : nat -> PrePostOp S' P' Outer True Q) => True).
  Proof.
    apply (handle M).
    - intros a.
  Abort. (* :( I think I need to do parameterised handlers instead. *)

End StateHandler.

(********************************************************************************)
(*                                                                              *)
(*    Functions polymorphic in the Dijkstra monad                               *)
(*                                                                              *)
(********************************************************************************)

Section DijkstraMonadPolymorphic.
  Context W (D:Dijkstra W).
  Import ListNotations.
  
  Section ListMap.
    Fixpoint list_mapW {A B} (w : A -> W B) (l : list A) : W (list B) :=
      match l with
      | [] => ret []
      | a :: l => bind (w a) (fun b => bind (list_mapW w l) (fun bs => ret (b :: bs)))
      end.

    Fixpoint list_mapD {A B w} (f:forall a:A, D B (w a)) (l : list A)
      : D (list B) (list_mapW w l) :=
      match l with
      | [] => dret []
      | a :: l => b <- f a ; bs <- list_mapD f l ; dret (cons b bs)
      end.
  End ListMap.

  Section Fold.
    Context A B (w : A -> B -> W B) (inv : W B) 
            (Hinv : forall a, omon_order W (bind inv (w a)) inv).
    Let w' a wb := bind wb (w a).
    Lemma fold_inv : forall l, omon_order W (fold_right w' inv l) inv.
    Proof.
      induction l as [|a l IH] ; simpl.
      apply preo_refl.
      simple refine (preo_trans _ _ _ (bind inv (w a)) _ _ _).
      apply omon_bind. assumption. intros ; apply preo_refl.
      apply Hinv.
    Qed.

    Context (unit : D B inv) (f : forall a b, D B (w a b)).

    Fixpoint foldD l : D B (fold_right w' inv l) :=
      match l with
      | [] => unit
      | a :: l => b <- foldD l ; f a b
      end.

    Definition foldD_inv l := wkn (foldD l) (fold_inv l). 
      
  End Fold.

  Section For.
    Context (start len : nat) (inv : W unit)
            (Hinv : omon_order W (bind inv (fun _ => inv)) inv).

    Let bounded_nat := { i : nat | start <= i < start + len }.

    Program Fixpoint bseq (len' : nat) (Hlen : len' <= len) : list bounded_nat :=
      match len' with
      | 0 => []
      | S len0 => (exist _ start _) :: bseq len0 _
      end.
    Next Obligation. intuition. Qed.
    Next Obligation. apply le_Sn_le. assumption. Qed.

    Context (Hinv0 : omon_order W (ret tt) inv).

    Program Definition for_inv (f : forall i, start <= i < start + len -> D unit inv)
      : D unit inv :=
      foldD_inv bounded_nat unit (fun _ _ => inv) inv _ (wkn (dret tt) Hinv0)
                (fun 'i _ => f i _) (bseq len _).
    Next Obligation. exact (proj2_sig i0). Qed.
      
  End For.

  Notation "'For' i 'from' start 'to' endc 'using' inv 'do' c 'done'" :=
    (for_inv start (endc - start) inv _ _ (fun i Hi => c))
      (at level 0, i ident).

  Program Definition stupid := For i from 0 to 5 using ret tt do dret tt done.  
  Next Obligation. rewrite monad_law1. apply preo_refl. Qed.
  Next Obligation. apply preo_refl. Qed.

End DijkstraMonadPolymorphic.

Section ForState.

  Notation "'For' i 'from' start 'to' endc 'using' inv 'do' c 'done'" :=
    (for_inv _ (StateWP nat) start (endc - start) inv _ _ (fun i Hi => c))
      (at level 0, i ident).

  Program Definition sum :=
    For i from 0 to 5 using PrePostWP nat (fun _ => True) (fun s0 s1 => s0 <= s1) do
        s0 <- get' ; put' (s0 + i) 
        done.
  Next Obligation. intuition. Qed.
  Next Obligation. apply H0. omega. Qed.

End ForState.