From SM Require Export Base TypeCatSpecialized.

From Coq Require Import FunctionalExtensionality.
From Coq.Logic Require Import EqdepFacts.

Set Primitive Projections.

(** Monadic structures and notations specialized to Type_Cat *)

Import MonadNotations.


(* Existing Instance Type_Cat. *)

Section DijkstraMonad.
  Context (W : Type -> Type) `{@KleisliMonad W}.


  Class DijkstraMonad :=
    {
      (* D A (w : W A) *)
      dm_func : forall A, W A -> Type ;
      (* x:A -> D A (retW x) *)
      dm_ret : forall {A} (x:A), dm_func A (ret x);
      dm_bind : forall {A B w2 (*A -> W B*) w1}
                  (f : forall (x:A), dm_func B (w2 x))
                  (m : dm_func A w1), dm_func B (w1 ≫= w2);

      dm_unitl : forall {A B} x w (f: forall (x:A), dm_func B (w x)),
          dm_bind f (dm_ret x) =⟨unitl w x⟩ f x ;
      dm_unitr : forall {A} w (m:dm_func A w),
          dm_bind dm_ret m =⟨ unitr w ⟩ m ;
      dm_assoc : forall {A B C} w1 w2 w3 (m1:dm_func A w1) (m2:forall (x:A), dm_func B (w2 x)) (m3:forall (y:B), dm_func C (w3 y)),
          dm_bind (fun x => dm_bind m3 (m2 x)) m1
          =⟨ assoc w2 w3 w1 ⟩ dm_bind m3 (dm_bind m2 m1)
    }.

  Section DijkstraMonadMap.
    Context `(Djm : DijkstraMonad).

    Notation D := dm_func.

    Context {A B} (f : A -> B).

    Definition dm_map {w : W A} (m : D A w) : D B (f <$> w) :=
      dm_bind (fun x => dm_ret (f x)) m.

  End DijkstraMonadMap.

End DijkstraMonad.

Arguments dm_ret {_ _ _ _} _.
Arguments dm_bind {_ _ _ _ _ _ _} _ _.
Notation "m ⋙= f" := (dm_bind f m) (at level 60, right associativity).
Notation "f ≪$≫ c" := (dm_map _ _ f c) (at level 60).


Section DijkstraMonadMorphism.

  (** Morphism between Dijkstra monads over the same monad W *)
  Context (W1 W2 : Type -> Type).
  Context `{KleisliMonad W1} `{KleisliMonad W2}.
  Context {θW : MonadMorphism (TF W1) (TF W2)}.

  Context {Djm1 : DijkstraMonad W1} {Djm2 : DijkstraMonad W2}.

  Notation D1 := (dm_func W1).
  Notation D2 := (dm_func W2).

  Class DijkstraMonadMorphism :=
    {
      dmmorph_trans : forall {A} {w : W1 A}, D1 A w -> D2 A (trans_monad θW _ w) ;

      dmmorph_com : forall {A B} (f : A -> B) w (m : D1 A w),
          dmmorph_trans (f ≪$≫ m)
            =⟨ mmorph_map θW f _⟩
          (f ≪$≫ dmmorph_trans m) ;
      
      dmmorph_unit : forall A (x:A),
          dmmorph_trans (dm_ret x)
            =⟨ mmorph_unit _ _ ⟩
          dm_ret x ;

      dmmorph_bind : forall A B wf wm (f : forall (x:A), D1 B (wf x)) (m : D1 A wm),
          ((dmmorph_trans m) ⋙= (fun x => dmmorph_trans (f x)))
            =⟨mmorph_bind θW _ wf wm⟩
          dmmorph_trans (m ⋙= f)
    }.

End DijkstraMonadMorphism.
(* (fun x => dmmorph_trans (dm_ret (f x))) =⟨ fun x => mmorph_unit _ _ ⟩ (fun x => dm_ret (f x)) *)


Section MonadMorphismToDijkstraMonad.

  Context (M W : Type -> Type).
  Context `{HM:KleisliMonad M} `{HW:KleisliMonad W}.

  (* Existing Instance Monad_from_KleisliMonad. *)

  Context (θ:MonadMorphism (TF M) (TF W)).

  Notation θ0 := (trans_monad θ _).
  
  Definition D A (w:W A) := { m : M A ∥ θ0 m = w }.

  Variable W_UIP : forall A, UIP_ (W A). 


  Program Instance MonadMorphismToDijkstraMonad : DijkstraMonad W :=
    {|
      dm_func := D ;
      dm_ret := ltac:(intros A x ; exists (ret x)) ;
      dm_bind := 
        ltac:(intros A B w2 w1 f [c0 e0]; exists (c0 ≫= fun x => wit (f x)))
    |}.
  Next Obligation.
    let t := eval cbv in (mmorph_unit θ) in apply t.
  Qed.

  Next Obligation.
    rewrite <- (mmorph_bind θ _ _ c0).
    f_equal; [extensionality x; exact (pf (f x))| assumption].
  Qed.

  (* monadic laws*)
  Solve All Obligations with
      intros; apply (eq_above_subtype θ0 (W_UIP _)) ;
    first [exact (unitl _ _)| exact (unitr _)| exact (assoc _ _ _)].

End MonadMorphismToDijkstraMonad.

Section DijkstraMonadToMonadMorphism.
  Context (W : Type -> Type) `{DijkstraMonad W}.

  Definition TotalM (A:Type) : Type := { w : W A ⫳ dm_func _ A w }. 
  Program Instance TotalMTriple : KleisliMonad TotalM :=
    {|
      Monad.ret A x := {| dfst := ret x ; dsnd := dm_ret x |} ;
      Monad.bind A B f m := {|
                             dfst := dfst m ≫= (fun x => dfst (f x)) ;
                             dsnd := dsnd m ⋙= (fun x => dsnd (f x))
                           |}
    |}.

  Solve All Obligations with
      intros; cbv; extensionality x ;
    unshelve eapply eq_eq_above_eq_nsigT; simpl ;
      first [
    exact (unitl _ _) |
    exact (unitr _) |
    exact (assoc _ _ _) |
    exact (dm_unitl _ _ _ _) |
    exact (dm_unitr _ _ _) |
    exact (dm_assoc _ _ _ _ _ _ _)].

  Existing Instance Monad_from_KleisliMonad.

  Program Definition morphism_TotalM_W : MonadMorphism (TF TotalM) (TF W) :=
    {|
      monad_morph :=
        {|
          NatTrans.NatTrans.Trans A m := dfst m 
        |}
    |}.

  Next Obligation.
    apply NatTrans.NatTrans.NatTrans_eq_simplify ; simpl.
    extensionality A ; extensionality mm.
    rewrite <- (assoc _ _ _); f_equal; extensionality x.
    rewrite (unitl _ _) ; trivial.
  Qed.

End DijkstraMonadToMonadMorphism.


(** Not updated yet, does it make any sense to update ?*)

(* Same thing as the previous but using positive subset type *)
(* The proofs are heavier due to the absence of η *)
(*     (compare dijkstra_monad_D) *)
(* Section MonadMorphismToDijkstraMonad. *)

(*   Variables M W : Type -> Type. *)
(*   Variable θ : forall A, M A -> W A. *)
(*   Arguments θ {_} _. *)

(*   Definition D A (w:W A) := { m : M A | θ m = w }. *)

(*   Context `{MonadMorphism _ _ (@θ)}. *)

(*   Global Instance dmret_D : DMRet _ D. *)
(*   Proof. *)
(*     intros A x ; exists (mret x). exact (mmorph_unit _ _ _ A x). *)
(*   Defined. *)

(*   Global Instance dmbind_D : DMBind _ D. *)
(*   Proof. *)
(*     intros A B w2 w1 f [c0 e0]. *)
(*     pose (g := fun x => proj1_sig (f x)). *)
(*     exists (c0 ≫= g). *)
(*     rewrite (mmorph_bind _ _ _ A B g c0). *)
(*     rewrite e0 ; f_equal. *)
(*     extensionality x; cbv ; destruct (f x) ; assumption. *)
(*   Defined. *)

(*   Lemma transport_sig : forall {A B} (F : B -> A -> Prop) {x y} h z, *)
(*       eq_rect x (fun x => {b : B | F b x}) z y h *)
(*       = exist (fun b => F b y) (proj1_sig z) (@eq_ind A x (F (proj1_sig z)) (proj2_sig z) y h). *)
(*   Proof. *)
(*     intros. *)
(*     dependent inversion h. *)
(*     destruct z. *)
(*     reflexivity. *)
(*   Qed. *)

(*   Variable W_UIP : forall A, UIP_ (W A).  *)

(*   Lemma eq_above_sig1_hset {A} {w1 w2 : W A} {h : w1 = w2} *)
(*         {z1 : D A w1} {z2 : D A w2} : *)
(*     proj1_sig z1 = proj1_sig z2 -> z1 =⟨ h ⟩ z2. *)
(*   Proof. *)
(*     intro Hz. *)
(*     unfold eq_above. *)
(*     change (D A) with (fun w => D A w). *)
(*     unfold D. *)
(*     rewrite (transport_sig (fun m w => θ m = w) h z1). *)
(*     destruct z2. *)
(*     apply eq_dep_eq_sig. *)
(*     apply eq_dep1_dep. *)
(*     simpl in Hz. symmetry in Hz. *)
(*     apply (eq_dep1_intro _ _ _ _ _ _ Hz). *)
(*     apply W_UIP. *)
(*   Qed. *)

(*   Context `{@Monad M _ _} `{@Monad W _ _}. *)

(*   Global Instance dijkstra_monad_D : DijkstraMonad _ D. *)
(*   Proof. *)
(*     constructor; intros; apply (eq_above_sig1_hset). *)
(*     - exact (unitl _ _ _ _ _). *)
(*     - destruct m ; exact (unitr _ _ _). *)
(*     - destruct m1. *)
(*       assert (Hm2 : m2 = fun x => exist _ (proj1_sig (m2 x)) (proj2_sig (m2 x))). *)
(*       extensionality y ; destruct (m2 y) ; reflexivity. *)
(*       rewrite Hm2; exact (assoc _ _ _ _ _ _ _). *)
(*   Qed. *)

(* End MonadMorphismToDijkstraMonad. *)

