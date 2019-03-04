From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import NatTrans.Main.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
From Categories Require Import Functor.Representable.Hom_Func.
From Categories Require Import Basic_Cons.CCC.

Local Open Scope morphism_scope.


Section Monad.

  Context {C : Category} (T : (C –≻ C)%functor).

  Let idT := NatTrans_id T.

  Local Open Scope nattrans.

  Class Monad : Type :=
    MkMonad {
      (** Monad operations *)
      η (* Monad_Unit *) : Functor_id C –≻ T ;
      μ (* Monad_Mult *) : T ∘ T –≻ T ;
      (* Syntactic helpers *)
      (* μ := Monad_Mult ; η := Monad_Unit ; *)

      (** Monad laws *)
      (* μ ∘ T η = id *)
      Monad_Left_Unit : μ ∘ (idT ∘_h η) ∘ NatTrans_to_id_compose T = idT ;
      (* μ ∘ η T = id *)
      Monad_Right_Unit : μ ∘ (η ∘_h idT) ∘ NatTrans_to_compose_id T = idT ;
      (* μ ∘ T μ = μ ∘ μ T *)
      Monad_Associativity : μ ∘ (idT ∘_h μ) ∘ NatTrans_Functor_assoc T T T = μ ∘ (μ ∘_h idT)
    }  .

End Monad.

Arguments η {_ _ _}.
Arguments μ {_ _ _}.

Section TransComp.
  Context {C D:Category} {T1 T2 : (C –≻ D)%functor}.
  Context {θ1 θ2 : NatTrans T1 T2}.

  Definition trans_comp A (H : θ1 = θ2) : Trans θ1 A = Trans θ2 A :=
    f_equal (fun h => Trans h A) H.
End TransComp.


Section MonadLawsPointwise.
  Context {C : Category} (T : (C –≻ C)%functor) `{@Monad _ T} (A:C).

  Lemma monad_left_unit : Trans μ A ∘ (T _a) (Trans η A) = id.
  Proof.
    set (H0 :=trans_comp A (Monad_Left_Unit T)). 
    cbn in H0. simpl_ids in H0.
    exact H0.
  Qed.
    
  Lemma monad_right_unit : Trans μ A ∘ (Trans η (T _o A)) = id.
  Proof.
    set (H0 :=trans_comp A (Monad_Right_Unit T)). 
    cbn in H0 ; rewrite F_id in H0. simpl_ids in H0.
    exact H0.
  Qed.

  Lemma monad_assoc : Trans μ A ∘ Trans μ (T _o A) = Trans μ A ∘ T _a (Trans μ A).
  Proof.
    set (H0 :=trans_comp A (Monad_Associativity T)). 
    cbn in H0. rewrite F_id in H0. simpl_ids in H0.
    symmetry ; exact H0.
  Qed.
End MonadLawsPointwise.


Section IdentityMonad.
  Context {C:Category}.

  Program Instance IdentityMonad : Monad (Functor_id C) :=
    {| η := NatTrans_id (Functor_id C) ;
       μ := NatTrans_from_id_compose (Functor_id C) |}.
  Solve Obligations with
    apply NatTrans_eq_simplify ; cbn ; extensionality x ; simpl_ids ; trivial.
End IdentityMonad.


Section KleisliMonad.
  Context {C : Category} (T : C -> C).

  Class KleisliMonad :=
    MkKleisliMonad {
      (** Monad operations *)
      ret (* Kleisli_Monad_Return *) : forall (A:C), A –≻ T A ;
      bind (* Kleisli_Monad_Bind *) : forall (A B : C), (A –≻ T B) -> (T A –≻ T B) ;
      (* Syntax helpers *)
      (* ret := Kleisli_Monad_Return ; *)
      (* bind := Kleisli_Monad_Bind ; *)

      (** Monad laws *)
      Kleisli_Monad_Left_Unit : forall A B (f : A –≻ T B), bind _ _ f ∘ ret _ = f ;
      Kleisli_Monad_Right_Unit : forall (A:C), bind _ _(ret A) = id (T A) ;
      Kleisli_Monad_Associativity : forall A B C (f : A –≻ T B) (g : B –≻ T C),
        bind _ _ (bind _ _ g ∘ f) = bind _ _ g ∘ bind _ _ f
    }.

  Arguments bind {_ _ _} _.

  Context `{KleisliMonad}.

  Program Definition TF : Functor C C :=
    {|
      FO := T ;
      FA := fun {a b} f => bind (ret b ∘ f)
    |}.
  Next Obligation.
    rewrite id_unit_right.
    exact (Kleisli_Monad_Right_Unit _).
  Qed.
  Next Obligation.
    rewrite <- (Kleisli_Monad_Associativity).
    rewrite <- !assoc. 
    rewrite (Kleisli_Monad_Left_Unit).
    reflexivity.
    all: assumption.
  Qed.

  Global Program Instance Monad_from_KleisliMonad : Monad TF :=
    {|
      η := {| Trans := ret |} ;
      μ := {| Trans := (fun c => bind (id (T c))) |}  |}.
  Solve Obligations with
      try (intros; simpl; rewrite (Kleisli_Monad_Left_Unit); reflexivity) ;
    try (intros; simpl;
            rewrite <- !(Kleisli_Monad_Associativity);
            rewrite <- !assoc;
            rewrite (Kleisli_Monad_Left_Unit) ;
            simpl_ids;
            trivial).

  Next Obligation with simpl_ids.
    apply NatTrans_eq_simplify ; cbn ; extensionality x...
    rewrite <- (Kleisli_Monad_Associativity).
    rewrite <- assoc.
    rewrite (Kleisli_Monad_Left_Unit)...
    apply (Kleisli_Monad_Right_Unit). 
  Qed.

  Next Obligation with simpl_ids.
    apply NatTrans_eq_simplify ; cbn ; extensionality x...
    intros; simpl ; rewrite !(Kleisli_Monad_Left_Unit) ; reflexivity.
  Qed.

  Next Obligation with simpl_ids.
    apply NatTrans_eq_simplify ; cbn ; extensionality x...
    rewrite <- (Kleisli_Monad_Associativity).
    rewrite <- assoc.
    rewrite !(Kleisli_Monad_Left_Unit). 
    rewrite !(Kleisli_Monad_Right_Unit)... 
    rewrite <- (Kleisli_Monad_Associativity)...
    reflexivity.
  Qed.

  Lemma bind_from_mul_map : forall {A B} (f: A –≻ T B),
      bind f = Trans μ B ∘ (TF _a f).
  Proof.
    intros ; cbv.
    rewrite <- (Kleisli_Monad_Associativity)...
    rewrite <- assoc.
    rewrite (Kleisli_Monad_Left_Unit). 
    f_equal ; simpl_ids.
    trivial.
  Qed.

  Lemma map_from_bind_ret : forall {A B} (f : A –≻ B),
      TF _a f  = bind (ret _ ∘ f).
  Proof. reflexivity. Qed.

    (* (Hom_Func C ∘ Prod_Functor (Functor_id C) T –≻ Hom_Func C ∘ Prod_Functor T T)%nattrans *)
End KleisliMonad.

Section IdentityTriple.
  Context {C:Category}.

  Definition Id : C -> C := fun c => c.

  Program Instance IdentityTriple : KleisliMonad Id :=
    MkKleisliMonad Id (fun c => @id C c) (fun _ _ f => f) _ _ _.
End IdentityTriple.

Section KleisliMonadFromMonad.
  Context {C:Category} (T : (C –≻ C)%functor) `{@Monad _ T}.

  Program Instance KleisliMonadFromMonad : KleisliMonad (FO T) :=
    {| ret := Trans η ; bind := fun X Y f => Trans μ Y ∘ T _a f |}.
  Next Obligation with simpl_ids.
    rewrite assoc. rewrite (Trans_com_sym η f).
    cbn. rewrite assoc_sym. rewrite (monad_right_unit T B)...
    trivial.
  Qed.

  Next Obligation. exact (monad_left_unit T _). Qed.

  Next Obligation.

    rewrite assoc. rewrite F_compose.
    rewrite !assoc_sym.
    rewrite <- (monad_assoc T C0).
    rewrite F_compose.
    rewrite !assoc_sym. f_equal.
    rewrite !assoc. rewrite (@Trans_com_sym _ _ _ T μ _ _ g). reflexivity.
  Qed.

End KleisliMonadFromMonad.



Section MonadMorphisms.
  Context {C : Category} (T1 T2 : (C –≻ C)%functor).
  Context `{@Monad _ T1} `{@Monad _ T2}.

  Local Open Scope nattrans.

  Record MonadMorphism :=
    MkMonadMorphism {
      monad_morph : T1 –≻ T2 ;
      Monad_Unit_com : monad_morph ∘ η = η ; 
      Monad_Mult_com : monad_morph ∘ μ = μ ∘ (monad_morph ∘_h monad_morph)
    }.

End MonadMorphisms.

Section MonadMorphism_id.
  Context {C : Category} (T : (C –≻ C)%functor) `{@Monad _ T}.
  
  Program Definition MonadMorphism_id : MonadMorphism T T :=
    MkMonadMorphism _ _ (NatTrans_id T) _ _.
  
  Solve Obligations with
    apply NatTrans_eq_simplify ; cbn ; extensionality x ;
      try (rewrite F_id) ; simpl_ids ; trivial.

End MonadMorphism_id.

Section MonadMorphism_comp.
  Context {C : Category} {T1 T2 T3 : (C –≻ C)%functor}.
  Context `{@Monad _ T1} `{@Monad _ T2} `{@Monad _ T3}.
  Context (θ12 : MonadMorphism T1 T2) (θ23 : MonadMorphism T2 T3).

  Program Definition MonadMorphism_comp : MonadMorphism T1 T3 :=
    MkMonadMorphism _ _ (monad_morph T2 T3 θ23 ∘ monad_morph T1 T2 θ12)%nattrans _ _.
  Next Obligation.
    rewrite NatTrans_compose_assoc; erewrite !(Monad_Unit_com) ; trivial.
  Qed.

  Next Obligation.
    rewrite NatTrans_compose_assoc.
    erewrite (Monad_Mult_com).
    rewrite <- NatTrans_compose_assoc.
    erewrite (Monad_Mult_com).
    rewrite !NatTrans_compose_assoc.
    rewrite NatTrans_comp_hor_comp.
    reflexivity.
  Qed.

End MonadMorphism_comp.

Section SimplifyMonadMorphisms.
  Context {C:Category} {T1 T2:(C –≻ C)%functor}.
  Context `{@Monad _ T1} `{@Monad _ T2}.
  Context (θ θ' : MonadMorphism T1 T2).

  Lemma MonadMorphism_eq_simplify  : (@monad_morph _ _ _ _ _ θ) = (@monad_morph _ _ _ _ _ θ') -> θ = θ'.
  Proof.
    destruct θ; destruct θ'.
    basic_simpl.
    ElimEq.
    PIR; trivial.
  Qed.
End SimplifyMonadMorphisms.

Section TripleMorphism.
  Context {C:Category} (T1 T2 : C -> C)
          `{@KleisliMonad _ T1} `{@KleisliMonad _ T2}.
  Record TripleMorphism :=
    MkTripleMorphism {
        triple_morph : forall (A:C), T1 A –≻ T2 A ;
        triple_unit_com : forall (A:C), triple_morph A ∘ ret T1 A = ret T2 A ;
        triple_bind_com : forall (A B:C) (f : A –≻ T1 B),
            triple_morph B ∘ bind T1 A B f =
            bind T2 A B (triple_morph B ∘ f) ∘ triple_morph A
      }.

  Program Definition MonadMorphismFromTripleMorphism (ψ : TripleMorphism) :
    MonadMorphism (TF T1) (TF T2) :=
    MkMonadMorphism (TF T1) (TF T2) {| Trans := triple_morph ψ |} _ _.
  Next Obligation.
    intros ; cbv ; rewrite triple_bind_com ;
      rewrite assoc_sym ; rewrite triple_unit_com ; reflexivity.
  Qed.

  Next Obligation.
    intros ; cbv ; rewrite triple_bind_com ;
      rewrite assoc_sym ; rewrite triple_unit_com ; reflexivity.
  Qed.

  Next Obligation.
    apply NatTrans_eq_simplify ; cbv ; extensionality c ;
      apply triple_unit_com.
  Qed.

  Next Obligation.
    apply NatTrans_eq_simplify ; cbv ; extensionality c.
    rewrite triple_bind_com.
    rewrite !assoc_sym ; f_equal.
    rewrite <- Kleisli_Monad_Associativity.
    rewrite !assoc_sym.
    rewrite Kleisli_Monad_Left_Unit.
    f_equal.
    rewrite id_unit_left.
    rewrite id_unit_right.
    reflexivity.
  Qed.
    
End TripleMorphism.

Arguments triple_morph {_ _ _ _ _} _ _.

Section TripleMorphism_id.
  Context {C:Category} (T: C -> C) `{@KleisliMonad _ T}.

  Program Definition TripleMorphism_id : TripleMorphism T T :=
    MkTripleMorphism T T (fun c => @id _ (T c)) _ _.

End TripleMorphism_id.

Section TripleMorphism_comp.
  Context {C:Category} (T1 T2 T3 : C -> C)
          `{@KleisliMonad _ T1} `{@KleisliMonad _ T2} `{@KleisliMonad _ T3}.
  Context (ψ12 : TripleMorphism T1 T2) (ψ23 : TripleMorphism T2 T3).

  Program Definition TripleMorphism_comp : TripleMorphism T1 T3 :=
    MkTripleMorphism T1 T3 (fun c => triple_morph ψ23 c ∘ triple_morph ψ12 c) _ _.
  Next Obligation.
    rewrite assoc ; rewrite 2!triple_unit_com ; reflexivity.
  Qed.

  Next Obligation.
    rewrite assoc. rewrite triple_bind_com. rewrite assoc_sym.
    rewrite triple_bind_com.
    rewrite !assoc.
    reflexivity.
  Qed.

End TripleMorphism_comp.

Section TripleMorphism_eq_simplify.
  Context {C:Category} (T1 T2 : C -> C)
          `{@KleisliMonad _ T1} `{@KleisliMonad _ T2}.
  Context (ψ ψ' : TripleMorphism T1 T2).

  Lemma TripleMorphism_eq_simplify : triple_morph ψ = triple_morph ψ' -> ψ = ψ'.
  Proof.
    destruct ψ ; destruct ψ'.
    basic_simpl.
    ElimEq.
    PIR; trivial.
  Qed.

End TripleMorphism_eq_simplify.

Section IdentityInitial.
  Context {C:Category} (M:C -> C) `{@KleisliMonad _ M}.

  Existing Instance IdentityTriple.
  Program Definition ret_morphism : TripleMorphism Id M :=
    MkTripleMorphism Id M (ret M) _ _.
  Next Obligation.
    rewrite Kleisli_Monad_Left_Unit; reflexivity.
  Qed.
End IdentityInitial.

Section MonadMorphismTriple.
  Context {C : Category} (T1 T2 : C -> C).
  Context `{H1:@KleisliMonad C T1} `{H2:@KleisliMonad C T2}. 

  Existing Instance Monad_from_KleisliMonad.

  Program Definition KleisliMonadMorphism
             (θ : NatTrans (TF T1) (TF T2))
             (map:= fun {A} => Trans θ A)
             (Hret : forall A, map ∘ ret _ A = ret _ A)
             (Hbind : forall {A B} (f : A –≻ T1 B),
                 map ∘ bind _ _ _ f = bind _ _ _ (map ∘ f) ∘ map)
    : MonadMorphism (TF T1) (TF T2) :=
    {| monad_morph := θ |}.
  Next Obligation.
    apply NatTrans_eq_simplify ; extensionality A ; exact (Hret A).
  Qed.

  Next Obligation.
    apply NatTrans_eq_simplify ; extensionality A ; cbv.
    rewrite (Hbind _ _ id) ; cbv.
    rewrite !assoc_sym.
    rewrite <- (Kleisli_Monad_Associativity _ _ _).
    f_equal.
    f_equal.
    rewrite !assoc_sym.
    rewrite (Kleisli_Monad_Left_Unit _ _).
    rewrite id_unit_right ; rewrite id_unit_left ; trivial.
  Qed.

  Context `{θ:MonadMorphism (@TF _ T1 H1) (@TF _ T2 H2)}.

  Notation θ0 := (Trans (monad_morph _ _ θ)).
  Lemma MonadMorphismBind : forall A B (f : A –≻ T1 B),
      bind _ _ _ (θ0 B ∘ f) ∘ θ0 A = θ0 B ∘ bind _ _ _ f.
  Proof.
    intros * ; cbv.
    rewrite !bind_from_mul_map.
    rewrite F_compose.
    rewrite !assoc.
    rewrite (Trans_com_sym (monad_morph _ _ θ)).
    rewrite !assoc_sym.
    f_equal.
    rewrite assoc.
    symmetry.
    exact (f_equal (fun h => Trans h B) (Monad_Mult_com _ _ θ)).
  Qed.
End MonadMorphismTriple.

Section MonadMorphismTriple'.
  Context {C:Category} (T1 T2 : (C –≻ C)%functor)
          `{@Monad _ T1} `{@Monad _ T2}.
  Existing Instance KleisliMonadFromMonad.

  Program Definition KleisliMonadMorphism'
             (θ : NatTrans T1 T2)
             (map:= fun {A} => Trans θ A)
             (Hret : forall A, map ∘ ret _ A = ret _ A)
             (Hbind : forall {A B} (f : A –≻ FO T1 B),
                 map ∘ bind _ _ _ f = bind _ _ _ (map ∘ f) ∘ map)
    : MonadMorphism T1 T2 :=
    {| monad_morph := θ |}.
  Next Obligation.
    apply NatTrans_eq_simplify ; extensionality A ; exact (Hret A).
  Qed.

  Next Obligation.
    apply NatTrans_eq_simplify ; extensionality A ; cbv.
    pose (Hm := Hbind (FO T1 A) A id).
    rewrite F_id in Hm.
    simpl_ids in Hm.
    rewrite assoc in Hm.
    exact Hm.
  Qed.
  
  Context `{θ:MonadMorphism T1 T2}.

  Notation θ0 := (Trans (monad_morph _ _ θ)).
  Lemma MonadMorphismBind' : forall A B (f : A –≻ FO T1 B),
      bind _ _ _ (θ0 B ∘ f) ∘ θ0 A = θ0 B ∘ bind _ _ _ f.
  Proof.
    intros * ; cbv.
    rewrite F_compose.
    rewrite 2!assoc.
    rewrite (Trans_com_sym (monad_morph _ _ θ)).
    rewrite !assoc_sym.
    f_equal.
    rewrite assoc.
    symmetry.
    exact (f_equal (fun h => Trans h B) (Monad_Mult_com _ _ θ)).
  Qed.
End MonadMorphismTriple'.


Section MonadCat.
  Context {C:Category}.

  Definition FunC : Category := Func_Cat C C.

  Program Instance MonadCat : Category :=
    Build_Category
      { T :  (C –≻ C)%functor & Monad T}
      ltac:(intros [T1] [T2] ; exact (MonadMorphism T1 T2))
             ltac:(intros [] [] [] ; apply MonadMorphism_comp)
                    _ _
                    ltac:(intros [] ; apply MonadMorphism_id) _ _.
  Solve Obligations with
      intros * ;
      repeat (match goal with
              | [X : sigT _ |- _] => destruct X
              | [F : MonadMorphism _ _ |- _] => destruct F
              end) ; try (apply MonadMorphism_eq_simplify);
      try (apply (@assoc FunC)) ;
      try (apply (@assoc_sym FunC)) ;
      try (apply (@id_unit_left FunC)) ;
      try (apply (@id_unit_right FunC)).
    
End MonadCat.

Section TripleCat.
  Context {C:Category}.

  Program Instance TripleCat : Category :=
    Build_Category
      { T :  C -> C & @KleisliMonad C T}
      ltac:(intros [T1] [T2] ; exact (TripleMorphism T1 T2))
             ltac:(intros [] [] [] ; apply TripleMorphism_comp)
                    _ _
                    ltac:(intros [] ; apply TripleMorphism_id) _ _.
  Solve Obligations with
      intros * ;
      repeat (match goal with
              | [X : sigT _ |- _] => destruct X
              | [F : TripleMorphism _ _ |- _] => destruct F
              end) ; try (apply TripleMorphism_eq_simplify) ; simpl ;
        extensionality c ;
        (apply assoc + apply assoc_sym + (simpl_ids ; reflexivity)).
End TripleCat.

Section AlgebraicOperations.

  Context {C : Category} (T:(C –≻ C)%functor) `{@Monad _ T}.
  Context `{@CCC C}.


  Definition PowerFunc (I:C) : (C –≻ C)%functor :=
    let I : (C ^op)%category := I in
    Fix_Bi_Func_1 I (Exp_Func CCC_HEXP).

  Record AlgebraicOperation :=
    {
      dom_ar : C ;
      codom_ar : C ;
      alg_op : ((PowerFunc dom_ar ∘ T)%functor –≻ (PowerFunc codom_ar ∘ T)%functor)%nattrans
    }.

  Record GenericEffect :=
    {
      dom : C ;
      codom : C ;
      gen_eff : dom –≻ (T _o codom)%object
    }.

  (* TODO : prove the equivalence between the two *)
End AlgebraicOperations.