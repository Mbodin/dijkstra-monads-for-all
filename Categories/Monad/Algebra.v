From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import NatTrans.Main.
From Categories Require Import Monad.Monad.
From Categories Require Import Basic_Cons.Product.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
(* From Categories Require Import Functor.Representable.Hom_Func. *)

Local Open Scope morphism_scope.

Section Algebra.

  Context {C:Category} (T:(C –≻ C)%functor) `{@Monad _ T}.

  Record AlgebraStructure (carrier : C) :=
    {
      alg_structure : (T _o carrier)%object –≻ carrier ;
      alg_unit : alg_structure ∘ Trans η carrier = id ;
      alg_mult : alg_structure ∘ Trans μ carrier = alg_structure ∘ T _a alg_structure
    }.

  Definition Algebra := { carrier : C & AlgebraStructure carrier }.

End Algebra.

Section FromKleisli.
  Context {C:Category} (T:C -> C) `{@KleisliMonad _ T}.

  Existing Instance Monad_from_KleisliMonad.
  Local Arguments ret {_ _ _ _}.
  Local Arguments bind {_ _ _ _ _} _.

  Let kleisli_unit_eq {A : C} (α : T A –≻ A) := α ∘ ret = id.
  Let kleisli_bind_eq {A : C} (α : T A –≻ A) := forall {X} (f : X –≻ T A), α ∘ bind f = α ∘ bind (ret ∘ α ∘ f).


  (* Section KleisliAlgebraLaws. *)
  (*   Context {A : C} (α : T A –≻ A). *)

  (*   Definition kleisli_unit_eq := α ∘ ret = id. *)
  (*   Definition kleisli_bind_eq := forall {X} (f : X –≻ T A), α ∘ bind f = α ∘ bind (ret ∘ α ∘ f). *)
  (* End KleisliAlgebraLaws. *)

  Section AlgebraFromKleisli.
    Context {A : C} (α : T A –≻ A).
    Variable Hunit : kleisli_unit_eq α.
    Variable Hbind : kleisli_bind_eq α.

    Program Definition AlgebraFromKleisli  : AlgebraStructure (TF T) A :=
      {| alg_structure := α |}.

    Next Obligation.
      pose (H0 := Hbind (T A) id) ; simpl_ids in H0; exact H0.
    Qed.
  End AlgebraFromKleisli.

  Section AlgebraToKleisli.
    Context {A:C} (Halg:AlgebraStructure (TF T) A).
    Notation α := (alg_structure _ _ Halg).

    Lemma alg_bind : kleisli_bind_eq α.
    Proof.
      cbv ; intros.
      rewrite (bind_from_mul_map T f).
      rewrite assoc_sym.
      rewrite (alg_mult (TF T) A).
      rewrite assoc.

      rewrite <- (map_from_bind_ret _ (α ∘ f)).
      rewrite F_compose.
      reflexivity.
    Qed.

    Lemma alg_ret : kleisli_unit_eq α.
    Proof. exact (alg_unit _ _ _). Qed.
  End AlgebraToKleisli.

End FromKleisli.


(* Section KleisliFromAlgebra. *)
(*   Context {C:Category} (T:(C –≻ C)%functor) `{@Monad _ T}. *)

(*   Context (A:Algebra T). *)
(*   Existing Instance KleisliMonadFromMonad. *)

(*   Notation α := (alg_structure _ _ (projT2 A)). *)

(*   Lemma alg_bind : kleisli_bind_eq (FO T) α. *)
(*   Proof. *)
(*     cbv. intros. destruct A. *)
(*     rewrite F_compose. *)
(*     replace (Trans μ x ∘ (T _a) (Trans η x) ∘ (T _a) (alg_structure _ _ a ∘ f)) *)
(*       with ((Trans μ x ∘ (T _a) (Trans η x)) ∘ (T _a) (alg_structure _ _ a ∘ f)) by apply assoc. *)
(*     rewrite (monad_left_unit T x). simpl_ids. *)
(*     rewrite F_compose ; rewrite !assoc_sym ; f_equal. *)
(*     exact (alg_mult _ _ a). *)
(*   Qed. *)

(*   Lemma alg_ret : kleisli_unit_eq (FO T) α. *)
(*   Proof. exact (alg_unit _ _ _). Qed. *)

(* End KleisliFromAlgebra. *)

Section AlgebraMorphisms.
  Context {C:Category} (T:(C –≻ C)%functor) `{@Monad _ T}.

  Section AlgebraMorphism.
    Context (A B : Algebra T).

    Notation α := (alg_structure T _ (projT2 A)).
    Notation β := (alg_structure T _ (projT2 B)).

    Record AlgebraMorphism :=
      {
        alg_morph_carrier : projT1 A –≻ projT1 B ;
        alg_morph :  alg_morph_carrier ∘ α = β ∘ T _a alg_morph_carrier
      }.
  End AlgebraMorphism.

  Section AlgebraMorphism_id.
    Context (A : Algebra T).

    Program Definition AlgebraMorphism_id : AlgebraMorphism A A :=
      {| alg_morph_carrier := @id _ (projT1 A) |}.
  End AlgebraMorphism_id.

  Section AlgebraMorphism_compose.
    Context (A B D : Algebra T).
    Context (f : AlgebraMorphism A B) (g : AlgebraMorphism B D).

    Definition AlgebraMorphism_compose : AlgebraMorphism A D.
    Proof.
      destruct f as [fa Hf] ; destruct g as [ga Hg].
      exists (ga ∘ fa).
      rewrite F_compose. rewrite assoc.
      rewrite Hf. rewrite <- !assoc. rewrite Hg.
      reflexivity.
    Defined.

  End AlgebraMorphism_compose.

  Section AlgebraMorphism_eq_simplify.
    Context (A B : Algebra T).

    Context (f g : AlgebraMorphism A B).

    Lemma AlgebraMorphism_eq_simplify  :
      (@alg_morph_carrier _ _ f) = (@alg_morph_carrier _ _ g) -> f = g.
    Proof.
      destruct f; destruct g.
      basic_simpl.
      ElimEq.
      PIR; trivial.
    Qed.
  End AlgebraMorphism_eq_simplify.

  Instance AlgebraCat : Category.
  Proof.
    unshelve econstructor.
    exact (Algebra T).
    apply AlgebraMorphism.
    all:intros * ;
      repeat (match goal with
              | [X : Algebra _ |- _] =>
                let H := fresh "H" in
                destruct X as [? H] ; destruct H
              | [F : AlgebraMorphism _ _ |- _] => destruct F
              end) ; try (apply AlgebraMorphism_eq_simplify).
    apply AlgebraMorphism_compose.
    apply AlgebraMorphism_id. 
    apply (@assoc C).
    apply (@assoc_sym C).
    apply (@id_unit_left C).
    apply (@id_unit_right C).
   Defined.


  Program Definition FreeAlgebra : (C –≻ AlgebraCat)%functor :=
    {|
      FO X := existT _ (T _o X)%object {| alg_structure := Trans μ X |} ;
      FA A B f := {| alg_morph_carrier := T _a f |}            
    |}.
  Next Obligation.
    apply monad_right_unit.
  Qed.

  Next Obligation.
    apply monad_assoc.
  Qed.

  Next Obligation.
    rewrite (@Trans_com_sym _ _ _ T μ _ _ f).
    reflexivity.
  Qed.

  (** Anomaly *)
  (* Solve Obligations with *)
  (*     apply AlgebraMorphism_eq_simplify ; simpl  ; *)
  (*   first [apply F_id | apply F_compose]. *)
  
  Next Obligation.
      apply AlgebraMorphism_eq_simplify ; simpl  ;
    first [apply F_id | apply F_compose].
  Qed.

  Next Obligation.
      apply AlgebraMorphism_eq_simplify ; simpl  ;
    first [apply F_id | apply F_compose].
  Qed.


  Section Products.
    Context `{HP : Has_Products C}.
    
    Program Instance AlgebraCat_product : Has_Products AlgebraCat :=
      fun a b =>
           let o := HP (projT1 a) (projT1 b) in
           let a1 : (T _o o)%object –≻ projT1 a :=
               alg_structure _ _ (projT2 a) ∘ T _a Pi_1 in
           let a2 : (T _o o)%object –≻ projT1 b :=
               alg_structure _ _ (projT2 b) ∘ T _a Pi_2 in
           {|
             product:= existT _ o {|alg_structure := Prod_morph_ex _ _ a1 a2|};
             Pi_1 := {| alg_morph_carrier := Pi_1 |} ;
             Pi_2 := {| alg_morph_carrier := Pi_2 |} ;
             Prod_morph_ex p' f g :=
               {| alg_morph_carrier :=
                    Prod_morph_ex o (projT1 p')
                                  (alg_morph_carrier _ _ f)
                                  (alg_morph_carrier _ _ g) |}
      |}.
    Next Obligation.
      eapply Prod_morph_unique ; try reflexivity;
      rewrite assoc_sym 
      ; [rewrite Prod_morph_com_1|rewrite Prod_morph_com_2];
      rewrite assoc ;
      rewrite (@Trans_com_sym _ _ _ T η (HP (projT1 a) (projT1 b)) _ _) ;
      rewrite assoc_sym ;
      rewrite alg_unit ;
      simpl_ids ; reflexivity.
    Qed.
    
    Next Obligation.
      eapply Prod_morph_unique; rewrite !assoc_sym;
        try ((rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2); reflexivity);
      (rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2);
      rewrite assoc;
      rewrite <- (F_compose T);
      (rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2);
      rewrite assoc;
      rewrite (@Trans_com_sym _ _ _ T μ (HP (projT1 a) (projT1 b)) _ _);
      rewrite (F_compose T);
      rewrite !assoc_sym;
      rewrite (alg_mult);
      reflexivity.
    Qed.

    Next Obligation.
      rewrite Prod_morph_com_1 ; reflexivity.
    Qed.

    Next Obligation.
      rewrite Prod_morph_com_2 ; reflexivity.
    Qed.

    Next Obligation.
      eapply Prod_morph_unique ; try reflexivity;
      rewrite !assoc_sym;
      (rewrite 2!Prod_morph_com_1 || rewrite 2!Prod_morph_com_2);
      rewrite !assoc;
      rewrite <- (F_compose T);
      (rewrite 1!Prod_morph_com_1 || rewrite 1!Prod_morph_com_2);
      rewrite (alg_morph);
      reflexivity.
    Qed.

    Next Obligation.
      repeat (match goal with | [H : Algebra _ |- _] => destruct H end);
      apply AlgebraMorphism_eq_simplify ; simpl.
      rewrite Prod_morph_com_1 ; reflexivity.
    Qed.

    Next Obligation.
      repeat (match goal with | [H : Algebra _ |- _] => destruct H end);
      apply AlgebraMorphism_eq_simplify ; simpl.
      rewrite Prod_morph_com_2 ; reflexivity.
    Qed.

    Next Obligation.
      repeat (match goal with
              | [H : Algebra _ |- _] => destruct H
              | [H : AlgebraMorphism _ _ |- _] => destruct H
              | [H : _ = _ |- _] => injection H  ; clear H end).
      intros <- <- H1 H2.
      apply AlgebraMorphism_eq_simplify ; simpl in *.
      eapply Prod_morph_unique ; eauto.
    Qed.


    Let P := Prod_Func C.
    Definition ProdAlg_Func := Prod_Func AlgebraCat.

    (* Program Definition ProdAlg_Func *)
    (*   : ((AlgebraCat × AlgebraCat) –≻ AlgebraCat)%functor := *)
    (* {| *)
    (*   FO x := *)
    (*     let o := (P _o (projT1 (fst x), projT1 (snd x)))%object in *)
    (*     let a1 : (T _o o)%object –≻ projT1 (fst x) := *)
    (*         alg_structure _ _ (projT2 (fst x)) ∘ T _a Pi_1 in *)
    (*     let a2 : (T _o o)%object –≻ projT1 (snd x) := *)
    (*         alg_structure _ _ (projT2 (snd x)) ∘ T _a Pi_2 in *)
    (*     existT _ o {| alg_structure := Prod_morph_ex _ _ a1 a2 |} *)
    (*   ; *)
    (*   FA a b f := *)
    (*     {| alg_morph_carrier := *)
    (*          Prod_morph_ex _ _ *)
    (*                        (alg_morph_carrier _ _ (fst f) ∘ Pi_1) *)
    (*                        (* _ (projT1 (fst a)) _ _, *) *)
    (*                        (alg_morph_carrier _ _ (snd f) ∘ Pi_2) *)
    (*                        (* _ (projT1 (snd a)) _ _) *) *)
    (*     |} *)
    (* |}. *)
    (* Next Obligation. *)
    (*   eapply Prod_morph_unique ; try reflexivity; *)
    (*   rewrite assoc_sym  *)
    (*   ; [rewrite Prod_morph_com_1|rewrite Prod_morph_com_2]; *)
    (*   rewrite assoc; *)
    (*   rewrite (@Trans_com_sym _ _ _ T η (HP (projT1 x1) (projT1 x2)) _ _) ; *)
    (*   rewrite assoc_sym ; *)
    (*   rewrite alg_unit ; *)
    (*   simpl_ids ; reflexivity. *)
    (* Qed. *)

    (* Next Obligation. *)
    (*   eapply Prod_morph_unique; rewrite !assoc_sym; *)
    (*     try ((rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2); reflexivity); *)
    (*   (rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2); *)
    (*   rewrite assoc; *)
    (*   rewrite <- (F_compose T); *)
    (*   (rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2); *)
    (*   rewrite assoc; *)
    (*   rewrite (@Trans_com_sym _ _ _ T μ (HP (projT1 x1) (projT1 x2)) _ _); *)
    (*   rewrite (F_compose T); *)
    (*   rewrite !assoc_sym; *)
    (*   rewrite (alg_mult); *)
    (*   reflexivity. *)
    (* Qed. *)

    (* Next Obligation. *)
    (*   eapply Prod_morph_unique ; try reflexivity; *)
    (*   rewrite !assoc_sym; *)
    (*   (rewrite 2!Prod_morph_com_1 || rewrite 2!Prod_morph_com_2); *)
    (*   rewrite !assoc; *)
    (*   rewrite <- (F_compose T); *)
    (*   (rewrite 2!Prod_morph_com_1 || rewrite 2!Prod_morph_com_2); *)
    (*   rewrite (F_compose T); *)
    (*   rewrite !assoc_sym; *)
    (*   rewrite (alg_morph); *)
    (*   reflexivity. *)
    (* Qed. *)

    (* Next Obligation. *)
    (*   apply AlgebraMorphism_eq_simplify ; simpl. *)
    (*   eapply Prod_morph_unique ; try reflexivity ; *)
    (*   (rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2) ; *)
    (*   destruct c1 ; destruct c2 ; auto. *)
    (* Qed. *)

    (* Next Obligation. *)
    (*   apply AlgebraMorphism_eq_simplify ; simpl ; *)
    (*   eapply Prod_morph_unique ; try reflexivity; *)
    (*   rewrite !assoc_sym; *)
    (*   (rewrite 2!Prod_morph_com_1 || rewrite 2!Prod_morph_com_2); *)
    (*   repeat (match goal with | [H : Algebra _ |- _] => destruct H end); *)
    (*   simpl; *)
    (*   rewrite !assoc; *)
    (*   (rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2); *)
    (*   trivial. *)
    (* Qed. *)
        
  End Products.

End AlgebraMorphisms.
