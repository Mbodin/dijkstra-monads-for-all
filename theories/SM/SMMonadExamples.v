From Coq Require Import List ssreflect.
From Mon Require Import Base.
From Mon.sprop Require Import SPropBase SPropMonadicStructures SpecificationMonads DijkstraMonadExamples DirectedContainers.
From Mon.SM Require Import dlist SMSyntax MonadTransformer SMDenotationsMonotonic MonadTransformerMonotonic.
From Mon.SRelation Require Import SRelationClasses SMorphisms.

From Equations Require Import Equations.

Transparent icbeta.
Transparent Substitution.dlookup.
Transparent Substitution.dmap.

Set Universe Polymorphism.


(********************************************************)
(* A few helper functions to evaluate terms in SM using *)
(* the abstract machine and proving equations           *)
(********************************************************)

Section EquationHelpers.
  Lemma reduce_iceq_invariant
  : forall (Γ0 Γ : ctx)(c0 c: ctype) (t:icterm Γ c) (π:stack c)
      (σ : isubstitution Γ0 Γ) (n m:nat),
      reduce Γ0 n c0 Γ c t π σ ≅ reduce Γ0 m c0 Γ c t π σ.
  Proof.
    intros.
    simple refine (ICTrans _ (ICSym (reduce_rebuild _ _ _ _ _ _ _ _))).
    apply reduce_rebuild.
  Qed.

  Import FunctionalExtensionality.

  Lemma iceq_reduce (Γ : ctx) (c: ctype) (t1 t2:icterm Γ c) (n m:nat)
    : reduce Γ n c Γ c t1 StckNil (id_isubst _) ≅ reduce Γ m c Γ c t2 StckNil (id_isubst _) -> t1 ≅ t2.
  Proof.
    intros Hred.
    rewrite -(isubst_id t1) -(isubst_id t2).
    simple refine (ICTrans (reduce_iceq_invariant Γ Γ c c t1 StckNil (id_isubst _) 0 n) _).
    simple refine (ICTrans _ (reduce_iceq_invariant Γ Γ c c t2 StckNil (id_isubst _) m 0)).
    assumption.
  Qed.

  Lemma iceq_monad_law2 (Γ : ctx) (A : Type) (t:icterm Γ (A ~> CM A)) (m : icterm Γ (CM A)) :
    t ≅ IMRet A -> IMBind t m ≅ m.
  Proof.
    intros H. simple refine (ICTrans _ (ICBindRet _)).
    apply ICBindCongr. apply ICRefl. assumption.
  Defined.

End EquationHelpers.

Arguments reduce : simpl nomatch.

(********************************************************)
(* The state monad implemented in SM and its derived    *)
(* monad transformer                                    *)
(********************************************************)

Section St.
  Context (S:Type).

  Definition st_car (A:Type) := S ~> CM (A × S).
  Definition st_ret (A:Type) : icterm nil (A ~> st_car A) :=
    IAbs (fun (a:A) => IAbs (fun (s:S) => IMRet (A × S) @ ⟨a, s⟩)).
  Definition st_bind (A B:Type) : icterm nil (st_car A ~~> (A ~> st_car B) ~~> st_car B) :=
    ICAbs (ICAbs (IAbs (fun s0 =>
                               IMBind 
                                      (IAbs (fun r =>
                                               (vz @ (nfst r)) @ (nsnd r)
                                      ))
                                      ((↑vz) @[st_car A] s0)

          ))).

  Definition bind_stack A B : S -> @stack nil ((A ~> st_car B) ~~> CM (B × S)) (st_car A) :=
    fun s => StckArg (st_car A) isArrPf s (StckCont (A × S) (fun r => @ICAbs _ _ (CM (B × S)) ((vz @[A ~> st_car B] (nfst r)) @ (nsnd r)))). 


  Program Definition st_icmonad : icmonad :=
    MkICMonad st_car st_ret st_bind _ _ _.
  Next Obligation.
    iceq_extensionality.
    apply (iceq_reduce _ _ _ _ 15 3).
    cbv.
    apply iceq_monad_law2.
    iceq_extensionality.
    apply (iceq_reduce _ _ _ _ 3 3).
    cbv.
    apply ICRefl.
  Qed.
  Next Obligation.
    iceq_extensionality ; apply (iceq_reduce _ _ _ _ 15 3); cbv.
    apply ICRefl.
  Qed.
  Next Obligation.
    iceq_extensionality ; apply (iceq_reduce _ _ _ _ 30 30); cbv.
    apply ICRefl.
  Qed.

  Import FunctionalExtensionality.
  Import SPropNotations.
  Program Definition ST_T  :=
    Eval cbv in CMonadTransformer st_icmonad _ _.
  Next Obligation.
    apply Ssig_eq ; simpl.
    extensionality f ; extensionality s.
    cbv.
    rewrite !monad_law3.
    f_equal.
    extensionality g.
    rewrite !monad_law1.
    reflexivity.
  Qed.
  
  Program Definition STCont0 : OrderedMonadUnder _ := @OrderedMonadUnderFromEqns MonoContSProp st_icmonad _ _ _ _ _.

  Definition STCont := Eval cbv in STCont0.
End St.

(********************************************************)
(* The update monad implemented in SM                   *)
(********************************************************)

From Mon.sprop Require Import Monoid.
Section SimpleUpdate.
  (* simply typed update monad on a monoid and an action *)
  (* special case of the dependet update monad           *)

  Context (M:monoid) (S : monoid_action M).

  Definition upd_car (A:Type) := S ~> CM (A × M).
  Definition upd_ret (A:Type) : icterm nil (A ~> upd_car A) :=
    IAbs (fun (a:A) => IAbs (fun (s:S) => IMRet _ @ ⟨a, e M⟩)).
  Definition upd_bind (X Y:Type) : icterm nil (upd_car X ~~> (X ~> upd_car Y) ~~> upd_car Y) :=
    ICAbs (
        ICAbs (
            IAbs (fun s0 =>
                    IMBind 
                      (IAbs (fun r =>
                               IMBind
                                 (IAbs (fun r' =>
                                          IMRet _ @ ⟨nfst r', (nsnd r') ⋅ (nsnd r)⟩))
                                 ((vz @ (nfst r)) @[upd_car Y] ((nsnd r) ⧕ s0))
                      ))
                      ((↑vz) @[upd_car X] s0)

          ))).

  Definition upd_icmonad_fronEqns pf1 pf2 pf3 : icmonad :=
    MkICMonad upd_car upd_ret upd_bind pf1 pf2 pf3.

  Import EqNotations.
  Import SPropNotations.
  Import FunctionalExtensionality.
  Program Definition upd_icmonad := upd_icmonad_fronEqns _ _ _.
  Next Obligation.
    iceq_extensionality; apply (iceq_reduce _ _ _ _ 15 3); cbv.
    apply iceq_monad_law2.
    iceq_extensionality; apply (iceq_reduce _ _ _ _ 3 3); cbv.
    rewrite monoid_law1.
    apply ICRefl.
  Qed.
  Next Obligation.
    iceq_extensionality; apply (iceq_reduce _ _ _ _ 15 3); cbv.
    rewrite monact_unit.
    apply iceq_monad_law2.
    iceq_extensionality; apply (iceq_reduce _ _ _ _ 3 3); cbv.
    rewrite monoid_law2.
    apply ICRefl.
  Qed.
  Next Obligation.
    iceq_extensionality; apply (iceq_reduce _ _ _ _ 45 45); cbv.
    iceq_congr.
    iceq_extensionality ; apply (iceq_reduce _ _ _ _ 50 50); cbv.
    iceq_congr.
    iceq_extensionality ; apply (iceq_reduce _ _ _ _ 50 50); cbv.
    rewrite monact_mult.
    iceq_congr.
    iceq_extensionality ; apply (iceq_reduce _ _ _ _ 50 50); cbv.
    rewrite monoid_law3 ; apply ICRefl.
  Qed.
End SimpleUpdate.



Section Update.
  Context S (P : dir_cont_struct S).
  Import SPropNotations.

  Definition dupd_car (A:Type) :=
    CArr (fun s0:S => CM (A × P s0)).
  Definition dupd_ret (A:Type) : icterm nil (A ~> dupd_car A) :=
    IAbs (fun (a:A) => IAbs (fun (s:S) => IMRet _ @ ⟨a, ✪⟩)).
  Definition dupd_bind (X Y:Type) : icterm nil (dupd_car X ~~> (X ~> dupd_car Y) ~~> dupd_car Y) :=
    ICAbs (
        ICAbs (
            IAbs (fun s0 =>
                    IMBind 
                      (IAbs (fun r =>
                               IMBind
                                 (IAbs (fun r' =>
                                          IMRet _ @ ⟨nfst r', (nsnd r) ⊛ (nsnd r')⟩))
                                 ((vz @ (nfst r)) @[dupd_car Y] (s0 ↫ (nsnd r)))
                      ))
                      ((↑vz) @[dupd_car X] s0)

          ))).

  Definition dupd_icmonad_fronEqns pf1 pf2 pf3 : icmonad :=
    MkICMonad dupd_car dupd_ret dupd_bind pf1 pf2 pf3.

  Import EqNotations.
  Import FunctionalExtensionality.
  Program Definition dupd_icmonad := dupd_icmonad_fronEqns _ _ _.
  Next Obligation.
    iceq_extensionality.
    apply (iceq_reduce _ _ _ _ 15 3).
    cbv.
    apply iceq_monad_law2.
    iceq_extensionality.
    apply (iceq_reduce _ _ _ _ 3 3).
    cbv.
    rewrite dc_law3.
    apply ICRefl.
  Qed.
  Next Obligation.
    iceq_extensionality ; apply (iceq_reduce _ _ _ _ 30 3); cbv.
    match goal with
    | [|- IMBind ?f ?m ≅ _] =>
      enough (IMBind f m = 
        IMBind 
          (IAbs (fun a : B × P (x0 ↫ ✪) =>
             IMRet (B × P x0) @ ⟨ nfst a, rew [P] dc_law1 _ P x0 in nsnd a ⟩))
          m) as ->
    end.
    refine (
        match dc_law1 _ P x0 as H0 in _ = x1 return 
              IMBind
                (IAbs
                   (fun a : B × P (x0 ↫ ✪) =>
                      IMRet (B × P x1) @[B × P x1 ~> CM (B × P x1)]
                            ⟨ nfst a, rew [P] H0 in nsnd a⟩))
                ((vz @ x) @ (x0 ↫ ✪))
    ≅ (vz @ x) @ x1
        with
        | eq_refl => _
        end).
    apply iceq_monad_law2.
    iceq_extensionality ; apply (iceq_reduce _ _ _ _ 15 3); cbv.
    apply ICRefl.
    do 2 f_equal.
    extensionality a.
    rewrite dc_law4 //.
  Qed.
  Next Obligation.
    iceq_extensionality ; apply (iceq_reduce _ _ _ _ 50 50); cbv.
    iceq_congr.
    iceq_extensionality ; apply (iceq_reduce _ _ _ _ 50 50); cbv.
    iceq_congr.
    iceq_extensionality ; apply (iceq_reduce _ _ _ _ 50 50); cbv.
    match goal with
    | [|- IMBind ?f ?m ≅ _] =>
      enough (IMBind f m = 
        IMBind 
          (IAbs
             (fun a : C × P (x ↫ (nsnd x0 ⊛ nsnd x1)) =>
                IMRet (C × P x) @ ⟨ nfst a, nsnd x0 ⊛ ( nsnd x1 ⊛rew <- [P] eq_sym (dc_law2 _ _ _ _ _) in nsnd a) ⟩ )
             )
          m) as ->
    end.
    match goal with
    | [|- IMBind _ ?m ≅ ?t] =>
      refine (
          match eq_sym (dc_law2 _ P x (nsnd x0) (nsnd x1)) as H0 in _ = x' return
              IMBind
                (IAbs
                   (fun a : C × P x' =>
                      IMRet (C × P x) @ ⟨ nfst a, nsnd x0 ⊛ ( nsnd x1 ⊛ rew <- [P] H0 in nsnd a)⟩))
                (((↑↑vz) @ nfst x1) @ x')
                ≅ t
          with
          | eq_refl => _
          end)
    end.
    iceq_congr.
    do 2 f_equal.
    extensionality a.
    unfold eq_rect_r.
    rewrite DepElim.eq_sym_invol.
    rewrite dc_law5 //.
  Qed.

End Update.

(********************************************************)
(* Instance of update monad transformer applied         *)
(********************************************************)

(* In all these cases the monadic laws hold definitionally *)

Program Definition RDCont S :=
  @OrderedMonadUnderFromEqns MonoContSProp (dupd_icmonad S (reader_dc S))
                             _ _ _ _ _.

Program Definition WrCont O :=
  @OrderedMonadUnderFromEqns
    MonoContSProp
    (dupd_icmonad _ (writer_dc (strict_list_monoid O)))
    _ _ _ _ _.

Program Definition LoggerCont O :=
  @OrderedMonadUnderFromEqns
    MonoContSProp
    (dupd_icmonad _ (logger_dc (strict_list_monoid O)))
    _ _ _ _ _.


(* Monotonic state monad, could be obtained through an update monad *)
Section MonSt.
  Context (S:Type) (rel_st : srelation S) `{PreOrder _ rel_st}.
  Import SPropNotations.

  Definition mst_car (A:Type) := CArr (fun s0:S => CM (A × { s1 :S ≫ rel_st s0 s1})).
  Program Definition mst_ret (A:Type) : icterm nil (A ~> mst_car A) :=
    IAbs (fun (a:A) => IAbs (fun (s:S) => IMRet _ @ ⟨a, ⦑s⦒⟩)).
  Next Obligation. sreflexivity. Qed.
  Program Definition mst_bind (A B:Type) : icterm nil (mst_car A ~~> (A ~> mst_car B) ~~> mst_car B) :=
    ICAbs (
        ICAbs (
            IAbs (fun s0 =>
                    IMBind 
                      (IAbs (fun r =>
                               IMBind
                                 (IAbs (fun r' => IMRet _ @ ⟨nfst r', ⦑Spr1 (nsnd r')⦒⟩))
                                 ((vz @ (nfst r)) @ (Spr1 (nsnd r)))
                      ))
                      ((↑vz) @[mst_car A] s0)

          ))).
  Next Obligation.
    move: r r' => [? [? ?]] [? [? ?]] ; estransitivity ; eassumption.
  Qed.

  Program Definition mst_icmonad : icmonad :=
    MkICMonad mst_car mst_ret mst_bind _ _ _.
  Next Obligation.
    iceq_extensionality.
    apply (iceq_reduce _ _ _ _ 15 3).
    cbv.
    apply iceq_monad_law2.
    iceq_extensionality.
    apply (iceq_reduce _ _ _ _ 3 3).
    cbv.
    apply ICRefl.
  Qed.
  Next Obligation.
    iceq_extensionality ; apply (iceq_reduce _ _ _ _ 15 3); cbv.
    apply iceq_monad_law2.
    iceq_extensionality ; apply (iceq_reduce _ _ _ _ 15 3); cbv.
    apply ICRefl.
  Qed.
  Next Obligation.
    iceq_extensionality ; apply (iceq_reduce _ _ _ _ 50 50); cbv.
    apply ICRefl.
  Qed.

End MonSt.

(********************************************************)
(* Partial definition of the exception monad in SM      *)
(********************************************************)

Section Exc.
  Context (E:Type).

  Definition exc_car (A:Type) := CM (A + E).
  Definition exc_ret (A:Type) : icterm nil (A ~> exc_car A) :=
    IAbs (fun (a:A) => IMRet (A + E) @ (inl a)).
  Definition exc_bind (A B:Type)
    : icterm nil (exc_car A ~~> (A ~> exc_car B) ~~> exc_car B) :=
    ICAbs (ICAbs (
               IMBind
                 (IAbs (fun aopt => match aopt with
                                 | inl a => vz @[A ~> exc_car B] a
                                 | inr e => IMRet (B+E) @ (inr e)
                                 end))
                 (↑vz)
          )).

  (* Proving the 3rd monadic law hits a performance issue...*)
End Exc.


(**********************************************************)
(* Continuation monad in SM and derived monad transformer *)
(**********************************************************)

Section Continuation.
  Context (Ans:Type).
  Definition cont_car (A:Type) := (A ~> CM Ans) ~~> CM Ans.
  Definition cont_ret (A:Type) : icterm nil (A ~> cont_car A) :=
    IAbs (fun (a:A) => ICAbs (vz @ a)).
  Definition cont_bind (A B:Type) : icterm nil (cont_car A ~~> (A ~> cont_car B) ~~> cont_car B) :=
    ICAbs (ICAbs (ICAbs (
           (↑↑vz) @c (IAbs (fun a => ((↑vz) @[A ~> cont_car B] a) @c vz))
          ))).

  Program Definition cont_icmonad : icmonad :=
    MkICMonad cont_car cont_ret cont_bind _ _ _.
  Next Obligation.
    iceq_extensionality; apply (iceq_reduce _ _ _ _ 30 3); cbv.
    iceq_congr.
    iceq_extensionality; apply (iceq_reduce _ _ _ _ 30 3) ; cbv.
    apply ICRefl.
  Qed.
  Next Obligation.
    iceq_extensionality; apply (iceq_reduce _ _ _ _ 30 3); cbv.
    apply ICRefl.
  Qed.
  Next Obligation.
    iceq_extensionality; apply (iceq_reduce _ _ _ _ 50 50) ; cbv.
    iceq_congr.
    iceq_extensionality; apply (iceq_reduce _ _ _ _ 50 50) ; cbv.
    apply ICRefl.
  Qed.

  Definition ic_call_cc A
    : icterm  (((A ~> cont_car Ans) ~~> cont_car Ans) :: nil) (cont_car A)
    :=
      ICAbs (
                (↑vz) @c (IAbs (fun a => ICAbs (IMBind vz ((↑vz)@[A ~> CM Ans] a)))) @c IMRet Ans  
               ).

End Continuation.

(****************************************************************)
(* Continuation Dijkstra monad with call_cc and excluded middle *)
(****************************************************************)

Definition retIdeal M :=
  @ideal_from_mmorph _ M (MonadExamples.ret_mmorph M).

Section ContinuationDijkstraMonad.
  Context (Ans:Type).

  Program Definition ContCont : OrderedMonadUnder _ :=
    @OrderedMonadUnderFromEqns MonoContSProp (cont_icmonad Ans) _ _ _ _ _.

  Program Definition Cont : OrderedMonadUnder _ :=
    @OrderedMonadUnderFromEqns (DiscreteMonad MonadExamples.Identity)
                               (cont_icmonad Ans) _ _ _ _ _.

  Program Definition ContD : Dijkstra ContCont :=
    Drel (CMonadIdeal (cont_icmonad Ans) _ MonoContSProp (retIdeal _)
                      _ _ _ _ _ _).
  
  Import Substitution. 
  Import SPropNotations.
  Program Definition call_cc A f :=
    icterm_to_term (DiscreteMonad MonadExamples.Identity)  (ic_call_cc Ans A)
                   (dCons f dNil).

  Definition call_cc_wp A wf :=
    icterm_to_term MonoContSProp (ic_call_cc Ans A)
                   (dCons wf dNil).

  Definition call_cc_srel A f wf frel :=
    icterm_to_srel_witness (DiscreteMonad MonadExamples.Identity)
                           MonoContSProp
                          (retIdeal _) 
                          (ic_call_cc Ans A)
                          (dCons (MkSRelVal  _ _ _ _ f wf frel) dNil).

  Program Definition call_ccD A f wf frel
    : ContD A (call_cc_wp A wf) :=
    Sexists _ (call_cc A f) (call_cc_srel A f wf frel).

  (* Eval cbv in ltac:(let t := type of call_ccD in exact t). *)

  Import SPropNotations.

  Program Definition null_wp {A }: ContCont A :=
    ⦑fun kwp => ⦑fun post => forall x, Spr1 (kwp x) post⦒⦒.
  Next Obligation.
    move: (H0 x0) ; apply (Spr2 (kwp x0)) ; assumption.
  Qed.
  Next Obligation. move: (H0 x) ; apply (H x). Qed.

  Program Definition to_null {A}
    : to_type MonoContSProp ((A ~> cont_car Ans Ans) ~~> cont_car Ans Ans) :=
    ⦑fun w => null_wp⦒.
  Next Obligation. auto. Qed.
    
  Program Definition call_cc_null A (f : (A -> ContD Ans null_wp) -> ContD Ans null_wp) : ContD A (call_cc_wp _ to_null) :=
    ⦑⦑fun k => Spr1 (Spr1 (f (fun a => ⦑⦑fun k' => k' (k a)⦒⦒))) id⦒⦒.
  Next Obligation. move: H H0 ; simpl ; intuition. Qed.
  Next Obligation. apply SPropAxioms.funext_sprop in H; induction H=> //. Qed.
  Next Obligation. move: H H0 ; cbv ; intuition. Qed.

  Definition DId := @Dθ _ MonoContSProp (MonadExamples.ret_mmorph _).

  Program Definition w_em A (p : A -> SProp) : ContCont (A + (forall a:A, Pure Ans (PrePostSpec (p a) (fun _ => sUnit))))%type :=
    ⦑fun h => ⦑fun post =>
              (forall a, p a -> Spr1 (h (inl a)) post)
                s/\ forall k, Spr1 (h (inr k)) post
    ⦒ ⦒.
  Next Obligation. intuition. Qed.
  Next Obligation.
    simpl in H0 |- *.
    destruct H0 as [H1 H2] ; split.
    intros a0 Hp ; move: (H1 a0 Hp); apply (H (inl a0)).
    intros k ; move: (H2 k) ; apply (H (inr k)).
  Qed.

  Program Definition em A (p:A -> SProp) :
    ContD (A + (forall a:A, Pure Ans (PrePostSpec (p a) (fun _ => sUnit))))%type
          (w_em A p) :=
    ⦑⦑fun k => k (inr (fun a => ⦑fun p0 H => ⦑k (inl a)⦒ ⦒)) ⦒⦒ .
  Next Obligation.
    destruct H as [? H1] ; apply H1=> //.
  Defined.
  Next Obligation. constructor=> //. Qed.
  Next Obligation.
    apply SPropAxioms.funext_sprop in H. induction H => //.
  Qed.
  Next Obligation.
    cbv in x, x', H |- *.
    apply H.
    simpl in H0.
    destruct H0 as [? H1].
    apply H1.
  Qed.

End ContinuationDijkstraMonad.
