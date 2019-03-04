From SM Require Import SMSyntax.
From Coq Require Import List.
From SM Require Base.

Section GeneratedICMonad.
  Import ListNotations.

  Fixpoint inhabit0 (n:nat) (Γ : ctx) (t0 : Type) {struct n} : Type :=
    match n with
    | 0 => match Γ with [] => unit | _ :: _ => t0 end
    | S n => match Γ with [] => unit | x :: xs => inhabit0 n xs t0 end
    end.

  Definition inhabit n Γ : Type := inhabit0 n Γ (in_ctx n Γ).

  Definition inhabit_infer0 n Γ t0 : (in_ctx n Γ -> t0) -> inhabit0 n Γ t0.
  Proof.
    revert Γ t0. induction n.
    intros [] t0 H. constructor. cbv. apply H ; apply Le.le_n_S ; apply le_0_n.
    intros [] t0 H. constructor. cbn. apply IHn. intro H0.
    apply H. unfold in_ctx. simpl. apply Lt.lt_n_S. exact H0.
 Qed.

 Definition inhabit_infer n Γ : inhabit n Γ.
 Proof. unfold inhabit. apply inhabit_infer0. trivial. Qed.

Definition exc_icmonad := 
fun E : Type =>
{|
icM := fun X : Type => CM (X + E);
icRet := fun X : Type =>
         @IAbs [] X (fun _ : X => CM (X + E))
           (fun x : X =>
            (fun (Γ : SMSyntax.ctx) (A : Type) (c : A -> ctype)
               (v : @arrDom (@CArr A c) I) (t : icterm Γ (@CArr A c)) =>
             @IApp Γ (@CArr A c) I v t) [] (X + E)%type
              (fun _ : X + E => CM (X + E)) (@inl X E x) 
              (@IMRet [] (X + E)));
icBind := fun X Y : Type =>
          @ICAbs [] (CM (X + E)) ((X ~> CM (Y + E)) ~~> CM (Y + E))
            (@ICAbs [CM (X + E)] (X ~> CM (Y + E)) 
               (CM (Y + E))
               ((fun (Γ : SMSyntax.ctx) (c1 c2 : ctype)
                   (t1 : icterm Γ (c1 ~~> c2))
                   (t2 : icterm Γ (@arrCDom (c1 ~~> c2) I)) =>
                 @ICApp Γ (c1 ~~> c2) I t1 t2) [X ~> CM (Y + E); CM (X + E)]
                  (CM (X + E)) (CM (Y + E))
                  ((fun (Γ : SMSyntax.ctx) (c1 c2 : ctype)
                      (t1 : icterm Γ (c1 ~~> c2))
                      (t2 : icterm Γ (@arrCDom (c1 ~~> c2) I)) =>
                    @ICApp Γ (c1 ~~> c2) I t1 t2)
                     [X ~> CM (Y + E); CM (X + E)] 
                     (X + E ~> CM (Y + E)) (CM (X + E) ~~> CM (Y + E))
                     ((fun (Γ : list ctype) (A B : Type) =>
                       @ICAbs Γ (A ~> CM B) (CM A ~~> CM B)
                         (@ICAbs ((A ~> CM B) :: Γ) 
                            (CM A) (CM B)
                            (@IMBind (CM A :: (A ~> CM B) :: Γ) A B
                               (@ICVar (CM A :: (A ~> CM B) :: Γ) 1
                                  (Le.le_n_S 1
                                     (S
                                        ((fix length 
                                          (l : list ctype) : nat :=
                                            match l with
                                            | [] => 0
                                            | _ :: l' => S (length l')
                                            end) Γ))
                                     (Le.le_n_S 0
                                        ((fix length 
                                          (l : list ctype) : nat :=
                                            match l with
                                            | [] => 0
                                            | _ :: l' => S (length l')
                                            end) Γ)
                                        (le_0_n
                                           ((fix length 
                                             (l : list ctype) : nat :=
                                               match l with
                                               | [] => 0
                                               | _ :: l' => S (length l')
                                               end) Γ)))))
                               (@ICVar (CM A :: (A ~> CM B) :: Γ) 0
                                  (Le.le_n_S 0
                                     (S
                                        ((fix length 
                                          (l : list ctype) : nat :=
                                            match l with
                                            | [] => 0
                                            | _ :: l' => S (length l')
                                            end) Γ))
                                     (le_0_n
                                        (S
                                           ((fix length 
                                             (l : list ctype) : nat :=
                                               match l with
                                               | [] => 0
                                               | _ :: l' => S (length l')
                                               end) Γ))))))))
                        [X ~> CM (Y + E); CM (X + E)] 
                        (X + E)%type (Y + E)%type)
                     (@IAbs [X ~> CM (Y + E); CM (X + E)] 
                        (X + E) (fun _ : X + E => CM (Y + E))
                        (fun z : X + E =>
                         match z with
                         | inl x =>
                             (fun (Γ : SMSyntax.ctx) 
                                (A : Type) (c : A -> ctype)
                                (v : @arrDom (@CArr A c) I)
                                (t : icterm Γ (@CArr A c)) =>
                              @IApp Γ (@CArr A c) I v t)
                               [X ~> CM (Y + E); CM (X + E)] X
                               (fun _ : X => CM (Y + E)) x
                               (@ICVar [X ~> CM (Y + E); CM (X + E)] 0
                                  (inhabit_infer 0
                                     [X ~> CM (Y + E); CM (X + E)]))
                         | inr e =>
                             (fun (Γ : SMSyntax.ctx) 
                                (A : Type) (c : A -> ctype)
                                (v : @arrDom (@CArr A c) I)
                                (t : icterm Γ (@CArr A c)) =>
                              @IApp Γ (@CArr A c) I v t)
                               [X ~> CM (Y + E); CM (X + E)] 
                               (Y + E)%type (fun _ : Y + E => CM (Y + E))
                               (@inr Y E e)
                               (@IMRet [X ~> CM (Y + E); CM (X + E)] (Y + E))
                         end)))
                  (@ICVar [X ~> CM (Y + E); CM (X + E)] 1
                     (inhabit_infer 1 [X ~> CM (Y + E); CM (X + E)])))) |}.

Definition st_icmonad := 
fun S0 : Type =>
{|
icM := fun X : Type => S0 ~> CM (Base.nprod X S0);
icRet := fun X : Type =>
         @IAbs [] X (fun _ : X => S0 ~> CM (Base.nprod X S0))
           (fun x : X =>
            @IAbs [] S0 (fun _ : S0 => CM (Base.nprod X S0))
              (fun s : S0 =>
               (fun (Γ : SMSyntax.ctx) (A : Type) 
                  (c : A -> ctype) (v : @arrDom (@CArr A c) I)
                  (t : icterm Γ (@CArr A c)) => @IApp Γ (@CArr A c) I v t) []
                 (Base.nprod X S0)
                 (fun _ : Base.nprod X S0 => CM (Base.nprod X S0))
                 {| Base.nfst := x; Base.nsnd := s |}
                 (@IMRet [] (Base.nprod X S0))));
icBind := fun X Y : Type =>
          @ICAbs [] (S0 ~> CM (Base.nprod X S0))
            ((X ~> S0 ~> CM (Base.nprod Y S0)) ~~> S0 ~> CM (Base.nprod Y S0))
            (@ICAbs [S0 ~> CM (Base.nprod X S0)]
               (X ~> S0 ~> CM (Base.nprod Y S0)) (S0 ~> CM (Base.nprod Y S0))
               (@IAbs
                  [X ~> S0 ~> CM (Base.nprod Y S0);
                  S0 ~> CM (Base.nprod X S0)] S0
                  (fun _ : S0 => CM (Base.nprod Y S0))
                  (fun s : S0 =>
                   (fun (Γ : SMSyntax.ctx) (c1 c2 : ctype)
                      (t1 : icterm Γ (c1 ~~> c2))
                      (t2 : icterm Γ (@arrCDom (c1 ~~> c2) I)) =>
                    @ICApp Γ (c1 ~~> c2) I t1 t2)
                     [X ~> S0 ~> CM (Base.nprod Y S0);
                     S0 ~> CM (Base.nprod X S0)] (CM (Base.nprod X S0))
                     (CM (Base.nprod Y S0))
                     ((fun (Γ : SMSyntax.ctx) (c1 c2 : ctype)
                         (t1 : icterm Γ (c1 ~~> c2))
                         (t2 : icterm Γ (@arrCDom (c1 ~~> c2) I)) =>
                       @ICApp Γ (c1 ~~> c2) I t1 t2)
                        [X ~> S0 ~> CM (Base.nprod Y S0);
                        S0 ~> CM (Base.nprod X S0)]
                        (Base.nprod X S0 ~> CM (Base.nprod Y S0))
                        (CM (Base.nprod X S0) ~~> CM (Base.nprod Y S0))
                        ((fun (Γ : list ctype) (A B : Type) =>
                          @ICAbs Γ (A ~> CM B) (CM A ~~> CM B)
                            (@ICAbs ((A ~> CM B) :: Γ) 
                               (CM A) (CM B)
                               (@IMBind (CM A :: (A ~> CM B) :: Γ) A B
                                  (@ICVar (CM A :: (A ~> CM B) :: Γ) 1
                                     (Le.le_n_S 1
                                        (S
                                           ((fix length 
                                             (l : list ctype) : nat :=
                                               match l with
                                               | [] => 0
                                               | _ :: l' => S (length l')
                                               end) Γ))
                                        (Le.le_n_S 0
                                           ((fix length 
                                             (l : list ctype) : nat :=
                                               match l with
                                               | [] => 0
                                               | _ :: l' => S (length l')
                                               end) Γ)
                                           (le_0_n
                                              ((fix length 
                                                (l : list ctype) : nat :=
                                                 match l with
                                                 | [] => 0
                                                 | _ :: l' => S (length l')
                                                 end) Γ)))))
                                  (@ICVar (CM A :: (A ~> CM B) :: Γ) 0
                                     (Le.le_n_S 0
                                        (S
                                           ((fix length 
                                             (l : list ctype) : nat :=
                                               match l with
                                               | [] => 0
                                               | _ :: l' => S (length l')
                                               end) Γ))
                                        (le_0_n
                                           (S
                                              ((fix length 
                                                (l : list ctype) : nat :=
                                                 match l with
                                                 | [] => 0
                                                 | _ :: l' => S (length l')
                                                 end) Γ))))))))
                           [X ~> S0 ~> CM (Base.nprod Y S0);
                           S0 ~> CM (Base.nprod X S0)] 
                           (Base.nprod X S0) (Base.nprod Y S0))
                        (@IAbs
                           [X ~> S0 ~> CM (Base.nprod Y S0);
                           S0 ~> CM (Base.nprod X S0)] 
                           (Base.nprod X S0)
                           (fun _ : Base.nprod X S0 => CM (Base.nprod Y S0))
                           (fun z : Base.nprod X S0 =>
                            (fun (Γ : SMSyntax.ctx) 
                               (A : Type) (c : A -> ctype)
                               (v : @arrDom (@CArr A c) I)
                               (t : icterm Γ (@CArr A c)) =>
                             @IApp Γ (@CArr A c) I v t)
                              [X ~> S0 ~> CM (Base.nprod Y S0);
                              S0 ~> CM (Base.nprod X S0)] S0
                              (fun _ : S0 => CM (Base.nprod Y S0))
                              (@Base.nsnd _ _ z)
                              ((fun (Γ : SMSyntax.ctx) 
                                  (A : Type) (c : A -> ctype)
                                  (v : @arrDom (@CArr A c) I)
                                  (t : icterm Γ (@CArr A c)) =>
                                @IApp Γ (@CArr A c) I v t)
                                 [X ~> S0 ~> CM (Base.nprod Y S0);
                                 S0 ~> CM (Base.nprod X S0)] X
                                 (fun _ : X => S0 ~> CM (Base.nprod Y S0))
                                 (@Base.nfst _ _ z)
                                 (@ICVar
                                    [X ~> S0 ~> CM (Base.nprod Y S0);
                                    S0 ~> CM (Base.nprod X S0)] 0
                                    (inhabit_infer 0
                                       [X ~> S0 ~> CM (Base.nprod Y S0);
                                       S0 ~> CM (Base.nprod X S0)]))))))
                     ((fun (Γ : SMSyntax.ctx) (A : Type) 
                         (c : A -> ctype) (v : @arrDom (@CArr A c) I)
                         (t : icterm Γ (@CArr A c)) =>
                       @IApp Γ (@CArr A c) I v t)
                        [X ~> S0 ~> CM (Base.nprod Y S0);
                        S0 ~> CM (Base.nprod X S0)] S0
                        (fun _ : S0 => CM (Base.nprod X S0)) s
                        (@ICVar
                           [X ~> S0 ~> CM (Base.nprod Y S0);
                           S0 ~> CM (Base.nprod X S0)] 1
                           (inhabit_infer 1
                              [X ~> S0 ~> CM (Base.nprod Y S0);
                              S0 ~> CM (Base.nprod X S0)])))))) |}.

Definition cont_icmonad := 
fun Ans : Type =>
{|
icM := fun X : Type => (X ~> CM Ans) ~~> CM Ans;
icRet := fun X : Type =>
         @IAbs [] X (fun _ : X => (X ~> CM Ans) ~~> CM Ans)
           (fun x : X =>
            @ICAbs [] (X ~> CM Ans) (CM Ans)
              ((fun (Γ : SMSyntax.ctx) (A : Type) 
                  (c : A -> ctype) (v : @arrDom (@CArr A c) I)
                  (t : icterm Γ (@CArr A c)) => @IApp Γ (@CArr A c) I v t)
                 [X ~> CM Ans] X (fun _ : X => CM Ans) x
                 (@ICVar [X ~> CM Ans] 0 (inhabit_infer 0 [X ~> CM Ans]))));
icBind := fun X Y : Type =>
          @ICAbs [] ((X ~> CM Ans) ~~> CM Ans)
            ((X ~> (Y ~> CM Ans) ~~> CM Ans) ~~> (Y ~> CM Ans) ~~> CM Ans)
            (@ICAbs [(X ~> CM Ans) ~~> CM Ans]
               (X ~> (Y ~> CM Ans) ~~> CM Ans) ((Y ~> CM Ans) ~~> CM Ans)
               (@ICAbs
                  [X ~> (Y ~> CM Ans) ~~> CM Ans; (X ~> CM Ans) ~~> CM Ans]
                  (Y ~> CM Ans) (CM Ans)
                  ((fun (Γ : SMSyntax.ctx) (c1 c2 : ctype)
                      (t1 : icterm Γ (c1 ~~> c2))
                      (t2 : icterm Γ (@arrCDom (c1 ~~> c2) I)) =>
                    @ICApp Γ (c1 ~~> c2) I t1 t2)
                     [Y ~> CM Ans; X ~> (Y ~> CM Ans) ~~> CM Ans;
                     (X ~> CM Ans) ~~> CM Ans] (X ~> CM Ans) 
                     (CM Ans)
                     (@ICVar
                        [Y ~> CM Ans; X ~> (Y ~> CM Ans) ~~> CM Ans;
                        (X ~> CM Ans) ~~> CM Ans] 2
                        (inhabit_infer 2
                           [Y ~> CM Ans; X ~> (Y ~> CM Ans) ~~> CM Ans;
                           (X ~> CM Ans) ~~> CM Ans]))
                     (@IAbs
                        [Y ~> CM Ans; X ~> (Y ~> CM Ans) ~~> CM Ans;
                        (X ~> CM Ans) ~~> CM Ans] X 
                        (fun _ : X => CM Ans)
                        (fun x : X =>
                         (fun (Γ : SMSyntax.ctx) (c1 c2 : ctype)
                            (t1 : icterm Γ (c1 ~~> c2))
                            (t2 : icterm Γ (@arrCDom (c1 ~~> c2) I)) =>
                          @ICApp Γ (c1 ~~> c2) I t1 t2)
                           [Y ~> CM Ans; X ~> (Y ~> CM Ans) ~~> CM Ans;
                           (X ~> CM Ans) ~~> CM Ans] 
                           (Y ~> CM Ans) (CM Ans)
                           ((fun (Γ : SMSyntax.ctx) 
                               (A : Type) (c : A -> ctype)
                               (v : @arrDom (@CArr A c) I)
                               (t : icterm Γ (@CArr A c)) =>
                             @IApp Γ (@CArr A c) I v t)
                              [Y ~> CM Ans; X ~> (Y ~> CM Ans) ~~> CM Ans;
                              (X ~> CM Ans) ~~> CM Ans] X
                              (fun _ : X => (Y ~> CM Ans) ~~> CM Ans) x
                              (@ICVar
                                 [Y ~> CM Ans; X ~> (Y ~> CM Ans) ~~> CM Ans;
                                 (X ~> CM Ans) ~~> CM Ans] 1
                                 (inhabit_infer 1
                                    [Y ~> CM Ans;
                                    X ~> (Y ~> CM Ans) ~~> CM Ans;
                                    (X ~> CM Ans) ~~> CM Ans])))
                           (@ICVar
                              [Y ~> CM Ans; X ~> (Y ~> CM Ans) ~~> CM Ans;
                              (X ~> CM Ans) ~~> CM Ans] 0
                              (inhabit_infer 0
                                 [Y ~> CM Ans; X ~> (Y ~> CM Ans) ~~> CM Ans;
                                 (X ~> CM Ans) ~~> CM Ans]))))))) |}.

Definition monst_icmonad := 
fun (S0 : Type) (rel_st : Relation_Definitions.relation S0)
  (H : @RelationClasses.PreOrder S0 rel_st) =>
{|
icM := fun X : Type =>
       @CArr S0
         (fun s0 : S0 =>
          CM (Base.nprod X (@Base.subtype S0 (fun s1 : S0 => rel_st s0 s1))));
icRet := fun X : Type =>
         @IAbs [] X
           (fun _ : X =>
            @CArr S0
              (fun s0 : S0 =>
               CM (Base.nprod X (@Base.subtype S0 (rel_st s0)))))
           (fun x : X =>
            @IAbs [] S0
              (fun s0 : S0 =>
               CM (Base.nprod X (@Base.subtype S0 (rel_st s0))))
              (fun s0 : S0 =>
               (fun (Γ : SMSyntax.ctx) (A : Type) 
                  (c : A -> ctype) (v : @arrDom (@CArr A c) I)
                  (t : icterm Γ (@CArr A c)) => @IApp Γ (@CArr A c) I v t) []
                 (Base.nprod X (@Base.subtype S0 (rel_st s0)))
                 (fun _ : Base.nprod X (@Base.subtype S0 (rel_st s0)) =>
                  CM (Base.nprod X (@Base.subtype S0 (rel_st s0))))
                 {|
                 Base.nfst := x;
                 Base.nsnd := {|
                              Base.wit := s0;
                              Base.pf :=  RelationClasses.PreOrder_Reflexive s0 |} |}
                 (@IMRet [] (Base.nprod X (@Base.subtype S0 (rel_st s0))))));
icBind := fun X Y : Type =>
          @ICAbs []
            (@CArr S0
               (fun s0 : S0 =>
                CM
                  (Base.nprod X
                     (@Base.subtype S0 (fun s1 : S0 => rel_st s0 s1)))))
            ((X ~>
              @CArr S0
                (fun s0 : S0 =>
                 CM
                   (Base.nprod Y
                      (@Base.subtype S0 (fun s1 : S0 => rel_st s0 s1))))) ~~>
             @CArr S0
               (fun s0 : S0 =>
                CM (Base.nprod Y (@Base.subtype S0 (rel_st s0)))))
            (@ICAbs
               [@CArr S0
                  (fun s0 : S0 =>
                   CM
                     (Base.nprod X
                        (@Base.subtype S0 (fun s1 : S0 => rel_st s0 s1))))]
               (X ~>
                @CArr S0
                  (fun s0 : S0 =>
                   CM
                     (Base.nprod Y
                        (@Base.subtype S0 (fun s1 : S0 => rel_st s0 s1)))))
               (@CArr S0
                  (fun s0 : S0 =>
                   CM (Base.nprod Y (@Base.subtype S0 (rel_st s0)))))
               (@IAbs
                  [X ~>
                   @CArr S0
                     (fun s0 : S0 =>
                      CM
                        (Base.nprod Y
                           (@Base.subtype S0 (fun s1 : S0 => rel_st s0 s1))));
                  @CArr S0
                    (fun s0 : S0 =>
                     CM
                       (Base.nprod X
                          (@Base.subtype S0 (fun s1 : S0 => rel_st s0 s1))))]
                  S0
                  (fun s0 : S0 =>
                   CM (Base.nprod Y (@Base.subtype S0 (rel_st s0))))
                  (fun s0 : S0 =>
                   (fun (Γ : SMSyntax.ctx) (c1 c2 : ctype)
                      (t1 : icterm Γ (c1 ~~> c2))
                      (t2 : icterm Γ (@arrCDom (c1 ~~> c2) I)) =>
                    @ICApp Γ (c1 ~~> c2) I t1 t2)
                     [X ~>
                      @CArr S0
                        (fun s1 : S0 =>
                         CM
                           (Base.nprod Y
                              (@Base.subtype S0 (fun s2 : S0 => rel_st s1 s2))));
                     @CArr S0
                       (fun s1 : S0 =>
                        CM
                          (Base.nprod X
                             (@Base.subtype S0 (fun s2 : S0 => rel_st s1 s2))))]
                     (CM
                        (Base.nprod X
                           (@Base.subtype S0 (fun s1 : S0 => rel_st s0 s1))))
                     (CM (Base.nprod Y (@Base.subtype S0 (rel_st s0))))
                     ((fun (Γ : SMSyntax.ctx) (c1 c2 : ctype)
                         (t1 : icterm Γ (c1 ~~> c2))
                         (t2 : icterm Γ (@arrCDom (c1 ~~> c2) I)) =>
                       @ICApp Γ (c1 ~~> c2) I t1 t2)
                        [X ~>
                         @CArr S0
                           (fun s1 : S0 =>
                            CM
                              (Base.nprod Y
                                 (@Base.subtype S0
                                    (fun s2 : S0 => rel_st s1 s2))));
                        @CArr S0
                          (fun s1 : S0 =>
                           CM
                             (Base.nprod X
                                (@Base.subtype S0
                                   (fun s2 : S0 => rel_st s1 s2))))]
                        (Base.nprod X
                           (@Base.subtype S0 (fun s1 : S0 => rel_st s0 s1)) ~>
                         CM (Base.nprod Y (@Base.subtype S0 (rel_st s0))))
                        (CM
                           (Base.nprod X
                              (@Base.subtype S0 (fun s1 : S0 => rel_st s0 s1))) ~~>
                         CM (Base.nprod Y (@Base.subtype S0 (rel_st s0))))
                        ((fun (Γ : list ctype) (A B : Type) =>
                          @ICAbs Γ (A ~> CM B) (CM A ~~> CM B)
                            (@ICAbs ((A ~> CM B) :: Γ) 
                               (CM A) (CM B)
                               (@IMBind (CM A :: (A ~> CM B) :: Γ) A B
                                  (@ICVar (CM A :: (A ~> CM B) :: Γ) 1
                                     (Le.le_n_S 1
                                        (S
                                           ((fix length 
                                             (l : list ctype) : nat :=
                                               match l with
                                               | [] => 0
                                               | _ :: l' => S (length l')
                                               end) Γ))
                                        (Le.le_n_S 0
                                           ((fix length 
                                             (l : list ctype) : nat :=
                                               match l with
                                               | [] => 0
                                               | _ :: l' => S (length l')
                                               end) Γ)
                                           (le_0_n
                                              ((fix length 
                                                (l : list ctype) : nat :=
                                                 match l with
                                                 | [] => 0
                                                 | _ :: l' => S (length l')
                                                 end) Γ)))))
                                  (@ICVar (CM A :: (A ~> CM B) :: Γ) 0
                                     (Le.le_n_S 0
                                        (S
                                           ((fix length 
                                             (l : list ctype) : nat :=
                                               match l with
                                               | [] => 0
                                               | _ :: l' => S (length l')
                                               end) Γ))
                                        (le_0_n
                                           (S
                                              ((fix length 
                                                (l : list ctype) : nat :=
                                                 match l with
                                                 | [] => 0
                                                 | _ :: l' => S (length l')
                                                 end) Γ))))))))
                           [X ~>
                            @CArr S0
                              (fun s1 : S0 =>
                               CM
                                 (Base.nprod Y
                                    (@Base.subtype S0
                                       (fun s2 : S0 => rel_st s1 s2))));
                           @CArr S0
                             (fun s1 : S0 =>
                              CM
                                (Base.nprod X
                                   (@Base.subtype S0
                                      (fun s2 : S0 => rel_st s1 s2))))]
                           (Base.nprod X
                              (@Base.subtype S0 (fun s1 : S0 => rel_st s0 s1)))
                           (Base.nprod Y (@Base.subtype S0 (rel_st s0))))
                        (@IAbs
                           [X ~>
                            @CArr S0
                              (fun s1 : S0 =>
                               CM
                                 (Base.nprod Y
                                    (@Base.subtype S0
                                       (fun s2 : S0 => rel_st s1 s2))));
                           @CArr S0
                             (fun s1 : S0 =>
                              CM
                                (Base.nprod X
                                   (@Base.subtype S0
                                      (fun s2 : S0 => rel_st s1 s2))))]
                           (Base.nprod X
                              (@Base.subtype S0 (fun s1 : S0 => rel_st s0 s1)))
                           (fun
                              _ : Base.nprod X
                                    (@Base.subtype S0
                                       (fun s1 : S0 => rel_st s0 s1)) =>
                            CM (Base.nprod Y (@Base.subtype S0 (rel_st s0))))
                           (fun
                              z : Base.nprod X
                                    (@Base.subtype S0
                                       (fun s1 : S0 => rel_st s0 s1)) =>
                            (fun (Γ : SMSyntax.ctx) 
                               (c1 c2 : ctype) (t1 : icterm Γ (c1 ~~> c2))
                               (t2 : icterm Γ (@arrCDom (c1 ~~> c2) I)) =>
                             @ICApp Γ (c1 ~~> c2) I t1 t2)
                              [X ~>
                               @CArr S0
                                 (fun s1 : S0 =>
                                  CM
                                    (Base.nprod Y
                                       (@Base.subtype S0
                                          (fun s2 : S0 => rel_st s1 s2))));
                              @CArr S0
                                (fun s1 : S0 =>
                                 CM
                                   (Base.nprod X
                                      (@Base.subtype S0
                                         (fun s2 : S0 => rel_st s1 s2))))]
                              (CM
                                 (Base.nprod Y
                                    (@Base.subtype S0
                                       (fun s1 : S0 =>
                                        rel_st
                                          (@Base.wit _ _ (@Base.nsnd _ _ z))
                                          s1))))
                              (CM
                                 (Base.nprod Y (@Base.subtype S0 (rel_st s0))))
                              ((fun (Γ : SMSyntax.ctx) 
                                  (c1 c2 : ctype) 
                                  (t1 : icterm Γ (c1 ~~> c2))
                                  (t2 : icterm Γ (@arrCDom (c1 ~~> c2) I)) =>
                                @ICApp Γ (c1 ~~> c2) I t1 t2)
                                 [X ~>
                                  @CArr S0
                                    (fun s1 : S0 =>
                                     CM
                                       (Base.nprod Y
                                          (@Base.subtype S0
                                             (fun s2 : S0 => rel_st s1 s2))));
                                 @CArr S0
                                   (fun s1 : S0 =>
                                    CM
                                      (Base.nprod X
                                         (@Base.subtype S0
                                            (fun s2 : S0 => rel_st s1 s2))))]
                                 (Base.nprod Y
                                    (@Base.subtype S0
                                       (fun s1 : S0 =>
                                        rel_st
                                          (@Base.wit _ _ (@Base.nsnd _ _ z))
                                          s1)) ~>
                                  CM
                                    (Base.nprod Y
                                       (@Base.subtype S0 (rel_st s0))))
                                 (CM
                                    (Base.nprod Y
                                       (@Base.subtype S0
                                          (fun s1 : S0 =>
                                           rel_st
                                             (@Base.wit _ _
                                                (@Base.nsnd _ _ z)) s1))) ~~>
                                  CM
                                    (Base.nprod Y
                                       (@Base.subtype S0 (rel_st s0))))
                                 ((fun (Γ : list ctype) (A B : Type) =>
                                   @ICAbs Γ (A ~> CM B) 
                                     (CM A ~~> CM B)
                                     (@ICAbs ((A ~> CM B) :: Γ) 
                                        (CM A) (CM B)
                                        (@IMBind (CM A :: (A ~> CM B) :: Γ) A
                                           B
                                           (@ICVar 
                                              (CM A :: (A ~> CM B) :: Γ) 1
                                              (inhabit_infer 1 (CM A :: (A ~> CM B) :: Γ)))
                                           (@ICVar 
                                              (CM A :: (A ~> CM B) :: Γ) 0
                                              (inhabit_infer 0 (CM A :: (A ~> CM B) :: Γ))))))
                                    [X ~>
                                     @CArr S0
                                       (fun s1 : S0 =>
                                        CM
                                          (Base.nprod Y
                                             (@Base.subtype S0
                                                (fun s2 : S0 => rel_st s1 s2))));
                                    @CArr S0
                                      (fun s1 : S0 =>
                                       CM
                                         (Base.nprod X
                                            (@Base.subtype S0
                                               (fun s2 : S0 => rel_st s1 s2))))]
                                    (Base.nprod Y
                                       (@Base.subtype S0
                                          (fun s1 : S0 =>
                                           rel_st
                                             (@Base.wit _ _
                                                (@Base.nsnd _ _ z)) s1)))
                                    (Base.nprod Y
                                       (@Base.subtype S0 (rel_st s0))))
                                 (@IAbs
                                    [X ~>
                                     @CArr S0
                                       (fun s1 : S0 =>
                                        CM
                                          (Base.nprod Y
                                             (@Base.subtype S0
                                                (fun s2 : S0 => rel_st s1 s2))));
                                    @CArr S0
                                      (fun s1 : S0 =>
                                       CM
                                         (Base.nprod X
                                            (@Base.subtype S0
                                               (fun s2 : S0 => rel_st s1 s2))))]
                                    (Base.nprod Y
                                       (@Base.subtype S0
                                          (fun s1 : S0 =>
                                           rel_st
                                             (@Base.wit _ _
                                                (@Base.nsnd _ _ z)) s1)))
                                    (fun
                                       _ : Base.nprod Y
                                             (@Base.subtype S0
                                                (fun s1 : S0 =>
                                                 rel_st
                                                 (@Base.wit _ _
                                                 (@Base.nsnd _ _ z)) s1)) =>
                                     CM
                                       (Base.nprod Y
                                          (@Base.subtype S0 (rel_st s0))))
                                    (fun
                                       r : Base.nprod Y
                                             (@Base.subtype S0
                                                (fun s1 : S0 =>
                                                 rel_st
                                                 (@Base.wit _ _
                                                 (@Base.nsnd _ _ z)) s1)) =>
                                     (fun (Γ : SMSyntax.ctx) 
                                        (A : Type) 
                                        (c : A -> ctype)
                                        (v : @arrDom (@CArr A c) I)
                                        (t : icterm Γ (@CArr A c)) =>
                                      @IApp Γ (@CArr A c) I v t)
                                       [X ~>
                                        @CArr S0
                                          (fun s1 : S0 =>
                                           CM
                                             (Base.nprod Y
                                                (@Base.subtype S0
                                                 (fun s2 : S0 => rel_st s1 s2))));
                                       @CArr S0
                                         (fun s1 : S0 =>
                                          CM
                                            (Base.nprod X
                                               (@Base.subtype S0
                                                 (fun s2 : S0 => rel_st s1 s2))))]
                                       (Base.nprod Y
                                          (@Base.subtype S0 (rel_st s0)))
                                       (fun
                                          _ : Base.nprod Y
                                                (@Base.subtype S0 (rel_st s0))
                                        =>
                                        CM
                                          (Base.nprod Y
                                             (@Base.subtype S0 (rel_st s0))))
                                       {|
                                       Base.nfst := @Base.nfst _ _ r;
                                       Base.nsnd := {|
                                                 Base.wit := @Base.wit _ _
                                                 (@Base.nsnd _ _ r);
                                                 Base.pf := RelationClasses.PreOrder_Transitive s0
                                                 (@Base.wit _ _
                                                 (@Base.nsnd _ _ z))
                                                 (@Base.wit _ _
                                                 (@Base.nsnd _ _ r))
                                                 (@Base.pf _ _
                                                 (@Base.nsnd _ _ z))
                                                 (@Base.pf _ _
                                                 (@Base.nsnd _ _ r)) |} |}
                                       (@IMRet
                                          [X ~>
                                           @CArr S0
                                             (fun s1 : S0 =>
                                              CM
                                                (Base.nprod Y
                                                 (@Base.subtype S0
                                                 (fun s2 : S0 => rel_st s1 s2))));
                                          @CArr S0
                                            (fun s1 : S0 =>
                                             CM
                                               (Base.nprod X
                                                 (@Base.subtype S0
                                                 (fun s2 : S0 => rel_st s1 s2))))]
                                          (Base.nprod Y
                                             (@Base.subtype S0 (rel_st s0)))))))
                              ((fun (Γ : SMSyntax.ctx) 
                                  (A : Type) (c : A -> ctype)
                                  (v : @arrDom (@CArr A c) I)
                                  (t : icterm Γ (@CArr A c)) =>
                                @IApp Γ (@CArr A c) I v t)
                                 [X ~>
                                  @CArr S0
                                    (fun s1 : S0 =>
                                     CM
                                       (Base.nprod Y
                                          (@Base.subtype S0
                                             (fun s2 : S0 => rel_st s1 s2))));
                                 @CArr S0
                                   (fun s1 : S0 =>
                                    CM
                                      (Base.nprod X
                                         (@Base.subtype S0
                                            (fun s2 : S0 => rel_st s1 s2))))]
                                 S0
                                 (fun s1 : S0 =>
                                  CM
                                    (Base.nprod Y
                                       (@Base.subtype S0
                                          (fun s2 : S0 => rel_st s1 s2))))
                                 (@Base.wit _ _ (@Base.nsnd _ _ z))
                                 ((fun (Γ : SMSyntax.ctx) 
                                     (A : Type) (c : A -> ctype)
                                     (v : @arrDom (@CArr A c) I)
                                     (t : icterm Γ (@CArr A c)) =>
                                   @IApp Γ (@CArr A c) I v t)
                                    [X ~>
                                     @CArr S0
                                       (fun s1 : S0 =>
                                        CM
                                          (Base.nprod Y
                                             (@Base.subtype S0
                                                (fun s2 : S0 => rel_st s1 s2))));
                                    @CArr S0
                                      (fun s1 : S0 =>
                                       CM
                                         (Base.nprod X
                                            (@Base.subtype S0
                                               (fun s2 : S0 => rel_st s1 s2))))]
                                    X
                                    (fun _ : X =>
                                     @CArr S0
                                       (fun s1 : S0 =>
                                        CM
                                          (Base.nprod Y
                                             (@Base.subtype S0
                                                (fun s2 : S0 => rel_st s1 s2)))))
                                    (@Base.nfst _ _ z)
                                    (@ICVar
                                       [X ~>
                                        @CArr S0
                                          (fun s1 : S0 =>
                                           CM
                                             (Base.nprod Y
                                                (@Base.subtype S0
                                                 (fun s2 : S0 => rel_st s1 s2))));
                                       @CArr S0
                                         (fun s1 : S0 =>
                                          CM
                                            (Base.nprod X
                                               (@Base.subtype S0
                                                 (fun s2 : S0 => rel_st s1 s2))))]
                                       0
                                       (inhabit_infer 0
                                          [X ~>
                                           @CArr S0
                                             (fun s1 : S0 =>
                                              CM
                                                (Base.nprod Y
                                                 (@Base.subtype S0
                                                 (fun s2 : S0 => rel_st s1 s2))));
                                          @CArr S0
                                            (fun s1 : S0 =>
                                             CM
                                               (Base.nprod X
                                                 (@Base.subtype S0
                                                 (fun s2 : S0 => rel_st s1 s2))))])))))))
                     ((fun (Γ : SMSyntax.ctx) (A : Type) 
                         (c : A -> ctype) (v : @arrDom (@CArr A c) I)
                         (t : icterm Γ (@CArr A c)) =>
                       @IApp Γ (@CArr A c) I v t)
                        [X ~>
                         @CArr S0
                           (fun s1 : S0 =>
                            CM
                              (Base.nprod Y
                                 (@Base.subtype S0
                                    (fun s2 : S0 => rel_st s1 s2))));
                        @CArr S0
                          (fun s1 : S0 =>
                           CM
                             (Base.nprod X
                                (@Base.subtype S0
                                   (fun s2 : S0 => rel_st s1 s2))))] S0
                        (fun s1 : S0 =>
                         CM
                           (Base.nprod X
                              (@Base.subtype S0 (fun s2 : S0 => rel_st s1 s2))))
                        s0
                        (@ICVar
                           [X ~>
                            @CArr S0
                              (fun s1 : S0 =>
                               CM
                                 (Base.nprod Y
                                    (@Base.subtype S0
                                       (fun s2 : S0 => rel_st s1 s2))));
                           @CArr S0
                             (fun s1 : S0 =>
                              CM
                                (Base.nprod X
                                   (@Base.subtype S0
                                      (fun s2 : S0 => rel_st s1 s2))))] 1
                           (inhabit_infer 1
                              [X ~>
                               @CArr S0
                                 (fun s1 : S0 =>
                                  CM
                                    (Base.nprod Y
                                       (@Base.subtype S0
                                          (fun s2 : S0 => rel_st s1 s2))));
                              @CArr S0
                                (fun s1 : S0 =>
                                 CM
                                   (Base.nprod X
                                      (@Base.subtype S0
                                         (fun s2 : S0 => rel_st s1 s2))))])))))) |}.

End GeneratedICMonad.


(* Goal forall S A m, ICApp isArrCPf (ICApp isArrCPf (icBind (st_icmonad S) A A) m) (icRet (st_icmonad S) A) ≅ m. *)
(* Proof. *)
(*   intros. *)
(*   match goal with *)
(*   | [|- ?m1 ≅ _] => set (Hm1 := icterm_eval_sound 3 m1) *)
(*   end. *)
(*   (* Transparent Substitution.dlookup. *) *)
(*   (* Transparent Substitution.dmap. *) *)
(*   (* Transparent weaken0. *) *)
(*   cbv in Hm1. *)
(*   simpl in Hm1. *)
  
  (* icBindRet : forall A m, ICApp (ICApp (icBind A A) m) (icRet A) ≅ m; *)
      (* icRetBind : forall A B f x, ICApp (ICApp (icBind A B) (IApp x (icRet A) eq_refl)) f ≅ IApp x f eq_refl ; *)
      (* icAssoc : forall A B C m f g, *)
      (*     ICApp (ICApp (icBind B C) (ICApp (ICApp (icBind A B) m) f)) g  *)
      (*           ≅ *)

      (*           ICApp (ICApp (icBind A C) m) (IAbs (fun x => (ICApp (ICApp (icBind B C) (IApp x f eq_refl)) g))) *)