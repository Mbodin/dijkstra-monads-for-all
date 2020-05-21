From Coq Require Import List ssreflect.
From Mon.sprop Require Import SPropBase.
From Equations Require Equations.



Lemma list_extensionality {A} (a:A) (l1 : list A)
  : forall l2, length l1 = length l2 -> (forall n, nth n l1 a = nth n l2 a) -> l1 = l2.
Proof.
  induction l1.
  intros [] ? ? ; [reflexivity | discriminate].
  intros [] Heq. discriminate. injection Heq.
  intros ? f ; f_equal. exact (f 0).
  apply IHl1. assumption. intros n ; exact (f (S n)).
Defined.

(** List depending on a list -- used to implement substitution *)


Module Type Ctx.
  Parameter A : Type.
End Ctx.

Set Universe Polymorphism.

Module DList(C : Ctx).
  Import C.
  Import ListNotations.
  Import Equations.
  Import SPropNotations.

  Section DListDef.
    Context (B: A -> Type).

    Inductive dlist : list A -> Type :=
    | dNil : dlist nil
    | dCons : forall {x xs} (y:B x), dlist xs -> dlist (x :: xs).
    Derive Signature for dlist.
    Derive NoConfusion for dlist.
  End DListDef.

  Arguments dNil {_}.
  Arguments dCons {_ _ _} _ _.

  Section dmapDef.
    Context {B1 B2 : A -> Type}.

    Equations dmap {l} (f: forall x:A, B1 x -> B2 x) (v:dlist B1 l) : dlist B2 l :=
      dmap _ dNil := dNil ;
      dmap f (dCons y ys) := dCons (f _ y) (dmap f ys). 

    Lemma dmap_ext {l} (f1 f2 : forall x:A, B1 x -> B2 x) (v1 v2:dlist B1 l) :
      v1 = v2 -> (forall a b1, f1 a b1 = f2 a b1) -> dmap f1 v1 = dmap f2 v2.
    Proof.
      funelim (dmap f1 v1) ; intros Hv Hf; dependent elimination Hv;
        simp dmap ; f_equal ; auto.
    Qed.
  End dmapDef.

  Definition iid {B} (i:A) (x: B i) := x.
  Definition icompose {B1 B2 B3} (f : forall i:A, B1 i -> B2 i) (g: forall i:A, B2 i -> B3 i) := fun {i:A} x => g i (f i x).

  Lemma dmap_id {B l} (v:dlist B l) : dmap iid v = v.
  Proof.
    funelim (dmap iid v) ; [ reflexivity | rewrite dmap_equation_2 ; f_equal ; assumption ].
  Qed.

  Lemma dmap_compose {B1 B2 B3 l} (v : dlist B1 l) f g :
    dmap (@icompose B1 B2 B3 f g) v = dmap g (dmap f v).
  Proof.
    funelim (dmap (@icompose B1 B2 B3 f g) v); simp dmap.
    reflexivity.
    f_equal ; assumption.
  Qed.


  Equations insert (n:nat) (x:A) (l:list A) : list A :=
    insert 0 x l := x :: l ;
    insert (S n) _ nil := nil ;
    insert (S n) x (y :: ys) := y :: insert n x ys.

  Equations remove (l:list A) (n:nat) : list A :=
    remove nil _ := nil ;
    remove (_ :: l) 0 := l ;
    remove (y :: ys) (S n) := y :: remove ys n.

  Lemma remove_insert_id (n:nat) (x:A) l :
    remove (insert n x l) n = l.
  Proof.
    funelim (insert n x l) ; simp remove.
    - reflexivity.
    - reflexivity.
    - rewrite insert_equation_3. simp remove. f_equal. assumption.
  Defined.


  Equations? lookup (n:nat) (l:list A) (H:n s< length l) : A :=
    lookup n nil H := _ ;
    lookup 0 (x :: _) _ := x ;
    lookup (S n) (_ :: xs) H := lookup n xs _.
  Proof. enough sEmpty as [] ; inversion H. inversion H ; assumption. Defined.
  Arguments lookup {_ _} _.
  Transparent lookup.

  (* Check (fun n l (H0 H1 : n s< length l) => eq_refl : @lookup n l H0 = @lookup n l H1). *)
  (* Check (fun n (x:A) l (H0: (S n) s< length (x::l)) (H1: n s< length l) => eq_refl : @lookup (S n) (x :: l) H0 = @lookup n l H1). *)

  Definition lookup_irr l : forall n1 n2 (en: n1 = n2) (H1 : n1 s< length l) (H2 : n2 s< length l), lookup H1 = lookup H2.
  Proof.
    induction l as [|x xs].
    intros ? ? ? H ; enough sEmpty as [] ; inversion H.
    intros [|n1] [|n2] ** ; try discriminate ; simp lookup.
    reflexivity.
    apply IHxs. injection en ; trivial.
  Defined.


  Equations upd (n:nat) (a:A) (l:list A) : list A :=
    upd _ _ nil := nil ;
    upd 0 a (_ :: l) := a :: l ;
    upd (S n) a (x :: l) := x :: (upd n a l).



  Lemma insert_remove_id (n:nat) l (H:n s< length l) :
    insert n (lookup H) (remove l n) = l.
  Proof.
    funelim (remove l n).
    - enough sEmpty as [] ; inversion H.
    - simp lookup ; simp insert ; reflexivity.
    - rewrite remove_equation_3. simp lookup ; simp insert ; f_equal. apply H.
  Qed.


  Equations dinsert {B} (n:nat) {x l} (y:B x) (v:dlist B l) : dlist B (insert n x l) :=
    dinsert 0 y v := dCons y v ;
    dinsert (S n)  _ dNil := dNil ;
    dinsert (S n) y (dCons v0 vs) := dCons v0 (dinsert n y vs). 

  Equations dremove {B} {l} (v:dlist B l) (n:nat): dlist B (remove l n) :=
    dremove dNil _ := dNil ;
    dremove (dCons _ v) 0 := v ;
    dremove (dCons v0 vs) (S n) := dCons v0 (dremove vs n).

  Transparent remove.
  Equations dinsert_rm {B} l (n:nat) (H:n s< length l) (y:B (lookup H)) (v:dlist B (remove l n)) : dlist B l :=
    dinsert_rm nil n H _ _ := ltac:(enough sEmpty as [] ; inversion H) ;
    dinsert_rm (_ :: _) 0 _ y v := dCons y v ;
    dinsert_rm (_ :: _) (S n) H y (dCons v0 vs) := dCons v0 (dinsert_rm _ n _ y vs).
  Next Obligation.
    revert n H y v.
    induction l.
    intros ? H ; enough sEmpty as [] ; inversion H.
    intros [|n] ? y v ; dependent elimination v; simp dinsert_rm.
  Defined.

  Equations? dlookup {B} n l (v:dlist B l) (H:n s< length l): B (lookup H) :=
    dlookup n nil _ H  := _ ;
    dlookup 0 (_ :: _) (dCons x _) _ := x;
    dlookup (S n) (_ :: _) (dCons _ v) H := dlookup n _ v _.
  Proof. enough sEmpty as [] ; inversion H. Qed.
  (* For some reason I do not understand, dlookup never simplifies *)
  Ltac simp_dlookup :=
    match goal with
    | [|- context x [dlookup ?n ?l ?v ?H]] =>
      let l0 := eval cbv in l in
          match l0 with
          | nil => enough sEmpty as [] ; inversion H
          | _ =>
            let n0 := eval cbv in n in
                match n0 with
                | 0 => rewrite (dlookup_equation_2 _ _ _ _ _ _)
                | S _ => rewrite (dlookup_equation_3 _ _ _ _ _ _ _)
                end
          end
    end.

  Next Obligation.
    move: n H ; induction v.
    intros ; simp_dlookup.
    move=> [|n] ? ; simp_dlookup ; constructor. apply IHv.
  Defined.

  Transparent upd.
  Equations dupd {B} n {a} (x : B a) {l} (v:dlist B l)
    : dlist B (upd n a l) :=
    dupd 0 _ dNil := dNil ;
    dupd (S n) _ dNil := dNil ;
    dupd 0 x (dCons _ v) := dCons x v ;
    dupd (S n) x (dCons z v) := dCons z (dupd n x v).

  Transparent lookup.
  Equations dupd' {B} n {l} (H:n s< length l) (x : B (lookup H)) (v:dlist B l)
    : dlist B l :=
    dupd' _ H _ dNil := ltac:(enough sEmpty as [] ; inversion H) ;
    dupd' 0 _ x (dCons _ v) := dCons x v ;
    dupd' (S n) H x (dCons z v) := dCons z (dupd' n _ x v).

  Lemma dlookup_dupd'_id {B} n {l} (H:n s< length l) (v:dlist B l) :
    dupd' n H (dlookup n _ v H) v = v.
  Proof.
    revert n H.
    induction v ; move => n H.
    simp_dlookup.
    destruct n ; simp_dlookup ; simp dupd'=>//.
    rewrite IHv //.
  Qed.

  Section Ap.
    Context (X Y:Type) (x1 x2 : X) (hx : x1 = x2) (f : X -> Y).
    Definition ap : f x1 = f x2 :=
      match hx in _ = x return f x1 = f x with
      | eq_refl => eq_refl
      end.
  End Ap.
  Section Apd.
    Context (X:Type) (Y : X -> Type) 
            (x1 x2 : X) (hx : x1 = x2) (f : forall x, Y x).
    Import EqNotations.
    Definition apd : rew hx in f x1 = f x2 :=
      match hx as h in _ = x return rew h in f x1 = f x with
      | eq_refl => eq_refl
      end.
  End Apd.

  Section dlistExt.
    Context (a0:A) (B: A -> Type).
    Import EqNotations.
    Let lkp_eq {l1} : forall {l2 : list A} n {H1} (Hl: l1 = l2),
          @lookup n l1 H1 = @lookup n l2 (eq_sind (fun l => n s< length l) H1 Hl).
    Proof. intros. dependent elimination Hl. reflexivity. Defined.
             
    (* Let lkp_eq {l1} : forall {l2 : list A} n {H1 H2}, *)
    (*    l1 = l2 -> @lookup n l1 H1 = @lookup n l2 H2. *)
    (* Proof. *)
    (*   induction l1. intros ? ? H ; enough sEmpty as [] ; inversion H. *)
    (*   intros [] ;[discriminate|]. *)
    (*   intros [] ? ? Heq ; *)
    (*     dependent elimination Heq ; simp lookup. reflexivity. *)
    (*   apply IHl1. reflexivity. *)
    (* Defined. *)
      (* induction 1. apply lookup_irr. reflexivity. Defined. *)

    Lemma box_irr :forall (p:SProp) (x1 x2 :p), box x1 = box x2.
    Proof. reflexivity. Defined.

    Ltac change_sprop H1 H2 :=
      change H1 with (unbox (box H1));
      dependent rewrite (box_irr _ H1 H2) ;
      change (unbox (box H2)) with H2.

    Lemma sprop_app_irr
      : forall {p:SProp} {Z : p -> Type} (f : forall (x:p), Z x) (x1 x2 : p), f x1 = f x2.
    Proof. reflexivity. Defined.

    Lemma rew_sprop_eq 
      : forall {p:SProp} {Z : p -> Type}
          (f : forall (x:p), Z x) (g : forall (x:p), Z x) (x1 x2 : p),
        (f x1 = g x1) = (f x2 = g x2).
    Proof. reflexivity. Defined.

    Lemma rew_sprop_eq' 
      : forall {p:SProp} {Z : p -> Type}
          (f : forall (x:p), Z x) (g : forall (x:p), Z x) (x1 x2 : p),
        f x1 = g x1 -> f x2 = g x2.
    Proof. intros ; rewrite <- (rew_sprop_eq f g x1 x2). assumption. Defined.

    Definition dlist_extensionality {l1} (v1 : dlist B l1)
      : forall l2 (Hl : l1 = l2) (v2: dlist B l2),
        (forall n H1, rew lkp_eq n Hl in dlookup n l1 v1 H1 =
                                    dlookup n l2 v2 (eq_sind (fun l => n s< length l) H1 Hl)) ->
        rew Hl in v1 = v2.
    Proof.
      induction v1 ; intros ? Hl v2.
      dependent elimination v2. dependent elimination Hl. reflexivity.
      inversion Hl.
      dependent elimination v2. 
      inversion Hl.
      dependent elimination Hl. intros f.
      simpl. f_equal.
      assert (0 s< length (x ::xs)) as H0 by do 2 constructor.
      move: (f 0 H0) => //.
      apply (IHv1 _ eq_refl).
      intros n H ; assert (S n s< length (x ::xs)) as Hsn by (constructor ; assumption). 
      move: (f (S n) Hsn) => //.
      simpl.
      do 2 simp_dlookup.
      apply (rew_sprop_eq' (dlookup n xs v1) (dlookup n xs d) (lookup_obligation_2 n x xs Hsn)).
   Qed.
      (* Set Printing Implicit. *)
      (* pose (sprop_app_irr (dlookup n xs v1) H (lookup_obligation_2 n x xs Hsn)). *)
      (* pose (sprop_app_irr (dlookup n xs d) H (lookup_obligation_2 n x xs Hsn)). *)
      (* assert (rew (sprop_app_irr (@lookup n xs) _ _) in dlookup n xs v1 H = dlookup n xs v1 (lookup_obligation_2 n x xs Hsn)). *)
      (* simpl. apply (sprop_app_irr (dlookup n xs v1) H (lookup_obligation_2 n x xs Hsn)). *)
      (*   reflexivity. *)
      (* change_sprop (lookup_obligation_2 n x xs Hsn) H. *)
        
      (* intros H0 ; simple refine H0. *)

      (* simpl. intros H'. exact H'. *)
      (* intros. simpl. *)

      (* assert (box H = box H2) by reflexivity. *)
      (* pose (Hf _ _ (fun H' => @lkp_eq xs xs n H H' (@eq_refl (list A) xs)) H H2).  *)
      (* simpl in e |- *. rewrite <- e. *)
      (* assert (@lkp_eq xs xs n H H2 (@eq_refl (list A) xs) = @lkp_eq xs xs n H H (@eq_refl (list A) xs)). *)
      (* simpl. do 2 simp_dlookup. *)
      (* intros. simpl. *)
      (* exact f0. *)
      (* cbv. move=> //=. *)
      (* reflexivity. *)
  End dlistExt.



  Transparent remove.
  Lemma dinsert_rm_dremove_id {B} l n H (v : dlist B l) :
    dinsert_rm l n H (dlookup n l v H) (dremove v n) = v.
  Proof.
    revert n H.
    induction v.
    intros ; simp_dlookup.
    intros [|n] H ; simp_dlookup; simp dremove.
    rewrite (dinsert_rm_equation_2 B x xs H y _) //.
    simp dinsert_rm. f_equal. apply IHv.
  Qed.

  Lemma dlookup_dinsert_rm_id {B} l n H x
        (v:dlist B (remove l n))  : dlookup n l (dinsert_rm l n H x v) H = x.
  Proof.
    revert n H x v.
    induction l.
    intros ; simp_dlookup.
    intros [|] H ? ? .
    rewrite (dinsert_rm_equation_2 B a l H _ _) ; simp_dlookup ; reflexivity.
    dependent elimination v.
    simp dinsert_rm; simp_dlookup; apply (IHl n _ x d).
  Qed.

  Definition dhd' {B x xs} (v:dlist B (x :: xs)) : B x.
  Proof. dependent elimination v ; assumption. Defined.

  Equations dtl {B l} (v:dlist B l) : dlist B (tl l) := 
    dtl dNil := dNil ;
    dtl (dCons _ vs) := vs.

  Lemma dlookup_dmap {B1 B2 l} n H f (v:dlist B1 l) :
    dlookup n _ (@dmap B1 B2 _ f v) H = f _ (dlookup _ _ v H).
  Proof.
    funelim (@dmap B1 B2 _ f v) ; simp dlookup.
    enough sEmpty as [] ; inversion H.
    destruct n ; simp lookup ; simp_dlookup. reflexivity.
  Qed.

  Equations dapp {B l1} (v1 : dlist B l1) {l2} (v2 : dlist B l2) : dlist B (l1 ++ l2) :=
    dapp dNil v2 := v2 ;
    dapp (dCons x v1) v2 := dCons x (dapp v1 v2).

  Lemma dmap_dapp {B1 B2 l1 l2} f v1 v2 :
    @dmap B1 B2 (l1 ++ l2) f (dapp v1 v2) = dapp (dmap f v1) (dmap f v2).
  Proof.
    funelim (dapp v1 v2) ; simp dmap ; simp dapp.
    - reflexivity.
    - rewrite dmap_equation_2. f_equal ; apply H.
  Qed.

  Section FromSection.
    Context {B : A -> Type} (s : forall a, B a).
    Equations from_section l : dlist B l :=
      from_section nil := dNil ;
      from_section (a :: l) := dCons (s a) (from_section l).

    Lemma dlookup_from_section l : forall n H,
      dlookup n l (from_section l) H = s (lookup H).
    Proof.
      induction l ; move=> [|?] ? // ; simp from_section ; simp_dlookup.
    Qed.

  End FromSection.

  Lemma dmap_from_section {B : A -> Type} (s : forall a, B a) l
        {B'} (f : forall a, B a -> B' a) :
      dmap f (from_section s l) = from_section (fun a => f a (s a)) l.
  Proof.
    induction l ; simp from_section ; simp dmap ; f_equal ; auto.
  Qed.

  Section FromSectionIndex.
    Context {B : A -> Type} (s: forall a, nat -> B a).
    Equations from_sectioni l (n:nat) : dlist B l :=
      from_sectioni nil _ := dNil ;
      from_sectioni (a :: l) n := dCons (s a n) (from_sectioni l (S n)).

    Lemma dlookup_from_sectioni l : forall n k H,
      dlookup n l (from_sectioni l k) H = s (lookup H) (n+k).
    Proof.
      induction l ; move=> [|?] ? ? // ; simp from_sectioni ; simp_dlookup.
      simpl. rewrite // plus_n_Sm. apply IHl.
    Qed.
  End FromSectionIndex.

  Lemma dmap_from_sectioni {B : A -> Type} (s : forall a, nat -> B a) l
        {B'} (f : forall a, B a -> B' a) : forall k,
      dmap f (from_sectioni s l k) = from_sectioni (fun a i => f a (s a i)) l k.
  Proof.
    induction l => ? ; simp from_sectioni ; simp dmap ; f_equal ; auto.
  Qed.
  
End DList.
