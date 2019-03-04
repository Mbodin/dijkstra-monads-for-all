From Coq Require Import List.
From Equations Require Equations.


(** List depending on a list -- used to implement substitution *)

Module Type Ctx.
  Parameter A : Type.
End Ctx.

Module DList(C : Ctx).
  Import C.
  Import ListNotations.
  Import Equations.

  Section DListDef.
    Context (B: A -> Type).

    Inductive dlist : list A -> Type :=
    | dNil : dlist nil
    | dCons : forall {x xs} (y:B x), dlist xs -> dlist (x :: xs).
    Derive Signature for dlist.
  End DListDef.

  Arguments dNil {_}.
  Arguments dCons {_ _ _} _ _.

  Section dmapDef.
    Context {B1 B2 : A -> Type}.

    Equations dmap {l} (f: forall x:A, B1 x -> B2 x) (v:dlist B1 l) : dlist B2 l :=
      dmap _ dNil := dNil ;
      dmap f (dCons y ys) := dCons (f _ y) (dmap f ys). 
  End dmapDef.

  Definition iid {B} (i:A) (x: B i) := x.
  Definition icompose {B1 B2 B3} (f : forall i:A, B1 i -> B2 i) (g: forall i:A, B2 i -> B3 i) := fun {i:A} x => g i (f i x).

  Lemma dmap_id {B l} (v:dlist B l) : dmap iid v = v.
  Proof.
    funelim (dmap iid v) ; [reflexivity | f_equal ; assumption].
  Qed.

  Lemma dmap_compose {B1 B2 B3 l} (v : dlist B1 l) f g :
    dmap (@icompose B1 B2 B3 f g) v = dmap g (dmap f v).
  Proof.
    funelim (dmap (@icompose B1 B2 B3 f g) v); simp dmap.
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
    f_equal ; assumption.
  Defined.

  Equations? lookup (n:nat) (l:list A) (H:n < length l) : A :=
    lookup n nil H := !%prg ;
    lookup 0 (x :: _) _ := x ;
    lookup (S n) (_ :: xs) H := lookup n xs _.
  Proof. inversion H. apply Lt.lt_S_n; assumption. Qed.
  Arguments lookup {_ _} _.

  Definition lookup_irr l : forall n1 n2 (en: n1 = n2) (H1 : n1 < length l) (H2 : n2 < length l), lookup H1 = lookup H2.
  Proof.
    induction l as [|x xs].
    intros ? ? ? H ; inversion H.
    intros [|n1] [|n2] ** ; try discriminate ; simp lookup.
    apply IHxs. injection en ; trivial.
  Defined.

  Lemma insert_remove_id (n:nat) l (H:n < length l) :
    insert n (lookup H) (remove l n) = l.
  Proof.
    funelim (lookup H) ; simp remove ; simp insert.
    inversion H.
    f_equal ; assumption.
  Qed.


  Equations dinsert {B} (n:nat) {x l} (y:B x) (v:dlist B l) : dlist B (insert n x l) :=
    dinsert 0 y v := dCons y v ;
    dinsert (S n)  _ dNil := dNil ;
    dinsert (S n) y (dCons v0 vs) := dCons v0 (dinsert n y vs). 

  Equations dremove {B} {l} (v:dlist B l) (n:nat): dlist B (remove l n) :=
    dremove dNil _ := dNil ;
    dremove (dCons _ v) 0 := v ;
    dremove (dCons v0 vs) (S n) := dCons v0 (dremove vs n).

  (* Import EqNotations. *)
  (* Lemma dremove_dinsert_id {B} (n:nat) {x:A} {l} (y:B x) (v:dlist B l) : *)
  (*   dremove (dinsert n y v) n = rew <- [dlist B] (remove_insert_id n x l) in v. *)
  (* Proof. *)
  (*   funelim (dinsert n y v) ; simp dremove. *)
  (*   f_equal ; assumption. *)
  (* Qed. *)

  Transparent remove.
  Equations? dinsert_rm {B} l (n:nat) (H:n < length l) (y:B (lookup H)) (v:dlist B (remove l n)) : dlist B l :=
    dinsert_rm nil n H _ _ := !%prg ;
    dinsert_rm (_ :: _) 0 _ y v := dCons y v ;
    dinsert_rm (_ :: _) (S n) H y (dCons v0 vs) := dCons v0 (dinsert_rm _ n _ y vs).
  Proof. inversion H. Qed.
  Opaque remove.


  (* Definition dinsert_rm {B} : forall l (n:nat) (H:n < length l) (y:B (lookup H)) (v:dlist B (remove l n)), dlist B l. *)
  (* Proof. *)
  (*   induction l. *)
  (*   intros ? H ; exfalso ; inversion H. *)
  (*   intros [|n] H y v ; simp lookup in y ; simp remove in v. *)
  (*   exact (dCons y v). *)
  (*   dependent destruction v. *)
  (*   apply (dCons y0 (IHl _ _ y v)).  *)
  (* Defined. *)

  Equations? dlookup {B} n l (v:dlist B l) (H:n < length l): B (lookup H) :=
    dlookup n nil _ H  := !%prg ;
    dlookup 0 (_ :: _) (dCons x _) _ := x;
    dlookup (S n) (_ :: _) (dCons _ v) H := dlookup n _ v _.
  Proof. inversion H. Qed.

  Lemma dinsert_rm_dremove_id {B} l n H (v : dlist B l) :
    dinsert_rm l n H (dlookup n l v H) (dremove v n) = v.
  Proof.
    funelim (dremove v n) ; simp dlookup ; simp dinsert_rm.
    inversion H.
    f_equal. apply H.
  Qed.

  Lemma dlookup_dinsert_rm_id {B} l n H x
        (v:dlist B (remove l n))  : dlookup n l (dinsert_rm l n H x v) H = x.
  Proof.
    funelim (dinsert_rm l n H x v) ; simp dlookup.
    inversion H0.
  Qed.

  Equations dhd' {B x xs} (v:dlist B (x :: xs)) : B x :=
    dhd' (dCons v0 _) := v0.

  Equations dtl {B l} (v:dlist B l) : dlist B (tl l) := 
    dtl dNil := dNil ;
    dtl (dCons _ vs) := vs.

  Lemma dlookup_dmap {B1 B2 l} n H f (v:dlist B1 l) :
    dlookup n _ (@dmap B1 B2 _ f v) H = f _ (dlookup _ _ v H).
  Proof.
    funelim (@dmap B1 B2 _ f v) ; simp dlookup.
    inversion H.
    destruct n ; simp lookup ; simp dlookup.
    change (dlookup (S ?n) (_ :: ?l) (dCons _ ?v) ?H) with (dlookup n l v (lookup_obligation_2 n x xs H)).
    change (@lookup (S ?n) (_ :: ?l) ?H) with (@lookup n l (lookup_obligation_2 n x xs H)).
    apply H.
  Qed.


End DList.
