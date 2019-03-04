From SM Require Import SMSyntax.
From SM Require Import Base.
From Coq Require RelationClasses.

(** Examples of monad internal to SM in PHOAS *)

Section Examples.
  Import SMNotations.

  Section Exception.
    Context (E: Type).
    Definition Exc (X:Type) := CM (X + E).

    Definition exc_ret {X} `{VarType} : cterm (X ~> Exc X) :=
      λ∘ x : X, mret (inl x).

    Definition exc_bind {A B} `{VarType} : cterm (Exc A ~~> (A ~> Exc B) ~~> Exc B) :=
      λ∙ m : Exc A,
      λ∙ f : (A ~> Exc B),
       z ← m ⊱  
        match z with
        | inl x => f @∘ x
        | inr e => mret (inr e)
        end.

    Definition exc_cmonad : cmonad :=
      {| cM := Exc ; cRet := @exc_ret ; cBind := @exc_bind |}.
  End Exception.

  Section State.
    Context (S:Type).

    Definition St (X:Type) := S ~> CM (X × S).

    Definition st_ret {X} `{VarType} := λ∘ x : X, λ∘ s : S, mret ⟨x, s⟩.

    Definition st_bind {A B} `{VarType} :=
      λ∙ m : St A,
        λ∙ f : (A ~> St B),
          λ∘ s : S,
            z ← m @∘ s ⊱ f @∘ (nfst z) @∘ (nsnd z).  

    Definition st_cmonad :cmonad :=
      {| cM := St ; cRet := @st_ret ; cBind := @st_bind |}.
  End State.

  Section Continuations.
    Context (Ans:Type).

    Definition Cont (X:Type) := (X ~> CM Ans) ~~> CM Ans.

    Definition cont_ret {X} `{VarType} := λ∘ x : X, λ∙ k : (X ~> CM Ans), k @∘ x.

    Definition cont_bind {A B} `{VarType} :=
      λ∙ m : Cont A,
        λ∙ f : (A ~> Cont B),
          λ∙ k : (B ~> CM Ans),
            m @∙ (λ∘ x : A, f @∘ x @∙ k).

    Definition cont_cmonad : cmonad :=
      {| cM := Cont ; cRet := @cont_ret ; cBind := @cont_bind |}.

  End Continuations.

  Section MonSt.
    Import Relation_Definitions.
    Import RelationClasses.
    Context (S:Type) (st_rel : relation S) `{PreOrder S st_rel}.
    Definition MonSt (X:Type) := CArr (fun s0:S => CM (X × {s1 : S ∥ st_rel s0 s1})).
    Program Definition monst_ret {X} `{VarType} :=
      λ∘ x : X, λ∘ s0 : S, mret ⟨ x, subt _ (st_rel s0) s0 _ ⟩.
    Next Obligation.
      reflexivity.
    Defined.

    Program Definition monst_bind {A B} `{VarType} :=
      λ∙ m : MonSt A,
        λ∙ f : (A ~> MonSt B),
          λ∘ s0 : S,
            z ← m @∘ s0 ⊱
              r ← f @∘ (nfst z) @∘ (wit (nsnd z)) ⊱
              mret ⟨ nfst r, subt _ (st_rel s0) (wit (nsnd r)) _ ⟩.
    Next Obligation.
      transitivity (wit (nsnd z)).
      exact (pf (nsnd z)).
      exact (pf (nsnd r)).
    Defined.

    Definition monst_cmonad : cmonad :=
      {| cM := MonSt ; cRet := @monst_ret ; cBind := @monst_bind |}.
  End MonSt.

End Examples.





