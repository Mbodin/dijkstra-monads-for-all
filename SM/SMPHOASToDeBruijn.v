From Template Require Import All.
From Coq Require Import List.
Import ListNotations.
From SM Require Import SMSyntax SMExamples.

Quote Definition qimret := @IMRet.
Program Definition imbind := (fun Γ A B => @ICAbs Γ (A ~> CM B) _ (@ICAbs _ (CM A) (CM B) (@IMBind _ A B (@ICVar (_ :: _ :: Γ) 1 _) (@ICVar (_ :: _ :: Γ) 0 _)))).  
Next Obligation.
  repeat apply Le.le_n_S; apply le_0_n.
Defined.
Next Obligation.
  repeat apply Le.le_n_S; apply le_0_n.
Defined.
   
Quote Definition qimbind := Eval cbv in imbind.
Quote Definition qipair := (fun Γ c1 c2 t1 t2 => @ICAbs Γ c1 _ (@ICAbs _ c2 (c1 ⨰ c2) (@IPair _ c1 c2 t1 t2))).
Quote Definition qiproj1 := (fun Γ c1 c2 t => @ICAbs Γ (c1 ⨰ c2) c1 (@IProj1 _ (c1 ⨰ c2) I t)).
Quote Definition qiproj2 := (fun Γ c1 c2 t => @ICAbs Γ (c1 ⨰ c2) c2 (@IProj2 _ (c1 ⨰ c2) I t)).
Quote Definition qiabs := @IAbs.
Quote Definition qiapp := (fun Γ A c v t => @IApp Γ (@CArr A c) I v t).
Quote Definition qicvar := @ICVar.
Quote Definition qicabs := @ICAbs.
Quote Definition qicapp := (fun Γ c1 c2 t1 t2 => @ICApp Γ (c1 ~~> c2) I t1 t2).

Definition icterm_constrs :=
  [qimret ; qimbind ; qipair ; qiproj1 ; qiproj2 ; qiabs ; qiapp ; qicvar ; qicabs ; qicapp ].



Definition icterm_mind := "SM.SMSyntax.icterm".
Definition cterm_mind := "SM.SMSyntax.cterm".


Quote Definition qnil := @nil.
Quote Definition qcons := @cons.

Fixpoint make_list (ty:term) (ls : list term) : term :=
  match ls with
  | nil => tApp qnil [ty]
  | x :: xs => tApp qcons [ty ; x ; make_list ty xs]
  end.

Quote Definition qbool := bool.
Quote Definition qtrue := true.
Quote Definition qfalse := false.
Definition qtest_list := make_list qbool [qtrue ; qfalse ; qtrue].
Make Definition test_list := Eval cbv in qtest_list.

Quote Definition qeq := @eq.
Quote Definition qeqrefl := @eq_refl.


Quote Definition qzero := 0.
Quote Definition qsucc := S.
Definition make_nat (n:nat) : term.
Proof.
  induction n as [|? IH] ; [exact qzero | exact (tApp qsucc [IH])].
Defined.


Record env_t :=
  {
    ctx : list term ;
    map_bvar : list term -> nat -> nat -> term
  }.

Definition add (k:nat) (env : env_t) : env_t :=
  {|
    ctx := map (lift0 k) (ctx env) ;
    map_bvar ctx i j :=
      if Nat.ltb i k
      then tRel (i + j)
      else map_bvar env ctx (i - k) (j + k)
  |}.
Definition succ := add 1.

Definition place qc (env: env_t) :=
  let k0 := List.length (qc :: ctx env) in
  {|
    ctx := qc :: ctx env ;
    map_bvar ctx i j :=
      match i with
      | 0 =>
        let j' := List.length ctx - k0 in 
        make_nat j'
      | S i => map_bvar env ctx i j
      end
  |}.


Quote Definition qfail := "Failed".
Definition default_env := {| ctx := [] ; map_bvar _ i j := qfail |}.


Quote Definition qctype := ctype.
Quote Definition qctype_option := (option ctype).
Quote Definition qsome := @Some.

Axiom leave_me_alone : forall n Γ, in_ctx n Γ.
Quote Definition qleave_me_alone := leave_me_alone.

Fixpoint translate env t :=
  match t with
  | tRel n => map_bvar env (ctx env) n 0
  | tEvar ev args => tEvar ev (List.map (translate env) args)
  | tLambda na T M => tLambda na (translate env T) (translate (succ env) M)
  | tApp u v =>
    let default 'tt := mkApps (translate env u) (List.map (translate env) v) in
    match u with
    | tInd mind l =>
      if eq_string (inductive_mind mind) cterm_mind
      then
        match v with
        | [ qvar ; qc ] =>
          let u' := tInd (mkInd icterm_mind 0) [] in
          tApp u' [make_list qctype (ctx env) ; translate env qc]
        | _ => qfail
        end
      else default tt
    | tConstruct mind k l =>
      if eq_string (inductive_mind mind) cterm_mind
      then
        match k with
        | 7 =>
          match v with
          | [qvar ; qc ; qvar_arg] =>
            let qvar_arg' := translate env qvar_arg in
            let Γ := make_list qctype (ctx env) in
            let in_ctx := tApp qleave_me_alone [qvar_arg' ; Γ] in
            tApp qicvar [ Γ ; qvar_arg' ; in_ctx]
          | _ => qfail
          end
        | 8 =>
          match v with
          | [ qvar ; qc1 ; qc2 ; tLambda x qvarc1 qct ] =>
            let qc1' := translate env qc1 in
            let qc2' := translate env qc2 in
            tApp qicabs [make_list qctype (ctx env)  ; qc1' ; qc2' ;
                           translate (place qc1' env) qct]
          | _ => qfail (* the constructor Abs of cterm takes 4 args, right ? *)
          end
        | _ =>
          match v with
          | nil => qfail
          | qvar :: args =>
            mkApps (nth k icterm_constrs qfail) 
                   (make_list qctype (ctx env)::List.map (translate env) args)
          end
        end
      else default tt
    |  _ => default tt
    end 
  | tProd na A B => tProd na (translate env A) (translate (succ env) B)
  | tCast c kind ty => tCast (translate env c) kind (translate env ty)
  | tLetIn na b ty b' => tLetIn na (translate env b) (translate env ty) (translate (succ env) b')
  | tCase ind p c brs =>
    let brs' := List.map (on_snd (translate env)) brs in
    tCase ind (translate env p) (translate env c) brs'
  | tProj p c => tProj p (translate env c)
  | tFix mfix idx =>
    let env' := add (List.length mfix) env in
    let mfix' := List.map (map_def (translate env')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let env' := add (List.length mfix) env in
    let mfix' := List.map (map_def (translate env')) mfix in
    tCoFix mfix' idx
  | tInd mind l => tInd mind []
  | tConstruct mind n l => tConstruct mind n []
  | tSort _ => tSort []
  | x => x (* FIxME *)
end.


Definition translateFull (t : term) :=
  match t with
  | tLambda _ _ t' => translate default_env t'
  | _ => qfail
  end.


Module Tests.
  Set Printing Universes.
  Quote Definition sumXE := (fun X E => X + E)%type.
  Make Definition sumXE' := Eval cbv in sumXE.

  (* Debugging troubles with universes :
     Make Definition does not handle universes correctly but
     tmMkDefinition does handle them *)
  Definition qt0 :=
    (tLambda (nNamed "E") (tSort [])
      (tLambda (nNamed "X") (tSort [])
                (tApp
                      (tInd
                        {|
                        inductive_mind := "Coq.Init.Datatypes.sum";
                        inductive_ind := 0 |} []) [tRel 0; tRel 1]))).
  Import MonadNotation.
  Run TemplateProgram (x <- tmEval cbv qt0 ;;
                      tmMkDefinition "t0" x).
  (* Make Definition t0 := Eval cbv in qt0. *)

  Quote Definition qexc_ret :=
    ltac:(let t := eval cbv in (fun var E X => @exc_ret E X var) in exact t).
  Definition qexc_ret' := Eval lazy in (translateFull qexc_ret). 
  Run TemplateProgram (x <- tmEval cbv qexc_ret' ;;
                      tmMkDefinition "exc_ret'" x).

  Import SMNotations.
  Quote Definition qstuff := (fun `{VarType} X => λ∙ x : CM X, x).
  Definition qstuff' := Eval lazy in (translateFull qstuff). 
  Run TemplateProgram (x <- tmEval cbv qstuff' ;;
                      tmMkDefinition "stuff'" x).

  Quote Definition qbidule := Eval cbv in (fun `{VarType} X Y => λ∙ x : CM (X + Y), mbind x (λ∘ x : (X+Y),  match x with | inl x => mret 1 | inr y => mret 2 end)).
  Definition qbidule' := Eval cbv in (translateFull qbidule). 
  Run TemplateProgram (x <- tmEval cbv qbidule' ;;
                      tmMkDefinition "bidule'" x).

  Quote Definition qchose := Eval cbv in (fun `{VarType} X => λ∙ x : CM (X), λ∙ y : CM X, x).
  Definition qchose' := Eval lazy in (translateFull qchose). 
  Run TemplateProgram (x <- tmEval cbv qchose' ;;
                      tmMkDefinition "chose'" x).

  Quote Definition qtruc := Eval cbv in
        (fun `{VarType} X => λ∙ f : X ~> CM X, λ∘ x : X, f @∘ x).
  Definition qtruc' := Eval lazy in (translateFull qtruc).
  Run TemplateProgram (x <- tmEval cbv qtruc' ;;
                      tmMkDefinition "truc'" x).

  Quote Definition qexc_bind := Eval cbv in (fun var E X Y => @exc_bind E X Y var).
  Definition qexc_bind' := Eval lazy in (translateFull qexc_bind). 
  Run TemplateProgram (x <- tmEval cbv qexc_bind' ;;
                      tmMkDefinition "exc_bind'" x).

  Quote Definition qcont_ret := Eval cbv in (fun var Ans X => @cont_ret Ans X var).
  Definition qcont_ret' := Eval lazy in (translateFull qcont_ret).
  Run TemplateProgram (x <- tmEval cbv qcont_ret' ;;
                      tmMkDefinition "cont_ret'" x).

  Quote Definition qcont_bind := Eval cbv in (fun var Ans X Y => @cont_bind Ans X Y var).
  Definition qcont_bind' := Eval lazy in (translateFull qcont_bind).
  Run TemplateProgram (x <- tmEval cbv qcont_bind' ;;
                      tmMkDefinition "cont_bind'" x).
End Tests.


Section TranslateCMonad.
  Import MonadNotation.

  Quote Definition qMkICMonad := @MkICMonad.

  Definition translate_cmonad (c : cmonad) : TemplateMonad term :=
    icM <- tmEval cbv (cM c) ;;
    qicM <- tmQuote icM ;;

    cret <- tmEval cbv (fun var X => @cRet c X var) ;;
    qcret <- tmQuote cret;;
    qicret <- tmEval lazy (translateFull qcret) ;;

    cbind <- tmEval cbv (fun var X Y => @cBind c X Y var) ;;
    qcbind <- tmQuote cbind ;;
    qicbind <- tmEval lazy (translateFull qcbind) ;;

    tmEval lazy (tApp qMkICMonad [qicM ; qicret ; qicbind]).

End TranslateCMonad.


Section ICMonads.
  Import MonadNotation.

  Section ExcICMonad.
    Context (E : Type).
    Run TemplateProgram (qicexc <- translate_cmonad (exc_cmonad E) ;;
                                tmMkDefinition "exc_icmonad" qicexc).
  End ExcICMonad.

  Section StICMonad.
    Context (S : Type).
    Run TemplateProgram (qicst <- translate_cmonad (st_cmonad S) ;;
                                tmMkDefinition "st_icmonad" qicst).
  End StICMonad.

  Section ContICMonad.
    Context (Ans : Type).
    Run TemplateProgram (qiccont <- translate_cmonad (cont_cmonad Ans) ;;
                                tmMkDefinition "cont_icmonad" qiccont).
  End ContICMonad.

  Section MonSt.
    Import Relation_Definitions.
    Import RelationClasses.
    Context (S : Type) (rel_st : relation S) `{PreOrder S rel_st}.
    Run TemplateProgram (qicst <- translate_cmonad (monst_cmonad S rel_st) ;;
                                tmMkDefinition "monst_icmonad" qicst).
  End MonSt.

  Set Printing Implicit.
  Print exc_icmonad.
  Print st_icmonad.
  Print cont_icmonad.
  Print monst_icmonad.
End ICMonads.
