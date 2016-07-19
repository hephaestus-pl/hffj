Require Import Syntax.
Require Import List.
Hypothesis ct_fix : CT = (CDecl 1 (ClassObject) nil (KDecl 1 nil nil nil) nil) :: nil .

Lemma ex: (ClassId 1 <: ClassObject).
  apply S_Decl.
  unfold extends.
  rewrite ct_fix.
  simpl.
  eauto.
Qed.

Eval compute in ([ (Id 1) := ExpFieldAccess (ExpVar this) (Id 2)] ExpVar (Id 1)).