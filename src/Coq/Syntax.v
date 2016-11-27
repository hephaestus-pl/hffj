Require Export List.
Require Export Metatheory.
Require Import String.
Require Export env.

Module Refs.
Notation "'refs' x":= (map ref x) (at level 30).
End Refs.
Export Refs.

Notation "'[' X ']'" := (list X) (at level 40).
(* We will use Notation to make automation easier
 * This will be the notation to be similar with haskell *)

Definition ClassName := id.
Parameter Object: ClassName.

Definition Var := id.
Parameter this: Var.

Inductive Argument :=
  | Arg : id -> Argument.

Inductive Assignment :=
  | Assgnmt : id -> id -> Assignment.

Inductive FormalArg :=
  | FArg : ClassName -> id -> FormalArg.

Instance FargRef : Referable FormalArg :={
  ref farg := 
    match farg with 
   | FArg _ id => id end
}.

Definition fargType (f: FormalArg):ClassName := 
  match f with FArg t _ => t end.

Inductive Constructor :=
  | KDecl : id -> [FormalArg] -> [Argument] -> [Assignment] -> Constructor.

Inductive FieldDecl :=
  | FDecl : ClassName -> id -> FieldDecl.

Instance FieldRef : Referable FieldDecl :={
  ref fdecl := 
    match fdecl with 
   | FDecl _ id => id end
}.

Definition fieldType (f: FieldDecl): ClassName := 
  match f with FDecl t _ => t end.

Inductive Exp : Type :=
  | ExpVar : Var -> Exp
  | ExpFieldAccess : Exp -> id -> Exp
  | ExpMethodInvoc : Exp -> id -> [Exp] -> Exp
  | ExpCast : ClassName -> Exp -> Exp
  | ExpNew : id -> [Exp] -> Exp.

(*
Inductive NoDupList (T:Type) {H: Referable T} (xs: [T]) := 
  |noDup_nil : NoDup (@nil T) -> NoDupList T
  |noDupSome : forall , NoDup  -> NoDupList (map ref xs).

Print NoDupList.
*)

(* Notice that arguments cannot have duplicate names *)
Inductive MethodDecl :=
  | MDecl : ClassName -> id -> forall (fargs: [FormalArg]), NoDup (this :: refs fargs) -> Exp -> MethodDecl.


Instance MDeclRef : Referable MethodDecl :={
  ref mdecl := 
    match mdecl with 
   | MDecl _ id _ _ _ => id end
}.


Inductive ClassDecl:=
  | CDecl: id -> ClassName -> 
    forall (fDecls:[FieldDecl]), NoDup (refs fDecls) -> Constructor -> 
    forall (mDecls:[MethodDecl]), NoDup (refs mDecls) -> ClassDecl.

Instance CDeclRef : Referable ClassDecl :={
  ref cdecl := 
    match cdecl with 
   | CDecl id _ _ _ _ _ _ => id end
}.

Inductive Program :=
  | CProgram : forall (cDecls: [ClassDecl]), NoDup (refs cDecls) -> Exp -> Program.



Parameter CT: [ClassDecl].
(*We will assume a global CT to make our definitions easier
 *To instance the CT use Hypothesis x: CT = ... *)
Axiom sane_CT: find Object CT = None.

Reserved Notation "C '<:' D " (at level 40).
Inductive Subtype : id -> ClassName -> Prop :=
  | S_Refl: forall C: ClassName, C <: C
  | S_Trans: forall (C D E: ClassName), 
    C <: D -> 
    D <: E -> 
    C <: E
  | S_Decl: forall C D fs noDupfs K mds noDupMds,
    find C CT = Some (CDecl C D fs noDupfs K mds noDupMds ) ->
    C <: D
where "C '<:' D" := (Subtype C D).
Hint Constructors Subtype.

Tactic Notation "subtype_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "S_Refl" | Case_aux c "S_Trans" 
  | Case_aux c "S_Decl"].

Axiom subtype_LEM: forall C D,
  C <: D \/ ~ C <: D.


Inductive fields : id -> [FieldDecl] -> Prop :=
 | F_Obj : fields Object nil
 | F_Decl : forall C D fs  noDupfs K mds noDupMds fs', 
     find C CT = Some (CDecl C D fs noDupfs K mds noDupMds) ->
     NoDup (refs fs') ->
     NoDup (refs fs) ->
     fields D fs' ->
     NoDup (refs (fs' ++ fs)) ->
     fields C (fs'++fs).
Tactic Notation "fields_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "F_Obj" | Case_aux c "F_Decl"].

Reserved Notation "'mtype(' m ',' D ')' '=' c '~>' c0" (at level 40, c at next level).
Inductive m_type (m: id) (C: ClassName) (Bs: [ClassName]) (B: ClassName) : Prop:=
  | mty_ok : forall D Fs K Ms fargs noDupfs noDupMds,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds)->
              In m (map ref Ms) ->
              map fargType fargs = Bs ->
              mtype(m, C) = Bs ~> B
  | mty_no_override: forall D Fs K Ms fargs noDupfs noDupMds,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds) ->
              ~In m (map ref Ms) ->
              map fargType fargs = Bs ->
              mtype(m, D) = Bs ~> B ->
              mtype(m, C) = Bs ~> B
  where "'mtype(' m ',' D ')' '=' cs '~>' c0"
        := (m_type m D cs c0).


Inductive m_body (m: id) (C: ClassName) (xs: [ClassName]) (e: Exp) : Prop:=
  | mbdy_ok : forall D Fs K Ms fargs noDupfs noDupMds,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds)->
              In m (map ref Ms) ->
              map ref fargs = xs ->
              m_body m C xs e
  | mbdy_no_override: forall D Fs K Ms fargs noDupfs noDupMds,
              find C CT = Some (CDecl C D Fs noDupfs K Ms noDupMds)->
              ~In m (map ref Ms) ->
              map ref fargs = xs ->
              m_body m D xs e ->
              m_body m C xs e.
Notation "'mbody(' m ',' D ')' '=' xs 'o' e" := (m_body m D xs e) (at level 40).

Hint Constructors m_type m_body fields.
Tactic Notation "mbdy_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "mbdy_ok" | Case_aux c "mbdy_no_override"].

Fixpoint subst (e: Exp) (ds: [Exp]) (xs: [Var]): Exp := 
  match e with
  | ExpVar var => match find_where var xs with
                  | Some i => match nth_error ds i with
                                   | None => e | Some di => di end
                  | None => e end
  | ExpFieldAccess exp i => ExpFieldAccess (subst exp ds xs) i
  | ExpMethodInvoc exp i exps => 
      ExpMethodInvoc (subst exp ds xs) i (map (fun x => subst x ds xs) exps)
  | ExpCast cname exp => ExpCast cname (subst exp ds xs)
  | ExpNew cname exps => ExpNew cname (map (fun x => subst x ds xs) exps)
  end.
Notation " [; ds '\' xs ;] e " := (subst e ds xs) (at level 30).

Eval compute in ([;(ExpVar this) :: ExpFieldAccess (ExpVar this) (Id 2) :: nil \ Id 2 :: Id 1 :: nil;] ExpVar (Id 1)).
Check (subst (ExpVar (Id 1)) ((ExpFieldAccess (ExpVar this) (Id 2))::nil)) ((Id 1)::nil).

(*
Fixpoint subst (e: Exp) (v: Var) (e': Exp) : Exp:=
  match e with
  | ExpVar var => if beq_id var v then e' else e
  | ExpFieldAccess exp i => ExpFieldAccess (subst exp v e') i
  | ExpMethodInvoc exp i exps => 
      ExpMethodInvoc (subst exp v e') i (map (fun x => subst x v e') exps)
  | ExpCast cname exp => ExpCast cname (subst exp v e')
  | ExpNew cname exps => ExpNew cname (map (fun x => subst x v e') exps)
  end.
Notation " ([ v' '\' v ']' e )" := (subst e v v') (at level 35).

Eval compute in (([ExpFieldAccess (ExpVar this) (Id 2) \ Id 1] ExpVar (Id 1))).
Inductive subst_list : Exp -> [Var] -> [Exp] -> Exp -> Prop :=
  | Subst_Var : forall ds xs xi di i,
      nth_error xs i = Some xi->
      nth_error ds i = Some di ->
      [; ds \ xs ;] (ExpVar xi) = di
  | Subst_FieldAcc : forall e: Exp, [; ds \ xs ;] e = e
  | Subst_Invk : forall e: Exp, [; nil \ nil ;] e = e
  | Subst_Cast : forall e: Exp, [; nil \ nil ;] e = e
  | Subst_New : forall e: Exp, [; nil \ nil ;] e = e
  | Subst_cons : forall e1 e2 e3 (e': Exp) (v: Var) es vs,
    ([e' \ v] e1) = e2->
    [;es \ vs;] e2 = e3 ->
    [; e'::es \ v::vs ;] e1 = e3
where " [; es '\' vs ;] e1 '=' e2 " := (subst_list e1 vs es e2).
Print ExpVar.
*)

Inductive appears_free_in : Var -> Exp -> Prop :=
  | afi_var : forall x,
    appears_free_in x (ExpVar x)
  | afi_field : forall x e fi,
    appears_free_in x e ->
    appears_free_in x (ExpFieldAccess e fi)
  | afi_m_invk1 : forall x e mname es,
    appears_free_in x e ->
    appears_free_in x (ExpMethodInvoc e mname es)
  | afi_m_invk2 : forall x e e' mname es,
    List.In e' es ->
    appears_free_in x e' ->
    appears_free_in x (ExpMethodInvoc e mname es)
  | afi_cast : forall x e CName,
    appears_free_in x e ->
    appears_free_in x (ExpCast CName e)
  | afi_new : forall x e es CName,
    List.In e es ->
    appears_free_in x e ->
    appears_free_in x (ExpNew CName es).

Hint Constructors appears_free_in.
Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "afi_var" | Case_aux c "afi_field"
  | Case_aux c "afi_m_invk1" | Case_aux c "afi_m_invk2"
  | Case_aux c "afi_cast" | Case_aux c "afi_new"].


Definition closed (e: Exp) :=
  forall x, ~ appears_free_in x e.

Inductive Warning (s: string) : Prop :=
  | w_str : Warning s.
Notation stupid_warning := (Warning "stupid warning").
Axiom STUPID_STEP : stupid_warning.

Reserved Notation "Gamma '|-' x ':' C" (at level 60, x at next level). Print get.
Inductive ExpTyping (Gamma: env ClassName) : Exp -> ClassName -> Prop :=
  | T_Var : forall x C, get Gamma x = Some C -> 
                Gamma |- ExpVar x : C
  | T_Field: forall e0 C0 fs i Fi Ci fi,
                Gamma |- e0 : C0 ->
                fields C0 fs ->
                nth_error fs i = Some Fi ->
                Ci = fieldType Fi ->
                fi = ref Fi ->
                Gamma |- ExpFieldAccess e0 fi : Ci
  | T_Invk : forall e0 C Cs C0 Ds m es,
                Gamma |- e0 : C0 ->
                mtype(m, C0) = Ds ~> C ->
                Forall2 (ExpTyping Gamma) es Cs ->
                Forall2 Subtype Cs Ds ->
                Gamma |- ExpMethodInvoc e0 m es : C
  | T_New : forall C Ds Cs fs es,
                fields C fs ->
                Ds = map fieldType fs ->
                Forall2 (ExpTyping Gamma) es Cs ->
                Forall2 Subtype Cs Ds ->
                Gamma |- ExpNew C es : C
  | T_UCast : forall e0 D C,
                Gamma |- e0 : D ->
                D <: C ->
                Gamma |- ExpCast C e0 : C
  | T_DCast : forall e0 C D,
                Gamma |- e0 : D ->
                C <: D ->
                C <> D ->
                Gamma |- ExpCast C e0 : C
  | T_SCast : forall e0 D C,
                Gamma |- e0 : D ->
                ~ D <: C ->
                ~ C <: D ->
                stupid_warning ->
                Gamma |- ExpCast C e0 : C
  where " Gamma '|-' e ':' C " := (ExpTyping Gamma e C).

Tactic Notation "typing_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Field" 
  | Case_aux c "T_Invk" | Case_aux c "T_New"
  | Case_aux c "T_UCast" | Case_aux c "T_DCast" 
  | Case_aux c "T_SCast"].

Reserved Notation "e '~>' e1" (at level 60).
Inductive Computation : Exp -> Exp -> Prop :=
  | R_Field : forall C Fs es fi ei i,
            fields C Fs ->
            nth_error Fs i = Some fi ->
            nth_error es i = Some ei-> 
            ExpFieldAccess (ExpNew C es) (ref fi) ~> ei
  | R_Invk : forall C m xs ds es e0,
            mbody(m, C) = xs o e0 ->
            NoDup (this :: xs) ->
            List.length ds = List.length xs ->
            ExpMethodInvoc (ExpNew C es) m ds ~> [; ExpNew C es :: ds \ this :: xs;] e0
  | R_Cast : forall C D es,
            C <: D ->
            ExpCast D (ExpNew C es) ~> ExpNew C es
  | RC_Field : forall e0 e0' f,
            e0 ~> e0' ->
            ExpFieldAccess e0 f ~> ExpFieldAccess e0' f
  | RC_Invk_Recv : forall e0 e0' m es,
            e0 ~> e0' ->
            ExpMethodInvoc e0 m es ~> ExpMethodInvoc e0' m es
  | RC_Invk_Arg : forall e0 ei' m es es' ei,
            ei ~> ei' ->
            In ei es ->
            In ei es' ->
            ExpMethodInvoc e0 m es ~> ExpMethodInvoc e0 m es'
  | RC_New_Arg : forall C ei' es es' ei,
            ei ~> ei' ->
            In ei es ->
            In ei es' ->
            ExpNew C es ~> ExpNew C es'
  | RC_Cast : forall C e0 e0',
            e0 ~> e0' ->
            ExpCast C e0 ~> ExpCast C e0'
  where "e '~>' e1" := (Computation e e1).

Tactic Notation "computation_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "R_Field" | Case_aux c "R_Invk" 
  | Case_aux c "R_Cast" | Case_aux c "RC_Field"
  | Case_aux c "RC_Invk_Recv" | Case_aux c "RC_Invk_Arg" 
  | Case_aux c "RC_New_Arg" | Case_aux c "RC_Cast"].

Definition ExpTyping_ind' := 
  fun (Gamma : env ClassName) (P : Exp -> ClassName -> Prop)
  (f : forall (x : id) (C : ClassName), get Gamma x = Some C -> P (ExpVar x) C)
  (f0 : forall (e0 : Exp) (C0 : ClassName) (fs : [FieldDecl]) (i : nat) (Fi : FieldDecl)
          (Ci : ClassName) (fi : id),
        Gamma |- e0 : C0 ->
        P e0 C0 ->
        fields C0 fs ->
        nth_error fs i = Some Fi -> Ci = fieldType Fi -> fi = ref Fi -> P (ExpFieldAccess e0 fi) Ci)
  (f1 : forall (e0 : Exp) (C : ClassName) (Cs : [ClassName]) (C0 : ClassName) (Ds : [ClassName]) 
          (m : id) (es : [Exp]),
        Gamma |- e0 : C0 ->
        P e0 C0 ->
        mtype( m, C0)= Ds ~> C ->
        Forall2 (ExpTyping Gamma) es Cs ->
        Forall2 Subtype Cs Ds -> 
        Forall2 P es Cs ->
        P (ExpMethodInvoc e0 m es) C)
  (f2 : forall (C : id) (Ds Cs : [ClassName]) (fs : [FieldDecl]) (es : [Exp]),
        fields C fs ->
        Ds = map fieldType fs ->
        Forall2 (ExpTyping Gamma) es Cs ->
        Forall2 Subtype Cs Ds -> 
        Forall2 P es Cs ->
        P (ExpNew C es) C)
  (f3 : forall (e0 : Exp) (D C : ClassName), Gamma |- e0 : D -> P e0 D -> D <: C -> P (ExpCast C e0) C)
  (f4 : forall (e0 : Exp) (C : id) (D : ClassName),
        Gamma |- e0 : D -> P e0 D -> C <: D -> C <> D -> P (ExpCast C e0) C)
  (f5 : forall (e0 : Exp) (D C : ClassName),
        Gamma |- e0 : D -> P e0 D -> ~ D <: C -> ~ C <: D -> stupid_warning -> P (ExpCast C e0) C) =>
fix F (e : Exp) (c : ClassName) (e0 : Gamma |- e : c) {struct e0} : P e c :=
  match e0 in (_ |- e1 : c0) return (P e1 c0) with
  | T_Var _ x C e1 => f x C e1
  | T_Field _ e1 C0 fs i Fi Ci fi e2 f6 e3 e4 e5 => f0 e1 C0 fs i Fi Ci fi e2 (F e1 C0 e2) f6 e3 e4 e5
  | T_Invk _ e1 C Cs C0 Ds m es e2 m0 f6 f7 => f1 e1 C Cs C0 Ds m es e2 (F e1 C0 e2) m0 f6 f7 
          ((fix list_Forall_ind (es' : [Exp]) (Cs' : [ClassName]) 
            (map : Forall2 (ExpTyping Gamma) es' Cs'): 
               Forall2 P es' Cs' :=
            match map with
            | Forall2_nil _ => Forall2_nil P
            | (@Forall2_cons _ _ _ ex cx ees ccs H1 H2) => Forall2_cons ex cx (F ex cx H1) (list_Forall_ind ees ccs H2)
          end) es Cs f6)
  | T_New _ C Ds Cs fs es f6 e1 f7 f8 => f2 C Ds Cs fs es f6 e1 f7 f8
          ((fix list_Forall_ind (es' : [Exp]) (Cs' : [ClassName]) 
            (map : Forall2 (ExpTyping Gamma) es' Cs'): 
               Forall2 P es' Cs' :=
            match map with
            | Forall2_nil _ => Forall2_nil P
            | (@Forall2_cons _ _ _ ex cx ees ccs H1 H2) => Forall2_cons ex cx (F ex cx H1) (list_Forall_ind ees ccs H2)
          end) es Cs f7)
  | T_UCast _ e1 D C e2 s => f3 e1 D C e2 (F e1 D e2) s
  | T_DCast _ e1 C D e2 s n => f4 e1 C D e2 (F e1 D e2) s n
  | T_SCast _ e1 D C e2 s s0 w => f5 e1 D C e2 (F e1 D e2) s s0 w
  end.
