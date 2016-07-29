Require Export List.
Require Export SfLib.
Require Export String.

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
  ref cdecl := 
    match cdecl with 
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

Inductive Exp : Set :=
  | ExpVar : Var -> Exp
  | ExpFieldAccess : Exp -> id -> Exp
  | ExpMethodInvoc : Exp -> id -> [Exp] -> Exp
  | ExpCast : ClassName -> Exp -> Exp
  | ExpNew : id -> [Exp] -> Exp.

Inductive MethodDecl :=
  | MDecl : ClassName -> id -> [FormalArg] -> Exp -> MethodDecl.

Instance MDeclRef : Referable MethodDecl :={
  ref mdecl := 
    match mdecl with 
   | MDecl _ id _ _ => id end
}.


Inductive ClassDecl:=
  | CDecl: id -> ClassName -> [FieldDecl] -> Constructor -> [MethodDecl] -> ClassDecl.

Inductive Program :=
  | CProgram : [ClassDecl] -> Exp -> Program.

Instance CDeclRef : Referable ClassDecl :={
  ref cdecl := 
    match cdecl with 
   | CDecl id _ _ _ _ => id end
}.

Parameter CT: [ClassDecl].
(*We will assume a global CT to make our definitions easier
 *To instance the CT use Hypothesis x: CT = ... *)

Reserved Notation "C '<:' D " (at level 40).
Inductive Subtype : id -> ClassName -> Prop :=
  | S_Refl: forall C: ClassName, C <: C
  | S_Trans: forall (C D E: ClassName), 
    C <: D -> 
    D <: E -> 
    C <: E
  | S_Decl: forall C D fs K mds,
    find C CT = Some (CDecl C D fs K mds) ->
    C <: D
where "C '<:' D" := (Subtype C D).
Hint Constructors Subtype.

Tactic Notation "subtype_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "S_Refl" | Case_aux c "S_Trans" 
  | Case_aux c "S_Decl"].

Inductive fields : id -> [FieldDecl] -> Prop :=
 | fields_obj : fields Object nil
 | fields_other : forall C D fs K mds fs', 
     find C CT = Some (CDecl C D fs K mds) ->
     fields D fs' ->
     fields C (fs'++fs).

Reserved Notation "'mtype(' m ',' D ')' '=' c '~>' c0" (at level 40).
Inductive m_type (m: id) (C: ClassName) (Bs: [ClassName]) (B: ClassName) : Prop:=
  | mty_ok : forall D Fs K Ms fargs e,
              find C CT = Some (CDecl C D Fs K Ms)->
              In (MDecl B m fargs e) Ms ->
              map fargType fargs = Bs ->
              mtype(m, C) = Bs ~> B
  | mty_no_override: forall D Fs K Ms fargs e,
              find C CT = Some (CDecl C D Fs K Ms)->
              ~In (MDecl B m fargs e) Ms->
              map fargType fargs = Bs ->
              mtype(m, D) = Bs ~> B ->
              mtype(m, C) = Bs ~> B
  where "'mtype(' m ',' D ')' '=' c '~>' c0"
        := (m_type m D c c0).


Inductive m_body (m: id) (C: ClassName) (xs: [ClassName]) (e: Exp) : Prop:=
  | mbdy_ok : forall D Fs K Ms fargs B,
              find C CT = Some (CDecl C D Fs K Ms)->
              In (MDecl B m fargs e) Ms ->
              map ref fargs = xs ->
              m_body m C xs e
  | mbdy_no_override: forall D Fs K Ms fargs B,
              find C CT = Some (CDecl C D Fs K Ms)->
              ~In (MDecl B m fargs e) Ms->
              map ref fargs = xs ->
              m_body m D xs e ->
              m_body m C xs e.
Notation "'mbody(' m ',' D ')' '=' xs 'o' e" := (m_body m D xs e) (at level 40).

Hint Constructors m_type m_body fields.
Tactic Notation "mbdy_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "mbdy_ok" | Case_aux c "mbdy_no_override"].


Fixpoint subst (e: Exp) (v: Var) (v': Exp) : Exp:=
  match e with
  | ExpVar var => if eq_id_dec var v then v' else ExpVar var
  | ExpFieldAccess exp i => ExpFieldAccess (subst exp v v') i
  | ExpMethodInvoc exp i exps => 
      ExpMethodInvoc (subst exp v v') i (map (fun x => subst x v v') exps)
  | ExpCast cname exp => ExpCast cname (subst exp v v')
  | ExpNew cname exps => ExpNew cname (map (fun x => subst x v v') exps)
  end.
Notation " '[' v ':=' v' ']' e " := (subst e v v') (at level 40).

Reserved Notation "Gamma '|-' x ':' C" (at level 40, x at next level).
Print Forall'.


Inductive Warning (s: string) : Prop :=
  | w_str : Warning s.
Notation stupid_warning := (Warning "stupid warning").

Inductive ExpTyping (Gamma: partial_map ClassName) : Exp -> ClassName -> Prop:=
  | T_Var : forall x C, Gamma x = Some C -> 
                Gamma |- ExpVar x : C
  | T_Field: forall e0 C0 fs i Fi Ci fi,
                Gamma |- e0 : C0 ->
                fields C0 fs ->
                Some Fi = nth_error fs i ->
                Ci = fieldType Fi ->
                fi = ref Fi ->
                Gamma |- ExpFieldAccess e0 fi : Ci
  | T_Invk : forall e0 C Cs C0 Ds m es,
                Gamma |- e0 : C0 ->
                mtype(m, C0) = Ds ~> C ->
                Forall' (fun e' C' => Gamma |- e' : C') es Cs ->
                Forall' (fun C' D' => C' <: D') Cs Ds ->
                Gamma |- ExpMethodInvoc e0 m es : C
  | T_New : forall C Ds Cs fs es,
                fields C fs ->
                Ds = map fieldType fs ->
                Forall' (fun e' C' => Gamma |- e' : C') es Cs ->
                Forall' (fun C' D' => C' <: D') Cs Ds ->
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
                D <: C ->
                C <: D ->
                stupid_warning ->
                Gamma |- ExpCast C e0 : C
  where " Gamma '|-' e ':' C " := (ExpTyping Gamma e C).
