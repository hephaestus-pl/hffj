Require Export List.
Require Export SfLib.

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

Definition fargType (f: FormalArg):ClassName := 
  match f with FArg t _ => t end.

Definition fargName (f: FormalArg): id := 
  match f with FArg _ i => i end.

Inductive Constructor :=
  | KDecl : id -> [FormalArg] -> [Argument] -> [Assignment] -> Constructor.

Inductive FieldDecl :=
  | FDecl : ClassName -> id -> FieldDecl.

Inductive Exp : Set :=
  | ExpVar : Var -> Exp
  | ExpFieldAccess : Exp -> id -> Exp
  | ExpMethodInvoc : Exp -> id -> [Exp] -> Exp
  | ExpCast : ClassName -> Exp -> Exp
  | ExpNew : id -> [Exp] -> Exp.

Inductive MethodDecl :=
  | MDecl : ClassName -> id -> [FormalArg] -> Exp -> MethodDecl.

Inductive ClassDecl:=
  | CDecl: id -> ClassName -> [FieldDecl] -> Constructor -> @partial_map MethodDecl -> ClassDecl.

Inductive Program :=
  | CProgram : [ClassDecl] -> Exp -> Program.

Instance CDeclRef : Referable ClassDecl :={
  ref cdecl := 
    match cdecl with 
   | CDecl id _ _ _ _ => id end
}.

Parameter CT: @partial_map ClassDecl.
(*We will assume a global CT to make our definitions easier
 *To instance the CT use Hypothesis x: CT = ... *)

(*Auxiliaries*)
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
Hint Constructors fields.

Inductive ty : Type :=
  | ty_var : ClassName -> ty
  | ty_fun : [ClassName] -> ClassName -> ty.

Notation "'#' t" :=  (ty_var t) (at level 40).
Notation "t '~>' t'" :=  (ty_fun t t') (at level 40).
Hint Constructors ty.

(*Reserved Notation "'mtype(' m ',' D ')' '=' t" (at level 40).*)
Inductive m_type: id -> ClassName -> ty -> Prop :=
  | mt_self : forall C D B Bs Fs K m Ms fargs e,
              find C CT = Some (CDecl C D Fs K Ms)->
              find m Ms = Some (MDecl B m fargs e) ->
              map fargType fargs = Bs ->
              m_type m C (Bs ~> B)
  | mt_super : forall C D Fs K m Ms t,
              find C CT = Some (CDecl C D Fs K Ms)->
              find m Ms = None ->
              m_type m D t ->
              m_type m C t.
(*
  where "'mtype(' m ',' D ')' '=' t"
        := (m_type m D c c0 t).
*)

Hint Constructors m_type.
Tactic Notation "mty_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "mt_self" | Case_aux c "mt_super"].

Inductive m_body (m: id) (C: ClassName) (xs: [id]) (e: Exp) : Prop:=
  | mb_self : forall D B Fs K Ms fargs,
              find C CT = Some (CDecl C D Fs K Ms) ->
              In m (keys Ms) ->
              find m Ms = Some (MDecl B m fargs e) ->
              map fargName fargs = xs ->
              m_body m C xs e
  | mb_super: forall D Fs K Ms fargs,
              find C CT = Some (CDecl C D Fs K Ms) ->
              ~In m (keys Ms) ->
              map fargName fargs = xs ->
              m_body m D xs e ->
              m_body m C xs e.

Hint Constructors m_body.
Tactic Notation "mbody_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "mb_self" | Case_aux c "mb_super"].

Definition Bind := @partial_map Exp.

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




