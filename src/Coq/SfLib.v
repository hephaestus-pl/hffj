(** * SfLib: Software Foundations Library *)

(* $Date: 2013-01-16 22:29:57 -0500 (Wed, 16 Jan 2013) $ *)

(** Here we collect together several useful definitions and theorems
    from Basics.v, List.v, Poly.v, Ind.v, and Logic.v that are not
    already in the Coq standard library.  From now on we can [Import]
    or [Export] this file, instead of cluttering our environment with
    all the examples and false starts in those files. *)

(** * From the Coq Standard Library *)

Require Omega.   (* needed for using the [omega] tactic *)
Require Export Bool.
Require Export List.
Require Export Arith.
Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)

(** * From Basics.v *)

Definition admit {T: Type} : T.  Admitted.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Theorem andb_true_elim1 : forall b c,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity.  Qed.

Theorem andb_true_elim2 : forall b c,
  andb b c = true -> c = true.
Proof.
(* An exercise in Basics.v *)
Admitted.

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
(* An exercise in Lists.v *)
Admitted.

(* From Poly.v *)

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) 
                     (at level 60, right associativity).

(** * From Props.v *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(** * From Logic.v *)

Theorem andb_true : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
    destruct c.
      apply conj. reflexivity. reflexivity.
      inversion H.
    inversion H.  Qed.

Theorem not_eq_beq_false : forall n n' : nat,
     n <> n' ->
     beq_nat n n' = false.
Proof. 
(* An exercise in Logic.v *)
Admitted.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.  Qed.

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof. 
(* An exercise in Logic.v *)
Admitted.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
(* An exercise in Logic.v *)
Admitted.

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
(* An exercise in Logic.v *)
Admitted.

Inductive appears_in (n : nat) : list nat -> Prop :=
| ai_here : forall l, appears_in n (n::l)
| ai_later : forall m l, appears_in n l -> appears_in n (m::l).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive total_relation : nat -> nat -> Prop :=
  tot : forall n m : nat, total_relation n m.

Inductive empty_relation : nat -> nat -> Prop := .

(** * From Later Files *)

Definition relation (X:Type) := X -> X -> Prop.

Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2. 

Inductive multi (X:Type) (R: relation X) 
                            : X -> X -> Prop :=
  | multi_refl  : forall (x : X),
                 multi X R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi X R y z ->
                    multi X R x z.
Implicit Arguments multi [[X]]. 

Tactic Notation "multi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "multi_refl" | Case_aux c "multi_step" ].

Theorem multi_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> multi R x y.
Proof.
  intros X R x y r.
  apply multi_step with y. apply r. apply multi_refl.   Qed.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  (* FILL IN HERE *) Admitted.

(* Identifiers and polymorphic partial maps. *)
Inductive id : Type := 
  Id : nat -> id.

Definition beq_id id1 id2 :=
  match (id1, id2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall i,
  true = beq_id i i.
Proof.
  intros. destruct i.
  apply beq_nat_refl.  Qed.

Theorem beq_id_eq : forall i1 i2,
  true = beq_id i1 i2 -> i1 = i2.
Proof.
  intros i1 i2 H.
  destruct i1. destruct i2.
  apply beq_nat_eq in H. subst.
  reflexivity.  Qed.

Theorem beq_id_false_not_eq : forall i1 i2,
  beq_id i1 i2 = false -> i1 <> i2.
Proof.
  intros i1 i2 H.
  destruct i1. destruct i2.
  apply beq_nat_false in H.
  intros C. apply H. inversion C. reflexivity.  Qed.

Theorem not_eq_beq_id_false : forall i1 i2,
  i1 <> i2 -> beq_id i1 i2 = false.
Proof.
  intros i1 i2 H.
  destruct i1. destruct i2.
  assert (n <> n0).
    intros C. subst. apply H. reflexivity.
  apply not_eq_beq_false. assumption.  Qed.

Theorem beq_id_sym: forall i1 i2,
  beq_id i1 i2 = beq_id i2 i1.
Proof.
  intros i1 i2. destruct i1. destruct i2. apply beq_nat_sym. Qed.

Theorem eq_id_dec: forall (i1 i2: id),
  {i1 = i2} + {i1 <> i2}.
Proof.
  intros.
  destruct i1, i2.
  destruct eq_nat_dec with n n0.
  left; auto.
  right; intro.
  apply n1; inversion H; auto.
Qed.


Inductive partial_map {A : Set} := 
  | empty : partial_map
  | record : id -> A -> partial_map -> partial_map .

Definition update {A: Set} (d : partial_map)
                  (key : id) (value : A) : partial_map :=
           record key value d.

Fixpoint find {A: Set} (key: id) (d: partial_map) : option A :=
  match d with
  | empty => None
  | record k v d' => if beq_id key k
                     then Some v
                     else find key d'
  end.

Fixpoint keys {A: Set} (d: @partial_map A) : list id :=
  match d with
  | empty => []
  | record k _ d' => k :: keys d'
  end.

Inductive findi {A: Set} : id -> (@partial_map A) -> option A -> Prop:=
  | not_in : forall key, findi key empty None
  | in_head : forall key v d, findi key (record key v d) (Some v)
  | not_in_head : forall k1 k2 v d x, 
    k1 <> k2 -> findi k1 (record k2 v d) x -> findi k1 d x.

Definition binds {A: Set} x (v: A) d: Prop := find x d = Some v.
Definition no_binds {A: Set} x d: Prop := find x d = @None A.

Definition is_in {A: Set} id d := exists x: A, find id d = Some x.
Notation "id '\in' d" := (is_in id d) (at level 20).

Lemma update_eq : forall (A: Set) (d: partial_map) (k: id) (v: A),
  find k (update d k v) = Some v.
Proof.
  intros. unfold update. simpl. rewrite <- beq_id_refl. auto.
Qed.

Lemma update_neq : forall (A: Set) (d: partial_map) (m n: id) (o: A),
  beq_id m n = false -> find m (update d n o) = find m d.
Proof.
  intros. unfold update, find. rewrite H; auto.
Qed.

Lemma update_shadow : forall (A: Set) (d: partial_map) (k1: id) (v1 v2: A),
  find k1 (record k1 v1 (record k1 v2 d)) = Some v1.
Proof with auto.
  intros.
  simpl.
  rewrite <- beq_id_refl...
Qed.

Lemma find_deterministic: forall (A: Set) d (k1: id) (x1 x2: option A),
  find k1 d = x1 ->
  find k1 d = x2 ->
  x1 = x2.
Proof with eauto.
  intros.
  destruct x1, x2; 
  destruct (@find A) in *; auto with rewrite.
  rewrite <- H; auto.
  inversion H.
  inversion H0.
  inversion H.
Qed.

Lemma find_dec : forall (A: Set) k1 d (v:option A),
  {find k1 d = Some v} + {find k1 d = None}.
Proof.
Admitted.

Class Referable (a: Set) :={
  ref : a -> id;

  finder: id -> list a -> option a := 
  let fix f (key: id) (l: list a) :=
    match l with
      | [] => None
      | (x :: xs) => if eq_id_dec key (ref x) 
                      then Some x
                      else f key xs
    end in f
}.


(** * Some useful tactics *)

Tactic Notation "solve_by_inversion_step" tactic(t) :=  
match goal with  
| H : _ |- _ => solve [ inversion H; subst; t ] 
end
|| fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
solve by inversion 1.
