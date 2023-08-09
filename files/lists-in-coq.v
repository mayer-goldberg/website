(* lists-in-coq.v
 * Working with lists in Coq
 * 
 * Programmer: Mayer Goldberg, 2013
 *)

Require Import Setoid.
Require Import Arith.

Inductive List {T} : Type :=
| nil : @List T
| cons : T -> @List T -> @List T.

Eval cbv in (cons 2 (cons 3 (cons 4 nil))).

(* 
     = cons 2 (cons 3 (cons 4 nil))
     : List
 *)

Fixpoint length {T : Type} (x : @List T) :=
  match x with
    | nil => 0
    | cons _ s => 1 + length s
  end.
Eval cbv in (length (cons 4 (cons 9 (cons 6 (cons 3 (cons 5 (cons 1 nil))))))).

(* 
     = 6
     : nat
 *)

Lemma L_length_of_cons {T}: 
  forall (x : T) (s : @List T), length (cons x s) = 1 + length s.
Proof.
  intros x s.
  unfold length; fold (@length T); reflexivity.
Qed.

Definition maybe_car {T : Type} (e : @List T) :=
  match e with
    | nil => None
    | cons x _ => Some x
  end.

Definition maybe_cdr {T : Type} (e : @List T) :=
  match e with
    | nil => None
    | cons _ s => Some s
  end.

Definition L_list_consistency_1_statement {T : Type} :=
  forall (x : T) (s : @List T), 
    maybe_car (cons x s) = Some x.

Definition  L_list_consistency_2_statement {T : Type} :=
  forall (x : T) (s : @List T),
    maybe_cdr (cons x s) = Some s.

Lemma L_list_consistency_1_proof {T : Type}: @L_list_consistency_1_statement T.
Proof.
  intros x s.
  unfold maybe_car; reflexivity.
Qed.

Lemma L_list_consistency_2_proof {T : Type}: @L_list_consistency_2_statement T.
Proof.
  intros x s.
  unfold maybe_cdr; reflexivity.
Qed.

Theorem T_list_consistency {T : Type}:
  @L_list_consistency_1_statement T /\
  @L_list_consistency_2_statement T.
Proof.
  split.
  apply L_list_consistency_1_proof.
  apply L_list_consistency_2_proof.
Qed.

Fixpoint append {T : Type} (s r : @List T) :=
  match s with
    | nil => r
    | cons x w => cons x (append w r)
  end.

Lemma L_append_nil {T : Type}:
  forall (s : @List T), append nil s = s.
Proof.
  intro s.
  unfold append; reflexivity.
Qed.

Lemma L_append_cons {T : Type}: 
  forall (x : T) (s w : @List T), 
    append (cons x s) w = cons x (append s w).
Proof.
  intros x s w.
  unfold append; fold (@append T); reflexivity.
Qed.

Lemma L_append_to_nil {T : Type}:
  forall (s : @List T), append s nil = s.
Proof.
  induction s.
  unfold append; reflexivity.
  rewrite L_append_cons, IHs; reflexivity.
Qed.

Lemma L_length_cons {T : Type}:
  forall (x : T) (s : @List T),
    length (cons x s) = 1 + length s.
Proof.
  intros x s.
  unfold length; fold (@length T); reflexivity.
Qed.

Lemma L_append_length {T : Type}:
  forall (s r : @List T),
    length (append s r) = length s + length r.
Proof.
  intros s' r.
  generalize s' as s.
  induction s.

  rewrite L_append_nil.
  unfold length at 2.
  rewrite plus_0_l; reflexivity.

  rewrite L_append_cons.
  repeat rewrite L_length_cons.
  rewrite IHs.
  rewrite plus_assoc.
  reflexivity.
Qed.

Theorem T_append_assoc {T : Type}:
  forall (a b c : @List T), append (append a b) c = append a (append b c).
Proof.
  induction a, b.
  intro c.
  unfold append; reflexivity.

  repeat rewrite L_append_nil; reflexivity.

  intro c.
  rewrite L_append_nil, L_append_to_nil; reflexivity.

  intro c.
  repeat rewrite L_append_cons.
  rewrite IHa.
  rewrite L_append_cons.
  reflexivity.
Qed.

Fixpoint reverse {T : Type} (s : @List T) :=
  match s with
    | nil => nil
    | cons a r => append (reverse r) (cons a nil)
  end.

Fixpoint reverseI {T : Type} (s r : @List T) :=
  match s with
    | nil => r
    | cons a w => reverseI w (cons a r)
  end.

Eval cbv in (reverse (cons 1 (cons 2 (cons 3 (cons 4 nil))))).

Eval cbv in (reverseI (cons 1 (cons 2 (cons 3 (cons 4 nil)))) nil).

(* 
     = cons 4 (cons 3 (cons 2 (cons 1 nil)))
     : List
 *)

Lemma L_unfold_reverseI {T : Type}:
  forall (x : T) (s w : @List T), reverseI (cons x s) w = reverseI s (cons x w).
Proof.
  intros x s w.
  unfold reverseI; reflexivity.
Qed.

Lemma L_reverse_1 {T : Type}:
  forall (x : T) (s : @List T), reverse (cons x s) = append (reverse s) (cons x nil).
Proof.
  intro x.
  induction s.
  unfold reverse; reflexivity.
  unfold reverse; unfold append; reflexivity.
Qed.

Lemma L_reverseII {T : Type}:
  forall (s w : @List T), reverseI s w = append (reverse s) w.
Proof.
  induction s.
  unfold reverse; unfold reverseI; reflexivity.

  intro w.
  rewrite L_unfold_reverseI, IHs, L_reverse_1, T_append_assoc, L_append_cons, L_append_nil; reflexivity.
Qed.

Lemma L_reverse_2 {T : Type}:
  forall (x : T) (s : @List T), reverse (append s (cons x nil)) = cons x (reverse s).
Proof.
  intro x.
  induction s.
  rewrite L_append_nil.
  unfold reverse.
  rewrite L_append_nil.
  reflexivity.

  rewrite L_append_cons, L_reverse_1, IHs, L_append_cons, L_reverse_1; reflexivity.
Qed.

Theorem T_reverse_reverse {T : Type}:
  forall (s : @List T), reverse (reverse s) = s.
Proof.
  induction s.
  unfold reverse; reflexivity.

  rewrite L_reverse_1, L_reverse_2, IHs; reflexivity.
Qed.

Theorem T_reverse_append {T : Type}:
  forall (s w : @List T), 
    reverse (append s w) = append (reverse w) (reverse s).
Proof.
  induction s, w.
  unfold reverse; unfold append; reflexivity.

  rewrite L_append_nil; unfold reverse at 3; rewrite L_append_to_nil; reflexivity.

  rewrite L_append_to_nil; unfold reverse at 2; rewrite L_append_nil; reflexivity.

  rewrite L_append_cons.
  repeat rewrite L_reverse_1.
  rewrite IHs.
  rewrite L_reverse_1.
  rewrite T_append_assoc.
  reflexivity.
Qed.

Theorem T_reverse {T : Type}:
  forall (s : @List T), reverseI s nil = reverse s.
Proof.
  induction s.
  unfold reverseI; unfold reverse; reflexivity.
  rewrite L_unfold_reverseI.
  rewrite L_reverseII.
  rewrite <- L_reverse_1.
  reflexivity.
Qed.

