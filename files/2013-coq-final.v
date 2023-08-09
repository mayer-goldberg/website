(* 2013-coq-final.v
 * Some axioms and theorems about real numbers
 * 
 * Programmer: Mayer Goldberg, 2013
 *)

Section Reals.

  Require Import Setoid.

  Axiom PNP: forall p : Prop, p \/ ~p.

  Variable R : Set.
  Variable zero : R.
  Variable one : R.
  Variable A : R -> R -> R.
  Variable M : R -> R -> R.

  Axiom x_add_comm: forall x y : R, A x y = A y x.

  Axiom x_add_assoc: forall x y z : R, A (A x y) z = A x (A y z).

  Axiom x_left_dist: forall x y z : R, M x (A y z) = A (M x y) (M x z).

  Axiom x_mult_comm: forall x y : R, M x y = M y x.

  Axiom x_mult_assoc: forall x y z : R, M (M x y) z = M x (M y z).

  Axiom x_zero: forall x : R, A x zero = x.

  Axiom x_one: forall x : R, M x one = x.

  Axiom x_neg: forall x : R, exists xneg : R, A x xneg = zero.

  Axiom x_inv: forall x : R, ~(x = zero) -> exists xinv : R, M x xinv = one.

  Definition inverse_of (x y : R) := M y x = one.

  Theorem T0: forall x xneg xneg' : R, 
                (A x xneg = zero /\
                 A x xneg' = zero) ->
                xneg = xneg'.
  Proof.
    intros x xneg xneg' H1.
    destruct H1 as [H1 H2].
    assert (H3: A xneg (A x xneg) = A xneg (A x xneg')).
    rewrite H1, H2; reflexivity.
    repeat rewrite <- x_add_assoc, 
    (x_add_comm xneg),
    H1,
    (x_add_comm zero),
    x_zero in H3.
    exact H3.
  Qed.

  Theorem T1: forall x y : R, 
                (x <> zero) -> (y <> zero) -> 
                exists xinv yinv : R, 
                  inverse_of xinv x /\
                  inverse_of yinv y /\
                  M (M x y) (M xinv yinv) = one.
  Proof.     
    intros x y H1 H2.
    apply x_inv in H1.
    apply x_inv in H2.
    destruct H1 as [xinv H1].
    destruct H2 as [yinv H2].
    exists xinv.
    exists yinv.
    split.
    exact H1.
    split.
    exact H2.
    rewrite (x_mult_comm x y).
    rewrite <- x_mult_assoc.
    rewrite (x_mult_assoc y x xinv).
    rewrite H1.
    rewrite x_one.
    rewrite H2.
    reflexivity.
  Qed.

  Theorem T2: forall x y z : R, (x <> zero) -> 
                           ((M x y) = (M x z)) ->
                           (y = z).
  Proof.     
    admit.
  Qed.

  Theorem T3: forall x y z : R, M (A x y) z = A (M x z) (M y z).
  Proof.
    admit.
  Qed.

  Theorem T4: forall x : R, A zero x = x.
  Proof.
    admit.
  Qed.

  Theorem T5: forall x : R, M one x = x.
  Proof.
    admit.
  Qed.

  Theorem T6: forall x y z : R, (A x y = A x z) -> (y = z).
  Proof.
    admit.
  Qed.

  Theorem T7: forall m n p q : R, 
                M (A m n) (A p q) = 
                A (A (M m p) (M n p)) (A (M m q) (M n q)).
  Proof.
    admit.
  Qed.

  Theorem T8a: forall m n p q : R, A m (A n (A p q)) = A (A m n) (A p q).
  Proof.
    admit.
  Qed.

  Theorem T8b: forall m n p q : R, A m (A n (A p q)) = A (A (A m n) p) q.
  Proof.
    admit.
  Qed.

  Theorem T9: forall m n p : R, A m (A n p) = A (A p m) n.
  Proof.
    admit.
  Qed.

  Theorem T10: forall m n p : R, M m (M n p) = M p (M m n).
  Proof.
    admit.
  Qed.

  Theorem T11: forall m n p q : R, M m (A n (A p q)) = A (A (M m n) (M m p)) (M m q).
  Proof.
    admit.
  Qed.

  Theorem T12: forall m n p q : R,
                 M (M m (A n p)) q = A (M (M m n) q) (M m (M p q)).
  Proof.
    admit.
  Qed.

  Theorem T13: forall x : R, (forall m : R, A m x = m) -> x = zero.
  Proof.
    admit.
  Qed.

  Theorem T14: forall x : R, (exists m : R, A m x = m) -> x = zero.
  Proof.
    admit.	
  Qed.

  Theorem T15: forall m : R, M m zero = zero.
  Proof.
    admit.
  Qed.

  Theorem T16: forall x : R, (forall m : R, M m x = m) -> x = one.
  Proof.
    admit.
  Qed.

  Theorem T17: forall x : R, (exists m : R, m <> zero /\ M m x = m) -> x = one.
  Proof.
    admit.
  Qed.

  Theorem T18: forall m n : R, 
               exists mneg nneg : R,
                 A m mneg = zero /\
                 A n nneg = zero /\
                 M mneg nneg = M m n.
  Proof.
    admit.
  Qed.

End Reals.
