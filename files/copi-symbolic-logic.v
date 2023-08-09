(* copy-symbolic-logic.v
 * Solutions to exercises in Copi's famous book on 
 * logic.
 * 
 * Programmer: Mayer Goldgerg, 2012
 *)

(** Dear Reader: 

  I created this file while studying Coq myself. You can think of this file as a training log for the benefit of those who are also studying Coq and wish to have a collection of worked-out exercises on which to practice and hone their skills. Since I plan on using Coq in some of my courses, the first audience in mind are my own students, but of course, I gladly make this work available for all, in the hope that readers will find it useful. 

  These are not the best or shortest proofs possible. The speed and ease with which I generated these proofs changed drammatically during the creation of the file, and this is what I hope for for my readers. I'm sure that if I go back and re-do the proofs, that many will be significantly shorter and simpler. Despite of this, I believe the file to be great training material for proving theorems with Coq, and I hope you will try out the exercises.
  
  To use this file effectively, open it in either the CoqIDE or the ProofGeneral, and evaluate everything up to the first theorem. Then insert blank lines before my proof, and try to prove it yourself. If you succeed, congratulations! -- delete or comment out my own proof. If you fail, you can examine my own proof, one statement at a time. The CoqIDE and ProofGeneral allow you to scroll both up and down in a proof, which is a great way to see where you are in the proof and what is still missing.

  The goal of this work is eventually to include all those exercises in Irving Copi's book on symbolic logic that involve proofs. Other exercises --- encoding English sentences in sentential logic and first-order predicate logic, finding errors in theorems, and other wonderful exercises, cannot be encoded straightforwardly in Coq, and so I skipped over them.

  This is as of yet work-in-progress. As I am typing in the exercises, you will see empty ``templates'' for exercises, that I still need to type in. Just skip those, and move on to the next theorem the statement of which appears in the file.

 *)

Require Import Setoid.
Require Import ClassicalFacts.

Section Copi.
  
  (** I'm going to begin with some preliminaries that shall be used throughout the solutions. Many of these include classical theorems that are unavailable, in whole or in part, in constructive logic. *)

  Axiom PNP: excluded_middle.
  
  (* it's often a lot of work to get by without this *)
  Axiom propositional_extensionality: prop_extensionality.
  
  Theorem referential_transparency:
    forall (f : Prop -> Prop) (x y : Prop),
      (x <-> y) -> ((f x) <-> (f y)).
  Proof.
    intros f x y H1.
    rewrite <- (propositional_extensionality x y).
    split; intro; assumption.
    exact H1.
  Qed.
  
  Lemma hypothetical_syllogism:
    forall (p q : Prop), 
      (p -> q) <-> (~q -> ~p).
  Proof.
    intros p q.
    split.
    intros H1 H2.
    
    destruct (PNP p) as [H3 | H3'].
    apply H1 in H3.
    unfold not in H2; contradict H3.
    exact H2.
    exact H3'.
    intros H1 H2.
    destruct (PNP q) as [H3 | H3'].
    exact H3.
    apply H1 in H3'.
    unfold not in H3'; apply H3' in H2; contradict H2.
  Qed.
  
  Lemma material_conditional:
    forall x y : Prop, (x -> y) <-> (~x \/ y).
  Proof.
    intros x y.
    split.
    intro H1.
    destruct (PNP x) as [H2 | H3].
    apply H1 in H2.
    right.
    exact H2.
    left.
    exact H3.
    intros H1 H2.
    destruct H1 as [H1 | H1'].
    unfold not in H1.
    apply H1 in H2.
    contradict H2.
    exact H1'.
  Qed.
  
  Lemma de_morgan_1:
    forall p q : Prop,
      ~ (p \/ q) <-> (~p /\ ~q).
  Proof.
    intros p q.
    split.
    intro H1.
    unfold not in H1.
    split.
    unfold not.
    intro H2.
    destruct H1.
    left.
    exact H2.
    unfold not.
    intro H2.
    destruct H1.
    right.
    exact H2.
    intro H1.
    destruct H1 as [H11 H12].
    unfold not.
    intro H2.
    unfold not in H11.
    unfold not in H12.
    destruct H2 as [H21 | H22].
    apply (H11 H21).
    apply (H12 H22).
  Qed.
  
  Lemma de_morgan_2:
    forall p q : Prop,
      ~ (p /\ q) <-> (~p \/ ~q).
  Proof.
    intros p q.
    split.
    intro H1.
    unfold not in H1.
    destruct (PNP p) as [H2 | H3].
    destruct (PNP q) as [H4 | H5].
    assert (H6: p /\ q).
    split.
    exact H2.
    exact H4.
    apply H1 in H6.
    contradict H6.
    right.
    exact H5.
    left.
    exact H3.
    intro H1.
    unfold not in H1.
    unfold not.
    intro H2.
    destruct H2 as [H2 H2'].
    destruct H1 as [H1 | H1'].
    apply H1 in H2; contradict H2.
    apply H1' in H2'; contradict H2'.
  Qed.
  
  Lemma AandBthenC:
    forall a b c : Prop,
      ((a /\ b) -> c) <-> (a -> b -> c).
  Proof.
    intros a b c.
    split.
    intros H1 H2 H3.
    assert (H4: a /\ b).
    split.
    exact H2.
    exact H3.
    apply H1 in H4; exact H4.
    
    intros H1 H2.
    destruct H2 as [H2 H2'].
    exact (H1 H2 H2').
  Qed.
  
  Axiom prop_subst:
  forall (f : Prop -> Prop) (P Q : Prop), 
    (P <-> Q) -> ((f P) <-> (f Q)).
  
  Theorem not_exists {T : Type}:
    forall (P : T -> Prop), ~ (exists x, P x) <-> (forall x, ~ P x).
  Proof.
    intros P.
    split.
    intros H1.
    unfold not in H1.
    intro x.
    unfold not.
    intro H2.
    apply H1.
    exists x.
    exact H2.
    intro H1.
    unfold not in H1.
    unfold not.
    intro H2.
    destruct H2 as [x H2].
    apply H1 in H2.
    exact H2.
  Qed.
  
  Theorem not_forall {T : Type}:
    forall (P : T -> Prop), ~ (forall x, P x) <-> (exists x, ~ P x).
  Proof.
    intro P.
    split.
    intro H1.
    unfold not in H1.
    unfold not.
    destruct (PNP (exists x : T, P x -> False)) as [H21 | H22].
    exact H21.
    rewrite -> not_exists in H22.
    destruct H1.
    intro x.
    specialize (H22 x).
    destruct (PNP (P x)) as [H31 | H32].
    exact H31.
    apply H22 in H32.
    contradict H32.
    intro H1.
    unfold not.
    intro H2.
    destruct H1 as [x H1].
    apply H1.
    apply H2.
  Qed.
  
  (** Proofs to theorems in the book start here. *)
  
  Theorem page36_III_1: 
    forall (A B C D : Prop), 
      (A -> B) ->
      (C -> D) ->
      ((~B \/ ~D) /\ (~A \/ ~B)) ->
      (~A \/ ~C).
  Proof.
    intros A B C D H1 H2 H3.
    destruct H3 as [H3 H4].
    elim H4; clear H4.
    intros J1.
    elim H3; clear H3.
    intro J2.
    left; exact J1.
    intro J2.
    left; exact J1.
    intro J1.
    elim H3; clear H3.
    intro J2; clear J2.

    unfold not in J1.
    left; unfold not; intro J2.
    exact (J1 (H1 J2)).
    intro J2.
    unfold not in J1.
    unfold not in J2.
    left.
    unfold not.
    intro J3.
    exact (J1 (H1 J3)).
  Qed.
  
  Theorem Page36_III_2: 
    forall e f g h : Prop,
      (e -> (f /\ ~ g)) ->
      ((f \/ g) -> h) -> 
      e -> h.
  Proof.
    intros e f g h H1 H2 H3.
    apply H1 in H3.
    destruct H3 as [H3 H4].
    apply H2.
    left; exact H3.
  Qed.
  
  Theorem Page36_III_3: 
    forall j k l : Prop,
      (j -> k) ->
      (j \/ k \/ ~l) ->
      ~k ->
      ~l /\ ~k.
  Proof.
    intros j k l H1 H2 H3.
    split.
    destruct H2 as [H4 | H5].
    apply H1 in H4.
    unfold not in H3.
    apply H3 in H4.
    contradict H4.
    destruct H5 as [H2 | H4].
    unfold not in H3.
    apply H3 in H2.
    contradict H2.
    exact H4.
    exact H3.
  Qed.
  
  Theorem Page36_III_4: 
    forall m n o p q : Prop,
      (m -> n) ->
      (n -> o) -> 
      ((m -> o) -> (n -> p)) ->
      ((m -> p) -> q) -> 
      q.
  Proof.
    intros m n o p q H1 H2 H3 H4.
    apply H4.
    intro H5.
    assert (H6: m -> o).
    intro H6; clear H6.
    apply H1 in H5.
    apply H2 in H5.
    exact H5.
    apply H3 in H6.
    exact H6.
    apply H1.
    exact H5.
  Qed.
  
  Theorem Page36_III_5: 
    forall r s t u v w x y : Prop,
      ((r -> ~s) /\ (t -> ~u)) ->
      ((v -> ~w) /\ (x -> ~y)) ->
      ((t -> w) /\ (u -> s)) ->
      (v \/ r) ->
      (~t \/ ~u).
  Proof.
    intros r s t u v w x y H1 H2 H3 H4.
    destruct H1 as [H1 H1'].
    destruct H2 as [H2 H2'].
    destruct H3 as [H3 H3'].
    destruct H4 as [H4 | H4'].
    apply H2 in H4.
    left.
    unfold not.
    intro H5.
    unfold not in H4.
    apply H3 in H5.
    apply H4 in H5.
    exact H5.
    right.
    unfold not.
    intro H5.
    apply H1 in H4'.
    apply H3' in H5.
    unfold not in H4'.
    apply H4' in H5.
    exact H5.
  Qed.
  
  Theorem Page36_III_6: 
    forall a b c d e f g : Prop,
      (a -> (b /\ c)) ->
      (~a -> ((d -> e) /\ (f -> g))) ->
      ((b /\ c) \/ ((~a -> d) /\ (~a -> f))) ->
      (~ (b /\ c) /\ ~ (g /\ d)) ->
      (e \/ g).
  Proof.
    intros a b c d e f g H1 H2 H3 H4.
    destruct H4 as [H4 H4'].
    destruct H3 as [H3 | H3'].
    destruct H3 as [H3 H3'].
    unfold not in H4.
    assert(H5: b /\ c).
    split.
    exact H3.
    exact H3'.
    apply H4 in H5.
    contradict H5.
    destruct H3' as [H3 H3'].
    unfold not in H2.
    unfold not in H3.
    unfold not in H3'.
    unfold not in H4.
    unfold not in H4'.
    assert (H5: a -> False).
    intro H5.
    apply H1 in H5.
    apply H4 in H5.
    exact H5.
    specialize (H2 H5).
    specialize (H3 H5).
    specialize (H3' H5).
    destruct H2 as [H2 H2'].
    left.
    apply H2.
    exact H3.
  Qed.
  
  Theorem Page37_III_7: 
    forall h i j k l m n o,
      ((~ h \/ i) -> (j -> k)) ->
      ((~l /\ ~m) -> (k -> n)) ->
      ((h -> l) /\ (l -> h)) ->
      ((~l /\ ~m) /\ ~o) ->
      (j -> n).
  Proof.
    intros h i j k l m n o H1 H2 H3 H4.
    destruct H3 as [H3 H3'].
    destruct H4 as [H4 H4'].
    clear H4'.
    destruct H4 as [H4 H4'].
    assert(H5: ~l /\ ~m).
    split.
    exact H4.
    exact H4'.
    intro H6.
    apply H2.
    split.
    exact H4.
    exact H4'.
    apply H1.
    left.
    unfold not.
    intro H7.
    apply H3 in H7.
    unfold not in H4.
    apply H4 in H7.
    exact H7.
    exact H6.
  Qed.
  
  Theorem Page37_III_8: 
    forall v w x y z a : Prop, 
      (v -> w) ->
      (x -> y) ->
      (z -> w) ->
      (x -> a) ->
      (w -> x) ->
      (((v -> y) /\ (z -> a)) -> (v \/ z)) ->
      (y \/ a).
  intros v w x y z a H1 H2 H3 H4 H5 H6.
  assert(H7: v -> y).
  intro H8; apply H2; apply H5; apply H1; exact H8.
  assert (H8: z -> a).
  intro H8.
  apply H4; apply H5; apply H3; exact H8.
  assert(H9: (v -> y) /\ (z -> a)).
  split. exact H7. exact H8.
  apply H6 in H9.
  destruct H9 as [H9 | H9'].
  apply H7 in H9.
  left.
  exact H9.
  apply H8 in H9'.
  right.
  exact H9'.
  Qed.
  
  Theorem Page37_III_9: 
    forall v w x y z a : Prop,
      (v -> w) ->
      (x -> y) ->
      (z -> w) -> 
      (x -> a) ->
      (w -> x) ->
      (((v -> y) /\ (z -> a)) -> (v \/ z)) ->
      (y \/ a).
  Proof.
    intros v w x y z a H1 H2 H3 H4 H5 H6.
    assert (H7: v -> y).
    intro H8.
    apply H1 in H8.
    apply H5 in H8.
    apply H2 in H8.
    exact H8.
    assert (H8: z -> a).
    intro H8.
    apply H3 in H8.
    apply H5 in H8.
    apply H4 in H8.
    exact H8.
    assert (H9: (v -> y) /\ (z -> a)).
    split.
    exact H7.
    exact H8.
    apply H6 in H9.
    assert (H10: w).
    destruct H9 as [H9 | H9'].
    apply H1 in H9.
    exact H9.
    apply H3 in H9'.
    exact H9'.
    specialize (H5 H10).
    specialize (H2 H5).
    left.
    exact H2.
  Qed.
  
  Theorem Page_37_III_10:
    forall b c d e f g h,
      ((b \/ c) -> (d \/ e)) ->
      ((d \/ e \/ f) -> (g \/ h)) ->
      ((g \/ h) -> ~d) ->
      (e -> ~g) ->
      b ->
      h.
  Proof.
    intros b c d e f g h H1 H2 H3 H4 H5.
    assert (H6: b \/ c).
    left.
    exact H5.
    apply H1 in H6.
    assert(H7: d \/ e \/ f).
    rewrite <- or_assoc.
    left.
    exact H6.
    apply H2 in H7.
    destruct H7 as [H7 | H7'].
    assert (H8: g \/ h).
    left; exact H7.              
    apply H3 in H8.
    destruct H6 as [H6 | H6'].
    unfold not in H8.                  
    apply H8 in H6.
    contradict H6.
    apply H4 in H6'.
    unfold not in H6'.
    apply H6' in H7.
    contradict H7.
    exact H7'.
  Qed.
  
  Theorem Page_43_I_1:
    forall a b c d : Prop,
      ((~a -> b) /\ (c \/ ~d)) ->
      ((~a -> b) /\ (~d \/ c)).
  Proof.
    intros a b c d H1.
    destruct H1 as [H1 H1'].
    split.
    intro H2.
    apply H1 in H2.
    exact H2.              
    rewrite -> or_comm.
    exact H1'.
  Qed.
  
  Theorem Page_43_I_2:
    forall e f g h : Prop,
      ((~e \/ f) /\ (g \/ ~h)) ->
      ((e -> f) /\ (g \/ ~ h)).
  Proof.
    intros e f g h H1.
    destruct H1 as [H1 H1'].
    destruct H1 as [H1 | H1''].
    split.
    intro H2.
    unfold not in H1.
    apply H1 in H2.
    contradict H2.
    exact H1'.
    split.
    intro.
    exact H1''.
    exact H1'.
  Qed.
  
  Theorem Page_43_I_3:
    forall i j k l : Prop,
      ((i -> ~j) \/ (~k -> ~l)) ->
      ((i -> ~j) \/ (l -> k)).
  Proof.
    intros i j k l H1.
    destruct H1 as [H1 | H1'].
    left.                  
    exact H1.
    right.
    intro H2.
    destruct (PNP k).
    exact H.
    unfold not in H.
    unfold not in H1'.
    apply H1' in H.
    contradict H.
    exact H2.
  Qed.
  
  Theorem Page_43_I_4:
    forall m n o : Prop,
      (m -> ~(n \/ ~o)) ->
      (m -> (~n /\ ~~o)).
  Proof.
    intros m n o H1 H2.
    apply H1 in H2.
    split.
    unfold not in H2.
    unfold not.
    intro H3.
    apply H2.
    left.
    exact H3.
    unfold not in H2.
    unfold not.
    intro H3.
    assert (H4: n \/ (o -> False)).
    right.
    exact H3.
    apply H2 in H4.
    exact H4.
  Qed.
  
  Theorem Page_43_I_5:
    forall p q r : Prop,
      ((p -> (q \/ r)) \/ (p -> (q \/ r))) ->
      (p -> (q \/ r)).
  Proof.
    intros p q r H1.
    destruct H1 as [H1 | H1].
    exact H1.
    exact H1.
  Qed.
  
  Theorem Page_43_I_6:
    forall s t u v w,
      ((s /\ (t /\ u)) -> (v <-> ~w)) ->
      (((s /\ t) /\ u) -> (v <-> ~w)).
  Proof.
    intros s t u v w H1.
    rewrite -> and_assoc.
    exact H1.
  Qed.
  
  Theorem Page_43_I_7:
    forall x y z a b,
      ((x /\ (y /\ z)) -> (a <-> ~b)) ->
      (x -> ((y /\ z) -> (a <-> ~b))).
  Proof.
    intros x y z a b H1 H2 H3.
    assert(H4: x /\ y /\ z).
    split.
    exact H2.
    exact H3.
    apply H1 in H4.
    exact H4.
  Qed.
  
  Theorem Page_43_I_8:
    forall c d e f : Prop,
      ((c /\ ~d) -> (e <-> ~f)) ->
      ((c /\ ~d) -> ((e /\ ~f) \/ (~e /\ ~ ~f))).
  Proof.
    intros c d e f H1 H2.
    apply H1 in H2.
    clear H1.
    unfold iff in H2.
    destruct H2 as [H2 H2'].
    apply material_conditional in H2.
    apply material_conditional in H2'.
    refine (or_ind _ _ H2).
    intro H3.
    assert (H4: ~ ~ f).
    destruct H2' as [H2' | H2''].
    exact H2'.
    unfold not in H3.
    apply H3 in H2''.
    contradict H2''.
    right.
    split.
    exact H3.
    exact H4.
    intro H3.
    assert (H4: e).
    destruct H2' as [H2' | H2''].
    unfold not in H2'.
    unfold not in H3.
    apply H2' in H3.
    contradict H3.
    exact H2''.
    left.
    split.
    exact H4.
    exact H3.
  Qed.
  
  Theorem Page_43_I_9:
    forall g h i j : Prop,
      ((g \/ h) /\ (i \/ j)) ->
      (((g \/ h) /\ i) \/ ((g \/ h) /\ j)).
  Proof.
    intros g h i j H1.
    destruct H1 as [H1 H2].
    destruct H2 as [H2 | H2'].
    left.
    split.
    exact H1.
    exact H2.
    right.
    split.
    exact H1.
    exact H2'.
  Qed.
  
  Theorem Page_43_I_10:
    forall k l m n o p : Prop,
      ((k /\ l) -> (m /\ ((n /\ o) /\ p))) ->
      ((k /\ l) -> (m /\ ((o /\ n) /\ p))).
  Proof.
    intros k l m n o p H1.
    intro H2.
    apply H1 in H2.
    destruct H2 as [H2 H2'].
    split.
    exact H2.
    destruct H2' as [H2' H2''].
    split.
    rewrite -> and_comm.
    exact H2'.
    exact H2''.
  Qed.
  
  Theorem Page_43_I_11:
    forall q r s t u : Prop,
      (~ (q \/ ~ ((r /\ ~s) /\ (t \/ ~u)))) ->
      ~ (q \/ (~ (r /\ ~s) \/ ~ (t \/ ~u))).
  Proof.
    intros q r s t u.
    intro H1.
    rewrite <- de_morgan_2.
    exact H1.
  Qed.
  
  Theorem Page_43_I_12:
    forall v w x y z : Prop,
      (~v -> (w -> (~ (x /\ y) -> ~z))) ->
      (~v -> ((w /\ ~ (x /\ y)) -> ~z)).
  Proof.  
    intros v w x y z H1.
    rewrite -> AandBthenC.
    exact H1.
  Qed.
  
  Theorem Page_43_I_13:
    forall a b c d e : Prop,
      ((a \/ (b \/ c)) \/ ((d \/ d) \/ e)) ->
      ((a \/ (b \/ c)) \/ (d \/ (d \/ e))).
  Proof.
    intros a b c d e.
    intro.
    destruct H as [H | H'].
    left.
    exact H.
    right.
    destruct H' as [H' | H].
    rewrite <- or_assoc.
    left.
    exact H'.
    right.
    right.
    exact H.
  Qed.
  
  Theorem Page_43_I_14:
    forall f g h i : Prop,
      ((f -> g) /\ (((g -> h) /\ (h -> g)) -> (h -> i))) ->
      ((f -> g) /\ ((g <-> h) -> (h -> i))).
  Proof.
    intros f g h i H1.
    unfold iff.
    exact H1.
  Qed.
  
  Lemma double_negation: forall x, x <-> ~ ~ x.
  Proof.
    intro x.
    split.
    intro H1.
    destruct (PNP (~ x)) as [H2 | H2'].
    unfold not in H2; apply H2 in H1; contradict H1.
    exact H2'.
    
    intro H1.
    destruct (PNP x) as [H2 | H2'].
    exact H2.
    unfold not in H2'.
    unfold not in H1.
    apply H1 in H2'.
    contradict H2'.
  Qed.
  
  Lemma left_and_distributivity:
    forall a b c : Prop, (a /\ (b \/ c)) <-> ((a /\ b) \/ (a /\ c)).
  Proof.
    intros a b c.
    split.
    intro H1.
    destruct H1 as [H1 H1'].
    destruct H1' as [H1' | H1''].
    assert (H2: a /\ b).
    split; assumption.
    left; exact H2.
    assert (H2: a /\ c).
    split; assumption.
    right; exact H2.
    
    intro H1.
    destruct H1 as [H1 | H1'].
    destruct H1 as [H1 H1'].
    assert (H2: b \/ c).
    left; exact H1'.
    split; assumption.
    destruct H1' as [H1 H1'].
    split.
    exact H1.
    right; exact H1'.
  Qed.
  
  Theorem Page_43_I_15:
    forall j k l m n : Prop,
      (j <-> ~(((k /\ ~l) \/ ~m) /\ ((k /\ ~l) \/ ~n))) ->
      (j <-> ~ ((k /\ ~l) \/ (~m /\ ~n))).
  Proof.
    intros j k l m n.
    intro H1.
    destruct H1 as [H1 H1'].
    split.
    intro H2.
    rewrite de_morgan_1.
    split.
    rewrite de_morgan_2.
    rewrite <- double_negation.
    apply H1 in H2.
    rewrite -> de_morgan_2 in H2.
    destruct H2 as [H2 | H2'].
    rewrite -> de_morgan_1 in H2.
    rewrite -> de_morgan_2 in H2.
    rewrite <-? double_negation in H2.
    destruct H2 as [H2 H2'].
    exact H2.
    rewrite -> de_morgan_1 in H2'.
    destruct H2' as [H2 H2'].
    rewrite -> de_morgan_2 in H2.
    rewrite <- double_negation in H2.
    exact H2.
    apply H1 in H2.
    rewrite ->? de_morgan_1 in H2.
    rewrite ->? de_morgan_2 in H2.
    rewrite ->? de_morgan_1 in H2.
    rewrite <-? double_negation in H2.
    rewrite -> de_morgan_2.
    rewrite <-? double_negation.
    destruct H2 as [H2 | H2'].
    destruct H2 as [H2 H2'].
    left; exact H2'.
    destruct H2' as [H2 H2'].
    right; exact H2'.
    intro H2.
    apply H1'.
    generalize H2.
    rewrite <- hypothetical_syllogism.
    intro H3.
    destruct H3 as [H3 H3'].
    destruct H3 as [H4 | H4].
    left; exact H4.
    destruct H3' as [H5 | H5'].
    left; exact H5.
    right.
    split; assumption.
  Qed.
  
  Theorem Page_43_I_16:
    forall o p q r : Prop,
      (o -> ((p /\ ~q) <-> (p /\ ~ ~r))) ->
      (o -> ((p /\ ~q) <-> (~ ~p /\ ~ ~r))).
  Proof.
    intros o p q r H1 H2.
    apply H1 in H2.
    clear H1.
    unfold iff in H2.
    destruct H2 as [H2 H3].
    unfold iff.
    split.
    intro H4.
    destruct H4 as [H4 H5].
    split.
    rewrite <- double_negation.
    exact H4.
    assert(H6: p /\ ~q).
    split; assumption.
    apply H2 in H6.
    destruct H6 as [H7 H8].
    exact H8.
    rewrite <- double_negation.
    exact H3.
  Qed.
  
  Theorem Page_43_I_17:
    forall s t u : Prop,
      (~s <-> (~ ~t -> (~ ~ ~u \/ (~t /\ s)))) ->
      (~s <-> (~ ~ ~t \/ (~ ~ ~u \/ (~t /\ s)))).
  Proof.        
    intros s t u H1.
    rewrite <- material_conditional.
    exact H1.
  Qed.
  
  Theorem Page_43_I_18:
    forall v w x y z : Prop,
      (v -> ((~w -> ~ ~ x) \/ ((~ y -> z) \/ (~ z -> ~ y)))) ->
      (v -> ((~x -> w) \/ ((~y -> z) \/ (~z -> ~y)))).
  Proof.    
    intros v w x y z.
    rewrite <- hypothetical_syllogism at 1.
    intro; assumption.
  Qed.
  
  Theorem Page_43_I_19:
    forall a b c d : Prop,
      ((a /\ ~b) -> ((c /\ c) -> (c -> d))) ->
      ((a /\ ~b) -> (c -> (c -> d))).
  Proof.    
    intros a b c d H1 H2 H3 H4.
    apply H1 in H2.
    exact H2.
    split; assumption.
    exact H3.
  Qed.
  
  Theorem Page_43_I_20:
    forall e f g h : Prop,
      ((e /\ ~f) -> (g -> (g -> h))) ->
      ((e /\ ~f) -> ((g /\ g) -> h)).
  Proof.    
    intros e f g h H1 H2 H3.
    apply H1 in H2.
    exact H2.
    destruct H3; assumption.
    destruct H3; assumption.
  Qed.
  
  Theorem Page_45_III_1:
    forall a b,
      (~ a) -> (a -> b).
  Proof.    
    intros a b H1 H2.
    unfold not in H1.
    apply H1 in H2; contradict H2.
  Qed.
  
  Theorem Page_45_III_2:
    forall c d,
      c -> (d -> c).
  Proof.    
    intros c d H1 H2.
    exact H1.
  Qed.
  
  Theorem Page_45_III_3:
    forall e f g,
      (e -> (f -> g)) -> 
      (f -> (e -> g)).
  Proof.    
    intros e f g H1 H2 H3.
    specialize (H1 H3 H2); exact H1.
  Qed.
  
  Theorem Page_45_III_4:
    forall h i j,
      (h -> (i /\ j)) ->
      (h -> i).
  Proof.    
    intros h i j H1 H2.
    specialize (H1 H2); destruct H1; assumption.
  Qed.
  
  Theorem Page_45_III_5:
    forall k l m : Prop, 
      (k -> l) ->
      (k -> (l \/ m)).
  Proof.    
    intros k l m H1 H2.
    specialize (H1 H2).
    left; assumption.
  Qed.
  
  Theorem Page_45_III_6:
    forall n o p : Prop,
      (n -> o) ->
      ((n /\ p) -> o).
  Proof.    
    intros n o p H1 H2.
    destruct H2 as [H2 H3].
    specialize (H1 H2); exact H1.
  Qed.
  
  Theorem Page_45_III_7:
    forall q r s,
      ((q \/ r) -> s) ->
      (q -> s).
  Proof.    
    intros q r s H1 H2.
    assert (H3: q \/ r).
    left; exact H2.
    specialize (H1 H3); exact H1.
  Qed.
  
  Theorem Page_45_III_8:
    forall t u v : Prop,
      (t -> ~ (u -> v)) ->
      (t -> u).
  Proof.    
    intros t u v H1 H2.
    specialize (H1 H2).
    rewrite -> material_conditional in H1.    
    rewrite -> de_morgan_1 in H1.
    destruct H1 as [H1 _].
    rewrite <- double_negation in H1; exact H1.
  Qed.
  
  Theorem Page_45_III_9:
    forall w x y : Prop,
      (w -> (x /\ ~y)) ->
      (w -> (y -> x)).
  Proof.    
    intros w x y H1 H2 H3.
    specialize (H1 H2).
    destruct H1 as [H1 _]; exact H1.
  Qed.
  
  Theorem Page_45_III_10:
    forall a b c d : Prop,
      (a -> ~ (b -> c)) ->
      ((d /\ b) -> c) ->
      d -> ~a.
  Proof.    
    intros a b c d H1 H2 H3.
    rewrite -> hypothetical_syllogism in H1.
    apply H1.
    rewrite <- double_negation.
    intros H4.
    assert (H5: d /\ b).
    split; assumption.
    specialize (H2 H5).
    exact H2.
  Qed.
  
  Theorem Page_45_III_11:
    forall e f g : Prop,
      (e -> f) ->
      (e -> g) ->
      (e -> (f /\ g)).        
  Proof.    
    intros e f g H1 H2 H3.
    specialize (H1 H3).
    specialize (H2 H3).
    split; assumption.
  Qed.
  
  Theorem Page_45_III_12:
    forall h i j,
      (h -> (i \/ j)) ->
      ~i ->
      (h -> j).
  Proof.    
    intros h i j H1 H2 H3.
    specialize (H1 H3).
    unfold not in H2.
    destruct H1 as [H1 | H1'].
    specialize (H2 H1); contradict H2.
    exact H1'.
  Qed.
  
  Theorem Page_45_III_13:
    forall k l m n o p q r,
      ((k \/ l) -> ~ (m /\ n)) ->
      ((~ m \/ ~ n) -> (o <-> p)) ->
      ((o <-> p) -> (q /\ r)) ->
      ((l \/ k) -> (r /\ q)).
  Proof.    
    intros k l m n o p q r H1 H2 H3 H4.
    rewrite -> and_comm.
    apply H3.
    apply H2.
    rewrite <- de_morgan_2.
    apply H1.
    rewrite -> or_comm.
    exact H4.
  Qed.
  
  Theorem Page_45_III_14:
    forall s t : Prop,
      (s -> t) ->
      (s \/ t) -> t.
  Proof.    
    intros s t H1 H2.
    destruct H2 as [H2 | H3].
    apply H1; assumption.
    assumption.
  Qed.
  
  Theorem Page_45_III_15: 
    forall u v w x : Prop,
      ((~u \/ v) /\ (u \/ w)) ->
      (~x -> ~w) ->
      (v \/ x).
  Proof.    
    intros u v w x H1 H2.
    destruct H1 as [H1 H3].
    destruct H3 as [H3 | H4].
    destruct H1 as [H1 | H4].
    specialize (H1 H3); contradict H1.
    left; exact H4.
    rewrite <- hypothetical_syllogism in H2.
    specialize (H2 H4).
    right; assumption.
  Qed.
  
  Theorem Page_45_III_16:
    forall a b c d e : Prop,
      (a -> (b -> c)) ->
      (c -> (d /\ e)) ->
      (a -> (b -> d)).
  Proof.    
    intros a b c d e H1 H2 H3 H4.
    specialize (H2 (H1 H3 H4)).
    destruct H2 as [H2 _].
    exact H2.
  Qed.
  
  Theorem Page_45_III_17:
    forall e f g : Prop,
      (e -> f) ->
      (g -> f) ->
      ((e \/ g) -> f).
  Proof.    
    intros e f g H1 H2 H3.
    destruct H3.
    apply H1; assumption.
    apply H2; assumption.
  Qed.
  
  Theorem Page_45_III_18:
    forall h i j k : Prop,
      (((h /\ i) -> j) /\ (~k -> (i /\ ~j))) ->
      (h -> k).
  Proof.    
    intros h i j k H1 H2.
    destruct H1 as [H1 H3].
    rewrite -> hypothetical_syllogism in H3.
    rewrite <- double_negation in H3.
    apply H3.
    unfold not.
    intro H4.
    destruct H4 as [H4 H5].
    apply H5.
    apply H1.
    split; assumption.
  Qed.
  
  Theorem Page_45_III_19:
    forall l m n : Prop,
      ((l /\ (m \/ n)) -> (m /\ n)) ->
      (l -> (m -> n)).
  Proof.    
    intros l m n H1 H2 H3.
    assert (H4: (l /\ (m \/ n))).
    split.
    exact H2.
    left; exact H3.
    specialize (H1 H4).
    destruct H1 as [_ H1].
    exact H1.
  Qed.
  
  Theorem Page_45_III_20:
    forall o p q r : Prop,
      (o -> (p -> q)) ->
      (p -> (q -> r)) ->
      (o -> (p -> r)).
  Proof.    
    intros o p q r H1 H2 H3 H4.
    specialize (H2 H4 (H1 H3 H4)); exact H2.
  Qed.
  
  Theorem Page_45_III_21:
    forall s t u v : Prop,
      (s -> (t /\ u)) ->
      ((t \/ u) -> v) ->
      (s -> v).
  Proof.    
    intros s t u v H1 H2 H3.
    specialize (H1 H3).
    destruct H1 as [H1 _].
    apply H2.
    left; exact H1.
  Qed.
  
  Theorem Page_45_III_22:
    forall w x y z : Prop,
      (~w \/ ((x -> y) /\ (z -> y))) ->
      (w /\ (x \/ z)) ->
      y.
  Proof.    
    intros w x y z H1 H2.
    destruct H2 as [H2 H3].
    destruct H1 as [H1 | H4].
    unfold not in H1.
    specialize (H1 H2); contradict H1.
    destruct H4 as [H4 H5].
    destruct H3 as [H6 | H7].
    apply H4; exact H6.
    apply H5; exact H7.
  Qed.
  
  Theorem Page_45_III_23:
    forall a b c d e : Prop,
      ((a \/ b) -> (c /\ d)) -> 
      (~a -> (e -> ~e)) ->
      ~c ->
      ~e.
  Proof.   
    intros a b c d e H1 H2 H3.
    intro H4.
    unfold not in H3.
    assert (H5: a -> (c /\ d)).
    intros H6.
    assert(H7: a \/ b).
    left; exact H6.
    specialize (H1 H7).
    destruct H1 as [H1 _].
    specialize (H3 H1).
    contradict H3.
    elim H2.
    intro H6.
    specialize (H5 H6).
    destruct H5 as [H5 H7].
    specialize (H3 H5); contradict H3.
    exact H4.
    exact H4.
  Qed.
  
  Theorem Page_45_III_24:
    forall f g h i : Prop,
      ((f -> g) /\ (h -> i)) ->
      (f \/ h) ->
      ((f -> ~i) /\ (h -> ~g)) ->
      (g <-> ~i).
  Proof.    
    intros f g h i H1 H2 H3.
    split.
    intro H4.
    destruct H3 as [H3 H3'].
    apply H3.
    destruct H1 as [H1 H1'].
    destruct H2 as [H2 | H2'].
    exact H2.
    specialize (H3' H2').
    specialize (H3' H4); contradict H3'.
    intro H4.
    destruct H1 as [H1 H5].
    apply H1.
    destruct H2 as [H2 | H2'].
    exact H2.
    specialize (H5 H2').
    specialize (H4 H5).
    contradict H4.
  Qed.
  
  Theorem Page_45_III_25:
    forall j k l m n o p : Prop,
      (j /\ (k /\ l)) -> 
      ((k /\ j) -> (m \/ (n \/ o))) ->
      (~m /\ (~p /\ ~o)) ->
      n.
  Proof.    
    intros j k l m n o p H1 H2 H3.
    destruct H1 as [H11 [H12 H13]].
    destruct H3 as [H31 [H32 H33]].
    assert (H4: k /\ j).
    split; assumption.
    specialize (H2 H4).
    destruct H2 as [H2 | [H2' | H2'']].
    unfold not in H31; specialize (H31 H2); contradict H31.
    exact H2'.
    unfold not in H33; specialize (H33 H2''); contradict H33.
  Qed.
  
  Theorem Page_45_III_26:
    forall q r s t : Prop,
      (q \/ (r /\ s)) ->
      ((q -> t) /\ (t -> s)) ->
      s.
  Proof.    
    intros q r s t H1 H2.
    destruct H2 as [H21 H22].
    destruct H1 as [H11 | [H12 H13]].
    apply H22; apply H21; exact H11.
    exact H13.
  Qed.
  
  Theorem Page_45_III_27:
    forall u v w x : Prop,
      ((u -> v) /\ (w -> x)) ->
      ((u \/ w) -> (v \/ x)).
  Proof.    
    intros u v w x H1 H2.
    destruct H1 as [H11 H12].
    destruct H2 as [H21 | H22].
    apply H11 in H21.
    left; exact H21.
    apply H12 in H22.
    right; exact H22.
  Qed.
  
  Theorem Page_45_III_28:
    forall y z a b : Prop,
      ((y -> z) /\ (a -> b)) ->
      ((y /\ a) -> (z /\ b)).
  Proof.    
    intros y z a b H1 H2.
    destruct H1 as [H11 H12].
    destruct H2 as [H21 H22].
    split.
    apply H11; exact H21.
    apply H12; exact H22.
  Qed.
  
  Theorem Page_45_III_29:
    forall c d e f g : Prop,
      ((c -> d) /\ (e -> f)) ->
      (g -> (c \/ e)) ->
      (g -> (d \/ f)).
  Proof.    
    intros c d e f g H1 H2 H3.
    destruct H1 as [H11 H12].
    specialize (H2 H3).
    destruct H2 as [H21 | H22].
    left; apply H11; exact H21.
    right; apply H12; exact H22.
  Qed.
  
  Theorem Page_45_III_30:
    forall h i j k l m : Prop,
      ((h -> i) /\ (j -> k)) ->
      (h \/ j) ->
      ((h -> ~k) /\ (j -> ~i)) ->
      ((i /\ ~k) -> l) ->
      (k -> (i \/ m)) ->
      (l \/ m).
  Proof.    
    intros h i j k l m H1 H2 H3 H4 H5.
    destruct H1 as [H11 H12].
    destruct H3 as [H31 H32].
    destruct H2 as [H21 | H22].
    left.
    apply H4.
    split.
    apply H11; exact H21.
    apply H31; exact H21.
    specialize (H5 (H12 H22)).
    destruct H5 as [H51 | H52].
    left.
    apply H4.
    split.
    exact H51.
    apply H31.
    rewrite -> hypothetical_syllogism in H32.
    rewrite <- double_negation in H32.
    specialize (H32 H51).
    specialize (H32 H22); contradict H32.
    right; exact H52.
  Qed.
  
  Theorem Page_54_1: 
    forall a b c: Prop,
      (a \/ (b /\ c)) ->
      (a -> c) ->
      c.
  Proof.
    intros a b c H1 H2.
    destruct H1 as [H11 | [H121 H122]].
    apply H2 in H11; exact H11.
    exact H122.
  Qed.
  
  Theorem Page_54_2: 
    forall d e f g h : Prop,
      ((d \/ e) -> (f -> g)) ->
      ((~g \/ h) -> (d /\ f)) ->
      g.
  Proof.
    intros d e f g h H1 H2.
    rewrite ->? material_conditional in H1.
    rewrite ->? material_conditional in H2.
    rewrite -> de_morgan_1 in H1.  
    rewrite -> de_morgan_1 in H2.
    rewrite <- double_negation in H2.
    destruct H2 as [[H21 H22] | [H23 H24]].
    exact H21.
    destruct H1 as [[H11 H12] | [H13 | H14]].
    unfold not in H11; apply H11 in H23; contradict H23.
    unfold not in H13; apply H13 in H24; contradict H24.
    exact H14.
  Qed.
  
  Theorem Page_54_3: 
    forall h i j k l : Prop,
      ((h -> i) /\ (j -> k)) ->
      ((i \/ k) -> l) ->
      (~l) ->
      ~(h \/ j).
  Proof.
    intros h i j k l H1 H2 H3.
    destruct H1 as [H11 H12].
    rewrite -> de_morgan_1.
    split.
    rewrite -> material_conditional in H11.
    rewrite -> material_conditional in H12.
    rewrite -> material_conditional in H2.
    rewrite -> de_morgan_1 in H2.
    destruct H11 as [H111 | H112].
    exact H111.
    destruct H2 as [H21 | H22].
    destruct H21 as [H211 H212].
    unfold not in H211; apply H211 in H112; contradict H112.
    unfold not in H3; apply H3 in H22; contradict H22.
    rewrite -> hypothetical_syllogism in H2.
    specialize (H2 H3).
    rewrite -> de_morgan_1 in H2.
    destruct H2 as [H21 H22].
    rewrite -> hypothetical_syllogism in H12.
    apply H12.
    exact H22.
  Qed.
  
  Theorem Page_54_4: 
    forall m n o p r s q t u : Prop,
      ((m \/ n) -> (o /\ p)) ->
      ((o \/ q) -> (~r /\ s)) ->
      ((r \/ r) -> (m /\ u)) ->
      ~r.
  Proof.
    intros m n o p r s q t u H1 H2 H3.
    unfold not.
    intro H4.
    assert(H5: r \/ r).
    left; exact H4.
    specialize (H3 H5).
    clear H5.
    destruct H3 as [H31 H32].
    assert(H5: m \/ n).
    left; exact H31.
    specialize (H1 H5).
    clear H5.
    destruct H1 as [H11 H12].
    assert(H5: o \/ q).
    left; exact H11.
    specialize (H2 H5).
    destruct H2 as [H21 _].
    unfold not in H21.
    specialize (H21 H4).
    exact H21.
  Qed.
  
  Theorem Page_54_5: 
    forall v w x y z a b c : Prop,
      ((v -> ~w) /\ (x -> y)) ->
      ((~w -> z) /\ (y -> ~a)) ->
      ((z -> ~b) /\ (~a -> c)) ->
      (v /\ x) ->
      ~b /\ c.
  Proof.
    intros v w x y z a b c H1 H2 H3 H4.
    destruct H1 as [H11 H12].
    destruct H2 as [H21 H22].
    destruct H3 as [H31 H32].
    destruct H4 as [H41 H42].
    split.
    apply H31.
    apply H21.
    apply H11.
    exact H41.
    apply H32.
    apply H22.
    apply H12.
    exact H42.
  Qed.
  
  Theorem Page_56_I_1: 
    forall p q : Prop,
      p -> (q -> p).
  Proof.
    intros p q H1 H2.
    exact H1.
  Qed.
  
  Theorem Page_56_I_2: 
    forall p q r : Prop,
      (p -> (q -> r)) -> ((p -> q) -> (p -> r)).
  Proof.
    intros p q r H1 H2 H3.
    apply H1.
    exact H3.
    apply H2; exact H3.
  Qed.
  
  Theorem Page_56_I_3: 
    forall p q r : Prop,
      (p -> (q -> r)) -> (q -> (p -> r)).
  Proof.
    intros p q r H1 H2 H3.
    apply H1.
    exact H3.
    exact H2.
  Qed.
  
  Theorem Page_56_I_4: 
    forall p q : Prop,
      (p -> q) -> (~q -> ~p).
  Proof.
    intros p q H1 H2.
    unfold not in H2.
    unfold not.
    intro H3.
    specialize (H2 (H1 H3)).
    exact H2.
  Qed.
  
  Theorem Page_56_I_5: 
    forall p : Prop,
      ~ ~p -> p.
  Proof.
    intros p H1.
    unfold not in H1.
    destruct (PNP p) as [H2 | H3].
    exact H2.
    unfold not in H3.
    apply H1 in H3.
    contradict H3.
  Qed.
  
  Theorem Page_56_I_6: 
    forall p : Prop,
      p -> ~ ~p.
  Proof.
    intros p H1.
    unfold not.
    intro H2.
    apply H2.
    exact H1.
  Qed.
  
  Theorem Page_56_I_7: 
    forall a b c : Prop,
      (a -> b) -> ((b -> c) -> (a -> c)).
  Proof.
    intros a b c H1 H2 H3.
    specialize (H2 (H1 H3)).
    exact H2.
  Qed.
  
  Theorem Page_56_I_8: 
    forall a b c : Prop,
      ((a -> b) /\ (a -> c)) -> (a -> (b \/ c)).
  Proof.
    intros a b c H1 H2.
    destruct H1 as [H11 H12].
    specialize (H11 H2).
    left; exact H11.
  Qed.
  
  Theorem Page_56_I_9: 
    forall a b c : Prop,
      ((a -> b) /\ (a -> c)) -> (a -> (b /\ c)).
  Proof.
    intros a b c H1 H2.
    destruct H1 as [H11 H12].
    specialize (H11 H2).
    specialize (H12 H2).
    split; assumption.
  Qed.
  
  Theorem Page_56_I_10: 
    forall a b : Prop,
      (a -> b) -> (a -> (a /\ b)).
  Proof.
    intros a b H1 H2.
    specialize (H1 H2).
    split; assumption.
  Qed.
  
  Theorem Page_56_I_11: 
    forall a b : Prop,
      (a -> b) -> ((~a -> b) -> b).
  Proof.
    intros a b H1 H2.
    destruct (PNP a) as [H3 | H4].
    specialize (H1 H3); assumption.
    specialize (H2 H4); assumption.
  Qed.
  
  Theorem Page_56_I_12: 
    forall a b c : Prop,
      (a -> b) -> ((a /\ c) -> (b /\ c)).
  Proof.
    intros a b c H1 H2.
    destruct H2 as [H21 H22].
    split.
    specialize (H1 H21); assumption.
    assumption.
  Qed.
  
  Theorem Page_56_I_13: 
    forall a b : Prop,
      ((a -> b) -> b) -> (a \/ b).
  Proof.
    intros a b H1.
    destruct (PNP a) as [H2 | H3].
    left; exact H2.
    right; apply H1.
    intro H4.
    unfold not in H3.
    specialize (H3 H4).
    contradict H3.
  Qed.
  
  Theorem Page_56_I_14: 
    forall a b c : Prop,
      (b -> c) -> ((a \/ b) -> (c \/ a)).
  Proof.
    intros a b c H1 H2.
    destruct H2 as [H21 | H22].
    right; exact H21.
    left; apply H1; exact H22.
  Qed.
  
  Theorem Page_56_I_15: 
    forall a b c d e : Prop,
      (a -> (b /\ c)) -> ((b -> (d /\ e)) -> (a -> d)).
  Proof.
    intros a b c d e H1 H2 H3.
    specialize (H1 H3); clear H3.
    destruct H1 as [H11 H12].
    specialize (H2 H11).
    destruct H2; assumption.
  Qed.
  
  Theorem Page_56_I_16: 
    forall a b c d e : Prop,
      ((a \/ b) -> c) -> (((c \/ d) -> e) -> (a -> e)).
  Proof.
    intros a b c d e H1 H2 H3.
    apply H2.
    left.
    apply H1.
    left; exact H3.
  Qed.
  
  Theorem Page_56_I_17: 
    forall a b : Prop,
      ((a -> b) -> a) -> a.
  Proof.
    intros a b H1.
    rewrite ->? material_conditional in H1.
    rewrite -> de_morgan_1 in H1.
    rewrite <- double_negation in H1.
    destruct H1 as [[H11 H12] | H13]; assumption.
  Qed.
  
  Theorem Page_56_I_18: 
    forall p : Prop,
      p -> (p /\ p).
  Proof.
    intros p H1.
    split; assumption.
  Qed.
  
  Theorem Page_56_I_19: 
    forall p q : Prop,
      (p /\ q) -> p.
  Proof.
    intros p q H1.
    destruct H1 as [H11 H12]; assumption.
  Qed.
  
  Theorem Page_56_I_20: 
    forall p q r : Prop,
      (p -> q) -> (~(q /\ r) -> ~(r /\ p)).
  Proof.
    intros p q r H1 H2.
    rewrite -> de_morgan_2 in H2.
    rewrite -> de_morgan_2.
    destruct H2 as [H21 | H22].
    rewrite -> hypothetical_syllogism in H1.
    specialize (H1 H21).
    right; exact H1.
    left; exact H22.
  Qed.
  
  Theorem Page_56_II_1: 
    forall a b : Prop,
      (a -> b) \/ (a -> ~b).
  Proof.
    intros a b.
    rewrite ->? material_conditional.
    destruct (PNP b) as [H1 | H2].
    left; right; assumption.
    right; right; assumption.
  Qed.
  
  Theorem Page_56_II_2: 
    forall a b : Prop,
      (a -> b) \/ (~a -> b).
  Proof.
    intros a b.
    destruct (PNP a) as [H1 | H2].
    right.
    intros H3.
    unfold not in H3.
    apply H3 in H1.
    contradict H1.
    left.
    intro H3.
    unfold not in H2.
    apply H2 in H3.
    contradict H3.
  Qed.
  
  Theorem Page_56_II_3: 
    forall a b : Prop,
      (a -> b) \/ (b -> a).
  Proof.
    intros a b.
    destruct (PNP a).
    right.
    rewrite -> material_conditional.
    right; assumption.
    left.  
    rewrite -> material_conditional.
    left; assumption.
  Qed.
  
  Theorem Page_56_II_4: 
    forall a b c : Prop,
      (a -> b) \/ (b -> c).
  Proof.
    intros a b c.
    rewrite ->? material_conditional.
    destruct (PNP b).
    left.
    right; assumption.
    right.
    left; assumption.
  Qed.
  
  Theorem Page_56_II_5: 
    forall a b c : Prop,
      (a -> b) \/ (~a -> c).
  Proof.
    intros a b c.
    rewrite ->? material_conditional.
    destruct (PNP a).
    right.
    left.
    rewrite <- double_negation; assumption.
    left.
    left; assumption.
  Qed.
  
  Theorem Page_56_II_6: 
    forall a b : Prop,
      a \/ (a -> b).
  Proof.
    intros a b.
    destruct (PNP a) as [H1 | H2].
    left; assumption.
    right.
    intro H3.
    unfold not in H2.
    apply H2 in H3.
    contradict H3.
  Qed.
  
  Theorem Page_56_II_7: 
    forall p : Prop,
      p <-> ~ ~p.
  Proof.
    apply double_negation.
  Qed.
  
  Theorem Page_56_II_8: 
    forall a b : Prop,
      a <-> (a /\ (a \/ b)).
  Proof.
    intros a b.
    split.
    intros H1.
    split.
    exact H1.
    left; exact H1.
    intro H1.
    destruct H1 as [H11 [H12 | H13]]; assumption.
  Qed.
  
  Theorem Page_56_II_9: 
    forall a b : Prop,
      a <-> (a \/ (a /\ b)).
  Proof.
    intros a b.
    split.
    intro H1.
    left; assumption.
    intro H1.
    destruct H1 as [H11 | [H12 H13]]; assumption.
  Qed.
  
  Theorem Page_56_II_10: 
    forall a : Prop,
      ~ ((a -> ~a) /\ (~a -> a)).
  Proof.
    intro a.
    rewrite -> de_morgan_2.
    rewrite ->? material_conditional.
    destruct (PNP a) as [H1 | H2].
    left.
    rewrite -> de_morgan_1.
    rewrite <-? double_negation.
    split; assumption.
    right.
    rewrite de_morgan_1.
    rewrite <-? double_negation.
    split; assumption.
  Qed.
  
  Theorem Page_61_1: 
    forall a b c d: Prop,
      (a -> b) -> 
      (b -> ((c -> ~ ~c) -> d)) ->
      (a -> d).
  Proof.
    intros a b c d H1 H2 H3.
    specialize (H2 (H1 H3)).
    clear H1 H3.
    assert(H4: c -> ~ ~c).
    intro H3.
    rewrite <- double_negation; exact H3.
    specialize (H2 H4); exact H2.
  Qed.
  
  Theorem Page_61_2: 
    forall e f g h i j : Prop,
      ((e \/ f) -> g) ->
      (h -> (i /\ j)) ->
      ((e -> g) /\ (h -> i)).
  Proof.
    intros e f g h i j H1 H2.
    split.
    intro H3.
    assert (H4: e \/ f).
    left; exact H3.
    specialize (H1 H4); exact H1.
    intro H3.
    specialize (H2 H3).
    destruct H2 as [H2 _]; exact H2.
  Qed.
  
  Theorem Page_61_3: 
    forall k l m n o p : Prop,
      ((k -> l) /\ (m -> n)) ->
      ((l \/ n) -> ((o -> (o \/ p)) -> (k /\ m))) ->
      (k <-> m).
  Proof.
    intros k l m n o p H1 H2.
    destruct H1 as [H11 H12].
    split.
    intro H3.
    specialize (H11 H3).
    assert (H4: l \/ n).
    left; exact H11.
    specialize (H2 H4).
    clear H4.
    assert(H4: o -> o \/ p).
    intros H4.
    left; exact H4.
    specialize (H2 H4).
    destruct H2 as [_ H21].
    exact H21.
    intro H3.
    specialize (H12 H3).
    assert (H4: l \/ n).
    right; exact H12.
    specialize (H2 H4).
    clear H4.
    assert(H4: o -> o \/ p).
    intros H4.
    left; exact H4.
    specialize (H2 H4).
    destruct H2 as [H21 _]; exact H21.
  Qed.
  
  Theorem Page_61_4: 
    forall q r s t u v : Prop,
      (q \/ (r -> s)) ->
      ((r -> (r /\ s)) -> (t \/ u)) ->
      ((t -> q) /\ (u -> v)) ->
      (q \/ v).
  Proof.
    intros q r s t u v H1 H2 H3.
    destruct H3 as [H31 H32].
    destruct H1 as [H11 | H12].
    left; exact H11.
    cut (t \/ u).
    intro H4.
    destruct H4 as [H41 | H42].
    specialize (H31 H41).
    left; exact H31.
    right; apply H32; exact H42.
    apply H2.
    intro H4.
    split.
    exact H4.
    apply H12; exact H4.
  Qed.
  
  Theorem Page_61_5: 
    forall w x y z a b : Prop,
      ((w -> (~x /\ ~y)) /\ (z -> ~(x \/ y))) ->
      ((~a -> w) /\ (~b -> z)) ->
      ((a -> x) /\ (b -> y)) ->
      (x <-> y).
  Proof.
    intros w x y z a b H1 H2 H3.
    destruct H1 as [H11 H12].
    destruct H2 as [H21 H22].
    destruct H3 as [H31 H32].
    split.
    intro H4.
    apply H32.
    rewrite -> hypothetical_syllogism in H22.
    rewrite <- double_negation in H22.
    apply H22.
    rewrite -> hypothetical_syllogism in H12.
    rewrite <- double_negation in H12.
    apply H12.
    left; exact H4.
    intro H4.
    apply H31.
    rewrite -> hypothetical_syllogism in H21.
    rewrite <- double_negation in H21.
    apply H21.
    rewrite -> hypothetical_syllogism in H11.
    apply H11.
    rewrite -> de_morgan_2.
    rewrite <-? double_negation.
    right; exact H4.
  Qed.
  
  Theorem Page_61_6: 
    forall c d e f g h : Prop,
      ((c \/ d) -> (e -> f)) ->
      ((e -> (e /\ f)) -> g) ->
      (g -> ((~h \/ ~ ~h) -> (c /\ h))) ->
      (c <-> g).
  Proof.
    intros c d e f g h H1 H2 H3.
    split.
    intro H4.
    apply H2.
    intro H5.
    split.
    exact H5.
    apply H1.
    left; exact H4.
    exact H5.
    intro H4.
    specialize (H3 H4).
    rewrite <- double_negation in H3.
    assert(H5: ~h \/ h).
    rewrite -> or_comm.
    apply (PNP h).
    specialize (H3 H5).
    destruct H3 as [H31 _]; exact H31.
  Qed.
  
  Theorem Page_76_I_1 {T : Type}: 
    forall A B : T -> Prop, forall t : T,
      (forall x, (A x -> B x)) ->
      (~ B t) ->
      (~ A t).
  Proof.
    intros A B t H1 H2.
    unfold not in H2.
    unfold not.
    intro H3.
    specialize (H2 ((H1 t) H3)); exact H2.
  Qed.    
  
  Theorem Page_76_I_2 {T : Type}: 
    forall C D E : T -> Prop,
      (forall x, (C x -> D x)) ->
      (forall x, (E x -> ~ D x)) ->
      (forall x, (E x -> ~ C x)).
  Proof.
    intros C D E H1 H2 x H3.
    specialize ((H2 x) H3).
    intro H4.
    specialize (H2 (H1 x H4)); exact H2.
  Qed.
  
  Theorem Page_76_I_3 {T : Type}: 
    forall F G H : T -> Prop, 
      (forall x, F x -> ~ G x) ->
      (exists x, H x /\ G x) ->
      (exists x, H x /\ ~ F x).
  Proof.
    intros F G H H1 H2.
    elim H2.



    elim H2; intros x H3.
    destruct H3 as [H31 H32].
    assert (H4: F x -> ~ G x).
    apply H1.
    rewrite -> hypothetical_syllogism in H4.
    rewrite <- double_negation in H4.
    specialize (H4 H32).
    assert (H5: H x /\ ~ F x).
    split; assumption.
    exists x; exact H5.
  Qed.
  
  Theorem Page_76_I_4: 
    forall I J : Type -> Prop,
      (forall x, I x -> J x) ->
      (exists x, I x /\ ~ J x) ->
      (forall x, J x -> I x).
  Proof.
    intros I J H1 H2.
    elim H2; intros x H3.
    destruct H3 as [H31 H32].
    apply H1 in H31.
    unfold not in H32.
    apply H32 in H31.
    contradict H31.
  Qed.
  
  Theorem Page_76_I_5: 
    forall K L M : Type -> Prop,
      (forall x, K x -> L x) ->
      (forall x, ((K x /\ L x) -> M x)) ->
      (forall x, K x -> M x).
  Proof.
    intros K L M H1 H2 x H3.
    apply H2.
    split.
    exact H3.
    apply H1.
    exact H3.
  Qed.
  
  Theorem Page_76_I_6: 
    forall N O P : Type -> Prop,
      (forall x, N x -> O x) -> 
      (forall x, P x -> O x) ->
      (forall x, (N x \/ P x) -> O x).
  Proof.
    intros N O P H1 H2 x H3.  
    destruct H3 as [H31 | H32].
    apply H1; exact H31.
    apply H2; exact H32.
  Qed.
  
  Theorem Page_76_I_7: 
    forall Q R : Type -> Prop,
      (forall x, Q x -> R x) ->
      (exists x, Q x \/ R x) ->
      (exists x, R x).
  Proof.
    intros Q R H1 H2.
    elim H2; intros x H3.
    clear H2.
    destruct H3 as [H31 | H32].
    apply H1 in H31.
    exists x; exact H31.
    exists x; exact H32.
  Qed.
  
  Theorem Page_76_I_8: 
    forall S T U V W : Type -> Prop,
      (forall x, S x -> (T x -> U x)) ->
      (forall x, U x -> (V x /\ W x)) ->
      (forall x, S x -> (T x -> V x)).
  Proof.
    intros S T U V W H1 H2 x H3 H4.
    apply H1 in H3.
    apply H2 in H3.
    destruct H3 as [H3 _]; exact H3.
    exact H4.
  Qed.
  
  Theorem Page_76_I_9: 
    forall X Y Z A : Type -> Prop,
      (forall x, (X x \/ Y x) -> (Z x /\ Z x)) ->
      (forall x, (Z x \/ A x) -> (X x /\ Y x)) ->
      (forall x, X x <-> Z x).
  Proof.
    intros X Y Z A H1 H2 x.
    split.
    intro H3.
    assert(H4: X x \/ Y x).
    left; exact H3.
    clear H3.
    apply H1 in H4.
    destruct H4 as [H4 _]; exact H4.
    intro H3.
    assert(H4: Z x \/ A x).
    left; exact H3.
    apply H2 in H4.  
    destruct H4 as [H4 _]; exact H4.
  Qed.
  
  Theorem Page_76_I_10: 
    forall B C D E F G : Type -> Prop,
      (forall x, (B x -> C x) /\ (D x -> E x)) ->
      (forall x, (C x \/ E x) -> ((F x -> (G x -> F x)) -> (B x /\ D x))) ->
      (forall x, B x <-> D x).
  Proof.
    intros B C D E F G H1 H2 x.
    assert(H4: (B x -> C x) /\ (D x -> E x)).
    apply H1.
    destruct H4 as [H41 H42].
    split.
    intro H3.
    specialize (H41 H3).
    assert(H5: C x \/ E x).
    left; exact H41.
    apply H2 in H5.
    destruct H5 as [H51 H52].
    exact H52.
    intros H6 H7.
    exact H6.
    intros H3.
    apply H42 in H3.
    assert (H5: C x \/ E x).
    right; exact H3.
    apply H2 in H5.
    destruct H5 as [H51 H52].
    exact H51.
    intros H6 H7; exact H6.
  Qed.
  
  Theorem Page_103_I_1 {T : Type}: 
    forall (A B C : T -> Prop) (k : T),
      (forall x, A x -> B x) ->
      (forall x, (B x -> C x) -> (A k -> C k)).
  Proof.
    (* not sure why this is true! *)
    admit.
  Qed.
  
  Theorem Page_103_I_2: 
    forall (D E F : nat -> Prop), exists a,
      (forall x, D x -> E x) ->
      (D a -> (forall y, (E y -> F y) -> F a)).
  Proof.
    intros D E F.
    assert (H1: ~ (exists a : nat,
                     (forall x : nat, D x -> E x) ->
                     D a -> forall y : nat, (E y -> F y) -> F a) -> False).
    firstorder.
    constructor.
    destruct (PNP (exists a : nat,
                     (forall x : nat, D x -> E x) ->
                     D a -> forall y : nat, (E y -> F y) -> F a)) as [H21 | H22].
    exact H21.
    unfold not in H1.
    apply H1 in H22.
    contradict H22.
  Qed.
  
  Theorem Page_103_I_3: 
    forall (G H I : Type -> Prop),
      (forall x, G x -> (forall y, H y -> I y)) ->
      ((forall x, G x) -> (forall y, H y -> I y)).
  Proof.
    intros G H I H1 H2 x H3.
    specialize (H1 x (H2 x)).
    apply H1.
    exact H3.
  Qed.
  
  Theorem Page_103_I_4: 
    forall (J K : nat -> Prop),
      ((exists x, J x) -> (exists y, K y)) ->
      (exists x, J x -> exists y, K y).
  Proof.
    intros J K H1.
    assert (n : nat).
    constructor.
    exists n.
    intro H.
    apply H1.
    exists n.
    exact H.
  Qed.
  
  Theorem Page_103_I_5: 
    forall (L M : Type -> Prop),
      ((exists x, L x) -> (forall y, M y)) ->
      (forall x, (L x -> (forall y, M y))).
  Proof.
    intros L M H1.
    intros x H2.
    apply H1.
    exists x.
    exact H2.
  Qed.
  
  Theorem Page_103_I_6: 
    forall (N O P : Type -> Prop),
      (forall x, N x -> O x) ->
      (forall x, P x -> ((forall y, (P y -> N y)) -> O x)).
  Proof.
    intros N O P H1 x H2 H3.
    apply H1.
    apply H3.
    exact H2.
  Qed.
  
  Theorem Page_103_I_7: 
    forall (Q R S T : Type -> Prop),
      (forall x, Q x -> R x) ->
      (forall x, S x -> T x) ->
      ((forall x, R x -> S x) -> (forall y, Q y -> T y)).
  Proof.
    intros Q R S T H1 H2 H3 y H4.  
    apply H2; apply H3; apply H1; exact H4.
  Qed.
  
  Theorem Page_103_I_8: 
    forall (U V W : Type -> Prop),
      (exists x, U x) -> (forall y, (U y \/ V y) -> W y) ->
      ((exists x, U x) /\ (exists x, W x)) ->
      (exists x, U x /\ W x).
  Proof.
    intros U V W H1 H2 H3.
    destruct H1 as [x H1].
    assert (H4: U x \/ V x).
    left; exact H1.
    specialize (H2 x H4).
    assert (H5: U x /\ W x).
    split; assumption.
    exists x.
    exact H5.
  Qed.
  
  Theorem Page_104_I_9: 
    forall (X Y Z : Type -> Prop),
      ((exists x, X x) -> (forall y, Y y -> Z y)) ->
      ((exists x, X x /\ Y x) -> (exists y, X y /\ Z y)).
  Proof.
    intros X Y Z H1 H2.
    destruct H2 as [x [H21 H22]].
    apply H1 in H22.
    exists x.
    split; assumption.
    exists x.
    exact H21.
  Qed.
    
  Theorem Page_104_I_10: 
    forall (A B C D : Type -> Prop),
      ((exists x, A x) -> (forall y, B y -> C y)) ->
      ((exists x, D x) -> (exists y, B y)) ->
      ((exists x, A x /\ D x) -> (exists y, C y)).
  Proof.
    intros A B C D H1 H2 H3.
    destruct H3 as [x [H3 H4]].
    destruct H2 as [y H2].
    exists x; assumption.
    exists y.
    apply H1.
    exists x; assumption.
    assumption.
  Qed.
  
  Theorem Page_104_I_11: 
    forall (E F : Type -> Prop),
      (forall x, exists y, E x \/ F y) ->
      ((forall x, E x) \/ (exists y, F y)).
  Proof.
    intros E F H1.
    destruct (PNP (forall x, E x)) as [H21 | H22].
  
    left.
    exact H21.
  
    right.
    destruct (PNP (exists y, F y)) as [H31 | H32].
  
    exact H31.
    rewrite -> not_forall in H22.
    rewrite -> not_exists in H32.
    destruct H22 as [x H2].
    specialize (H1 x).
    destruct H1 as [y [H11 | H12]].
    apply H2 in H11.
    contradict H11.

    specialize (H32 y).
    apply H32 in H12.
    contradict H12.
  Qed.
    
  Theorem Page_104_I_12: 
    forall (G H I : Type -> Prop),
      ((exists x, G x) \/ (forall y, G y -> H y)) ->
      (forall x, I x -> ~ G x) ->
      ((forall x, G x -> I x) -> (forall y, G y -> H y)).
  Proof.
    intros G H I H1 H2 H3 y H4.
    destruct H1 as [H11 | H12].
    assert (H5: ~G y).
    apply H3 in H4.
    apply H2 in H4.
    exact H4.
    apply H5 in H4.
    contradict H4.
    apply H12 in H4.
    exact H4.
  Qed.

  Theorem Page_104_I_13: 
    forall (J K : Type -> Prop),
      ((exists x, J x) \/ (exists y, K y)) ->
      (forall x, J x -> K x) ->
      (exists y, K y).
  Proof.
    intros J K H1 H2.
    destruct H1 as [H11 | H12].
    destruct H11 as [x H1].
    apply H2 in H1.
    exists x; exact H1.
    exact H12.
  Qed.
  
  Theorem Page_104_I_14: 
    forall (L M N : Type -> Prop),
      (forall x, L x -> M x) ->
      (forall x, M x -> N x) ->
      ((exists x, L x) -> (exists y, N y)).
  Proof.
    intros L M N H1 H2 H3.
    destruct H3 as [x H3].
    apply H1 in H3; apply H2 in H3.
    exists x; exact H3.
    Qed.
  
  Theorem Page_104_I_15: 
    forall (O P Q R S T : Type -> Prop),
      (forall x, O x -> ((forall y, P y -> Q y) -> R x)) ->
      (forall x, R x -> ((forall y, P y -> S y) -> T x)) ->
      ((forall y, P y -> (Q y /\ S y)) -> (forall x, O x -> T x)).
  Proof.
    intros O P Q R S T H1 H2 H3 x H4.
    apply H1 in H4.
    apply H2 in H4.
    exact H4.
    intros y J1.
    apply H3.
    exact J1.
    intros y J1.
    apply H3 in J1; destruct J1 as [J1 _]; exact J1.
  Qed.
  
  Theorem Page_104_I_16: 
    forall (U V W X Y : Type -> Prop),
      (exists x, U x /\ (forall y, V y -> W y)) ->
      (forall x, U x -> ((exists y, X y /\ W y) -> Y x)) ->
      ((exists y, X y /\ V y) -> (exists x, Y x)).
  Proof.
    intros U V W X Y H1 H2 H3.
    destruct H3 as [y [H31 H32]].
    destruct H1 as [x [H11 H12]].
    apply H12 in H32.
    assert (H4: exists y, X y /\ W y).
    exists y.
    split; assumption.
    apply H2 in H11.
    exists x; exact H11.
    exact H4.
  Qed.  
  
  Theorem Page_104_I_17: 
    forall (A B C D E F : Type -> Prop),
      (forall x, A x -> ((forall y, B y) -> C x)) ->
      (forall x, C x -> ((forall y, D y) -> E x)) ->
      ((forall x, B x /\ F x) -> ((forall y, F y -> D y) -> (forall z, A z -> E z))).
  Proof.
    intros A B C D E F H1 H2 H3 H4 z H5.
    apply H2.
    apply H1.
    exact H5.
    intro y.
    specialize (H3 y).
    destruct H3 as [H31 H32].
    exact H31.
    
    intro y.
    apply H4.
    apply H3.
  Qed.
  
  Theorem Page_104_I_18: 
    forall (G H : Type -> Prop),
      (forall x, exists y, G x /\ H y) ->
      ((forall x, G x) /\ (exists y, H y)).
  Proof.
    intros G H H1.
    split.
    intro x.
    specialize (H1 x).
    destruct H1 as [y [H1 H2]].
    exact H1.
    specialize (H1 Set).
    destruct H1 as [y [_ H1]].
    exists y.
    exact H1.
  Qed.
    
  Theorem Page_104_I_19: 
    forall (I J : Type -> Prop),
      (exists x, forall y, I x <-> J y) ->
      (forall y, exists x, I x <-> J y).
  Proof.
    intros I J H1 y.
    destruct H1 as [x H1].
    exists x.
    apply H1.
  Qed.
  
  Theorem Page_104_I_20: 
    forall (K L : nat -> Prop),
      (forall x, exists y, K x /\ L y) ->
      (exists y, forall x, K x /\ L y).
  Proof.
    intros K L H1.
    destruct (PNP (exists y, L y)) as [H21 | H22].
    destruct H21 as [y H2].
    exists y.
    intro x.
    split.
    specialize (H1 x).
    destruct H1 as [z [H11 H12]].
    exact H11.
    exact H2.
    rewrite -> not_exists in H22.
    assert(y : nat).
    constructor.
    exists y.
    intro x.
    split.
    specialize (H1 x).  
    destruct H1 as [z [H11 _]].
    exact H11.
    specialize (H1 x).
    destruct H1 as [z [_ H1]].
    specialize (H22 z).
    apply H22 in H1.
    contradict H1.
  Qed.
  
  Theorem Page_104_I_20' {T : Type}: 
    forall (K : T -> Prop) (L : T -> Prop),
      (forall x, exists y, K x /\ L y) ->
      (exists y, forall x, K x /\ L y).
  Proof.
    intros K L H1.
    (* seems bloody false to me! *)
    admit.
  Qed.
End Copi.