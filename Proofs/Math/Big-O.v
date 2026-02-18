Require Import Arith.

Definition reflexive {A: Type} (r: A -> A -> Prop) : Prop := forall x: A, r x x.

Definition symmetric {A: Type} (r: A -> A -> Prop) : Prop := forall x y: A, r x y -> r y x.

Definition transitive {A: Type} (r: A -> A -> Prop) : Prop := forall x y z: A, r x y -> r y z -> r x z.

Definition preorder {A: Type} (r: A -> A -> Prop): Prop := reflexive r /\ transitive r.

Definition big_o (f g: nat -> nat): Prop := exists n M: nat, forall x: nat, x >= n -> f x <= M * (g x).

Notation "x << y" := (big_o x y) (at level 50, left associativity).

Theorem big_o_refl: reflexive big_o.
Proof.
  unfold reflexive. intros f. unfold big_o.
  exists 0. exists 1. intros. simpl. rewrite Nat.add_0_r.
  exact (le_n (f x)).
Qed.

Theorem max_correct: forall n m: nat, max n m >= n /\ max n m >= m.
Proof. Admitted.

Theorem geq_trans: forall a b c: nat, a >= b -> b >= c -> a >= c.
Proof. Admitted.

Theorem leq_trans: forall a b c: nat, a <= b -> b <= c -> a <= c.
Proof. Admitted.

Theorem mul_leq: forall n m c: nat, n <= m -> n <= c * m.
Proof. Admitted.

Theorem mul_both_leq: forall n m c: nat, n <= m -> c * n <= c * m.
Proof. Admitted.

Theorem big_o_trans: transitive big_o.
Proof.
  unfold transitive. intros f g h. unfold big_o.
  intros. destruct H as [n H]. destruct H as [M H]. destruct H0 as [n0 H0]. destruct H0 as [M0 H0].
  exists (max n n0). exists (M * M0). intros.
  specialize (H x). specialize (H0 x).
  pose proof max_correct. specialize (H2 n n0). destruct H2.
  pose proof geq_trans. pose proof geq_trans.
  specialize (H4 x (Init.Nat.max n n0) n). specialize (H5 x (Init.Nat.max n n0) n0).
  pose proof H1.
  apply H4 in H1.
  apply H5 in H6.
  apply H in H1. apply H0 in H6.
  pose proof mul_both_leq. specialize (H7 (g x) (M0 * h x) M). apply H7 in H6.
  pose proof leq_trans. specialize (H8 (f x) (M * g x) (M * (M0 * h x))). apply H8 in H1.
  - rewrite Nat.mul_assoc in H1. apply H1.
  - apply H6.
  - apply H3.
  - apply H2.
Qed.

Theorem big_o_preorder: preorder big_o.
Proof.
  unfold preorder. split.
  - apply big_o_refl.
  - apply big_o_trans.
Qed.