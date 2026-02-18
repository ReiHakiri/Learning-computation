Definition reflexive {A: Type} (r: A -> A -> Prop) : Prop := forall x: A, r x x.

Definition symmetric {A: Type} (r: A -> A -> Prop) : Prop := forall x y: A, r x y -> r y x.

Definition transitive {A: Type} (r: A -> A -> Prop) : Prop := forall x y z: A, r x y -> r y z -> r x z.

Definition equivalence_relation {A: Type} (r: A -> A -> Prop) : Prop := reflexive r /\ symmetric r /\ transitive r.

Definition left_total {A B: Type} (r: A -> B -> Prop) : Prop := forall x: A, exists y: B, r x y.

Definition functional {A B: Type} (r: A -> B -> Prop) : Prop := forall x: A, forall y z: B, r x y -> r x z -> y = z.

Definition is_function {A B: Type} (r: A -> B -> Prop) := left_total r /\ functional r.

Definition injective {A B: Type} (f: A -> B) : Prop := forall x y: A, f x = f y -> x = y.

Definition surjective {A B: Type} (f: A -> B) : Prop := forall y: B, exists x: A, y = f x.

Definition bijective {A B: Type} (f: A -> B) : Prop := injective f /\ surjective f.

Definition fun_eq {A B: Type} (f: A -> B) (g: A -> B) : Prop := forall x: A, f x = g x.

Notation "x -- y" := (fun_eq x y) (at level 50, left associativity).

Theorem eq_to_fun_eq: forall A B: Type, forall f g: A -> B, f = g -> f -- g.
Proof.
  unfold fun_eq. intros.
  rewrite H. reflexivity.
Qed.

Theorem fun_eq_refl: forall A B: Type, forall f: A -> B, f -- f.
Proof.
  intros. unfold fun_eq. intros. reflexivity.
Qed.

Theorem fun_eq_sym: forall A B: Type, forall f g: A -> B, f -- g -> g -- f.
Proof.
  unfold fun_eq. intros.
  specialize (H x).
  rewrite H. reflexivity.
Qed.

Theorem fun_eq_trans: forall A B: Type, forall f g h: A -> B, f -- g -> g -- h -> f -- h.
Proof.
  unfold fun_eq. intros.
  specialize (H x). specialize (H0 x).
  rewrite H0 in H. assumption.
Qed.

Definition id {A: Type} (x: A) := x.

Definition composition {A B: Type} {C: Type} (f: B -> C) (g: A -> B) := fun x: A => f(g x).

Notation "x ' y" := (composition x y) (at level 60, right associativity).

Theorem fun_eq_left_comp: forall A B C: Type, forall f g: A -> B, forall h: B -> C, f -- g -> (h ' f) -- (h ' g).
Proof.
  unfold fun_eq. unfold composition.
  intros.
  rewrite H. reflexivity.
Qed.

Theorem fun_eq_right_comp: forall A B C: Type, forall f g: B -> C, forall h: A -> B, f -- g -> (f ' h) -- (g ' h).
Proof.
  unfold fun_eq. unfold composition.
  intros.
  rewrite H. reflexivity.
Qed.

Theorem composition_associative: forall A B C D: Type, forall x: C -> D, forall y: B -> C, forall z: A -> B, (x ' y) ' z = x ' (y ' z).
Proof.
  unfold composition.
  reflexivity.
Qed.

Definition is_inv {A B: Type} (f: A -> B) (inv: B -> A) : Prop := (f ' inv) -- id /\ id -- (inv ' f).

Definition invertible {A B: Type} (f: A -> B) : Prop := exists g: B -> A, is_inv f g.

Theorem inv_imply_bij: forall A B: Type, forall f: A -> B, invertible f -> bijective f. (* Converse does not hold in constructive logic *)
Proof.
  cbv.
  intros A B f H. destruct H as [g H]. destruct H.
  split.
    - intros.
      assert (g(f x) = g(f y)).
        -- f_equal. assumption.
        -- repeat rewrite <- H0 in H2. assumption.
    - intros. exists (g y). rewrite H. reflexivity.
Qed.

Theorem unique_inv: forall A B: Type, forall f: A -> B, forall g: B -> A, forall h: B -> A, is_inv f g -> is_inv f h -> g -- h.
Proof.
  unfold is_inv. unfold id. unfold composition. unfold fun_eq.
  intros. destruct H. destruct H0. f_equal.
Qed.

Theorem conjugation: forall A B: Type, forall h: A -> B, invertible h -> forall f: A -> A, exists inv_h: B -> A, is_inv h inv_h /\ exists g: B -> B, f -- (inv_h ' g ' h).
Proof.
  intros. unfold invertible in H. destruct H as [g H].
  exists g. split.
  - assumption.
  - exists (h ' f ' g).
    cbv. unfold is_inv in H. unfold composition in H. unfold fun_eq in H. unfold id in H. destruct H.
    intros x.
    repeat rewrite <- H0. reflexivity.
Qed.

Definition notb (b: bool): bool :=
  match b with
  | true => false
  | false => true
  end.

Theorem cantor: forall A: Type, ~ exists f: A -> A -> bool, surjective f.
Proof.
  intros. unfold not.
  intros. destruct H as [f H]. unfold surjective in H.
  set (g := fun x: A => notb(f x x)).
  assert (~ exists x: A, f x = g).
  unfold not. intros. destruct H0.
  assert (f x x <> g x). unfold not.
  unfold g. intros.
  destruct (f x x) in H1.
  simpl in H1. discriminate.
  simpl in H1. discriminate.
  assert (f x x = g x). rewrite H0. reflexivity.
  congruence.
  specialize (H g).
  destruct H.
  assert (exists x: A, f x = g).
  exists x. rewrite H. reflexivity.
  congruence.
Qed.

Definition isomorphic (A B: Type) := exists f: A -> B, invertible f.