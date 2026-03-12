Require Import Arith.
Require Import List.
Import ListNotations.

Definition reflexive {A: Type} (r: A -> A -> Prop) : Prop := forall x: A, r x x.

Definition symmetric {A: Type} (r: A -> A -> Prop) : Prop := forall x y: A, r x y -> r y x.

Definition transitive {A: Type} (r: A -> A -> Prop) : Prop := forall x y z: A, r x y -> r y z -> r x z.

Definition preorder {A: Type} (r: A -> A -> Prop): Prop := reflexive r /\ transitive r.

Definition equivalence_relation {A: Type} (r: A -> A -> Prop) : Prop := reflexive r /\ symmetric r /\ transitive r.

Definition bidirection {A: Type} (r: A -> A -> Prop): A -> A -> Prop := fun x y: A => r x y /\ r y x.

Theorem preorder_induce_eq_rel: forall A: Type, forall r: A -> A -> Prop, preorder r -> equivalence_relation(bidirection r).
Proof.
  unfold preorder. unfold equivalence_relation. unfold bidirection. unfold reflexive. unfold symmetric. unfold transitive.
  intros. destruct H. split.
  - intros. split.
    -- apply (H x).
    -- apply (H x).
  - split.
    -- intros. destruct H1. split.
      --- apply H2.
      --- apply H1.
    -- intros. destruct H1. destruct H2. split.
      --- specialize (H0 x y z). apply H0 in H1.
        ---- apply H1.
        ---- apply H2.
      --- specialize (H0 z y x). apply H0 in H4.
        ---- apply H4.
        ---- apply H3.
Qed.

Record system: Type := {
  state: Type;
  step: state -> state}.
  
Fixpoint repeat {X: Type} (f: X -> X) (n: nat) (x: X) :=
  match n with
  | 0 => x
  | S n' => f(repeat f n' x)
  end.
  
Definition image_invertible {A B: Type} (f: A -> B) (P: A -> Prop) := exists g: B -> A, (forall x: A, P x -> g(f x) = x) /\ (forall y: B, P(g y) /\ f(g y) = y).

Definition closed {X: Type} (P: X -> Prop) (f: X -> X): Prop := forall x: X, P x -> P(f x).

Record simulation (S1 S2: system): Type := {
  P: state S1 -> Prop;
  h: state S1 -> state S2;
  i: state S1 -> nat;
  closed_enc: closed P (fun x: state S1 => repeat (step S1) (i x) x);
  invertible_enc: image_invertible h P;
  step_correspond: forall x: state S1, P x -> h(repeat (step S1) (i x) x) = (step S2) (h x)}.
  
Definition can_simulate (S1 S2: system): Prop := exists I: simulation S1 S2, True.

Notation "x --> y" := (can_simulate x y) (at level 50, left associativity).

Definition mutual_simulate: system -> system -> Prop := bidirection can_simulate.

Notation "x <--> y" := (mutual_simulate x y) (at level 50, left associativity).

Theorem can_simulate_refl: reflexive can_simulate.
Proof.
  unfold reflexive. intros S. unfold can_simulate.
  eexists.
  refine ({| 
  P := fun x: state S => True; 
  h := fun x: state S => x; 
  i := fun x: state S => 1; 
  closed_enc := _; 
  invertible_enc := _; 
  step_correspond := _ |}).
  - unfold closed. intros. exact I.
  - unfold image_invertible. exists (fun x: state S => x). split.
    -- intros. reflexivity.
    -- intros. split.
      --- exact I.
      --- reflexivity. 
  - intros. simpl. reflexivity.
  - exact I.
Qed.

Theorem contrapositive: forall P Q: Prop, (P -> Q) -> (~ Q -> ~ P).
Proof.
  unfold not. intros.
  apply H in H1. apply H0 in H1. apply H1.
Qed.

Fixpoint sum (f: nat -> nat) (n: nat) :=
  match n with
  | 0 => 0
  | S n' => f n' + sum f n'
  end.
  
Theorem sum_add_distr: forall f g: nat -> nat, forall n: nat, sum (fun x: nat => f x + g x) n = sum f n + sum g n.
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. ring.
Qed.

Theorem sum_constant_mul_comm: forall f: nat -> nat, forall c n: nat, sum(fun x: nat => c * (f x)) n = c * (sum f n).
Proof.
  intros. induction n.
  - simpl. rewrite Nat.mul_0_r. reflexivity.
  - simpl. rewrite IHn. ring.
Qed.

Theorem repeat_add: forall A: Type, forall f: A -> A, forall n m: nat, forall x: A, repeat f (n + m) x = repeat f n (repeat f m x).
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem repeat_fun_closed: forall A: Type, forall P: A -> Prop, forall f: A -> A, forall i: A -> nat, closed P f -> closed P (fun x: A => repeat f (i x) x).
Proof.
  unfold closed. intros. induction (i0 x).
  - simpl. apply H0.
  - simpl. apply H in IHn. apply IHn.
Qed.

Theorem nested_eq_sum_repeat_fun: forall A: Type, forall f: A -> A, forall i: A -> nat, 
  forall n: nat, forall x: A,
  
  let F := fun x: A => repeat f (i x) x in
  let R := repeat F in
  let R' := fun x: A => repeat f (sum (fun t: nat => i(R t x)) n) x in
  
  R n x = R' x.
Proof.
  intros. induction n.
  - unfold R. unfold R'. simpl. reflexivity.
  - unfold R. unfold R'. simpl. rewrite repeat_add. unfold R.
    unfold R in IHn. unfold R' in IHn. rewrite IHn.
    unfold F. reflexivity.
Qed.

Theorem two_image_invertible: forall A B C: Type, forall P1: A -> Prop, forall P2: B -> Prop, forall f: A -> B, forall g: B -> C,
  image_invertible f P1 -> image_invertible g P2 -> image_invertible (fun x: A => g(f x)) (fun x: A => P1 x /\ P2(f x)).
Proof.
  unfold image_invertible. intros.
  destruct H as [f_inv H]. destruct H0 as [g_inv H0]. destruct H. destruct H0.
  exists (fun x: C => f_inv(g_inv x)). split.
  - intros. destruct H3. 
    specialize (H0 (f x)). apply H0 in H4. rewrite H4.
    specialize (H x). apply H in H3. rewrite H3. reflexivity.
  - intros. repeat split.
    -- specialize (H1 (g_inv y)). destruct H1. apply H1.
    -- specialize (H1 (g_inv y)). destruct H1. rewrite H3.
       specialize (H2 y). destruct H2. apply H2.
    -- specialize (H1 (g_inv y)). destruct H1. rewrite H3.
       specialize (H2 y). destruct H2. apply H4.
Qed.

Lemma _big_closed: forall S1 S2: system, forall I: simulation S1 S2, forall n: nat,
  let P := P _ _ I in
  let i := i _ _ I in
  
  let F := fun x: state S1 => repeat (step S1) (i x) x in
  let R := repeat F in
  
  closed P (R n).
Proof.
  intros. destruct I. unfold closed. intros.
  assert (i1 = i0). reflexivity.
  induction n.
  - unfold R. simpl. apply H.
  - unfold R. simpl. fold R. apply closed_enc0 in IHn. unfold F.
    rewrite <- H0. apply IHn.
Qed.

Lemma push_h: forall S1 S2: system, forall I: simulation S1 S2, forall n: nat, forall x: state S1,
  let P := P _ _ I in
  let h := h _ _ I in
  let i := i _ _ I in
  
  let F := fun x: state S1 => repeat (step S1) (i x) x in
  let R := repeat F in
  
  P x -> h(R n x) = repeat (step S2) n (h x).
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - unfold R. simpl. fold R. rewrite <- IHn.
    pose proof _big_closed. specialize (H0 _ _ I n). simpl in H.
    destruct I. apply step_correspond0.
    apply H0. fold P0. apply H.
Qed.

Theorem can_simulate_trans: transitive can_simulate.
Proof.
  unfold transitive. unfold can_simulate. intros S1 S2 S3. intros.
  destruct H. destruct H0.
  remember x. remember x0. destruct x. destruct x0.
  
  pose proof nested_eq_sum_repeat_fun as useful_equality. 
  pose proof _big_closed as big_closed.
  pose proof push_h as push_h.
  
  set (F := fun x: state S1 => repeat (step S1) (i0 x) x).
  set (G := fun x: state S2 => repeat (step S2) (i1 x) x).
  set (R := repeat F).
  eexists.
  refine ({|
  P := fun x: state S1 => P0 x /\ P1(h0 x);
  h := fun x: state S1 => h1(h0 x);
  i := fun x: state S1 => sum(fun t: nat => i0(R t x)) (i1(h0 x));
  closed_enc := _;
  invertible_enc := _;
  step_correspond := _ |}).
  
  assert (P S1 S2 s = P0) as P0_change. rewrite Heqs. reflexivity.
  assert (h S1 S2 s = h0) as h0_change. rewrite Heqs. reflexivity.
  assert (i S1 S2 s = i0) as i0_change. rewrite Heqs. reflexivity.
  
  - unfold closed. intros. destruct H1.
  
    specialize (useful_equality _ (step S1) i0 (i1(h0 x)) x). simpl in useful_equality. 
    fold F in useful_equality. fold R in useful_equality.
    rewrite <- useful_equality.
    
    split.
    -- specialize (big_closed _ _ s (i1(h0 x))). simpl in big_closed.
       rewrite P0_change in big_closed. rewrite i0_change in big_closed. fold F in big_closed. fold R in big_closed.
       
       apply big_closed. apply H1.
    
    -- specialize (push_h _ _ s (i1(h0 x)) x). simpl in push_h.
       rewrite P0_change in push_h. rewrite h0_change in push_h. rewrite i0_change in push_h.
       fold F in push_h. fold R in push_h.
       
       apply push_h in H1. rewrite H1. apply closed_enc1. apply H2.

  - apply two_image_invertible.
    -- apply invertible_enc0.
    -- apply invertible_enc1.
  
  - intros. destruct H1. pose proof push_h as push_h1.
    
    assert (P S1 S2 s = P0) as P0_change. rewrite Heqs. reflexivity.
    assert (h S1 S2 s = h0) as h0_change. rewrite Heqs. reflexivity.
    assert (i S1 S2 s = i0) as i0_change. rewrite Heqs. reflexivity.
    
    specialize (useful_equality _ (step S1) i0 (i1(h0 x)) x). simpl in useful_equality. 
    fold F in useful_equality. fold R in useful_equality.
    rewrite <- useful_equality.
    
    specialize (push_h _ _ s (i1(h0 x)) x). simpl in push_h.
    rewrite P0_change in push_h. rewrite h0_change in push_h. rewrite i0_change in push_h.
    fold F in push_h. fold R in push_h.
    
    rewrite push_h. apply step_correspond1.
    -- apply H2.
    -- apply H1.
   
  - apply I. 
Qed.

Theorem can_simulate_preorder: preorder can_simulate.
Proof.
  unfold preorder. split.
  - exact can_simulate_refl.
  - exact can_simulate_trans.
Qed.

Theorem mutual_simulate_eq_rel: equivalence_relation mutual_simulate.
Proof.
  apply preorder_induce_eq_rel. exact can_simulate_preorder.
Qed.

Record implementation {Q A: Type} (S: system) (f: Q -> A): Type := {
  P1: state S -> Prop;
  P2: state S -> Prop;
  h1: state S -> Q;
  h2: state S -> A;
  s: state S -> nat;
  invertible_enc1: image_invertible h1 P1;
  invertible_enc2: image_invertible h2 P2;
  correct: forall x: state S, P1 x -> h2(repeat (step S) (s x) x) = f(h1 x)}.

Definition can_solve {Q A: Type} (S: system) (f: Q -> A): Prop := exists imp: implementation S f, True.

Notation "x ! y" := (can_solve x y) (at level 50, left associativity).

Theorem simulation_shares_implementation: 
  forall S1 S2: system, S1 --> S2 -> forall Q A: Type, forall f: Q -> A, S2 ! f -> S1 ! f.
Proof.
  unfold can_solve. intros.
  destruct H as [H t]. clear t. destruct H0 as [H0 t]. clear t. remember H as s.
  destruct H. destruct H0.
  
  set (F := fun x: state S1 => repeat (step S1) (i0 x) x).
  set (G := fun x: state S2 => repeat (step S2) (s0 x) x).
  set (R := repeat F).
  eexists.
  refine ({|
  P1 := fun x: state S1 => P0 x /\ P3(h0 x);
  P2 := fun x: state S1 => P0 x /\ P4(h0 x);
  h1 := fun x: state S1 => h3(h0 x);
  h2 := fun x: state S1 => h4(h0 x);
  s := fun x: state S1 => sum(fun t: nat => i0(R t x)) (s0(h0 x));
  invertible_enc1 := _;
  invertible_enc2 := _;
  correct := _ |}).
  
  - apply two_image_invertible.
    -- pose proof invertible_enc0. apply H.
    -- apply invertible_enc3.
  
  - unfold image_invertible.
    destruct invertible_enc0 as [h0_inv IE0]. destruct IE0. destruct invertible_enc4 as [h4_inv IE4]. destruct IE4.
    exists (fun x: A => h0_inv(h4_inv x)). split.
    -- intros. destruct H1. specialize (H(h0 x)). apply H in H2.
       rewrite H2. pose proof e. specialize (H3 x). apply H3 in H1. rewrite H1. reflexivity.
    -- intros. repeat split.
      --- pose proof a. specialize (H1(h4_inv y)). destruct H1. apply H1.
      --- pose proof e. pose proof a.
          specialize (H2(h4_inv y)). destruct H2. rewrite H3.
          specialize (H0 y). destruct H0. apply H0.
      --- pose proof e. pose proof a.
          specialize (H2(h4_inv y)). destruct H2. rewrite H3.
          specialize (H0 y). destruct H0. apply H4.
  
  - intros. destruct H.
    pose proof nested_eq_sum_repeat_fun as useful_equality. 
    specialize (useful_equality (state S1) (step S1) i0 (s0(h0 x)) x).
    simpl in useful_equality. fold F in useful_equality. fold R in useful_equality.
    rewrite <- useful_equality.
    
    assert (P S1 S2 s = P0) as P0_change. rewrite Heqs. reflexivity.
    assert (h S1 S2 s = h0) as h0_change. rewrite Heqs. reflexivity.
    assert (i S1 S2 s = i0) as i0_change. rewrite Heqs. reflexivity.
    
    pose proof push_h as push_h. specialize (push_h S1 S2 s (s0(h0 x)) x).
    simpl in push_h. rewrite P0_change in push_h. rewrite h0_change in push_h. rewrite i0_change in push_h.
    fold F in push_h. fold R in push_h.
    
    rewrite push_h. specialize (correct0 (h0 x)). rewrite correct0. reflexivity.
    -- apply H0.
    -- apply H.
    
  - apply I.
Qed.

Definition has_property {S: system} (x: state S) (P: state S -> Prop): Prop :=
  exists x': state S, (exists n: nat, x' = repeat (step S) n x) /\ P x'.
  
Definition nontrivial_property {S: system} (P: state S -> Prop): Prop :=
  (exists t_eg: state S, has_property t_eg P) /\ (exists f_eg: state S, ~ has_property f_eg P).

Definition specific_eq {S: system} (x: state S): state S -> Prop := fun y => y = x.

Notation "'s=' x" := (specific_eq x) (at level 50, left associativity).

Definition reduces_to {S: system} (x y: state S): Prop := exists n: nat, y = repeat (step S) n x.

Notation "x 'R->' y" := (reduces_to x y) (at level 50, left associativity).

Theorem reduces_to_shares_has_property:
  forall S: system, forall P: state S -> Prop, forall x y: state S,
  x R-> y -> has_property y P -> has_property x P.
Proof.
  unfold has_property. unfold reduces_to. intros.
  destruct H as [n H].
  destruct H0 as [x' H0]. destruct H0. destruct H0 as [m H0].
  exists x'. split.
  - exists (m + n). rewrite repeat_add. rewrite <- H. rewrite <- H0. reflexivity.
  - apply H1.
Qed.

Theorem has_property_of_reduces_to: forall S: system, forall x y: state S, x R-> y <-> has_property x (s= y).
Proof.
  intros. split.
  - intros. unfold reduces_to in H. unfold has_property. destruct H as [n H].
    exists y. split.
    -- exists n. apply H.
    -- unfold specific_eq. reflexivity.
  - intros. unfold has_property in H. unfold reduces_to. destruct H as [x' H]. destruct H. destruct H as [n H].
    unfold specific_eq in H0. rewrite H0 in H.
    exists n. apply H.
Qed.

Record diagonalizable := {
  d_S: system;
  d_true: state d_S;
  d_false: state d_S;
  d_tf_distinct: d_true <> d_false;
  d_C: state d_S -> state d_S -> state d_S -> state d_S;
  d_C_correct_T: 
    forall x y z: state d_S, x R-> d_true -> (d_C x y z) R-> y;
  d_C_correct_F:
    forall x y z: state d_S, x R-> d_false -> (d_C x y z ) R-> z;
  d_o1: state d_S -> state d_S -> state d_S;
  d_o2: state d_S -> state d_S -> state d_S;
  D_enc: state d_S -> state d_S -> state d_S -> state d_S -> state d_S;
  D': state d_S;
  D := fun f a b x: state d_S => d_C (d_o2 f (d_o1 x x)) a b;
  D'_correct: forall f a b x: state d_S, (d_o1 (D_enc D' f a b) x) = D f a b x}.

Definition d_decider {S: diagonalizable} (f: state (d_S S)) (P: state (d_S S) -> Prop): Prop :=
  forall x: state (d_S S), 
  ((d_o2 S) f x R-> d_true S -> has_property x P) /\
  ((d_o2 S) f x R-> d_false S -> ~ has_property x P) /\
  ((d_o2 S) f x R-> d_true S \/ (d_o2 S) f x R-> d_false S).
  
Theorem reduces_to_refl: forall S: system, reflexive(@reduces_to S).
Proof.
  unfold reflexive. intros. unfold reduces_to. exists 0. simpl. reflexivity.
Qed.

Theorem reduces_to_trans: forall S: system, transitive(@reduces_to S).
Proof.
  unfold transitive. unfold reduces_to. intros.
  destruct H as [n H]. destruct H0 as [m H0].
  exists (m + n).
  rewrite repeat_add. rewrite <- H. apply H0.
Qed.

Theorem reduces_to_preorder: forall S: system, preorder (@reduces_to S).
Proof.
  unfold preorder. intros. split.
  - apply reduces_to_refl.
  - apply reduces_to_trans.
Qed.

Definition fixed_point {A: Type} (f: A -> A) (x: A): Prop := x = f x.

Definition sys_fixed_point (S: system) (x: state S) := fixed_point (step S) x.

Theorem reduces_to_shares_fixed_point:
  forall S: system, forall x y: state S,
  x R-> y -> has_property y (sys_fixed_point S) -> has_property x (sys_fixed_point S).
Proof.
  intros. pose proof reduces_to_shares_has_property.
  specialize (H1 S (sys_fixed_point S) x y). apply H1 in H.
  - apply H.
  - apply H0.
Qed.

Theorem repeat_comm: forall X: Type, forall f: X -> X, forall n m: nat, forall x: X, repeat f n (repeat f m x) = repeat f m (repeat f n x).
Proof.
  intros. rewrite <- repeat_add. rewrite Nat.add_comm. rewrite repeat_add. reflexivity.
Qed.

Theorem repeat_comm_single: forall X: Type, forall f: X -> X, forall n: nat, forall x: X, f(repeat f n x) = repeat f n (f x).
Proof.
  intros. replace f with (repeat f 1).
  - rewrite repeat_comm. simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem fixed_point_stops: forall X: Type, forall f: X -> X, forall x: X, fixed_point f x -> forall n: nat, repeat f n x = x.
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - simpl. rewrite repeat_comm_single. rewrite <- H. apply IHn.
Qed.

Theorem fixed_point_reduces_to: forall S: system, forall x: state S, fixed_point (step S) x -> forall y: state S, x R-> y -> x = y.
Proof.
  intros. unfold reduces_to in H0. destruct H0 as [n H0].
  rewrite H0. rewrite fixed_point_stops.
  - reflexivity.
  - apply H.
Qed.

Theorem system_confluence: forall S: system, forall x y z: state S, x R-> y -> x R-> z -> (exists a: state S, y R-> a /\ z R-> a).
Proof.
  unfold reduces_to. intros.
  destruct H as [n H]. destruct H0 as [m H0].
  destruct (n <=? m) eqn:E.
  - apply Nat.leb_le in E.
    exists z. split.
    -- exists (m - n). rewrite H. rewrite <- repeat_add. rewrite Nat.sub_add.
      --- apply H0.
      --- apply E.
    -- exists 0. simpl. reflexivity.
  - apply Nat.leb_gt in E. apply Nat.lt_le_incl in E.
    exists y. split.
    -- exists 0. simpl. reflexivity.
    -- exists (n - m). rewrite H0. rewrite <- repeat_add. rewrite Nat.sub_add.
      --- apply H.
      --- apply E.
Qed.

Theorem reduces_to_shares_not_fixed_point:
  forall S: system, forall x y: state S,
  x R-> y -> ~ has_property y (sys_fixed_point S) -> 
  ~ has_property x (sys_fixed_point S).
Proof.
  intros. unfold not. intros.
  unfold has_property in H1. destruct H1 as [x' [[m H1] H2]].
  assert (x R-> x').
  - unfold reduces_to. exists m. apply H1.
  - pose proof system_confluence. specialize (H4 S x y x'). specialize (H4 H H3).
    destruct H4 as [a H4]. destruct H4. apply fixed_point_reduces_to in H5 as H6.
    -- assert (a R-> x').
      --- rewrite H6. apply reduces_to_refl.
      --- pose proof reduces_to_trans. unfold transitive in H8. specialize (H8 S y a x' H4 H7).
          assert (has_property y (sys_fixed_point S)).
          ---- unfold has_property. exists x'. split.
            ----- unfold reduces_to in H8. destruct H8 as [n H8]. exists n. apply H8.
            ----- apply H2.
          ---- apply H0 in H9. destruct H9.
    -- unfold sys_fixed_point in H2. apply H2.
Qed.

Theorem turing:
  forall S: diagonalizable,
  nontrivial_property(sys_fixed_point (d_S S)) ->
  ~ exists f: state (d_S S), d_decider f(sys_fixed_point (d_S S)).
Proof.
  unfold not. intros.
  unfold nontrivial_property in H. destruct H as [[t_eg H1] [f_eg H2]].
  destruct H0 as [f H0].
  
  set (diagonal := D_enc S (D' S) f f_eg t_eg).
  set (witness := d_o1 S diagonal diagonal).
  
  unfold d_decider in H0. specialize (H0 witness).
  destruct H0 as [H0 [H3 H4]].
  
  pose proof (D'_correct S) as diag_correct.
  
  destruct H4.
  
  - pose proof (d_C_correct_T S) as cond_correct_T. pose proof H. apply H0 in H.
  
    assert (witness R-> f_eg).
    
    -- unfold witness. unfold diagonal. rewrite diag_correct.
       unfold D. fold diagonal. fold witness. apply cond_correct_T. apply H4.
    -- pose proof reduces_to_shares_not_fixed_point.
       specialize (H6 (d_S S) witness f_eg). apply H6 in H5.
       --- apply H5 in H. destruct H.
       --- apply H2.
  
  - pose proof (d_C_correct_F S) as cond_correct_F. pose proof H. apply H3 in H.
  
    assert (witness R-> t_eg).
    
    -- unfold witness. unfold diagonal. rewrite diag_correct.
       unfold D. fold diagonal. fold witness. apply cond_correct_F. apply H4.
    -- pose proof reduces_to_shares_fixed_point.
       specialize (H6 (d_S S) witness t_eg). apply H6 in H5.
       --- apply H in H5. destruct H5.
       --- apply H1.
Qed.

Record rice_extendable: Type := {
  r_S: system;
  r_true: state r_S;
  r_false: state r_S;
  r_tf_distinct: r_true <> r_false;
  r_C: state r_S -> state r_S -> state r_S -> state r_S;
  r_C_correct_T: 
    forall x y z: state r_S, x R-> r_true -> (r_C x y z) R-> y;
  r_C_correct_F: 
    forall x y z: state r_S, x R-> r_false -> (r_C x y z) R-> z;
  r_o2: state r_S -> state r_S -> state r_S;
  r_H_semi: state r_S;
  r_H_semi_correct:
    forall x: state r_S, 
    (r_o2 r_H_semi x R-> r_true <-> sys_fixed_point r_S x)}.

Definition r_decider {S: rice_extendable}
  (f: state (r_S S)) (P: state (r_S S) -> Prop): Prop :=
  forall x: state (r_S S),
  ((r_o2 S) f x R-> r_true S -> has_property x P) /\
  ((r_o2 S) f x R-> r_false S -> ~ has_property x P) /\
  ((r_o2 S) f x R-> r_true S \/ (r_o2 S) f x R-> r_false S).

Theorem rice: forall S: rice_extendable,
  forall P: state(r_S S) -> Prop, nontrivial_property P ->
  ~ exists f: state(r_S S), r_decider f P.
Proof.
  unfold not. intros.
  unfold nontrivial_property in H. destruct H as [[t_eg H1] [f_eg H2]].
  destruct H0 as [f H0].
Abort.
