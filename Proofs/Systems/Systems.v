Require Import Arith.

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

Inductive lambda_term: Type :=
  | x: nat -> lambda_term
  | composition: lambda_term -> lambda_term -> lambda_term
  | lambda: nat -> lambda_term -> lambda_term.

Notation "x 'o' y" := (composition x y) (at level 50, left associativity).

Inductive reduce_marked: Type :=
  | oc: reduce_marked -> reduce_marked -> reduce_marked
  | lambdac: nat -> reduce_marked -> reduce_marked
  | R: lambda_term -> reduce_marked.
  
Notation "x 'oc' y" := (oc x y) (at level 50, left associativity).
  
Fixpoint substitute (l1: lambda_term) (n: nat) (l2: lambda_term): lambda_term :=
  match l1 with
  | x m => if m =? n then l2 else x m
  | l' o l'' => (substitute l' n l2) o (substitute l'' n l2)
  | lambda m l' => lambda m (substitute l' n l2)
  end.
  
Fixpoint var_free (l: lambda_term) (n: nat) :=
  match l with
  | x m => m =? n
  | l' o l'' => orb (var_free l' n) (var_free l'' n)
  | lambda m l' => if m =? n then false else var_free l' n
  end.
  
Fixpoint substitutable (l1: lambda_term) (l2: lambda_term): bool :=
  match l1 with
  | lambda m l' => negb(var_free l2 m)
  | l' o l'' => andb (substitutable l' l2) (substitutable l'' l2)
  | _ => true
  end.

Definition beta_reduction (l: lambda_term): lambda_term :=
  match l with
  | (lambda n l') o l'' => if substitutable l' l'' then substitute l' n l'' else l
  | l => l
  end.

Fixpoint R_remover (r: reduce_marked): lambda_term :=
  match r with
  | R l => l
  | r' oc r'' => (R_remover r') o (R_remover r'')
  | lambdac n r' => lambda n (R_remover r')
  end.
  
Fixpoint normal_step (r: reduce_marked): reduce_marked :=
  match r with
  | R((lambda n l') o l'') => R(beta_reduction((lambda n l') o l''))
  | R(l' o l'') => (R l') oc (R l'')
  | R(lambda n l') => lambdac n (R l')
  | (lambdac n r') oc r'' => R(beta_reduction((lambda n (R_remover r')) o (R_remover r'')))
  | r' oc r'' => (normal_step r') oc r''
  | lambdac n r' => lambdac n (normal_step r')
  | r => r
  end.
  
Definition reduce_step (r: reduce_marked): reduce_marked := normal_step(normal_step r).

Definition lambda_calculus: system := {| state := reduce_marked; step := reduce_step |}.

Definition lc_true: reduce_marked := R(lambda 1 (lambda 0 (x 1))).

Definition lc_false: reduce_marked := R(lambda 1 (lambda 0 (x 0))).

Definition if_then_else: reduce_marked := R(lambda 2(lambda 1(lambda 0((x 2) o (x 1) o (x 0))))).

Definition halts (l: reduce_marked): Prop := exists n: nat, exists l': reduce_marked, l' = repeat reduce_step n l /\ l' = reduce_step l'.

Definition continue: reduce_marked := R((lambda 0 ((x 0) o (x 0) o (x 0))) o (lambda 0 ((x 0) o (x 0) o (x 0)))).

Definition halt: reduce_marked := R(x 0).

Fixpoint gt (x y: nat): bool :=
  match x, y with
  | S x', 0 => true
  | S x', S y' => gt x' y'
  | _, _ => false
  end.
  
Notation "x >? y" := (gt x y) (at level 50, left associativity).

Theorem continue_grows: 
  forall n: nat, n >? 1 = true -> repeat reduce_step (S(S(S n))) continue = 
  (repeat reduce_step n ((reduce_step continue) oc (R(lambda 0(x 0 o x 0 o x 0))) oc (R(lambda 0(x 0 o x 0 o x 0))))).
Proof.
  intros.
  destruct n. simpl in H. congruence. destruct n. simpl in H. congruence.
  induction n.
    - simpl. reflexivity.
    - simpl. simpl in IHn. rewrite IHn. reflexivity.
      reflexivity.
Qed.

Definition weird_expr (n: nat) := 
  repeat reduce_step n ((reduce_step continue) oc (R(lambda 0(x 0 o x 0 o x 0))) oc (R(lambda 0(x 0 o x 0 o x 0)))).

Definition continue_closed (n: nat) :=
  match n with
  | 0 => continue
  | 1 => reduce_step(continue)
  | 2 => reduce_step(reduce_step(continue))
  | S(S(S n')) => weird_expr n'
  end.
  
Theorem continue_closed_correct: forall n: nat, continue_closed n = repeat reduce_step n continue.
Proof.
  intros.
  destruct n. simpl. reflexivity. destruct n. simpl. reflexivity. destruct n. simpl. reflexivity.
  destruct (n >? 1) eqn:E.
  - simpl. pose proof continue_grows. specialize (H n). apply H in E. simpl in E. rewrite E. reflexivity.
  - destruct n. simpl. reflexivity. destruct n. simpl. reflexivity. simpl in E. congruence.
Qed.

Theorem weird_expr_S_to_step: forall n: nat, weird_expr (S n) = reduce_step(weird_expr n).
Proof.
  intros. unfold weird_expr. reflexivity.
Qed.

Theorem repeat_step_commute: forall A: Type, forall f: A -> A, forall n: nat, forall x: A, f(repeat f n x) = repeat f n (f x).
Proof.
  intros. replace (f(repeat f n x0)) with (repeat f 1 (repeat f n x0)).
  - rewrite <- repeat_add. rewrite Nat.add_comm. rewrite repeat_add. simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem weird_expr_move: forall n: nat, weird_expr n <> reduce_step(weird_expr n).
Proof.
  unfold not. intros.
  induction n.
  - unfold weird_expr in H. unfold reduce_step in H. simpl in H. congruence.
  -
Admitted.

Theorem continue_closed_move: forall n: nat, continue_closed n <> reduce_step(continue_closed n).
Proof.
  unfold not. intros.
  destruct n. unfold continue_closed in H. unfold continue in H. unfold reduce_step in H. simpl in H. congruence.
  destruct n. unfold continue_closed in H. unfold continue in H. unfold reduce_step in H. simpl in H. congruence.
  destruct n. unfold continue_closed in H. unfold continue in H. unfold reduce_step in H. simpl in H. congruence.
  simpl in H. pose proof weird_expr_move. specialize (H0 n). unfold not in H0. apply H0 in H. destruct H.
Qed.

Theorem continue_continues: ~ halts continue.
Proof.
  unfold not. unfold halts. intros.
  destruct H as [n H]. destruct H as [l H]. destruct H. rewrite <- continue_closed_correct in H.
  rewrite H in H0. pose proof continue_closed_move. specialize (H1 n). unfold not in H1. apply H1 in H0. destruct H0.
Qed.

Theorem halt_halts: halts halt.
Proof.
  unfold halts. exists 1. exists (R(x 0)). split.
  - unfold reduce_step. simpl. reflexivity.
  - unfold reduce_step. simpl. reflexivity.
Qed.

Definition whole (A: Type): A -> Prop := fun x: A => True.

Theorem implement_composition: 
  forall S: system, forall Q A: Type, forall f: Q -> A, forall A': Type, forall g: A -> A', 
  S ! f -> image_invertible g (whole A) -> S ! (fun x: Q => g(f x)).
Proof.
  unfold can_solve. intros.
  destruct H as [M H]. clear H. destruct M. eexists.
  refine ({|
  P1 := P3;
  P2 := P4;
  h1 := h3;
  h2 := fun x: state S => g(h4 x);
  s := s0;
  invertible_enc1 := invertible_enc3;
  invertible_enc2 := _;
  correct := _ |}).

  - unfold image_invertible. unfold image_invertible in H0.
    destruct H0 as [g_inv H0]. destruct H0. destruct invertible_enc4 as [h4_inv IE]. destruct IE.
    exists (fun x: A' => h4_inv(g_inv x)). split.
    -- intros. specialize (H (h4 x0)). 
       unfold whole in H. pose proof I. apply H in H4.
       rewrite H4. specialize (H1 x0).
       apply H1 in H3. apply H3.
    -- intros. split.
      --- specialize (H2 (g_inv y)). destruct H2. apply H2.
      --- specialize (H2 (g_inv y)). destruct H2. rewrite H3.
          specialize (H0 y). destruct H0. apply H4.
 
  - intros. rewrite correct0.
    -- reflexivity.
    -- apply H.
 
  - apply I.
Qed.

Definition b_to_lc (b: bool): reduce_marked :=
  match b with
  | true => lc_true
  | false => lc_false
  end.
  
Theorem eventual_same: forall l: reduce_marked, l = reduce_step l -> forall n: nat, l = repeat reduce_step n l.
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - replace (S n) with (n + 1). rewrite repeat_add. simpl.
    rewrite <- H. apply IHn.
    ring.
Qed.

Fixpoint geb (n m: nat): bool :=
  match n, m with
  | S n, 0 => false
  | S n', S m' => geb n' m'
  | _, _ => true
  end.

Theorem eventual_continue: forall l: reduce_marked, (exists n: nat, exists l': reduce_marked, repeat reduce_step n l = l' /\ ~ halts l') -> ~ halts l.
Proof.
  unfold not. intros. destruct H as [n [l' H]]. destruct H.
  assert (halts l'). unfold halts in H0. destruct H0 as [n' [l'' H0]]. destruct H0. unfold halts.
  exists n'. exists l''. split.
  - rewrite <- H. rewrite <- repeat_add. rewrite Nat.add_comm.
    rewrite repeat_add. rewrite <- H0.
    pose proof eventual_same. specialize (H3 l'' H2 n). apply H3.
  - apply H2.
  - apply H1 in H2. destruct H2. 
Qed.

Theorem eventual_halt: forall l: reduce_marked, (exists n: nat, exists l': reduce_marked, repeat reduce_step n l = l' /\ halts l') -> halts l.
Proof.
  unfold halts. intros. destruct H as [n [l' H]]. destruct H. destruct H0 as [n' [l'' [H0 H1]]].
  exists (n' + n). exists l''. rewrite repeat_add. split.
  - rewrite H. apply H0.
  - apply H1.
Qed.

Theorem lc_halting_problem:
  ~ exists halts_pred: reduce_marked -> reduce_marked -> bool,
  forall l1 l2: reduce_marked, halts_pred l1 l2 = true <-> halts (l1 oc l2).
Proof.
  unfold not. intros. destruct H as [halts_pred H].
  
  assert (forall l1 l2: reduce_marked,
          (b_to_lc(halts_pred l1 l2) = lc_true -> halts(l1 oc l2)) /\
          (b_to_lc(halts_pred l1 l2) = lc_false -> ~ halts(l1 oc l2))) as lc_phrased.
  intros. split.
  - intros. specialize (H l1 l2). destruct H. destruct (halts_pred l1 l2).
    -- assert (true = true). reflexivity. apply H in H2. apply H2.
    -- simpl in H0. unfold lc_false in H0. unfold lc_true in H0. congruence.
  - unfold not. intros. specialize (H l1 l2). destruct H. destruct (halts_pred l1 l2).
    -- simpl in H0. unfold lc_true in H0. unfold lc_false in H0. congruence.
    -- apply H2 in H1. congruence.
    
  - set (lc_halts := fun l1 l2: reduce_marked => b_to_lc(halts_pred l1 l2)).
    set (diagonal := lambdac 1 (if_then_else oc ((lambdac 0 (lc_halts (R(x 0)) (R(x 0)))) oc (R(x 1))) oc continue oc halt)).
    destruct (halts_pred diagonal diagonal) eqn:E.
    
    assert (lc_halts diagonal diagonal = lc_true). unfold lc_halts. rewrite E. simpl. reflexivity.
    specialize (lc_phrased diagonal diagonal). pose proof H0. apply lc_phrased in H0.

    assert (repeat reduce_step 1 (diagonal oc diagonal) = continue).
    unfold diagonal at 1. simpl.
Admitted.