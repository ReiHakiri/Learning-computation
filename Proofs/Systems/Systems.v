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
  | o: lambda_term -> lambda_term -> lambda_term
  | lambda: nat -> lambda_term -> lambda_term.
  
Inductive reduce_marked: Type :=
  | oc: reduce_marked -> reduce_marked -> reduce_marked
  | lambdac: nat -> reduce_marked -> reduce_marked
  | R: lambda_term -> reduce_marked.
  
Fixpoint substitute (l1: lambda_term) (n: nat) (l2: lambda_term): lambda_term :=
  match l1 with
  | x m => if m =? n then l2 else x m
  | o l' l'' => o (substitute l' n l2) (substitute l'' n l2)
  | lambda m l' => if m =? n then lambda m (substitute l' n l2) else lambda m l'
  end.
  
Fixpoint var_in (l: lambda_term) (n: nat) :=
  match l with
  | x m => m =? n
  | o l' l'' => orb (var_in l' n) (var_in l'' n)
  | lambda m l' => var_in l' n
  end.
  
Fixpoint substitutable (l1: lambda_term) (l2: lambda_term): bool :=
  match l1 with
  | lambda m l' => negb(var_in l2 m)
  | o l' l'' => andb (substitutable l' l2) (substitutable l'' l2)
  | _ => true
  end.
  
Definition alpha_conversion (l: lambda_term) (n: nat): lambda_term :=
  match l with
  | lambda m l' => lambda n (substitute l' n (x n))
  | l => l
  end.

Definition beta_reduction (l: lambda_term): lambda_term :=
  match l with
  | o (lambda n l') l'' => if substitutable l' l'' then substitute l' n l'' else l
  | l => l
  end.
  
Fixpoint normal_step (r: reduce_marked): reduce_marked :=
  match r with
  | R(o (lambda n l') l'') => R(beta_reduction(o (lambda n l') l''))
  | R(o l' l'') => oc (R l') (R l'')
  | R(lambda n l') => lambdac n (R l')
  | oc (lambdac n (R l')) (R l'') => R(beta_reduction(o (lambda n l') l''))
  | oc r' r'' => oc (normal_step r') r''
  | lambdac n r' => lambdac n (normal_step r')
  | r => r
  end.

Fixpoint R_remover (r: reduce_marked): lambda_term :=
  match r with
  | R l => l
  | oc r' r'' => o (R_remover r') (R_remover r'')
  | lambdac n r' => lambda n (R_remover r')
  end.

Definition R_adder (l: lambda_term): reduce_marked := R l.

Definition lc_step (l: lambda_term): lambda_term := R_remover(normal_step(R_adder l)).

Definition lambda_calculus: system := {| state := lambda_term; step := lc_step |}.

Definition lc_true: lambda_term := lambda 1 (lambda 0 (x 1)).

Definition lc_false: lambda_term := lambda 1 (lambda 0 (x 0)).

Definition reduces (l: lambda_term): Prop := exists n: nat, exists l': lambda_term, l' = repeat lc_step n l /\ l' = lc_step l'.

Theorem lc_halting_problem:
  ~ exists reduces_pred: lambda_term -> lambda_term -> bool,
  (forall l1 l2: lambda_term, reduces_pred l1 l2 = true <-> reduces (o l1 l2)) /\
  lambda_calculus ! reduces_pred.
Proof. Abort.