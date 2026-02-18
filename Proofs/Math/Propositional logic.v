Require Import Coq.Arith.PeanoNat.
Require Import List.
Import ListNotations.

Inductive bool' : Type :=
  | T
  | F.

Inductive sentential : Type :=
  | v: nat -> sentential
  | a: sentential -> sentential -> sentential
  | o: sentential -> sentential -> sentential
  | n: sentential -> sentential
  | i: sentential -> sentential -> sentential
  | b: sentential -> sentential -> sentential.

Notation "x 'a' y" := (a x y) (at level 50, left associativity).
Notation "x 'o' y" := (o x y) (at level 50, left associativity).
Notation "x 'i' y" := (i x y) (at level 60, right associativity).
Notation "x 'b' y" := (b x y) (at level 60, right associativity).
Notation "'n' x" := (n x) (at level 40, left associativity).
  
Definition a_f (t1: bool') (t2: bool'): bool' :=
  match t1, t2 with
  | T, T => T
  | _, _ => F
  end.
  
Definition o_f (t1: bool') (t2: bool'): bool' :=
  match t1, t2 with
  | F, F => F
  | _, _ => T
  end.

Definition n_f (t: bool') : bool' :=
  match t with
  | T => F
  | F => T
  end.
  
Definition i_f (t1: bool') (t2: bool'): bool' :=
  match t1, t2 with
  | T, F => F
  | _, _ => T
  end.

Definition b_f (t1: bool') (t2: bool'): bool' :=
  match t1, t2 with
  | T, T => T
  | F, F => T
  | _, _ => F
  end.
  
Fixpoint truth (s: sentential) (v: nat -> bool') : bool' :=
  match s with
  | v n' => v n'
  | s1 a s2 => a_f (truth s1 v) (truth s2 v)
  | s1 o s2 => o_f (truth s1 v) (truth s2 v)
  | n s => n_f (truth s v)
  | s1 i s2 => i_f (truth s1 v) (truth s2 v)
  | s1 b s2 => b_f (truth s1 v) (truth s2 v)
  end.
  
Definition taut (s: sentential) : Prop := forall v: nat -> bool', truth s v = T.

Definition taut_i (Γ: list sentential) (s: sentential) : Prop := forall s': sentential, In s' Γ -> forall v: nat -> bool', truth s' v = T -> truth s v = T.

Inductive nd: (list sentential) -> sentential -> Prop :=
  | pr: forall Γ: list sentential, forall x: sentential, In x Γ -> nd Γ x
  | mp: forall Γ: list sentential, forall x y: sentential, nd Γ (x i y) -> nd Γ x -> nd Γ y
  | mt: forall Γ: list sentential, forall x y: sentential, nd Γ (x i y) -> nd Γ (n y) -> nd Γ (n x)
  | imp_intro: forall Γ: list sentential, forall x y: sentential, nd (x :: Γ) y -> nd Γ (x i y)
  | dn: forall Γ: list sentential, forall x: sentential, nd Γ (n(n x)) -> nd Γ x
  | idn: forall Γ: list sentential, forall x: sentential, nd Γ x -> nd Γ (n(n x))
  | conj_intro: forall Γ: list sentential, forall x y: sentential, nd Γ x -> nd Γ y -> nd Γ (x a y)
  | conj_elim_l: forall Γ: list sentential, forall x y: sentential, nd Γ (x a y) -> nd Γ x
  | conj_elim_r: forall Γ: list sentential, forall x y: sentential, nd Γ (x a y) -> nd Γ y
  | disj_intro_l: forall Γ: list sentential, forall x y: sentential, nd Γ x -> nd Γ (x o y)
  | disj_intro_r: forall Γ: list sentential, forall x y: sentential, nd Γ y -> nd Γ (x o y)
  | mtp_l: forall Γ: list sentential, forall x y: sentential, nd Γ (x o y) -> nd Γ (n y) -> nd Γ x
  | mtp_r: forall Γ: list sentential, forall x y: sentential, nd Γ (x o y) -> nd Γ (n x) -> nd Γ y
  | bi_intro: forall Γ: list sentential, forall x y: sentential, nd Γ (x i y) -> nd Γ (y i x) -> nd Γ (x b y)
  | bi_elim_l: forall Γ: list sentential, forall x y: sentential, nd Γ (x b y) -> nd Γ (x i y)
  | bi_elim_r: forall Γ: list sentential, forall x y: sentential, nd Γ (x b y) -> nd Γ (y i x)
  | raa: forall Γ: list sentential, forall x: sentential, (exists y: sentential, nd (x :: Γ) y /\ nd (x :: Γ) (n y)) -> nd Γ x.