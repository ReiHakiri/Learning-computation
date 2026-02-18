Require Import Coq.Arith.PeanoNat.
Require Import List.
Import ListNotations.

Fixpoint replace {type: Type} (L: list type) (index: nat) (new: type) : list type :=
  match L with
  | [] => []
  | x :: y => if (index =? 0) then new :: y else cons x (replace y (index - 1) new)
  end.

Definition head_edit_tape {Σ : Type} (tape: list Σ) (position: nat) (new_symbol: Σ) : list Σ := replace tape position new_symbol.

Definition edit_position (position: nat) (forward: bool) : nat :=
  if forward then (position + 1) else
  match position with
  | 0 => 0
  | S position' => position'
  end.

Definition move_edit_tape {Σ : Type} (tape: list Σ) (position: nat) (forward: bool) (blank: Σ) : list Σ :=
  match position, forward with
  | 0, false => blank :: tape
  | position, false => tape
  | position, true => if position =? (length tape) - 1 then tape ++ [blank] else tape
  end.

Record TM (Σ: Type) (q: Type) (transition: Σ -> q -> (Σ * q * bool)) (blank: Σ) (eqhalt: q -> bool) := {
  tape: list Σ;
  state: q;
  position: nat;
  halted: bool
}.

Definition TM_step 
  {Σ: Type} 
  {q: Type} 
  {transition: Σ -> q -> (Σ * q * bool)} 
  {blank: Σ} 
  {eqhalt: q -> bool}
  (x: TM Σ q transition blank eqhalt)
  : TM Σ q transition blank eqhalt :=
  
  if (halted Σ q transition blank eqhalt x) then x else
  
  let x_tape := tape Σ q transition blank eqhalt x in
  let x_state := state Σ q transition blank eqhalt x in
  let x_position := position Σ q transition blank eqhalt x in
  
  match transition (nth x_position x_tape blank) (x_state) with
  | (new_symbol, new_state, forward) => 
  
  if (eqhalt (new_state)) 
  
  then {|tape := x_tape; state := x_state; position := x_position; halted := true|} 
  
  else {|tape := move_edit_tape (head_edit_tape x_tape x_position new_symbol) x_position forward blank; 
        state := new_state; 
        position := edit_position x_position forward;
        halted := false
        |}
  
  end.
  
Fixpoint TM_run
  {Σ: Type} 
  {q: Type} 
  {transition: Σ -> q -> (Σ * q * bool)} 
  {blank: Σ} 
  {eqhalt: q -> bool}
  (x: TM Σ q transition blank eqhalt)
  (fuel: nat)
  : TM Σ q transition blank eqhalt :=
  
  match fuel with
  | 0 => x
  | S fuel' => TM_run (TM_step x) fuel'
  end.

Inductive sigma2 := c | b.

Inductive q18 := u1 | u2 | u3 | u4 | u5 | u6 | u7 | u8 | u9 | u10 | u11 | u12 | u13 | u14 | u15 | u16 | u17 | u18 | halt.

Definition eqhalt_18_2 (state: q18) : bool :=
  match state with
  | halt => true
  | state => false
  end.

Definition table_18_2 (symbol: sigma2) (state: q18) : sigma2 * q18 * bool := 
  match symbol, state with
  | c, u1 => (b, u2, true)
  | b, u1 => (b, u3, true)
  | c, u2 => (c, u1, true)
  | b, u2 => (b, u1, true)
  | c, u3 => (c, u5, false)
  | b, u3 => (b, u9, false)
  | c, u4 => (c, u5, false)
  | b, u4 => (b, u6, false)
  | c, u5 => (c, u4, false)
  | b, u5 => (c, u4, false)
  | c, u6 => (b, u2, true)
  | b, u6 => (c, u4, false)
  | c, u7 => (c, u8, false)
  | b, u7 => (b, u9, false)
  | c, u8 => (b, u12, true)
  | b, u8 => (b, u7, false)
  | c, u9 => (b, u10, false)
  | b, u9 => (b, u7, false)
  | c, u10 => (c, u13, true)
  | b, u10 => (b, u15, true)
  | c, u11 => (b, u7, false)
  | b, u11 => (b, u12, true)
  | c, u12 => (c, u11, true)
  | b, u12 => (b, u11, true)
  | c, u13 => (c, u15, false)
  | b, u13 => (b, u14, true)
  | c, u14 => (c, u13, true)
  | b, u14 => (b, u13, true)
  | c, u15 => (b, u9, false)
  | b, u15 => (c, u16, true)
  | c, u16 => (c, u17, true)
  | b, u16 => (b, u15, true)
  | c, u17 => (c, halt, true)
  | b, u17 => (c, u18, true)
  | c, u18 => (c, u15, true)
  | b, u18 => (c, u1, true)
  | c, halt => (c, halt, true)
  | b, halt => (c, halt, true)
  end.

Definition example_tape : list sigma2 := [c ; c ; b ; c ; c ; c; b ; b ; b; c ; c ; c ; c ; c ; b ; b ; c ; c ; b ; c ; c].

Definition eg_u_18_2 : TM sigma2 q18 table_18_2 b eqhalt_18_2 := 
  {|tape := example_tape; 
   state := u1; 
   position := 0; 
   halted := false
   |}.
  
(* This UTM was found here: https://dna.hamilton.ie/assets/dw/NearyWoodsMCU07.pdf *)

Compute TM_run eg_u_18_2 100.

Proposition zero_step_same: 
  forall Σ: Type, 
  forall q: Type, 
  forall transition: Σ -> q -> (Σ * q * bool), 
  forall blank: Σ, 
  forall eqhalt: q -> bool, 
  forall x: TM Σ q transition blank eqhalt,
  
  TM_run x 0 = x.
  
Proof.
  auto.
Qed.

Definition start_on_halt
  {Σ: Type} 
  {q: Type} 
  {transition: Σ -> q -> (Σ * q * bool)} 
  {blank: Σ} 
  {eqhalt: q -> bool}
  (x: TM Σ q transition blank eqhalt)
  : bool :=
  
  halted Σ q transition blank eqhalt (TM_run x 0).

Definition halting
  {Σ: Type} 
  {q: Type} 
  {transition: Σ -> q -> (Σ * q * bool)} 
  {blank: Σ} 
  {eqhalt: q -> bool}
  (x: TM Σ q transition blank eqhalt)
  : Prop :=
  
  (exists fuel: nat, halted Σ q transition blank eqhalt (TM_run x fuel) = true) /\ (start_on_halt x = false).
  
Definition eg_halting : TM sigma2 q18 table_18_2 b eqhalt_18_2 :=
  {|tape := [c; c]; state := u16; position := 0; halted := false|}.
  
Proposition exists_halting: 
  exists Σ: Type, 
  exists q: Type, 
  exists transition: Σ -> q -> (Σ * q * bool), 
  exists blank: Σ, 
  exists eqhalt: q -> bool, 
  exists x: TM Σ q transition blank eqhalt,
  
  halting x.
  
Proof.
  exists sigma2. exists q18. exists table_18_2. exists b. exists eqhalt_18_2. exists eg_halting.
  unfold halting. exists.
  exists 2. auto.
  auto.
Qed.