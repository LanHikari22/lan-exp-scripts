Require Import CoqAnalysis.Nat.

Record Z : Type := {
  pos : nat;
  neg : nat
}.

Proposition z_reduce_pos : forall a b : nat, pos {| pos := a; neg := b |} = a.
Proof.
  intros a b.
  simpl.
  reflexivity.
Qed.

Proposition z_reduce_neg : forall a b : nat, neg {| pos := a; neg := b |} = b.
Proof.
  intros a b.
  simpl.
  reflexivity.
Qed.

(*
  a - b = c - d
  a     = c - d + b
  a + d = c + b
*)
Definition z_eq (a b : Z) : Prop :=
  pos a + neg b = pos b + neg a.

Declare Scope Z_scope.
Bind Scope Z_scope with Z.
Delimit Scope Z_scope with Z.

Notation "x ~= y" := (z_eq x y) (at level 70) : Z_scope.
Notation "x -Z y" := {| pos := x; neg := y |} (at level 60) : Z_scope.

(* To show an operation is an equivalence relation we need refl, trans, and sym *)

Open Scope Z_scope.
Proposition z_eq_refl : forall a : Z, a ~= a.
Proof.
  intros a.
  unfold z_eq.
  reflexivity.
Qed.

Proposition z_eq_sym : forall a b : Z, (a ~= b) -> b ~= a.
Proof.
  intros a b H0.
  unfold z_eq in *.
  rewrite -> H0.
  reflexivity.
Qed.

Proposition z_eq_trans : forall a b c : Z, (a ~= b) -> (b ~= c) -> (a ~= c).
Proof.
  intros a b c H0l H0r.
  unfold z_eq in *.
  apply <- (add_cancel_r ((pos b) + (neg c)) ((neg a)) ((pos c) + (neg b)) ) in H0r.
  rewrite <- add_assoc in H0r.
  rewrite -> (add_comm (neg c) (neg a)) in H0r.
  rewrite -> add_assoc in H0r.
  rewrite <- H0l in H0r.
  rewrite <- add_assoc in H0r.
  rewrite -> (add_comm (neg b) (neg c)) in H0r.
  rewrite <- add_assoc in H0r.
  rewrite -> (add_comm (neg b) (neg a)) in H0r.
  rewrite -> add_assoc in H0r.
  rewrite -> add_assoc in H0r.
  apply -> add_cancel_r in H0r.
  rewrite -> H0r.
  reflexivity.
Qed.

Require Import Stdlib.Setoids.Setoid.
Add Parametric Relation : Z z_eq
  reflexivity proved by z_eq_refl
  symmetry proved by z_eq_sym
  transitivity proved by z_eq_trans
  as Z_setoid.

Proposition z_eq_trans_2 :forall a b c : Z, (a ~= b) -> (b ~= c) -> (a ~= c).
Proof.
  intros a b c H0 H1.
  rewrite -> H0.
  rewrite -> H1.
  reflexivity.
Qed.

Definition z_add (a b : Z) : Z :=
  {| 
    pos := (pos a) + (pos b) ; 
    neg := (neg a) + (neg b)
  |}.

(*
(a - b) * (c - d) = ac -ad -bc +bd = (ac + bd) - (ad + bc)
*)
Definition z_mult (a b : Z) : Z :=
  {| 
    pos := ((pos a) * (pos b)) + ((neg a) * (neg b)); 
    neg := ((pos a) * (neg b)) + ((neg a) * (pos b))
  |}.

(*
Open Scope Z_scope.
Close Scope Z_scope.
*)

Notation "x + y" := (z_add x y) (at level 50, left associativity) : Z_scope.

Notation "x * y" := (z_mult x y) (at level 40, left associativity) : Z_scope.

Require Import Stdlib.Classes.Morphisms.
Instance z_add_proper : 
  Proper (z_eq ==> z_eq ==> z_eq ) z_add.
Proof.
  intros x x' Hx y y' Hy.
  unfold z_add, z_eq in *.
  rewrite -> z_reduce_pos.
  rewrite -> z_reduce_pos.
  rewrite -> z_reduce_neg.
  rewrite -> z_reduce_neg.
  rewrite -> add_assoc.
  rewrite -> add_comm_acbd.
  rewrite -> Hx.
  rewrite -> add_comm_cdab.
  rewrite -> Hy.
  rewrite -> add_assoc.
  rewrite -> add_comm_cadb.
  reflexivity.
Qed.
Close Scope Z_scope.

Open Scope Z_scope.

(* Now this is trivial thanks to proof of z_add_proper which lets us rewrite under addition *)
Proposition z_add_respects_equivalence : forall a b c : Z, a ~= b -> a + c ~= b + c.
Proof.
  intros a b c H0.
  rewrite <- H0.
  reflexivity.
Qed.

Close Scope Z_scope.

Require Import Stdlib.Classes.Morphisms.
Instance z_mult_proper : 
  Proper (z_eq ==> z_eq ==> z_eq ) z_mult.
Proof.
  intros a a_ Ha b b_ Hb.
  transitivity (z_mult a_ b).
  {
    (* Goal: z_mult a b ~= z_mult a_ b *)
    unfold z_eq in *.
    unfold z_mult.
    repeat rewrite -> z_reduce_pos.
    repeat rewrite -> z_reduce_neg.
    repeat rewrite -> add_assoc.
    do 4 apply -> (add_cancel 0).
    repeat rewrite -> add_assoc.
    rewrite -> add_comm_8_a0_swap_a5.
    rewrite -> add_comm_8_a0_swap_a1.
    rewrite -> add_comm_8_a0_swap_a6.
    rewrite <- mult_dist_over_add_r.
    repeat rewrite -> add_0_r.
    repeat rewrite -> def_add_clause_0.
    rewrite <- add_assoc.
    rewrite <- mult_dist_over_add_r.
    rewrite <- Ha.
    rewrite <- mult_dist_over_add.
    do 4 apply -> (add_cancel 0).
    repeat rewrite -> add_assoc.
    rewrite -> add_comm_8_a0_swap_a4.
    rewrite -> add_comm_8_a0_swap_a1.
    rewrite -> add_comm_8_a0_swap_a7.
    rewrite <- mult_dist_over_add_r.
    repeat rewrite -> add_0_r.
    repeat rewrite -> def_add_clause_0.
    rewrite <- add_assoc.
    rewrite <- mult_dist_over_add_r.
    rewrite -> add_comm in Ha.
    rewrite -> Ha.
    rewrite -> (add_comm (pos a_) (neg a)).
    rewrite <- mult_dist_over_add.
    rewrite -> (add_comm (pos b) (neg b)).
    rewrite -> add_comm in Ha.
    rewrite -> Ha.
    rewrite -> (add_comm (neg a) (pos a_)).
    reflexivity.
  }
  {
    (* Goal: z_mult a_ b ~= z_mult a_ b_ *)
    unfold z_eq in *.
    unfold z_mult.
    repeat rewrite -> z_reduce_pos.
    repeat rewrite -> z_reduce_neg.
    repeat rewrite -> add_assoc.
    do 4 apply -> (add_cancel 0).
    repeat rewrite -> add_assoc.
    rewrite -> add_comm_8_a0_swap_a4.
    rewrite -> add_comm_8_a0_swap_a1.
    rewrite -> add_comm_8_a0_swap_a6.
    rewrite <- mult_dist_over_add.
    repeat rewrite -> add_0_r.
    repeat rewrite -> def_add_clause_0.
    rewrite <- add_assoc.
    rewrite <- mult_dist_over_add.
    rewrite -> (add_comm (neg b_) (pos b)).
    rewrite -> (add_comm (neg b) (pos b_)).
    rewrite <- Hb.
    rewrite <- mult_dist_over_add_r.
    do 4 apply -> (add_cancel 0).
    repeat rewrite -> add_assoc.
    rewrite -> add_comm_8_a0_swap_a4.
    rewrite -> add_comm_8_a0_swap_a1.
    rewrite -> add_comm_8_a0_swap_a6.
    rewrite <- mult_dist_over_add.
    repeat rewrite -> add_0_r.
    repeat rewrite -> def_add_clause_0.
    rewrite <- add_assoc.
    rewrite <- mult_dist_over_add.
    rewrite -> (add_comm) in Hb.
    rewrite -> Hb.
    rewrite -> (add_comm (neg b) (pos b_)).
    rewrite <- mult_dist_over_add_r.
    rewrite <- Hb.
    rewrite -> (add_comm (neg b_) (pos b)).
    reflexivity.
  }
Qed.

Open Scope Z_scope.

Proposition z_mult_respects_equivalence : forall a b c : Z, a ~= b -> a * c ~= b * c.
Proof.
  intros a b c H0.
  rewrite <- H0.
  reflexivity.
Qed.

Close Scope Z_scope.

Definition z_neg (a : Z) : Z :=
  {| pos := (neg a); neg := (pos a) |}.

Notation "-- x" := (z_neg x) (at level 45) : Z_scope.

Require Import Stdlib.Classes.Morphisms.
Instance z_neg_proper : 
  Proper (z_eq ==> z_eq ) z_neg.
Proof.
  intros a a' Ha.
  unfold z_eq in *.
  unfold z_neg.
  repeat rewrite z_reduce_pos.
  repeat rewrite z_reduce_neg.
  rewrite -> add_comm in Ha.
  rewrite -> Ha.
  apply add_comm.
Qed.

Open Scope Z_scope.
Proposition z_neg_respects_equivalence : forall a a' : Z, a ~= a' -> --a ~= --a'.
Proof.
  intros a a' H0.
  rewrite -> H0.
  reflexivity.
Qed.

Proposition z_neg_dist_over_add : forall a b : Z, (-- (a + b)) = ((-- a) + (-- b)).
Proof.
  intros a b.
  unfold z_add.
  unfold z_neg.
  do 3 rewrite -> z_reduce_pos.
  do 3 rewrite -> z_reduce_neg.
  reflexivity.
Qed.

Proposition z_neg_reduce_double : forall a : Z, (-- (-- a)) = a.
Proof.
  intros [a_ _a].
  unfold z_neg.
  do 2 rewrite -> z_reduce_pos.
  do 2 rewrite -> z_reduce_neg.
  reflexivity.
Qed.

Proposition z_neg_both_sides : forall a b : Z, (a ~= b) <-> ((-- a) ~= (-- b)).
Proof.
  intros [a_ _a] [b_ _b].
  split.
  {
    intros H0.
    rewrite -> H0.
    reflexivity.
  }
  {
    intros H0.
    unfold z_neg in H0.
    unfold z_eq in *.
    do 4 rewrite -> z_reduce_pos in *.
    do 4 rewrite -> z_reduce_neg in *.
    symmetry in H0.
    rewrite -> (add_comm _b a_) in H0.
    rewrite -> (add_comm _a b_) in H0.
    exact H0.
  }
Qed.

Close Scope Z_scope.

Definition NZ (n : nat) : Z :=
  {| pos := n; neg := 0 |}.

Notation "NZ# x" := (NZ x) (at level 60).

Open Scope Z_scope.

Proposition def_nz_pos : forall a : nat, (pos (NZ#a)) = a.
Proof.
  intros a.
  unfold NZ.
  unfold pos.
  reflexivity.
Qed.

Proposition def_nz_neg : forall a : nat, (neg (NZ#a)) = 0.
Proof.
  intros a.
  unfold NZ.
  unfold neg.
  reflexivity.
Qed.

Proposition z_0_neg_as_nz : forall a : nat, {| pos := a; neg := 0 |} = (NZ#a).
Proof.
  intros a.
  simpl.
  reflexivity.
Qed.

Proposition z_0_pos_as_neg_nz : forall a : nat, {| pos := 0; neg := a |} = (-- (NZ# a)).
Proof.
  intros a.
  unfold z_neg.
  rewrite -> def_nz_neg.
  rewrite -> def_nz_pos.
  reflexivity.
Qed.

Proposition z_nz_inject : forall a b : nat, ((NZ# a) ~= (NZ# b)) <-> (a = b).
Proof.
  intros a b.
  unfold NZ.
  unfold z_eq.
  do 2 rewrite -> z_reduce_pos.
  do 2 rewrite -> z_reduce_neg.
  do 2 rewrite -> add_0_r.
  reflexivity.
Qed.

Proposition z_0_ne_succ : forall a : nat, (NZ#0) ~= (NZ# (S a)) -> False.
Proof.
  intros a H0.
  unfold NZ in H0.
  unfold z_eq in H0.
  do 2 rewrite -> z_reduce_neg in H0.
  do 2 rewrite -> z_reduce_pos in H0.
  rewrite -> def_add_clause_0 in H0.
  rewrite -> add_0_r in H0.
  discriminate.
Qed.

Proposition z_0_ne_neg_succ : forall a : nat, (NZ#0) ~= (-- (NZ# (S a))) -> False.
Proof.
  intros a H0.
  unfold NZ in H0.
  unfold z_neg in H0.
  unfold z_eq in H0.
  do 3 rewrite -> z_reduce_neg in H0.
  do 3 rewrite -> z_reduce_pos in H0.
  rewrite -> def_add_clause_0 in H0.
  rewrite -> add_0_r in H0.
  discriminate.
Qed.

Proposition z_pos_ne_neg : forall a b : nat, (NZ# (S a)) ~= (-- (NZ# (S b))) -> False.
Proof.
  intros a b H0.
  unfold z_neg in H0.
  unfold NZ in H0.
  unfold z_eq in H0.
  do 3 rewrite -> z_reduce_neg in H0.
  do 3 rewrite -> z_reduce_pos in H0.
  rewrite -> def_add_clause_0 in H0.
  rewrite -> def_add_clause_1 in H0.
  discriminate.
Qed.

Proposition z_non_neg_eqv_neg_implies_0 : forall a b : nat,
  ((NZ#a) ~= (-- NZ#b))%Z -> (a = 0) /\ (b = 0).
Proof.
  intros a b H0.
  unfold z_neg in H0.
  unfold z_eq in H0.
  simpl in H0.
  apply zero_sum_zero_parts in H0.
  exact H0.
Qed.

Proposition z_same_parts_eqv_0 : forall a : nat, ({| pos := a; neg := a |} ~= (NZ# 0)).
Proof.
  intros a.
  unfold z_eq.
  simpl.
  rewrite -> add_0_r.
  reflexivity.
Qed.

Proposition z_reduce_shared_part_pos : forall (a b : nat),
  ({| pos := (a + b); neg := a |} ~= (NZ#b))%Z.
Proof.
  intros a b.
  unfold z_eq.
  simpl.
  rewrite -> add_0_r.
  rewrite -> add_comm.
  reflexivity.
Qed.

Proposition z_reduce_shared_part_neg : forall (a b : nat),
  ({| pos := a; neg := (a + b) |} ~= (-- NZ#b))%Z.
Proof.
  intros a b.
  unfold z_eq.
  simpl.
  reflexivity.
Qed.

Proposition z_eqv_0_is_same : forall a_ _a : nat, 
  ({| pos := a_; neg := _a |} ~= (NZ# 0)) <-> (a_ = _a).
Proof.
  intros a_ _a.
  split.
  {
    intros H0.
    unfold NZ in H0.
    unfold z_eq in H0.
    do 2 rewrite -> z_reduce_neg in H0.
    do 2 rewrite -> z_reduce_pos in H0.
    rewrite -> def_add_clause_0 in H0.
    rewrite -> add_0_r in H0.
    exact H0.
  }
  {
    intros H0.
    rewrite -> H0.
    unfold NZ.
    unfold z_eq.
    do 2 rewrite -> z_reduce_neg.
    do 2 rewrite -> z_reduce_pos.
    rewrite -> add_0_r.
    rewrite -> def_add_clause_0.
    reflexivity.
  }
Qed.

Proposition z_pos_diff_is_nz : forall a b : nat, 
  {| pos := a + b; neg := a |} ~= (NZ# b).
Proof.
  intros a b.
  unfold NZ.
  unfold z_eq.
  do 2 rewrite -> z_reduce_neg.
  do 2 rewrite -> z_reduce_pos.
  rewrite -> add_0_r.
  rewrite -> add_comm.
  reflexivity.
Qed.

Proposition z_neg_diff_is_neg_nz : forall a b : nat, 
  {| pos := a; neg := a + b |} ~= (-- (NZ# b)).
Proof.
  intros a b.
  unfold NZ.
  unfold z_neg.
  unfold z_eq.
  do 3 rewrite -> z_reduce_neg.
  do 3 rewrite -> z_reduce_pos.
  rewrite -> def_add_clause_0.
  reflexivity.
Qed.

Proposition z_pos_diff_succ_is_nz : forall a : nat,
  {| pos := (S a); neg := a |} ~= (NZ#1).
Proof.
  intros a.
  rewrite <- add_1_is_succ.
  rewrite -> (add_comm 1 a).
  rewrite -> z_pos_diff_is_nz.
  reflexivity.
Qed.

Proposition z_neg_diff_succ_is_neg_nz : forall a : nat,
  {| pos := a; neg := (S a) |} ~= (-- (NZ#1)).
Proof.
  intros a.
  rewrite <- add_1_is_succ.
  rewrite -> (add_comm 1 a).
  rewrite -> z_neg_diff_is_neg_nz.
  reflexivity.
Qed.

Proposition z_eqv_nz_as_diff_sum : forall a_ _a b : nat,
  ({| pos := a_; neg := _a |} ~= (NZ# b)) <-> (a_ = (_a + b)%nat).
Proof.
  intros a_ _a b.
  split.
  {
    intros H0.
    unfold NZ in H0.
    unfold z_eq in H0.
    do 2 rewrite -> z_reduce_neg in H0.
    do 2 rewrite -> z_reduce_pos in H0.
    rewrite -> add_0_r in H0.
    rewrite -> H0.
    apply add_comm.
  }
  {
    intros H0.
    rewrite -> H0.
    apply z_pos_diff_is_nz.
  }
Qed.

Proposition z_eqv_neg_nz_as_diff_sum : forall a_ _a b : nat,
  ({| pos := a_; neg := _a |} ~= (-- (NZ# b))) <-> (_a = (a_ + b)%nat).
Proof.
  intros a_ _a b.
  split.
  {
    intros H0.
    unfold NZ in H0.
    unfold z_neg in H0.
    unfold z_eq in H0.
    do 3 rewrite -> z_reduce_neg in H0.
    do 3 rewrite -> z_reduce_pos in H0.
    rewrite -> def_add_clause_0 in H0.
    rewrite <- H0.
    reflexivity.
  }
  {
    intros H0.
    rewrite -> H0.
    apply z_neg_diff_is_neg_nz.
  }
Qed.

Proposition z_trichotomy_0 : forall a : Z, 
  a ~= (NZ#0) -> 
  ((exists ! n : nat, a ~= (NZ#S(n))) -> False) /\
  ((exists ! n : nat, a ~= (--(NZ#S(n)))) -> False).
Proof.
  intros a H0.
  split.
  {
    intros [p0 [Hp0 Hp0u]].
    rewrite -> H0 in Hp0.
    apply z_0_ne_succ in Hp0.
    exact Hp0.
  }
  {
    intros [p0 [Hp0 Hp0u]].
    rewrite -> H0 in Hp0.
    apply z_0_ne_neg_succ in Hp0.
    exact Hp0.
  }
Qed.


Proposition z_trichotomy_1 : forall a : Z, 
  (exists ! n : nat, a ~= (NZ#S(n))) ->
  ((a ~= (NZ#0)) -> False) /\
  ((exists ! n : nat, a ~= (--(NZ#S(n)))) -> False).
Proof.
  intros a [p0 [Hp0 Hp0u]].
  split.
  {
    intros H1.
    rewrite -> Hp0 in H1.
    symmetry in H1.
    apply z_0_ne_succ in H1.
    exact H1.
  }
  {
    intros [p1 [Hp1 Hp1u]].
    rewrite -> Hp0 in Hp1.
    apply z_pos_ne_neg in Hp1.
    exact Hp1.
  }
Qed.

Proposition z_trichotomy_2 : forall a : Z, 
  (exists ! n : nat, a ~= (--(NZ#S(n)))) ->
  ((a ~= (NZ#0)) -> False) /\
  ((exists ! n : nat, a ~= (NZ#S(n))) -> False).
Proof.
  intros a [p0 [Hp0 Hp0u]].
  split.
  {
    intros H1.
    rewrite -> Hp0 in H1.
    symmetry in H1.
    apply z_0_ne_neg_succ in H1.
    exact H1.
  }
  {
    intros [p1 [Hp1 Hp1u]].
    rewrite -> Hp0 in Hp1.
    symmetry in Hp1.
    apply z_pos_ne_neg in Hp1.
    exact Hp1.
  }
Qed.

Proposition z_trichotomy_3 : forall a : Z, 
  (a ~= (NZ#0)) \/ 
  (exists ! n : nat, a ~= (NZ#S(n))) \/
  (exists ! n : nat, a ~= --(NZ#S(n))).
Proof.
  intros [a_ _a].
  induction a_ as [| a_'].
  {
    destruct _a as [| _a'].
    {
      left.
      unfold NZ.
      reflexivity.
    }
    {
      right; right.
      exists _a'.
      split.
      {
        unfold z_neg.
        rewrite -> def_nz_pos.
        rewrite -> def_nz_neg.
        reflexivity.
      }
      {
        intros x' Hx'.
        rewrite -> z_0_pos_as_neg_nz in Hx'.
        injection Hx' as Hx'.
        symmetry in Hx'.
        exact Hx'.
      }
    }
  }
  {
    destruct IHa_' as [Hz | [Hpos | Hneg]].
    {
      right; left.
      exists 0.
      split.
      {
        apply -> z_eqv_0_is_same in Hz.
        rewrite <- Hz.
        apply z_pos_diff_succ_is_nz.
      }
      {
        intros x' Hx'.
        apply -> z_eqv_0_is_same in Hz.
        rewrite -> Hz in Hx'.
        rewrite -> z_pos_diff_succ_is_nz in Hx'.
        injection Hx' as Hx'.
        rewrite -> add_0_r in Hx'.
        exact Hx'.
      }
    }
    {
      destruct Hpos as [p0 [Hp0 Hp0u]].
      apply -> z_eqv_nz_as_diff_sum in Hp0.
      rewrite -> Hp0.
      right; left.
      (*
      assert (Hexists : forall n : nat, {| pos := S (_a + S p0); neg := _a |} ~= (NZ# S n)).
      {
        intros n.
        rewrite <- def_add_clause_1.
        rewrite -> add_swap_s.
        rewrite -> z_pos_diff_is_nz.
        (* Goal: (NZ# S (S p0)) ~= (NZ# S n) *)
      }
      *)
      exists (S p0).
      split.
      {
        rewrite <- def_add_clause_1.
        rewrite -> add_swap_s.
        rewrite -> z_pos_diff_is_nz.
        reflexivity.
      }
      {
        intros x' Hx'.
        rewrite <- def_add_clause_1 in Hx'.
        rewrite -> add_swap_s in Hx'.
        rewrite -> z_eqv_nz_as_diff_sum in Hx'.
        apply -> add_cancel in Hx'.
        injection Hx' as Hx'.
        exact Hx'.
      }
    }
    {
      destruct Hneg as [p0 [Hp0 Hp0u]].
      destruct p0 as [| p0'].
      {
        apply -> z_eqv_neg_nz_as_diff_sum in Hp0.
        rewrite -> Hp0.
        left.
        rewrite <- add_1_is_succ.
        rewrite -> add_comm.
        apply <- z_eqv_0_is_same.
        reflexivity.
      }
      {
        apply -> z_eqv_neg_nz_as_diff_sum in Hp0.
        rewrite -> Hp0.
        right; right.
        (*
        assert ( Hexists : forall n : nat, 
          {| pos := S a_'; neg := a_' + S (S p0') |} ~= (-- (NZ# S n)) ).
        {
          intros n.
          rewrite <- add_swap_s.
          rewrite -> z_neg_diff_is_neg_nz.
          (* Goal: (-- (NZ# S p0')) ~= (-- (NZ# S n)) *)
        }
        *)
        exists p0'.
        split.
        {
          rewrite <- add_swap_s.
          rewrite -> z_neg_diff_is_neg_nz.
          reflexivity.
        }
        {
          intros x' Hx'.
          rewrite <- add_swap_s in Hx'.
          rewrite -> z_neg_diff_is_neg_nz in Hx'.
          injection Hx' as Hx'.
          symmetry in Hx'.
          exact Hx'.
        }
      }
    }
  }
Qed.

Proposition z_trichotomy_3_again_with_nat_ord : forall a_ _a : nat, 
  ({| pos := a_; neg := _a |} ~= (NZ#0)) \/ 
  (exists ! n : nat, {| pos := a_; neg := _a |} ~= (NZ#S(n))) \/
  (exists ! n : nat, {| pos := a_; neg := _a |} ~= --(NZ#S(n))).
Proof.
  intros a_ _a.
  destruct (nat_ord_trichotomy_3 a_ _a) as [Heq | [Hgt | Hlt]].
  {
    rewrite -> Heq.
    left.
    rewrite -> z_eqv_0_is_same.
    reflexivity.
  }
  {
    right; left.
    rewrite -> gt_as_ge_succ in Hgt.
    unfold ge in Hgt.
    destruct Hgt as [p0 [Hp0 Hp0u]].
    rewrite -> Hp0.
    (*
    assert (Hexists : forall n : nat, {| pos := S _a + p0; neg := _a |} ~= (NZ# S n) ).
    {
      intros n.
      rewrite -> add_swap_s.
      rewrite -> z_pos_diff_is_nz.
      (* Goal: (NZ# S p0) ~= (NZ# S n) *)
    }
    *)
    exists p0.
    split.
    {
      rewrite -> add_swap_s.
      rewrite -> z_pos_diff_is_nz.
      reflexivity.
    }
    {
      intros x' Hx'.
      rewrite -> add_swap_s in Hx'.
      rewrite -> z_pos_diff_is_nz in Hx'.
      injection Hx' as Hx'.
      do 2 rewrite -> add_0_r in Hx'.
      exact Hx'.
    }
  }
  {
    right; right.
    rewrite -> gt_as_ge_succ in Hlt.
    destruct Hlt as [p0 [Hp0 Hp0u]].
    rewrite -> Hp0.
    rewrite -> add_swap_s.
    (*
    assert (Hexists : forall n : nat, {| pos := a_; neg := a_ + S p0 |} ~= (-- (NZ# S n)) ).
    {
      intros n.
      rewrite -> z_neg_diff_is_neg_nz.
      (* Goal : (-- (NZ# S p0)) ~= (-- (NZ# S n)) *)
    }
    *)
    exists p0.
    split.
    {
      rewrite -> z_neg_diff_is_neg_nz.
      reflexivity.
    }
    {
      intros x' Hx'.
      rewrite -> z_neg_diff_is_neg_nz in Hx'.
      injection Hx' as Hx'.
      symmetry in Hx'.
      exact Hx'.
    }
  }
Qed.

Proposition z_0_pad_pos_l : forall a_ _a : nat, 
  {| pos := a_; neg := _a |} = {| pos := 0 + a_; neg := _a |}.
Proof.
  easy.
Qed.

Proposition z_0_pad_neg_l : forall a_ _a : nat, 
  {| pos := a_; neg := _a |} = {| pos := a_; neg := 0 + _a |}.
Proof.
  easy.
Qed.

(*\begin{Z is a commutative ring}*)

Proposition z_add_comm : forall a b : Z, a + b = b + a.
Proof.
  intros [a_ _a] [b_ _b].
  unfold z_add.
  do 2 rewrite -> z_reduce_pos.
  do 2 rewrite -> z_reduce_neg.
  rewrite -> (add_comm a_ b_).
  rewrite -> (add_comm _b _a).
  reflexivity.
Qed.

Proposition z_add_assoc : forall a b c : Z, (a + b) + c = a + (b + c).
Proof.
  intros [a_ _a] [b_ _b] [c_ _c].
  unfold z_add.
  do 5 rewrite -> z_reduce_pos.
  do 5 rewrite -> z_reduce_neg.
  do 2 rewrite -> add_assoc.
  reflexivity.
Qed.

Proposition z_add_0_l : forall a : Z, (NZ#0) + a = a.
Proof.
  intros [a_ _a].
  unfold NZ.
  unfold z_add.
  do 2 rewrite -> z_reduce_pos.
  do 2 rewrite -> z_reduce_neg.
  do 2 rewrite -> def_add_clause_0.
  reflexivity.
Qed.

Proposition z_add_0_r : forall a : Z, a + (NZ#0) = a.
Proof.
  intros a.
  rewrite -> z_add_comm.
  apply z_add_0_l.
Qed.

Proposition z_additive_inverse_l : forall a : Z, (-- a) + a ~= (NZ#0).
Proof.
  intros [a_ _a].
  unfold z_neg.
  unfold z_add.
  do 2 rewrite -> z_reduce_pos.
  do 2 rewrite -> z_reduce_neg.
  rewrite -> add_comm.
  rewrite -> z_eqv_0_is_same.
  reflexivity.
Qed.

Proposition z_additive_inverse_r : forall a : Z, a + (-- a) ~= (NZ#0).
Proof.
  intros a.
  rewrite -> z_add_comm.
  apply z_additive_inverse_l.
Qed.

Proposition z_mult_comm : forall a b : Z, a * b = b * a.
Proof.
  intros [a_ _a] [b_ _b].
  unfold z_mult.
  do 2 rewrite -> z_reduce_pos.
  do 2 rewrite -> z_reduce_neg.
  rewrite -> (mult_comm _a _b).
  rewrite -> (mult_comm a_ b_).
  rewrite -> (add_comm (a_ * _b) (_a * b_)).
  rewrite -> (mult_comm _a b_).
  rewrite -> (mult_comm a_ _b).
  reflexivity.
Qed.

Proposition z_mult_assoc : forall a b c : Z, (a * b) * c = a * (b * c).
Proof.
  intros [a_ _a] [b_ _b] [c_ _c].
  unfold z_mult.
  do 5 rewrite -> z_reduce_pos.
  do 5 rewrite -> z_reduce_neg.
  do 4 rewrite -> mult_dist_over_add_r.
  do 4 rewrite -> mult_dist_over_add.
  do 8 rewrite <- mult_assoc.
  do 4 rewrite -> z_0_pad_pos_l.
  do 9 rewrite -> (add_assoc).
  rewrite -> add_comm_8_a0_swap_a5.
  rewrite -> add_comm_8_a0_swap_a3.
  rewrite -> add_comm_8_a0_swap_a7.
  rewrite -> add_comm_8_a0_swap_a2.
  rewrite -> add_comm_8_a0_swap_a6.
  rewrite -> add_comm_8_a0_swap_a1.
  rewrite -> add_comm_8_a0_swap_a4.
  do 4 rewrite -> add_0_r.
  do 4 rewrite -> z_0_pad_neg_l.
  do 6 rewrite -> (add_assoc).
  rewrite -> add_comm_8_a0_swap_a5.
  rewrite -> add_comm_8_a0_swap_a3.
  rewrite -> add_comm_8_a0_swap_a7.
  rewrite -> add_comm_8_a0_swap_a2.
  rewrite -> add_comm_8_a0_swap_a6.
  rewrite -> add_comm_8_a0_swap_a1.
  rewrite -> add_comm_8_a0_swap_a4.
  do 4 rewrite -> add_0_r.
  reflexivity.
Qed.

Proposition z_mult_ident_l : forall a : Z, (NZ#1) * a = a.
Proof.
  intros [a_ _a].
  unfold NZ.
  unfold z_mult.
  do 2 rewrite -> z_reduce_pos.
  do 2 rewrite -> z_reduce_neg.
  do 2 rewrite -> mult_ident.
  do 2 rewrite -> def_mult_clause_0.
  do 2 rewrite -> add_0_r.
  reflexivity.
Qed.

Proposition z_mult_ident_r : forall a : Z, a * (NZ#1) = a.
Proof.
  intros a.
  rewrite -> z_mult_comm.
  apply z_mult_ident_l.
Qed.

Proposition z_mult_dist_over_add_l : forall a b c : Z, a * (b + c) = (a * b) + (a * c).
Proof.
  intros [a_ _a] [b_ _b] [c_ _c].
  unfold z_mult.
  unfold z_add.
  do 6 rewrite -> z_reduce_pos.
  do 6 rewrite -> z_reduce_neg.
  do 4 rewrite -> mult_dist_over_add.
  do 4 rewrite -> add_assoc.
  do 4 rewrite -> z_0_pad_pos_l.
  do 6 rewrite -> (add_assoc).
  rewrite -> add_comm_8_a0_swap_a7.
  rewrite -> add_comm_8_a0_swap_a3.
  rewrite -> add_comm_8_a0_swap_a5.
  rewrite -> add_comm_8_a0_swap_a2.
  rewrite -> add_comm_8_a0_swap_a6.
  rewrite -> add_comm_8_a0_swap_a1.
  rewrite -> add_comm_8_a0_swap_a4.
  do 4 rewrite -> add_0_r.
  do 4 rewrite -> z_0_pad_neg_l.
  do 6 rewrite -> (add_assoc).
  rewrite -> add_comm_8_a0_swap_a7.
  rewrite -> add_comm_8_a0_swap_a3.
  rewrite -> add_comm_8_a0_swap_a5.
  rewrite -> add_comm_8_a0_swap_a2.
  rewrite -> add_comm_8_a0_swap_a6.
  rewrite -> add_comm_8_a0_swap_a1.
  rewrite -> add_comm_8_a0_swap_a4.
  do 4 rewrite -> add_0_r.
  reflexivity.
Qed.

Proposition z_mult_dist_over_add_r : forall a b c : Z, (b + c) * a = (b * a) + (c * a).
Proof.
  intros a b c.
  rewrite -> (z_mult_comm (b + c) a).
  rewrite -> (z_mult_comm b a).
  rewrite -> (z_mult_comm c a).
  apply z_mult_dist_over_add_l.
Qed.

(*\end{Z is a commutative ring}*)

Definition z_sub (a b : Z) : Z :=
  a + (-- b).

Notation "x - y" := (z_sub x y) (at level 50, left associativity) : Z_scope.

Require Import Stdlib.Classes.Morphisms.
Instance z_sub_proper : 
  Proper (z_eq ==> z_eq ==> z_eq ) z_sub.
Proof.
  intros a a' Ha b b' Hb.
  unfold z_sub.
  rewrite -> Ha.
  rewrite -> Hb.
  reflexivity.
Qed.

Proposition z_sub_refold : forall a b : Z, a + (-- b) = a - b.
Proof.
  intros a b.
  unfold z_sub.
  reflexivity.
Qed.

Proposition z_mult_0_l : forall a : Z, (NZ#0) * a = (NZ#0).
Proof.
  intros [a_ _a].
  unfold NZ.
  unfold z_mult.
  do 2 rewrite -> z_reduce_pos.
  do 2 rewrite -> z_reduce_neg.
  do 2 rewrite -> def_mult_clause_0.
  rewrite -> def_add_clause_0.
  reflexivity.
Qed.

Proposition z_mult_0_r : forall a : Z, a * (NZ#0) = (NZ#0).
Proof.
  intros a.
  rewrite -> z_mult_comm.
  apply z_mult_0_l.
Qed.

Proposition z_mult_no_zero_div : forall a b : Z, 
  (a * b ~= (NZ#0)) <-> (a ~= (NZ#0) \/ b ~= (NZ#0)).
Proof.
  intros a b.
  split.
  {
    intros H0.
    destruct (z_trichotomy_3 a) as [Heqa | [Hgta | Hlta]].
    {
      left.
      exact Heqa.
    }
    {
      destruct Hgta as [p0 [Hp0 Hp0u]].
      destruct (z_trichotomy_3 b) as [Heqb | [Hgtb | Hltb]].
      {
        right.
        exact Heqb.
      }
      {
        destruct Hgtb as [p1 [Hp1 Hp1u]].
        rewrite -> Hp0 in H0.
        rewrite -> Hp1 in H0.
        unfold NZ in H0.
        unfold z_mult in H0.
        unfold z_eq in H0.
        do 4 rewrite z_reduce_pos in H0.
        do 4 rewrite z_reduce_neg in H0.
        do 2 rewrite -> def_mult_clause_0 in H0.
        do 3 rewrite -> add_0_r in H0.
        rewrite -> mult_0_r in H0.
        rewrite -> def_add_clause_0 in H0.
        discriminate.
      }
      {
        destruct Hltb as [p1 [Hp1 Hp1u]].
        rewrite -> Hp0 in H0.
        rewrite -> Hp1 in H0.
        unfold NZ in H0.
        unfold z_neg in H0.
        unfold z_mult in H0.
        unfold z_eq in H0.
        do 5 rewrite z_reduce_pos in H0.
        do 5 rewrite z_reduce_neg in H0.
        do 2 rewrite -> def_mult_clause_0 in H0.
        rewrite -> mult_0_r in H0.
        do 3 rewrite -> add_0_r in H0.
        rewrite -> def_add_clause_0 in H0.
        discriminate.
      }
    }
    {
      destruct Hlta as [p0 [Hp0 Hp0u]].
      rewrite -> Hp0 in H0.
      destruct (z_trichotomy_3 b) as [Heqb | [Hgtb | Hltb]].
      {
        right.
        exact Heqb.
      }
      {
        destruct Hgtb as [p1 [Hp1 Hp1u]].
        rewrite -> Hp1 in H0.
        unfold NZ in H0.
        unfold z_neg in H0.
        unfold z_mult in H0.
        unfold z_eq in H0.
        do 5 rewrite z_reduce_pos in H0.
        do 5 rewrite z_reduce_neg in H0.
        do 2 rewrite -> def_mult_clause_0 in H0.
        rewrite -> add_0_r in H0.
        rewrite -> mult_0_r in H0.
        do 3 rewrite -> def_add_clause_0 in H0.
        discriminate.
      }
      {
        destruct Hltb as [p1 [Hp1 Hp1u]].
        rewrite -> Hp1 in H0.
        unfold NZ in H0.
        unfold z_neg in H0.
        unfold z_mult in H0.
        unfold z_eq in H0.
        do 6 rewrite z_reduce_pos in H0.
        do 6 rewrite z_reduce_neg in H0.
        do 2 rewrite -> def_mult_clause_0 in H0.
        rewrite -> mult_0_r in H0.
        do 2 rewrite -> add_0_r in H0.
        rewrite -> def_add_clause_0 in H0.
        discriminate.
      }
    }
  }
  {
    intros H0.
    destruct H0 as [H0l | H0r].
    {
      rewrite -> H0l.
      rewrite -> z_mult_0_l.
      reflexivity.
    }
    {
      rewrite -> H0r.
      rewrite -> z_mult_0_r.
      reflexivity.
    }
  }
Qed.

Proposition z_mult_cancel_r : forall a b c : Z, 
  (a * c ~= b * c) -> (c ~= (NZ#0) -> False) -> a ~= b.
Proof.
  intros a b c H0 H1.
  destruct (z_trichotomy_3 c) as [Heqc | [Hgtc | Hltc]].
  {
    exfalso.
    apply H1.
    exact Heqc.
  }
  {
    destruct Hgtc as [p0 [Hp0 Hp0u]].
    clear H1 Hp0u.
    rewrite -> Hp0 in H0.
    unfold NZ in H0.
    unfold z_eq in H0.
    unfold z_mult in H0.
    do 3 rewrite -> z_reduce_pos in H0.
    do 3 rewrite -> z_reduce_neg in H0.
    do 4 rewrite -> mult_0_r in H0.
    do 2 rewrite -> add_0_r in H0.
    do 2 rewrite -> def_add_clause_0 in H0.
    do 2 rewrite <- mult_dist_over_add_r in H0.
    apply mult_cancel_r in H0.
    destruct H0 as [H0l | H0r].
    {
      unfold z_eq.
      exact H0l.
    }
    {
      discriminate.
    }
  }
  {
    destruct Hltc as [p0 [Hp0 Hp0u]].
    clear H1 Hp0u.
    rewrite -> Hp0 in H0.
    unfold NZ in H0.
    unfold z_neg in H0.
    unfold z_eq in H0.
    unfold z_mult in H0.
    do 4 rewrite -> z_reduce_pos in H0.
    do 4 rewrite -> z_reduce_neg in H0.
    do 4 rewrite -> mult_0_r in H0.
    do 2 rewrite -> add_0_r in H0.
    do 2 rewrite -> def_add_clause_0 in H0.
    do 2 rewrite <- mult_dist_over_add_r in H0.
    apply mult_cancel_r in H0.
    destruct H0 as [H0l | H0r].
    {
      unfold z_eq.
      symmetry.
      rewrite -> (add_comm (pos b) (neg a)).
      rewrite -> (add_comm (pos a) (neg b)).
      exact H0l.
    }
    {
      discriminate.
    }
  }
Qed.

Proposition z_mult_cancel_l : forall a b c : Z, 
  (c * a ~= c * b) -> (c ~= (NZ#0) -> False) -> a ~= b.
Proof.
  intros a b c.
  rewrite -> (z_mult_comm c a).
  rewrite -> (z_mult_comm c b).
  apply z_mult_cancel_r.
Qed.

Proposition z_mult_cancel_r_2 : 
  forall (a b c : Z) (Hnzc : c ~= (NZ#0) -> False), 
  (a * c ~= b * c) <-> a ~= b.
Proof.
  intros a b c Hnzc.
  split.
  {
    intros H0.
    apply z_mult_cancel_r in H0.
    2: exact Hnzc.
    exact H0.
  }
  {
    intros H0.
    rewrite -> H0.
    reflexivity.
  }
Qed.

Proposition z_mult_cancel_l_2 : 
  forall (a b c : Z) (Hnzc : c ~= (NZ#0) -> False), 
  (c * a ~= c * b) <-> a ~= b.
Proof.
  intros a b c Hnzc.
  rewrite -> (z_mult_comm c a).
  rewrite -> (z_mult_comm c b).
  apply z_mult_cancel_r_2.
  exact Hnzc.
Qed.

Proposition z_mult_cancel_r_3 : forall a b c : Z, 
  (a * c ~= b * c) <-> ((c ~= (NZ#0)) \/ a ~= b).
Proof.
  intros a b c.
  split.
  {
    intros H0.
    destruct (z_trichotomy_3 c) as [Hzc | [Hpc | Hnc]].
    {
      left.
      exact Hzc.
    }
    {
      apply (z_trichotomy_1 c) in Hpc as [Hnzc Hnnc].
      apply z_mult_cancel_r_2 in H0.
      2: exact Hnzc.
      right.
      exact H0.
    }
    {
      apply (z_trichotomy_2 c) in Hnc as [Hnzc Hnpc].
      apply z_mult_cancel_r_2 in H0.
      2: exact Hnzc.
      right.
      exact H0.
    }
  }
  {
    intros [H0l | H0r].
    {
      rewrite -> H0l.
      do 2 rewrite -> z_mult_0_r.
      reflexivity.
    }
    {
      rewrite -> H0r.
      reflexivity.
    }
  }
Qed.

Proposition z_mult_cancel_l_3 : forall a b c : Z, 
  (c * a ~= c * b) <-> ((c ~= (NZ#0)) \/ a ~= b).
Proof.
  intros a b c.
  rewrite -> (z_mult_comm c a).
  rewrite -> (z_mult_comm c b).
  apply z_mult_cancel_r_3.
Qed.

Proposition z_add_cancel_r : forall a b c : Z,
  (a + c ~= b + c) <-> (a ~= b).
Proof.
  intros [a_ _a] [b_ _b] [c_ _c].
  split.
  {
    intros H0.
    unfold z_add in *.
    unfold z_eq in *.
    do 5 rewrite -> z_reduce_pos in *.
    do 5 rewrite -> z_reduce_neg in *.
    rewrite -> (add_comm a_ c_) in H0.
    rewrite -> (add_comm b_ c_) in H0.
    do 2 rewrite <- add_assoc in H0.
    apply -> add_cancel in H0.
    do 2 rewrite -> add_assoc in H0.
    apply -> add_cancel_r in H0.
    exact H0.
  }
  {
    intros H0.
    rewrite -> H0.
    reflexivity.
  }
Qed.

Proposition z_add_cancel_l : forall a b c : Z,
  (c + a ~= c + b) <-> (a ~= b).
Proof.
  intros a b c.
  rewrite -> (z_add_comm c a).
  rewrite -> (z_add_comm c b).
  apply z_add_cancel_r.
Qed.

Proposition z_sub_same_eqv_0 : forall a : Z, a - a ~= (NZ#0).
Proof.
  intros a.
  unfold z_sub.
  rewrite -> z_additive_inverse_r.
  reflexivity.
Qed.


Proposition z_sub_same_r_eq_a : forall a b : Z, a + b - b ~= a.
Proof.
  intros a b.
  unfold z_sub.
  rewrite -> z_add_assoc.
  rewrite -> z_additive_inverse_r.
  rewrite -> z_add_0_r.
  reflexivity.
Qed.

Proposition z_mov_neg_r_to_rhs : forall a b c : Z, (a - b ~= c) <-> (a ~= c + b).
Proof.
  intros a b c.
  split.
  {
    intros H0.
    apply <- (z_add_cancel_r (a - b) c b) in H0.
    unfold z_sub in H0.
    rewrite -> z_add_assoc in H0.
    rewrite -> z_additive_inverse_l in H0.
    rewrite -> z_add_0_r in H0.
    exact H0.
  }
  {
    intros H0.
    rewrite -> H0.
    unfold z_sub.
    rewrite -> z_add_assoc.
    rewrite -> z_additive_inverse_r.
    rewrite -> z_add_0_r.
    reflexivity.
  }
Qed.

Proposition z_mult_reduce_pos_pos : forall a b : nat,
  (NZ# (S a)) * (NZ# (S b)) ~= (NZ# (S a) * (S b)).
Proof.
  intros a b.
  unfold NZ.
  unfold z_mult.
  unfold z_eq.
  do 4 rewrite -> z_reduce_pos.
  do 4 rewrite -> z_reduce_neg.
  do 2 rewrite -> def_mult_clause_0.
  rewrite -> mult_0_r.
  rewrite -> def_add_clause_0.
  do 2 rewrite -> add_0_r.
  reflexivity.
Qed.

Proposition z_mult_reduce_neg_neg : forall a b : nat,
  (-- (NZ# (S a))) * (-- (NZ# (S b))) ~= (NZ# (S a) * (S b)).
Proof.
  intros a b.
  unfold NZ.
  unfold z_neg.
  unfold z_mult.
  unfold z_eq.
  do 6 rewrite -> z_reduce_pos.
  do 6 rewrite -> z_reduce_neg.
  do 2 rewrite -> def_mult_clause_0.
  rewrite -> mult_0_r.
  rewrite -> def_add_clause_0.
  do 2 rewrite -> add_0_r.
  reflexivity.
Qed.

Proposition z_mult_reduce_pos_neg : forall a b : nat,
  (NZ# (S a)) * (-- (NZ# (S b))) ~= (-- (NZ# (S a) * (S b))).
Proof.
  intros a b.
  unfold NZ.
  unfold z_neg.
  unfold z_mult.
  unfold z_eq.
  do 6 rewrite -> z_reduce_pos.
  do 6 rewrite -> z_reduce_neg.
  do 2 rewrite -> def_mult_clause_0.
  rewrite -> mult_0_r.
  do 2 rewrite -> def_add_clause_0.
  rewrite -> add_0_r.
  reflexivity.
Qed.

Proposition z_mult_reduce_neg_pos : forall a b : nat,
  (-- NZ# (S a)) * ((NZ# (S b))) ~= (-- (NZ# (S a) * (S b))).
Proof.
  intros a b.
  unfold NZ.
  unfold z_neg.
  unfold z_mult.
  unfold z_eq.
  do 6 rewrite -> z_reduce_pos.
  do 6 rewrite -> z_reduce_neg.
  do 2 rewrite -> def_mult_clause_0.
  rewrite -> mult_0_r.
  do 3 rewrite -> def_add_clause_0.
  reflexivity.
Qed.

Proposition z_mult_reduce_non_neg : forall a b : nat,
  (NZ# a) * (NZ# b) ~= (NZ# a * b).
Proof.
  intros a b.
  unfold z_mult.
  unfold z_eq.
  simpl.
  do 3 rewrite -> add_0_r.
  do 1 rewrite -> mult_0_r.
  do 1 rewrite -> add_0_r.
  reflexivity.
Qed.

Proposition z_add_reduce_pos_pos : forall a b : nat,
  (NZ# (S a)) + (NZ# (S b)) = (NZ# (S a) + (S b)).
Proof.
  intros a b.
  unfold NZ.
  unfold z_add.
  do 2 rewrite -> z_reduce_pos.
  do 2 rewrite -> z_reduce_neg.
  rewrite -> def_add_clause_0.
  reflexivity.
Qed.

Proposition z_add_reduce_non_neg : forall a b : nat,
  (NZ# a) + (NZ# b) = (NZ# a + b).
Proof.
  easy.
Qed.

Proposition z_formal_sub_as_sub : forall (a b : nat),
  {| pos := a; neg := b |} ~= (NZ#a) - (NZ#b).
Proof.
  intros a b.
  unfold z_eq.
  simpl.
  rewrite -> add_0_r.
  reflexivity.
Qed.

Proposition z_add_assoc_middle : forall a b c d : Z, a + b + c + d ~= a + (b + c) + d.
Proof.
  intros a b c d.
  repeat rewrite -> z_add_assoc.
  do 2 apply z_add_cancel_l.
  rewrite -> z_add_comm.
  reflexivity.
Qed.

Proposition z_neg_reduce_neg_0 : (-- (NZ# 0)) = (NZ# 0).
Proof.
  unfold NZ.
  unfold z_neg.
  rewrite -> z_reduce_pos.
  rewrite -> z_reduce_neg.
  reflexivity.
Qed.

Proposition z_sub_reduce_0_r : forall a : Z, (a - (NZ#0) ~= a)%Z.
Proof.
  intros [a b].
  unfold z_sub.
  rewrite -> z_neg_reduce_neg_0.
  rewrite -> z_add_0_r.
  reflexivity.
Qed.

Proposition z_neg_extract_from_sub_neg_l : forall a b : nat, 
  ((-- NZ#a) - (NZ#b)) ~= (-- (NZ# a + b)).
Proof.
  intros a b.
  unfold z_neg.
  unfold z_eq.
  simpl.
  reflexivity.
Qed.

Proposition z_neg_mov_rhs_to_lhs : forall a b : Z, (a ~= -- b)%Z <-> (a + b ~= (NZ#0)).
Proof.
  intros a b.
  split.
  {
    intros H0.
    rewrite -> H0.
    rewrite -> z_additive_inverse_l.
    reflexivity.
  }
  {
    intros H0.
    rewrite -> z_neg_both_sides in H0.
    rewrite -> z_neg_dist_over_add in H0.
    rewrite -> z_add_comm in H0.
    rewrite -> z_neg_reduce_neg_0 in H0.
    rewrite -> z_sub_refold in H0.
    rewrite -> z_mov_neg_r_to_rhs in H0.
    rewrite -> z_add_0_l in H0.
    symmetry in H0.
    exact H0.
  }
Qed.

Proposition def_z_neg : forall a b : nat, 
  (-- {| pos := a; neg := b |}) = {| pos := b; neg := a |}.
Proof.
  intros a b.
  easy.
Qed.

Proposition z_neg_extract_from_mult_l : forall a b : Z, (-- a) * b ~= (-- (a * b)).
Proof.
  intros [a_ _a] [b_ _b].
  unfold z_neg.
  unfold z_mult.
  unfold z_eq.
  do 6 rewrite -> z_reduce_pos.
  do 6 rewrite -> z_reduce_neg.
  repeat rewrite -> add_assoc.
  rewrite -> (add_comm (a_ * _b) (_a * b_)).
  repeat rewrite <- add_assoc.
  apply add_cancel.
  apply add_cancel.
  rewrite -> (add_comm (_a * _b) (a_ * b_)).
  apply add_cancel.
  reflexivity.
Qed.

Proposition z_neg_extract_from_mult_r : forall a b : Z, a * (-- b) ~= (-- (a * b)).
Proof.
  intros a b.
  rewrite -> (z_mult_comm a (-- b)).
  rewrite -> (z_mult_comm a b).
  apply z_neg_extract_from_mult_l.
Qed.

Proposition z_neg_inject : forall a b : Z, a ~= b <-> (-- a) ~= (-- b).
Proof.
  intros [a_ _a] [b_ _b].
  split.
  {
    intros H0.
    rewrite -> H0.
    reflexivity.
  }
  {
    intros H0.
    unfold z_neg in *.
    unfold z_eq in *.
    do 4 rewrite -> z_reduce_pos in *.
    do 4 rewrite -> z_reduce_neg in *.
    rewrite -> (add_comm _b a_) in H0.
    symmetry in H0.
    rewrite -> H0.
    rewrite -> (add_comm _a b_).
    reflexivity.
  }
Qed.

Proposition z_mult_rem_pos_implies_pos : forall (a : Z) (b c : nat), 
  (a * (NZ#S(b)) ~= (NZ#S(c)))%Z -> exists ! k : nat, a ~= (NZ#S(k)).
Proof.
  intros a b c H0.
  destruct (z_trichotomy_3 a) as [Hza | [Hpa | Hna]].
  {
    rewrite -> Hza in H0.
    rewrite -> z_mult_0_l in H0.
    discriminate.
  }
  {
    destruct Hpa as [p0 [Hp0 _]].
    exists (p0).
    split.
    {
      exact Hp0.
    }
    {
      intros x' Hx'.
      rewrite -> Hp0 in Hx'.
      rewrite -> z_nz_inject in Hx'.
      injection Hx' as Hx'.
      exact Hx'.
    }
  }
  {
    destruct Hna as [p0 [Hp0 _]].
    rewrite -> Hp0 in H0.
    rewrite -> z_neg_extract_from_mult_l in H0.
    symmetry in H0.
    rewrite -> z_mult_reduce_pos_pos in H0.
    apply z_pos_ne_neg in H0.
    contradiction H0.
  }
Qed.

(* TODO
Proposition z_mult_rem_unsigned_must_be_non_pos_1 : forall (a : Z) (b c : nat), 
  (a * (NZ#b) ~= (-- NZ#c))%Z -> exists ! k : nat, a ~= (-- NZ#k).
Proof.
  intros [a b] c d H0.
  destruct (z_trichotomy_3 {| pos := a; neg := b |}) as [Hz | [Hp | Hn]].
  {
    exists (0).
    split.
    {
      exact Hz.
    }
    {
      intros x' Hx'.
      rewrite -> Hz in Hx'.
      rewrite -> z_neg_both_sides in Hx'.
      rewrite -> z_neg_reduce_neg_0 in Hx'.
      rewrite -> z_neg_reduce_double in Hx'.
      rewrite -> z_nz_inject in Hx'.
      exact Hx'.
    }
  }
  {
    destruct Hp as [p0 [Hp0 _]].
    rewrite -> Hp0 in H0.
    rewrite -> z_mult_reduce_non_neg in H0.
    rewrite -> z_pos_ne_neg

    destruct c as [| c'].
    {
      rewrite ->

    }
    {

    }
  }
  {

  }

Qed.
*)

Proposition z_mult_rhs_neg_part_neg : forall (a : Z) (b c : nat), 
  (a * (NZ#S(b)) ~= (-- (NZ#S(c))))%Z -> exists ! k : nat, a ~= (-- (NZ#S(k))).
Proof.
  intros a b c H0.
  destruct (z_trichotomy_3 a) as [Hza | [Hpa | Hna]].
  {
    rewrite -> Hza in H0.
    rewrite -> z_mult_0_l in H0.
    discriminate.
  }
  {
    destruct Hpa as [p0 [Hp0 _]].
    rewrite -> Hp0 in H0.
    rewrite -> z_mult_reduce_pos_pos in H0.
    apply z_pos_ne_neg in H0.
    contradiction H0.
  }
  {
    destruct Hna as [p0 [Hp0 _]].
    rewrite -> Hp0 in H0.
    exists (p0).
    split.
    {
      exact Hp0.
    }
    {
      intros x' Hx'.
      rewrite -> Hp0 in Hx'.
      rewrite <- z_neg_inject in Hx'.
      rewrite -> z_nz_inject in Hx'.
      injection Hx' as Hx'.
      exact Hx'.
    }
  }
Qed.

Proposition z_add_from_two_equations : forall a b c d : Z, 
  (a ~= b) -> (c ~= d) -> (a + c ~= b + d).
Proof.
  intros a b c d H0 H1.
  rewrite -> H0.
  rewrite -> H1.
  reflexivity.
Qed.

Proposition z_cross_add_from_two_equations : forall a b c d : Z, 
  (a ~= b) -> (c ~= d) -> (a + d ~= b + c).
Proof.
  intros a b c d H0 H1.
  rewrite -> H0.
  rewrite -> H1.
  reflexivity.
Qed.

Proposition z_mult_from_two_equations : forall a b c d : Z, 
  (a ~= b) -> (c ~= d) -> (a * c ~= b * d).
Proof.
  intros a b c d H0 H1.
  rewrite -> H0.
  rewrite -> H1.
  reflexivity.
Qed.

Proposition z_cross_mult_from_two_equations : forall a b c d : Z, 
  (a ~= b) -> (c ~= d) -> (a * d ~= b * c).
Proof.
  intros a b c d H0 H1.
  rewrite -> H0.
  rewrite -> H1.
  reflexivity.
Qed.

(*\begin{Z comm}*)

Proposition z_mult_assoc_8_a1_a2 : forall a0 a1 a2 a3 a4 a5 a6 a7 : Z, 
  a0 * a1 * a2 * a3 * a4 * a5 * a6 * a7 = a0 * (a1 * a2) * a3 * a4 * a5 * a6 * a7.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  repeat rewrite -> z_mult_assoc.
  reflexivity.
Qed.

Proposition z_mult_assoc_8_a2_a3 : forall a0 a1 a2 a3 a4 a5 a6 a7 : Z, 
  a0 * a1 * a2 * a3 * a4 * a5 * a6 * a7 = a0 * a1 * (a2 * a3) * a4 * a5 * a6 * a7.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  repeat rewrite -> z_mult_assoc.
  reflexivity.
Qed.

Proposition z_mult_assoc_8_a3_a4 : forall a0 a1 a2 a3 a4 a5 a6 a7 : Z, 
  a0 * a1 * a2 * a3 * a4 * a5 * a6 * a7 = a0 * a1 * a2 * (a3 * a4) * a5 * a6 * a7.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  repeat rewrite -> z_mult_assoc.
  reflexivity.
Qed.

Proposition z_mult_assoc_8_a4_a5 : forall a0 a1 a2 a3 a4 a5 a6 a7 : Z, 
  a0 * a1 * a2 * a3 * a4 * a5 * a6 * a7 = a0 * a1 * a2 * a3 * (a4 * a5) * a6 * a7.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  repeat rewrite -> z_mult_assoc.
  reflexivity.
Qed.

Proposition z_mult_assoc_8_a5_a6 : forall a0 a1 a2 a3 a4 a5 a6 a7 : Z, 
  a0 * a1 * a2 * a3 * a4 * a5 * a6 * a7 = a0 * a1 * a2 * a3 * a4 * (a5 * a6) * a7.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  repeat rewrite -> z_mult_assoc.
  reflexivity.
Qed.

Proposition z_mult_comm_8_a0_swap_a1 : forall a0 a1 a2 a3 a4 a5 a6 a7 : Z, 
  a0 * a1 * a2 * a3 * a4 * a5 * a6 * a7 = a1 * a0 * a2 * a3 * a4 * a5 * a6 * a7.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  rewrite -> (z_mult_comm _ a0).
  reflexivity.
Qed.

Proposition z_mult_comm_8_a0_swap_a2 : forall a0 a1 a2 a3 a4 a5 a6 a7 : Z, 
  a0 * a1 * a2 * a3 * a4 * a5 * a6 * a7 = a2 * a1 * a0 * a3 * a4 * a5 * a6 * a7.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_assoc_8_a1_a2.
  rewrite -> (z_mult_comm a0 _).
  rewrite <- z_mult_assoc.
  rewrite -> (z_mult_comm a1 _).
  reflexivity.
Qed.

Proposition z_mult_comm_8_a0_swap_a3 : forall a0 a1 a2 a3 a4 a5 a6 a7 : Z, 
  a0 * a1 * a2 * a3 * a4 * a5 * a6 * a7 = a3 * a1 * a2 * a0 * a4 * a5 * a6 * a7.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_assoc_8_a1_a2.
  rewrite -> (z_mult_comm a0 _).
  rewrite <- z_mult_assoc.
  rewrite -> z_mult_assoc_8_a2_a3.
  rewrite -> (z_mult_comm a0 _).
  rewrite <- z_mult_assoc.
  rewrite -> z_mult_assoc_8_a1_a2.
  rewrite -> (z_mult_comm _ a3).
  rewrite <- z_mult_assoc.
  rewrite -> (z_mult_comm _ a3).
  reflexivity.
Qed.

Proposition z_mult_comm_8_a0_swap_a4 : forall a0 a1 a2 a3 a4 a5 a6 a7 : Z, 
  a0 * a1 * a2 * a3 * a4 * a5 * a6 * a7 = a4 * a1 * a2 * a3 * a0 * a5 * a6 * a7.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  rewrite -> z_mult_assoc_8_a3_a4.
  rewrite -> (z_mult_comm a0 _).
  rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  reflexivity.
Qed.

Proposition z_mult_comm_8_a0_swap_a5 : forall a0 a1 a2 a3 a4 a5 a6 a7 : Z, 
  a0 * a1 * a2 * a3 * a4 * a5 * a6 * a7 = a5 * a1 * a2 * a3 * a4 * a0 * a6 * a7.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  rewrite -> z_mult_assoc_8_a4_a5.
  rewrite -> (z_mult_comm a0 _).
  rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  reflexivity.
Qed.

Proposition z_mult_comm_8_a0_swap_a6 : forall a0 a1 a2 a3 a4 a5 a6 a7 : Z, 
  a0 * a1 * a2 * a3 * a4 * a5 * a6 * a7 = a6 * a1 * a2 * a3 * a4 * a5 * a0 * a7.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  rewrite -> z_mult_assoc_8_a5_a6.
  rewrite -> (z_mult_comm a0 _).
  rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  reflexivity.
Qed.
    
Proposition z_mult_comm_8_a0_swap_a7 : forall a0 a1 a2 a3 a4 a5 a6 a7 : Z, 
  a0 * a1 * a2 * a3 * a4 * a5 * a6 * a7 = a7 * a1 * a2 * a3 * a4 * a5 * a6 * a0.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  repeat rewrite -> z_mult_assoc.
  rewrite -> (z_mult_comm a0 _).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  reflexivity.
Qed.

Proposition z_mult_comm_acbd : forall a b c d : Z, a * b * c * d = a * c * b * d.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_bacd : forall a b c d : Z, a * b * c * d = b * a * c * d.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_bcad : forall a b c d : Z, a * b * c * d = b * c * a * d.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_cabd : forall a b c d : Z, a * b * c * d = c * a * b * d.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_cbad : forall a b c d : Z, a * b * c * d = c * b * a * d.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_abdc : forall a b c d : Z, a * b * c * d = a * b * d * c.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_acdb : forall a b c d : Z, a * b * c * d = a * c * d * b.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_badc : forall a b c d : Z, a * b * c * d = b * a * d * c.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_bcda : forall a b c d : Z, a * b * c * d = b * c * d * a.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_cadb : forall a b c d : Z, a * b * c * d = c * a * d * b.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_cbda : forall a b c d : Z, a * b * c * d = c * b * d * a.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_adbc : forall a b c d : Z, a * b * c * d = a * d * b * c.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_adcb : forall a b c d : Z, a * b * c * d = a * d * c * b.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_bdac : forall a b c d : Z, a * b * c * d = b * d * a * c.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_bdca : forall a b c d : Z, a * b * c * d = b * d * c * a.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_cdab : forall a b c d : Z, a * b * c * d = c * d * a * b.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_cdba : forall a b c d : Z, a * b * c * d = c * d * b * a.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_dabc : forall a b c d : Z, a * b * c * d = d * a * b * c.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_dacb : forall a b c d : Z, a * b * c * d = d * a * c * b.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_dbac : forall a b c d : Z, a * b * c * d = d * b * a * c.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_dbca : forall a b c d : Z, a * b * c * d = d * b * c * a.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_dcab : forall a b c d : Z, a * b * c * d = d * c * a * b.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

Proposition z_mult_comm_dcba : forall a b c d : Z, a * b * c * d = d * c * b * a.
Proof.
  intros a b c d.
  do 4 rewrite <- (z_mult_ident_l (a * b * c * d)).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a4.
  rewrite -> z_mult_comm_8_a0_swap_a3.
  rewrite -> z_mult_comm_8_a0_swap_a5.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  do 4 rewrite -> (z_mult_ident_r).
  reflexivity.
Qed.

(*\end{Z comm}*)


Definition z_ge (a b : Z) : Prop :=
  exists! k : nat, a ~= b + (NZ#k).

Notation "x >= y" := (z_ge x y) (at level 70) : Z_scope.

Definition z_gt (a b : Z) : Prop :=
(a >= b) /\ (a ~= b -> False).

Notation "x > y" := (z_gt x y) (at level 70) : Z_scope.

Proposition z_gt_as_pos_diff : forall a b : Z, 
  (a > b) <-> (exists ! k : nat, a - b ~= (NZ#S(k))).
Proof.
  intros a b.
  split.
  {
    intros H0.
    unfold z_gt in H0.
    destruct H0 as [[p0 [Hp0 Hp0u]] H0r].
    destruct p0 as [| p0'].
    {
      rewrite -> z_add_0_r in Hp0.
      contradiction H0r.
    }
    {
      (*
      assert ( Hexists : forall k : nat, a - b ~= NZ# S k ).
      {
        intros k.
        rewrite -> Hp0.
        rewrite -> z_add_comm.
        unfold z_sub.
        rewrite -> z_add_assoc.
        rewrite -> z_additive_inverse_r.
        rewrite -> z_add_0_r.
        (* Goal : NZ# S p0' ~= NZ# S k *)
      }
      *)
      exists p0'.
      split.
      {
        rewrite -> Hp0.
        rewrite -> z_add_comm.
        unfold z_sub.
        rewrite -> z_add_assoc.
        rewrite -> z_additive_inverse_r.
        rewrite -> z_add_0_r.
        reflexivity.
      }
      {
        intros x' Hx'.
        rewrite -> Hp0 in Hx'.
        (* v Hx' : b + (NZ# S p0') - b ~= NZ# S x' *)
        rewrite -> z_add_comm in Hx'.
        unfold z_sub in Hx'.
        rewrite -> z_add_assoc in Hx'.
        rewrite -> z_additive_inverse_r in Hx'.
        rewrite -> z_add_0_r in Hx'.
        injection Hx' as Hx'.
        do 2 rewrite -> add_0_r in Hx'.
        (* ^ Hx' : p0' = x' *)
        exact Hx'.
      }
    }
  }
  {
    intros [p0 [Hp0 Hp0u]].
    unfold z_gt.
    unfold z_ge.
    split.
    {
      apply -> (z_mov_neg_r_to_rhs) in Hp0.
      (*
      assert (Hexists : forall k : nat, a ~= b + (NZ# k)).
      {
        intros k.
        rewrite -> Hp0.
        rewrite -> z_add_comm.
        (* Goal: b + (NZ# S p0) ~= b + (NZ# k) *)
      }
      *)
      exists (S p0).
      split.
      {
        rewrite -> Hp0.
        rewrite -> z_add_comm.
        reflexivity.
      }
      {
        intros x' Hx'.
        rewrite -> Hp0 in Hx'.
        rewrite -> z_add_comm in Hx'.
        apply -> z_add_cancel_l in Hx'.
        apply -> z_nz_inject in Hx'.
        exact Hx'.
      }
    }
    {
      intros H0.
      rewrite -> H0 in Hp0.
      rewrite -> z_sub_same_eqv_0 in Hp0.
      discriminate.
    }
  }
Qed.

Proposition z_add_preserves_ord : forall a b c : Z, (a > b) <-> (a + c > b + c).
Proof.
  intros a b c.
  split.
  {
    intros H0.
    rewrite -> z_gt_as_pos_diff in *.
    destruct H0 as [p0 [Hp0 Hp0u]].
    apply -> (z_mov_neg_r_to_rhs) in Hp0.
    (*
    assert (Hexists : forall k : nat, a + c - (b + c) ~= NZ# S k).
    {
      intros k.
      rewrite -> Hp0.
      rewrite -> z_add_assoc.
      unfold z_sub.
      rewrite -> z_add_assoc.
      rewrite -> z_additive_inverse_r.
      rewrite -> z_add_0_r.
      rewrite -> z_nz_inject.
      (* Goal : S p0 = S k *)
    }
    *)
    exists p0.
    split.
    {
      rewrite -> Hp0.
      rewrite -> z_add_assoc.
      unfold z_sub.
      rewrite -> z_add_assoc.
      rewrite -> z_additive_inverse_r.
      rewrite -> z_add_0_r.
      rewrite -> z_nz_inject.
      reflexivity.
    }
    {
      intros x' Hx'.
      rewrite -> Hp0 in Hx'.
      rewrite -> z_add_assoc in Hx'.
      unfold z_sub in Hx'.
      rewrite -> z_add_assoc in Hx'.
      rewrite -> z_additive_inverse_r in Hx'.
      rewrite -> z_add_0_r in Hx'.
      rewrite -> z_nz_inject in Hx'.
      injection Hx' as Hx'.
      exact Hx'.
    }
  }
  {
    intros H0.
    rewrite -> z_gt_as_pos_diff in *.
    destruct H0 as [p0 [Hp0 Hp0u]].
    (* v Hp0 : a + c - (b + c) ~= NZ# S p0 *)
    unfold z_sub in Hp0.
    rewrite -> z_neg_dist_over_add in Hp0.
    rewrite -> (z_add_comm (-- b) (-- c)) in Hp0.
    rewrite <- z_add_assoc in Hp0.
    apply -> z_mov_neg_r_to_rhs in Hp0.
    rewrite -> z_add_assoc in Hp0.
    rewrite -> z_additive_inverse_r in Hp0.
    rewrite -> z_add_0_r in Hp0.
    (* ^ Hp0 : a ~= (NZ# S p0) + b *)
    (*
    assert (Hexists : forall k : nat, a - b ~= NZ# S k ).
    {
      intros k.
      rewrite -> Hp0.
      rewrite -> z_sub_same_r_eq_a.
      rewrite -> z_nz_inject.
      (* Goal : S p0 = S k *)
    }
    *)
    exists p0.
    split.
    {
      rewrite -> Hp0.
      rewrite -> z_sub_same_r_eq_a.
      rewrite -> z_nz_inject.
      reflexivity.
    }
    {
      intros x' Hx'.
      rewrite -> Hp0 in Hx'.
      rewrite -> z_sub_same_r_eq_a in Hx'.
      rewrite -> z_nz_inject in Hx'.
      injection Hx' as Hx'.
      exact Hx'.
    }
  }
Qed.

Proposition z_pos_mult_preserves_ord : forall a b c : Z, 
  (a > b) -> (exists ! k : nat, c ~= (NZ#(S k))) -> (a*c > b*c).
Proof.
  intros a b c H0 H1.
  apply z_gt_as_pos_diff.
  apply -> z_gt_as_pos_diff in H0.
  destruct H0 as [p0 [Hp0 Hp0u]].
  destruct H1 as [p1 [Hp1 Hp1u]].
  clear Hp0u Hp1u.
  rewrite -> z_mov_neg_r_to_rhs in Hp0.
  (*
  assert (Hexists : forall k : nat, a * c - b * c ~= NZ# S k).
  {
    intros k.
    rewrite -> Hp0.
    rewrite -> Hp1.
    rewrite -> z_mult_dist_over_add_r.
    rewrite -> z_sub_same_r_eq_a.
    rewrite -> z_mult_reduce_pos_pos.
    rewrite -> z_nz_inject.
    rewrite -> def_mult_clause_1.
    rewrite -> def_add_clause_1.
    (* Goal : S (p1 + p0 * S p1) = S k *)
  }
  *)
  exists (p1 + (p0 * (S p1)))%nat.
  split.
  {
    rewrite -> Hp0.
    rewrite -> Hp1.
    rewrite -> z_mult_dist_over_add_r.
    rewrite -> z_sub_same_r_eq_a.
    rewrite -> z_mult_reduce_pos_pos.
    rewrite -> z_nz_inject.
    rewrite -> def_mult_clause_1.
    rewrite -> def_add_clause_1.
    reflexivity.
  }
  {
    intros x' Hx'.
    rewrite -> Hp0 in Hx'.
    rewrite -> Hp1 in Hx'.
    rewrite -> z_mult_dist_over_add_r in Hx'.
    rewrite -> z_sub_same_r_eq_a in Hx'.
    rewrite -> z_mult_reduce_pos_pos in Hx'.
    rewrite -> z_nz_inject in Hx'.
    rewrite -> def_mult_clause_1 in Hx'.
    rewrite -> def_add_clause_1 in Hx'.
    injection Hx' as Hx'.
    exact Hx'.
  }
Qed.

Proposition z_neg_reverses_ord : forall a b : Z, (a > b) <-> ((-- b) > (-- a)).
Proof.
  intros a b.
  split.
  {
    intros H0.
    apply -> z_gt_as_pos_diff in H0.
    apply z_gt_as_pos_diff.
    destruct H0 as [p0 [Hp0 _]].
    rewrite -> z_mov_neg_r_to_rhs in Hp0.
    (*
    assert (Hexists : forall k : nat, -- b - -- a ~= NZ# S k).
    {
      intros k.
      rewrite -> Hp0.
      unfold z_sub.
      rewrite -> z_neg_reduce_double.
      rewrite <- z_add_assoc.
      rewrite -> z_add_comm.
      rewrite <- z_add_assoc.
      rewrite -> z_additive_inverse_r.
      rewrite -> z_add_0_l.
      rewrite -> z_nz_inject.
      (* Goal : S p0 = S k *)
    }
    *)
    exists p0.
    split.
    {
      rewrite -> Hp0.
      unfold z_sub.
      rewrite -> z_neg_reduce_double.
      rewrite <- z_add_assoc.
      rewrite -> z_add_comm.
      rewrite <- z_add_assoc.
      rewrite -> z_additive_inverse_r.
      rewrite -> z_add_0_l.
      rewrite -> z_nz_inject.
      reflexivity.
    }
    {
      intros x' Hx'.
      rewrite -> Hp0 in Hx'.
      unfold z_sub in Hx'.
      rewrite -> z_neg_reduce_double in Hx'.
      rewrite <- z_add_assoc in Hx'.
      rewrite -> z_add_comm in Hx'.
      rewrite <- z_add_assoc in Hx'.
      rewrite -> z_additive_inverse_r in Hx'.
      rewrite -> z_add_0_l in Hx'.
      rewrite -> z_nz_inject in Hx'.
      injection Hx' as Hx'.
      exact Hx'.
    }
  }
  {
    intros H0.
    apply z_gt_as_pos_diff.
    apply z_gt_as_pos_diff in H0.
    destruct H0 as [p0 [Hp0 _]].
    unfold z_sub in Hp0.
    rewrite -> z_neg_reduce_double in Hp0.
    rewrite -> z_add_comm in Hp0.
    rewrite -> z_sub_refold in Hp0.
    rewrite -> z_mov_neg_r_to_rhs in Hp0.
    (*
    assert (Hexists : forall k : nat, a - b ~= NZ# S k).
    {
      intros k.
      rewrite -> Hp0.
      rewrite -> z_sub_same_r_eq_a.
      rewrite -> z_nz_inject.
      (* Goal : S p0 = S k *)
    }
    *)
    exists p0.
    split.
    {
      rewrite -> Hp0.
      rewrite -> z_sub_same_r_eq_a.
      rewrite -> z_nz_inject.
      reflexivity.
    }
    {
      intros x' Hx'.
      rewrite -> Hp0 in Hx'.
      rewrite -> z_sub_same_r_eq_a in Hx'.
      rewrite -> z_nz_inject in Hx'.
      injection Hx' as Hx'.
      exact Hx'.
    }
  }
Qed.

Proposition z_ord_trans : forall a b c : Z, (a > b) -> (b > c) -> (a > c).
Proof.
  intros a b c H0 H1.
  apply z_gt_as_pos_diff in H0.
  apply z_gt_as_pos_diff in H1.
  apply z_gt_as_pos_diff.
  destruct H0 as [p0 [Hp0 _]].
  destruct H1 as [p1 [Hp1 _]].
  rewrite -> z_mov_neg_r_to_rhs in Hp0.
  (* v Hp1 : b - c ~= NZ# S p1 *)
  rewrite -> z_neg_both_sides in Hp1.
  unfold z_sub in Hp1.
  rewrite -> z_neg_dist_over_add in Hp1.
  rewrite -> z_add_comm in Hp1.
  rewrite -> z_neg_reduce_double in Hp1.
  rewrite -> z_sub_refold in Hp1.
  rewrite -> z_mov_neg_r_to_rhs in Hp1.
  rewrite -> z_add_comm in Hp1.
  rewrite -> z_sub_refold in Hp1.
  (* ^ Hp1 : c ~= b - (NZ# S p1) *)
  (*
  assert (Hexists : forall k : nat, a - c ~= NZ# S k).
  {
    intros k.
    rewrite -> Hp0.
    rewrite -> Hp1.
    unfold z_sub.
    rewrite -> z_neg_dist_over_add.
    rewrite -> z_neg_reduce_double.
    rewrite <- z_add_assoc.
    rewrite -> z_add_assoc_middle.
    rewrite -> z_additive_inverse_r.
    rewrite -> z_add_0_r.
    rewrite -> z_add_reduce_pos_pos.
    rewrite -> def_add_clause_1.
    rewrite -> z_nz_inject.
    (* Goal : S (p0 + S p1) = S k *)
  }
  *)
  exists (p0 + (S p1))%nat.
  split.
  {
    rewrite -> Hp0.
    rewrite -> Hp1.
    unfold z_sub.
    rewrite -> z_neg_dist_over_add.
    rewrite -> z_neg_reduce_double.
    rewrite <- z_add_assoc.
    rewrite -> z_add_assoc_middle.
    rewrite -> z_additive_inverse_r.
    rewrite -> z_add_0_r.
    rewrite -> z_add_reduce_pos_pos.
    rewrite -> def_add_clause_1.
    rewrite -> z_nz_inject.
    reflexivity.
  }
  {
    intros x' Hx'.
    rewrite -> Hp0 in Hx'.
    rewrite -> Hp1 in Hx'.
    unfold z_sub in Hx'.
    rewrite -> z_neg_dist_over_add in Hx'.
    rewrite -> z_neg_reduce_double in Hx'.
    rewrite <- z_add_assoc in Hx'.
    rewrite -> z_add_assoc_middle in Hx'.
    rewrite -> z_additive_inverse_r in Hx'.
    rewrite -> z_add_0_r in Hx'.
    rewrite -> z_add_reduce_pos_pos in Hx'.
    rewrite -> def_add_clause_1 in Hx'.
    rewrite -> z_nz_inject in Hx'.
    injection Hx' as Hx'.
    exact Hx'.
  }
Qed.

Proposition z_ord_trichotomy_0 : forall a b : Z, 
  (a ~= b) -> (((a > b) -> False) /\ ((b > a) -> False)).
Proof.
  intros a b H0.
  split.
  {
    intros H1.
    apply z_gt_as_pos_diff in H1.
    destruct H1 as [p0 [Hp0 _]].
    rewrite -> H0 in Hp0.
    rewrite -> z_sub_same_eqv_0 in Hp0.
    discriminate.
  }
  {
    intros H1.
    apply z_gt_as_pos_diff in H1.
    destruct H1 as [p0 [Hp0 _]].
    rewrite -> H0 in Hp0.
    rewrite -> z_sub_same_eqv_0 in Hp0.
    discriminate.
  }
Qed.

Proposition z_ord_trichotomy_1 : forall a b : Z,
  (a > b) -> (((a ~= b) -> False) /\ ((b > a) -> False)).
Proof.
  intros a b H0.
  split.
  {
    intros H1.
    assert (H2 : (a > b) -> False).
    {
      apply z_ord_trichotomy_0.
      symmetry.
      exact H1.
    }
    contradiction H2.
  }
  {
    intros H1.
    rewrite z_gt_as_pos_diff in *.
    destruct H0 as [p0 [Hp0 _]].
    destruct H1 as [p1 [Hp1 _]].
    rewrite -> z_mov_neg_r_to_rhs in Hp0.
    rewrite -> Hp0 in Hp1.
    unfold z_sub in Hp1.
    rewrite -> z_neg_dist_over_add in Hp1.
    rewrite -> z_add_comm in Hp1.
    rewrite -> z_add_assoc in Hp1.
    rewrite -> z_additive_inverse_l in Hp1.
    rewrite -> z_add_0_r in Hp1.
    discriminate.
  }
Qed.

Proposition z_ord_trichotomy_2 : forall a b : Z,
  (b > a) -> (((a ~= b) -> False) /\ ((a > b) -> False)).
Proof.
  intros a b H0.
  split.
  {
    intros H1.
    apply z_gt_as_pos_diff in H0.
    destruct H0 as [p0 [Hp0 _]].
    rewrite -> H1 in Hp0.
    rewrite -> z_sub_same_eqv_0 in Hp0.
    discriminate.
  }
  {
    apply (z_ord_trichotomy_1 b a).
    exact H0.
  }
Qed.

Proposition z_ord_trichotomy_3 : forall a b : Z,
  (a ~= b) \/ (a > b) \/ (b > a).
Proof.
  intros a b.
  destruct (z_trichotomy_3 a) as [Hza | [Hpa | Hma]].
  {
    destruct (z_trichotomy_3 b) as [Hzb | [Hpb | Hmb]].
    {
      left.
      rewrite -> Hza.
      rewrite -> Hzb.
      reflexivity.
    }
    {
      destruct Hpb as [p0 [Hp0 _]].
      right; right.
      apply z_gt_as_pos_diff.
      (*
      assert (Hexists : forall k : nat, b - a ~= NZ# S k).
      {
        (* ... *)
        (* Goal : S p0 = S k *)
      }
      *)
      exists p0.
      split.
      {
        rewrite -> Hza.
        unfold z_sub.
        rewrite -> z_neg_reduce_neg_0.
        rewrite -> z_add_0_r.
        rewrite -> Hp0.
        rewrite -> z_nz_inject.
        reflexivity.
      }
      {
        intros x' Hx'.
        rewrite -> Hza in Hx'.
        unfold z_sub in Hx'.
        rewrite -> z_neg_reduce_neg_0 in Hx'.
        rewrite -> z_add_0_r in Hx'.
        rewrite -> Hp0 in Hx'.
        rewrite -> z_nz_inject in Hx'.
        injection Hx' as Hx'.
        exact Hx'.
      }
    }
    {
      destruct Hmb as [p0 [Hp0 _]].
      right; left.
      apply z_gt_as_pos_diff.
      (*
      assert (Hexists : forall k : nat, a - b ~= NZ# S k).
      {
        (* ... *)
        (* Goal : S p0 = S k *)
      }
      *)
      exists p0.
      split.
      {
        rewrite -> Hza.
        rewrite -> Hp0.
        unfold z_sub.
        rewrite -> z_neg_reduce_double.
        rewrite -> z_add_0_l.
        rewrite -> z_nz_inject.
        reflexivity.
      }
      {
        intros x' Hx'.
        rewrite -> Hza in Hx'.
        rewrite -> Hp0 in Hx'.
        unfold z_sub in Hx'.
        rewrite -> z_neg_reduce_double in Hx'.
        rewrite -> z_add_0_l in Hx'.
        rewrite -> z_nz_inject in Hx'.
        injection Hx' as Hx'.
        exact Hx'.
      }
    }
  }
  {
    destruct (z_trichotomy_3 b) as [Hzb | [Hpb | Hnb]].
    {
      right; left.
      apply z_gt_as_pos_diff.
      destruct Hpa as [p0 [Hp0 _]].
      (*
      assert (Hexists : forall k : nat, a - b ~= NZ# S k).
      {
        (* ... *)
        (* Goal : S p0 = S k *)
      }
      *)
      exists p0.
      split.
      {
        rewrite -> Hp0.
        rewrite -> Hzb.
        unfold z_sub.
        rewrite -> z_neg_reduce_neg_0.
        rewrite -> z_add_0_r.
        rewrite -> z_nz_inject.
        reflexivity.
      }
      {
        intros x' Hx'.
        rewrite -> Hp0 in Hx'.
        rewrite -> Hzb in Hx'.
        unfold z_sub in Hx'.
        rewrite -> z_neg_reduce_neg_0 in Hx'.
        rewrite -> z_add_0_r in Hx'.
        rewrite -> z_nz_inject in Hx'.
        injection Hx' as Hx'.
        exact Hx'.
      }
    }
    {
      destruct Hpa as [p0 [Hp0 _]].
      destruct Hpb as [p1 [Hp1 _]].
      destruct (nat_ord_trichotomy_3 p0 p1) as [Heq | [Hgt | Hlt]].
      {
        rewrite <- Heq in Hp1.
        left.
        rewrite -> Hp0.
        rewrite -> Hp1.
        reflexivity.
      }
      {
        apply gt_as_ge_succ in Hgt.
        unfold ge in Hgt.
        destruct Hgt as [p2 [Hp2 _]].
        right; left.
        apply z_gt_as_pos_diff.
        rewrite -> Hp2 in Hp0.
        (*
        assert (Hexists : forall k : nat, a - b ~= NZ# S k).
        {
          (* ... *)
          (* Goal : S (S p1 + p2) = S (S p1 + k) *)
        }
        *)
        exists p2.
        split.
        {
          rewrite -> Hp0.
          rewrite -> Hp1.
          apply z_mov_neg_r_to_rhs.
          rewrite -> z_add_reduce_pos_pos.
          rewrite -> z_nz_inject.
          rewrite -> (def_add_clause_1 p2 (S p1)).
          rewrite -> (add_comm p2 (S p1)).
          reflexivity.
        }
        {
          intros x' Hx'.
          rewrite -> Hp0 in Hx'.
          rewrite -> Hp1 in Hx'.
          apply z_mov_neg_r_to_rhs in Hx'.
          rewrite -> z_add_reduce_pos_pos in Hx'.
          rewrite -> z_nz_inject in Hx'.
          rewrite -> (def_add_clause_1 x' (S p1)) in Hx'.
          rewrite -> (add_comm x' (S p1)) in Hx'.
          injection Hx' as Hx'.
          apply add_cancel in Hx'.
          exact Hx'.
        }
      }
      {
        right; right.
        apply gt_as_ge_succ in Hlt.
        unfold ge in Hlt.
        destruct Hlt as [p2 [Hp2 _]].
        apply z_gt_as_pos_diff.
        rewrite -> Hp2 in Hp1.
        clear Hp2.
        (*
        assert (Hexists : forall k : nat, b - a ~= NZ# S k).
        {
          (* ... *)
          (* Goal : S (p2 + S p0) = S (k + S p0) *)
        }
        *)
        exists p2.
        split.
        {
          rewrite -> z_mov_neg_r_to_rhs.
          rewrite -> Hp1.
          rewrite -> Hp0.
          rewrite -> z_add_reduce_pos_pos.
          rewrite -> (def_add_clause_1 p2 (S p0)).
          rewrite -> z_nz_inject.
          rewrite -> add_comm.
          reflexivity.
        }
        {
          intros x' Hx'.
          rewrite -> z_mov_neg_r_to_rhs in Hx'.
          rewrite -> Hp1 in Hx'.
          rewrite -> Hp0 in Hx'.
          rewrite -> z_add_reduce_pos_pos in Hx'.
          rewrite -> (def_add_clause_1 x' (S p0)) in Hx'.
          rewrite -> z_nz_inject in Hx'.
          rewrite -> add_comm in Hx'.
          injection Hx' as Hx'.
          apply add_cancel_r in Hx'.
          exact Hx'.
        }
      }
    }
    {
      right; left.
      apply z_gt_as_pos_diff.
      destruct Hpa as [p0 [Hp0 _]].
      destruct Hnb as [p1 [Hp1 _]].
      (*
      assert (Hexists : forall k : nat, a - b ~= NZ# S k).
      {
        (* ... *)
        (* Goal : S (p0 + S p1) = S k *)
      }
      *)
      exists (p0 + (S p1))%nat.
      split.
      {
        rewrite -> Hp0.
        rewrite -> Hp1.
        unfold z_sub.
        rewrite -> z_neg_reduce_double.
        rewrite -> z_add_reduce_pos_pos.
        rewrite -> z_nz_inject.
        rewrite -> def_add_clause_1.
        reflexivity.
      }
      {
        intros x' Hx'.
        rewrite -> Hp0 in Hx'.
        rewrite -> Hp1 in Hx'.
        unfold z_sub in Hx'.
        rewrite -> z_neg_reduce_double in Hx'.
        rewrite -> z_add_reduce_pos_pos in Hx'.
        rewrite -> z_nz_inject in Hx'.
        rewrite -> def_add_clause_1 in Hx'.
        injection Hx' as Hx'.
        exact Hx'.
      }
    }
  }
  {
    destruct Hma as [p0 [Hp0 _]].
    destruct (z_trichotomy_3 b) as [Hzb | [Hpb | Hmb]].
    {
      right; right.
      apply z_gt_as_pos_diff.
      (*
      assert (Hexists : forall k : nat, b - a ~= NZ# S k).
      {
        (* ... *)
        (* Goal : S p0 = S k *)
      }
      *)
      exists p0.
      split.
      {
        rewrite -> Hp0.
        rewrite -> Hzb.
        unfold z_sub.
        rewrite -> z_neg_reduce_double.
        rewrite -> z_add_0_l.
        rewrite -> z_nz_inject.
        reflexivity.
      }
      {
        intros x' Hx'.
        rewrite -> Hp0 in Hx'.
        rewrite -> Hzb in Hx'.
        unfold z_sub in Hx'.
        rewrite -> z_neg_reduce_double in Hx'.
        rewrite -> z_add_0_l in Hx'.
        rewrite -> z_nz_inject in Hx'.
        injection Hx' as Hx'.
        exact Hx'.
      }
    }
    {
      right; right.
      destruct Hpb as [p1 [Hp1 _]].
      apply z_gt_as_pos_diff.
      (*
      assert (Hexists : forall k : nat, b - a ~= NZ# S k).
      {
        (* ... *)
        (* Goal : S (p1 + S p0) = S k *)
      }
      *)
      exists (p1 + (S p0))%nat.
      split.
      {
        rewrite -> Hp0.
        rewrite -> Hp1.
        unfold z_sub.
        rewrite -> z_neg_reduce_double.
        rewrite -> z_add_reduce_pos_pos.
        rewrite -> z_nz_inject.
        rewrite -> def_add_clause_1.
        reflexivity.
      }
      {
        intros x' Hx'.
        rewrite -> Hp0 in Hx'.
        rewrite -> Hp1 in Hx'.
        unfold z_sub in Hx'.
        rewrite -> z_neg_reduce_double in Hx'.
        rewrite -> z_add_reduce_pos_pos in Hx'.
        rewrite -> z_nz_inject in Hx'.
        rewrite -> def_add_clause_1 in Hx'.
        injection Hx' as Hx'.
        exact Hx'.
      }
    }
    {
      destruct Hmb as [p1 [Hp1 _]].
      destruct (nat_ord_trichotomy_3 p0 p1) as [Heq | [Hgt | Hlt]].
      {
        left.
        rewrite -> Hp0.
        rewrite -> Hp1.
        rewrite -> Heq.
        reflexivity.
      }
      {
        right; right.
        apply z_gt_as_pos_diff.
        rewrite gt_as_ge_succ in Hgt.
        unfold ge in Hgt.
        destruct Hgt as [p2 [Hp2 _]].
        (*
        assert (Hexists : forall k : nat, b - a ~= NZ# S k).
        {
          (* ... *)
          (* Goal : S (p2 + S p1) = S (k + S p1) *)
        }
        *)
        exists p2.
        split.
        {
          rewrite -> Hp0.
          rewrite -> Hp1.
          unfold z_sub.
          rewrite -> z_neg_reduce_double.
          rewrite -> z_add_comm.
          rewrite -> z_sub_refold.
          rewrite -> z_mov_neg_r_to_rhs.
          rewrite -> Hp2.
          rewrite -> z_add_reduce_pos_pos.
          rewrite -> z_nz_inject.
          rewrite -> (def_add_clause_1 p2 (S p1)).
          rewrite -> add_comm.
          reflexivity.
        }
        {
          intros x' Hx'.
          rewrite -> Hp0 in Hx'.
          rewrite -> Hp1 in Hx'.
          unfold z_sub in Hx'.
          rewrite -> z_neg_reduce_double in Hx'.
          rewrite -> z_add_comm in Hx'.
          rewrite -> z_sub_refold in Hx'.
          rewrite -> z_mov_neg_r_to_rhs in Hx'.
          rewrite -> Hp2 in Hx'.
          rewrite -> z_add_reduce_pos_pos in Hx'.
          rewrite -> z_nz_inject in Hx'.
          rewrite -> (def_add_clause_1 x' (S p1)) in Hx'.
          rewrite -> add_comm in Hx'.
          injection Hx' as Hx'.
          apply -> add_cancel_r.
          exact Hx'.
        }
      }
      {
        apply gt_as_ge_succ in Hlt.
        unfold ge in Hlt.
        destruct Hlt as [p2 [Hp2 _]].
        right; left.
        apply z_gt_as_pos_diff.
        (*
        assert (Hexists : forall k : nat, a - b ~= NZ# S k).
        {
          (* ... *)
          (* Goal : S (p2 + S p0) = S (k + S p0) *)
        }
        *)
        exists p2.
        split.
        {
          rewrite -> Hp0.
          rewrite -> Hp1.
          rewrite -> Hp2.
          unfold z_sub.
          rewrite -> z_neg_reduce_double.
          rewrite -> z_add_comm.
          rewrite -> z_sub_refold.
          rewrite -> z_mov_neg_r_to_rhs.
          rewrite -> z_add_reduce_pos_pos.
          rewrite -> z_nz_inject.
          rewrite -> (def_add_clause_1 p2 (S p0)).
          rewrite -> add_comm.
          reflexivity.
        }
        {
          intros x' Hx'.
          rewrite -> Hp0 in Hx'.
          rewrite -> Hp1 in Hx'.
          rewrite -> Hp2 in Hx'.
          unfold z_sub in Hx'.
          rewrite -> z_neg_reduce_double in Hx'.
          rewrite -> z_add_comm in Hx'.
          rewrite -> z_sub_refold in Hx'.
          rewrite -> z_mov_neg_r_to_rhs in Hx'.
          rewrite -> z_add_reduce_pos_pos in Hx'.
          rewrite -> z_nz_inject in Hx'.
          rewrite -> (def_add_clause_1 x' (S p0)) in Hx'.
          rewrite -> add_comm in Hx'.
          injection Hx' as Hx'.
          apply add_cancel_r in Hx'.
          exact Hx'.
        }
      }
    }
  }
Qed.

Fixpoint z_pexp (a : Z) (b : nat) : Z :=
  match b with
  | 0 => (NZ#1)
  | (S b') => (z_mult a (z_pexp a b'))
  end.

Notation "x ** y" := (z_pexp x y) (at level 45) : Z_scope.

Require Import Stdlib.Classes.Morphisms.
Instance z_pexp_proper : 
  Proper (z_eq ==> eq ==> z_eq ) z_pexp.
Proof.
  intros a a_ Ha b b_ Hb.
  rewrite <- Hb.
  generalize dependent b_.
  induction b as [| b' IHb'].
  {
    simpl.
    reflexivity.
  }
  {
    intros b_ H0.
    simpl.
    symmetry in H0.
    destruct b_ as [| b_'].
    {
      discriminate.
    }
    {
      injection H0 as H0.
      symmetry in H0.
      assert (H1 : a ** b'  ~= a_ ** b').
      {
        apply (IHb' b_' H0).
      }
      rewrite -> H1.
      rewrite -> Ha.
      reflexivity.
    }
  }
Qed.

Proposition z_pexp_respects_equivilence : forall a a' : Z, forall b b' : nat,
  a ~= a' -> b = b' -> a ** b ~= a' ** b'.
Proof.
  intros a a' b b' H0 H1.
  rewrite -> H0.
  rewrite -> H1.
  reflexivity.
Qed.

Proposition def_z_pexp_clause_0 : forall a : Z, a ** 0 = (NZ#1).
Proof.
  intros a.
  simpl.
  reflexivity.
Qed.

Proposition def_z_pexp_clause_1 : forall a : Z, forall b : nat, a ** (S b) = a * (a ** b).
Proof.
  intros a.
  simpl.
  reflexivity.
Qed.

Proposition z_pexp_same_mult_is_square : forall a : Z, a * a = a ** 2.
Proof.
  intros a.
  do 2 rewrite -> def_z_pexp_clause_1.
  rewrite -> def_z_pexp_clause_0.
  rewrite -> z_mult_ident_r.
  reflexivity.
Qed.

Proposition z_square_is_non_neg : forall a : Z, exists ! k : nat, a ** 2 ~= (NZ#k).
Proof.
  intros a.
  destruct (z_trichotomy_3 a) as [Hza | [Hpa | Hna]].
  {
    (*
    assert (Hexists : forall k : nat, a ** 2 ~= NZ# k).
    {
      (* ... *)
      (* Goal : 0 = k *)
    }
    *)
    exists 0.
    split.
    {
      rewrite -> Hza.
      rewrite <- z_pexp_same_mult_is_square.
      rewrite -> z_mult_0_l.
      rewrite -> z_nz_inject.
      reflexivity.
    }
    {
      intros x' Hx'.
      rewrite -> Hza in Hx'.
      rewrite <- z_pexp_same_mult_is_square in Hx'.
      rewrite -> z_mult_0_l in Hx'.
      rewrite -> z_nz_inject in Hx'.
      exact Hx'.
    }
  }
  {
    destruct Hpa as [p0 [Hp0 _]].
    (*
    assert (Hexists : forall k : nat, a ** 2 ~= NZ# k).
    {
      (* ... *)
      (* Goal : (S p0 * S p0)%nat = k *)
    }
    *)
    exists ((S p0) * (S p0))%nat.
    split.
    {
      rewrite -> Hp0.
      rewrite <- z_pexp_same_mult_is_square.
      rewrite -> z_mult_reduce_pos_pos.
      rewrite -> z_nz_inject.
      reflexivity.
    }
    {
      intros x' Hx'.
      rewrite -> Hp0 in Hx'.
      rewrite <- z_pexp_same_mult_is_square in Hx'.
      rewrite -> z_mult_reduce_pos_pos in Hx'.
      rewrite -> z_nz_inject in Hx'.
      exact Hx'.
    }
  }
  {
    destruct Hna as [p0 [Hp0 _]].
    (*
    assert (Hexists : forall k : nat, a ** 2 ~= NZ# k).
    {
      (* ... *)
      (* Goal : (S p0 * S p0)%nat = k *)
    }
    *)
    exists ((S p0) * (S p0))%nat.
    split.
    {
      rewrite -> Hp0.
      rewrite <- z_pexp_same_mult_is_square.
      rewrite -> z_mult_reduce_neg_neg.
      rewrite -> z_nz_inject.
      reflexivity.
    }
    {
      intros x' Hx'.
      rewrite -> Hp0 in Hx'.
      rewrite <- z_pexp_same_mult_is_square in Hx'.
      rewrite -> z_mult_reduce_neg_neg in Hx'.
      rewrite -> z_nz_inject in Hx'.
      exact Hx'.
    }
  }
Qed.

Close Scope Z_scope.

Definition Z_nz := { a : Z | (a ~= (NZ#0))%Z -> False }.

Declare Scope Z_nz_scope.
Bind Scope Z_nz_scope with Z_nz.
Delimit Scope Z_nz_scope with Z_nz.


(*This notation at least allows us to write with it*)

Notation Z_nz_ex := (exist (fun a : Z => ((a ~= (NZ#0))%Z -> False))).

(*
(*This notation cannot be written, only used by the system*)
Notation "(Z_nz_ex x y )" := (exist (fun a : Z => ((a ~= (NZ#0))%Z -> False)) x y) (at level 45).
*)


Definition z_nz_mult (a b : Z_nz) : Z_nz.
Proof.
  destruct a as [a Hnza].
  destruct b as [b Hnzb].
  exists (a * b)%Z.
  {
    intros H0.
    apply z_mult_no_zero_div in H0 as [H0l | H0r].
    {
      apply Hnza.
      exact H0l.
    }
    {
      apply Hnzb.
      exact H0r.
    }
  }
Defined.

Notation "x * y" := (z_nz_mult x y) (at level 40, left associativity) : Z_nz_scope.

Proposition z_nz_reduce_proj1_sig : forall 
  (a : Z) (Ha : ((a ~= (NZ#0))%Z -> False)),
  (proj1_sig (
    (exist (fun x => ((x ~= (NZ#0))%Z -> False)) a Ha) 
  )%Z_nz) = a.
Proof.
  intros a H.
  simpl.
  reflexivity.
Qed.

Proposition z_nz_reduce_add : forall a b : nat,
  ((NZ#a) + (NZ#b) ~= (NZ# a + b))%Z.
Proof.
  intros a b.
  unfold NZ, z_add, z_eq.
  simpl.
  rewrite -> add_0_r.
  reflexivity.
Qed.

Proposition z_nz_mult_reduce_proj1_sig : forall 
  (a b : Z) (Ha : ((a ~= (NZ#0))%Z -> False)) (Hb : ((b ~= (NZ#0))%Z -> False)), 
  (proj1_sig (
    (exist (fun x => ((x ~= (NZ#0))%Z -> False)) a Ha) * 
    (exist (fun x => ((x ~= (NZ#0))%Z -> False)) b Hb)
  )%Z_nz) = (a * b)%Z.
Proof.
  intros a H.
  simpl.
  reflexivity.
Qed.

Proposition z_nz_mult3_reduce_proj1_sig_assoc1 : forall 
  (a b c : Z) 
  (Ha : ((a ~= (NZ#0))%Z -> False))
  (Hb : ((b ~= (NZ#0))%Z -> False))
  (Hc : ((c ~= (NZ#0))%Z -> False)), 
  (proj1_sig (
    (exist (fun x => ((x ~= (NZ#0))%Z -> False)) a Ha) * 
    (exist (fun x => ((x ~= (NZ#0))%Z -> False)) b Hb) *
    (exist (fun x => ((x ~= (NZ#0))%Z -> False)) c Hc)
  )%Z_nz) = (a * b * c)%Z.
Proof.
  intros a H.
  simpl.
  reflexivity.
Qed.

Proposition z_nz_mult3_reduce_proj1_sig_assoc2 : forall 
  (a b c : Z) 
  (Ha : ((a ~= (NZ#0))%Z -> False))
  (Hb : ((b ~= (NZ#0))%Z -> False))
  (Hc : ((c ~= (NZ#0))%Z -> False)), 
  (proj1_sig (
    (exist (fun x => ((x ~= (NZ#0))%Z -> False)) a Ha) * 
    ((exist (fun x => ((x ~= (NZ#0))%Z -> False)) b Hb) *
    (exist (fun x => ((x ~= (NZ#0))%Z -> False)) c Hc))
  )%Z_nz) = (a * (b * c))%Z.
Proof.
  intros a H.
  simpl.
  reflexivity.
Qed.

Proposition z_mult_preserves_ne_z_1 : forall a b : nat,
  (((NZ#a) ~= (NZ#0))%Z -> False) /\ (((NZ#b) ~= (NZ#0))%Z -> False)
  <-> ((NZ#(a * b) ~= (NZ#0))%Z -> False).
Proof.
  intros a b.
  split.
  {
    intros [H0 H1] H2.
    destruct a as [| a'].
    {
      apply H0.
      reflexivity.
    }
    {
      destruct b as [| b'].
      {
        apply H1.
        reflexivity.
      }
      {
        discriminate.
      }
    }
  }
  {
    intros H0.
    split.
    {
      intros H1.
      apply H0. (* suffice to show this *)
      rewrite -> z_nz_inject in H1.
      rewrite -> H1.
      rewrite -> def_mult_clause_0.
      reflexivity.
    }
    {
      intros H1.
      apply H0.
      rewrite -> z_nz_inject in H1.
      rewrite -> H1.
      rewrite -> mult_0_r.
      reflexivity.
    }
  }
Qed.

Proposition z_mult_preserves_ne_z_2 : forall a b : Z,
  ((a ~= (NZ#0))%Z -> False) /\ ((b ~= (NZ#0))%Z -> False)
  <-> ((a * b ~= (NZ#0))%Z -> False).
Proof.
  intros a b.
  split.
  {
    intros [H0 H1] H2.
    apply z_mult_no_zero_div in H2 as [H2l | H2r].
    1: apply H0. exact H2l.
    1: apply H1. exact H2r.
  }
  {
    intros H0.
    split.
    {
      intros H1.
      rewrite -> H1 in H0.
      rewrite -> z_mult_0_l in H0.
      apply H0.
      reflexivity.
    }
    {
      intros H1.
      rewrite -> H1 in H0.
      rewrite -> z_mult_0_r in H0.
      apply H0.
      reflexivity.
    }
  }
Qed.

Proposition z_mult_preserves_ne_z_3 : forall a b : nat,
  (((NZ#a) ~= (NZ#0))%Z -> False) /\ (((NZ#b) ~= (NZ#0))%Z -> False)
  <-> (((NZ#a) * (NZ#b) ~= (NZ#0))%Z -> False).
Proof.
  intros a b.
  split.
  {
    intros [H0 H1] H2.
    destruct a as [| a'].
    {
      apply H0.
      reflexivity.
    }
    {
      destruct b as [| b'].
      {
        apply H1.
        reflexivity.
      }
      {
        rewrite -> z_mult_reduce_pos_pos in H2.
        discriminate.
      }
    }
  }
  {
    intros H0.
    split.
    {
      intros H1.
      apply H0. (* suffice to show this *)
      rewrite -> z_nz_inject in H1.
      rewrite -> H1.
      rewrite -> z_mult_reduce_non_neg.
      rewrite -> def_mult_clause_0.
      reflexivity.
    }
    {
      intros H1.
      apply H0.
      rewrite -> z_nz_inject in H1.
      rewrite -> H1.
      rewrite -> z_mult_reduce_non_neg.
      rewrite -> mult_0_r.
      reflexivity.
    }
  }
Qed.

Proposition z_mult_preserves_ne_z_succ : forall a b : nat,
  ((NZ#(S (b +  a * S b)) ~= (NZ#0))%Z -> False).
Proof.
  intros a b H0.
  discriminate.
Qed.


Proposition z_nz_mult_reduce : forall (a b : Z)
  (Ha : ((a ~= (NZ#0))%Z -> False))
  (Hb : ((b ~= (NZ#0))%Z -> False))
  (Hc : ((a * b ~= (NZ#0))%Z -> False)),
  (proj1_sig (((exist (fun x => ((x ~= (NZ#0))%Z -> False)) a Ha) * 
  (exist (fun x => ((x ~= (NZ#0))%Z -> False)) b Hb))%Z_nz)) = 
  (proj1_sig ((exist (fun x => ((x ~= (NZ#0))%Z -> False)) (a * b)%Z Hc))).
Proof.
  intros a b H0 H1 H2.
  simpl.
  reflexivity.
Qed.

Definition z_nz_1 : Z_nz.
Proof.
  exists (NZ#1)%Z.
  discriminate.
Defined.

Proposition z_nz_reduce_proj1_sig_for_1 : (proj1_sig z_nz_1) = (NZ# 1).
Proof.
  simpl.
  reflexivity.
Qed.

Proposition z_nz_mult_ident_l : forall a : Z_nz, (proj1_sig (z_nz_1 * a)%Z_nz) = (proj1_sig a).
Proof.
  intros [a Hnza].
  simpl.
  rewrite -> z_mult_ident_l.
  reflexivity.
Qed.

Proposition z_nz_mult_ident_r : forall a : Z_nz, (proj1_sig (a * z_nz_1)%Z_nz) = (proj1_sig a).
Proof.
  intros [a Hnza].
  simpl.
  rewrite -> z_mult_ident_r.
  reflexivity.
Qed.

(*\begin{Z extra}*)

Proposition z_mult_dist_over_sub_l : forall a b c : Z, (a * (b - c) ~= (a * b) - (a * c))%Z.
Proof.
  intros a b c.
  unfold z_sub.
  rewrite -> z_mult_dist_over_add_l.
  reflexivity.
Qed.

Proposition z_mult_dist_over_sub_r : forall a b c : Z, ((b - c) * a ~= (a * b) - (a * c))%Z.
Proof.
  intros a b c.
  unfold z_sub.
  rewrite -> z_mult_dist_over_add_r.
  rewrite -> (z_neg_extract_from_mult_l).
  rewrite -> (z_mult_comm b a).
  rewrite -> (z_mult_comm c a).
  reflexivity.
Qed.

Proposition z_mult_dist_over_sub_r_r : forall a b c : Z, ((b - c) * a ~= (b * a) - (c * a))%Z.
Proof.
  intros a b [c_ _c].
  unfold z_sub.
  rewrite -> z_mult_dist_over_add_r.
  rewrite <- z_neg_extract_from_mult_l.
  reflexivity.
Qed.

Proposition z_normal_form_sign_dichotomy : forall (z : Z), exists (a : nat),
  (z ~= (NZ#a))%Z \/ (z ~= (-- (NZ#a)))%Z.
Proof.
  intros [a b].
  destruct (nat_ord_trichotomy_3 a b) as [Heq | [Hgt | Hlt]].
  {
    exists (0).
    left. (* don't care *)
    rewrite -> Heq.
    rewrite -> z_same_parts_eqv_0.
    reflexivity.
  }
  {
    apply gt_as_ge_succ in Hgt.
    destruct Hgt as [p0 [Hp0 _]].
    rewrite -> add_swap_s in Hp0.
    exists (S p0).
    left.
    rewrite -> Hp0.
    rewrite -> z_reduce_shared_part_pos.
    reflexivity.
  }
  {
    apply gt_as_ge_succ in Hlt.
    destruct Hlt as [p0 [Hp0 _]].
    rewrite -> add_swap_s in Hp0.
    exists (S p0).
    right.
    rewrite -> Hp0.
    rewrite -> z_reduce_shared_part_neg.
    reflexivity.
  }
Qed.

Proposition z_sign_preserves_nz : forall (a : nat),
  (((NZ#a) ~= (NZ#0))%Z -> False) <-> (((-- (NZ#a)) ~= (NZ#0))%Z -> False).
Proof.
  intros a.
  split.
  {
    intros H0 H1.
    unfold z_neg in H1.
    unfold z_eq in H1.
    simpl in H1.
    destruct a as [| a'].
    {
      apply H0.
      reflexivity.
    }
    {
      discriminate.
    }
  }
  {
    intros H0 H1.
    destruct a as [| a'].
    {
      rewrite -> z_neg_reduce_neg_0 in H0.
      apply H0.
      reflexivity.
    }
    {
      discriminate.
    }
  }
Qed.

Proposition z_normal_form_preserves_nz_pos : forall (z : Z) (a : nat),
  (z ~= (NZ#a))%Z -> ((z ~= (NZ#0))%Z -> False)
  -> (((NZ#a) ~= (NZ#0))%Z -> False).
Proof.
  intros z a H0 H1 H2.
  rewrite -> H0 in H1.
  specialize (H1 H2).
  contradiction.
Qed.

Proposition z_normal_form_preserves_nz_neg : forall (z : Z) (a : nat),
  (z ~= (-- (NZ#a)))%Z -> ((z ~= (NZ#0))%Z -> False)
  -> (((NZ#a) ~= (NZ#0))%Z -> False).
Proof.
  intros z a H0 H1 H2.
  rewrite -> H0 in H1.
  specialize (z_sign_preserves_nz a) as H3.
  destruct H3 as [_ H3].
  specialize (H3 H1 H2).
  contradiction.
Qed.

Proposition z_pos_ne_0 : forall (a : nat), ((NZ#(S a)) ~= (NZ#0))%Z -> False.
Proof.
  intros a H0.
  apply -> z_nz_inject in H0.
  discriminate.
Qed.

(*\end{Z extra}*)