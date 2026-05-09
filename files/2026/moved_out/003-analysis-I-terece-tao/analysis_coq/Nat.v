Require Import CoqAnalysis.Misc.

Proposition nat_succ_inject : forall (a b : nat), (S a = S b) <-> (a = b).
Proof.
  intros a b.
  split.
  {
    intros H0.
    injection H0 as H0.
    exact H0.
  }
  {
    intros H0.
    rewrite -> H0.
    reflexivity.
  }
Qed.

Proposition ax_nat_succ_ne : forall n : nat, (S n) = n -> False.
Proof.
  intros n H0.
  induction n as [| n' IHn'].
  {
    discriminate H0.
  }
  {
    injection H0 as H1.
    apply IHn' in H1.
    contradiction H1.
  }
Qed.

Proposition ax_nat_zero_has_no_succ : forall n : nat, 0 = (S n) -> False.
Proof.
  intros n H0.
  discriminate H0.
Qed.

Proposition add_0_l : forall n : nat, 0 + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Proposition add_Sn_m : forall n m : nat, (S n) + m = S (n + m).
Proof.
  intros n m.
  simpl.
  reflexivity.
Qed.

Proposition add_0_r : forall n: nat, n + 0 = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  {
    rewrite -> add_0_l.
    reflexivity.
  }
  {
    rewrite -> add_Sn_m.
    rewrite -> IHn'.
    reflexivity.
  }
Qed.

Proposition add_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  {
    rewrite -> add_0_l.
    rewrite -> add_0_l.
    reflexivity.
  }
  {
    rewrite -> add_Sn_m.
    rewrite -> add_Sn_m.
    rewrite -> IHn'.
    reflexivity.
  }
Qed.

Proposition add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  {
    rewrite -> add_0_l.
    rewrite -> add_0_r.
    reflexivity.
  }
  {
    rewrite -> add_Sn_m.
    rewrite -> IHn'.
    rewrite <- add_n_Sm.
    reflexivity.
  }
Qed.

(* Print add_comm. *)

Proposition add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  {
    rewrite -> add_0_l.
    rewrite -> add_0_l.
    reflexivity.
  }
  {
    rewrite -> add_Sn_m.
    rewrite -> IHn'.
    rewrite -> add_Sn_m.
    rewrite <- add_Sn_m.
    reflexivity.
  }
Qed.

Proposition add_cancel : forall a b c : nat,
  a + b = a + c <-> b = c.
Proof.
  intros a b c.
  split.
  {
    intros H0.
    induction a as [| a' IHa'].
    {
      rewrite -> add_0_l in H0.
      rewrite -> add_0_l in H0.
      rewrite <- H0.
      reflexivity.
    }
    {
      rewrite -> add_Sn_m in H0.
      rewrite -> add_Sn_m in H0.
      injection H0 as H1.
      apply IHa' in H1.
      rewrite <- H1.
      reflexivity.
    }
  }
  {
    intros H0.
    rewrite -> H0.
    reflexivity.
  }
Qed.

Proposition add_cancel_r : forall a b c : nat, a + b = c + b <-> a = c.
Proof.
  intros a b c.
  rewrite -> (add_comm a b).
  rewrite -> (add_comm c b).
  apply add_cancel.
Qed.

Proposition add_cancel_2 : forall a b : nat,
a = a + b <-> 0 = b.
Proof.
  intros a b.
  split.
  {
    intros H0.
    rewrite <- (add_0_r a ) in H0.
    rewrite <- add_assoc in H0.
    rewrite -> (add_0_l b) in H0.
    apply add_cancel in H0.
    rewrite <- H0.
    reflexivity.
  }
  {
    intros H0.
    rewrite <- H0.
    rewrite -> add_0_r.
    reflexivity.
  }
Qed.

Proposition add_1_is_succ : forall a : nat, 1 + a = (S a).
Proof.
  induction a as [| a' IHa'].
  {
    rewrite -> add_0_r.
    reflexivity.
  }
  {
    rewrite <- add_n_Sm.
    rewrite -> IHa'.
    reflexivity.
  }
Qed.

Proposition add_assoc_middle : forall a b c d : nat, (a + b) + (c + d) = (a + (b + c)) + d.
Proof.
  intros a b c d.
  induction a as [| a' IHa'].
  {
    rewrite -> 2 add_0_l.
    apply add_assoc.
  }
  {
    rewrite -> 4 add_Sn_m.
    rewrite -> IHa'.
    reflexivity.
  }
Qed.

Proposition add_comm_acb : forall a b c : nat, a + b + c = a + c + b.
Proof.
  intros a b c.
  rewrite <- add_assoc.
  rewrite <- add_assoc.
  apply <- add_cancel.
  rewrite -> add_comm.
  reflexivity.
Qed.

Proposition add_comm_bac : forall a b c : nat, a + b + c = b + a + c.
Proof.
  intros a b c.
  rewrite -> (add_comm a b).
  reflexivity.
Qed.

Proposition add_comm_cab : forall a b c : nat, a + b + c = c + a + b.
Proof.
  intros a b c.
  rewrite -> (add_comm c a).
  rewrite <- add_assoc.
  rewrite <- add_assoc.
  apply <- add_cancel.
  rewrite -> add_comm.
  reflexivity.
Qed.

Proposition add_comm_bca : forall a b c : nat, a + b + c = b + c + a.
Proof.
  intros a b c.
  rewrite -> (add_comm a b).
  rewrite <- add_assoc.
  rewrite <- add_assoc.
  apply <- add_cancel.
  rewrite -> add_comm.
  reflexivity.
Qed.

Proposition add_comm_cba : forall a b c : nat, a + b + c = c + b + a.
Proof.
  intros a b c.
  rewrite -> (add_comm_cab a b c).
  rewrite <- add_assoc.
  rewrite <- add_assoc.
  apply <- add_cancel.
  rewrite -> add_comm.
  reflexivity.
Qed.

Proposition add_comm_adbc : forall a b c d : nat, a + b + c + d = a + d + b + c.
Proof.
  intros a b c d.
  rewrite <- add_assoc.
  rewrite <- add_assoc.
  rewrite <- add_assoc.
  rewrite <- add_assoc.
  apply <- add_cancel.
  rewrite -> add_assoc.
  rewrite -> add_assoc.
  rewrite -> add_comm_cab.
  reflexivity.
Qed.

Proposition add_comm_acbd : forall a b c d : nat, a + b + c + d = a + c + b + d.
Proof.
  intros a b c d.
  rewrite -> (add_comm_acb a b c).
  reflexivity.
Qed.

Proposition add_comm_cdab : forall a b c d : nat, a + b + c + d = c + d + a + b.
Proof.
  intros a b c d.
  rewrite -> (add_comm_cba a b c).
  rewrite <- add_assoc.
  rewrite <- add_assoc.
  rewrite <- add_assoc.
  rewrite <- add_assoc.
  apply <- add_cancel.
  rewrite -> add_assoc.
  rewrite -> add_assoc.
  rewrite -> (add_comm_cba d a b).
  reflexivity.
Qed.

Proposition add_comm_cadb : forall a b c d : nat, a + b + c + d = c + a + d + b.
Proof.
  intros a b c d.
  rewrite -> (add_comm_cab a b c).
  rewrite <- add_assoc.
  rewrite <- add_assoc.
  rewrite -> (add_comm b d).
  rewrite -> add_assoc.
  rewrite -> add_assoc.
  reflexivity.
Qed.

Require Import Stdlib.Classes.RelationClasses.
Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Setoids.Setoid.

Section OpComm8.

Context {T : Type}.
Context (op : T -> T -> T).
Context (eqv : T -> T -> Prop).

Infix "⊗" := op (at level 50, left associativity).
Infix "~" := eqv (at level 60).

Hypothesis HComm : forall a b : T, (a ⊗ b) ~ (b ⊗ a).
Hypothesis HAssoc : forall a b c : T, (a ⊗ b) ⊗ c ~ a ⊗ (b ⊗ c).

Hypothesis Heqv_equiv : Equivalence eqv.
Existing Instance Heqv_equiv.

Hypothesis Hop_proper :
  Proper (eqv ==> eqv ==> eqv) op.

Proposition op_comm_8_a0_swap_a1 : 
  forall (a0 a1 a2 a3 a4 a5 a6 a7 : T),
  (a0 ⊗ a1 ⊗ a2 ⊗ a3 ⊗ a4 ⊗ a5 ⊗ a6 ⊗ a7) ~ (a1 ⊗ a0 ⊗ a2 ⊗ a3 ⊗ a4 ⊗ a5 ⊗ a6 ⊗ a7).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  rewrite -> (HComm _ a0).
  reflexivity.
Qed.

End OpComm8.

Lemma nat_add_proper : Proper (eq ==> eq ==> eq) Nat.add.
Proof.
  unfold Proper, respectful.
  intros x1 x2 y1 y2 Hx Hy.
  subst.
  reflexivity.
Qed.

Proposition add_comm_8_a0_swap_a1 : forall a0 a1 a2 a3 a4 a5 a6 a7 : nat, 
  a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 = a1 + a0 + a2 + a3 + a4 + a5 + a6 + a7.
Proof.
  apply (op_comm_8_a0_swap_a1 Nat.add eq).
  { apply add_comm. } { apply eq_equivalence. } { apply nat_add_proper. }

  (*
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  rewrite -> (add_comm _ a0).
  reflexivity.
  *)
Qed.

Proposition add_comm_8_a0_swap_a2 : forall a0 a1 a2 a3 a4 a5 a6 a7 : nat, 
  a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 = a2 + a1 + a0 + a3 + a4 + a5 + a6 + a7.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  repeat apply <- add_cancel_r.
  rewrite -> (add_comm _ a0).
  rewrite <- add_assoc.
  apply <- add_cancel.
  rewrite -> add_comm.
  reflexivity.
Qed.

Proposition add_comm_8_a0_swap_a3 : forall a0 a1 a2 a3 a4 a5 a6 a7 : nat, 
  a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 = a3 + a1 + a2 + a0 + a4 + a5 + a6 + a7.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  repeat apply <- add_cancel_r.
  rewrite -> (add_comm _ a0).
  repeat rewrite <- add_assoc.
  apply <- add_cancel.
  repeat rewrite -> add_assoc.
  rewrite -> add_comm_cab.
  reflexivity.
Qed.

Proposition add_comm_8_a0_swap_a4 : forall a0 a1 a2 a3 a4 a5 a6 a7 : nat, 
  a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 = a4 + a1 + a2 + a3 + a0 + a5 + a6 + a7.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  repeat apply <- add_cancel_r.
  rewrite -> (add_comm _ a0).
  repeat rewrite <- add_assoc.
  apply <- add_cancel.
  repeat rewrite -> add_assoc.
  rewrite -> (add_comm a4 a1).
  repeat rewrite <- add_assoc.
  apply <- add_cancel.
  repeat rewrite -> add_assoc.
  rewrite -> add_comm_cab.
  reflexivity.
Qed.

Proposition add_comm_8_a0_swap_a5 : forall a0 a1 a2 a3 a4 a5 a6 a7 : nat, 
  a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 = a5 + a1 + a2 + a3 + a4 + a0 + a6 + a7.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  repeat apply <- add_cancel_r.
  rewrite -> (add_comm _ a0).
  repeat rewrite <- add_assoc.
  apply <- add_cancel.
  repeat rewrite -> add_assoc.
  rewrite -> (add_comm a5 a1).
  repeat rewrite <- add_assoc.
  apply <- add_cancel.
  repeat rewrite -> add_assoc.
  rewrite -> (add_comm a5 a2).
  repeat rewrite <- add_assoc.
  apply <- add_cancel.
  repeat rewrite -> add_assoc.
  rewrite -> add_comm_cab.
  reflexivity.
Qed.

Proposition add_comm_8_a0_swap_a6 : forall a0 a1 a2 a3 a4 a5 a6 a7 : nat, 
  a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 = a6 + a1 + a2 + a3 + a4 + a5 + a0 + a7.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  repeat apply <- add_cancel_r.
  rewrite -> (add_comm _ a0).
  repeat rewrite <- add_assoc.
  apply <- add_cancel.
  repeat rewrite -> add_assoc.
  rewrite -> (add_comm a6 a1).
  repeat rewrite <- add_assoc.
  apply <- add_cancel.
  repeat rewrite -> add_assoc.
  rewrite -> (add_comm a6 a2).
  repeat rewrite <- add_assoc.
  apply <- add_cancel.
  repeat rewrite -> add_assoc.
  rewrite -> (add_comm a6 a3).
  repeat rewrite <- add_assoc.
  apply <- add_cancel.
  repeat rewrite -> add_assoc.
  rewrite -> add_comm_cab.
  reflexivity.
Qed.
    
Proposition add_comm_8_a0_swap_a7 : forall a0 a1 a2 a3 a4 a5 a6 a7 : nat, 
  a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 = a7 + a1 + a2 + a3 + a4 + a5 + a6 + a0.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7.
  rewrite -> (add_comm _ a0).
  repeat rewrite <- add_assoc.
  apply <- add_cancel.
  repeat rewrite -> add_assoc.
  rewrite -> (add_comm a7 a1).
  repeat rewrite <- add_assoc.
  apply <- add_cancel.
  repeat rewrite -> add_assoc.
  rewrite -> (add_comm a7 a2).
  repeat rewrite <- add_assoc.
  apply <- add_cancel.
  repeat rewrite -> add_assoc.
  rewrite -> (add_comm a7 a3).
  repeat rewrite <- add_assoc.
  apply <- add_cancel.
  repeat rewrite -> add_assoc.
  rewrite -> (add_comm a7 a4).
  repeat rewrite <- add_assoc.
  apply <- add_cancel.
  repeat rewrite -> add_assoc.
  rewrite -> add_comm_cab.
  reflexivity.
Qed.

(* Print Assumptions add_cancel. (* Closed under the global context *) *)

Proposition sum_pos : forall a b : nat, (a = 0 -> False) -> (a + b = 0 -> False).
Proof.
  intros a b H0.
  induction b as [| b' IHb'].
  {
    rewrite -> add_0_r.
    apply H0. (* H0 is exactly the goal *)
  }
  {
    rewrite <- add_n_Sm.
    intros H1.
    discriminate. (* Works without intros H1, likely applied to it implicitly *)
  }
Qed.

(* Corrollary 2.2.9 vpg 38 *)
Proposition zero_sum_zero_parts : forall a b : nat, (a + b = 0) <-> a = 0 /\ b = 0.
Proof.
  intros a b.
  split.
  {
    intros H0.
    apply conj.
    {
      destruct a as [| a'] eqn:Ea.
      {
        reflexivity.
      }
      {
        rewrite -> add_Sn_m in H0.
        discriminate H0.
      }
    }
    {
      destruct b as [| b'] eqn:Eb.
      {
        reflexivity.
      }
      {
        rewrite <- add_n_Sm in H0.
        discriminate H0.
      }
    }
  }
  {
    intros H0.
    destruct H0 as [H0l H0r] eqn:EqH0.
    {
      rewrite -> H0l.
      rewrite -> H0r.
      rewrite -> add_0_l.
      reflexivity.
    }
  }
Qed.

Proposition add_swap_s : forall a b : nat, S a + b = a + S b.
Proof.
  intros a b.
  rewrite -> add_Sn_m.
  rewrite <- add_n_Sm.
  reflexivity.
Qed.

Proposition add_succ_implies_ne_2 : forall a b : nat, a = (S a) + b -> False.
Proof.
  intros a b H0.
  rewrite -> (add_swap_s a b) in H0.
  apply add_cancel_2 in H0.
  discriminate.
Qed.

Proposition add_succ_implies_ne_3 : forall a b c : nat, a = (S b) + c -> (a = b -> False).
  intros a b c H0 H1.
  rewrite <- H1 in H0.
  apply add_succ_implies_ne_2 in H0.
  contradiction H0.
Qed.

Proposition add_distinct_implies_pos : forall a b c : nat, 
  a = b + c /\ (a = b -> False) -> (c = 0 -> False).
Proof.
  intros a b c H0.
  destruct H0 as [H0l H0r].
  {
    intros H1.
    rewrite -> H1 in H0l.
    rewrite -> add_0_r in H0l.
    apply H0r.
    rewrite -> H0l.
    reflexivity.
  }
Qed.

(* Lemma 2.2.10 vpg 38 *)
Proposition pos_num_has_unique_pred : forall a : nat, (a = 0 -> False) -> exists b : nat, S b = a.
Proof.
  intros a H0.
  destruct a as [| a'] eqn:Ea.
  {
    (* Could also just write: contradiction. *)
    (* Could also just write: contradiction (H0 eq_refl). *)
    exfalso.
    apply H0.
    reflexivity.
  }
  {
    exists a'.
    reflexivity.
  }
Qed.

(* exists says There exists some *)
(* exists! says There exists exactly one *)
Definition ge (n m : nat) : Prop :=
  exists! p : nat, n = m + p.

Definition gt (n m : nat) : Prop :=
(ge n m) /\ (n = m -> False).

Set Warnings "-notation-overridden".
Notation "x >= y" := (ge x y) (at level 70) : nat_scope.
Notation "x > y" := (gt x y) (at level 70) : nat_scope.
Set Warnings "+notation-overridden".

Proposition ge_refl : forall a : nat, ge a a.
Proof.
  intros a.
  unfold ge.
  destruct a as [| a'] eqn:Ea.
  {
    exists 0.
    split.
    {
      rewrite -> add_0_l.
      reflexivity.
    }
    {
      intros p0 H0.
      rewrite -> add_0_l in H0.
      apply H0.
    }
  }
  {
    exists 0.
    split.
    {
      rewrite -> add_0_r.
      reflexivity.
    }
    {
      intros p0 H0.
      apply (add_cancel_2) in H0.
      apply H0.
    }
  }
Qed.

Proposition ge_trans : forall a b c : nat, (ge a b) -> (ge b c) -> (ge a c).
Proof.
  intros a b c H0 H1.
  unfold ge in H0.
  unfold ge in H1.
  unfold ge.
  destruct H0 as [p0 [Hp0 Hp0u]].
  {
    destruct H1 as [p1 [Hp1 Hp1u]].
    {
      rewrite -> Hp0.
      rewrite Hp1.
      exists (p1 + p0).
      split.
      {
        rewrite -> add_assoc.
        reflexivity.
      }
      {
        intros x' H2.
        rewrite <- add_assoc in H2.
        apply (add_cancel c (p1 + p0) x') in H2.
        apply H2.
      }
    }
  }
Qed.

Proposition nat_add_two_equations : forall a0 a1 a2 a3 b1 b2 : nat,
  (b1 = a0 + a1) -> (b2 = a2 + a3) -> (b1 + b2 = a0 + a1 + a2 + a3).
Proof.
  intros a0 a1 a2 a3 b1 b2 H0 H1.
  rewrite -> H0.
  rewrite -> H1.
  rewrite -> add_assoc.
  reflexivity.
Qed.

Proposition gt_as_ge_succ : forall a b : nat, (a > b) <-> (a >= (S b)).
Proof.
  split.
  {
    intros H0.
    unfold ge in *.
    unfold gt in *.
    destruct H0 as [H0l H0r].
    unfold ge in *.
    destruct H0l as [p0 [Hp0 Hp0u]].
    assert (H1 : p0 = 0 -> False).
    {
      apply (add_distinct_implies_pos a b p0).
      split. apply Hp0. apply H0r.
    }
    destruct p0 as [| p0'].
    {
      contradiction H1.
      reflexivity.
    }
    {
      rewrite -> Hp0.
      rewrite <- add_swap_s.
      exists p0'.
      split.
      {
        reflexivity.
      }
      {
        intros x' Hx'.
        apply -> add_cancel in Hx'.
        exact Hx'.
      }
    }
  }
  {
    intros H0.
    unfold ge in *.
    unfold gt in *.
    destruct H0 as [p0 [Hp0 Hp0u]].
    unfold ge.
    split.
    {
      exists (S p0).
      split.
      {
        rewrite -> Hp0.
        rewrite -> add_swap_s.
        reflexivity.
      }
      {
        intros x' Hx'.
        rewrite -> Hp0 in Hx'.
        rewrite -> add_swap_s in Hx'.
        apply -> add_cancel in Hx'.
        exact Hx'.
      }
    }
    {
      intros H1.
      rewrite -> H1 in Hp0.
      apply add_succ_implies_ne_2 in Hp0.
      exact Hp0.
    }
  }
Qed.

Proposition ge_is_succ_invariant : forall a b : nat, a >= b <-> (S a) >= (S b).
Proof.
  intros a b.
  split.
  {
    intros H0.
    unfold ge in *.
    destruct H0 as [p0 [Hp0 Hp0u]].
    rewrite -> Hp0.
    rewrite <- add_Sn_m.
    exists p0.
    split.
    {
      reflexivity.
    }
    {
      intros x' Hx'.
      apply -> add_cancel in Hx'.
      exact Hx'.
    }
  }
  {
    intros H0.
    unfold ge in *.
    destruct H0 as [p0 [Hp0 Hp0u]].
    rewrite -> add_Sn_m in Hp0.
    injection Hp0 as Hp0.
    rewrite -> Hp0.
    exists p0.
    split.
    {
      reflexivity.
    }
    {
      intros x' Hx'.
      apply -> add_cancel in Hx'.
      exact Hx'.
    }
  }
Qed.

Proposition gt_succ_as_ge : forall a b : nat, ((S a) > b) <-> (a >= b).
Proof.
  intros a b.
  split.
  {
    intros H0.
    destruct b as [| b'].
    {
      unfold ge.
      apply gt_as_ge_succ in H0.
      exists (a).
      split.
      {
        rewrite -> add_0_l.
        reflexivity.
      }
      {
        intros x' Hx'.
        rewrite -> add_0_l in Hx'.
        exact Hx'.
      }
    }
    {
      apply gt_as_ge_succ in H0.
      apply ge_is_succ_invariant in H0.
      exact H0.
    }
  }
  {
    intros H0.
    apply gt_as_ge_succ.
    apply -> ge_is_succ_invariant.
    exact H0.
  }
Qed.

Proposition gt_implies_ge : forall a b : nat, (a > b) -> (a >= b).
Proof.
  intros a b H0.
  destruct H0 as [H0l H0r].
  exact H0l.
Qed.

Proposition eq_implies_ge : forall a b : nat, (a = b) -> (a >= b).
Proof.
  intros a b H0.
  rewrite -> H0.
  apply ge_refl.
Qed.

Proposition gt_trans : forall a b c : nat, (gt a b) -> (gt b c) -> (gt a c).
Proof.
  intros a b c H0 H1.
  unfold gt.
  split.
  2:
  {
    destruct H0 as [H0l H0r].
    destruct H1 as [H1l H1r].
    destruct H0l as [p0 [Hp0 _]].
    destruct H1l as [p1 [Hp1 _]].
    specialize (nat_add_two_equations b p0 c p1 a b Hp0 Hp1) as H0.
    rewrite -> add_comm in H0.
    do 2 rewrite <- add_assoc in H0.
    apply -> add_cancel in H0.
    destruct p0 as [| p0'].
    {
      rewrite -> add_0_r in Hp0.
      specialize (H0r Hp0).
      contradiction.
    }
    {
      destruct p1 as [| p1'].
      {
        rewrite -> add_0_r in Hp1.
        specialize (H1r Hp1).
        contradiction.
      }
      {
        rewrite -> add_comm in H0.
        rewrite <- add_assoc in H0.
        rewrite -> add_Sn_m in H0.
        rewrite <- add_swap_s in H0.
        specialize (add_succ_implies_ne_3 a c (p1' + (S p0')) H0) as H1.
        exact H1.
      }
    }
  }
  {
    apply gt_implies_ge in H0, H1.
    specialize (ge_trans a b c H0 H1) as H2.
    exact H2.
  }
Qed.

Proposition ge_is_add_invariant : forall a b c : nat, (a >= b) <-> ((a + c) >= (b + c)).
Proof.
  intros a b c.
  unfold ge.
  split.
  {
    intros H0.
    destruct H0 as [p0 [Hp0 Hp0u]].
    {
      rewrite -> Hp0.
      exists p0.
      split.
      {
        rewrite <- (add_assoc b c p0).
        rewrite -> (add_comm c p0).
        rewrite -> (add_assoc b p0 c).
        reflexivity.
      }
      {
        intros x' H0.
        rewrite <- (add_assoc) in H0.
        rewrite -> (add_comm p0 c) in H0.
        rewrite -> (add_assoc) in H0.
        apply add_cancel in H0.
        apply H0.
      }
    }
  }
  {
    intros H0.
    destruct H0 as [p0 [Hp0 Hp0u]].
    {
      rewrite -> (add_comm b c) in Hp0.
      rewrite -> (add_comm a c) in Hp0.
      rewrite <- (add_assoc c b p0) in Hp0.
      apply add_cancel in Hp0.
      rewrite -> Hp0.
      exists p0.
      split.
      {
        reflexivity.
      }
      {
        intros x' H0.
        apply add_cancel in H0.
        apply H0.
      }
    }
  }
Qed.

Proposition gt_is_add_invariant : forall a b c : nat, (a > b) <-> ((a + c) > (b + c)).
Proof.
  intros a b c.
  split.
  {
    intros H0.
    split.
    {
      apply gt_implies_ge in H0.
      apply ge_is_add_invariant.
      exact H0.
    }
    {
      intros H1.
      destruct H0 as [H0l H0r].
      rewrite -> (add_comm a c) in H1.
      rewrite -> (add_comm b c) in H1.
      specialize (add_cancel c a b) as H2.
      destruct H2 as [H2 _].
      specialize (H2 H1).
      specialize (H0r H2).
      contradiction.
    }
  }
  {
    intros H0.
    split.
    2:
    {
      destruct H0 as [H0l H0r].
      rewrite -> (add_comm a c) in H0r.
      rewrite -> (add_comm b c) in H0r.
      specialize (add_cancel c a b) as H1.
      destruct H1 as [_ H1].
      intros H2.
      specialize (H1 H2).
      specialize (H0r H1).
      contradiction.
    }
    {
      apply gt_implies_ge in H0.
      apply <- (ge_is_add_invariant a b c).
      exact H0.
    }
  }
Qed.

Proposition gt_0_l_is_false : forall a : nat, 0 > a -> False.
Proof.
  intros a H0.
  destruct H0 as [H0l H0r].
  induction a as [| a' IHa'].
  {
    contradiction.
  }
  {
    apply gt_as_ge_succ in H0l.
    destruct H0l as [H0ll H0lr].
    specialize (IHa' H0ll H0lr) as H1.
    contradiction.
  }
Qed.

Proposition gt_succ_l_0_r : forall a : nat, (S a) > 0.
Proof.
  intros a.
  apply gt_as_ge_succ.
  unfold ge.
  exists (a).
  split.
  {
    rewrite <- add_1_is_succ.
    reflexivity.
  }
  {
    intros x' Hx'.
    rewrite -> (add_1_is_succ x') in Hx'.
    injection Hx' as Hx'.
    exact Hx'.
  }
Qed.

Proposition gt_succ_same_l : forall a : nat, (S a) > a.
Proof.
  intros a.
  apply gt_succ_as_ge.
  apply ge_refl.
Qed.

Proposition ge_implies_eq_or_gt : forall a b : nat, (a >= b) -> ((a = b) \/ (a > b)).
Proof.
  intros a b H0.
  destruct H0 as [p0 [Hp0 Hp0u]].
  destruct p0 as [| p0'].
  {
    rewrite -> add_0_r in Hp0.
    left.
    apply Hp0.
  }
  {
    right.
    apply gt_as_ge_succ.
    unfold ge.
    rewrite <- add_swap_s in Hp0.
    exists (p0').
    split.
    {
      exact Hp0.
    }
    {
      intros x' Hx'.
      rewrite -> Hp0 in Hx'.
      apply add_cancel in Hx'.
      exact Hx'.
    }
  }
Qed.

Proposition ge_a_ge_b_b_ge_Sa_is_false : forall (a b : nat), (a >= b) -> (b >= S a) -> False.
Proof.
  intros a b H0 H1.
  destruct H0 as [p0 [Hp0 _]].
  destruct H1 as [p1 [Hp1 _]].
  rewrite -> Hp1 in Hp0.
  rewrite <- add_assoc in Hp0.
  specialize (add_succ_implies_ne_2 a (p1 + p0) Hp0) as H1.
  contradiction.
Qed.

Proposition add_neutral_r : forall a b : nat, a + b = a -> b = 0.
Proof.
  intros a b H0.
  induction a as [| a' IHa'].
  {
    rewrite -> add_0_l in H0.
    rewrite -> H0.
    reflexivity.
  }
  {
    rewrite -> add_Sn_m in H0.
    injection H0 as H1.
    apply IHa' in H1.
    rewrite -> H1.
    reflexivity.
  }
Qed.

Proposition ge_antisymmetric : forall a b : nat, (ge a b) -> (ge b a) -> (a = b).
Proof.
  intros a b H0 H1.
  unfold ge in H0.
  unfold ge in H1.
  destruct H0 as [p0 [Hp0 Hp0u]].
  {
    destruct H1 as [p1 [Hp1 Hp1u]].
    {
      assert (H2: p0 = 0).
      {
        rewrite -> Hp1 in Hp0.
        rewrite <- add_assoc in Hp0.
        symmetry in Hp0.
        apply add_neutral_r in Hp0.
        apply zero_sum_zero_parts in Hp0.
        destruct Hp0 as [Hp0l Hp0r].
        {
          rewrite <- Hp0r.
          reflexivity.
        }
      }
      rewrite -> H2 in Hp0.
      rewrite -> add_0_r in Hp0.
      rewrite -> Hp0.
      reflexivity.
    }
  }
Qed.

Proposition gt_pos_shift : forall a b : nat, 
  (gt b a) <-> exists! d : nat, (d = 0 -> False) /\ b = a + d.
Proof.
  unfold gt.
  unfold ge.
  intros a b.
  split.
  {
    intros H0.
    destruct H0 as [H0l H0r].
    {
      destruct H0l as [p0 [Hp0 Hp0u]].
      {
        exists p0.
        split.
        {
          split. (*<- Goal: (p0 = 0 -> False) /\ b = a + p0 *)
          {
            intros H1.
            rewrite -> H1 in Hp0.
            rewrite -> add_0_r in Hp0.
            apply H0r.
            rewrite Hp0.
            reflexivity.
          }
          {
            rewrite <- Hp0.
            reflexivity.
          }
        }
        {
          intros x' Hx'.
          destruct Hx' as [Hxl Hxr].
          {
            rewrite -> Hp0 in Hxr.
            apply add_cancel in Hxr.
            apply Hxr.
          }
        }
      }
    }
  }
  {
    intros H0.
    destruct H0 as [p0 [[Hp0l Hp0r] Hp0u]].
    {
      split. (*<- Goal: (exists ! p : nat, b = a + p) /\ (b = a -> False)*)
      {
        exists p0.
        split.
        {
          rewrite -> Hp0r.
          reflexivity.
        }
        {
          intros x' Hx'.
          rewrite -> Hp0r in Hx'.
          apply add_cancel in Hx'.
          apply Hx'.
        }
      }
      {
        (* Goal: b = c -> False*)
        intros H1. (* -> Goal: False*)
        rewrite -> H1 in Hp0r.
        apply add_cancel_2 in Hp0r.
        apply Hp0l.
        rewrite <- Hp0r.
        reflexivity.
      }
    }
  }
Qed.

(* apply goes forward for hypotheses, and backwards for goals. So if cancel was only -> it would not work, but because it's <-> there is a backwards b = c -> a + b = a + c 
    where to show a + b = a + c, it suffices to show b = c, so now it applies.*)
(* so for P -> Q, apply on goal says to show Q it suffices to show P. *)
(* on hypothesis, P is given so by def of implication proof of P gives proof of Q.*)
(*apply (proj2 (add_cancel a p1 (p1 + p0))). (*<- Goal: a + p1 = a + (p1 + p0)*) *)

Proposition gt_is_antirefl : forall a b : nat, 
  (gt a b) -> (gt b a) -> False.
Proof.
  unfold gt.
  unfold ge.
  intros a b H0 H1.
  destruct H0 as [H0l H0r].
  {
    destruct H1 as [H1l H1r].
    {
      destruct H0l as [p0 [Hp0 Hp0u]].
      {
        destruct H1l as [p1 [Hp1 Hp1u]].
        {
          assert (H2 : p0 = 0 -> False).
          {
            apply (add_distinct_implies_pos a b p0).
            split.
            {
              apply Hp0.
            }
            {
              apply H0r.
            }
          }
          assert (H3 : p1 = 0 -> False).
          {
            apply (add_distinct_implies_pos b a p1).
            split.
            {
              apply Hp1.
            }
            {
              apply H1r.
            }
          }
          rewrite -> Hp0 in Hp1.
          destruct p0 as [| p0'].
          {
            apply H2.
            reflexivity.
          }
          {
            destruct p1 as [| p1'].
            {
              apply H3.
              reflexivity.
            }
            {
              rewrite <- add_assoc in Hp1.
              apply add_cancel_2 in Hp1.
              discriminate.
            }
          }
        }
      }
    }
  }
Qed.

Proposition nat_ord_trichotomy_0 : forall a b : nat, 
  (gt a b) -> ((a = b) -> False) /\ ((gt b a) -> False).
Proof.
  intros a b.
  unfold gt.
  unfold ge.
  intros H0.
  destruct H0 as [H0l H0r].
  {
    destruct H0l as [p0 [Hp0 Hp0u]].
    {
      split.
      {
        apply H0r.
      }
      {
        intros H1.
        destruct H1 as [H1l H1r].
        {
          destruct H1l as [p1 [Hp1 Hp1u]].
          {
            rewrite -> Hp0 in Hp1.
            rewrite <- add_assoc in Hp1.
            apply add_cancel_2 in Hp1.
            assert ( H2 : p0 = 0 -> False).
            {
              apply (add_distinct_implies_pos a b p0).
              split. apply Hp0. apply H0r.
            }
            destruct p0 as [| p0'].
            {
              apply H2.
              reflexivity.
            }
            {
              rewrite -> add_Sn_m in Hp1.
              discriminate.
            }
          }
        }
      }
    }
  }
Qed.

Proposition nat_ord_trichotomy_1 : forall a b : nat, 
   (a = b) -> ((gt a b) -> False) /\ ((gt b a) -> False).
Proof.
  intros a b.
  unfold gt.
  unfold ge.
  intros H0.
  split.
  {
    intros H1.
    destruct H1 as [H1l H1r].
    {
      apply H1r.
      apply H0.
    }
  }
  {
    intros H1.
    destruct H1 as [H1l H1r].
    {
      apply H1r.
      rewrite <- H0.
      reflexivity.
    }
  }
Qed.

Proposition nat_ord_trichotomy_2 : forall a b : nat, 
  (gt b a) -> ((gt a b) -> False) /\ ((a = b) -> False).
Proof.
  intros a b.
  unfold gt.
  unfold ge.
  intros [[p0 [Hp0 Hp0u]] H0r].
  split.
  {
    intros H1.
    destruct H1 as [H1l H1r].
    {
      destruct H1l as [p1 [Hp1 Hp1u]].
      {
        rewrite -> Hp0 in Hp1.
        rewrite <- add_assoc in Hp1.
        apply add_cancel_2 in Hp1.
        assert ( H2 : p0 = 0 -> False).
        {
          apply (add_distinct_implies_pos b a p0).
          split. apply Hp0. apply H0r.
        }
        destruct p0 as [| p0'].
        {
          apply H2.
          reflexivity.
        }
        {
          rewrite -> add_Sn_m in Hp1.
          discriminate.
        }
      }
    }
  }
  {
    intros H1.
    apply H0r.
    rewrite <- H1.
    reflexivity.
  }
Qed.

Proposition nat_ord_trichotomy_3 : forall a b : nat,
  (a = b) \/ (a > b) \/ (b > a).
Proof.
  intros a.
  induction a as [| a' IHa'].
  {
    intros [| b'].
    {
      left.
      reflexivity.
    }
    {
      right; right.
      apply gt_as_ge_succ.
      unfold ge.
      exists b'.
      split.
      {
        rewrite -> add_Sn_m.
        apply f_equal.
        rewrite -> add_0_l.
        reflexivity.
      }
      {
        intros x' Hx'.
        rewrite -> add_Sn_m in Hx'.
        injection Hx' as Hx'.
        rewrite -> Hx'.
        reflexivity.
      }
    }
  }
  {
    intros b.
    destruct (IHa' b) as [Heq | [Hgt | Hlt]].
    {
      rewrite -> Heq.
      right; left.
      apply gt_as_ge_succ.
      apply ge_refl.
    }
    {
      apply gt_as_ge_succ in Hgt.
      right; left.
      apply gt_as_ge_succ.
      apply -> ge_is_succ_invariant.
      unfold ge in *.
      destruct Hgt as [p0 [Hp0 Hp0u]].
      rewrite -> Hp0.
      exists (S p0).
      split.
      {
        rewrite -> add_swap_s.
        reflexivity.
      }
      {
        intros x' Hx'.
        rewrite -> add_swap_s in Hx'.
        apply -> add_cancel in Hx'.
        exact Hx'.
      }
    }
    {
      apply gt_as_ge_succ in Hlt.
      destruct Hlt as [p0 [Hp0 Hp0u]].
      destruct p0 as [| p0'].
      {
        left.
        rewrite -> add_0_r in Hp0.
        symmetry in Hp0.
        exact Hp0.
      }
      {
        right; right.
        apply gt_as_ge_succ.
        unfold ge in *.
        rewrite -> Hp0.
        exists p0'.
        split.
        {
          rewrite <- add_swap_s.
          reflexivity.
        }
        {
          intros x' Hx'.
          rewrite <- add_swap_s in Hx'.
          apply -> add_cancel in Hx'.
          exact Hx'.
        }
      }
    }
  }
Qed.

Proposition nat_eq_dichotomy : forall (a b : nat), 
  (a = b) \/ ((a = b) -> False).
Proof.
  intros a b.
  destruct (nat_ord_trichotomy_3 a b) as [Heq | [Hgt | Hlt]].
  {
    left.
    exact Heq.
  }
  {
    unfold gt in Hgt.
    destruct Hgt as [Hge Hnzab].
    right.
    exact Hnzab.
  }
  {
    unfold gt in Hlt.
    destruct Hlt as [Hle Hnzba].
    right.
    intros H0.
    symmetry in H0.
    specialize (Hnzba H0).
    contradiction.
  }
Qed.

Proposition nat_ord_trichotomy_0_ne : forall a b : nat, 
  ((gt a b) -> False) -> ((a = b)) \/ ((gt b a)).
Proof.
  intros a b H0.
  destruct (nat_ord_trichotomy_3 a b) as [Heq | [Hgt | Hlt]].
  {
    left.
    exact Heq.
  }
  {
    specialize (H0 Hgt).
    contradiction.
  }
  {
    right.
    exact Hlt.
  }
Qed.

Proposition nat_ord_trichotomy_1_ne : forall a b : nat, 
   ((a = b) -> False) -> ((gt a b)) \/ ((gt b a)).
Proof.
  intros a b H0.
  destruct (nat_ord_trichotomy_3 a b) as [Heq | [Hgt | Hlt]].
  {
    specialize (H0 Heq).
    contradiction.
  }
  {
    left.
    exact Hgt.
  }
  {
    right.
    exact Hlt.
  }
Qed.

Proposition nat_ord_trichotomy_2_ne : forall a b : nat, 
  ((gt b a) -> False) -> (gt a b) \/ (a = b).
Proof.
  intros a b H0.
  destruct (nat_ord_trichotomy_3 a b) as [Heq | [Hgt | Hlt]].
  {
    right.
    exact Heq.
  }
  {
    left.
    exact Hgt.
  }
  {
    specialize (H0 Hlt).
    contradiction.
  }
Qed.

Proposition mult_0_l : forall a : nat, 0 * a = 0.
Proof.
  intros a.
  simpl.
  reflexivity.
Qed.

Proposition mult_Sa_b : forall a b : nat, (S a) * b = b + (a * b).
Proof.
  intros a b.
  simpl.
  reflexivity.
Qed.

Proposition mult_0_r : forall a : nat, a * 0 = 0.
Proof.
  intros a.
  induction a as [| a' IHa'].
  {
    rewrite -> mult_0_l.
    reflexivity.
  }
  {
    rewrite -> mult_Sa_b.
    rewrite -> add_0_l.
    apply IHa'.
  }
Qed.

Proposition mult_ident : forall a : nat, 1 * a = a.
Proof.
  intros a.
  rewrite -> (mult_Sa_b 0 a).
  rewrite -> mult_0_l.
  rewrite -> add_0_r.
  reflexivity.
Qed.

Proposition mult_ident_r : forall a : nat, a * 1 = a.
Proof.
  intros a.
  induction a as [| a' IHa'].
  {
    rewrite -> mult_0_l.
    reflexivity.
  }
  {
    rewrite -> mult_Sa_b.
    rewrite -> IHa'.
    rewrite -> add_1_is_succ.
    reflexivity.
  }
Qed.

Proposition mult_unfold_r : forall a b : nat, a * (S b) = a + (a * b).
Proof.
  intros a b.
  induction a as [| a' IHa'].
  {
    rewrite -> mult_0_l.
    rewrite -> mult_0_l.
    rewrite -> add_0_l.
    reflexivity.
  }
  {
    rewrite -> mult_Sa_b.
    rewrite -> mult_Sa_b.
    rewrite -> IHa'.
    rewrite -> add_Sn_m.
    rewrite -> add_Sn_m.
    apply nat_succ_inject.
    rewrite -> (add_comm a' (b + (a' * b))).
    rewrite <- add_assoc.
    apply (add_cancel b (a' + a' * b) (a' * b + a')).
    rewrite -> add_comm.
    reflexivity.
  }
Qed.

Proposition mult_comm : forall a b : nat, a * b = b * a.
Proof.
  intros a b.
  induction a as [| a' IHa'].
  {
    rewrite -> mult_0_l.
    rewrite -> mult_0_r.
    reflexivity.
  }
  {
    rewrite -> mult_Sa_b.
    rewrite -> IHa'.
    rewrite -> mult_unfold_r.
    reflexivity.
  }
Qed.

Proposition mult_a_Sb : forall a b : nat, a * (S b) = a + (a * b).
Proof.
  intros a b.
  rewrite -> mult_comm.
  rewrite -> mult_Sa_b.
  rewrite -> mult_comm.
  reflexivity.
Qed.

Proposition mult_dist_over_add : forall a b c : nat, a * (b + c) = a * b + a * c.
Proof.
  intros a b c.
  induction a as [| a' IHa'].
  {
    rewrite -> 3 mult_0_l.
    rewrite -> add_0_l.
    reflexivity.
  }
  {
    rewrite -> 3 mult_Sa_b.
    rewrite -> IHa'.
    rewrite -> 2 add_assoc_middle.
    rewrite -> (add_comm c (a' * b)).
    reflexivity.
  }
Qed.

Proposition mult_dist_over_add_r : forall a b c : nat, (a + b) * c = a * c + b * c.
Proof.
  intros a b c.
  rewrite -> (mult_comm (a + b) c).
  rewrite -> (mult_comm a c).
  rewrite -> (mult_comm b c).
  apply mult_dist_over_add.
Qed.

Proposition mult_dist_add_over_add : forall (a b c d : nat),
  ((a + b) * (c + d) = a*c + a*d + b*c + b*d)%nat.
Proof.
  intros a b c d.
  rewrite -> mult_dist_over_add.
  do 2 rewrite -> mult_dist_over_add_r.
  repeat rewrite <- add_assoc.
  apply <- add_cancel.
  repeat rewrite -> add_assoc.
  apply <- add_cancel_r.
  apply add_comm.
Qed.

Proposition mult_assoc : forall a b c : nat,
  a * (b * c) = (a * b) * c.
Proof.
  intros a b c.
  induction a as [| a' IHa'].
  {
    rewrite -> mult_0_l.
    rewrite -> (mult_0_l b).
    rewrite -> (mult_0_l c).
    reflexivity.
  }
  {
    rewrite -> 2 mult_Sa_b.
    rewrite -> (mult_comm (b + a' * b) c).
    rewrite -> mult_dist_over_add.
    rewrite -> IHa'.
    rewrite -> (mult_comm c b).
    rewrite -> (mult_comm c (a' * b)).
    reflexivity.
  }
Qed.

Proposition mult_no_zero_div : forall a b : nat, a * b = 0 <-> a = 0 \/ b = 0.
Proof.
  intros a b.
  split.
  {
    intros H0.
    destruct a as [| a'].
    {
      left.
      {
        reflexivity.
      }
    }
    {
      destruct b as [| b'].
      {
        right.
        {
          reflexivity.
        }
      }
      {
        left.
        {
          rewrite -> mult_Sa_b in H0.
          rewrite -> add_Sn_m in H0.
          discriminate.
        }
      }
    }
  }
  {
    intros H0.
    destruct H0 as [H0l | H0r].
    {
      rewrite -> H0l.
      rewrite -> mult_0_l.
      reflexivity.
    }
    {
      rewrite -> H0r.
      rewrite -> mult_0_r.
      reflexivity.
    }
  }
Qed.

Proposition mult_preserves_gt : forall a b c: nat, 
  (c = 0 -> False) /\ ((gt a b)) -> (gt (a * c) (b * c)).
Proof.
  intros a b c.
  unfold gt.
  unfold ge.
  intros H0.
  destruct H0 as [H0l H0r].
  {
    destruct H0r as [H1l H1r].
    {
      split.
      {
        (* Goal: exists ! p : nat, a * c = b * c + p *)
        destruct c as [| c'].
        {
          contradiction H0l.
          reflexivity.
        }
        {
          destruct H1l as [p0 [Hp0 Hp0u]].
          {
            assert (H2 : p0 = 0 -> False).
            {
              apply (add_distinct_implies_pos a b p0).
              split. apply Hp0. apply H1r.
            }
            destruct p0 as [| p0'].
            {
              contradiction H2.
              reflexivity.
            }
            {
              exists ((S c') * (S p0')).
              split.
              {
                (* Goal: a * S c' = b * S c' + S c' * S p0' *)
                rewrite -> Hp0.
                rewrite -> mult_dist_over_add_r.
                rewrite -> (mult_comm (S c') (S p0')).
                reflexivity.
              }
              {
                intros x' Hx'.
                (* Goal: S c' * S p0' = x' *)
                rewrite -> Hp0 in Hx'.
                rewrite -> mult_dist_over_add_r in Hx'.
                apply add_cancel in Hx'.
                rewrite -> mult_comm in Hx'.
                apply Hx'.
              }
            }
          }
        }
      }
      {
        (* Goal: a * c = b * c -> False *)
        destruct c as [| c'].
        {
          contradiction H0l.
          reflexivity.
        }
        {
          rewrite -> mult_unfold_r.
          rewrite -> mult_unfold_r.
          destruct H1l as [p0 [Hp0 Hp0u]].
          {
            rewrite -> Hp0.
            rewrite <- add_assoc.
            intros H2.
            apply add_cancel in H2.
            rewrite -> mult_dist_over_add_r in H2.
            rewrite -> add_assoc in H2.
            rewrite -> (add_comm p0 (b * c')) in H2.
            symmetry in H2.
            rewrite <- add_assoc in H2.
            apply (add_cancel_2 (b * c') (p0 + p0 * c')) in H2.
            assert (H3 : p0 = 0).
            {
              symmetry in H2.
              apply (zero_sum_zero_parts p0 (p0 * c')) in H2.
              destruct H2 as [H2l H2r].
              {
                apply H2l.
              }
            }
            apply H1r.
            rewrite -> Hp0.
            rewrite -> H3.
            rewrite -> add_0_r.
            reflexivity.
          }
        }
      }
    }
  }
Qed.

Proposition mult_cancel : forall a b c : nat, (a*b = a*c) <-> b = c \/ a = 0.
Proof.
  intros a b c.
  split.
  {
    intros H0.
    destruct a as [| a'].
    {
      right.
      reflexivity.
    }
    {
      generalize dependent c.
      induction b as [| b' IHb'].
      {
        intros c H0.
        rewrite -> mult_0_r in H0.
        symmetry in H0.
        apply mult_no_zero_div in H0.
        destruct H0 as [H0l | H0r].
        {
          right.
          exact H0l.
        }
        {
          left.
          symmetry.
          exact H0r.
        }
      }
      {
        intros c H0.
        destruct c as [| c'].
        {
          rewrite -> mult_0_r in H0.
          apply mult_no_zero_div in H0.
          destruct H0 as [H0l | H0r].
          {
            right.
            exact H0l.
          }
          {
            left.
            exact H0r.
          }
        }
        {
          rewrite -> mult_unfold_r in H0.
          rewrite -> mult_unfold_r in H0.
          apply add_cancel in H0.
          destruct (IHb' c' H0) as [H1l | H1r].
          {
            left.
            rewrite -> H1l.
            reflexivity.
          }
          {
            right.
            exact H1r.
          }
        }
      }
    }
  }
  {
    intros [H0l | H0r].
    {
      rewrite -> H0l.
      reflexivity.
    }
    {
      rewrite -> H0r.
      do 2 rewrite -> mult_0_l.
      reflexivity.
    }
  }
Qed.

Proposition mult_cancel_r : forall a b c : nat, (b*a = c*a) <-> (b = c \/ a = 0).
Proof.
  intros a b c.
  rewrite -> (mult_comm b a).
  rewrite -> (mult_comm c a).
  apply mult_cancel.
Qed.

Proposition mult_cancel_2 : forall a b : nat, (a = a*b) <-> b = 1 \/ a = 0.
Proof.
  intros a b.
  split.
  {
    intros H0.
    assert (H1 : (a * 1 = a * b)).
    {
      rewrite -> mult_ident_r.
      exact H0.
    }
    apply mult_cancel in H1.
    destruct H1 as [H1l | H1r].
    {
      left.
      symmetry.
      exact H1l.
    }
    {
      right.
      exact H1r.
    }
  }
  {
    intros H0.
    destruct H0 as [H0l | H0r].
    {
      rewrite -> H0l.
      rewrite -> mult_ident_r.
      reflexivity.
    }
    {
      rewrite -> H0r.
      rewrite -> mult_0_l.
      reflexivity.
    }
  }
Qed.

Proposition mult_cancel_l_3 : forall a b c : nat, ((S a)*b = (S a)*c) <-> (b=c).
Proof.
  intros a b c.
  split.
  {
    intros H0.
    apply -> mult_cancel in H0.
    destruct H0 as [H0l | H0r].
    {
      exact H0l.
    }
    {
      discriminate.
    }
  }
  {
    intros H0.
    rewrite -> H0.
    reflexivity.
  }
Qed.

Proposition mult_cancel_r_3 : forall a b c : nat, (a*(S c) = b*(S c)) <-> (a=b).
Proof.
  intros a b c.
  rewrite -> (mult_comm a (S c)).
  rewrite -> (mult_comm b (S c)).
  apply mult_cancel_l_3.
Qed.

Proposition mult_cancel_l_4 : forall (a b c : nat) (Hnza : (a=0) -> False), 
  (a*b = a*c) <-> (b=c).
Proof.
  intros a b c Hnza.
  destruct a as [| a'].
  {
    contradiction.
  }
  {
    apply mult_cancel_l_3.
  }
Qed.

Proposition mult_cancel_r_4 : forall (a b c : nat) (Hnzc : (c=0) -> False), 
  (a*c = b*c) <-> (a=b).
Proof.
  intros a b c Hnzc.
  destruct c as [| c'].
  {
    contradiction.
  }
  {
    apply mult_cancel_r_3.
  }
Qed.

Proposition mult_from_two_equations : forall (a b c d : nat),
  (a = b) -> (c = d) -> (a*c = b*d).
Proof.
  intros a b c d H0 H1.
  rewrite -> H0.
  rewrite -> H1.
  reflexivity.
Qed.

Fixpoint exp (a b : nat) : nat :=
  match b with
  | 0 => 1
  | (S b') => a * (exp a b')
  end.

Notation "x ** y" := (exp x y) (at level 45).

Proposition nat_exp_power_0 : forall (a : nat), a ** 0 = 1.
Proof.
  intros a.
  simpl.
  reflexivity.
Qed.

Proposition nat_exp_power_succ_l : forall (a b : nat), a ** (S b) = a * (a ** b).
Proof.
  intros a b.
  simpl.
  reflexivity.
Qed.

Proposition nat_exp_power_succ_r : forall (a b : nat), a ** (S b) = (a ** b) * a.
Proof.
  intros a b.
  simpl.
  rewrite -> mult_comm.
  reflexivity.
Qed.

Proposition nat_exp_base_1_ident : forall (a : nat), 1 ** a = 1.
Proof.
  intros a.
  induction a as [| a' IHa'].
  {
    rewrite -> nat_exp_power_0.
    reflexivity.
  }
  {
    rewrite -> nat_exp_power_succ_l.
    rewrite -> mult_ident.
    apply IHa'.
  }
Qed.

Proposition nat_exp_power_add : forall (a b c : nat), (a ** b) * (a ** c) = (a ** (b+c)).
Proof.
  intros a b c.
  induction b as [| b' IHb'].
  {
    rewrite -> nat_exp_power_0.
    rewrite -> add_0_l.
    rewrite -> mult_ident.
    reflexivity.
  }
  {
    rewrite -> nat_exp_power_succ_l.
    rewrite <- mult_assoc.
    rewrite -> IHb'.
    rewrite <- nat_exp_power_succ_l.
    rewrite -> add_Sn_m.
    reflexivity.
  }
Qed.

Proposition nat_exp_base_succ_ne_0 : forall (a b : nat),
  ((S a) ** b) = 0 -> False.
Proof.
  intros a b H0.
  induction b as [| b' IHb'].
  {
    rewrite -> nat_exp_power_0 in H0.
    discriminate.
  }
  {
    rewrite -> nat_exp_power_succ_l in H0.
    apply mult_no_zero_div in H0.
    destruct H0 as [H0l | H0r].
    {
      discriminate.
    }
    {
      specialize (IHb' H0r).
      contradiction.
    }
  }
Qed.

Proposition nat_exp_power_add_cancel_r : forall (n c0 c1 a b c : nat),
  (c0 * ((S n) ** (a+c)) = c1 * ((S n) ** (b+c))) <-> 
  (c0 * ((S n) ** a) = c1 * ((S n) ** b)).
Proof.
  intros n c0 c1 a b c.
  split.
  {
    intros H0.
    apply -> (mult_cancel_r_4 (c0 * ((S n) ** a)) (c1 * ((S n) ** b)) (S n ** (c))).
    2: exact (nat_exp_base_succ_ne_0 n c).
    repeat rewrite <- mult_assoc.
    do 2 rewrite -> nat_exp_power_add.
    exact H0.
  }
  {
    intros H0.
    apply <- (mult_cancel_r_4 (c0 * ((S n) ** a)) (c1 * ((S n) ** b)) (S n ** (c))) in H0.
    2: exact (nat_exp_base_succ_ne_0 n c).
    repeat rewrite <- mult_assoc in H0.
    do 2 rewrite -> nat_exp_power_add in H0.
    exact H0.
  }
Qed.

Proposition nat_exp_power_add_cancel_l : forall (n c0 c1 a b c : nat),
  (c0 * ((S n) ** (a+b)) = c1 * ((S n) ** (a+c))) <-> 
  (c0 * ((S n) ** b) = c1 * ((S n) ** c)).
Proof.
  intros n c0 c1 a b c.
  rewrite -> (add_comm a b).
  rewrite -> (add_comm a c).
  apply nat_exp_power_add_cancel_r.
Qed.

(*\begin{nat extra}*)

Proposition nat_eq_mult_pos_implies_gt_or_ab_0_or_c_0 : forall (a b c : nat),
  (a = b * (S c)) -> ((a > b) \/ ((a = 0) /\ (b = 0)) \/ (c = 0)).
Proof.
  intros a b c H0.
  destruct (nat_ord_trichotomy_3 a b) as [Heq | [Hgt | Hlt]].
  {
    rewrite -> Heq in H0.
    rewrite -> mult_comm in H0.
    rewrite -> mult_Sa_b in H0.
    apply -> add_cancel_2 in H0.
    symmetry in H0.
    apply mult_no_zero_div in H0.
    destruct H0 as [H1l | H1r].
    {
      right; right.
      exact H1l.
    }
    {
      right; left.
      split.
      {
        rewrite -> H1r in Heq.
        exact Heq.
      }
      {
        exact H1r.
      }
    }
  }
  {
    left.
    exact Hgt.
  }
  {
    rewrite -> H0 in Hlt.
    rewrite mult_comm in Hlt.
    rewrite -> mult_Sa_b in Hlt.
    assert (Hlt' : 0 + b > c * b + b).
    {
      rewrite -> add_0_l.
      rewrite -> add_comm.
      exact Hlt.
    }
    apply gt_is_add_invariant in Hlt'.
    specialize (gt_0_l_is_false (c*b) Hlt') as H1.
    contradiction.
  }
Qed.

Proposition nat_euclid_div : forall (a b : nat), exists (k l : nat), 
  ((S b) > l)%nat /\ (a = k * (S b) + l)%nat.
Proof.
  intros a b.
  generalize dependent b.
  induction a as [| a' IHa'].
  {
    intros b.
    exists (0).
    exists (0).
    split.
    {
      apply gt_succ_l_0_r.
    }
    {
      rewrite -> add_0_r.
      rewrite -> mult_0_l.
      reflexivity.
    }
  }
  {
    intros b.
    specialize (IHa' b) as H0.
    destruct H0 as [k' [l' [HgtSbl Hdiv]]].
    (*
      S a' < S b
      a'  := 4
      S b := 6

      a'   = k' * S b + l' <-> 4 = k' * 6 + l' <-> 4 = 0 * 6 + 4.
      S a' = k  * S b + l  <-> 5 = k  * 6 + l  <-> 5 = 0 * 6 + 5

      S a' = S b
      a'  := 5
      S b := 6

      a'   = k' * S b + l' <-> 5 = k' * 6 + l' <-> 5 = 0 * 6 + 5.
      S a' = k  * S b + l  <-> 6 = k  * 6 + l  <-> 6 = 1 * 6 + 0.

      S a' > S b
      a'  := 25
      S b := 13

      a'   = k' * S b + l' <-> 25 = k' * 13 + l' <-> 25 = 1 * 13 + 12.
      S a' = k  * S b + l  <-> 26 = k  * 13 + l  <-> 26 = 2 * 13 + 0.
    *)
    destruct (nat_eq_dichotomy (l' + 1) (S b)) as [Heq | Hne].
    {
      exists (k' + 1)%nat.
      exists (0).
      split.
      {
        apply gt_succ_l_0_r.
      }
      {
        rewrite -> add_0_r.
        rewrite -> mult_dist_over_add_r.
        rewrite -> mult_ident.
        assert (Hrw : ((S a' = k' * S b + (l' + 1)) -> (S a' = k' * S b + S b))%nat).
        {
          intros H0.
          rewrite -> Heq in H0.
          exact H0.
        }
        apply Hrw.
        clear Hrw.
        rewrite -> add_assoc.
        rewrite -> Hdiv.
        rewrite <- add_1_is_succ.
        rewrite -> add_comm.
        reflexivity.
      }
    }
    {
      exists (k').
      exists (l' + 1)%nat.
      split.
      {
        apply (nat_ord_trichotomy_1_ne) in Hne.
        destruct Hne as [Hlt | Hgt].
        {
          rewrite -> add_comm in Hlt.
          rewrite -> add_1_is_succ in Hlt.
          apply -> gt_succ_as_ge in Hlt.
          apply -> gt_succ_as_ge in HgtSbl.
          specialize (ge_a_ge_b_b_ge_Sa_is_false b l' HgtSbl Hlt) as H1.
          contradiction.
        }
        {
          exact Hgt.
        }
      }
      {
        rewrite <- (add_1_is_succ a').
        rewrite -> Hdiv.
        rewrite -> add_comm.
        rewrite -> add_assoc.
        reflexivity.
      }
    }
  }
Qed.

Definition nat_divisible (a b : nat) :=
  exists k : nat, a = k*b.

Definition nat_indivisible (a b : nat) (Hnzb : (b = 0) -> False) :=
  exists k l : nat, (b > S l) /\ (a = k*b + S l).

Proposition nat_divisibility_dichotomy : forall (a b : nat) (Hnzb : (b = 0) -> False),
  (nat_divisible a b) \/ (nat_indivisible a b Hnzb).
Proof.
  intros a b Hnzb.
  destruct b as [| b'].
  {
    contradiction.
  }
  {
    specialize (nat_euclid_div a b') as [p0 [p1 [Hmod Hdiv]]].
    destruct p1 as [| p1'].
    {
      left.
      rewrite -> add_0_r in Hdiv.
      unfold nat_divisible.
      exists (p0).
      exact Hdiv.
    }
    {
      right.
      unfold nat_indivisible.
      exists (p0).
      exists (p1').
      split.
      {
        exact Hmod.
      }
      {
        exact Hdiv.
      }
    }
  }
Qed.

Proposition nat_gt_succ_r_implies_indivisible : forall (a b : nat) (Hnza : (a = 0) -> False),
  (a > (S b)) -> (nat_indivisible (S b) a Hnza).
Proof.
  intros a b Hnza H0.
  unfold nat_indivisible.
  exists (0).
  exists (b).
  split.
  {
    exact H0.
  }
  {
    rewrite -> mult_0_l.
    rewrite -> add_0_l.
    reflexivity.
  }
Qed.

Proposition nat_pos_remainder_implies_indivisible : forall (a c0 c1 b : nat) 
  (Hnzb : (b = 0) -> False), (b > (S c0)) -> (a = c1 * b + (S c0)) -> 
  (nat_indivisible a b Hnzb).
Proof.
  intros a c0 c1 b Hnzb Hmod Hndiv.
  unfold nat_indivisible.
  exists (c1).
  exists (c0).
  split.
  {
    exact Hmod.
  }
  {
    exact Hndiv.
  }
Qed.

Proposition gt_same_is_false : forall (a : nat), (a > a) -> False.
Proof.
  intros a H0.
  destruct a as [| a'].
  {
    apply gt_0_l_is_false in H0.
    contradiction.
  }
  {
    apply gt_succ_as_ge in H0.
    destruct H0 as [p0 [Hp0 _]].
    apply add_succ_implies_ne_2 in Hp0.
    contradiction.
  }
Qed.

Fixpoint nat_diff (a b : nat) : nat :=
  match a, b with
  | O, O => O
  | O, _ => b
  | _, O => a
  | S a', S b' => (nat_diff a' b')
  end.

Proposition nat_diff_same_is_0 : forall (a : nat), (nat_diff a a) = 0.
Proof.
  induction a as [| a' IHa'].
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    apply IHa'.
  }
Qed.

Proposition nat_diff_eq_0_is_same : forall (a b : nat), 
  ((nat_diff a b) = 0) <-> (a = b).
Proof.
  intros a b.
  split.
  {
    intros H0.
    generalize dependent b.
    induction a as [| a' IHa'].
    {
      destruct b as [| b'].
      {
        reflexivity.
      }
      {
        discriminate.
      }
    }
    {
      destruct b as [| b'].
      {
        discriminate.
      }
      {
        intros H0.
        simpl in H0.
        apply (IHa' b') in H0.
        rewrite -> H0.
        reflexivity.
      }
    }
  }
  {
    intros H0.
    rewrite -> H0.
    apply nat_diff_same_is_0.
  }
Qed.

Proposition nat_diff_0_l : forall (a : nat), (nat_diff 0 a) = a.
Proof.
  intros a.
  destruct a as [| a'].
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    reflexivity.
  }
Qed.

Proposition nat_diff_0_r : forall (a : nat), (nat_diff a 0) = a.
Proof.
  intros a.
  destruct a as [| a'].
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    reflexivity.
  }
Qed.

Proposition nat_diff_comm : forall (a b : nat),
  (nat_diff a b) = (nat_diff b a).
Proof.
  intros a b.
  generalize dependent b.
  induction a as [| a' IHa'].
  {
    intros b.
    rewrite -> nat_diff_0_l.
    rewrite -> nat_diff_0_r.
    reflexivity.
  }
  {
    intros b.
    destruct b as [| b'].
    {
      rewrite -> nat_diff_0_l.
      rewrite -> nat_diff_0_r.
      reflexivity.
    }
    {
      simpl.
      apply (IHa' b').
    }
  }
Qed.

Proposition nat_diff_reduce_add_r : forall (a b : nat),
  (nat_diff (a + b) b) = a.
Proof.
  intros a b.
  generalize dependent a.
  induction b as [| b' IHb'].
  {
    intros a.
    rewrite -> add_0_r.
    rewrite -> nat_diff_0_r.
    reflexivity.
  }
  {
    intros a.
    rewrite <- add_swap_s.
    simpl.
    apply (IHb' a).
  }
Qed.

Proposition nat_diff_reduce_add_l : forall (a b : nat),
  (nat_diff (b + a) b) = a.
Proof.
  intros a b.
  generalize dependent a.
  induction b as [| b' IHb'].
  {
    intros a.
    rewrite -> add_0_l.
    rewrite -> nat_diff_0_r.
    reflexivity.
  }
  {
    intros a.
    simpl.
    apply (IHb' a).
  }
Qed.

Proposition nat_diff_dichotomy : forall (a b : nat),
  (exists! k : nat, a = (b + k)%nat /\ (nat_diff a b) = k) \/ 
  (exists! k : nat, b = (a + k)%nat /\ (nat_diff a b) = k).
Proof.
  intros a b.
  destruct (nat_ord_trichotomy_3 a b) as [Heq | [Hgt | Hlt]].
  {
    left.
    exists (0).
    split.
    {
      rewrite add_0_r.
      split.
      1: exact Heq.
      apply nat_diff_eq_0_is_same.
      exact Heq.
    }
    {
      intros x' [Hx'l Hx'r].
      rewrite -> Heq in Hx'r.
      rewrite -> nat_diff_same_is_0 in Hx'r.
      exact Hx'r.
    }
  }
  {
    apply gt_as_ge_succ in Hgt.
    unfold ge in Hgt.
    destruct Hgt as [p0 [Hp0 _]].
    left.
    exists (S p0).
    split.
    {
      split.
      rewrite -> add_swap_s in Hp0.
      1: exact Hp0.
      rewrite -> add_swap_s in Hp0.
      rewrite -> Hp0.
      rewrite -> nat_diff_reduce_add_l.
      reflexivity.
    }
    {
      intros x' [Hx'l Hx'r].
      rewrite -> Hp0 in Hx'r.
      rewrite -> add_swap_s in Hx'r.
      rewrite -> nat_diff_reduce_add_l in Hx'r.
      exact Hx'r.
    }
  }
  {
    apply gt_as_ge_succ in Hlt.
    unfold ge in Hlt.
    destruct Hlt as [p0 [Hp0 _]].
    right.
    exists (S p0).
    split.
    {
      split.
      rewrite -> add_swap_s in Hp0.
      1: exact Hp0.
      rewrite -> add_swap_s in Hp0.
      rewrite -> Hp0.
      rewrite -> nat_diff_comm.
      rewrite -> nat_diff_reduce_add_l.
      reflexivity.
    }
    {
      intros x' [Hx'l Hx'r].
      rewrite -> Hp0 in Hx'r.
      rewrite -> add_swap_s in Hx'r.
      rewrite -> nat_diff_comm in Hx'r.
      rewrite -> nat_diff_reduce_add_l in Hx'r.
      exact Hx'r.
    }
  }
Qed.

Proposition nat_diff_cancel_l : forall (a b c : nat),
  (nat_diff (a+b) (a+c)) = (nat_diff b c).
Proof.
  intros a b c.
  generalize dependent c.
  generalize dependent b.
  induction a as [| a' IHa'].
  {
    intros c b.
    do 2 rewrite -> add_0_l.
    reflexivity.
  }
  {
    intros b c.
    simpl.
    apply (IHa' b c).
  }
Qed.

Proposition nat_diff_cancel_r : forall (a b c : nat),
  (nat_diff (b+a) (c+a)) = (nat_diff b c).
Proof.
  intros a b c.
  generalize dependent c.
  generalize dependent b.
  induction a as [| a' IHa'].
  {
    intros c b.
    do 2 rewrite -> add_0_r.
    reflexivity.
  }
  {
    intros b c.
    rewrite -> (add_comm b (S a')).
    rewrite -> (add_comm c (S a')).
    simpl.
    rewrite <- (add_comm b a').
    rewrite <- (add_comm c a').
    apply (IHa' b c).
  }
Qed.

Proposition nat_diff_dist_mult_l : forall (a b c : nat),
  ((a * (nat_diff b c)) = (nat_diff (a*b) (a*c)))%nat.
Proof.
  intros a b c.
  destruct (nat_diff_dichotomy b c) as [Hge_bc | Hle_bc].
  {
    destruct Hge_bc as [p0 [[Hp0l Hp0r] _]].
    rewrite -> Hp0r.
    rewrite -> Hp0l.
    rewrite -> mult_dist_over_add.
    rewrite -> nat_diff_reduce_add_l.
    reflexivity.
  }
  {
    destruct Hle_bc as [p0 [[Hp0l Hp0r] _]].
    rewrite -> Hp0r.
    rewrite -> Hp0l.
    rewrite -> mult_dist_over_add.
    rewrite -> nat_diff_comm.
    rewrite -> nat_diff_reduce_add_l.
    reflexivity.
  }
Qed.

Proposition nat_diff_dist_mult_r : forall (a b c : nat),
  (((nat_diff b c) * a) = (nat_diff (b*a) (c*a)))%nat.
Proof.
  intros a b c.
  rewrite -> mult_comm.
  rewrite -> (mult_comm b a).
  rewrite -> (mult_comm c a).
  apply nat_diff_dist_mult_l.
Qed.

Proposition nat_f_has_lower_bound_0 : forall f : nat -> nat,
  forall a : nat, (f a >= 0)%nat.
Proof.
  intros f a.
  unfold ge.
  exists (f a).
  split.
  {
    rewrite -> add_0_l.
    reflexivity.
  }
  {
    intros x' Hx'.
    rewrite -> add_0_l in Hx'.
    exact Hx'.
  }
Qed.

Proposition nat_infinite_descent_implies_f_0_max_1 :
  forall (f : nat -> nat) (n : nat), (forall k: nat, f k > f (S k))%nat -> (f 0 >= f n)%nat.
Proof.
  intros f n H0.
  induction n as [| n' IHn'].
  {
    unfold ge.
    exists (0).
    split.
    {
      rewrite -> add_0_r.
      reflexivity.
    }
    {
      intros x' Hx'.
      apply add_cancel_2 in Hx'.
      exact Hx'.
    }
  }
  {
    specialize (H0 n').
    inversion H0 as [H00 H01].
    apply (ge_trans (f 0) (f n') (f (S n'))).
    1: exact IHn'. 1: exact H00.
  }
Qed.

Proposition nat_infinite_descent_implies_f_0_max_2 :
  forall (f : nat -> nat) (n : nat), (forall k: nat, f k > f (S k))%nat -> (f 0 > f (S n))%nat.
Proof.
  intros f n H0.
  induction n as [| n' IHn'].
  {
    specialize (H0 0).
    exact H0.
  }
  {
    specialize (H0 (S n')).
    specialize (gt_trans (f 0) (f (S n')) (f (S (S n'))) IHn' H0) as H1.
    exact H1.
  }
Qed.

Proposition nat_infinite_descent_implies_at_least_n_decrements :
  forall (f : nat -> nat) (n : nat), 
  (forall k: nat, f k > f (S k))%nat -> ((f 0) >= (f n) + n)%nat.
Proof.
  intros f n H0.
  induction n as [| n'].
  {
    rewrite -> add_0_r.
    apply ge_refl.
  }
  {
    destruct IHn' as [p0 [Hp0 _]].
    unfold ge.
    specialize (nat_infinite_descent_implies_f_0_max_2 f (n') H0) as H1.
    destruct H1 as [[p1 [Hp1 _]] H1r].
    destruct p1 as [| p1'].
    {
      rewrite -> add_0_r in Hp1.
      specialize (H1r Hp1).
      contradiction.
    }
    {
      clear H1r.
      specialize (H0 n') as H1.
      destruct H1 as [[p2 [Hp2 _]] H1r].
      rewrite -> Hp2 in Hp0.
      destruct p2 as [| p2'].
      {
        rewrite -> add_0_r in Hp2.
        specialize (H1r Hp2).
        contradiction.
      }
      {
        clear H1r.
        rewrite <- add_assoc in Hp0.
        rewrite <- add_assoc in Hp0.
        rewrite -> add_swap_s in Hp0.
        rewrite <- add_Sn_m in Hp0.
        rewrite -> add_assoc in Hp0.
        rewrite -> add_assoc_middle in Hp0.
        rewrite -> (add_comm p2' (S n')) in Hp0.
        rewrite <- add_assoc_middle in Hp0.
        exists (p2' + p0)%nat.
        split.
        {
          rewrite -> Hp0.
          reflexivity.
        }
        {
          intros x' Hx'.
          rewrite -> Hp0 in Hx'.
          apply add_cancel in Hx'.
          exact Hx'.
        }
      }
    }
  }
Qed.

Proposition nat_no_infinite_descent : forall f : nat -> nat,
  (forall n, f n > f (S n))%nat -> False.
Proof.
  intros f H0.
  remember (S (f 0)) as m.
  induction m as [| m' IHm'].
  {
    discriminate.
  }
  {
    injection Heqm as Heqm.
    specialize (nat_infinite_descent_implies_at_least_n_decrements f (m') H0) as H1.
    destruct H1 as [p0 [Hp0 _]].
    rewrite <- Heqm in Hp0.
    rewrite <- add_assoc in Hp0.
    rewrite -> add_comm in Hp0.
    rewrite <- add_assoc in Hp0.
    apply -> add_cancel_2 in Hp0.
    symmetry in Hp0.
    apply zero_sum_zero_parts in Hp0.
    destruct Hp0 as [_ Hzfm'].
    specialize (H0 m') as H1.
    rewrite -> Hzfm' in H1.
    specialize (gt_0_l_is_false (f (S m')) H1) as H2.
    contradiction.
  }
Qed.

Proposition nat_le_a_and_ge_succ_a_implies_always : forall (p : Prop) (a b : nat),
  (a >= b -> p)%nat -> (b >= (S a) -> p)%nat -> p.
Proof.
  intros p a b H0 H1.
  destruct (nat_ord_trichotomy_3 a b) as [Heq | [Hgt | Hlt]].
  {
    apply eq_implies_ge in Heq.
    specialize (H0 Heq).
    exact H0.
  }
  {
    apply gt_implies_ge in Hgt.
    specialize (H0 Hgt).
    exact H0.
  }
  {
    apply gt_as_ge_succ in Hlt.
    specialize (H1 Hlt).
    exact H1.
  }
Qed.

Proposition nat_no_sqrt_2 : forall (a : nat),
  (a*a = 2)%nat -> False.
Proof.
  intros a H0.
  apply (nat_le_a_and_ge_succ_a_implies_always _ 1 a).
  {
    intros [p0 [Hp0 _]].
    rewrite -> Hp0 in H0.
    destruct a as [| a'].
    {
      rewrite -> mult_0_l in H0.
      discriminate.
    }
    {
      simpl in H0.
      injection H0 as H0.
      destruct p0 as [| p0'].
      {
        rewrite -> add_0_r in Hp0.
        rewrite -> add_0_r in H0.
        rewrite <- Hp0 in H0.
        rewrite -> mult_ident_r in H0.
        destruct a' as [| a''].
        {
          rewrite -> add_0_r in H0.
          discriminate.
        }
        {
          simpl in H0; discriminate.
        }
      }
      {
        simpl in Hp0.
        injection Hp0 as Hp0.
        symmetry in Hp0.
        apply zero_sum_zero_parts in Hp0 as [_ Hp0].
        discriminate.
      }
    }
  }
  {
    intros H1.
    destruct H1 as [p0 [Hp0 _]].
    rewrite -> Hp0 in H0.
    simpl in H0.
    injection H0 as H0.
    rewrite <- add_swap_s in H0.
    rewrite -> add_Sn_m in H0.
    discriminate.
  }
Qed.

Proposition nat_double_is_same_add_l : forall (a : nat),
  2 * a = a + a.
Proof.
  intros a.
  assert (Hrw : 2 = 1 + 1).
  {
    easy.
  }
  rewrite -> Hrw.
  rewrite -> mult_dist_over_add_r.
  rewrite -> mult_ident.
  reflexivity.
Qed.

Proposition nat_double_is_same_add_r : forall (a : nat),
  a * 2 = a + a.
Proof.
  intros a.
  assert (Hrw : 2 = 1 + 1).
  {
    easy.
  }
  rewrite -> Hrw.
  rewrite -> mult_dist_over_add.
  rewrite -> mult_ident_r.
  reflexivity.
Qed.

Proposition nat_succ_ne_0 : forall (a : nat), ((S a) = 0) -> False.
Proof.
  intros a H0.
  discriminate.
Qed.

Proposition nat_succ_2_ne_1 : forall (a : nat), ((S (S a)) = 1) -> False.
Proof.
  intros a H0.
  discriminate.
Qed.

Proposition nat_mult_preserves_ne : forall (a b : nat),
  ((a = 0) -> False) -> ((b = 0) -> False) -> ((a * b = 0) -> False).
Proof.
  intros a b Hnza Hnzb Hnzab.
  apply mult_no_zero_div in Hnzab.
  destruct Hnzab as [Hza | Hzb].
  {
    specialize (Hnza Hza).
    contradiction.
  }
  {
    specialize (Hnzb Hzb).
    contradiction.
  }
Qed.

Proposition nat_square_preserves_ne : forall (a : nat),
  ((a = 0) -> False) -> ((a * a = 0) -> False).
Proof.
  intros a Hnza Hnzaa.
  apply mult_no_zero_div in Hnzaa.
  apply reduce_p_or_p in Hnzaa.
  specialize (Hnza Hnzaa).
  contradiction.
Qed.

Proposition nat_indivisible_and_divisible_is_false : forall (a b : nat)
  (Hnzb : (b = 0) -> False), (nat_indivisible a b Hnzb) -> (nat_divisible a b) -> False.
Proof.
  intros a b Hnzb Hndiv Hdiv.
  unfold nat_indivisible in Hndiv.
  unfold nat_divisible in Hdiv.
  destruct Hndiv as [p0 [p1 [Hmod Hndiv]]].
  destruct Hdiv as [p2 Hdiv].
  destruct b as [| b'].
  {
    apply gt_0_l_is_false in Hmod.
    contradiction.
  }
  {
    clear Hnzb.
    destruct (nat_ord_trichotomy_3 p0 p2) as [Heq_p0p2 | [Hgt_p0p2 | Hlt_p0p2]].
    {
      rewrite <- Heq_p0p2 in Hdiv.
      rewrite -> Hdiv in Hndiv.
      rewrite -> add_cancel_2 in Hndiv.
      discriminate.
    }
    {
      apply gt_as_ge_succ in Hgt_p0p2.
      destruct Hgt_p0p2 as [p3 [Hp3 _]].
      rewrite -> Hp3 in Hndiv.
      rewrite -> Hdiv in Hndiv.
      rewrite -> mult_dist_over_add_r in Hndiv.
      rewrite -> mult_Sa_b in Hndiv.
      rewrite -> (add_comm (S b')) in Hndiv.
      do 2 rewrite <- add_assoc in Hndiv.
      rewrite -> add_cancel_2 in Hndiv.
      discriminate.
    }
    {
      apply gt_as_ge_succ in Hlt_p0p2.
      destruct Hlt_p0p2 as [p3 [Hp3 _]].
      rewrite -> Hp3 in Hdiv.
      rewrite -> mult_dist_over_add_r in Hdiv.
      rewrite -> Hdiv in Hndiv.
      rewrite -> mult_Sa_b in Hndiv.
      rewrite -> (add_comm (S b')) in Hndiv.
      rewrite <- add_assoc in Hndiv.
      rewrite -> add_cancel in Hndiv.
      rewrite -> add_Sn_m in Hndiv.
      injection Hndiv as Hndiv.
      symmetry in Hndiv.
      destruct p3 as [| p3'].
      {
        rewrite -> mult_0_l in Hndiv.
        rewrite -> add_0_r in Hndiv.
        rewrite -> Hndiv in Hmod.
        apply gt_same_is_false in Hmod.
        contradiction.
      }
      {
        apply gt_succ_as_ge in Hmod.
        destruct Hmod as [p4 [Hp4 _]].
        rewrite -> Hp4 in Hndiv.
        rewrite <- add_assoc in Hndiv.
        apply add_succ_implies_ne_2 in Hndiv.
        contradiction.
      }
    }
  }
Qed.

Proposition nat_indivisible_and_eq_multiple_is_false : forall (a b c : nat)
  (Hnzb : (b = 0) -> False) (Hnzc : (c = 0) -> False), (nat_indivisible a b Hnzb) ->
  (a = b * c) -> False.
Proof.
  intros a b c Hnzb Hnzc Hndiv_ab H0.
  assert (Hdiv_ab : (nat_divisible a b)).
  {
    unfold nat_divisible.
    exists (c).
    rewrite -> mult_comm in H0.
    exact H0.
  }
  specialize (nat_indivisible_and_divisible_is_false a b Hnzb Hndiv_ab Hdiv_ab) as H2.
  contradiction.
Qed.

Proposition nat_even_eq_odd_is_false : forall (a b : nat),
  (2*a = 2*b + 1) -> False.
Proof.
  intros a b H0.
  generalize dependent b.
  induction a as [| a' IHa'].
  {
    intros b H0.
    rewrite -> mult_0_r in H0.
    rewrite -> add_comm in H0.
    discriminate.
  }
  {
    intros b H0.
    rewrite -> mult_a_Sb in H0.
    rewrite -> add_comm in H0.
    destruct b as [| b'].
    {
      rewrite -> mult_0_r in H0.
      rewrite -> add_0_l in H0.
      assert (Hrw: 2 = 1 + 1). 1: easy.
      rewrite -> Hrw in H0; clear Hrw.
      symmetry in H0.
      rewrite -> add_comm in H0.
      repeat rewrite <- add_assoc in H0.
      apply add_cancel_2 in H0.
      discriminate.
    }
    {
      rewrite -> mult_a_Sb in H0.
      rewrite -> add_comm in H0.
      repeat rewrite <- add_assoc in H0.
      rewrite -> add_cancel in H0.
      specialize (IHa' b' H0).
      contradiction.
    }
  }
Qed.

Proposition nat_2_gt_succ_is_1 : forall (a : nat), (2 > S a) <-> ((S a) = 1).
Proof.
  intros a.
  split.
  {
    intros H0.
    apply gt_as_ge_succ in H0.
    destruct H0 as [p0 [Hp0 _]].
    injection Hp0 as Hp0.
    symmetry in Hp0.
    apply zero_sum_zero_parts in Hp0 as [Hp0l Hp0r].
    rewrite -> Hp0l.
    reflexivity.
  }
  {
    intros H0.
    apply gt_as_ge_succ.
    unfold ge.
    exists (0).
    split.
    {
      rewrite -> H0.
      rewrite -> add_0_r.
      reflexivity.
    }
    {
      intros x' Hx'.
      rewrite -> H0 in Hx'.
      apply add_cancel_2 in Hx'.
      exact Hx'.
    }
  }
Qed.

Definition nat_prime (p : nat) (Hnzp : (p = 0) -> False) (Hn1p : (p = 1) -> False) := 
  forall (a : nat) (Hnza : (a = 0) -> False), 
  ((a = 1) -> False) -> ((a = p) -> False) -> (nat_indivisible p a Hnza).

Definition nat_2_is_prime : (nat_prime 2 (nat_succ_ne_0 1) (nat_succ_2_ne_1 0)).
Proof.
  unfold nat_prime.
  intros a Hnza Hne_ap Hne2_a.
  destruct (nat_ord_trichotomy_3 a 2) as [Heq | [Hgt | Hlt]].
  {
    specialize (Hne2_a Heq).
    contradiction.
  }
  {
    unfold nat_indivisible.
    exists (0).
    exists (1).
    split.
    {
      exact Hgt.
    }
    {
      rewrite -> mult_0_l.
      rewrite -> add_0_l.
      reflexivity.
    }
  }
  {
    apply gt_as_ge_succ in Hlt as [p0 [Hp0 _]].
    injection Hp0 as Hp0.
    destruct a as [| a'].
    {
      contradiction.
    }
    {
      injection Hp0 as Hp0.
      symmetry in Hp0.
      apply zero_sum_zero_parts in Hp0 as [Hp0l Hp0r].
      apply <- nat_succ_inject in Hp0l.
      specialize (Hne_ap Hp0l).
      contradiction.
    }
  }
Qed.

Definition nat_strong_induction : forall p : nat -> Prop,
  (forall n, (forall m, n > m -> p m) -> p n) ->
  forall n, p n.
Proof.
  intros p H0 n.
  assert (H1 : forall m, n >= m -> p m).
  {
    intros m H1.
    generalize dependent m.
    induction n as [| n' IHn'].
    {
      intros m H1.
      specialize (H0 0).
      assert (H2 : forall k, 0 > k -> p k).
      {
        intros k H2.
        apply gt_0_l_is_false in H2.
        contradiction.
      }
      specialize (H2 m) as H3.
      apply ge_implies_eq_or_gt in H1.
      destruct H1 as [H1l | H1r].
      {
        specialize (H0 H2) as H4.
        rewrite -> H1l in H4.
        exact H4.
      }
      {
        specialize (H3 H1r).
        exact H3.
      }
    }
    {
      intros m H1.
      apply ge_implies_eq_or_gt in H1.
      destruct H1 as [H1l | H1r].
      {
        assert (H2 : forall k : nat, S n' > k -> p k).
        {
          intros k H2.
          apply gt_as_ge_succ in H2.
          apply ge_is_succ_invariant in H2.
          specialize (IHn' k H2).
          exact IHn'.
        }
        specialize (H0 (S n') H2).
        rewrite -> H1l in H0.
        exact H0.
      }
      {
        apply gt_succ_as_ge in H1r.
        specialize (IHn' m H1r).
        exact IHn'.
      }
    }
  }
  specialize (H1 n (ge_refl n)).
  exact H1.
Qed.

Definition nat_induction : forall p : nat -> Prop,
  (p 0) -> (forall n : nat, (p n) -> (p (S n))) -> (forall n : nat, (p n)).
Proof.
  intros p H0 H1 n.
  induction n as [| n' IHn'].
  {
    exact H0.
  }
  {
    specialize (H1 n').
    apply H1.
    exact IHn'.
  }
Qed.

Definition example_nat_induction_with_strong_ind : forall p : nat -> Prop,
  (p 0) -> (forall n : nat, (p n) -> (p (S n))) -> (forall n : nat, (p n)).
Proof.
  intros p H0 H1 n.
  induction n as [n SIHn] using nat_strong_induction.
  destruct n as [| n'].
  {
    exact H0.
  }
  {
    specialize (SIHn n' (gt_succ_same_l n')).
    specialize (H1 n' SIHn).
    exact H1.
  }
Qed.

Proposition nat_p_adic_valuation : forall (a p : nat) 
  (Hnzp : (p = 0) -> False) (Hn1p : (p = 1) -> False)
  (Hnza : ((a = 0) -> False)) (Hpri_p : nat_prime p Hnzp Hn1p),
  exists k l : nat, (nat_indivisible l p Hnzp) /\ (a = (p**k) * l).
Proof.
  intros a p Hnzp Hn1p Hnza Hpri_p.
  destruct p as [| p']. 
  1: contradiction.
  specialize (nat_euclid_div a p') as [p0 [p1 [Hmod Hdiv]]].
  destruct p1 as [| p1'].
  {
    rewrite -> add_0_r in Hdiv.
    generalize dependent a.
    induction p0 as [p0 SIHp0] using nat_strong_induction.
    intros a Hnza Hdiv.
    assert (Hnzp0 : p0 = 0 -> False).
    {
      intros H0.
      rewrite -> H0 in Hdiv.
      rewrite -> mult_0_l in Hdiv.
      specialize (Hnza Hdiv).
      contradiction.
    }
    destruct (nat_divisibility_dichotomy p0 (S p') Hnzp) as [Hdiv_p0p' | Hndiv_p0p'].
    {
      destruct Hdiv_p0p' as [p2 Hdiv_p0p'].
      rewrite -> Hdiv_p0p' in Hdiv.
      specialize (nat_eq_mult_pos_implies_gt_or_ab_0_or_c_0
        p0 p2 p' Hdiv_p0p') as [Hgt_p0p2 | [[Hzp0 _] | Hzp']].
      {
        specialize (SIHp0 p2 Hgt_p0p2 p0 Hnzp0 Hdiv_p0p') as [p3 [p4 [Hndiv_lSp' Hvp0]]].
        rewrite <- Hdiv_p0p' in Hdiv.
        rewrite -> Hvp0 in Hdiv.
        rewrite <- mult_assoc in Hdiv.
        rewrite -> (mult_comm p4 (S p')) in Hdiv.
        rewrite -> mult_assoc in Hdiv.
        rewrite <- nat_exp_power_succ_r in Hdiv.
        exists (S p3).
        exists (p4).
        split.
        {
          exact Hndiv_lSp'.
        }
        {
          exact Hdiv.
        }
      }
      {
        specialize (Hnzp0 Hzp0).
        contradiction.
      }
      {
        apply <- nat_succ_inject in Hzp'.
        specialize (Hn1p Hzp') as H0.
        contradiction.
      }
    }
    {
      exists (1).
      exists (p0).
      split.
      {
        exact Hndiv_p0p'.
      }
      {
        rewrite -> nat_exp_power_succ_l.
        rewrite -> nat_exp_power_0.
        rewrite -> mult_ident_r.
        rewrite -> mult_comm.
        exact Hdiv.
      }
    }
  }
  {
    specialize (nat_pos_remainder_implies_indivisible a p1' p0 (S p') Hnzp Hmod Hdiv) as H0.
    exists (0).
    exists (a).
    split.
    {
      exact H0.
    }
    {
      rewrite -> nat_exp_power_0.
      rewrite -> mult_ident.
      reflexivity.
    }
  }
Qed.

Proposition nat_no_square_is_double_another : forall (a b : nat),
  ((b = 0) -> False) -> (a*a = 2 * b*b)%nat -> False.
Proof.
  intros a b Hnzb H0.
  destruct a as [| a'].
  {
    rewrite -> mult_0_l in H0.
    symmetry in H0.
    rewrite -> mult_no_zero_div in H0.
    destruct H0 as [H0l | H0r].
    {
      apply mult_no_zero_div in H0l.
      destruct H0l as [H0ll | H0lr].
      {
        discriminate.
      }
      {
        specialize (Hnzb H0lr).
        contradiction.
      }
    }
    {
      specialize (Hnzb H0r).
      contradiction.
    }
  }
  {
    destruct b as [| b'].
    1: contradiction.
    specialize (
      nat_p_adic_valuation (S a') 2 (nat_succ_ne_0 1) (nat_succ_2_ne_1 0) (nat_succ_ne_0 a')
      nat_2_is_prime
    ) as [e0 [p0 [Hndiv_p0 Hv0]]].
    specialize (
      nat_p_adic_valuation (S b') 2 (nat_succ_ne_0 1) (nat_succ_2_ne_1 0) (nat_succ_ne_0 b')
      nat_2_is_prime
    ) as [e1 [p1 [Hndiv_p1 Hv1]]].
    rewrite -> Hv0 in H0.
    rewrite <- mult_assoc in H0.
    rewrite -> (mult_comm (2 ** e0) p0) in H0.
    rewrite -> (mult_comm) in H0.
    do 2 rewrite <- mult_assoc in H0.
    rewrite -> nat_exp_power_add in H0.
    rewrite <- nat_double_is_same_add_l in H0.
    rewrite -> Hv1 in H0.
    repeat rewrite -> mult_assoc in H0.
    rewrite <- nat_exp_power_succ_l in H0.
    repeat rewrite <- mult_assoc in H0.
    rewrite -> (mult_comm (2 ** e1) p1) in H0.
    rewrite -> (mult_comm (2 ** (S e1)) _) in H0.
    repeat rewrite <- mult_assoc in H0.
    rewrite -> nat_exp_power_add in H0.
    rewrite <- (add_1_is_succ e1) in H0.
    rewrite -> (add_comm 1 e1) in H0.
    rewrite -> add_assoc in H0.
    rewrite <- nat_double_is_same_add_r in H0.
    destruct (nat_ord_trichotomy_3 (2 * e0) (e1 * 2 + 1)) as [Heq | [Hgt | Hlt]].
    {
      rewrite -> (mult_comm e1 2) in Heq.
      specialize (nat_even_eq_odd_is_false e0 e1 Heq) as H1.
      contradiction.
    }
    {
      apply gt_as_ge_succ in Hgt.
      destruct Hgt as [p2 [Hp2 _]].
      rewrite -> add_swap_s in Hp2.
      rewrite -> Hp2 in H0.
      rewrite <- add_assoc in H0.
      rewrite -> (add_comm 1 (S p2)) in H0.
      repeat rewrite -> add_assoc in H0.
      repeat rewrite -> mult_assoc in H0.
      apply -> (nat_exp_power_add_cancel_r) in H0.
      rewrite <- (add_0_r (e1 * 2)) in H0.
      repeat rewrite <- add_assoc in H0.
      apply -> (nat_exp_power_add_cancel_l) in H0.
      rewrite -> nat_exp_power_0 in H0.
      rewrite -> mult_ident_r in H0.
      rewrite -> add_0_l in H0.
      rewrite -> nat_exp_power_succ_r in H0.
      repeat rewrite -> mult_assoc in H0.
      rewrite -> mult_comm in H0.
      destruct Hndiv_p1 as [q0 [r0 [Hmod_p1 Hndiv_p1]]].
      assert (Hrw : (p1 * p1) =
                    (2 * (q0 * (q0 * 2) + q0 + q0) + 1)).
      {
        rewrite -> Hndiv_p1.
        apply nat_2_gt_succ_is_1 in Hmod_p1.
        rewrite -> Hmod_p1.
        rewrite -> mult_dist_add_over_add.
        do 2 rewrite -> mult_ident_r.
        rewrite -> mult_ident.
        apply add_cancel_r.
        rewrite -> mult_assoc.
        do 2 rewrite <- mult_dist_over_add_r.
        rewrite -> mult_comm.
        repeat rewrite -> mult_assoc.
        apply mult_cancel_l_3.
        do 2 apply add_cancel_r.
        rewrite -> mult_comm.
        rewrite -> mult_assoc.
        reflexivity.
      }
      rewrite -> Hrw in H0; clear Hrw.
      apply nat_even_eq_odd_is_false in H0.
      contradiction.
    }
    {
      apply gt_as_ge_succ in Hlt.
      destruct Hlt as [p2 [Hp2 _]].
      rewrite -> add_swap_s in Hp2.
      assert (Hrw : (p0 * (p0 * (2 ** 2 * e0)) = p1 * (p1 * (2 ** (e1 * 2 + 1)))) ->
                    (p0 * p0 = 2 * (p1 * p1 * (2 ** p2))) ).
      {
        intros Hrw.
        rewrite -> Hp2 in Hrw.
        rewrite <- (add_0_r (2 * e0)) in Hrw.
        do 2 rewrite -> mult_assoc in Hrw.
        rewrite <- add_assoc in Hrw.
        apply -> (nat_exp_power_add_cancel_l) in Hrw.
        rewrite -> nat_exp_power_0 in Hrw.
        rewrite -> mult_ident_r in Hrw.
        rewrite -> add_0_l in Hrw.
        rewrite -> nat_exp_power_succ_r in Hrw.
        rewrite -> mult_assoc in Hrw.
        rewrite -> (mult_comm _ 2) in Hrw.
        exact Hrw.
      }
      apply Hrw in H0; clear Hrw.
      destruct Hndiv_p0 as [q0 [r0 [Hmod_Sr0 Hndiv_qr0]]].
      assert (Hrw : (p0 * p0) = (q0 * 2 * (q0 * 2) + q0 * 2 + q0 * 2 + 1)).
      {
        rewrite -> Hndiv_qr0.
        apply nat_2_gt_succ_is_1 in Hmod_Sr0.
        rewrite -> Hmod_Sr0.
        rewrite -> mult_dist_add_over_add.
        do 2 rewrite -> mult_ident_r.
        rewrite -> mult_ident.
        reflexivity.
      }
      rewrite -> Hrw in H0; clear Hrw.
      assert (Hrw : (q0 * 2 * (q0 * 2) + q0 * 2 + q0 * 2 + 1) = 
                    (2 * (q0 * (q0 * 2) + q0 + q0) + 1 )).
      {
        apply add_cancel_r.
        rewrite -> (mult_comm q0 2).
        rewrite <- mult_assoc.
        do 2 rewrite <- (mult_dist_over_add 2).
        reflexivity.
      }
      rewrite -> Hrw in H0; clear Hrw.
      symmetry in H0.
      apply nat_even_eq_odd_is_false in H0.
      contradiction.
    }
  }
Qed.

(*\end{nat extra}*)

(*\end{N}*)
