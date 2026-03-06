Proposition ax_nat_distinct : forall a b : nat, (S a) = (S b) <-> a = b.
Proof.
  intros a b.
  split.
  {
    intros H0.
    injection H0 as H1.
    rewrite <- H1.
    reflexivity.
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

Proposition def_add_clause_0 : forall n : nat, 0 + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Proposition def_add_clause_1 : forall n m : nat, (S n) + m = S (n + m).
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
    rewrite -> def_add_clause_0.
    reflexivity.
  }
  {
    rewrite -> def_add_clause_1.
    rewrite -> IHn'.
    reflexivity.
  }
Qed.

Proposition add_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  {
    rewrite -> def_add_clause_0.
    rewrite -> def_add_clause_0.
    reflexivity.
  }
  {
    rewrite -> def_add_clause_1.
    rewrite -> def_add_clause_1.
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
    rewrite -> def_add_clause_0.
    rewrite -> add_0_r.
    reflexivity.
  }
  {
    rewrite -> def_add_clause_1.
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
    rewrite -> def_add_clause_0.
    rewrite -> def_add_clause_0.
    reflexivity.
  }
  {
    rewrite -> def_add_clause_1.
    rewrite -> IHn'.
    rewrite -> def_add_clause_1.
    rewrite <- def_add_clause_1.
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
      rewrite -> def_add_clause_0 in H0.
      rewrite -> def_add_clause_0 in H0.
      rewrite <- H0.
      reflexivity.
    }
    {
      rewrite -> def_add_clause_1 in H0.
      rewrite -> def_add_clause_1 in H0.
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
    rewrite -> (def_add_clause_0 b) in H0.
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
    rewrite -> 2 def_add_clause_0.
    apply add_assoc.
  }
  {
    rewrite -> 4 def_add_clause_1.
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

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

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
        rewrite -> def_add_clause_1 in H0.
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
      rewrite -> def_add_clause_0.
      reflexivity.
    }
  }
Qed.

Proposition add_swap_s : forall a b : nat, S a + b = a + S b.
Proof.
  intros a b.
  rewrite -> def_add_clause_1.
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

Notation "x >= y" := (ge x y) (at level 70) : nat_scope.
Notation "x > y" := (gt x y) (at level 70) : nat_scope.


Proposition ge_refl : forall a : nat, ge a a.
Proof.
  intros a.
  unfold ge.
  destruct a as [| a'] eqn:Ea.
  {
    exists 0.
    split.
    {
      rewrite -> def_add_clause_0.
      reflexivity.
    }
    {
      intros p0 H0.
      rewrite -> def_add_clause_0 in H0.
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
    rewrite <- def_add_clause_1.
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
    rewrite -> def_add_clause_1 in Hp0.
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
        rewrite -> def_add_clause_0.
        reflexivity.
      }
      {
        intros x' Hx'.
        rewrite -> def_add_clause_0 in Hx'.
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
        rewrite -> def_add_clause_1 in H0.
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
  rewrite -> def_add_clause_0 in H0.
  rewrite -> H0.
  reflexivity.
}
{
  rewrite -> def_add_clause_1 in H0.
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
              rewrite -> def_add_clause_1 in Hp1.
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
          rewrite -> def_add_clause_1 in Hp1.
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
        rewrite -> def_add_clause_1.
        apply f_equal.
        rewrite -> def_add_clause_0.
        reflexivity.
      }
      {
        intros x' Hx'.
        rewrite -> def_add_clause_1 in Hx'.
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

Proposition def_mult_clause_0 : forall a : nat, 0 * a = 0.
Proof.
  intros a.
  simpl.
  reflexivity.
Qed.

Proposition def_mult_clause_1 : forall a b : nat, (S a) * b = b + (a * b).
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
    rewrite -> def_mult_clause_0.
    reflexivity.
  }
  {
    rewrite -> def_mult_clause_1.
    rewrite -> def_add_clause_0.
    apply IHa'.
  }
Qed.

Proposition mult_ident : forall a : nat, 1 * a = a.
Proof.
  intros a.
  rewrite -> (def_mult_clause_1 0 a).
  rewrite -> def_mult_clause_0.
  rewrite -> add_0_r.
  reflexivity.
Qed.

Proposition mult_ident_r : forall a : nat, a * 1 = a.
Proof.
  intros a.
  induction a as [| a' IHa'].
  {
    rewrite -> def_mult_clause_0.
    reflexivity.
  }
  {
    rewrite -> def_mult_clause_1.
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
    rewrite -> def_mult_clause_0.
    rewrite -> def_mult_clause_0.
    rewrite -> def_add_clause_0.
    reflexivity.
  }
  {
    rewrite -> def_mult_clause_1.
    rewrite -> def_mult_clause_1.
    rewrite -> IHa'.
    rewrite -> def_add_clause_1.
    rewrite -> def_add_clause_1.
    apply ax_nat_distinct.
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
    rewrite -> def_mult_clause_0.
    rewrite -> mult_0_r.
    reflexivity.
  }
  {
    rewrite -> def_mult_clause_1.
    rewrite -> IHa'.
    rewrite -> mult_unfold_r.
    reflexivity.
  }
Qed.

Proposition mult_dist_over_add : forall a b c : nat, a * (b + c) = a * b + a * c.
Proof.
  intros a b c.
  induction a as [| a' IHa'].
  {
    rewrite -> 3 def_mult_clause_0.
    rewrite -> def_add_clause_0.
    reflexivity.
  }
  {
    rewrite -> 3 def_mult_clause_1.
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
    rewrite -> def_mult_clause_0.
    rewrite -> (def_mult_clause_0 b).
    rewrite -> (def_mult_clause_0 c).
    reflexivity.
  }
  {
    rewrite -> 2 def_mult_clause_1.
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
          rewrite -> def_mult_clause_1 in H0.
          rewrite -> def_add_clause_1 in H0.
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
      rewrite -> def_mult_clause_0.
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
      do 2 rewrite -> def_mult_clause_0.
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

Fixpoint exp (a b : nat) : nat :=
  match b with
  | 0 => 1
  | (S b') => a * (exp a b')
  end.

Notation "x ** y" := (exp x y) (at level 45).

(*\begin{nat extra}*)

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
      rewrite -> def_mult_clause_0.
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

(*\end{nat extra}*)

(*\end{N}*)
