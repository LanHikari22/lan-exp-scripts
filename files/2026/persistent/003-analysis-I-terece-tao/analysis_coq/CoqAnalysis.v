(*\begin{N}*)
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

Notation "x >= y" := (ge x y) (at level 70).
Notation "x > y" := (gt x y) (at level 70).


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


(*\end{N}*)

(*\begin{Z}*)

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

(*\end{Z extra}*)

(*\end{Z}*)

(*\begin{Q}*)

Record Q : Type := {
  num : Z;
  den : Z_nz
}.

(*
  a / b = c / d <->
  a * d = c * b 
*)
Definition q_eq (a b : Q) : Prop :=
  ((num a * (proj1_sig (den b)))%Z ~= (num b * (proj1_sig (den a)))%Z)%Z.

Declare Scope Q_scope.
Bind Scope Q_scope with Q.
Delimit Scope Q_scope with Q.

Notation "x ~= y" := (q_eq x y) (at level 70) : Q_scope.
Notation "x /Q y" := {| num := x; den := y |} (at level 60) : Q_scope.

Open Scope Q_scope.

Proposition q_reduce_num : forall (a : Z) (b : Z_nz), (num {| num:= a; den:= b |}) = a.
Proof.
  intros a b.
  simpl.
  reflexivity.
Qed.

Proposition q_reduce_den : forall (a : Z) (b : Z_nz), (den {| num:= a; den:= b |}) = b.
Proof.
  intros a b.
  simpl.
  reflexivity.
Qed.

Close Scope Q_scope.

(*\begin{q_eq is an equivilance}*)

Proposition q_eq_refl : forall a : Q, (a ~= a)%Q.
Proof.
  intros [a_ _a].
  unfold q_eq.
  rewrite -> q_reduce_num.
  rewrite -> q_reduce_den.
  reflexivity.
Qed.

Proposition q_eq_sym : forall a b : Q, (a ~= b)%Q -> (b ~= a)%Q.
Proof.
  intros [a_ _a] [b_ _b].
  unfold q_eq.
  do 2 rewrite -> q_reduce_num.
  do 2 rewrite -> q_reduce_den.
  intros H0.
  rewrite -> H0.
  reflexivity.
Qed.

Proposition q_eq_trans : forall a b c : Q, (a ~= b)%Q -> (b ~= c)%Q -> (a ~= c)%Q.
Proof.
  intros [a_ [_a _anz]] [b_ [_b _bnz]] [c_ [_c _cnz]] H0 H1.
  unfold q_eq in *.
  do 2 rewrite -> q_reduce_num in *.
  do 2 rewrite -> q_reduce_den in *.
  do 2 rewrite -> z_nz_reduce_proj1_sig in *.
  assert (H2 : ((a_ * _b) * (b_ * _c) ~= (b_ * _a) * (c_ * _b))%Z).
  {
    apply (z_mult_from_two_equations).
    apply H0.
    apply H1.
  }
  repeat rewrite <- z_mult_assoc in H2.
  (* v H2 : a_ * _b * b_ * _c ~= [...] *)
  rewrite -> (z_mult_comm_cdab) in H2.
  (* ^ H2 : b_ * _c * a_ * _b *)
  apply (z_mult_cancel_r) in H2.
  2: apply _bnz.
  repeat rewrite -> z_mult_assoc in H2.
  destruct (z_trichotomy_3 b_) as [Hzb_ | [Hpb_ | Hnb_]].
  {
    clear H2.
    rewrite -> Hzb_ in H0.
    rewrite -> Hzb_ in H1.
    rewrite -> z_mult_0_l in H0.
    rewrite -> z_mult_0_l in H1.
    apply z_mult_no_zero_div in H0.
    destruct H0 as [H0l | H0r].
    {
      rewrite -> H0l.
      rewrite -> z_mult_0_l.
      symmetry in H1.
      apply z_mult_no_zero_div in H1.
      destruct H1 as [H1l | H1r].
      {
        rewrite -> H1l.
        rewrite -> z_mult_0_l.
        reflexivity.
      }
      {
        contradiction.
      }
    }
    {
      contradiction.
    }
  }
  {
    apply (z_trichotomy_1) in Hpb_ as [Hnzb_ _].
    apply (z_mult_cancel_l) in H2.
    2: apply Hnzb_.
    rewrite -> z_mult_comm in H2.
    rewrite -> (z_mult_comm _a) in H2.
    exact H2.
  }
  {
    apply (z_trichotomy_2) in Hnb_ as [Hnzb_ _].
    apply (z_mult_cancel_l) in H2.
    2: apply Hnzb_.
    rewrite -> z_mult_comm in H2.
    rewrite -> (z_mult_comm _a) in H2.
    exact H2.
  }
Qed.

Require Import Stdlib.Setoids.Setoid.
Add Parametric Relation : Q q_eq
  reflexivity proved by q_eq_refl
  symmetry proved by q_eq_sym
  transitivity proved by q_eq_trans
  as Q_setoid.

Proposition q_eq_trans_2 : forall a b c : Q, (a ~= b)%Q -> (b ~= c)%Q -> (a ~= c)%Q.
Proof.
  intros a b c H0 H1.
  rewrite -> H0.
  rewrite -> H1.
  reflexivity.
Qed.

(*
  (
    (a /Q b) + (c /Q d) ~= (ad /Q bd) + (bc /Q bd) ~= (ad + bc) /Q bd
  )%Q
*)
Open Scope Z_scope.
Definition q_add (a b : Q) : Q :=
  {|
    num := ((num a) * (proj1_sig (den b))) + (proj1_sig (den a) * (num b));
    den := ((den a) * (den b))%Z_nz
  |}.
Close Scope Z_scope.

Notation "x + y" := (q_add x y) (at level 50, left associativity) : Q_scope.

Require Import Stdlib.Classes.Morphisms.
Instance q_add_proper : 
  Proper (q_eq ==> q_eq ==> q_eq ) q_add.
Proof.
  intros a a' Ha b b' Hb.
  transitivity (q_add a' b).
  {
    (* Goal : (q_add a b ~= q_add a' b)%Q *)
    destruct a as [a_ [_a Hnz_a]].
    destruct a' as [a_' [_a' Hnz_a']].
    destruct b as [b_ [_b Hnz_b]].
    destruct b' as [b_' [_b' Hnz_b']].
    unfold q_add, q_eq in *.
    do 4 rewrite -> q_reduce_num in *.
    do 4 rewrite -> q_reduce_den in *.
    do 3 rewrite -> z_nz_reduce_proj1_sig in *.
    do 1 rewrite -> z_nz_mult_reduce_proj1_sig in *.
    do 1 rewrite -> q_reduce_num in *.
    do 1 rewrite -> q_reduce_den in *.
    do 1 rewrite -> z_nz_mult_reduce_proj1_sig in *.
    repeat rewrite <- z_mult_assoc.
    do 4 rewrite -> (z_mult_dist_over_add_r).
    repeat rewrite <- z_mult_assoc.
    (* v Goal : a_ * _b * _a' (...) *)
    rewrite -> (z_mult_comm _ _a').
    repeat rewrite <- z_mult_assoc.
    rewrite -> (z_mult_comm _a' _).
    (* ^ Goal : a_ * _a' * _b (...) *)
    rewrite -> Ha.
    rewrite -> (z_mult_comm_acbd a_' _b _a _b).
    rewrite -> z_add_cancel_l.
    rewrite -> (z_mult_comm_cbad _a b_ _a' _b).
    reflexivity.
  }
  {
    (* Goal : (q_add a' b ~= q_add a' b')%Q *)
    destruct a as [a_ [_a Hnz_a]].
    destruct a' as [a_' [_a' Hnz_a']].
    destruct b as [b_ [_b Hnz_b]].
    destruct b' as [b_' [_b' Hnz_b']].
    unfold q_add, q_eq in *.
    do 4 rewrite -> q_reduce_num in *.
    do 4 rewrite -> q_reduce_den in *.
    do 3 rewrite -> z_nz_reduce_proj1_sig in *.
    do 1 rewrite -> z_nz_mult_reduce_proj1_sig in *.
    do 1 rewrite -> q_reduce_num in *.
    do 1 rewrite -> q_reduce_den in *.
    do 1 rewrite -> z_nz_mult_reduce_proj1_sig in *.
    repeat rewrite <- z_mult_assoc.
    do 4 rewrite -> (z_mult_dist_over_add_r).
    repeat rewrite <- z_mult_assoc.
    rewrite -> (z_mult_comm_adcb a_' _b _a' _b').
    apply z_add_cancel_l.
    rewrite -> (z_mult_comm_bdac _a' b_ _a' _b').
    rewrite -> Hb.
    rewrite -> (z_mult_comm_cadb b_' _b _a' _a').
    reflexivity.
  }
Qed.

Open Scope Q_scope.
Proposition q_add_respects_equivalence : forall a b c : Q, a ~= b -> a + c ~= b + c.
Proof.
  intros a b c H0.
  rewrite <- H0.
  reflexivity.
Qed.
Close Scope Q_scope.

(*
(
  (a /Q b) * (c /Q d) ~= (a * c) /Q (b * d)
)%Q
*)
Definition q_mult (a b : Q) : Q :=
  {|
    num := (num a) * (num b);
    den := (den a) * (den b);
  |}.

Notation "x * y" := (q_mult x y) (at level 40, left associativity) : Q_scope.

Require Import Stdlib.Classes.Morphisms.
Instance q_mult_proper : 
  Proper (q_eq ==> q_eq ==> q_eq ) q_mult.
Proof.
  intros a a' Ha b b' Hb.
  transitivity (q_mult a' b).
  {
    (* Goal : (a * b ~= a' * b)%Q *)
    destruct a as [a_ [_a Hnz_a]].
    destruct a' as [a_' [_a' Hnz_a']].
    destruct b as [b_ [_b Hnz_b]].
    destruct b' as [b_' [_b' Hnz_b']].
    unfold q_mult, q_eq in *.
    do 5 rewrite -> q_reduce_num in *.
    do 5 rewrite -> q_reduce_den in *.
    do 2 rewrite -> z_nz_reduce_proj1_sig in *.
    do 2 rewrite -> z_nz_mult_reduce_proj1_sig in *.
    repeat rewrite <- z_mult_assoc.
    rewrite -> (z_mult_comm_acbd a_ b_ _a' _b).
    rewrite -> Ha.
    rewrite -> (z_mult_comm_acbd a_' _a b_ _b).
    reflexivity.
  }
  {
    (* Goal : (a' * b ~= a' * b')%Q *)
    destruct a as [a_ [_a Hnz_a]].
    destruct a' as [a_' [_a' Hnz_a']].
    destruct b as [b_ [_b Hnz_b]].
    destruct b' as [b_' [_b' Hnz_b']].
    unfold q_mult, q_eq in *.
    do 5 rewrite -> q_reduce_num in *.
    do 5 rewrite -> q_reduce_den in *.
    do 2 rewrite -> z_nz_reduce_proj1_sig in *.
    do 2 rewrite -> z_nz_mult_reduce_proj1_sig in *.
    repeat rewrite <- z_mult_assoc.
    rewrite -> (z_mult_comm_bdac a_' b_ _a' _b').
    rewrite -> Hb.
    rewrite -> (z_mult_comm_cadb b_' _b a_' _a').
    reflexivity.
  }
Qed.

Open Scope Q_scope.
Proposition q_mult_respects_equivalence : forall a b c : Q, a ~= b -> a * c ~= b * c.
Proof.
  intros a b c H0.
  rewrite <- H0.
  reflexivity.
Qed.
Close Scope Q_scope.

Definition q_neg (a : Q) : Q :=
  {|
    num := (-- (num a))%Z;
    den := (den a)
  |}.

Notation "-- x" := (q_neg x) (at level 45) : Q_scope.

Require Import Stdlib.Classes.Morphisms.
Instance q_neg_proper : 
  Proper (q_eq ==> q_eq ) q_neg.
Proof.
  intros [a_ [_a Hnz_a]] [a_' [_a' Hnz_a']] Ha.
    unfold q_neg, q_eq in *.
    do 4 rewrite -> q_reduce_num in *.
    do 4 rewrite -> q_reduce_den in *.
    do 2 rewrite -> z_nz_reduce_proj1_sig in *.
    do 2 rewrite -> z_neg_extract_from_mult_l.
    rewrite <- z_neg_inject.
    exact Ha.
Qed.

Open Scope Q_scope.
Proposition q_neg_respects_equivalence : forall a a' : Q, a ~= a' -> --a ~= --a'.
Proof.
  intros a a' H0.
  rewrite -> H0.
  reflexivity.
Qed.
Close Scope Q_scope.

(*\end{q_eq is an equivilance}*)

Definition ZQ (a : Z) : Q :=
  {|
    num := a;
    den := z_nz_1
  |}.

Notation "ZQ# x" := (ZQ x) (at level 60).
Notation "NQ# x" := (ZQ (NZ x)) (at level 60).

Proposition q_nq_reduce_num : forall a : nat, (num (NQ# a)) = (NZ# a).
Proof.
  intros a.
  simpl.
  reflexivity.
Qed.

Proposition q_nq_reduce_den : forall a : nat, (den (NQ# a)) = z_nz_1.
Proof.
  intros a.
  simpl.
  reflexivity.
Qed.

Proposition q_num_0_is_eqv_0 : forall (a : Z) (b : Z_nz), 
  ((a /Q b) ~= (NQ#0))%Q <-> (a ~= (NZ# 0))%Z.
Proof.
  intros a b.
  split.
  {
    intros H0.
    unfold q_eq in H0.
    do 1 rewrite -> q_reduce_num in *.
    do 1 rewrite -> q_reduce_den in *.
    do 1 rewrite -> q_nq_reduce_num in *.
    do 1 rewrite -> q_nq_reduce_den in *.
    do 1 rewrite -> z_nz_reduce_proj1_sig_for_1 in *.
    rewrite -> z_mult_ident_r in H0.
    rewrite -> z_mult_0_l in H0.
    exact H0.
  }
  {
    intros H0.
    unfold q_eq in *.
    do 1 rewrite -> q_reduce_num in *.
    do 1 rewrite -> q_reduce_den in *.
    do 1 rewrite -> q_nq_reduce_num in *.
    do 1 rewrite -> q_nq_reduce_den in *.
    do 1 rewrite -> z_nz_reduce_proj1_sig_for_1 in *.
    rewrite -> z_mult_ident_r.
    rewrite -> z_mult_0_l.
    exact H0.
  }
Qed.

Definition Q_nz := { a : Q | ((num a) ~= (NZ#0))%Z -> False }.

Declare Scope Q_nz_scope.
Bind Scope Q_nz_scope with Q_nz.
Delimit Scope Q_nz_scope with Q_nz.

Notation Q_nz_ex := (exist (fun a : Q => (((num a) ~= (NZ#0))%Z -> False))).

Definition q_nz_from_q (a : Q) (H : ((num a) ~= (NZ#0))%Z -> False) : Q_nz.
Proof.
  exists (
    {|
      num := (num a);
      den := (den a)
    |}
  ).
  exact H.
Defined.

Definition q_nz_recip (a : Q_nz) : Q_nz :=
  (q_nz_from_q 
    {|
      num := (proj1_sig (den (proj1_sig a)));
      den := (Z_nz_ex (num (proj1_sig a)) (proj2_sig a))
    |}
    (proj2_sig (den (proj1_sig a)))
  ).

Notation "x **-1" := (q_nz_recip x) (at level 45) : Q_nz_scope.

Definition ZQ_nz (a : Z_nz) : Q_nz :=
  (q_nz_from_q
    {|
      num := (proj1_sig a);
      den := z_nz_1
    |}
    (proj2_sig a)
  ).

Definition q_nz_1 : Q_nz.
Proof.
  exists ((NQ# 1)).
  intros H0.
  discriminate.
Defined.

Definition q_nz_mult (a b : Q_nz) : Q_nz.
Proof.
  destruct b as [b Hnzb].
  destruct a as [a Hnza].
  exists (a * b)%Q.
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
Defined.

Notation "x * y" := (q_nz_mult x y) (at level 40, left associativity) : Q_nz_scope.

(*\begin{Q is a field}*)

Open Scope Q_scope.

Proposition q_add_comm : forall a b : Q, a + b ~= b + a.
Proof.
  intros [a [b Hnzb]] [c [d Hnzd]].
  unfold q_add.
  unfold q_eq.
  do 4 rewrite -> q_reduce_den in *.
  do 4 rewrite -> q_reduce_num in *.
  do 2 rewrite -> z_nz_reduce_proj1_sig in *.
  do 2 rewrite -> z_nz_mult_reduce_proj1_sig in *.
  rewrite -> (z_add_comm (c * b) (d * a)).
  rewrite -> (z_mult_comm d a).
  rewrite -> (z_mult_comm c b).
  rewrite -> (z_mult_comm d b).
  reflexivity.
Qed.

Proposition q_add_assoc : forall a b c : Q, (a + b) + c ~= a + (b + c).
Proof.
  intros [a [b Hnzb]] [c [d Hnzd]] [e [f Hnzf]].
  unfold q_add.
  unfold q_eq.
  do 7 rewrite -> q_reduce_den in *.
  do 7 rewrite -> q_reduce_num in *.
  do 3 rewrite -> z_nz_reduce_proj1_sig in *.
  do 2 rewrite -> z_nz_mult_reduce_proj1_sig in *.
  do 1 rewrite -> z_nz_mult3_reduce_proj1_sig_assoc1 in *.
  do 1 rewrite -> z_nz_mult3_reduce_proj1_sig_assoc2 in *.
  do 4 rewrite -> z_mult_dist_over_add_r.
  repeat rewrite <- z_mult_assoc.
  do 1 rewrite -> z_mult_dist_over_add_l.
  repeat rewrite <- z_mult_assoc.
  do 3 rewrite -> z_mult_dist_over_add_r.
  repeat rewrite <- z_add_assoc.
  reflexivity.
Qed.

Proposition q_add_0_l : forall a : Q, (NQ#0) + a ~= a.
Proof.
  intros [a [b Hnzb]].
  unfold q_add.
  unfold q_eq.
  do 2 rewrite -> q_reduce_den in *.
  do 2 rewrite -> q_reduce_num in *.
  do 1 rewrite -> z_nz_reduce_proj1_sig in *.
  do 1 rewrite -> q_nq_reduce_den in *.
  do 1 rewrite -> q_nq_reduce_num in *.
  do 1 rewrite -> z_nz_reduce_proj1_sig_for_1 in *.
  do 1 rewrite -> z_nz_mult_ident_l in *.
  do 1 rewrite -> z_nz_reduce_proj1_sig in *.
  rewrite -> z_mult_0_l.
  rewrite -> z_add_0_l.
  rewrite -> z_mult_ident_l.
  reflexivity.
Qed.

Proposition q_add_0_r : forall a : Q, a + (NQ#0) ~= a.
Proof.
  intros a.
  rewrite -> q_add_comm.
  apply q_add_0_l.
Qed.

Proposition q_additive_inverse_l : forall a : Q, (-- a) + a ~= (NQ#0).
Proof.
  intros [a [b Hnzb]].
  unfold q_neg.
  unfold q_add.
  unfold q_eq.
  do 3 rewrite -> q_reduce_den in *.
  do 3 rewrite -> q_reduce_num in *.
  do 1 rewrite -> z_nz_reduce_proj1_sig in *.
  do 1 rewrite -> q_nq_reduce_den in *.
  do 1 rewrite -> q_nq_reduce_num in *.
  do 1 rewrite -> z_nz_reduce_proj1_sig_for_1 in *.
  do 1 rewrite -> z_nz_mult_reduce_proj1_sig in *.
  rewrite -> z_mult_ident_r.
  rewrite -> z_mult_0_l.
  rewrite -> z_neg_extract_from_mult_l.
  rewrite -> z_add_comm.
  rewrite -> z_sub_refold.
  rewrite -> (z_mult_comm b a).
  rewrite -> z_sub_same_eqv_0.
  reflexivity.
Qed.

Proposition q_additive_inverse_r : forall a : Q, a + (-- a) ~= (NQ#0).
Proof.
  intros a.
  rewrite -> q_add_comm.
  apply q_additive_inverse_l.
Qed.

Proposition q_mult_comm : forall a b : Q, a * b ~= b * a.
Proof.
  intros [a [b Hnzb]] [c [d Hnzd]].
  unfold q_mult.
  unfold q_eq.
  do 4 rewrite -> q_reduce_den in *.
  do 4 rewrite -> q_reduce_num in *.
  do 2 rewrite -> z_nz_mult_reduce_proj1_sig in *.
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_badc.
  reflexivity.
Qed.

Proposition q_mult_assoc : forall a b c : Q, (a * b) * c ~= a * (b * c).
Proof.
  intros [a [b Hnzb]] [c [d Hnzd]] [e [f Hnzf]].
  unfold q_mult.
  unfold q_eq.
  do 7 rewrite -> q_reduce_den in *.
  do 7 rewrite -> q_reduce_num in *.
  do 1 rewrite -> z_nz_mult3_reduce_proj1_sig_assoc1 in *.
  do 1 rewrite -> z_nz_mult3_reduce_proj1_sig_assoc2 in *.
  repeat rewrite <- z_mult_assoc.
  reflexivity.
Qed.

Proposition q_mult_ident_l : forall a : Q, (NQ#1) * a ~= a.
Proof.
  intros [a [b Hnzb]].
  unfold q_mult.
  unfold q_eq.
  do 2 rewrite -> q_reduce_den in *.
  do 2 rewrite -> q_reduce_num in *.
  do 1 rewrite -> q_nq_reduce_den in *.
  do 1 rewrite -> q_nq_reduce_num in *.
  do 1 rewrite -> z_nz_reduce_proj1_sig in *.
  unfold z_nz_1.
  do 1 rewrite -> z_nz_mult_reduce_proj1_sig in *.
  do 2 rewrite -> z_mult_ident_l.
  reflexivity.
Qed.

Proposition q_mult_ident_r : forall a : Q, a * (NQ#1) ~= a.
Proof.
  intros a.
  rewrite -> (q_mult_comm a (NQ#1)).
  apply q_mult_ident_l.
Qed.

Proposition q_mult_dist_over_add_l : forall a b c : Q, a * (b + c) ~= (a * b) + (a * c).
Proof.
  intros [a [b Hnzb]] [c [d Hnzd]] [e [f Hnzf]].
  unfold q_add.
  unfold q_mult.
  unfold q_eq.
  do 8 rewrite -> q_reduce_den in *.
  do 8 rewrite -> q_reduce_num in *.
  do 2 rewrite -> z_nz_reduce_proj1_sig in *.
  do 2 rewrite -> z_nz_mult_reduce_proj1_sig in *.
  do 1 rewrite -> z_nz_mult3_reduce_proj1_sig_assoc2 in *.
  (* v Goal : (...) proj1_sig (
    ((Z_nz_exb Hnzb)) * ((Z_nz_exd Hnzd)) * (((Z_nz_exb Hnzb)) * ((Z_nz_exf Hnzf))) (...) *)
  simpl.
  (* ^ Goal : (...) b * d * (b * f) (...) *)
  do 1 rewrite -> z_mult_dist_over_add_l.
  do 2 rewrite -> z_mult_dist_over_add_r.
  repeat rewrite <- z_mult_assoc.
  (* v Goal : a * c * f * b * d * b * f [...]*)
  rewrite <- (z_mult_ident_l (a * c * f * b * d * b * f)%Z).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_ident_r.
  (* ^ Goal : a * c * b * f * b * d * f [...]*)
  (* v Goal : [...] a * d * e * b * d * b * f [...]*)
  rewrite <- (z_mult_ident_l (a * d * e * b * d * b * f)%Z).
  repeat rewrite <- z_mult_assoc.
  rewrite -> z_mult_comm_8_a0_swap_a7.
  rewrite -> z_mult_comm_8_a0_swap_a6.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_comm_8_a0_swap_a2.
  rewrite -> z_mult_comm_8_a0_swap_a1.
  rewrite -> z_mult_ident_r.
  (* ^ Goal : [...] b * d * a * e * b * d * f [...]*)
  reflexivity.
Qed.

Proposition q_mult_dist_over_add_r : forall a b c : Q, (b + c) * a ~= (b * a) + (c * a).
Proof.
  intros a b c.
  rewrite -> q_mult_comm.
  rewrite -> (q_mult_comm b a).
  rewrite -> (q_mult_comm c a).
  apply q_mult_dist_over_add_l.
Qed.

Proposition q_nz_multiplicative_inverse_l : forall a : Q_nz, 
  (proj1_sig (a * (a**-1))%Q_nz) ~= (NQ#1).
Proof.
  intros [[a [b Hnzb]] Hnza].
  unfold q_nz_recip.
  simpl.
  unfold q_eq.
  unfold q_mult.
  do 1 rewrite -> q_nq_reduce_den.
  do 1 rewrite -> q_nq_reduce_num.
  do 1 rewrite -> z_nz_reduce_proj1_sig_for_1.
  do 3 rewrite -> q_reduce_den.
  do 3 rewrite -> q_reduce_num.
  rewrite -> z_mult_ident_r.
  rewrite -> z_mult_ident_l.
  rewrite -> z_nz_mult_reduce_proj1_sig.
  rewrite -> z_mult_comm.
  reflexivity.
Qed.

Proposition q_nz_multiplicative_inverse_r : forall a : Q_nz, 
  (proj1_sig ((a**-1) * a)%Q_nz) ~= (NQ#1).
Proof.
  intros [[a [b Hnzb]] Hnza].
  unfold q_nz_recip.
  simpl.
  unfold q_eq.
  unfold q_mult.
  do 1 rewrite -> q_nq_reduce_den.
  do 1 rewrite -> q_nq_reduce_num.
  do 1 rewrite -> z_nz_reduce_proj1_sig_for_1.
  do 3 rewrite -> q_reduce_den.
  do 3 rewrite -> q_reduce_num.
  rewrite -> z_mult_ident_r.
  rewrite -> z_mult_ident_l.
  rewrite -> z_nz_mult_reduce_proj1_sig.
  rewrite -> z_mult_comm.
  reflexivity.
Qed.

Close Scope Q_scope.

(*\end{Q is a field}*)

Definition q_sub (a b : Q) : Q :=
  a + (-- b).

Notation "x - y" := (q_sub x y) (at level 50, left associativity) : Q_scope.

Definition q_div (a : Q) (b : Q_nz) : Q :=
  a * (proj1_sig (b**-1))%Q_nz.

Notation "x / y" := (q_div x y) (at level 40, left associativity) : Q_scope.

Open Scope Q_scope.

Proposition q_formal_div_as_div : forall (a b : Z) (Hnzb : ((b ~= (NZ#0))%Z -> False)),
  {| num := a; den := (Z_nz_ex b Hnzb) |} ~= ((ZQ#a) / (Q_nz_ex (ZQ#b) Hnzb)).
Proof.
  intros a b Hnzb.
  unfold q_div.
  unfold q_mult.
  unfold q_eq.
  simpl.
  rewrite -> z_mult_ident_r.
  rewrite -> z_mult_ident_l.
  reflexivity.
Qed.

Definition q_is_pos (a : Q) :=
  exists (k l : nat) (Hnzl : ((NZ#S(l)) ~= (NZ#0))%Z -> False), 
  a ~= {| num := (NZ#S(k)); den := (Z_nz_ex (NZ#S(l)) Hnzl)|}.

Definition q_is_neg (a : Q) :=
  exists (k : Q) (H : (q_is_pos k)), a ~= (-- k).

Definition q_is_pos_no_succ (a : Q) :=
  exists (k l : nat) (Hnzk : ((NZ#k) ~= (NZ#0))%Z -> False) 
  (Hnzl : ((NZ#l) ~= (NZ#0))%Z -> False), 
  a ~= {| num := (NZ#k); den := (Z_nz_ex (NZ#l) Hnzl)|}.

Proposition q_is_pos_as_pos_no_succ : forall a : Q, (q_is_pos a) <-> (q_is_pos_no_succ a).
Proof.
  intros [a [b Hnzb]].
  split.
  {
    intros [p0 [p1 [H0 H1]]].
    unfold q_is_pos_no_succ.
    assert (H2 : ((NZ# S p0) ~= (NZ#0))%Z -> False ).
    {
      easy.
    }
    exists (S p0).
    exists (S p1).
    exists (H2).
    exists (H0).
    exact H1.
  }
  {
    intros [p0 [p1 [H0 [H1 H2]]]].
    unfold q_is_pos.
    destruct p0 as [| p0'].
    {
      exfalso.
      apply H0.
      reflexivity.
    }
    {
      destruct p1 as [| p1'].
      {
        exfalso.
        apply H1.
        reflexivity.
      }
      {
        exists (p0').
        exists (p1').
        exists (H1).
        exact H2.
      }
    }
  }
Qed.

Proposition q_trichotomy_0 : forall a : Q, 
  a ~= (NQ#0) -> 
  ((q_is_pos a) -> False) /\
  ((q_is_neg a) -> False).
Proof.
  intros a H0.
  split.
  {
    intros H1.
    unfold q_is_pos in H1.
    destruct H1 as [p0 [p1 [Hnzl H1]]].
    rewrite -> H0 in H1.
    unfold q_eq in H1.
    simpl in H1.
    rewrite -> z_mult_0_l in H1.
    rewrite -> z_mult_ident_r in H1.
    discriminate.
  }
  {
    intros H1.
    unfold q_is_neg in H1.
    destruct H1 as [p0 [Hpos H1]].
    rewrite -> H0 in H1.
    unfold q_eq in H1.
    simpl in H1.
    rewrite -> z_mult_0_l in H1.
    rewrite -> z_mult_ident_r in H1.
    destruct p0 as [[b c] [[d e] Hnz_p0]].
    simpl in H1.
    destruct Hpos as [p1 [p2 [Hnzl H2]]].
    unfold q_eq in H2.
    simpl in H2.
    unfold z_neg in H1.
    simpl in H1.
    unfold z_eq in H1.
    simpl in H1.
    rewrite -> add_0_r in H1.
    rewrite -> H1 in H2.
    rewrite -> z_same_parts_eqv_0 in H2.
    rewrite -> z_mult_0_l in H2.
    symmetry in H2.
    apply z_mult_no_zero_div in H2 as [H2l | H2r].
    {
      discriminate.
    }
    {
      apply Hnz_p0.
      exact H2r.
    }
  }
Qed.

Proposition q_trichotomy_1 : forall a : Q, 
  (q_is_pos a) ->
  ((a ~= (NQ#0)) -> False) /\
  ((q_is_neg a) -> False).
Proof.
  intros [a_ [_a Hnz_a]] H0.
  split.
  {
    intros H1.
    apply q_trichotomy_0 in H1 as [H1l H1r].
    apply H1l.
    exact H0.
  }
  {
    intros H1.
    destruct H1 as [[b [c Hnzc]] [[p1 [p2 [Hnzp2 H1]]] H2]].
    destruct H0 as [p3 [p4 [Hnzp4 H3]]].
    unfold q_neg in H2.
    unfold q_eq in H2.
    simpl in H2.
    rewrite -> z_neg_extract_from_mult_l in H2.
    unfold q_eq in H3.
    simpl in H3.
    unfold q_eq in H1.
    simpl in H1.
    destruct (z_trichotomy_3 a_) as [Hza_ | [Hpa_ | Hna_]].
    {
      rewrite -> Hza_ in H2.
      rewrite -> z_mult_0_l in H2.
      rewrite -> z_neg_both_sides in H2.
      rewrite -> z_neg_reduce_double in H2.
      rewrite -> z_neg_reduce_neg_0 in H2.
      symmetry in H2.
      apply z_mult_no_zero_div in H2 as [H2l | H2r].
      {
        rewrite -> H2l in H1.
        rewrite -> z_mult_0_l in H1.
        symmetry in H1.
        apply z_mult_no_zero_div in H1 as [H1l | H1r].
        {
          discriminate.
        }
        {
          apply Hnzc.
          exact H1r.
        }
      }
      {
        apply Hnz_a.
        exact H2r.
      }
    }
    {
      destruct Hpa_ as [p5 [Hp5 _]].
      rewrite -> Hp5 in H2.
      destruct (z_trichotomy_3 c) as [Hzc | [Hpc | Hnc]].
      {
        apply Hnzc.
        exact Hzc.
      }
      {
        destruct Hpc as [p6 [Hp6 _]].
        rewrite -> Hp6 in H2.
        rewrite -> Hp6 in H1.
        rewrite -> z_mult_reduce_pos_pos in H2.
        rewrite -> z_mult_reduce_pos_pos in H1.
        rewrite -> Hp5 in H3.
        rewrite -> z_mult_reduce_pos_pos in H3.
        apply z_mult_rem_pos_implies_pos in H1 as [p7 [Hp7 _]].
        rewrite -> Hp7 in H2.
        symmetry in H3.
        rewrite -> z_mult_comm in H3.
        apply z_mult_rem_pos_implies_pos in H3 as [p8 [Hp8 _]].
        rewrite -> Hp8 in H2.
        rewrite -> z_mult_reduce_pos_pos in H2.
        apply z_pos_ne_neg in H2.
        exact H2.
      }
      {
        destruct Hnc as [p6 [Hp6 _]].
        rewrite -> Hp6 in H1.
        rewrite -> z_neg_extract_from_mult_r in H1.
        rewrite -> Hp5 in H3.
        rewrite -> z_mult_reduce_pos_pos in H3.
        symmetry in H3.
        rewrite -> z_mult_comm in H3.
        apply z_mult_rem_pos_implies_pos in H3 as [p7 [Hp7 _]].
        rewrite -> z_mult_reduce_pos_pos in H1.
        apply z_mult_rhs_neg_part_neg in H1 as [p8 [Hp8 _]].
        rewrite -> Hp6 in H2.
        rewrite -> Hp7 in H2.
        rewrite -> Hp8 in H2.
        rewrite -> z_neg_extract_from_mult_l in H2.
        rewrite -> z_neg_reduce_double in H2.
        rewrite -> z_mult_reduce_pos_pos in H2.
        rewrite -> z_neg_extract_from_mult_r in H2.
        rewrite -> z_mult_reduce_pos_pos in H2.
        symmetry in H2.
        apply z_pos_ne_neg in H2.
        contradiction H2.
      }
    }
    {
      destruct Hna_ as [p6 [Hp6 _]].
      rewrite -> Hp6 in H3.
      symmetry in H3.
      rewrite -> z_mult_comm in H3.
      rewrite -> z_neg_extract_from_mult_l in H3.
      rewrite -> z_mult_reduce_pos_pos in H3.
      apply z_mult_rhs_neg_part_neg in H3 as [p7 [Hp7 _]].
      rewrite -> Hp6 in H2.
      rewrite -> Hp7 in H2.
      destruct (z_trichotomy_3 c) as [Hzc | [Hpc | Hnc]].
      {
        apply Hnzc.
        exact Hzc.
      }
      {
        destruct Hpc as [p8 [Hp8 _]].
        rewrite -> Hp8 in H2.
        rewrite -> z_neg_extract_from_mult_l in H2.
        rewrite -> z_mult_reduce_pos_pos in H2.
        rewrite -> z_neg_extract_from_mult_r in H2.
        rewrite -> z_neg_reduce_double in H2.
        symmetry in H2.
        apply z_mult_rhs_neg_part_neg in H2 as [p9 [Hp9 _]].
        rewrite -> Hp8 in H1.
        rewrite -> Hp9 in H1.
        rewrite -> z_neg_extract_from_mult_l in H1.
        do 2 rewrite -> z_mult_reduce_pos_pos in H1.
        symmetry in H1.
        apply z_pos_ne_neg in H1.
        contradiction H1.
      }
      {
        destruct Hnc as [p8 [Hp8 _]].
        rewrite -> Hp8 in H1, H2.
        rewrite -> z_neg_extract_from_mult_r in H1, H2.
        rewrite -> z_mult_reduce_pos_pos in H1.
        apply z_mult_rhs_neg_part_neg in H1 as [p9 [Hp9 _]].
        rewrite -> Hp9 in H2.
        do 2 rewrite -> z_neg_extract_from_mult_l in H2.
        do 2 rewrite -> z_neg_reduce_double in H2.
        rewrite -> z_neg_extract_from_mult_r in H2.
        do 2 rewrite -> z_mult_reduce_pos_pos in H2.
        apply z_pos_ne_neg in H2.
        contradiction H2.
      }
    }
  }
Qed.

Proposition q_trichotomy_2 : forall a : Q, 
  (q_is_neg a) ->
  ((a ~= (NQ#0)) -> False) /\
  ((q_is_pos a) -> False).
Proof.
  intros a H0.
  split.
  {
    intros H1.
    apply q_trichotomy_0 in H1 as [H1l H1r].
    apply H1r.
    exact H0.
  }
  {
    intros H1.
    apply q_trichotomy_1 in H1 as [H1l H1r].
    apply H1r.
    exact H0.
  }
Qed.

Proposition q_trichotomy_3 : forall a : Q, 
  (a ~= (NQ#0)) \/
  (q_is_pos a) \/
  (q_is_neg a).
Proof.
  intros [a [b Hnzb]].
  destruct (z_trichotomy_3 a) as [Hza | [Hpa | Hna]].
  {
    left.
    unfold q_eq.
    simpl.
    rewrite -> z_mult_ident_r.
    rewrite -> z_mult_0_l.
    rewrite -> Hza.
    reflexivity.
  }
  {
    destruct Hpa as [p0 [Hp0 _]].
    destruct (z_trichotomy_3 b) as [Hzb | [Hpb | Hnb]].
    {
      exfalso.
      apply Hnzb.
      exact Hzb.
    }
    {
      destruct Hpb as [p1 [Hp1 _]].
      right; left.
      unfold q_is_pos.
      assert (Hnzl : ((NZ# S(p1)) ~= (NZ#0))%Z -> False).
      {
        easy.
      }
      exists (p0). exists (p1). exists (Hnzl).
      unfold q_eq.
      simpl.
      rewrite -> Hp0.
      rewrite -> Hp1.
      reflexivity.
    }
    {
      destruct Hnb as [p1 [Hp1 _]].
      right; right.
      assert (H2 : ((NZ#S(p1)) ~= (NZ#0))%Z -> False ).
      {
        discriminate.
      }
      unfold q_is_neg.
      assert (H3 : (q_is_pos (((NQ#(S(p0))) / (Q_nz_ex (NQ#(S(p1))) H2))%Q)) ).
      {
        unfold q_is_pos.
        exists (p0). exists (p1). exists (H2).
        rewrite <- q_formal_div_as_div.
        reflexivity.
      }
      exists ((NQ#(S(p0))) / (Q_nz_ex (NQ#(S(p1))) H2))%Q.
      exists (H3).
      rewrite <- q_formal_div_as_div.
      unfold q_eq.
      simpl.
      rewrite -> Hp0.
      rewrite -> Hp1.
      rewrite -> z_mult_reduce_pos_pos.
      rewrite -> z_neg_extract_from_mult_l.
      rewrite -> z_neg_extract_from_mult_r.
      rewrite -> z_neg_reduce_double.
      rewrite -> z_mult_reduce_pos_pos.
      reflexivity.
    }
  }
  {
    destruct Hna as [p0 [Hp0 _]].
    destruct (z_trichotomy_3 b) as [Hzb | [Hpb | Hnb]].
    {
      exfalso.
      apply Hnzb.
      exact Hzb.
    }
    {
      destruct Hpb as [p1 [Hp1 _]].
      right; right.
      assert (H2 : ((NZ#S(p1)) ~= (NZ#0))%Z -> False ).
      {
        discriminate.
      }
      unfold q_is_neg.
      assert (H3 : (q_is_pos (((NQ#(S(p0))) / (Q_nz_ex (NQ#(S(p1))) H2))%Q)) ).
      {
        unfold q_is_pos.
        exists (p0). exists (p1). exists (H2).
        rewrite <- q_formal_div_as_div.
        reflexivity.
      }
      exists ((NQ#(S(p0))) / (Q_nz_ex (NQ#(S(p1))) H2))%Q.
      exists (H3).
      rewrite <- q_formal_div_as_div.
      unfold q_eq.
      simpl.
      rewrite -> Hp0.
      rewrite -> Hp1.
      rewrite -> z_neg_extract_from_mult_l.
      rewrite -> z_mult_reduce_pos_pos.
      rewrite <- z_neg_both_sides.
      reflexivity.
    }
    {
      destruct Hnb as [p1 [Hp1 _]].
      right; left.
      unfold q_is_pos.
      assert (Hnzl : ((NZ# S(p1)) ~= (NZ#0))%Z -> False).
      {
        easy.
      }
      exists (p0). exists (p1). exists (Hnzl).
      unfold q_eq.
      simpl.
      rewrite -> Hp0.
      rewrite -> Hp1.
      rewrite -> z_neg_extract_from_mult_l.
      rewrite -> z_neg_extract_from_mult_r.
      rewrite <- z_neg_both_sides.
      rewrite -> z_mult_reduce_pos_pos.
      reflexivity.
    }
  }
Qed.

(*\begin{Q extra prev}*)

Proposition q_mov_neg_r_to_rhs : forall a b c : Q, (a - b ~= c) <-> (a ~= c + b).
Proof.
  intros a b c.
  split.
  {
    intros H0.
    unfold q_sub in H0.
    rewrite <- H0.
    rewrite -> q_add_assoc.
    rewrite -> q_additive_inverse_l.
    rewrite -> q_add_0_r.
    reflexivity.
  }
  {
    intros H0.
    unfold q_sub.
    rewrite -> H0.
    rewrite -> q_add_assoc.
    rewrite -> q_additive_inverse_r.
    rewrite -> q_add_0_r.
    reflexivity.
  }
Qed.

Proposition q_mov_rhs_to_lhs : forall a b : Q, (a ~= b)%Q <-> (a - b ~= (NQ#0))%Q.
Proof.
  intros a b.
  split.
  {
    intros H0.
    unfold q_sub.
    rewrite -> H0.
    rewrite -> q_additive_inverse_r.
    reflexivity.
  }
  {
    intros H0.
    rewrite -> q_mov_neg_r_to_rhs in H0.
    rewrite -> q_add_0_l in H0.
    exact H0.
  }
Qed.

Proposition q_sub_refold : forall a b : Q, a + (-- b) = a - b.
Proof.
  intros a b.
  unfold q_sub.
  reflexivity.
Qed.

Proposition q_neg_both_sides : forall a b : Q, (a ~= b) <-> ((-- a) ~= (-- b)).
Proof.
  intros [a [b Hnzb]] [c [d Hnzd]].
  split.
  {
    intros H0.
    rewrite -> H0.
    reflexivity.
  }
  {
    intros H0.
    unfold q_neg in H0.
    unfold q_eq in *.
    simpl in *.
    do 2 rewrite -> z_neg_extract_from_mult_l in H0.
    rewrite <- z_neg_both_sides in H0.
    exact H0.
  }
Qed.

Proposition q_neg_dist_over_add : forall a b : Q, (-- (a + b)) ~= ((-- a) + (-- b)).
Proof.
  intros [a [b Hnzb]] [c [d Hnzd]].
  unfold q_neg.
  unfold q_add.
  unfold q_eq.
  simpl.
  do 2 rewrite -> z_neg_extract_from_mult_l.
  do 1 rewrite -> z_neg_extract_from_mult_r.
  rewrite <- z_neg_dist_over_add.
  repeat rewrite <- z_mult_assoc.
  do 2 rewrite -> z_neg_extract_from_mult_l.
  reflexivity.
Qed.

Proposition q_neg_reduce_double : forall a : Q, (-- (-- a)) ~= a.
Proof.
  intros [a [b Hnzb]].
  unfold q_neg.
  unfold q_eq.
  simpl.
  rewrite -> z_neg_reduce_double.
  reflexivity.
Qed.

Proposition q_neg_reduce_neg_z : (-- (NQ# 0)) = (NQ# 0).
Proof.
  easy.
Qed.

Proposition q_neg_sub_is_rev : forall a b : Q, (-- (a - b)) ~= (b - a).
Proof.
  intros a b.
  unfold q_sub.
  rewrite -> q_neg_dist_over_add.
  rewrite -> q_neg_reduce_double.
  rewrite -> q_add_comm.
  reflexivity.
Qed.

Proposition q_pos_ne_neg : forall 
  (a b c d : nat) (Hnzb : ((NZ#S(b)) ~= (NZ#0))%Z -> False) 
  (Hnzd : ((NZ#S(d)) ~= (NZ#0))%Z -> False), (
    {| num := (NZ#S(a)); den := (Z_nz_ex (NZ#S(b)) Hnzb) |} ~=
    (-- {| num := (NZ#S(c)); den := (Z_nz_ex (NZ#S(d)) Hnzd) |})
  )%Q -> False.
Proof.
  intros a b c d Hnzb Hnzd H0.
  unfold q_neg in *.
  unfold q_eq in *.
  simpl in *.
  rewrite -> z_neg_extract_from_mult_l in H0.
  do 2 rewrite -> z_mult_reduce_pos_pos in H0.
  apply z_pos_ne_neg in H0.
  contradiction H0.
Qed.

Proposition q_sub_rev_is_not_pos : forall a b : Q, 
  (q_is_pos (a - b)) -> ((q_is_pos (b - a)) -> False).
Proof.
  intros a b H0 H1.
  unfold q_is_pos in *.
  destruct H0 as [p1 [p2 [H2 H3]]].
  destruct H1 as [p3 [p4 [H4 H5]]].
  rewrite -> q_neg_both_sides in H3.
  rewrite -> q_neg_sub_is_rev in H3.
  rewrite -> H3 in H5.
  symmetry in H5.
  apply q_pos_ne_neg in H5.
  contradiction H5.
Qed.

Proposition q_neg_diff_is_pos_rev : forall a b : Q,
  (q_is_neg (a - b)) <-> (q_is_pos (b - a)).
Proof.
  intros a b.
  split.
  {
    intros [p1 [[p2 [p3 [H0 H1]]] H2]].
    unfold q_is_pos.
    rewrite <- q_neg_sub_is_rev in H2.
    rewrite <- q_neg_both_sides in H2.
    exists (p2). exists (p3). exists (H0).
    rewrite -> H2.
    exact H1.
  }
  {
    intros [p0 [p1 [H0 H1]]].
    unfold q_is_neg.
    rewrite <- q_neg_sub_is_rev in H1.
    rewrite -> q_neg_both_sides in H1.
    rewrite -> q_neg_reduce_double in H1.
    assert (H2 : (q_is_pos ((NQ#S(p0)) / (Q_nz_ex (NQ#S(p1)) H0) )) ).
    {
      unfold q_is_pos.
      exists (p0). exists (p1). exists (H0).
      rewrite -> q_formal_div_as_div.
      reflexivity.
    }
    exists ((NQ#S(p0)) / (Q_nz_ex (NQ#S(p1)) H0) ).
    exists (H2).
    rewrite -> H1.
    rewrite -> q_formal_div_as_div.
    reflexivity.
  }
Qed.

Proposition q_add_from_two_equations : forall a b c d : Q, 
  (a ~= b) -> (c ~= d) -> (a + c ~= b + d).
Proof.
  intros a b c d H0 H1.
  rewrite -> H0.
  rewrite -> H1.
  reflexivity.
Qed.

Proposition q_cross_add_from_two_equations : forall a b c d : Q, 
  (a ~= b) -> (c ~= d) -> (a + d ~= b + c).
Proof.
  intros a b c d H0 H1.
  rewrite -> H0.
  rewrite -> H1.
  reflexivity.
Qed.

Proposition q_mult_from_two_equations : forall a b c d : Q, 
  (a ~= b) -> (c ~= d) -> (a * c ~= b * d).
Proof.
  intros a b c d H0 H1.
  rewrite -> H0.
  rewrite -> H1.
  reflexivity.
Qed.

Proposition q_cross_mult_from_two_equations : forall a b c d : Q, 
  (a ~= b) -> (c ~= d) -> (a * d ~= b * c).
Proof.
  intros a b c d H0 H1.
  rewrite -> H0.
  rewrite -> H1.
  reflexivity.
Qed.

Proposition q_nq_div_reduce_add : forall (a b c d : nat)
  (Hnzb : ((NZ#(S b)) ~= (NZ#0))%Z -> False) (Hnzd : ((NZ#(S d)) ~= (NZ#0))%Z -> False)
  (Hnzbd : ((NZ#(S b) * (S d)) ~= (NZ#0))%Z -> False),
  (((NQ# a) / (Q_nz_ex (NQ#S b) Hnzb))) + ((NQ# c) / (Q_nz_ex (NQ#(S d)) Hnzd))
  ~= ((NQ# a * S d + S b * c) / (Q_nz_ex (NQ# S b * S d) Hnzbd)).
Proof.
  intros a b c d Hnzb Hnzd Hnzbd.
  do 3 rewrite <- q_formal_div_as_div.
  unfold q_add.
  unfold q_eq.
  simpl.
  rewrite -> z_mult_reduce_pos_pos.
  unfold z_mult.
  unfold z_add.
  unfold z_eq.
  simpl.
  repeat rewrite -> mult_0_r.
  repeat rewrite -> def_mult_clause_0.
  repeat rewrite -> def_add_clause_0.
  repeat rewrite -> add_0_r.
  reflexivity.
Qed.

Proposition q_nq_div_reduce_add_succ : forall (a b c d : nat)
  (Hnzb : ((NZ#(S b)) ~= (NZ#0))%Z -> False) (Hnzd : ((NZ#(S d)) ~= (NZ#0))%Z -> False)
  (Hnzbd : ((NZ#S(d + b * S d)) ~= (NZ#0))%Z -> False),
  (((NQ# a) / (Q_nz_ex (NQ#S b) Hnzb))) + ((NQ# c) / (Q_nz_ex (NQ#(S d)) Hnzd))
  ~= ((NQ# a * S d + S b * c) / (Q_nz_ex (NQ# S(d + b * S d)) Hnzbd)).
Proof.
  intros a b c d Hnzb Hnzd Hnzbd.
  do 3 rewrite <- q_formal_div_as_div.
  unfold q_add.
  unfold q_eq.
  simpl.
  rewrite -> z_mult_reduce_pos_pos.
  unfold z_mult.
  unfold z_add.
  unfold z_eq.
  simpl.
  repeat rewrite -> mult_0_r.
  repeat rewrite -> def_mult_clause_0.
  repeat rewrite -> def_add_clause_0.
  repeat rewrite -> add_0_r.
  reflexivity.
Qed.

Proposition q_nq_div_reduce_sub : forall (a b c d : nat)
  (Hnzb : ((NZ#b) ~= (NZ#0))%Z -> False) (Hnzd : ((NZ#d) ~= (NZ#0))%Z -> False)
  (Hnzbd : ((NZ#b*d) ~= (NZ#0))%Z -> False),
  (((NQ# a) / (Q_nz_ex (NQ#b) Hnzb))) - ((NQ# c) / (Q_nz_ex (NQ#d) Hnzd))
  ~= (((NQ# a * d) - (NQ# b * c)) / (Q_nz_ex (NQ# b*d) Hnzbd)).
Proof.
  intros a b c d Hnzb Hnzd Hnzbd.
  unfold q_sub.
  do 2 rewrite <- q_formal_div_as_div.
  unfold q_add.
  unfold q_eq.
  simpl.
  do 2 rewrite -> z_mult_ident_l.
  do 2 rewrite -> z_mult_ident_r.
  rewrite -> z_neg_extract_from_mult_r.
  destruct b as [| b'].
  {
    exfalso.
    apply Hnzb.
    reflexivity.
  }
  {
    destruct d as [| d'].
    {
      exfalso.
      apply Hnzd.
      reflexivity.
    }
    {
      rewrite -> z_mult_reduce_pos_pos.
      destruct a as [| a'].
      {
        rewrite -> z_mult_0_l.
        rewrite -> def_mult_clause_0.
        do 2 rewrite -> z_add_0_l.
        destruct c as [| c'].
        {
          rewrite -> z_mult_0_r.
          rewrite -> mult_0_r.
          reflexivity.
        }
        {
          rewrite -> z_mult_reduce_pos_pos.
          reflexivity.
        }
      }
      {
        rewrite -> z_mult_reduce_pos_pos.
        destruct c as [| c'].
        {
          rewrite -> z_mult_0_r.
          rewrite -> mult_0_r.
          rewrite -> z_neg_reduce_neg_0.
          rewrite -> z_add_0_r.
          reflexivity.
        }
        {
          rewrite -> z_mult_reduce_pos_pos.
          reflexivity.
        }
      }
    }
  }
Qed.

Proposition q_div_reduce_sub_formal : forall (a b c d : Z)
  (Hnzb : (b ~= (NZ#0))%Z -> False) (Hnzd : (d ~= (NZ#0))%Z -> False)
  (Hnzbd : (b*d ~= (NZ#0))%Z -> False),
  {| num := a; den := (Z_nz_ex b Hnzb) |} - {| num := c; den := (Z_nz_ex d Hnzd) |}
  ~= {| num := a * d - b * c; den := (Z_nz_ex (b*d)%Z Hnzbd) |}.
Proof.
  intros a b c d Hnzb Hnzd Hnzbd.
  unfold q_neg.
  unfold q_add.
  unfold q_eq.
  simpl.
  rewrite -> z_neg_extract_from_mult_r.
  rewrite -> z_sub_refold.
  reflexivity.
Qed.

Proposition q_div_reduce_sub_formal_same_den : forall (a b c : Z)
  (Hnzb : (b ~= (NZ#0))%Z -> False),
  {| num := a; den := (Z_nz_ex b Hnzb) |} - {| num := c; den := (Z_nz_ex b Hnzb) |}
  ~= {| num := a - c; den := (Z_nz_ex b Hnzb) |}.
Proof.
  intros a b c Hnzb.
  unfold q_sub.
  unfold q_add.
  unfold q_eq.
  simpl.
  rewrite -> (z_mult_comm b (-- c)).
  rewrite <- z_mult_dist_over_add_r.
  rewrite -> z_sub_refold.
  rewrite -> z_mult_assoc.
  reflexivity.
Qed.

Proposition q_div_reduce_sub_formal_partial_shared_den_r : forall (a b c d e : Z)
  (Hnzbe : ((b*e) ~= (NZ#0))%Z -> False) 
  (Hnzde : ((d*e) ~= (NZ#0))%Z -> False) 
  (Hnzbde : ((b*d*e) ~= (NZ#0))%Z -> False),
  {| num := a; den := (Z_nz_ex (b*e)%Z Hnzbe) |} 
  - {| num := c; den := (Z_nz_ex (d*e)%Z Hnzde) |}
  ~= {| num := a * d - b * c; den := (Z_nz_ex (b*d*e)%Z Hnzbde) |}.
Proof.
  intros a b c d e Hnzbe Hnzde Hnzbde.
  unfold q_sub.
  unfold q_add.
  unfold q_eq.
  simpl.
  unfold z_sub.
  rewrite -> z_neg_extract_from_mult_r.
  do 2 rewrite -> z_mult_dist_over_add_r.
  do 2 rewrite -> z_neg_extract_from_mult_l.
  repeat rewrite <- z_mult_assoc.
  (* v Goal : a * d * e * b * d * e + [...] *)
  do 1 rewrite -> z_mult_assoc.
  rewrite -> (z_mult_comm_abdc a d e b).
  do 1 rewrite <- z_mult_assoc.
  (* ^ Goal : a * d * b * e * d * e + [...] *)
  rewrite -> z_add_cancel_l.
  rewrite <- z_neg_both_sides.
  (* v Goal : b * e * c * b * d * e ~= [...] *)
  do 1 rewrite -> z_mult_assoc.
  rewrite -> (z_mult_comm_acdb b e c b).
  do 1 rewrite <- z_mult_assoc.
  (* ^ Goal : b * c * b * e * d * e ~= [...] *)
  reflexivity.
Qed.

Proposition q_zq_div_reduce_sub : forall (a b c d : Z)
  (Hnzb : (b ~= (NZ#0))%Z -> False) (Hnzd : (d ~= (NZ#0))%Z -> False)
  (Hnzbd : (b*d ~= (NZ#0))%Z -> False),
  (((ZQ# a) / (Q_nz_ex (ZQ#b) Hnzb))) - ((ZQ# c) / (Q_nz_ex (ZQ#d) Hnzd))
  ~= ((ZQ# a * d - b * c) / (Q_nz_ex (ZQ# b*d) Hnzbd)).
Proof.
  intros a b c d Hnzb Hnzd Hnzbd.
  rewrite <- (q_formal_div_as_div (a * d - b * c)).
  unfold q_sub.
  rewrite <- (q_formal_div_as_div a).
  rewrite <- (q_formal_div_as_div c).
  apply q_div_reduce_sub_formal.
Qed.

Proposition q_nq_div_reduce_sub_succ_2 : forall (a b c d : nat)
  (Hnzb : ((NZ#(S b)) ~= (NZ#0))%Z -> False) (Hnzd : ((NZ#(S d)) ~= (NZ#0))%Z -> False)
  (Hnzbd : ((NZ#S(d + b * S d)) ~= (NZ#0))%Z -> False),
  (((NQ# a) / (Q_nz_ex (NQ#S b) Hnzb))) - ((NQ# c) / (Q_nz_ex (NQ#(S d)) Hnzd))
  ~= (((NQ# a * S d) - (NQ# S b * c)) / (Q_nz_ex (NQ# S(d + b * S d)) Hnzbd)).
Proof.
  intros a b c d Hnzb Hnzd Hnzbd.
  unfold q_sub.
  do 2 rewrite <- q_formal_div_as_div.
  unfold q_add.
  unfold q_eq.
  simpl.
  do 1 rewrite -> z_mult_reduce_pos_pos.
  unfold z_neg.
  unfold z_mult.
  unfold z_add.
  unfold z_eq.
  simpl.
  do 9 rewrite -> mult_0_r.
  do 6 rewrite -> def_add_clause_0.
  do 11 rewrite -> add_0_r.
  do 3 rewrite -> mult_ident_r.
  reflexivity.
Qed.

Proposition q_add_assoc_middle : forall a b c d : Q, a + (b + (c + d)) ~= a + (b + c) + d.
Proof.
  intros [a [b Hnzb]] [c [d Hnzd]] [e [f Hnzf]] [g [h Hnzh]].
  unfold q_add.
  unfold q_eq.
  simpl.
  repeat rewrite <- z_mult_assoc.
  repeat rewrite -> z_mult_dist_over_add_l.
  repeat rewrite -> z_mult_dist_over_add_r.
  repeat rewrite <- z_mult_assoc.
  repeat rewrite <- z_add_assoc.
  reflexivity.
Qed.

Proposition q_mult_cancel_r : 
  forall (a b c: Q) (Hnzc : ((num c) ~= (NZ#0))%Z -> False), 
  ((a*c) ~= b*c) <-> (a ~= b).
Proof.
  intros [a [b Hnzb]] [c [d Hnzd]] [e [f Hnzf]] Hnz0.
  split.
  {
    intros H0.
    unfold q_mult in *.
    unfold q_eq in *.
    simpl in *.
    do 2 rewrite <- z_mult_assoc in H0.
    apply z_mult_cancel_r in H0.
    2: exact Hnzf.
    rewrite -> (z_mult_comm a e) in H0.
    rewrite -> (z_mult_comm c e) in H0.
    do 2 rewrite -> z_mult_assoc in H0.
    apply z_mult_cancel_l in H0.
    2: exact Hnz0.
    exact H0.
  }
  {
    intros H0.
    unfold q_mult in *.
    unfold q_eq in *.
    simpl in *.
    do 2 rewrite <- z_mult_assoc.
    apply z_mult_cancel_r_2.
    1: exact Hnzf.
    rewrite -> (z_mult_comm a e).
    rewrite -> (z_mult_comm c e).
    do 2 rewrite -> z_mult_assoc.
    apply z_mult_cancel_l_2.
    1: exact Hnz0.
    exact H0.
  }
Qed.

Proposition q_mult_cancel_l : 
  forall (a b c: Q) (Hnzc : ((num c) ~= (NZ#0))%Z -> False), 
  ((c*a) ~= c*b) <-> (a ~= b).
Proof.
  intros a b c Hnzc.
  rewrite -> (q_mult_comm c a).
  rewrite -> (q_mult_comm c b).
  apply q_mult_cancel_r.
  exact Hnzc.
Qed.

Proposition q_eqn_num1_ne_z : forall (a b c d : Z)
  (Hnzb : (b ~= (NZ#0))%Z -> False)
  (Hnzc : (c ~= (NZ#0))%Z -> False)
  (Hnzd : (d ~= (NZ#0))%Z -> False),
  ({| num := a; den := (Z_nz_ex b Hnzb) |} ~= {| num := c; den := (Z_nz_ex d Hnzd) |})
  -> ((a ~= (NZ#0))%Z -> False).
Proof.
  intros a b c d Hnzb Hnzc Hnzd H0 H1.
  unfold q_eq in H0.
  simpl in H0.
  rewrite -> H1 in H0.
  rewrite -> z_mult_0_l in H0.
  symmetry in H0.
  apply z_mult_no_zero_div in H0 as [H0l | H0r].
  {
    apply Hnzc.
    exact H0l.
  }
  {
    apply Hnzb.
    exact H0r.
  }
Qed.

Proposition q_z_mult_reduce : forall (a b c d : Z)
  (Hnzb : (b ~= (NZ#0))%Z -> False)
  (Hnzd : (d ~= (NZ#0))%Z -> False)
  (Hnzbd : (b*d ~= (NZ#0))%Z -> False),
  {| num := a; den := (Z_nz_ex b Hnzb) |} * {| num := c; den := (Z_nz_ex d Hnzd) |}
  ~= {| num := (a*c)%Z; den := (Z_nz_ex (b*d)%Z Hnzbd) |}.
Proof.
  intros a b c d Hnzb Hnzd Hnzbd.
  unfold q_mult.
  unfold q_eq.
  simpl.
  rewrite -> z_mult_assoc.
  destruct (z_trichotomy_3 a) as [Hza | [Hpa | Hna]].
  {
    rewrite -> Hza.
    rewrite -> z_mult_0_l.
    reflexivity.
  }
  {
    destruct Hpa as [p0 [Hp0 _]].
    rewrite -> Hp0.
    rewrite -> z_mult_cancel_l_2.
    2: discriminate.
    rewrite <- z_mult_assoc.
    rewrite -> z_mult_cancel_r_2.
    2: exact Hnzd.
    reflexivity.
  }
  {
    destruct Hna as [p0 [Hp0 _]].
    rewrite -> Hp0.
    rewrite -> z_neg_extract_from_mult_l.
    rewrite <- z_neg_both_sides.
    rewrite -> z_mult_cancel_l_2.
    2: discriminate.
    reflexivity.
  }
Qed.

(* Still won't help us rewrite in num/den when over q_eq *)
Require Import Stdlib.Classes.Morphisms.
Instance zq_proper_over_z_eq : 
  Proper (z_eq ==> q_eq ) ZQ.
Proof.
  intros a a' Ha.
  unfold q_eq.
  simpl.
  do 2 rewrite -> z_mult_ident_r.
  exact Ha.
Qed.

Proposition q_num_rewrite : forall (a a' b : Z)
  (Hnzb : (b ~= (NZ#0))%Z -> False)
  (Heq : (a ~= a')%Z),
  {| num := a; den := (Z_nz_ex b Hnzb) |} ~= {| num := a'; den := (Z_nz_ex b Hnzb) |}.
Proof.
  intros a a' b Hnzb Heq.
  unfold q_eq.
  simpl.
  rewrite -> Heq.
  reflexivity.
Qed.

Proposition q_den_rewrite : forall (a b b' : Z)
  (Hnzb : (b ~= (NZ#0))%Z -> False)
  (Hnzb' : (b' ~= (NZ#0))%Z -> False)
  (Heq : (b ~= b')%Z),
  {| num := a; den := (Z_nz_ex b Hnzb) |} ~= {| num := a; den := (Z_nz_ex b' Hnzb') |}.
Proof.
  intros a b b' Hnzb Hnzb' Heq.
  unfold q_eq.
  simpl.
  rewrite -> Heq.
  reflexivity.
Qed.

Proposition q_is_pos_rewrite : forall (a a' : Q) (Heq : a ~= a'),
  (q_is_pos a) <-> (q_is_pos a').
Proof.
  intros a a' Heq.
  split.
  {
    intros H0.
    apply q_is_pos_as_pos_no_succ in H0.
    apply q_is_pos_as_pos_no_succ.
    unfold q_is_pos_no_succ in *.
    destruct H0 as [p0 [p1 [Hnzp0 [Hnzp1 H0]]]].
    exists (p0).
    exists (p1).
    exists (Hnzp0).
    exists (Hnzp1).
    rewrite <- H0.
    symmetry.
    exact Heq.
  }
  {
    intros H0.
    apply q_is_pos_as_pos_no_succ in H0.
    apply q_is_pos_as_pos_no_succ.
    unfold q_is_pos_no_succ in *.
    destruct H0 as [p0 [p1 [Hnzp0 [Hnzp1 H0]]]].
    exists (p0).
    exists (p1).
    exists (Hnzp0).
    exists (Hnzp1).
    rewrite <- H0.
    exact Heq.
  }
Qed.

Proposition q_is_neg_rewrite : forall (a a' : Q) (Heq : a ~= a'),
  (q_is_neg a) <-> (q_is_neg a').
Proof.
  intros a a'.
  split.
  {
    intros H0.
    unfold q_is_neg in *.
    destruct H0 as [q0 [Hpq0 H0]].
    exists (q0).
    exists (Hpq0).
    rewrite <- Heq.
    exact H0.
  }
  {
    intros H0.
    unfold q_is_neg in *.
    destruct H0 as [q0 [Hpq0 H0]].
    exists (q0).
    exists (Hpq0).
    rewrite -> Heq.
    exact H0.
  }
Qed.

Proposition q_neg_extract_from_mult_l : forall a b : Q, (-- a) * b ~= (-- (a * b)).
Proof.
  intros [a [b Hnzb]] [c [d Hnzd]].
  unfold q_neg.
  unfold q_mult.
  unfold q_eq.
  simpl.
  rewrite -> z_neg_extract_from_mult_l.
  reflexivity.
Qed.

Proposition q_neg_extract_from_mult_r : forall a b : Q, a * (-- b) ~= (-- (a * b)).
Proof.
  intros [a [b Hnzb]] [c [d Hnzd]].
  unfold q_neg.
  unfold q_mult.
  unfold q_eq.
  simpl.
  rewrite -> z_neg_extract_from_mult_r.
  reflexivity.
Qed.

Proposition q_neg_mult_swap_neg : forall (a b : Q), 
  (-- a) * b ~= a * (-- b).
Proof.
  intros a b.
  rewrite -> q_neg_extract_from_mult_l.
  rewrite -> q_neg_extract_from_mult_r.
  reflexivity.
Qed.

(*\end{Q extra prev}*)

(*\begin{Q is an ordered field}*)

Definition q_gt (a b : Q) : Prop :=
  (q_is_pos (a - b))%Q.

Notation "x > y" := (q_gt x y) (at level 70) : Q_scope.

Definition q_ge (a b : Q) : Prop :=
  (a > b) \/ (a ~= b).

Notation "x >= y" := (q_ge x y) (at level 70) : Q_scope.

Proposition q_ord_trichotomy_0 : forall a b : Q, 
  (a ~= b) -> (((a > b) -> False) /\ ((b > a) -> False)).
Proof.
  intros a b H0.
  split.
  {
    intros H1.
    unfold q_gt in H1.
    rewrite -> q_mov_rhs_to_lhs in H0.
    apply (q_trichotomy_0) in H0 as [H0l H0r].
    apply H0l.
    exact H1.
  }
  {
    intros H1.
    unfold q_gt in H1.
    rewrite -> q_mov_rhs_to_lhs in H0.
    unfold q_sub in H0.
    rewrite -> q_add_comm in H0.
    rewrite -> q_neg_both_sides in H0.
    rewrite -> q_neg_dist_over_add in H0.
    rewrite -> q_neg_reduce_double in H0.
    rewrite -> q_neg_reduce_neg_z in H0.
    rewrite -> q_sub_refold in H0.
    apply (q_trichotomy_0) in H0 as [H0l H0r].
    apply H0l.
    exact H1.
  }
Qed.

Proposition q_ord_trichotomy_1 : forall a b : Q,
  (a > b) -> (((a ~= b) -> False) /\ ((b > a) -> False)).
Proof.
  intros a b H0.
  split.
  {
    intros H1.
    unfold q_gt in H0.
    rewrite -> q_mov_rhs_to_lhs in H1.
    apply (q_trichotomy_0) in H1 as [H1l H1r].
    apply H1l.
    exact H0.
  }
  {
    intros H1.
    unfold q_gt in *.
    apply (q_sub_rev_is_not_pos) in H0.
    contradiction H0.
    exact H1.
  }
Qed.

Proposition q_ord_trichotomy_2 : forall a b : Q,
  (b > a) -> (((a ~= b) -> False) /\ ((a > b) -> False)).
Proof.
  intros a b H0.
  split.
  {
    intros H1.
    apply q_ord_trichotomy_1 in H0 as [H0l H0r].
    apply H0l.
    rewrite -> H1.
    reflexivity.
  }
  {
    intros H1.
    unfold q_gt in *.
    apply (q_sub_rev_is_not_pos) in H0.
    contradiction H0.
    exact H1.
  }
Qed.

Proposition q_ord_trichotomy_3 : forall a b : Q,
  (a ~= b) \/ (a > b) \/ (b > a).
Proof.
  intros a b.
  destruct (q_trichotomy_3 (a - b)) as [Hzd | [Hpd | Hnd]].
  {
    rewrite -> q_mov_neg_r_to_rhs in Hzd.
    rewrite -> q_add_0_l in Hzd.
    left.
    exact Hzd.
  }
  {
    right; left.
    unfold q_gt.
    exact Hpd.
  }
  {
    apply q_neg_diff_is_pos_rev in Hnd.
    right; right.
    unfold q_gt.
    exact Hnd.
  }
Qed.

Proposition q_ord_antisymmetric : forall a b : Q, (a > b) -> (b > a) -> False.
Proof.
  intros a b H0 H1.
  unfold q_gt in *.
  apply q_sub_rev_is_not_pos in H0.
  {
    contradiction H0.
  }
  {
    exact H1.
  }
Qed.

Proposition q_ord_trans : forall a b c : Q, (a > b) -> (b > c) -> (a > c).
Proof.
  intros a b c H0 H1.
  unfold q_gt in *.
  destruct H0 as [p0 [p1 [H2 H3]]].
  destruct H1 as [p2 [p3 [H4 H5]]].
  rewrite -> q_formal_div_as_div in *.
  assert (H6 : ((a - b) + (b - c) ~= 
    ((NQ# S p0) / (Q_nz_ex (NQ# S p1) H2)) + 
    ((NQ# S p2 ) / (Q_nz_ex (NQ# S p3) H4)))).
  {
    apply (q_add_from_two_equations).
    1: exact H3. 1: exact H5.
  }
  rewrite <- q_neg_sub_is_rev in H6.
  unfold q_sub in H6.
  rewrite -> q_neg_dist_over_add in H6.
  rewrite -> q_neg_reduce_double in H6.
  repeat rewrite <- q_add_assoc in H6.
  rewrite -> (q_add_comm (-- b + a) (b)) in H6.
  repeat rewrite <- q_add_assoc in H6.
  rewrite -> q_additive_inverse_r in H6.
  rewrite -> q_add_0_l in H6.
  rewrite -> q_sub_refold in H6.
  assert (H8 : ((NZ# S p1 * S p3) ~= (NZ#0))%Z -> False).
  {
    apply (z_mult_preserves_ne_z_succ).
  }
  rewrite -> (q_nq_div_reduce_add_succ _ _ _ _ _ _ H8) in H6.
  rewrite -> def_mult_clause_1 in H6.
  do 2 rewrite -> def_add_clause_1 in H6.
  unfold q_is_pos.
  exists (p3 + p0 * S p3 + S p1 * S p2)%nat.
  exists (p3 + p1 * S p3)%nat.
  exists (H8).
  rewrite -> q_formal_div_as_div.
  exact H6.
Qed.

Proposition q_add_preserves_ord : forall a b c : Q, (a > b) <-> (a + c > b + c).
Proof.
  intros a b c.
  split.
  {
    unfold q_gt.
    unfold q_is_pos.
    intros [p0 [p1 [H0 H1]]].
    rewrite <- q_add_0_l in H1.
    rewrite <- (q_additive_inverse_l c) in H1.
    unfold q_sub in H1.
    (* v H1 : -- c + c + (a + -- b) ~= [...] *)
    rewrite -> q_add_assoc in H1.
    rewrite -> q_add_comm in H1.
    rewrite <- q_add_assoc in H1.
    rewrite -> (q_add_comm c a) in H1.
    (* ^ H1 : a + c + -- b + -- c ~= [...] *)
    rewrite -> q_add_assoc in H1.
    rewrite <- q_neg_dist_over_add in H1.
    rewrite -> q_sub_refold in H1.
    exists (p0).
    exists (p1).
    exists (H0).
    exact H1.
  }
  {
    unfold q_gt.
    unfold q_is_pos.
    intros [p0 [p1 [H0 H1]]].
    unfold q_sub in H1.
    rewrite -> q_neg_dist_over_add in H1.
    rewrite <- q_add_assoc in H1.
    (* v H1 : a + c + -- b + -- c ~= [...] *)
    rewrite -> q_add_assoc in H1.
    rewrite -> (q_add_comm (--b) (--c)) in H1.
    rewrite <- q_add_assoc in H1.
    rewrite -> (q_add_comm a c) in H1.
    repeat rewrite -> q_add_assoc in H1.
    rewrite -> q_add_assoc_middle in H1.
    rewrite -> (q_add_comm a (--c)) in H1.
    rewrite <- q_add_assoc_middle in H1.
    do 1 rewrite <- q_add_assoc in H1.
    rewrite -> (q_add_comm c (--c)) in H1.
    (* ^ H1 : -- c + c + (a + -- b) ~= [...] *)
    rewrite -> q_additive_inverse_l in H1.
    rewrite -> q_add_0_l in H1.
    rewrite -> q_sub_refold in H1.
    exists (p0).
    exists (p1).
    exists (H0).
    exact H1.
  }
Qed.

Proposition q_pos_mult_preserves_ord : forall a b c : Q, 
  (a > b) -> (q_is_pos c) -> (a*c > b*c).
Proof.
  intros [a [b Hnzb]] [c [d Hnzd]] [e [f Hnzf]] H0 H1.
  unfold q_gt in *.
  apply q_is_pos_as_pos_no_succ.
  apply q_is_pos_as_pos_no_succ in H0, H1.
  unfold q_is_pos_no_succ in *.
  destruct H0 as [p0 [p1 [Hnzp0 [Hnzp1 H03]]]].
  destruct H1 as [p2 [p3 [Hnzp2 [Hnzp3 H13]]]].
  assert (Hnzbd : (b*d ~= (NZ#0))%Z -> False).
  {
    apply z_mult_preserves_ne_z_2.
    split. 1: exact Hnzb. 1: exact Hnzd.
  }
  rewrite (q_div_reduce_sub_formal _ _ _ _ _ _ Hnzbd) in H03.
  apply <- (q_mult_cancel_r 
    {| num := (a * d - b * c)%Z; den := (Z_nz_ex (b * d)%Z Hnzbd) |}
    {| num := (NZ#p0); den := (Z_nz_ex (NZ#p1) Hnzp1) |}
    {| num := (NZ#p2); den := (Z_nz_ex (NZ#p3) Hnzp3) |}
  ) in H03.
  2: exact Hnzp2.
  assert (Hnzbdp3 : (b*d*(NZ#p3) ~= (NZ#0))%Z -> False).
  {
    apply z_mult_preserves_ne_z_2.
    split. 1: exact Hnzbd. 1: exact Hnzp3.
  }
  assert (Hnzp1p3 : ((NZ#p1)*(NZ#p3) ~= (NZ#0))%Z -> False).
  {
    apply z_mult_preserves_ne_z_2.
    split. 1: exact Hnzp1. 1: exact Hnzp3.
  }
  rewrite -> (q_z_mult_reduce _ _ _ _ _ _ Hnzbdp3) in H03.
  rewrite -> (q_z_mult_reduce _ _ _ _ _ _ Hnzp1p3) in H03.
  assert (Hnzp0p2_1 : ((NZ#p0*p2) ~= (NZ#0))%Z -> False).
  {
    apply z_mult_preserves_ne_z_1.
    split. 1: exact Hnzp0. 1: exact Hnzp2.
  }
  assert (Hnzp1p3_1 : ((NZ#p1*p3) ~= (NZ#0))%Z -> False).
  {
    apply z_mult_preserves_ne_z_1.
    split. 1: exact Hnzp1. 1: exact Hnzp3.
  }
  exists (p0 * p2)%nat.
  exists (p1 * p3)%nat.
  exists (Hnzp0p2_1).
  exists (Hnzp1p3_1).
  unfold q_sub.
  rewrite -> H13.
  assert (Hnzbp3 : (b * (NZ#p3) ~= (NZ#0))%Z -> False).
  {
    apply z_mult_preserves_ne_z_2.
    split. 1: exact Hnzb. 1: exact Hnzp3.
  }
  assert (Hnzdp3 : (d * (NZ#p3) ~= (NZ#0))%Z -> False).
  {
    apply z_mult_preserves_ne_z_2.
    split. 1: exact Hnzd. 1: exact Hnzp3.
  }
  rewrite -> (q_z_mult_reduce _ _ _ _ _ _ Hnzdp3).
  rewrite -> (q_z_mult_reduce _ _ _ _ _ _ Hnzbp3).
  rewrite -> q_sub_refold.
  rewrite -> (q_div_reduce_sub_formal_partial_shared_den_r _ _ _ _ _ _ _ Hnzbdp3).
  rewrite -> z_mult_assoc.
  rewrite -> (z_mult_comm (NZ#p2) d).
  do 2 rewrite <- z_mult_assoc.
  assert (Hrw : ((a * d * (NZ#p2)) - (b * c * (NZ#p2)) ~=
                 ((a * d - b * c) * (NZ#p2)))%Z).
  {
    rewrite <- (z_mult_dist_over_sub_r_r).
    reflexivity.
  }
  rewrite -> (q_num_rewrite _ _ _ _ Hrw).
  clear Hrw.
  assert (Hrw : ((NZ# p0 * p2) ~= (NZ#p0) * (NZ#p2)
                )%Z).
  {
    unfold NZ.
    unfold z_eq.
    simpl.
    rewrite -> mult_0_r.
    do 3 rewrite -> add_0_r.
    reflexivity.
  }
  rewrite -> (q_num_rewrite _ _ _ _ Hrw).
  clear Hrw.
  assert (Hrw : ((NZ# p1 * p3) ~= (NZ#p1) * (NZ#p3)
                )%Z).
  {
    unfold NZ.
    unfold z_eq.
    simpl.
    rewrite -> mult_0_r.
    do 3 rewrite -> add_0_r.
    reflexivity.
  }
  rewrite -> (q_den_rewrite _ _ _ Hnzp1p3_1 Hnzp1p3 Hrw).
  exact H03.
Qed.

Proposition q_ord_rev : forall a b : Q,
  (a > b) <-> ((-- b) > (-- a)).
Proof.
  intros [a [b Hnzb]] [c [d Hnzd]].
  split.
  {
    intros H0.
    unfold q_gt in *.
    apply q_is_pos_as_pos_no_succ in H0.
    apply q_is_pos_as_pos_no_succ.
    unfold q_is_pos_no_succ in *.
    destruct H0 as [p0 [p1 [Hnzp0 [Hnzp1 H0]]]].
    do 2 rewrite -> q_neg_both_sides in H0.
    symmetry in H0.
    rewrite -> q_neg_reduce_double in H0.
    symmetry in H0.
    unfold q_sub in H0.
    rewrite -> q_neg_dist_over_add in H0.
    rewrite -> q_add_comm in H0.
    rewrite -> q_neg_dist_over_add in H0.
    rewrite -> q_neg_reduce_double in H0.
    rewrite -> q_sub_refold in H0.
    exists (p0).
    exists (p1).
    exists (Hnzp0).
    exists (Hnzp1).
    exact H0.
  }
  {
    intros H0.
    unfold q_gt in *.
    apply q_is_pos_as_pos_no_succ in H0.
    apply q_is_pos_as_pos_no_succ.
    unfold q_is_pos_no_succ in *.
    destruct H0 as [p0 [p1 [Hnzp0 [Hnzp1 H0]]]].
    do 2 rewrite -> q_neg_both_sides in H0.
    symmetry in H0.
    rewrite -> q_neg_reduce_double in H0.
    symmetry in H0.
    unfold q_sub in H0.
    rewrite <- q_add_comm in H0.
    do 2 rewrite -> q_neg_reduce_double in H0.
    rewrite -> q_sub_refold in H0.
    exists (p0).
    exists (p1).
    exists (Hnzp0).
    exists (Hnzp1).
    exact H0.
  }
Qed.

Proposition q_ord_lhs_rewrite : forall (a a' b : Q) (Heq : (a ~= a')%Q), 
  (a > b)%Q <-> (a' > b)%Q.
Proof.
  intros a a' b Heq.
  split.
  {
    intros H0.
    unfold q_gt in *.
    assert (Hrw : (a - b) ~= (a' - b)).
    {
      unfold q_sub.
      rewrite -> Heq.
      reflexivity.
    }
    apply (q_is_pos_rewrite _ _ Hrw) in H0.
    exact H0.
  }
  {
    intros H0.
    unfold q_gt in *.
    assert (Hrw : (a - b) ~= (a' - b)).
    {
      unfold q_sub.
      rewrite -> Heq.
      reflexivity.
    }
    apply (q_is_pos_rewrite _ _ Hrw) in H0.
    exact H0.
  }
Qed.

Proposition q_ord_rhs_rewrite : forall (a b b' : Q) (Heq : (b ~= b')%Q), 
  (a > b)%Q <-> (a > b')%Q.
Proof.
  intros a b b' Heq.
  split.
  {
    intros H0.
    unfold q_gt in *.
    assert (Hrw : (a - b) ~= (a - b')).
    {
      unfold q_sub.
      rewrite -> Heq.
      reflexivity.
    }
    apply (q_is_pos_rewrite _ _ Hrw) in H0.
    exact H0.
  }
  {
    intros H0.
    unfold q_gt in *.
    assert (Hrw : (a - b) ~= (a - b')).
    {
      unfold q_sub.
      rewrite -> Heq.
      reflexivity.
    }
    apply (q_is_pos_rewrite _ _ Hrw) in H0.
    exact H0.

  }
Qed.

Proposition q_neg_mult_reverses_ord : forall a b c : Q, 
  (a > b) -> (q_is_neg c) -> (b*c > a*c).
Proof.
  intros [a [b Hnzb]] [c [d Hnzd]] [e [f Hnzf]] H0 H1.
  assert (Hrw : {| num := e; den := (Z_nz_ex f Hnzf) |} ~= 
                {| num := e; den := (Z_nz_ex f Hnzf) |} - (NQ#0)).
  {
    unfold q_sub.
    rewrite -> q_neg_reduce_neg_z.
    rewrite -> q_add_0_r.
    reflexivity.
  }
  apply -> (q_is_neg_rewrite _ _ Hrw) in H1.
  clear Hrw.
  apply -> q_neg_diff_is_pos_rev in H1.
  apply q_ord_rev in H0.
  apply q_ord_rev.
  assert (Hrw : (-- ( {| num := a; den := (Z_nz_ex b Hnzb) |} ) * 
                (   {| num := e; den := (Z_nz_ex f Hnzf) |})) ~= 
                (   {| num := a; den := (Z_nz_ex b Hnzb) |}) *
                (-- {| num := e; den := (Z_nz_ex f Hnzf) |})).
  {
    rewrite <- q_neg_extract_from_mult_l.
    rewrite -> q_neg_mult_swap_neg.
    reflexivity.
  }
  apply <- (q_ord_lhs_rewrite _ _
    (-- ({| num := c; den := (Z_nz_ex d Hnzd) |}) * {| num := e; den := (Z_nz_ex f Hnzf) |})
     Hrw).
  clear Hrw.
  assert (Hrw : (-- ({| num := c; den := (Z_nz_ex d Hnzd) |} * 
                (   {| num := e; den := (Z_nz_ex f Hnzf) |}))) ~= 
                (   {| num := c; den := (Z_nz_ex d Hnzd) |}) *
                (-- {| num := e; den := (Z_nz_ex f Hnzf) |})).
  {
    rewrite <- q_neg_extract_from_mult_l.
    rewrite -> q_neg_mult_swap_neg.
    reflexivity.
  }
  apply <- (q_ord_rhs_rewrite 
    ({| num := a; den := (Z_nz_ex b Hnzb) |} * (-- {| num := e; den := (Z_nz_ex f Hnzf)|}))
     _ _ Hrw).
  clear Hrw.
  assert (Hrw : ((NQ#0) - {| num := e; den := (Z_nz_ex f Hnzf) |}) ~= 
                ((-- {| num := e; den := (Z_nz_ex f Hnzf) |}))).
  {
    unfold q_sub.
    rewrite -> q_add_0_l.
    reflexivity.
  }
  apply -> (q_is_pos_rewrite _ _ Hrw) in H1.
  apply q_pos_mult_preserves_ord.
  2: exact H1.
  apply q_ord_rev in H0.
  exact H0.
Qed.

(*\end{Q is an ordered field}*)

(*\begin{Q extra}*)
(*\end{Q extra}*)

(*\begin{Q abs and exp}*)

Fixpoint nat_diff (a b : nat) : nat :=
  match a, b with
  | O, O => O
  | O, _ => b
  | _, O => a
  | S a', S b' => (nat_diff a' b')
  end.

Definition z_abs (a : Z) : Z :=
  match a with
  | {| pos := a_; neg := _a |} => {| pos := (nat_diff a_ _a); neg := 0 |}
  end.

Proposition def_z_abs : forall a : Z, (z_abs a) = {| pos := (nat_diff (pos a) (neg a)); neg := 0 |}.
Proof.
  intros a.
  unfold z_abs.
  destruct a as [a b].
  simpl.
  reflexivity.
Qed.

Proposition z_abs_as_nat_diff : forall a : Z, 
  (z_abs a) = (NZ# (nat_diff (pos a) (neg a))).
Proof.
  intros [a b].
  simpl.
  unfold NZ.
  reflexivity.
Qed.

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
    rewrite -> def_add_clause_0.
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
    do 2 rewrite -> def_add_clause_0.
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

Proposition z_abs_preserves_ne_z : forall (a : Z), 
  ((a ~= (NZ#0))%Z -> False) -> (((z_abs a) ~= (NZ#0))%Z -> False).
Proof.
  intros [a b] H0 H1.
  rewrite -> def_z_abs in H1.
  simpl in H1.
  apply -> z_eqv_nz_as_diff_sum in H1.
  rewrite -> add_0_r in H1.
  simpl in H1.
  apply -> nat_diff_eq_0_is_same in H1.
  apply <- z_eqv_0_is_same in H1.
  apply H0.
  exact H1.
Qed.

Proposition z_abs_reduce_eqv_0 : forall (a : Z), 
  ((z_abs a) ~= (NZ#0))%Z <-> (a ~= (NZ#0))%Z.
Proof.
  intros [a b].
  split.
  {
    intros H0.
    unfold z_abs in H0.
    rewrite z_formal_sub_as_sub in H0.
    unfold z_sub in H0.
    rewrite -> z_neg_reduce_neg_0 in H0.
    rewrite -> z_add_0_r in H0.
    rewrite -> z_nz_inject in H0.
    apply -> nat_diff_eq_0_is_same in H0.
    rewrite -> H0.
    apply z_same_parts_eqv_0.
  }
  {
    intros H0.
    unfold z_abs.
    rewrite z_formal_sub_as_sub.
    unfold z_sub.
    rewrite -> z_neg_reduce_neg_0.
    rewrite -> z_add_0_r.
    rewrite -> z_nz_inject.
    apply nat_diff_eq_0_is_same.
    rewrite z_formal_sub_as_sub in H0.
    apply z_mov_neg_r_to_rhs in H0.
    rewrite -> z_add_0_l in H0.
    rewrite -> z_nz_inject in H0.
    exact H0.
  }
Qed.

Proposition z_abs_reduce_mult : forall (a b : Z),
  ((z_abs a) * (z_abs b) ~= (z_abs (a * b)))%Z.
Proof.
  intros [a b] [c d].
  do 2 rewrite -> z_abs_as_nat_diff.
  unfold z_mult.
  unfold z_eq.
  simpl.
  do 3 rewrite -> add_0_r.
  rewrite -> mult_0_r.
  do 1 rewrite -> add_0_r.
  destruct (nat_diff_dichotomy a b) as [Hge_ab | Hle_ab].
  {
    destruct Hge_ab as [p0 [[Hp00 Hp01] _]].
    rewrite -> Hp00.
    rewrite -> nat_diff_reduce_add_l.
    destruct (nat_diff_dichotomy c d) as [Hge_cd | Hle_cd].
    {
      destruct Hge_cd as [p1 [[Hp10 Hp11] _]].
      rewrite -> Hp11.
      rewrite -> Hp10.
      do 2 rewrite -> mult_dist_over_add_r.
      do 2 rewrite -> mult_dist_over_add.
      repeat rewrite <- add_assoc.
      rewrite -> (add_comm (p0 * p1) (b * d)).
      repeat rewrite -> add_assoc.
      (* v Goal : [...] b * d + b * p1 + p0 * d + b * d + p0 * p1 [...] *)
      do 2 rewrite <- add_assoc.
      rewrite -> add_assoc_middle.
      rewrite -> (add_comm (b * p1) (p0 * d)).
      rewrite <- add_assoc_middle.
      do 1 rewrite -> add_assoc.
      rewrite -> add_assoc_middle.
      rewrite -> (add_comm (b * p1) (b * d)).
      rewrite <- add_assoc_middle.
      repeat rewrite -> add_assoc.
      (* ^ Goal : [...] b * d + p0 * d + b * d + b * p1 + p0 * p1 [...] *)
      rewrite nat_diff_reduce_add_l.
      reflexivity.
    }
    {
      destruct Hle_cd as [p1 [[Hp10 Hp11] _]].
      rewrite -> Hp11.
      rewrite -> Hp10.
      do 2 rewrite -> mult_dist_over_add_r.
      do 2 rewrite -> mult_dist_over_add.
      repeat rewrite <- add_assoc.
      rewrite -> (add_comm (p0 * p1) (b * c)).
      repeat rewrite -> add_assoc.
      repeat rewrite <- add_assoc.
      rewrite -> nat_diff_cancel_l.
      repeat rewrite -> add_assoc.
      rewrite -> (add_comm (b * p1) (p0 * c)).
      repeat rewrite <- add_assoc.
      rewrite -> nat_diff_cancel_l.
      repeat rewrite -> add_assoc.
      rewrite -> (add_comm (b * p1) (b * c)).
      repeat rewrite <- add_assoc.
      rewrite -> nat_diff_cancel_l.
      rewrite nat_diff_comm.
      rewrite nat_diff_reduce_add_l.
      reflexivity.
    }
  }
  {
    destruct Hle_ab as [p0 [[Hp00 Hp01] _]].
    rewrite -> Hp01.
    rewrite -> Hp00.
    do 2 rewrite -> mult_dist_over_add_r.
    repeat rewrite -> add_assoc.
    rewrite -> (add_comm (a * c) (a * d)).
    rewrite -> nat_diff_cancel_l.
    rewrite -> nat_diff_dist_mult_l.
    rewrite -> nat_diff_comm.
    reflexivity.
  }
Qed.

Definition q_abs (a : Q) : Q.
Proof.
  assert (b : Z_nz).
  {
    destruct a as [a_ [_a Hnz_a]].
    exists (z_abs _a).
    intros H0.
    apply z_abs_preserves_ne_z in Hnz_a.
    2: exact H0.
    exact Hnz_a.
  }

  exact {| 
    num := (z_abs (num a)); 
    den := b 
  |}.
Defined.

(*
Compute (q_abs (-- NQ#4)).
= (4 -Z 0) /Q Z_nz_ex (1 -Z 0)%Z [...]
*)


Definition q_dist (a b : Q) : Q :=
  (q_abs (a - b)).

(*
Compute (q_dist (NQ#3) (NQ#5)).
= (2 -Z 0) /Q Z_nz_ex (1 -Z 0)%Z [...]
*)

Proposition def_q_abs : forall (a b : Z)
  (Hnzb : (b ~= (NZ#0))%Z -> False) (Hnzb_abs : ((z_abs b) ~= (NZ#0))%Z -> False),
  (q_abs {| num := a; den := (Z_nz_ex b Hnzb) |}) ~= 
  {| num := (z_abs a); den := (Z_nz_ex (z_abs b) Hnzb_abs) |}.
Proof.
  intros a b Hnzb Hnzb_abs.
  unfold q_abs.
  unfold q_eq.
  simpl.
  reflexivity.
Qed.

Require Import Stdlib.Classes.Morphisms.
Instance z_abs_proper : 
  Proper (z_eq ==> z_eq) z_abs.
Proof.
  intros [a b] [a' b'] Heq.
  do 2 rewrite -> z_abs_as_nat_diff.
  rewrite -> z_nz_inject.
  simpl.
  unfold z_eq in Heq.
  simpl in Heq.
  destruct (nat_diff_dichotomy a a') as [Hge_ab | Hle_ab].
  {
    destruct Hge_ab as [p0 [[Hp0l Hp0r] _]].
    rewrite -> Hp0l.
    destruct (nat_diff_dichotomy b b') as [Hge_bb' | Hle_bb'].
    {
      destruct Hge_bb' as [p1 [[Hp1l Hp1r] _]].
      rewrite -> Hp1l.
      rewrite -> Hp0l in Heq.
      rewrite -> Hp1l in Heq.
      rewrite <- add_assoc in Heq.
      apply -> add_cancel in Heq.
      rewrite -> add_comm in Heq.
      apply -> add_cancel in Heq.
      rewrite -> Heq.
      rewrite -> nat_diff_cancel_r.
      reflexivity.
    }
    {
      destruct Hle_bb' as [p1 [[Hp1l Hp1r] _]].
      rewrite -> Hp1l.
      rewrite -> Hp0l in Heq.
      rewrite -> Hp1l in Heq.
      rewrite <- add_assoc in Heq.
      apply -> add_cancel in Heq.
      rewrite -> add_assoc in Heq.
      rewrite -> (add_comm p0 b) in Heq.
      symmetry in Heq.
      rewrite <- add_assoc in Heq.
      apply -> add_cancel_2 in Heq.
      symmetry in Heq.
      apply zero_sum_zero_parts in Heq.
      destruct Heq as [Hzp0 Hzp1].
      rewrite -> Hzp0.
      rewrite -> Hzp1.
      do 2 rewrite -> add_0_r.
      reflexivity.
    }
  }
  {
    destruct Hle_ab as [p0 [[Hp0l Hp0r] _]].
    destruct (nat_diff_dichotomy b b') as [Hge_bb' | Hle_bb'].
    {
      destruct Hge_bb' as [p1 [[Hp1l Hp1r] _]].
      rewrite -> Hp0l in Heq.
      rewrite -> Hp1l in Heq.
      rewrite -> add_assoc_middle in Heq.
      rewrite -> (add_comm p0 b') in Heq.
      rewrite <- add_assoc_middle in Heq.
      apply add_cancel_2 in Heq.
      symmetry in Heq.
      apply zero_sum_zero_parts in Heq.
      destruct Heq as [Hzp0 Hzp1].
      rewrite -> Hzp0 in Hp0l.
      rewrite -> Hzp1 in Hp1l.
      rewrite -> add_0_r in Hp0l, Hp1l.
      rewrite -> Hp0l.
      rewrite -> Hp1l.
      reflexivity.
    }
    {
      destruct Hle_bb' as [p1 [[Hp1l Hp1r] _]].
      rewrite -> Hp0l in Heq.
      rewrite -> Hp1l in Heq.
      rewrite <- add_assoc in Heq.
      rewrite -> (add_comm p0 b) in Heq.
      do 2 rewrite -> add_assoc in Heq.
      rewrite -> add_cancel in Heq.
      rewrite -> Hp1l.
      rewrite -> Hp0l.
      rewrite -> Heq.
      rewrite -> nat_diff_cancel_r.
      reflexivity.
    }
  }
Qed.

Proposition z_abs_respects_equivalence : forall (a a' : Z),
  ((a ~= a') -> (z_abs a) ~= (z_abs a'))%Z.
Proof.
  intros a a' Heq.
  rewrite -> Heq.
  reflexivity.
Qed.

Proposition z_abs_reduce_non_neg : forall (a : nat),
  ((z_abs (NZ# a)) ~= (NZ# a))%Z.
Proof.
  intros a.
  rewrite -> z_abs_as_nat_diff.
  simpl.
  rewrite -> z_nz_inject.
  rewrite -> nat_diff_0_r.
  reflexivity.
Qed.

Require Import Stdlib.Classes.Morphisms.
Instance q_abs_proper : 
  Proper (q_eq ==> q_eq ) q_abs.
Proof.
  intros [a [b Hnzb]] [a' [b' Hnzb']] Ha.
  assert (Hnzb_abs : ((z_abs b) ~= (NZ#0))%Z -> False).
  {
    apply z_abs_preserves_ne_z.
    exact Hnzb.
  }
  assert (Hnzb'_abs : ((z_abs b') ~= (NZ#0))%Z -> False).
  {
    apply z_abs_preserves_ne_z.
    exact Hnzb'.
  }
  rewrite -> (def_q_abs _ _ _ Hnzb_abs).
  rewrite -> (def_q_abs _ _ _ Hnzb'_abs).
  unfold q_eq in *.
  simpl in *.
  do 2 rewrite -> z_abs_reduce_mult.
  rewrite -> Ha.
  reflexivity.
Qed.

Proposition q_abs_respects_equivalence : forall (a a' : Q),
  ((a ~= a') -> (q_abs a) ~= (q_abs a'))%Q.
Proof.
  intros a a' Heq.
  rewrite -> Heq.
  reflexivity.
Qed.

Proposition q_abs_reduce_eqv_0 : forall a : Q, 
  ((q_abs a) ~= (NQ#0)) <-> (a ~= (NQ#0)).
Proof.
  intros [a [b Hnzb]].
  split.
  {
    intros H0.
    assert (Hnzb_abs : ((z_abs b) ~= (NZ#0))%Z -> False).
    {
      apply z_abs_preserves_ne_z.
      exact Hnzb.
    }
    rewrite -> (def_q_abs _ _ _ Hnzb_abs) in H0.
    apply q_num_0_is_eqv_0 in H0.
    apply q_num_0_is_eqv_0.
    apply -> z_abs_reduce_eqv_0 in H0.
    exact H0.
  }
  {
    intros H0.
    apply q_num_0_is_eqv_0 in H0.
    assert (Hnzb_abs : ((z_abs b) ~= (NZ#0))%Z -> False).
    {
      apply z_abs_preserves_ne_z.
      exact Hnzb.
    }
    rewrite -> (def_q_abs _ _ _ Hnzb_abs).
    apply q_num_0_is_eqv_0.
    apply z_abs_reduce_eqv_0.
    exact H0.
  }
Qed.

Proposition q_abs_reduce_abs_0 :
  ((q_abs (NQ#0)) ~= (NQ#0))%Q.
Proof.
  easy.
Qed.

Proposition q_abs_reduce_pos : forall (a : Q) (Hpa : (q_is_pos a)),
  (q_abs a) ~= a.
Proof.
  intros [[a b] [[c d] Hnz0]] [p0 [p1 [Hnzp1 H0]]].
  assert (Hnz0_abs : ((z_abs {| pos := c; neg := d |}) ~= (NZ#0))%Z -> False).
  {
    apply z_abs_preserves_ne_z.
    exact Hnz0.
  }
  rewrite -> (def_q_abs _ _ _ Hnz0_abs).
  rewrite -> H0.
  unfold q_eq in H0.
  simpl in H0.
  unfold q_eq.
  simpl.
  do 2 rewrite -> z_formal_sub_as_sub.
  do 2 rewrite -> z_sub_reduce_0_r.
  do 2 rewrite -> z_mult_reduce_non_neg.
  rewrite -> z_nz_inject.
  destruct (nat_diff_dichotomy a b) as [Hge_ab | Hle_ab].
  {
    destruct Hge_ab as [p2 [[Hp2l Hp2r] _]].
    rewrite -> Hp2l.
    rewrite -> nat_diff_reduce_add_l.
    destruct (nat_diff_dichotomy c d) as [Hge_cd | Hle_cd].
    {
      destruct Hge_cd as [p3 [[Hp3l Hp3r] _]].
      rewrite -> Hp2l in H0.
      rewrite -> Hp3l in H0.
      rewrite -> Hp3r.
      do 2 rewrite -> z_reduce_shared_part_pos in H0.
      do 2 rewrite -> z_mult_reduce_non_neg in H0.
      rewrite -> z_nz_inject in H0.
      exact H0.
    }
    {
      destruct Hle_cd as [p3 [[Hp3l Hp3r] _]].
      rewrite -> Hp2l in H0.
      rewrite -> Hp3l in H0.
      rewrite -> Hp3r.
      rewrite -> z_reduce_shared_part_pos in H0.
      rewrite -> z_reduce_shared_part_neg in H0.
      rewrite -> z_neg_extract_from_mult_r in H0.
      do 2 rewrite -> z_mult_reduce_non_neg in H0.
      apply z_non_neg_eqv_neg_implies_0 in H0 as [H0l H0r].
      rewrite -> H0l.
      rewrite -> H0r.
      reflexivity.
    }
  }
  {
    destruct Hle_ab as [p2 [[Hp2l Hp2r] _]].
    rewrite -> Hp2r.
    destruct (nat_diff_dichotomy c d) as [Hge_cd | Hle_cd].
    {
      destruct Hge_cd as [p3 [[Hp3l Hp3r] _]].
      rewrite -> Hp3r.
      rewrite -> Hp2l in H0.
      rewrite -> Hp3l in H0.
      rewrite -> z_reduce_shared_part_pos in H0.
      rewrite -> z_reduce_shared_part_neg in H0.
      rewrite -> z_neg_extract_from_mult_l in H0.
      do 2 rewrite -> z_mult_reduce_non_neg in H0.
      symmetry in H0.
      apply z_non_neg_eqv_neg_implies_0 in H0 as [H0l H0r].
      rewrite -> H0l.
      rewrite -> H0r.
      reflexivity.
    }
    {
      destruct Hle_cd as [p3 [[Hp3l Hp3r] _]].
      rewrite -> Hp3r.
      rewrite -> Hp2l in H0.
      rewrite -> Hp3l in H0.
      do 2 rewrite -> z_reduce_shared_part_neg in H0.
      rewrite -> z_neg_extract_from_mult_l in H0.
      rewrite -> z_neg_extract_from_mult_r in H0.
      do 2 rewrite -> z_mult_reduce_non_neg in H0.
      apply z_neg_both_sides in H0.
      rewrite -> z_nz_inject in H0.
      exact H0.
    }
  }
Qed.

Proposition q_abs_both_sides : forall (a b : Q),
  (a ~= b) -> ((q_abs a) ~= (q_abs b)).
Proof.
  intros a b H0.
  rewrite -> H0.
  reflexivity.
Qed.

Proposition q_abs_reduce_neg : forall (a : Q), (q_abs (-- a)) ~= (q_abs a).
Proof.
  intros [[a b] [[c d] Hnz0]].
  unfold q_abs.
  unfold q_eq.
  simpl.
  do 3 rewrite -> z_0_neg_as_nz.
  rewrite -> (nat_diff_comm b a).
  reflexivity.
Qed.

Proposition q_abs_reduce_neg_val : forall (a : Q) (Hpa : (q_is_neg a)),
  (q_abs a) ~= (-- a).
Proof.
  intros [[a b] [[c d] Hnz0]] [q0 [Hpq0 Hq0r]].
  assert (Hnz0_abs : ((z_abs {| pos := c; neg := d |}) ~= (NZ#0))%Z -> False).
  {
    apply z_abs_preserves_ne_z.
    exact Hnz0.
  }
  rewrite -> (def_q_abs _ _ _ Hnz0_abs).
  rewrite -> Hq0r.
  rewrite -> q_neg_reduce_double.
  apply q_abs_both_sides in Hq0r.
  rewrite -> (def_q_abs _ _ _ Hnz0_abs) in Hq0r.
  rewrite -> Hq0r.
  rewrite -> q_abs_reduce_neg.
  apply q_abs_reduce_pos.
  exact Hpq0.
Qed.

Proposition q_abs_dichotomy : forall a : Q, 
  ((q_abs a) ~= (NQ#0)) \/ (q_is_pos (q_abs a)).
Proof.
  intros a.
  destruct (q_trichotomy_3 a) as [Hza | [Hpa | Hna]].
  {
    apply q_abs_both_sides in Hza.
    rewrite -> q_abs_reduce_abs_0 in Hza.
    left.
    exact Hza.
  }
  {
    right.
    apply q_abs_reduce_pos in Hpa as H0.
    apply (q_is_pos_rewrite _ _ H0).
    exact Hpa.
  }
  {
    right.
    apply q_abs_reduce_neg_val in Hna as H0.
    apply (q_is_pos_rewrite _ _ H0).
    destruct Hna as [q0 [Hpq0 Hrwq0]].
    apply q_neg_both_sides in Hrwq0.
    apply (q_is_pos_rewrite _ _ Hrwq0).
    assert (Hrw : ((-- (-- q0)) ~= q0)%Q).
    {
      rewrite -> q_neg_reduce_double.
      reflexivity.
    }
    apply (q_is_pos_rewrite _ _ Hrw).
    clear Hrw.
    exact Hpq0.
  }
Qed.

Proposition q_abs_triangle_inequality : forall (a b : Q),
  ((q_abs a) + (q_abs b) >= (q_abs (a + b)))%Q.

Proposition q_abs_ineq_between_neg_pos : forall (a b : Q), 
  (a >= (q_abs b)) <-> ((a >= b) /\ (b >= (--a))).

Proposition q_abs_reduce_mult : forall (a b : Q),
  ((q_abs a) * (q_abs b) ~= (q_abs (a * b)))%Q.

Proposition q_dist_reduce_eqv_0 : forall (a b : Q),
  ((q_dist a b) ~= (NQ#0) <-> (a ~= b))%Q.

Proposition q_dist_dichotomy : forall (a b : Q), 
  ((q_dist a b) ~= (NQ#0)) \/ (q_is_pos (q_abs a)).

Proposition q_dist_triangle_inequality : forall (a b c : Q),
  (q_dist a b) + (q_dist b c) >= (q_dist a c).

(*epsilon closeness*)
Definition q_eps_close (a b eps : Q) (Hpeps : (q_is_pos eps)) :=
  eps >= (q_dist a b).

Proposition q_eps_close_eqv_is_close : forall (a b eps : Q) (Hpeps : (q_is_pos eps)),
  (a ~= b)%Q <-> (q_eps_close a b eps Hpeps).

Proposition q_eps_close_additive_1 : forall (a b c eps1 eps2 : Q) 
  (Hpeps1 : (q_is_pos eps1)) (Hpeps2 : (q_is_pos eps2))
  (Hpeps1p2 : (q_is_pos (eps1 + eps2))),
  (q_eps_close a b eps1 Hpeps1) -> 
  (q_eps_close b c eps2 Hpeps2) -> 
  (q_eps_close a c (eps1 + eps2) Hpeps1p2).

Proposition q_eps_close_additive_2 : forall (a b c d eps1 eps2 : Q) 
  (Hpeps1 : (q_is_pos eps1)) (Hpeps2 : (q_is_pos eps2))
  (Hpeps1p2 : (q_is_pos (eps1 + eps2))),
  (q_eps_close a b eps1 Hpeps1) -> 
  (q_eps_close c d eps2 Hpeps2) -> 
  ((q_eps_close (a + c) (b + d) (eps1 + eps2) Hpeps1p2) /\
   (q_eps_close (a - c) (b - d) (eps1 + eps2) Hpeps1p2)).

Proposition q_eps_close_for_between : forall (a b c d eps : Q)
  (Hpeps : (q_is_pos eps)),
  ((q_eps_close a b eps Hpeps) /\ (q_eps_close a c eps Hpeps)) ->
  ((d >= b /\ c >= d) \/ (b >= d /\ d >= c)) ->
  (q_eps_close a d eps Hpeps).

Proposition q_eps_close_multiplicative_1 : forall (a b eps : Q) (c : Q_nz)
  (Hpeps : (q_is_pos eps))
  (Hpepsc : (q_is_pos (eps * (q_abs (proj1_sig c))))%Q),
  (q_eps_close a b eps Hpeps) -> 
  (q_eps_close (a*(proj1_sig c)) (b*(proj1_sig c)) (eps * (q_abs (proj1_sig c))) Hpepsc).

Proposition q_eps_close_multiplicative_2 : forall (a b c d eps1 eps2 : Q) 
  (Hpeps1 : (q_is_pos eps1)) (Hpeps2 : (q_is_pos eps2))
  (Hp1 : (q_is_pos (eps1 * (q_abs c) + eps2 * (q_abs a) + eps1 * eps2))),

(*\end{Q abs and exp}*)

Close Scope Q_scope.
(*\end{Q}*)