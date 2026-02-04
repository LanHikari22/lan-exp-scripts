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

Proposition add_preserves_ge : forall a b c : nat, (ge a b) <-> (ge (a + c) (b + c)).
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

Proposition gt_to_ge : forall a b : nat, (gt b a) <-> (ge b (S a)).
Proof.
intros a b.
unfold gt.
unfold ge.
split.
{
  intros H0.
  destruct H0 as [H0l H0r].
  {
    destruct H0l as [p0 [Hp0 Hp0u]].
    {
      rewrite -> Hp0.
      destruct p0 as [| p0'] eqn:Ep0.
      {
        rewrite -> add_0_r in Hp0.
        apply H0r in Hp0.
        contradiction Hp0.
      }
      {
        exists p0'.
        split.
        {
          rewrite -> add_swap_s.
          reflexivity.
        }
        {
          intros x' Hx'.
          rewrite <- add_swap_s in Hx'.
          apply add_cancel in Hx'.
          apply Hx'.
        }
      }
    }
  }
}
{
  intros H0.
  destruct H0 as [p0 [Hp0 Hp0u]].
  {
    split.
    {
      exists (S p0).
      split.
      {
        rewrite <- add_swap_s.
        rewrite -> Hp0.
        reflexivity.
      }
      {
        intros x' Hx'.
        rewrite -> Hp0 in Hx'.
        rewrite -> add_swap_s in Hx'.
        apply add_cancel in Hx'.
        apply Hx'.
      }
    }
    {
      intros H1.
      rewrite H1 in Hp0.
      apply add_succ_implies_ne_2 in Hp0.
        contradiction Hp0.
      }
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
  intros a b H0.
  unfold gt.
  unfold ge.
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
  intros H0.
  destruct H0 as [H0l H0r].
  {
    destruct H0l as [p0 [Hp0 Hp0u]].
    {
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
    }
  }
Qed.
(* still to show at least one is true *)


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

Proposition mult_pos_no_zero_div : forall a b : nat, a * b = 0 <-> a = 0 \/ b = 0.
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