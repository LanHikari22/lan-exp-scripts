Proposition reduce_p_or_p : forall (p : Prop), p \/ p -> p.
Proof.
  intros p H0.
  destruct H0 as [H0l | H0r].
  1: exact H0l. 1: exact H0r.
Qed.
