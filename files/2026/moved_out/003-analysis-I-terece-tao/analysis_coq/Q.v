Require Import CoqAnalysis.Nat.
Set Warnings "+notation-overridden".
Require Import CoqAnalysis.Z.
Require Import CoqAnalysis.Misc.

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

Proposition q_nq_1_is_same_num_den : forall (a : nat) (Hnza : ((NZ#a) ~= (NZ#0))%Z -> False), 
  ((NQ#1) ~= {| num := (NZ#a); den := (Z_nz_ex (NZ#a) Hnza) |})%Q.
Proof.
  intros a Hnza.
  unfold q_eq.
  simpl.
  rewrite -> z_mult_ident_l.
  rewrite -> z_mult_ident_r.
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

Proposition q_num_0_is_eqv_0_1 : forall (b : Z_nz), 
  ({| num := (NZ#0); den := b |} ~= (NQ#0))%Q.
Proof.
  intros [b Hnzb].
  unfold q_eq.
  simpl.
  do 2 rewrite -> z_mult_0_l.
  reflexivity.
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

Definition q_recip (a : Q) (Hnza : ((num a) ~= (NZ#0))%Z -> False) : Q :=
  {|
    num := (proj1_sig (den a));
    den := (Z_nz_ex (num a) Hnza)
  |}.

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

Proposition q_mult_0_l : forall a : Q, (NQ#0) * a ~= (NQ#0).
Proof.
  intros [a [b Hnzb]].
  unfold q_mult, q_eq; simpl.
  do 2 rewrite -> z_mult_0_l.
  reflexivity.
Qed.

Proposition q_mult_0_r : forall a : Q, a * (NQ#0) ~= (NQ#0).
Proof.
  intros [a [b Hnzb]].
  unfold q_mult, q_eq; simpl.
  rewrite -> z_mult_0_l.
  rewrite -> z_mult_0_r.
  rewrite -> z_mult_0_l.
  reflexivity.
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

Proposition q_norm_multiplicative_inverse : forall (a b : nat) 
  (Hnza : ((NZ#a) ~= (NZ#0))%Z -> False) (Hnzb : ((NZ#b) ~= (NZ#0))%Z -> False),
  ({| num := (NZ#a); den := (Z_nz_ex (NZ#b) Hnzb) |} *
   {| num := (NZ#b); den := (Z_nz_ex (NZ#a) Hnza) |} ~= (NQ#1))%Q.
Proof.
  intros a b Hnza Hnzb.
  unfold q_eq, q_mult; simpl.
  rewrite -> z_mult_ident_r.
  rewrite -> z_mult_ident_l.
  rewrite -> z_mult_comm.
  reflexivity.
Qed.

Proposition q_nq_multiplicative_inverse_l : forall (a : nat) 
  (Hnza : ((NZ#a) ~= (NZ#0))%Z -> False),
  ((NQ#a) * {| num := (NZ#1); den := (Z_nz_ex (NZ#a) Hnza) |} ~= (NQ#1))%Q.
Proof.
  intros a Hnza.
  unfold q_eq, q_mult; simpl.
  do 2 rewrite -> z_mult_ident_r.
  do 2 rewrite -> z_mult_ident_l.
  reflexivity.
Qed.

Proposition q_nq_multiplicative_inverse_r : forall (a : nat) 
  (Hnza : ((NZ#a) ~= (NZ#0))%Z -> False),
  ({| num := (NZ#1); den := (Z_nz_ex (NZ#a) Hnza) |} * (NQ#a) ~= (NQ#1))%Q.
Proof.
  intros a Hnza.
  unfold q_eq, q_mult; simpl.
  do 2 rewrite -> z_mult_ident_r.
  rewrite -> z_mult_ident_l.
  reflexivity.
Qed.

Proposition q_double_is_same_add : forall (a : Q),
  a * (NQ#2) ~= a + a.
Proof.
  intros [a [b Hnzb]].
  assert (Hrw : (NQ#2) ~= (NQ#1) + (NQ#1)).
  {
    easy.
  }
  rewrite -> Hrw.
  rewrite -> q_mult_dist_over_add_l.
  rewrite -> q_mult_ident_r.
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

(*\begin{Q extra 0}*)

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

Proposition q_reduce_sub_0 : forall a : Q, (a - (NQ#0) ~= a)%Q.
Proof.
  intros a.
  unfold q_sub.
  rewrite -> q_neg_reduce_neg_z.
  rewrite -> q_add_0_r.
  reflexivity.
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
  repeat rewrite -> mult_0_l.
  repeat rewrite -> add_0_l.
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
  repeat rewrite -> mult_0_l.
  repeat rewrite -> add_0_l.
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
        rewrite -> mult_0_l.
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

Proposition q_nz_reduce_frac_add : forall (a b c d : nat)
  (Hnzb : ((NZ#b) ~= (NZ#0))%Z -> False) (Hnzd : ((NZ#d) ~= (NZ#0))%Z -> False)
  (Hnzbd : ((NZ#b*d) ~= (NZ#0))%Z -> False),
  (((NZ# a) /Q (Z_nz_ex (NZ#b) Hnzb))) + ((NZ# c) /Q (Z_nz_ex (NZ#d) Hnzd))
  ~= ((NZ# a * d + b * c) /Q (Z_nz_ex (NZ# b * d) Hnzbd)).
Proof.
  intros a b c d Hnzb Hnzd Hnzbd.
  unfold q_add, q_eq; simpl.
  do 4 rewrite -> z_mult_reduce_non_neg.
  rewrite -> z_nz_reduce_add.
  rewrite -> z_mult_reduce_non_neg.
  reflexivity.
Qed.


Proposition q_nq_reduce_add : forall a b : nat,
  (NQ#a) + (NQ#b) ~= (NQ# a + b).
Proof.
  intros a b.
  unfold q_add, q_eq.
  simpl.
  do 2 rewrite -> z_mult_ident_l.
  do 3 rewrite -> z_mult_ident_r.
  rewrite -> z_nz_reduce_add.
  reflexivity.
Qed.

Proposition q_nq_reduce_sub : forall a b : nat,
  ((NQ#a) - (NQ#b) ~= (ZQ# ((NZ#a) - (NZ#b))%Z))%Q.
Proof.
  intros a b.
  unfold q_sub, q_neg, q_add, q_eq.
  simpl.
  do 3 rewrite -> z_mult_ident_r.
  rewrite -> z_mult_ident_l.
  rewrite -> z_sub_refold.
  reflexivity.
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

Proposition q_div_reduce_sub_formal_same_den_2 : forall (a b c : nat)
  (Hnzb : ((NZ#b) ~= (NZ#0))%Z -> False),
  {| num := (NZ#a); den := (Z_nz_ex (NZ#b) Hnzb) |} - 
  {| num := (NZ#c); den := (Z_nz_ex (NZ#b) Hnzb) |}
  ~= {| num := (NZ#a) - (NZ#c); den := (Z_nz_ex (NZ#b) Hnzb) |}.
Proof.
  intros a b c.
  apply q_div_reduce_sub_formal_same_den.
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
  do 6 rewrite -> add_0_l.
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

Proposition q_add_cancel_l : forall (a b c: Q), (a + b ~= a + c) <-> (b ~= c).
Proof.
  intros [a [b Hnzb]] [c [d Hnzd]] [e [f Hnzf]].
  split.
  {
    intros H0.
    unfold q_add in *.
    unfold q_eq in *.
    simpl in *.
    do 2 rewrite -> z_mult_dist_over_add_r in H0.
    do 4 rewrite <- z_mult_assoc in H0.
    assert (Hrw : (a * d * b * f ~= a * f * b * d)%Z).
    {
      repeat rewrite -> z_mult_assoc.
      apply z_mult_cancel_l_3.
      right.
      rewrite -> z_mult_comm.
      repeat rewrite <- z_mult_assoc.
      apply z_mult_cancel_r_3.
      right.
      rewrite -> z_mult_comm.
      reflexivity.
    }
    rewrite -> Hrw in H0.
    clear Hrw.
    rewrite -> z_add_cancel_l in H0.
    repeat rewrite -> z_mult_assoc in H0.
    apply z_mult_cancel_l in H0.
    2: exact Hnzb.
    rewrite -> (z_mult_comm b f) in H0.
    rewrite -> (z_mult_comm b d) in H0.
    repeat rewrite <- z_mult_assoc in H0.
    apply z_mult_cancel_r in H0.
    2: exact Hnzb.
    exact H0.
  }
  {
    intros H0.
    rewrite -> H0.
    reflexivity.
  }
Qed.

Proposition q_add_cancel_r : forall (a b c: Q), (a + c ~= b + c) <-> (a ~= b).
Proof.
  intros a b c.
  split.
  {
    intros H0.
    rewrite -> (q_add_comm a c) in H0.
    rewrite -> (q_add_comm b c) in H0.
    apply -> q_add_cancel_l in H0.
    exact H0.
  }
  {
    intros H0.
    rewrite -> H0.
    reflexivity.
  }
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

Proposition q_z_mult_reduce_2 : forall (a b c d : nat)
  (Hnzb : ((NZ#b) ~= (NZ#0))%Z -> False)
  (Hnzd : ((NZ#d) ~= (NZ#0))%Z -> False)
  (Hnzbd : ((NZ#b*d) ~= (NZ#0))%Z -> False),
  {| num := (NZ#a); den := (Z_nz_ex (NZ#b) Hnzb) |} * 
  {| num := (NZ#c); den := (Z_nz_ex (NZ#d) Hnzd) |}
  ~= {| num := (NZ#a*c); den := (Z_nz_ex (NZ#(b*d)) Hnzbd) |}.
Proof.
  intros a b c d Hnzb Hnzd Hnzbd.
  specialize ((proj1 (z_mult_preserves_ne_z_3 b d)) (conj Hnzb Hnzd)) as Hnzbd'.
  rewrite -> (q_z_mult_reduce _ _ _ _ _ _ Hnzbd').
  unfold q_eq.
  simpl.
  do 4 rewrite -> z_mult_reduce_non_neg.
  reflexivity.
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

Proposition q_neg_num_extract : forall (a b : Z) (Hnzb : (b ~= (NZ#0))%Z -> False),
  {| num := (-- a)%Z; den := (Z_nz_ex b Hnzb) |} ~= 
  (-- {| num := a; den := (Z_nz_ex b Hnzb) |}).
Proof.
  intros a b Hnzb.
  reflexivity.
Qed.

Proposition q_neg_den_extract : forall (a b : Z) (Hnzb : (b ~= (NZ#0))%Z -> False)
  (Hnzb' : ((-- b) ~= (NZ#0))%Z -> False),
  {| num := a; den := (Z_nz_ex (-- b)%Z Hnzb') |} ~= 
  (-- {| num := a; den := (Z_nz_ex b Hnzb) |}).
Proof.
  intros a b Hnzb Hnzb'.
  unfold q_eq.
  simpl.
  rewrite -> z_neg_extract_from_mult_l.
  rewrite -> z_neg_extract_from_mult_r.
  rewrite -> z_neg_reduce_double.
  reflexivity.
Qed.

Proposition q_neg_reduce_zq : forall (a : Z), (ZQ# (-- a)) ~= (-- (ZQ#a)).
Proof.
  intros a.
  reflexivity.
Qed.

Proposition q_zq_reduce_add_neg_l : forall (a b : nat), 
  ((ZQ# -- (NZ#a) + (NZ#b)) ~= (-- NQ#a) + (NQ#b))%Q.
Proof.
  intros a b.
  unfold q_neg, q_add, q_eq.
  simpl.
  do 3 rewrite -> z_mult_ident_r.
  rewrite -> z_mult_ident_l.
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

Proposition zq_inject : forall (a b : Z), (a ~= b)%Z <-> ((ZQ#a) ~= (ZQ#b)).
Proof.
  intros a b.
  split.
  {
    intros H0.
    unfold ZQ.
    unfold q_eq.
    simpl.
    do 2 rewrite -> z_mult_ident_r.
    exact H0.
  }
  {
    intros H0.
    unfold ZQ in H0.
    unfold q_eq in H0.
    simpl in H0.
    do 2 rewrite -> z_mult_ident_r in H0.
    exact H0.
  }
Qed.

Proposition zq_neg_extract : forall (a : Z), (ZQ# (-- a)) ~= (-- (ZQ#a)).
Proof.
  intros a.
  unfold q_neg.
  unfold q_eq.
  simpl.
  rewrite -> z_mult_ident_r.
  reflexivity.
Qed.

Proposition q_is_pos_implies_num_nz : forall (a : Q) (Hpa : q_is_pos a),
  ((num a) ~= (NZ#0))%Z -> False.
Proof.
  intros [a [b Hnzb]] Hpa H0.
  apply q_is_pos_as_pos_no_succ in Hpa.
  unfold q_is_pos_no_succ in Hpa.
  destruct Hpa as [p0 [p1 [Hnzp0 [Hnzp1 Hpa]]]].
  simpl in H0.
  rewrite (q_num_rewrite _ _ _ _ H0) in Hpa.
  rewrite -> q_num_0_is_eqv_0_1 in Hpa.
  symmetry in Hpa.
  rewrite -> q_num_0_is_eqv_0 in Hpa.
  specialize (Hnzp0 Hpa).
  contradiction.
Qed.


(*\end{Q extra 0}*)

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
  rewrite -> mult_Sa_b in H6.
  do 2 rewrite -> add_Sn_m in H6.
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

(* Depending on application, this can be too slow. Be explicit about 
   the direction in apply with apply -> or apply <-. *)
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

Proposition q_ge_lhs_rewrite : forall (a a' b : Q) (Heq : a ~= a'),
  (a >= b)%Q <-> (a' >= b)%Q.
Proof.
  intros a a' b Heq.
  split.
  {
    intros H0.
    unfold q_ge in H0.
    unfold q_ge.
    destruct H0 as [H0l | H0r].
    {
      specialize (q_ord_lhs_rewrite a a' b Heq) as Hrw.
      destruct Hrw as [Hrw _].
      specialize (Hrw H0l).
      left.
      exact Hrw.
    }
    {
      right.
      rewrite <- Heq.
      exact H0r.
    }
  }
  {
    intros H0.
    unfold q_ge in H0.
    unfold q_ge.
    destruct H0 as [H0l | H0r].
    {
      specialize (q_ord_lhs_rewrite a a' b Heq) as Hrw.
      destruct Hrw as [_ Hrw].
      specialize (Hrw H0l).
      left.
      exact Hrw.
    }
    {
      right.
      rewrite <- Heq in H0r.
      exact H0r.
    }
  }
Qed.

Proposition q_ge_rhs_rewrite : forall (a b b' : Q) (Heq : b ~= b'),
  (a >= b) <-> (a >= b').
Proof.
  intros a a' b Heq.
  split.
  {
    intros H0.
    unfold q_ge in H0.
    unfold q_ge.
    destruct H0 as [H0l | H0r].
    {
      specialize (q_ord_rhs_rewrite a a' b Heq) as Hrw.
      destruct Hrw as [Hrw _].
      specialize (Hrw H0l).
      left.
      exact Hrw.
    }
    {
      right.
      rewrite <- Heq.
      exact H0r.
    }
  }
  {
    intros H0.
    unfold q_ge in H0.
    unfold q_ge.
    destruct H0 as [H0l | H0r].
    {
      specialize (q_ord_rhs_rewrite a a' b Heq) as Hrw.
      destruct Hrw as [_ Hrw].
      specialize (Hrw H0l).
      left.
      exact Hrw.
    }
    {
      right.
      rewrite <- Heq in H0r.
      exact H0r.
    }
  }
Qed.

Proposition q_ge_rev : forall a b : Q,
  (a >= b) <-> ((-- b) >= (-- a)).
Proof.
  intros a b.
  split.
  {
    intros H0.
    unfold q_ge in H0.
    unfold q_ge.
    destruct H0 as [H0l | H0r].
    {
      left.
      apply -> q_ord_rev.
      exact H0l.
    }
    {
      right.
      rewrite <- q_neg_both_sides.
      symmetry.
      exact H0r.
    }
  }
  {
    intros H0.
    unfold q_ge in H0.
    unfold q_ge.
    destruct H0 as [H0l | H0r].
    {
      left.
      apply <- q_ord_rev.
      exact H0l.
    }
    {
      right.
      rewrite <- q_neg_both_sides in H0r.
      symmetry.
      exact H0r.
    }
  }
Qed.

Proposition q_ge_refl : forall a : Q, (a >= a)%Q.
Proof.
  intros [a [b Hnzb]].
  unfold q_ge.
  right.
  reflexivity.
Qed.

Proposition q_0_is_not_pos : (q_is_pos (NQ#0)) -> False.
Proof.
  intros H0.
  unfold q_is_pos in H0.
  destruct H0 as [p0 [p1 [HnzSp1 H0]]].
  unfold q_eq in H0.
  simpl in H0.
  rewrite -> z_mult_0_l in H0.
  rewrite -> z_mult_ident_r in H0.
  rewrite -> z_nz_inject in H0.
  discriminate.
Qed.

Proposition q_nq_inject : forall (a b : nat),
  ((NQ#a) ~= (NQ#b))%Q <-> (a = b).
Proof.
  intros a b.
  split.
  {
    intros H0.
    unfold q_eq in H0.
    simpl in H0.
    do 2 rewrite -> z_mult_ident_r in H0.
    rewrite -> z_nz_inject in H0.
    exact H0.
  }
  {
    intros H0.
    rewrite -> H0.
    reflexivity.
  }
Qed.

Proposition q_ord_nq_inject : forall (a b : nat),
  ((NQ# a) > (NQ# b))%Q <-> (a > b)%nat.
Proof.
  intros a b.
  split.
  {
    intros H0.
    destruct (nat_ord_trichotomy_3 a b) as [Heq | [Hgt | Hlt]].
    {
      rewrite -> Heq in H0.
      unfold q_gt in H0.
      assert (Hrw : (((NQ#b) - (NQ#b)) ~= (NQ#0))%Q ).
      {
        unfold q_sub.
        rewrite -> q_additive_inverse_r.
        reflexivity.
      }
      apply (q_is_pos_rewrite _ _ Hrw) in H0.
      apply q_0_is_not_pos in H0.
      contradiction.
    }
    {
      exact Hgt.
    }
    {
      apply gt_as_ge_succ in Hlt.
      destruct Hlt as [p0 [Hp0 _]].
      specialize (q_nq_inject b (S a + p0)) as Hrw.
      destruct Hrw as [_ Hrw].
      specialize (Hrw Hp0).
      apply -> (q_ord_rhs_rewrite (NQ#a) _ _ Hrw) in H0.
      clear Hrw.
      unfold q_gt in H0.
      apply q_is_pos_as_pos_no_succ in H0.
      unfold q_is_pos_no_succ in H0.
      destruct H0 as [p1 [p2 [Hnzp1 [Hnzp2 H0]]]].
      rewrite -> q_nq_reduce_sub in H0.
      unfold q_sub, q_neg, q_add, q_eq in H0.
      simpl in H0.
      rewrite -> z_mult_ident_r in H0.
      unfold z_sub, z_neg, z_mult, z_eq in H0.
      simpl in H0.
      do 2 rewrite -> add_0_r in H0.
      do 2 rewrite -> mult_0_r in H0.
      rewrite -> add_0_r in H0.
      rewrite -> add_0_l in H0.
      rewrite -> mult_dist_over_add_r in H0.
      rewrite -> add_comm in H0.
      rewrite -> add_assoc in H0.
      rewrite -> (add_comm p2 (a * p2)) in H0.
      do 2 rewrite <- add_assoc in H0.
      rewrite -> add_cancel_2 in H0.
      symmetry in H0.
      apply zero_sum_zero_parts in H0.
      destruct H0 as [H0l H0r].
      specialize (z_nz_inject p2 0) as H1.
      destruct H1 as [_ H1].
      specialize (H1 H0l).
      specialize (Hnzp2 H1).
      contradiction.
    }
  }
  {
    intros H0.
    destruct (q_ord_trichotomy_3 (NQ#a) (NQ#b)) as [Heq | [Hgt | Hlt]].
    {
      rewrite -> q_nq_inject in Heq.
      rewrite -> Heq in H0.
      apply gt_same_is_false in H0.
      contradiction.
    }
    {
      exact Hgt.
    }
    {
      apply gt_as_ge_succ in H0.
      destruct H0 as [p0 [Hp0 _]].
      rewrite -> Hp0 in Hlt.
      unfold q_gt in Hlt.
      apply q_is_pos_as_pos_no_succ in Hlt.
      unfold q_is_pos_no_succ in Hlt.
      destruct Hlt as [p1 [p2 [Hnzp1 [Hnzp2 Hlt]]]].
      rewrite -> q_nq_reduce_sub in Hlt.
      unfold q_sub, q_neg, q_add, q_eq in Hlt.
      simpl in Hlt.
      rewrite -> z_mult_ident_r in Hlt.
      unfold z_sub, z_neg, z_mult, z_eq in Hlt.
      simpl in Hlt.
      do 2 rewrite -> add_0_r in Hlt.
      do 2 rewrite -> mult_0_r in Hlt.
      rewrite -> add_0_r in Hlt.
      rewrite -> add_0_l in Hlt.
      rewrite -> mult_dist_over_add_r in Hlt.
      rewrite -> add_comm in Hlt.
      rewrite -> add_assoc in Hlt.
      rewrite -> (add_comm p2 (b * p2)) in Hlt.
      do 2 rewrite <- add_assoc in Hlt.
      rewrite -> add_cancel_2 in Hlt.
      symmetry in Hlt.
      apply zero_sum_zero_parts in Hlt.
      destruct Hlt as [Hltl Hltr].
      specialize (z_nz_inject p2 0) as H1.
      destruct H1 as [_ H1].
      specialize (H1 Hltl).
      specialize (Hnzp2 H1).
      contradiction.
    }
  }
Qed.

Proposition q_ord_is_add_invariant_l : forall (a b c : Q),
   ((b > c) <-> (a + b) > (a + c))%Q.
Proof.
  intros a b c.
  assert (Hrw: a + b - (a + c) ~= b - c).
  {
    unfold q_sub.
    rewrite -> q_neg_dist_over_add.
    rewrite -> q_add_assoc.
    rewrite -> q_add_assoc_middle.
    rewrite -> (q_add_comm b (-- a)).
    rewrite <- q_add_assoc_middle.
    rewrite <- q_add_assoc.
    rewrite -> q_additive_inverse_r.
    rewrite -> q_add_0_l.
    reflexivity.
  }
  split.
  {
    intros H0.
    unfold q_gt in *.
    apply (q_is_pos_rewrite _ _ Hrw).
    exact H0.
  }
  {
    intros H0.
    unfold q_gt in *.
    apply (q_is_pos_rewrite _ _ Hrw).
    exact H0.
  }
Qed.

Proposition q_ord_is_add_invariant_r : forall (a b c : Q),
   ((a > b) <-> (a + c) > (b + c))%Q.
Proof.
  intros a b c.
  split.
  {
    intros H0.
    specialize (q_add_comm a c) as Hrw1.
    specialize (q_add_comm b c) as Hrw2.
    apply (q_ord_lhs_rewrite _ _ _ Hrw1).
    apply (q_ord_rhs_rewrite _ _ _ Hrw2).
    apply -> q_ord_is_add_invariant_l.
    exact H0.
  }
  {
    intros H0.
    apply <- (q_ord_is_add_invariant_l c).
    specialize (q_add_comm c a) as Hrw1.
    specialize (q_add_comm c b) as Hrw2.
    apply (q_ord_lhs_rewrite _ _ _ Hrw1).
    apply (q_ord_rhs_rewrite _ _ _ Hrw2).
    exact H0.
  }
Qed.

Proposition q_normal_form_a_pos_implies_pos : forall (a b : nat) 
  (Hnza : ((NZ#a) ~= (NZ#0))%Z -> False) (Hnzb : ((NZ#b) ~= (NZ#0))%Z -> False),
  (q_is_pos {| num := (NZ#a); den := (Z_nz_ex (NZ#b) Hnzb) |}).
Proof.
  intros a b Hnza Hnzb.
  apply q_is_pos_as_pos_no_succ.
  unfold q_is_pos_no_succ.
  exists (a).
  exists (b).
  exists (Hnza).
  exists (Hnzb).
  unfold q_eq.
  simpl.
  unfold z_mult, z_eq.
  simpl.
  do 2 rewrite -> add_0_r.
  rewrite -> mult_0_r.
  rewrite -> add_0_r.
  reflexivity.
Qed.

Proposition q_nq_pos_implies_q_is_pos : forall (a : nat) 
  (Hnza : ((NZ#a) ~= (NZ#0))%Z -> False), (q_is_pos (NQ# a)).
Proof.
  intros a Hnza.
  apply q_is_pos_as_pos_no_succ.
  unfold q_is_pos_no_succ.
  exists (a).
  exists (1).
  exists (Hnza).
  exists ((proj2_sig z_nz_1)).
  unfold q_eq.
  simpl.
  reflexivity.
Qed.
  

Proposition q_normal_form_ge_0 : forall (a b : nat) (Hnzb : ((NZ#b) ~= (NZ#0))%Z -> False),
  ({| num := (NZ#a); den := (Z_nz_ex (NZ#b) Hnzb) |} >= (NQ#0))%Q.
Proof.
  intros a b Hnzb.
  unfold q_ge.
  destruct a as [| a'].
  {
    right.
    apply q_num_0_is_eqv_0_1.
  }
  {
    left.
    unfold q_gt.
    apply (q_is_pos_rewrite _ _ (q_reduce_sub_0 ((NZ# S a') /Q Z_nz_ex (NZ# b) Hnzb))).
    specialize (z_pos_ne_0 a') as Hpa'.
    apply q_normal_form_a_pos_implies_pos.
    exact Hpa'.
  }
Qed.

Proposition q_ord_is_pos_mult_invariant_l : forall (a b c : Q) 
  (Hpa : q_is_pos a), ((b > c) <-> (a * b) > (a * c))%Q.
Proof.
  intros a b c Hpa.
  split.
  {
      intros H0.
      unfold q_gt in H0.
      apply q_is_pos_as_pos_no_succ in H0.
      destruct H0 as [p0 [p1 [Hnzp0 [Hnzp1 H0]]]].
      unfold q_gt.
      apply q_is_pos_as_pos_no_succ.
      unfold q_is_pos_no_succ.
      apply q_is_pos_as_pos_no_succ in Hpa.
      destruct Hpa as [p2 [p3 [Hnzp2 [Hnzp3 Hgta]]]].
      specialize ((proj1 (z_mult_preserves_ne_z_1 p2 p0)) (conj Hnzp2 Hnzp0)) as Hnzp2p0.
      specialize ((proj1 (z_mult_preserves_ne_z_1 p3 p1)) (conj Hnzp3 Hnzp1)) as Hnzp3p1.
      exists ((p2 * p0)%nat).
      exists ((p3 * p1)%nat).
      exists (Hnzp2p0).
      exists (Hnzp3p1).
      unfold q_sub.
      rewrite <- q_neg_extract_from_mult_r.
      rewrite <- q_mult_dist_over_add_l.
      rewrite -> q_sub_refold.
      rewrite -> H0.
      rewrite -> Hgta.
      rewrite -> (q_z_mult_reduce_2 _ _ _ _ _ _ Hnzp3p1).
      reflexivity.
  }
  {
    intros H0.
    unfold q_gt in H0.
    apply q_is_pos_as_pos_no_succ in H0.
    destruct H0 as [p0 [p1 [Hnzp0 [Hnzp1 H0]]]].
    apply q_is_pos_as_pos_no_succ in Hpa.
    destruct Hpa as [p2 [p3 [Hnzp2 [Hnzp3 Hgta]]]].
    unfold q_sub in H0.
    rewrite <- q_neg_extract_from_mult_r in H0.
    rewrite <- q_mult_dist_over_add_l in H0.
    rewrite -> q_sub_refold in H0.
    apply <- (q_mult_cancel_l (a * (b - c)) 
       ((NZ# p0) /Q Z_nz_ex (NZ# p1) Hnzp1)
       {| num := (NZ#p3); den := (Z_nz_ex (NZ#p2) Hnzp2) |}) in H0.
    2: exact Hnzp3.
    rewrite -> Hgta in H0.
    rewrite <- q_mult_assoc in H0.
    rewrite -> q_norm_multiplicative_inverse in H0.
    rewrite -> q_mult_ident_l in H0.
    specialize ((proj1 (z_mult_preserves_ne_z_1 p2 p1)) (conj Hnzp2 Hnzp1)) as Hnzp2p1.
    rewrite -> (q_z_mult_reduce_2 p3 p2 p0 p1 Hnzp2 Hnzp1 Hnzp2p1) in H0.
    unfold q_gt.
    specialize ((proj1 (z_mult_preserves_ne_z_1 p3 p0)) (conj Hnzp3 Hnzp0)) as Hnzp3p0.
    specialize (q_normal_form_a_pos_implies_pos (p3 * p0) (p2 * p1) Hnzp3p0 Hnzp2p1) as H1.
    apply (q_is_pos_rewrite _ _ H0).
    exact H1.
  }
Qed.

Proposition q_ord_is_pos_mult_invariant_r : forall (a b c : Q) 
  (Hpc : q_is_pos c), ((a > b) <-> (a * c) > (b * c))%Q.
Proof.
  intros a b c Hpc.
  split.
  {
    intros H0.
    apply (q_ord_lhs_rewrite (a * c) (c * a) _ (q_mult_comm a c)).
    apply (q_ord_rhs_rewrite _ (b * c) (c * b) (q_mult_comm b c)).
    apply -> q_ord_is_pos_mult_invariant_l.
    1: exact H0. 1: exact Hpc.
  }
  {
    intros H0.
    specialize (proj1 (q_ord_lhs_rewrite (a * c) (c * a) (b * c) (q_mult_comm a c))) as Hrw;
    apply Hrw in H0; clear Hrw.
    specialize (proj1 (q_ord_rhs_rewrite (c * a) (b * c) (c * b) (q_mult_comm b c))) as Hrw;
    apply Hrw in H0; clear Hrw.
    specialize (proj2 (q_ord_is_pos_mult_invariant_l c a b Hpc) H0) as H1.
    exact H1.
  }
Qed.

Proposition q_ge_is_add_invariant_l : forall (a b c : Q),
   ((b >= c) <-> (a + b) >= (a + c))%Q.
Proof.
  intros a b c.
  split.
  {
    intros H0.
    unfold q_ge in *.
    destruct H0 as [H0l | H0r].
    {
      left.
      apply -> (q_ord_is_add_invariant_l a) in H0l.
      exact H0l.
    }
    {
      right.
      apply q_add_cancel_l.
      exact H0r.
    }
  }
  {
    intros H0.
    unfold q_ge in *.
    destruct H0 as [H0l | H0r].
    {
      left.
      apply <- (q_ord_is_add_invariant_l a) in H0l.
      exact H0l.
    }
    {
      right.
      apply q_add_cancel_l in H0r.
      exact H0r.
    }
  }
Qed.

Proposition q_ge_is_add_invariant_r : forall (a b c : Q),
   ((a >= b) <-> (a + c) >= (b + c))%Q.
Proof.
  intros a b c.
  split.
  {
    intros H0.
    specialize (q_add_comm a c) as Hrw1.
    specialize (q_add_comm b c) as Hrw2.
    apply (q_ge_lhs_rewrite _ _ _ Hrw1).
    apply (q_ge_rhs_rewrite _ _ _ Hrw2).
    apply -> q_ge_is_add_invariant_l.
    exact H0.
  }
  {
    intros H0.
    apply <- (q_ge_is_add_invariant_l c).
    specialize (q_add_comm c a) as Hrw1.
    specialize (q_add_comm c b) as Hrw2.
    apply (q_ge_lhs_rewrite _ _ _ Hrw1).
    apply (q_ge_rhs_rewrite _ _ _ Hrw2).
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
  apply -> q_ord_rev in H0.
  apply <- q_ord_rev.
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

(*\begin{Q extra last}*)

Definition Q_pos := { a : Q | (q_is_pos a) }.

Proposition q_is_pos_preserves_pos_add : forall (a b : Q),
  (q_is_pos a) -> (q_is_pos b) -> (q_is_pos (a + b)).
Proof.
  intros a b Hpa Hpb.
  apply q_is_pos_as_pos_no_succ in Hpa, Hpb.
  apply q_is_pos_as_pos_no_succ.
  destruct Hpa as [p0 [q0 [Hnz_p0 [Hnz_q0 Hnew_p0q0]]]].
  destruct Hpb as [p1 [q1 [Hnz_p1 [Hnz_q1 Hnew_p1q1]]]].
  unfold q_is_pos_no_succ.
  specialize (proj1 (z_mult_preserves_ne_z_1 q0 q1) (conj Hnz_q0 Hnz_q1)) as Hnz_q0q1.
  specialize (proj1 (z_mult_preserves_ne_z_1 p0 q1) (conj Hnz_p0 Hnz_q1)) as Hnz_p0q1.
  specialize (proj1 (z_mult_preserves_ne_z_1 p1 q0) (conj Hnz_p1 Hnz_q0)) as Hnz_p1q0.
  specialize (z_non_neg_add_preserves_ne (p0 * q1) (p1 * q0) Hnz_p0q1 Hnz_p1q0 ) as Hnz_sum.
  exists ((p0*q1 + p1*q0)%nat).
  exists ((q0*q1)%nat).
  exists (Hnz_sum).
  exists (Hnz_q0q1).
  rewrite -> Hnew_p0q0.
  rewrite -> Hnew_p1q1.
  rewrite -> (q_nz_reduce_frac_add _ _ _ _ _ _ Hnz_q0q1).
  assert (Hrw : (p0 * q1 + q0 * p1 = p0 * q1 + p1 * q0)%nat).
  {
    rewrite -> (mult_comm q0 p1).
    reflexivity.
  }
  apply (q_num_rewrite _ _ _ _ (proj2 (z_nz_inject _ _) Hrw)); clear Hrw.
Qed.

Proposition q_ord_add_two_joined_inequalities : forall (a b c : Q),
  (a > b)%Q -> (c > a)%Q -> (c > b)%Q.
Proof.
  intros a b c H0 H1.
  unfold q_gt in *.
  specialize (q_is_pos_preserves_pos_add (a - b) (c - a) H0 H1) as H2.
  assert (Hrw : ((a - b + (c - a)) ~= (c - b))%Q).
  {
    unfold q_sub.
    rewrite -> q_add_comm.
    rewrite -> q_add_assoc.
    rewrite -> q_add_assoc_middle.
    rewrite -> q_additive_inverse_l.
    rewrite -> q_add_0_r.
    reflexivity.
  }
  apply -> (q_is_pos_rewrite _ _ Hrw) in H2; clear Hrw.
  exact H2.
  (*
    {(a > b) -> (c > a) -> ?} <->
    {(a - b > 0) -> (c - a > 0) -> (a - b + c - a > 0)} <->
    {(a - b > 0) -> (c - a > 0) -> (c - b > 0)} <->
    {(a > b) -> (c > a) -> (c > b)}.

    {(a > b) -> (c > a) -> (a+c > a+b)} <->
    {(a > b) -> (c > a) -> (c > b)}.
  *)
Qed.

Proposition q_mult_dist_add_over_add : forall (a b c d : Q),
  ((a + b) * (c + d) ~= a*c + a*d + b*c + b*d)%Q.
Proof.
  intros a b c d.
  rewrite -> q_mult_dist_over_add_l.
  do 2 rewrite -> q_mult_dist_over_add_r.
  repeat rewrite -> q_add_assoc.
  rewrite -> q_add_cancel_l.
  repeat rewrite <- q_add_assoc.
  rewrite -> q_add_cancel_r.
  rewrite -> q_add_comm.
  reflexivity.
Qed.


(*\end{Q extra last}*)

(*\begin{Q abs and epsilon}*)

Definition q_abs (a : Q) : Q :=
  {| 
    num := (z_abs (num a));
    den := (Z_nz_ex (z_abs (proj1_sig (den a))) (z_abs_preserves_ne_z _ (proj2_sig (den a))))
  |}.


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

(*\end{Q abs and epsilon}*)

(*\begin{Q exp}*)

Fixpoint q_pexp (a : Q) (n : nat) : Q :=
  match n with
  | 0 => (NQ#1)
  | (S n') => (q_mult a (q_pexp a n'))
  end.

Notation "x ** y" := (q_pexp x y) (at level 45) : Q_scope.

Definition q_nexp (a : Q) (Hnza : (num(a) ~= (NZ#0))%Z -> False) (n : nat) : Q :=
  (q_pexp (q_recip a Hnza) n).

Proposition q_pexp_power_0 : forall (a : Q), ((a ** 0) ~= (NQ#1))%Q.
Proof.
  intros a.
  simpl.
  reflexivity.
Qed.

Proposition q_pexp_power_succ_l : forall (a : Q) (b : nat), ((a ** (S b)) ~= (a * (a ** b)))%Q.
Proof.
  intros a b.
  simpl.
  reflexivity.
Qed.

Proposition q_pexp_power_succ_r : forall (a : Q) (b : nat), ((a ** (S b)) ~= ((a ** b) * a))%Q.
Proof.
  intros a b.
  simpl.
  rewrite -> q_mult_comm.
  reflexivity.
Qed.

Proposition q_pexp_base_rewrite : forall (b b' : Q) (p : nat), 
  (b ~= b')%Q -> (b ** p ~= b' ** p)%Q.
Proof.
  intros b b' p Heq.
  induction p as [| p' IHp'].
  {
    unfold q_pexp.
    reflexivity.
  }
  {
    do 2 rewrite -> q_pexp_power_succ_l.
    rewrite -> IHp'.
    rewrite -> Heq.
    reflexivity.
  }
Qed.

Proposition q_pexp_power_even_reduce_neg : forall (a : Q) (b : nat),
  ((-- a) ** (2*b)) ~= (a ** (2*b)).
Proof.
  intros a b.
  induction b as [| b'].
  {
    rewrite -> mult_0_r.
    do 2 rewrite -> q_pexp_power_0.
    reflexivity.
  }
  {
    rewrite -> mult_Sa_b.
    rewrite -> add_Sn_m.
    do 2 rewrite -> q_pexp_power_succ_l.
    rewrite -> mult_ident.
    rewrite <- add_n_Sm.
    do 2 rewrite -> q_pexp_power_succ_l.
    rewrite <- nat_double_is_same_add_l.
    rewrite -> IHb'.
    rewrite <- q_mult_assoc.
    rewrite -> q_neg_extract_from_mult_r.
    do 3 rewrite -> q_neg_extract_from_mult_l.
    rewrite -> q_neg_reduce_double.
    rewrite -> q_mult_assoc.
    reflexivity.
  }
Qed.

Proposition q_square_dist_over_add : forall (a b : Q),
  ((a + b)%Q ** 2 ~= a**2 + (NQ#2)*a*b + b**2)%Q.
Proof.
  intros a b.
  unfold q_pexp.
  do 3 rewrite -> q_mult_ident_r.
  rewrite -> q_mult_dist_add_over_add.
  rewrite -> q_add_cancel_r.
  repeat rewrite -> q_add_assoc.
  rewrite -> q_add_cancel_l.
  rewrite -> (q_mult_comm b a).
  rewrite <- q_double_is_same_add.
  rewrite -> q_mult_comm.
  rewrite -> q_mult_assoc.
  reflexivity.
Qed.


(*\end{Q exp}*)

(*\begin{Q interspersing}*)

Proposition q_in_euclid_div_form : forall 
    (a b : nat) (Hnzb : ((NZ# b) ~= (NZ#0))%Z -> False), 
  exists k l : nat, ({| num := (NZ#a); den := (Z_nz_ex (NZ#b) Hnzb) |} ~= (NQ#k) + 
  {| num := (NZ#l); den := (Z_nz_ex (NZ#b) Hnzb) |}) /\ (b > l)%nat.
Proof.
  intros a b Hnzb.
  destruct b as [| b'].
  {
    exfalso.
    apply Hnzb.
    reflexivity.
  }
  {
    specialize (nat_euclid_div a b') as H0.
    destruct H0 as [k [l [Hmod Hdiv]]].
    exists (k).
    exists (l).
    split.
    {
      unfold q_add.
      unfold q_eq.
      simpl.
      do 2 rewrite -> z_mult_ident_l.
      do 2 rewrite -> z_mult_reduce_non_neg.
      rewrite -> z_add_reduce_non_neg.
      rewrite -> z_mult_reduce_non_neg.
      rewrite -> z_nz_inject.
      apply mult_cancel_r.
      left.
      exact Hdiv.
    }
    {
      exact Hmod.
    }
  }
Qed.

Proposition q_normal_form_sign_dichotomy : forall (q : Q), exists (a b : nat)
  (Hnzb : ((NZ#b) ~= (NZ#0))%Z -> False), 
  (q ~= {| num := (NZ#a); den := (Z_nz_ex (NZ#b) Hnzb) |}) \/ 
  (q ~= (-- {| num := (NZ#a); den := (Z_nz_ex (NZ#b) Hnzb) |})).
Proof.
  intros [z1 [z2 Hnzz2]].
  destruct (z_normal_form_sign_dichotomy z1) as [a [Hnnz1 | Hnz1]].
  {
    destruct (z_normal_form_sign_dichotomy z2) as [b [Hnnz2 | Hnz2]].
    {
      specialize (z_normal_form_preserves_nz_pos z2 b Hnnz2 Hnzz2) as Hnzb.
      exists (a).
      exists (b).
      exists (Hnzb).
      left.
      specialize (q_num_rewrite z1 (NZ#a) z2 Hnzz2 Hnnz1) as Hrw.
      rewrite -> Hrw.
      clear Hrw.
      specialize (q_den_rewrite (NZ#a) z2 (NZ#b) Hnzz2 Hnzb Hnnz2) as Hrw.
      rewrite -> Hrw.
      clear Hrw.
      reflexivity.
    }
    {
      specialize (z_normal_form_preserves_nz_neg z2 b Hnz2 Hnzz2) as Hnzb.
      exists (a).
      exists (b).
      exists (Hnzb).
      right.
      specialize (q_num_rewrite z1 (NZ#a) z2 Hnzz2 Hnnz1) as Hrw.
      rewrite -> Hrw.
      clear Hrw.
      specialize (z_sign_preserves_nz b) as Hnzb'.
      destruct Hnzb' as [Hnzb' _].
      specialize (Hnzb' Hnzb).
      specialize (q_den_rewrite (NZ#a) z2 (-- (NZ#b)) Hnzz2 Hnzb' Hnz2) as Hrw.
      rewrite -> Hrw.
      clear Hrw.
      rewrite -> (q_neg_den_extract _ _ Hnzb _).
      reflexivity.
    }
  }
  {
    destruct (z_normal_form_sign_dichotomy z2) as [b [Hnnz2 | Hnz2]].
    {
      specialize (z_normal_form_preserves_nz_pos z2 b Hnnz2 Hnzz2) as Hnzb.
      exists (a).
      exists (b).
      exists (Hnzb).
      right.
      specialize (q_num_rewrite z1 (-- NZ#a) z2 Hnzz2 Hnz1) as Hrw.
      rewrite -> Hrw.
      clear Hrw.
      specialize (q_den_rewrite (-- NZ#a) z2 (NZ#b) Hnzz2 Hnzb Hnnz2) as Hrw.
      rewrite -> Hrw.
      clear Hrw.
      reflexivity.
    }
    {
      specialize (z_normal_form_preserves_nz_neg z2 b Hnz2 Hnzz2) as Hnzb.
      exists (a).
      exists (b).
      exists (Hnzb).
      left.
      specialize (q_num_rewrite z1 (-- NZ#a) z2 Hnzz2 Hnz1) as Hrw.
      rewrite -> Hrw.
      clear Hrw.
      specialize (z_sign_preserves_nz b) as Hnzb'.
      destruct Hnzb' as [Hnzb' _].
      specialize (Hnzb' Hnzb).
      specialize (q_den_rewrite (-- NZ#a) z2 (-- NZ#b) Hnzz2 Hnzb' Hnz2) as Hrw.
      rewrite -> Hrw.
      clear Hrw.
      rewrite -> (q_neg_den_extract _ _ Hnzb _).
      rewrite -> q_neg_num_extract.
      rewrite -> q_neg_reduce_double.
      reflexivity.
    }
  }
Qed.

Proposition q_1_sub_fraction_is_pos : forall (a b : nat) (Hnzb : ((NZ#b) ~= (NZ#0))%Z -> False),
  (b > a)%nat -> (q_is_pos ((NQ#1) - {| num := (NZ#a); den := (Z_nz_ex (NZ#b) Hnzb) |})).
Proof.
  intros a b Hnzb Hfrac.
  assert (Hrw : (NQ# 1) - ((NZ# a) /Q Z_nz_ex (NZ# b) Hnzb) ~=
                (((NZ# b) - (NZ#a)) /Q Z_nz_ex (NZ# b) Hnzb)).
  {
    unfold q_sub.
    rewrite -> (q_nq_1_is_same_num_den b Hnzb).
    rewrite -> q_sub_refold.
    rewrite -> q_div_reduce_sub_formal_same_den_2.
    reflexivity.
  }
  apply (q_is_pos_rewrite _ _ Hrw).
  apply q_is_pos_as_pos_no_succ.
  apply gt_as_ge_succ in Hfrac.
  destruct Hfrac as [p0 [Hp0 _]].
  unfold q_is_pos_no_succ.
  rewrite -> add_swap_s in Hp0.
  specialize (z_pos_ne_0 p0) as Hnzp0.
  exists (S p0).
  exists (b).
  exists (Hnzp0).
  exists (Hnzb).
  unfold q_sub, q_neg, q_add, q_eq.
  simpl.
  unfold z_sub, z_neg, z_add, z_mult, z_eq.
  simpl.
  do 3 rewrite -> add_0_r.
  do 3 rewrite -> mult_0_r.
  do 2 rewrite -> add_0_r.
  rewrite -> add_0_l.
  rewrite <- add_assoc.
  rewrite <- mult_dist_over_add_r.
  rewrite <- mult_Sa_b.
  rewrite -> mult_cancel_r.
  left.
  rewrite -> Hp0.
  rewrite <- add_Sn_m.
  rewrite -> add_comm.
  reflexivity.
Qed.

Proposition q_floor_pos : forall (a : Q),
  (q_is_pos a) -> exists k : nat, ((a >= (NQ#k) /\ (NQ#k + 1) > a)).
Proof.
  intros q H0.
  apply q_is_pos_as_pos_no_succ in H0.
  unfold q_is_pos_no_succ in H0.
  destruct H0 as [p0 [p1 [Hnzp0 [Hnzp1 H0]]]].
  specialize (q_in_euclid_div_form p0 p1 Hnzp1) as Hdiv.
  destruct Hdiv as [k [l [Hdiv Hmod]]].
  exists (k).
  split.
  {
    apply (q_ge_lhs_rewrite _ _ _ H0).
    apply (q_ge_lhs_rewrite _ _ _ Hdiv).
    specialize (q_add_0_r (NQ#k)) as Hrw.
    symmetry in Hrw.
    apply (q_ge_rhs_rewrite _ _ _ Hrw); clear Hrw.
    specialize (q_ge_is_add_invariant_l 
      (NQ#k) (((NZ# l) /Q Z_nz_ex (NZ# p1) Hnzp1)) (NQ#0)) as Hrw.
    destruct Hrw as [Hrw _].
    apply Hrw.
    apply q_normal_form_ge_0.
  }
  {
    apply (q_ord_rhs_rewrite _ _ _ H0).
    apply (q_ord_rhs_rewrite _ _ _ Hdiv).
    specialize (q_nq_reduce_add k 1) as Hrw.
    symmetry in Hrw.
    apply (q_ord_lhs_rewrite _ _ _ Hrw); clear Hrw.
    specialize (q_ord_is_add_invariant_l
      (NQ#k) (NQ#1) (((NZ# l) /Q Z_nz_ex (NZ# p1) Hnzp1))
    ) as Hrw.
    destruct Hrw as [Hrw _].
    apply Hrw.
    unfold q_gt.
    apply q_1_sub_fraction_is_pos.
    exact Hmod.
  }
Qed.

Proposition q_floor_in_z : forall (a : Q),
  exists k : Z, ((a >= (ZQ#k) /\ (ZQ#k + (NZ#1)) > a)).
Proof.
  intros q.
  destruct (q_trichotomy_3 q) as [Heqq | [Hpq | Hnq]].
  {
    exists ((NZ#0)).
    split.
    {
      apply (q_ge_lhs_rewrite _ _ _ Heqq).
      apply q_ge_refl.
    }
    {
      apply (q_ord_rhs_rewrite _ _ _ Heqq).
      specialize (z_nz_reduce_add 0 1) as Hrw.
      apply zq_inject in Hrw.
      simpl in Hrw.
      apply (q_ord_lhs_rewrite _ _ _ Hrw).
      apply <- q_ord_nq_inject.
      apply gt_succ_l_0_r.
    }
  }
  2:
  {
    destruct Hnq as [q1 [Hpq1 Hnq]].
    specialize (q_floor_pos q1 Hpq1) as H0.
    destruct H0 as [k1 [Hfl0 Hfl1]].
    destruct Hfl0 as [Hfl0l | Hfl0r].
    {
      exists (((-- NZ#(k1)) - (NZ#1))%Z).
      split.
      {
        apply (q_ge_lhs_rewrite _ _ _ Hnq).
        specialize (z_neg_extract_from_sub_neg_l k1 1) as Hrw.
        apply zq_inject in Hrw.
        apply (q_ge_rhs_rewrite _ _ _ Hrw); clear Hrw.
        apply (q_ge_rhs_rewrite _ _ _ (q_neg_reduce_zq (NZ# k1 + 1))).
        apply -> q_ge_rev.
        unfold q_ge.
        left.
        exact Hfl1.
      }
      {
        apply (q_ord_rhs_rewrite _ _ _ Hnq).
        assert (Hrw : ((-- (NZ# k1) - (NZ# 1) + (NZ# 1)) ~= 
                      (-- (NZ# k1)))%Z).
        {
          unfold z_sub.
          rewrite -> z_add_assoc.
          rewrite -> z_additive_inverse_l.
          rewrite -> z_add_0_r.
          reflexivity.
        }
        apply zq_inject in Hrw.
        apply (q_ord_lhs_rewrite _ _ _ Hrw); clear Hrw.
        apply (q_ord_lhs_rewrite _ _ _  (q_neg_reduce_zq (NZ#k1))).
        apply -> q_ord_rev.
        exact Hfl0l.
      }
    }
    {
      exists ((-- NZ#(k1))%Z).
      split.
      {
        apply (q_ge_lhs_rewrite _ _ _ Hnq).
        apply (q_ge_rhs_rewrite _ _ _ (q_neg_reduce_zq (NZ# k1))).
        apply -> q_ge_rev.
        unfold q_ge.
        right.
        exact (q_eq_sym _ _ Hfl0r).
      }
      {
        apply (q_ord_rhs_rewrite _ _ _ Hnq).
        specialize (q_neg_both_sides q1 (NQ#k1)) as [Hrw _].
        specialize (Hrw Hfl0r).
        apply (q_ord_rhs_rewrite _ _ _ Hrw); clear Hrw.
        apply (q_ord_lhs_rewrite _ _ _ (q_zq_reduce_add_neg_l k1 1)).
        apply (q_ord_rhs_rewrite _ _ _ (q_eq_sym _ _ (q_add_0_r (-- (NQ#k1))))).
        specialize (q_ord_is_add_invariant_l (-- (NQ#k1)) (NQ#1) (NQ#0)) as [Hrw _].
        apply Hrw; clear Hrw.
        apply q_ord_nq_inject.
        apply gt_succ_l_0_r.
      }
    }
  }
  {
    specialize (q_floor_pos q Hpq) as [k [Hfl0 Hfl1]].
    exists (NZ#k).
    split.
    {
      exact Hfl0.
    }
    {
      exact Hfl1.
    }
  }
Qed.

Proposition q_ord_pair_has_midpoint : forall (a b : Q) (Hgtba : (b > a)),
  exists k : Q, ((k > a) /\ (b > k)).
Proof.
  intros a b Hgtba.
  specialize (z_pos_ne_0 1) as Hnz2.
  specialize (q_nz_from_q (NQ#2) Hnz2) as nq_2.
  specialize (q_nq_pos_implies_q_is_pos 2 Hnz2) as Hp2.
  assert (Hrw : (a + b) * ((NZ# 1) /Q Z_nz_ex (NZ# 2) Hnz2) * (NQ# 2) ~=
                (a + b)).
  {
    rewrite -> q_mult_assoc.
    rewrite -> q_nq_multiplicative_inverse_r.
    rewrite -> q_mult_ident_r.
    reflexivity.
  }
  exists ((a + b) * {| num := (NZ#1); den := (Z_nz_ex (NZ#2) Hnz2) |}).
  split.
  {
    apply <- (q_ord_is_pos_mult_invariant_r 
      ((a + b) * ((NZ# 1) /Q Z_nz_ex (NZ# 2) Hnz2)) a (NQ#2)).
    2: exact Hp2.
    apply (q_ord_lhs_rewrite _ _ _ Hrw); clear Hrw.
    apply (q_ord_rhs_rewrite _ _ _ (q_double_is_same_add a)).
    apply -> q_ord_is_add_invariant_l.
    exact Hgtba.
  }
  {
    apply <- (q_ord_is_pos_mult_invariant_r 
      b ((a + b) * ((NZ# 1) /Q Z_nz_ex (NZ# 2) Hnz2)) (NQ#2)).
    2: exact Hp2.
    apply (q_ord_rhs_rewrite _ _ _ Hrw); clear Hrw.
    apply (q_ord_lhs_rewrite _ _ _ (q_double_is_same_add b)).
    apply -> q_ord_is_add_invariant_r.
    exact Hgtba.
  }
Qed.

Definition q_seq_inf_descent (f : nat -> Q) := forall (n : nat),
  (f n) > (f (S n)).

Proposition q_pos_no_sqrt_2 : forall (a : Q), 
  (q_is_pos a) -> ((a ** 2) ~= (NQ#2))%Q -> False.
Proof.
  intros a Hpa H0.
  unfold q_pexp in H0.
  rewrite -> q_mult_ident_r in H0.
  apply q_is_pos_as_pos_no_succ in Hpa.
  unfold q_is_pos_no_succ in Hpa.
  destruct Hpa as [p0 [p1 [Hnzp0 [Hnzp1 Hpa]]]].
  rewrite -> Hpa in H0.
  specialize ((proj1 (z_mult_preserves_ne_z_1 p1 p1)) (conj Hnzp1 Hnzp1)) as Hnzp1p1.
  rewrite -> (q_z_mult_reduce_2 _ _ _ _ _ _ Hnzp1p1) in H0.
  unfold q_eq in H0; simpl in H0.
  rewrite -> z_mult_ident_r in H0.
  rewrite -> z_mult_reduce_non_neg in H0.
  rewrite -> z_nz_inject in H0.
  rewrite -> mult_assoc in H0.
  specialize (
    nat_no_square_is_double_another p0 p1 
    ((proj1 (z_nz_ne_inject p1 0)) Hnzp1) H0) as H1.
  contradiction.
Qed.

Proposition q_no_sqrt_2 : forall (a : Q), 
  ((a ** 2) ~= (NQ#2))%Q -> False.
Proof.
  intros a H0.
  destruct (q_trichotomy_3 a) as [Hza | [Hpa | Hna]].
  {
    unfold q_pexp in H0.
    rewrite -> q_mult_ident_r in H0.
    rewrite -> Hza in H0.
    rewrite -> q_mult_0_r in H0.
    rewrite -> q_nq_inject in H0.
    discriminate.
  }
  {
    apply (q_pos_no_sqrt_2 a Hpa H0).
  }
  {
    unfold q_is_neg in Hna.
    destruct Hna as [q0 [Hpq0 H1]].
    rewrite -> (q_pexp_base_rewrite _ _ _ H1) in H0.
    rewrite <- (mult_ident_r 2) in H0.
    rewrite -> q_pexp_power_even_reduce_neg in H0.
    rewrite -> (mult_ident_r 2) in H0.
    apply (q_pos_no_sqrt_2 q0 Hpq0 H0).
  }
Qed.

(*\end{Q interspersing}*)

Close Scope Q_scope.