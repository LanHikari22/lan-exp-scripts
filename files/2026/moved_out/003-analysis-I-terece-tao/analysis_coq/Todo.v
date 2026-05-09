Set Warnings "-notation-overridden".
Require Import CoqAnalysis.Nat.
Set Warnings "+notation-overridden".
Require Import CoqAnalysis.Z.
Require Import CoqAnalysis.Q.
Require Import CoqAnalysis.Misc.

(*\begin{Q abs and epsilon}*)


Definition proj_Q_nz_to_Q (x : Q_nz) : Q := proj1_sig x.

Definition Q_1_over_2 : Q :=
  {| num := (NZ#1); den := (Z_nz_ex (NZ#2) (z_pos_ne_0 1)) |}.

(* f(x) = 1/2 (x + 2/x) *)
Definition sqrt_2_approx_form (x : Q_nz) 
  : Q :=
  Q_1_over_2 * ((proj_Q_nz_to_Q x) + (NQ#2) * (proj_Q_nz_to_Q (x **-1))).

Proposition sqrt_2_approx_form_preserves_ne_0 : forall (x : Q_nz),
  ((num (sqrt_2_approx_form x)) ~= (NZ#0))%Z -> False.
Proof.
  intros [[a [b Hnzb]] Hnza] H0.
  simpl in Hnza.
  unfold sqrt_2_approx_form in H0.
  simpl in H0.
  do 2 rewrite -> z_mult_ident_l in H0.
  destruct (z_trichotomy_3 a) as [Hza | [Hpa | Hna]].
  {
    specialize (Hnza Hza).
    contradiction.
  }
  {
    destruct Hpa as [p0 [Hp0 _]].

  }
  {

  }
Qed.

(* a_0 = 2 | a_{Sn} = f(a_n) *)
Fixpoint sqrt_2_approx (n : nat) : Q_nz :=
  match n with
  | 0 => Q_nz_ex (NQ#2) (z_pos_ne_0 1)
  | (S n') => let x'  := sqrt_2_approx n' in
              let fx' := (sqrt_2_approx_form x') in 
              Q_nz_ex fx' (sqrt_2_approx_form_preserves_ne_0 x')
  end.

Proposition nat_2_power_a_ge_a : forall (a : nat), (2 ** a) >= a.
Proof.

Qed.

Require Import Stdlib.Classes.Morphisms.
Instance q_abs_proper : 
  Proper (q_eq ==> q_eq ) q_abs.
Proof.
  intros [p [q Hnzq]] [p' [q' Hnzq']] Heq.
  unfold q_abs, q_eq; simpl.
  unfold q_eq in Heq; simpl in Heq.
  apply z_abs_as_nat_diff
Qed.

Proposition q_abs_triangle_inequality : forall (a b : Q),
  ((q_abs a) + (q_abs b) >= (q_abs (a + b)))%Q.
Proof.
  intros [a0 [b0 Hnzb0]] [a1 [b1 Hnzb1]] .
  unfold q_abs.
  simpl.

Qed.

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
  (q_eps_close a b eps1 Hpeps1) -> 
  (q_eps_close c d eps2 Hpeps2) -> 
  (q_eps_close (a*c) (b*d) (eps1 * (q_abs c) + eps2 * (q_abs a) + eps1 * eps2) Hp1).

(*\end{Q abs and epsilon}*)

(*\begin{Q exp}*)

Proposition q_pexp_mult_as_exp_add : forall (a : Q) (n m : nat),
  (a ** n) * (a ** m) ~= (a ** (n + m)).
  
Proposition q_pexp_dist_mult_as_exp_mult : forall (a : Q) (n m : nat),
  ((a ** n) ** m) ~= (a ** (n * m)).

Proposition q_pexp_dist_over_mult : forall (a b : Q) (n : nat),
  ((a * b) ** n) ~= (a ** n) * (b ** n).

Proposition q_pexp_only_0_evals_to_0_for_pos_exp : forall (a : Q) (n : nat) 
  (Hnzn : (n > 0)%nat), ((a ** n) ~= (NQ#0)) <-> (a ~= (NQ#0)).

Proposition q_pexp_preserves_ge_ge_0 : forall (a b : Q) (n : nat),
  ((a >= b) /\ (b >= (NQ#0))) <-> (((a ** n) >= (b ** n)) /\ ((b ** n) >= (NQ#0))).

Proposition q_pexp_preserves_gt_ge_0 : forall (a b : Q) (n : nat)
  (Hnzn : (n > 0)%nat),
  ((a > b) /\ (b >= (NQ#0))) <-> (((a ** n) > (b ** n)) /\ ((b ** n) >= (NQ#0))).

Proposition q_pexp_extract_exp_from_q_abs : forall (a : Q) (n : nat),
  (q_abs (a ** n)) ~= ((q_abs a) ** n).

(*\end{Q exp}*)


(*
*)