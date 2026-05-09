(*
Set Warnings "-notation-overridden".
Require Import CoqAnalysis.Nat.
Set Warnings "+notation-overridden".
Require Import CoqAnalysis.Z.
Require Import CoqAnalysis.Q.
Require Import CoqAnalysis.Misc.

(*
Proposition nat_prime_indivisible_mult_preserves_indivisible : forall (a b p : nat)
  (Hnzp : (p = 0) -> False) (Hn1p : (p = 1) -> False) (Hpri_p : (nat_prime p Hnzp Hn1p)), 
  (nat_indivisible a p Hnzp) -> (nat_indivisible b p Hnzp) ->
  (nat_indivisible (a*b) p Hnzp).
Proof.
  intros a b p Hnzp Hn1p Hpri_p [q0 [r0 [Hmod_a Hndiv_a]]] [q1 [r1 [Hmod_b Hndiv_b]]].
  unfold nat_prime in Hpri_p.
  destruct (nat_divisibility_dichotomy (a * b) p Hnzp) as [Hdiv_ab | Hndiv_ab].
  {
    destruct Hdiv_ab as [q2 Hdiv_ab].
    specialize (mult_from_two_equations 
      a (q0 * p + (S r0)) b (q1 * p + (S r1)) Hndiv_a Hndiv_b) as H0.
    destruct a as [| a'].
    {
      rewrite mult_0_l in H0.
      rewrite -> mult_dist_add_over_add in H0.
      simpl in H0.
      rewrite -> add_comm in H0.
      discriminate.
    }
    {
      destruct b as [| b'].
      {
        rewrite mult_0_r in H0.
        rewrite -> mult_dist_add_over_add in H0.
        simpl in H0.
        rewrite -> add_comm in H0.
        discriminate.
      }
      {
        specialize (
          Hpri_p ((S a')*(S b')) (nat_mult_preserves_ne (S a') (S b') 
          (nat_succ_ne_0 a') (nat_succ_ne_0 b'))
        ) as H1.


      }
    }

    rewrite -> Hdiv_ab in H0.
    rewrite -> mult_dist_add_over_add in H0.


  }
  {

  }

  unfold nat_indivisible.


  apply q_cross_mult_from_two_equations
Qed.
*)

(*\begin{Q interspersing}*)
Proposition q_sqrt_2_approx : forall (eps : Q) (Hpeps : (q_is_pos eps)),
  exists k : Q, (q_is_pos k) -> (((NQ#2) > (k ** 2))%Q /\ (((k + eps) ** 2) > (NQ#2))%Q).
(*\end{Q interspersing}*)

*)