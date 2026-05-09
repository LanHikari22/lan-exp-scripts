(* Hello World in Rocq *)

From Stdlib Require Import String.

(* A simple value *)
Definition hello : string := "Hello, Rocq!".

(* A theorem about it *)
Theorem hello_length :
  String.length hello = 12.
Proof.
  reflexivity.
Qed.

Module M.
  Inductive Nat : Set :=
    | O : Nat
    | S : Nat -> Nat.
End M.

Fixpoint myplus (n m:M.Nat) {struct n} : M.Nat :=
  match n with
  | M.O => m
  | M.S p => M.S (myplus p m)
  end.

Fixpoint nat_to_Nat (n : nat) : M.Nat :=
  match n with
  | O => M.O
  | S n' => M.S (nat_to_Nat n')
  end.

Fixpoint Nat_to_nat (n : M.Nat) : nat :=
  match n with
  | M.O => O
  | M.S n' => S (Nat_to_nat n')
  end.

Eval compute in (Nat_to_nat (myplus (nat_to_Nat 48) (nat_to_Nat 56))).