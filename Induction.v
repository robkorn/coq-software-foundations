
Require Export Basics.

Theorem plus_n_O : forall n : nat,
  n = n + 0.
Proof.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity. Qed.


Theorem plus_n_Sm : forall n m : nat,
S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity. Qed.


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [|n' IHn'].
  - induction m as [|m' IHm'].
    + reflexivity.
    + simpl. rewrite <- IHm'. simpl. reflexivity.
  - induction m as [|m' IHm'].
    + simpl. rewrite IHn'. simpl. reflexivity.
    + simpl. rewrite IHn'. simpl. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity. Qed.

Fixpoint double (n:nat) :=
match n with
| O => O
| S n' => S (S (double n' ))
end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity. Qed.


(* Fixpoint evenb (n:nat) : bool := *)
(*   match n with *)
(*     | O => true *)
(*     | S O => false *)
(*     | S (S m) => evenb m *)
(*   end. *)

(* Theorem evenb_S : forall n : nat, *)
(*   evenb (S n) = negb (evenb n). *)
(* Proof. *)
(*   induction n as [|n' IHn']. *)
(*   - simpl. reflexivity. *)
(*   - induction n' as [| n'']. *)

