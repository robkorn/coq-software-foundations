
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


Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H : n + m = m + n).
    { rewrite -> plus_comm. reflexivity. }
    rewrite -> H. reflexivity. Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite plus_assoc.
  assert (H : n + m = m + n).
         { rewrite plus_comm. reflexivity. }
         rewrite H. rewrite plus_assoc. reflexivity. Qed.


Theorem mult_Sm_n : forall m n : nat,
        S m * n = n * m + n.
Proof.
  intros m n.
  induction n as [|n' IHn'].
  - simpl. rewrite <- mult_n_O. reflexivity.
  - rewrite <- mult_n_Sm.
    rewrite <- plus_n_Sm.
    rewrite IHn'. simpl.
    rewrite <- plus_n_Sm.
    assert (H : m + (n' * m) + n' = (n' * m) + n' + m).
    { rewrite plus_comm.
      rewrite plus_assoc.
      rewrite plus_comm.
      rewrite plus_assoc.
      reflexivity. }
    rewrite H.
    reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction m as [|m' IHm'].
  - rewrite mult_0_l. rewrite mult_0_r. reflexivity.
  - rewrite <- mult_n_Sm. rewrite mult_Sm_n. reflexivity. Qed.

(* bin to nat pres incr  *)

Theorem bin_to_nat_pres_incr : forall m : bin,
    bin_to_nat (incr m) = bin_to_nat m + 1.
Proof.
  induction m as [|dm IHdm|sdm IHsdm].
  - simpl. reflexivity.
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. repeat (rewrite <- plus_n_O).
    rewrite IHsdm.
    symmetry.
    rewrite <- plus_assoc.
    rewrite <- plus_assoc.
    rewrite <- plus_assoc.
    rewrite plus_Sn_m. simpl.
    rewrite plus_n_Sm. reflexivity.
Qed.
     