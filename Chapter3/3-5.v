

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
             | O => true
             | S i' => false
              end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
end.

Module caseanyl.
(* Theorem plus 1 neq 0 : ∀ n : nat, *)
(* beq nat (n + 1) 0 = false. *)
(* Proof. *)

Theorem plus_1_neq_0 : forall n : nat,
    beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n'].
  - reflexivity.
  - reflexivity.
  Qed.

(* Theorem negb involutive : ∀ b : bool, *)
(* negb (negb b) = b. *)
(* Proof. *)

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
Qed.


Theorem plus_1_neq_0' : forall n : nat,
    beq_nat (n + 1) 0 = false.
Proof.
  intros [|n'].
  - reflexivity.
  - reflexivity.
Qed.
   

(* Attempt #1 *)
Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
Proof.
  intros b c.
  intros hbct.
  destruct b as [|].
  - destruct c as [|].
    + reflexivity.
    + simpl andb in hbct. rewrite hbct. reflexivity.
  - destruct c as [|].
    + reflexivity.
    + simpl andb in hbct. rewrite hbct. reflexivity.
Qed.      


(* Attemp #2 To Make it cleaner, not sure if it really is cleaner afterall. *)
Theorem andb_true_elim2' : forall b c : bool,
    andb b c = true -> c = true.
Proof.
  intros b c.
  intros hbct.
  destruct b as [|]. destruct c as [|].
  - reflexivity.
  - simpl andb in hbct. rewrite hbct. reflexivity.
  - destruct c as [|].
    + reflexivity.
    + simpl andb in hbct. rewrite hbct. reflexivity.
Qed.                   
(* Theorem zero nbeq plus 1 : ∀ n : nat, *)
(* beq nat 0 (n + 1) = false. *)

Theorem zero_nbeq_plus_1 : forall n : nat,
    beq_nat 0 (n + 1) = false.
Proof.
  intros [|n'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

end caseanyl