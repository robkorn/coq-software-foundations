

Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => b2
    | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.



Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.


Infix "&&" := andb.
Infix "||" := orb.

Example test_Orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.


Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => match b2 with
            | true => false
            | false => true
            end

  | false => match b2 with
             | true => true
             | false => true
             end
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Check negb.


Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => match b2 with
            | true => match b3 with
                      | true => true
                      | false => false
                      end
            | false => false
            end
  | false => false
             
  end.


Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check test_andb34.


Module Factorial.


Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => 1
    | S i => (S i) * factorial ((S i) - 1)     
end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                      : nat_scope.

Check (0 + 3).

End Factorial.

Module blt_nat.

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

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | 0 => false
      | S m' => leb n' m'
      end
  end.

Definition blt_nat (n m : nat) : bool :=
  match beq_nat n m with
  | true => false
  | false => leb n m
end.


Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

End blt_nat.

Theorem plus_0_l : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

(* Theorem plus id example : forall (n m:nat), *)
(* n = m → *)
(* n + n = m + m. *)

Theorem plus_id_example : forall n m : nat,
    n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity.
Qed.
                    

Theorem plus_id_exercise : forall n m o : nat,
n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros hnm hmo.
  rewrite hnm.
  rewrite <- hmo.
  reflexivity.
Qed.

(* Theorem mult 0 plus : ∀ n m : nat, *)
(* (0 + n) × m = n × m. *)
(* Proof. *)
(* intros n m. *)
(* rewrite → plus O n. *)
(* reflexivity. Qed. *)


Theorem mult_0_plus : forall n m : nat,
    (0 + n) * m = n * m.
  Proof.
    intros n m.
    rewrite plus_O_n.
    reflexivity.
  Qed.

Theorem mult_S_1 : forall n m : nat,
    m = S n ->
    m * (1 + n) = m * m.
Proof.
  intros n m.
  intros hmsn.
  rewrite plus_1_l.
  rewrite hmsn.
  reflexivity.
Qed.




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

End caseanyl.


Theorem indentity_fn_aplied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x ) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f hfx b.
  rewrite hfx. rewrite hfx.
  reflexivity.
Qed.

Theorem negation_fn_aplied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x ) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f hnx b.
  rewrite hnx. rewrite hnx. 
  destruct b as [|].
  - simpl. reflexivity.
  -  simpl. reflexivity.
Qed.


Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  destruct b as [|]. destruct c as [|].
  - simpl. reflexivity.
  - simpl. intros hft. rewrite hft. reflexivity.
  - simpl. intros hfc. rewrite hfc. reflexivity.
Qed.



(* Need to think about how to implement this properly. *)
Inductive bin : Type :=
| Zip : bin
| Dos : bin -> bin
| SDos : bin -> bin.

Fixpoint incr (n : bin) : bin :=
  match n with
  | Zip => SDos Zip
  | Dos i => Dos n
  | SDos i => Dos (incr i)
end.

Fixpoint bin_to_nat (n : bin) : nat :=
  match n with
  | Zip => 0
  | Dos i => 2 * (bin_to_nat i)
  | SDos i => 2 * (bin_to_nat i) + 1
end.

Definition test_bin_incr_1 : bin_to_nat Zip = 0.
Proof. simpl. reflexivity. Qed.

Definition test_bin_incr_2 : bin_to_nat (incr Zip) = 1.
Proof. simpl. reflexivity. Qed.

Definition test_bin_incr_3 : bin_to_nat (incr (incr Zip)) = 2.
Proof. simpl. reflexivity. Qed.

Definition test_bin_incr_4 : bin_to_nat (incr (incr Zip)) = S ( S (bin_to_nat Zip)).
Proof. simpl. reflexivity. Qed.

Definition test_bin_incr_5 : bin_to_nat (incr (incr (incr ( SDos Zip)))) = 8.
Proof. simpl. reflexivity. Qed.