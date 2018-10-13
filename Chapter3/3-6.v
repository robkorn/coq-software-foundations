
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