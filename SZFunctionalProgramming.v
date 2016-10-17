Theorem plus_0_n: forall n : nat,
  0 + n = n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem plus_1_l : forall n:nat,
  1 + n = S n.
Proof.
  intros n.
  reflexivity.
Qed.


Theorem plus_id_example : forall n m: nat,
  n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m ->
  m = o ->
  n + m = m + o.
Proof.
  intros n m o.
  intros H J.
  rewrite -> H.
  rewrite -> J.
  reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros m n.
  intros H.
  rewrite -> plus_1_l.
  rewrite <- H.
  reflexivity.
Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O =>
      match m with
      | O => true
      | S m' => false
      end
  | S n' =>
      match m with
      | O => false
      | S m' => beq_nat n' m'
      end
  end.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n as [| n'].
    reflexivity.
    reflexivity.
Qed.


Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b.
    reflexivity.
    reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  rewrite -> negb_involutive.
  reflexivity.
Qed.

Theorem orb_true : forall (b c : bool),
  b = true -> (orb b c) = true.
Proof.
  intros.
  rewrite -> H.
  destruct c.
    reflexivity.
    reflexivity.
Qed.

Theorem orb_false : forall (b c : bool),
  b = false -> (orb b c) = c.
Proof.
  intros.
  rewrite -> H.
  destruct c.
    reflexivity.
    reflexivity.
Qed.

Lemma andb_a_true : forall (a b : bool),
  a = true ->
 (andb a b) = b.
Proof.
  intros a b H.
  rewrite -> H.
  destruct b.
    reflexivity.
    reflexivity.
Qed.

Theorem andb_a_false : forall (a b : bool),
  a = false ->
  (andb a b) = a.
Proof.
  intros.
  rewrite -> H.
  destruct b.
    reflexivity.
    reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  destruct b.
    rewrite -> orb_true.
    rewrite -> andb_a_true.
    intros.
    rewrite -> H.
    reflexivity.
    reflexivity.
    reflexivity.

    rewrite -> orb_false.
    rewrite -> andb_a_false.
    intros.
    rewrite -> H.
    reflexivity.
    reflexivity.
    reflexivity.
Qed.

Inductive bin : Type :=
  | BO :  bin
  | BT :  bin -> bin
  | BST : bin -> bin.

Definition bin_incr (a : bin) : bin :=
  match a with
  | BO    => BST a
  | BT b  => BST b
  | BST c => BST a
  end.

Fixpoint bin_to_nat (a : bin) : nat :=
  match a with
  | BO    => O
  | BT b  => 2 * (bin_to_nat b)
  | BST c => 1 + 2 * (bin_to_nat c)
  end.

Example test_bin_incr1: (bin_to_nat BO) = 0.

Example test_bin_incr2: (bin_to_nat (BST BO)) = 1.

Example test_bin_incr3: (bin_to_nat (BT (BST BO))) = 2.

Example test_bin_incr4: (bin_to_nat (BT (BT (BST BO)))) = 4.

Example test_bin_incr5: (bin_to_nat (BST (BT (BT (BT (BST BO)))))) = 9.

