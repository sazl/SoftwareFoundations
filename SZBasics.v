(*<------------------------------------------------------------------------->*)

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

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O    => true
  | S n' =>
      match m with
      | O    => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=
  match (beq_nat n m) with
  | true  => false
  | false => leb n m
  end.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

(*<------------------------------------------------------------------------->*)

Theorem plus_0_n: forall n : nat,
  0 + n = n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem mult_0_l : forall n:nat,
  0 * n = 0.
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

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
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

(*<------------------------------------------------------------------------->*)

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative : forall b c,
  andb b c = andb c b.
Proof.
  intros b c.
  destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : forall b c,
  andb b c = andb c b.
Proof.
  intros b c. destruct b.
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
Qed.

Theorem andb3_exchange : forall b c d,
  andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b.
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem plus_1_neq_0' : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative'' : forall b c,
  andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(*<------------------------------------------------------------------------->*)

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros [|n'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  - reflexivity.
  - rewrite <- H.
    reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  - reflexivity.
  - rewrite <- H.
    destruct b.
    + reflexivity.
    + reflexivity.
Qed.

(*<------------------------------------------------------------------------->*)


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

Lemma orb_a_true : forall (b : bool), (orb true b) = true.
Proof.
  reflexivity.
Qed.

Lemma orb_a_false : forall (b : bool), (orb false b) = b.
Proof.
  reflexivity.
Qed.

Lemma andb_a_true : forall (b : bool), (andb true b) = b.
Proof.
  reflexivity.
Qed.

Theorem andb_a_false : forall (b : bool), (andb false b) = false.
Proof.
  reflexivity.
Qed.

Theorem eqb_commutative : forall (a b : bool),
  a = b -> b = a.
Proof.
  intros.
  rewrite -> H.
  reflexivity.
Qed.

Theorem andb_eq_orb : forall (b c : bool),
  (andb b c = orb b c) -> b = c.
Proof.
  intros [] c.
  - rewrite -> andb_a_true.
    rewrite -> orb_a_true.
    intros.
    + rewrite -> H.
      reflexivity.
  - rewrite -> andb_a_false.
    rewrite -> orb_a_false.
    intros.
    + rewrite -> H.
      reflexivity.
Qed.

(*<------------------------------------------------------------------------->*)

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
Proof. reflexivity. Qed.

Example test_bin_incr2: (bin_to_nat (BST BO)) = 1.
Proof. reflexivity. Qed.

Example test_bin_incr3: (bin_to_nat (BT (BST BO))) = 2.
Proof. reflexivity. Qed.

Example test_bin_incr4: (bin_to_nat (BT (BT (BST BO)))) = 4.
Proof. reflexivity. Qed.

Example test_bin_incr5: (bin_to_nat (BST (BT (BT (BT (BST BO)))))) = 17.
Proof. reflexivity. Qed.
