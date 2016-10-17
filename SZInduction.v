Add LoadPath "/home/sami/Programming/langs/coq/".
Require Export Basics.
Require Export SZUtility.

(*------------------------------------------*)

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

(*------------------------------------------*)

Theorem andb_b_false: forall b c : bool,
  c = false ->
  andb b c = false.
Proof.
  intros.
  destruct b.
    rewrite -> H.
    reflexivity.
    rewrite -> H.
    reflexivity.
Qed.

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H.
    reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  Case "b = true".
    rewrite <- H.
    reflexivity.
  Case "b = false".
    rewrite <- H.
    rewrite -> andb_b_false.
    reflexivity.
    reflexivity.
Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros.
  induction n as [| n'].
  Case "n = 0".
    simpl.
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'". simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof.
  intros.
  induction n as [| n'].
  Case "n = 0".
    simpl.
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros.
  induction n as [| n'].
  Case "n = 0".
    simpl.
    rewrite <- plus_n_O.
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O    => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n,
  double n = n + n.
Proof.
  intros.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (m + (n + p) = (m + n) + p).
    Case "Proof of assertion".
      rewrite -> plus_assoc.
      reflexivity.
  assert (n + (m + p) = (n + m) + p).
    Case "Proof of assertion".
      rewrite -> plus_assoc.
      reflexivity.
  rewrite -> H.
  rewrite -> H0.
  assert (n + m = m + n).
    Case "Proof of assertion".
      rewrite -> plus_comm.
      reflexivity.
  rewrite -> H1.
  reflexivity.
Qed.

Theorem mult_m_Sn : forall m n : nat,
  m * S n = m + m * n.
Proof.
  intros.
  induction m as [| m'].
  Case "m = 0".
    reflexivity.
  Case "m = S m'".
    simpl.
    rewrite -> IHm'.
    rewrite -> plus_swap.
    reflexivity.
Qed.


Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  intros m n.
  induction n as [| n'].
  Case "n = 0".
    simpl.
    rewrite -> mult_0_r.
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite <- IHn'.
    rewrite <- mult_m_Sn.
    reflexivity.       
Qed.

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  intros.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    destruct n' as [| m].
      reflexivity.
      rewrite -> IHn'.
    rewrite -> negb_involutive.
    reflexivity.
Qed.

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  intros.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem zero_nbeq_S : forall n : nat,
  beq_nat 0 (S n) = false.
Proof.
  intros.
  destruct n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros.
  destruct b.
    reflexivity.
    reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat, 
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros.
  induction p as [| p'].
  Case "p = 0".
    simpl.
    rewrite -> H.
    reflexivity.
  Case "p = S p'".
    simpl.
    rewrite -> IHp'.
    reflexivity.
Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  intros.
  destruct n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    reflexivity.
Qed.

Theorem mult_1_l : forall n:nat,
  1 * n = n.
Proof.
  intros.
  simpl.
  rewrite -> plus_0_r.
  reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros.
  destruct b as [| b'].
  Case "b = true".
    simpl.
    destruct c as [| c'].
    SCase "c = true".
      reflexivity.
    SCase "c = false".
      reflexivity.
  Case "b = false".
    reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    rewrite -> plus_assoc.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    rewrite -> mult_plus_distr_r.
    reflexivity.
Qed.
