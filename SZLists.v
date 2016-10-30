Add LoadPath "/home/sami/Programming/langs/coq/".
Require Export Induction.
Module NatList.

(*<------------------------------------------------------------------------->*)

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat := 
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat := 
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod := 
  match p with
  | (x,y) => (y,x)
  end.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros [n m].
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros [n m].
  reflexivity.
Qed.

(*<------------------------------------------------------------------------->*)

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil    => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil    => nil 
  | h :: t => t
  end.

Fixpoint repeat (n count : nat) : natlist := 
  match count with
  | O        => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat := 
  match l with
  | nil    => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist := 
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) 
                     (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

(*<------------------------------------------------------------------------->*)

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | 0 :: t => nonzeros t
  | h :: t => h :: nonzeros t
  end.

Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t =>
    match (evenb h) with
    | true  => oddmembers t
    | false => h :: oddmembers t
    end
  end.

Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

Inductive natlistprod : Type :=
  natlistpair : natlist -> natlist -> natlistprod.

Notation "( x , y )" := (natlistpair x y).

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match (l1, l2) with
  | (nil, ys)          => ys
  | (xs, nil)          => xs
  | (x :: xs, y :: ys) => x :: y :: (alternate xs ys)
  end.

Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4: alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

(*<------------------------------------------------------------------------->*)

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat := 
  match s with
  | nil    => 0
  | h :: t =>
    match (beq_nat h v) with
    | true  => S (count v t)
    | false => count v t
    end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag :=
  alternate.


Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag :=
  v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool := 
  negb (beq_nat 0 (count v s)).

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

(*<------------------------------------------------------------------------->*)

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil    => nil
  | h :: t =>
    match (beq_nat h v) with
    | true  => t
    | false => h :: remove_one v t
    end
  end.

Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil    => nil
  | h :: t =>
    match (beq_nat h v) with
    | true  => remove_all v t
    | false => h :: remove_all v t
    end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | nil    => true
  | h :: t => andb (member h s2) (subset t (remove_one h s2))
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O    => true
  | S n' =>
      match m with
      | O    => false
      | S m' => leb n' m'
      end
  end.

Definition blt_nat (n m : nat) : bool :=
  match (beq_nat n m) with
  | true  => false
  | false => leb n m
  end.

Lemma leb_n_Sm : forall n : nat,
  leb n (S n) = true.
Proof.
  intros.
  induction n as [| m].
  - reflexivity.
  - simpl.
    rewrite -> IHm.
    reflexivity.  
Qed.

Theorem bag_theorem : forall (b : bag) (v : nat),
  leb (count v b) (count v (add v b)) = true.
Proof.
  intros.
  induction b as [| n b' IHb'].
  - reflexivity.
  - destruct v as [| u].
    + destruct n as [| m].
      * simpl.
        rewrite -> leb_n_Sm.
        reflexivity.
      * simpl.
        rewrite -> leb_n_Sm.
        reflexivity.
    + simpl.
      rewrite <- beq_nat_refl.
      rewrite -> leb_n_Sm.
      reflexivity.
Qed.

(*<------------------------------------------------------------------------->*)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof.
  reflexivity.
Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2.
  induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl.
    rewrite -> IHl1'.
    reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l.
  induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl.
    rewrite -> app_length.
    rewrite -> plus_comm.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros.
  induction l as [| n l' IHl'].
  - reflexivity.
  - simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.

Lemma app_cons_comm : forall (n : nat) (l : natlist),
  n :: l = [n] ++ l.
Proof.
  intros.
  induction l as [| n' l'].
  - reflexivity.
  - reflexivity.
Qed.

Lemma rev_cons : forall (n : nat) (l : natlist),
  rev (l ++ [n]) = n :: rev l.
Proof.
  intros.
  induction l as [| m k IHk].
  - reflexivity.
  - simpl.
    rewrite ->IHk.
    reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros.
  induction l as [| n l' IHl'].
  - reflexivity.
  - simpl.
    rewrite -> rev_cons.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros.
  induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl.
    rewrite ->IHl1'.
    induction n as [| n'].
    + reflexivity.
    + reflexivity.
Qed.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match (l1, l2) with
  | (nil, nil)       => true
  | (nil, m :: u)    => false
  | (n :: t, nil)    => false
  | (n :: t, m :: u) => (beq_nat n m) && (beq_natlist t u)
  end.

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
Proof. reflexivity. Qed.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl : forall l : natlist,
  true = beq_natlist l l.
Proof.
  intros.
  induction l as [| n l' IHl'].
  { reflexivity. }
  { 
    simpl.
    assert (beq_nat n n = true) as H.
    induction n as [| n' IHn'].
    { reflexivity. }
    {
      simpl.
      rewrite -> IHn'.
      reflexivity.
    }
    rewrite -> H.
    rewrite <- IHl'.
    reflexivity.
  }
Qed.

Theorem count_member_nonzero : forall (s : bag),
  leb 1 (count 1 (1 :: s)) = true.
Proof.
  intros.
  destruct s as [| n s' IHs'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl.
    reflexivity.
  - (* S n' *)
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem remove_decreases_count: forall (s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s.
  induction s as [| n s' IHs'].
  - reflexivity.
  - simpl.
    destruct n as [| n' IHn'].
    + simpl.
      rewrite -> ble_n_Sn.
      reflexivity.
    + simpl.
      rewrite -> IHs'.
      reflexivity.
Qed.

Lemma leb_nat_refl : forall n : nat,
  leb n n = true.
Proof.
  intros.
  induction n as [| m].
  - reflexivity.
  - simpl.
    rewrite -> IHm.
    reflexivity.
Qed.

Lemma count_n_nil : forall (n : nat),
  count n [] = 0.
Proof.
  intros.
  reflexivity.
Qed.

Lemma sum_nil_H : forall (v : bag),
  sum [] v = v.
Proof.
  intros.
  reflexivity.
Qed.

Lemma sum_H_nil : forall (v : bag),
  sum v [] = v.
Proof.
  intros.
  induction v as [| h1 t1].
  - reflexivity.
  - simpl.
    reflexivity.
Qed.

Theorem bag_count_sum : forall (n : nat) (s1 s2 : bag),
  leb ((count n s1) + (count n s2)) (count n (sum s1 s2)) = true.
Proof.
  intros.
  induction s1 as [| h1 t1].
  - destruct s2 as [| h2 t2].
    + reflexivity.
    + rewrite -> count_n_nil.
      rewrite -> plus_O_n.
      rewrite -> sum_nil_H.
      rewrite -> leb_nat_refl.
      reflexivity.
  - destruct s2 as [| h2 t2].
    + rewrite -> sum_H_nil.
      rewrite -> count_n_nil.
      rewrite <- plus_n_O.
      rewrite -> leb_nat_refl.
      reflexivity.
    + rewrite <- IHt1.
      simpl.
Qed.

Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

(*<------------------------------------------------------------------------->*)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None    => d
  end.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | []      => None
  | x :: xs => Some x
  end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros.
  destruct l as [| n kl].
  - reflexivity.
  - reflexivity.
Qed.

(*<------------------------------------------------------------------------->*)

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id x1 x2 :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall (x : id),
  true = beq_id x x.
Proof.
  intros.
  destruct x.
  - simpl.
    rewrite <- beq_nat_refl.
    reflexivity.
Qed.

Inductive partial_map : Type :=
  | empty : partial_map
  | record : id -> nat -> partial_map -> partial_map.

Definition update (d : partial_map)
                  (key : id) (value : nat)
                  : partial_map :=
  record key value d.

Fixpoint find (key : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record k v d' => if beq_id key k
                     then Some v
                     else find key d'
  end.

Theorem update_eq : forall (d : partial_map) (k : id) (v: nat),
  find k (update d k v) = Some v.
Proof.
  intros.
  simpl.
  rewrite <- beq_id_refl.
  reflexivity.
Qed.

Theorem update_neq : forall (d : partial_map) (m n : id) (o: nat),
  beq_id m n = false -> find m (update d n o) = find m d.
Proof.
  intros.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

