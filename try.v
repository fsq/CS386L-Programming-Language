Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

Compute (next_weekday monday).

(** assertion *)
Example test_next_weekday :
  (next_weekday (next_weekday monday)) = tuesday. Admitted.

Inductive bool : Type :=
  |true : bool
  |false: bool.

Definition negb (b : bool) : bool :=
  match b with
    | true => false
    | false=> true
  end.

Definition addb (b1:bool) (b2:bool) :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1 : (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2 : (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb3 : (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4 : (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5 : false || false || true = true.
Proof. simpl. reflexivity. Qed.

Check true.


Inductive rgb : Type := 
  | red : rgb
  | green : rgb
  | blue : rgb.

Inductive color : Type :=
  | black : color
  | white : color
  | primary : rgb->color.

Definition monochrome (c:color) : bool :=
  match c with
  | black => true
  | white => true
  | primary red => true
  | primary _ => false  
  end.


Compute (monochrome (primary red)).

Module test_nat.
Inductive nat : Type :=
  | O : nat
  | S : nat->nat.

Definition pred (x : nat) : nat :=
  match x with
  |O => O
  |S x' => x'
  end.
End test_nat.

Compute (S (S (S O))).
Check (S (S(S(S(S O))))).

Fixpoint evenb (x:nat) : bool :=
  match x with
  | O => true
  | S n => negb (evenb n)
  end.
Definition oddb (x:nat):bool := negb (evenb x).


Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_oddb2: oddb 100 = false.
Proof. simpl. reflexivity. Qed.

Module Nat_playground2.
Fixpoint plus (n:nat) (m:nat) : nat :=
  match n with
  | 0 => m
  | S n' => S (plus n' m)
  end.

Compute (plus 2 3).


Fixpoint mult (n m:nat):nat :=
  match n with
  | 0 => 0
  | S n' => plus m (mult n' m)
  end.

Example test_mult1 : (mult 3 3)=9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat):nat :=
  match (n, m) with
  | (0, _) => 0
  | (n, 0) => n
  | (S n', S m') => minus n' m'
  end.
End Nat_playground2.

Fixpoint exp (base power:nat) : nat :=
  match power with
  |0 => 1
  |S p' =>mult base (exp base p')
  end.


Notation "x + y" := (plus x y).

Fixpoint beq_nat (x y:nat):bool :=
  match x with
  | 0 => match y with
         | 0 => true
         | _ => false
         end
  | S x' => match y with
         | 0 => false
         | S y' => beq_nat x' y'
         end
  end.

Fixpoint leb (x y:nat) : bool :=
  match x with
  | 0 => true
  | S x' => match y with
            | 0 => false
            | S y' => leb x' y'
            end
  end.

Example test_leb1 : (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.

Example test_leb2 : (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_leb3 : (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n:nat, 0 + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem plus_1_l : forall n:nat, (1 + n) = S n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem mult_O_n : forall n:nat, 0 * n = 0.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem plus_id_example : forall n m:nat, 
  n = m -> n+n = m+m.
Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.

   rewrite -> plus_1_l.
   rewrite -> H.
(*   rewrite -> H. *) 
(*   rewrite plus_1_l. *) 

  simpl.
  reflexivity.
Qed.

Theorem plus_1_neq_0 : forall n:nat, 
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n'].
  - reflexivity.
  - simpl. reflexivity.
Qed.

Theorem negb_involutive : forall b : bool, 
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem add_commutative : forall b c ,
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
