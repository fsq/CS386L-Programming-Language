Require Import List Arith.

(* General instructions: Follow the specifc instructions below, and replace
every occurrence of "admitted" with your own code or proof. *)

(* Exercise 1 *)
(* Define an inductive predicate to specify lists whose length is even. *)

(* Name this predicate "len_ev" *)
(* insert your solution here. *)
(* Use "Arguments len_ev {A} _." to make the type argument implicit *)
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Inductive len_ev {A:Type}: list A->Prop:=
  | len_ev0 : len_ev nil
  | len_ev2 a b: len_ev [a;b]
  | len_ev_con x y: len_ev x -> len_ev y -> len_ev (x++y).


Lemma len_ev_example :
   forall a : nat, len_ev (a::(2*a)::(3*a)::(4*a)::nil).
Proof.
  intros a.
  apply (len_ev_con ([a;2*a])).
  - apply len_ev2.
  - apply len_ev2.
Qed.


(* Exercise 2 *)
(* Define an inductive predicate named "swapped" to express that list1 
   is the same as list2 where two consecutive elements have been
   swapped.
   - the first constructor specifies that the first two elements of the
     list have been swapped and the rest is the same for the two lists.
     For instance (swapped (1::3::2::4::nil) (3::1::2::4::nil)) should be
     provable using this constructor.
   - the second constructor specifies that the two lists have the same first
     element, but their tails have a swap in them.
     For instance (swapped (1::3::2::4::nil) (1::2::3::4::nil)) should have
     a proof that starts by using this constructor.
     This predicate should have three arguments: a type A and two lists of
     type A.  Make the type A an implicit argument using the command
     "Arguments swapped {A} _ _." *)

Inductive swapped {A:Type}: list A->list A->Prop:=
  | swap_f a b : forall l:list A,swapped (a::b::l) (b::a::l)
  | swap_t a :  forall l1 l2:list A, swapped l1 l2->swapped (a::l1) (a::l2).

Lemma swapped_ex : swapped (1::3::2::4::nil) (1::2::3::4::nil).
Proof.
  apply swap_t.
  apply swap_f.
Qed.

(* Exercise 3 *)
(* Define an inductive relation named "rearranged" that is satisfied by list1 list2 if
   one of the following cases is satisfied:
   1/ list1 and list2 are the same
   2/ list1 is a swap of list3 and list3 is a rearranged list2.
   Again, this relation should be polymorphic, and you should add an
   implicit argument declaration. *)

Inductive rearranged {A:Type}: list A->list A->Prop :=
  | rearrange_eq : forall l1 l2:list A, l1=l2 -> rearranged l1 l2
  | rearrange_sw : forall l1 l2 l3:list A, 
                    swapped l1 l3->rearranged l3 l2->rearranged l1 l2.

Example rearranged_ex1 : rearranged (2::1::4::3::nil) (1::2::3::4::nil).
Proof.
  assert (swapped [2;1;4;3] [1;2;4;3]).
  apply swap_f.
  assert (swapped [1;2;4;3] [1;2;3;4]).
  apply swap_t. apply swap_t. apply swap_f.
  assert (rearranged [1;2;3;4] [1;2;3;4]).
  apply rearrange_eq. reflexivity.
  assert (rearranged [1;2;4;3] [1;2;3;4]).
  apply (rearrange_sw  [1;2;4;3] [1;2;3;4] [1;2;3;4]).
  apply H0. apply rearrange_eq. reflexivity.
  apply (rearrange_sw  [2;1;4;3] [1;2;3;4] [1;2;4;3]).
  apply H.  apply H2.
Qed.
Example rearranged_ex2 : rearranged (4::3::2::1::nil) (1::2::3::4::nil).
Proof.
  apply (rearrange_sw [4;3;2;1] [1;2;3;4] [3;4;2;1]). 
  apply swap_f.
  apply (rearrange_sw [3;4;2;1] [1;2;3;4] [3;2;4;1]).
  apply swap_t. apply swap_f.
  apply (rearrange_sw [3;2;4;1] [1;2;3;4] [3;2;1;4]).
  apply swap_t. apply swap_t. apply swap_f.
  apply (rearrange_sw [3;2;1;4] [1;2;3;4] [2;3;1;4]).
  apply swap_f.
  apply (rearrange_sw [2;3;1;4] [1;2;3;4] [2;1;3;4]).
  apply swap_t. apply swap_f.
  apply (rearrange_sw [2;1;3;4] [1;2;3;4] [1;2;3;4]).
  apply swap_f. 
  apply rearrange_eq.
  reflexivity.
Qed.

(* Exercise 4 *)
Lemma rearranged_refl : forall (A : Type) (list1 : list A), rearranged list1 list1.
Proof.
  intros.
  apply rearrange_eq. reflexivity.
Qed.

Lemma rearranged_transitive : forall (A : Type) (list1 list2 list3 : list A),
  rearranged list1 list2 -> rearranged list2 list3 -> rearranged list1 list3.
Proof.
  intros A l1 l2 l3 H Q.
  induction H.
  - induction Q.
    + rewrite H. rewrite<-H0. apply rearranged_refl.
    + rewrite H. apply (rearrange_sw l0 l2 l3).
      apply H0. apply Q.
  - apply IHrearranged in Q. apply (rearrange_sw l1 l3 l0).
    apply H. apply Q.
Qed.

Lemma swapped_sym : forall A (list1 list2:list A), swapped list1 list2 -> swapped list2 list1.
Proof.
  intros T l1.
  induction l1.
  - intros l2 H. inversion H.
  - intros l2 H.
    induction H.
    + apply swap_f. 
    + apply swap_t. apply IHswapped.
Qed.

Lemma rearranged_sym : forall (A : Type) (list1 list2 : list A), rearranged list1 list2 -> rearranged list2 list1.
Proof.
  intros. induction H.
  - apply rearrange_eq. symmetry in H. apply H.
  - apply (rearranged_transitive A l2 l3 l1).
    + apply IHrearranged.
    + apply rearrange_sw with l1.
      { apply swapped_sym. apply H. }
      { apply rearrange_eq. reflexivity. }
Qed.

Lemma rearranged_Tail : forall A (a:A) list1 list2, rearranged list1 list2 -> rearranged (a::list1) (a::list2).
Proof.
  intros. induction H.
  - apply rearrange_eq. rewrite H. reflexivity.
  - apply rearrange_sw with (a :: l3).
    + apply swap_t. apply H.
    + apply IHrearranged. 
Qed.

(* This function definitions describes insertion sorting *)

Fixpoint insert x l :=
  match l with 
    nil => x::nil
  | y::tl => if leb x y then x::l else y::insert x tl
  end.

Fixpoint sort l :=
  match l with
    nil => nil
  | x::tl => insert x (sort tl)
  end.

(* Now prove that sorting a list returns an output that satisfies the rearranged relation on the input. *)

Lemma insert_rearranged : forall x l, rearranged (insert x l) (x::l).
Proof.
  intros x l.
  induction l.
  - simpl. apply rearrange_eq. reflexivity.
  - destruct (leb x a ) eqn:Q.
    + simpl. rewrite Q. apply rearranged_refl.
    + simpl. rewrite Q. apply rearranged_sym. 
      apply (rearrange_sw (x :: a :: l)(a :: insert x l) (a::x::l)).
      { apply swap_f. }
      { apply rearranged_Tail. apply rearranged_sym. apply IHl. }
Qed.

Lemma sort_split:
  forall x l, exists l1 l2, l1++l2=l /\ insert x l = l1++[x]++l2.
Proof.
  intros.
  induction l.
  - simpl. exists (nil). exists nil.
    simpl. split. reflexivity. reflexivity.
  - unfold insert.
    destruct (x<=?a) eqn:H.
    + exists nil. exists (a::l).
      simpl. split. reflexivity. reflexivity.
    + fold insert. destruct IHl. destruct H0. destruct H0.
      exists (a::x0). exists x1. simpl. 
      split.
      { rewrite H0. reflexivity. }
      { rewrite H1. reflexivity. } 
Qed.

Lemma rear_pump:
  forall {A:Type} (x:A) (l1 l2:list A), 
    rearranged ([x]++l1++l2) (l1++[x]++l2).
Proof.
  intros.
  induction l1.
  - simpl. apply rearranged_refl.
  - simpl. apply (rearrange_sw (x :: a :: l1 ++ l2) (a :: l1 ++ x :: l2) (a::x::l1++l2)).
    { apply swap_f. }
    { apply rearranged_Tail.
      apply IHl1. }
Qed.

Lemma sort_rea_helper : 
  forall x l1 l2, rearranged l1 l2->rearranged (insert x l1) (x::l2).
Proof.
  intros x l1 l2 H.
  assert (exists la lb, la++lb=l1/\insert x l1 = la++[x]++lb).
  - apply sort_split.
  - destruct H0. destruct H0.  destruct H0.
    rewrite H1.
    apply (rearranged_transitive nat (x0 ++ [x] ++ x1) ([x]++x0++x1) (x :: l2)).
    { apply rearranged_sym. apply rear_pump. }
    { rewrite H0. simpl.  apply rearranged_Tail. apply H. }
Qed.


Lemma sort_rearranged : forall l, rearranged (sort l) l.
Proof.
  intros l.
  induction l.
  - simpl. apply rearranged_refl.
  - simpl. apply sort_rea_helper. apply IHl. 
Qed.




  

