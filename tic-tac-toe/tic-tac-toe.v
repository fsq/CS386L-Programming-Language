Require Import board.

Inductive safe (b:board) : Prop :=
  | win : (get_state b)=win -> safe b
  | tie : (get_state b)=tie -> safe b
  | safe_step: 
    (exists (x:step), 
      ((valid_move b x) /\ ((get_state (move b x))=win)) 
      \/
      (forall (y:step), 
       (valid_round b x y)->(safe (move (move b x) y))))
      ->
      safe b.

Ltac helper H y:=
  unfold valid_round in H;
  induction y as [c s];subst;destruct H as [H1 [H2 [H3 [H4 H5]]]];
  clear H1;
  apply sym_eq_iff in H2; subst;
  induction c; simpl in H3;simpl;
  try (exfalso;unfold not in H3;apply H3;constructor);
  try (inversion H4);
  try (inversion H5);apply safe_step;clear H3 H4 H5.

Ltac final c :=exists (st c X);left;split;simpl;split;constructor.

Ltac put c := exists (st c X);right;intros y H;helper H y.

Theorem tic_tac_toe_first_always_safe:
  safe empty_board.
Proof.
  apply safe_step.
  put c00. 

  - put c11; try(final c22).
    + put c20; try(final c02).
      * final c10.
  - put c11; try(final c22).
    + put c12; try(final c10).
      * put c21. put c20. put c01.
  - put c11; try(final c22).
    + put c20; try(final c02).
      * put c12. put c21. put c11.
  - put c02; try(final c01).
    + put c21.
      * put c12. put c22. put c20.
      * put c10. put c22. put c20.
      * put c12. put c22. put c10.
      * put c10. put c20. put c21.
  - put c11; try(final c22).
    + put c02; try(final c20).
      * final c01.
  - put c01; try(final c02).
    + put c11; try(final c21).
      * final c22.
  - put c11; try(final c22).
    + put c20; try(final c10).
      * final c02.
  - put c02; try(final c01).
    + put c20; try(final c11).
      * final c10.
    + final c01.
    + final c01.
    + final c01.
    + final c01.
    + final c01.
Qed.
