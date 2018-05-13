(*********************************************************)
(*  Formal  Proof of the Tic-Tac-Toe's Perfect Strategy  *)
(*  Author: Shuangquan Feng                              *)
(*  Date:   Apr 29. 2018                                 *)
(*********************************************************)

(* Tic-Tac-Toe' first player has a perfect strategy to never lose the game *)

Require Import board.

(* Definition of 'safe' board state:
   Either
   1. Player1 wins or ties
   2. There exists a move for player1 where either 
      a. player1 wins or ties the game
      b. for any moves player2 can make,
         the resulting state is incomplete(i.e. not lose)
                and still safe for player1.
*)

Inductive safe (b:board) : Prop :=
  | win : (get_state b)=win -> safe b (* p1 wins *)
  | tie : (get_state b)=tie -> safe b (* p1 ties *)
  | safe_step: 
    (exists (x:step), 
      (* p1 makes one move and wins *)
      ((valid_move b x) /\ ((get_state (move b x))=win)) 
      \/
      (* p1 makes one move, forall possible moves for p2, p1 is safe *)
      (forall (y:step), 
       (valid_round b x y)
            ->(((get_state (move b x))=incomplete)/\safe (move (move b x) y))))
      ->
      safe b.

(* The main theorem we want to prove.
   The initial empty board is safe, i.e. player1 can always win or tie *)
Theorem tic_tac_toe_first_always_safe:   
    safe empty_board.

(* define some handy tactics to simplify the proof. *)

(* player1 puts X at cell c can directly win or tie the game *)
Ltac final c := exists (st c X); left; split; simpl; split; constructor.

(* player1 puts X at cell c,
   and enumerate all valid moves of player2 *)
Ltac put c' := 
    exists (st c' X); right; intros y H; split;
    try(reflexivity);unfold valid_round in H;
    induction y as [c s];subst; (* c:a cell, s:X *)
    (* separate out the props in 'valid_round' *)
    destruct H as [H1 [H2 [H3 [H4 H5]]]]; 
    clear H1;
    apply sym_eq_iff in H2; subst; 
    (* enumerate all the moves player2 can choose *)
    induction c; simpl in H3; simpl; 
    (* get rid of the contradictions *)
    try (exfalso; unfold not in H3; apply H3; constructor);
    try (inversion H4);
    try (inversion H5);
    apply safe_step; clear H3 H4 H5.

Proof.
  apply safe_step.

  (* player1 always first put X at top left corner *)
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
Qed.

