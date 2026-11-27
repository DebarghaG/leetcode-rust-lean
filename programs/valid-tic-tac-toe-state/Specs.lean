import Aegis.ValidTicTacToe.Code.Funs

/-!
# Specifications of `Aegis.ValidTicTacToe.valid_tic_tac_toe`

LeetCode problem `valid-tic-tac-toe-state`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option maxHeartbeats 1000000

namespace AegisSpec.ValidTicTacToe

open Aegis.ValidTicTacToe

abbrev Board : Type := Slice (alloc.vec.Vec Std.U8)

def spaceByte : Nat := 32

def xByte : Nat := 88

def oByte : Nat := 79

def cellByte (board : Board) (i j : Nat) : Std.U8 :=
  match board.val[i]? with
  | none => 0#u8
  | some row =>
    match row.val[j]? with
    | none => 0#u8
    | some c => c

def cell (board : Board) (i j : Nat) : Nat := (cellByte board i j).val

def cells (board : Board) : List Nat :=
  ((List.range 3).map (fun i => (List.range 3).map (fun j => cell board i j))).flatten

def countByte (board : Board) (b : Nat) : Nat := (cells board).count b

def xCount (board : Board) : Nat := countByte board xByte

def oCount (board : Board) : Nat := countByte board oByte

def winLines : List (List (Nat × Nat)) :=
  [[(0, 0), (0, 1), (0, 2)],
   [(1, 0), (1, 1), (1, 2)],
   [(2, 0), (2, 1), (2, 2)],
   [(0, 0), (1, 0), (2, 0)],
   [(0, 1), (1, 1), (2, 1)],
   [(0, 2), (1, 2), (2, 2)],
   [(0, 0), (1, 1), (2, 2)],
   [(0, 2), (1, 1), (2, 0)]]

def Wins (board : Board) (c : Nat) : Prop :=
  ∃ line, line ∈ winLines ∧ ∀ p, p ∈ line → cell board p.1 p.2 = c

def XWins (board : Board) : Prop := Wins board xByte

def OWins (board : Board) : Prop := Wins board oByte

def Shape3 (board : Board) : Prop :=
  board.val.length = 3 ∧ ∀ i, i < 3 → ∃ row, board.val[i]? = some row ∧ row.val.length = 3

def CellsValid (board : Board) : Prop :=
  ∀ i j, i < 3 → j < 3 →
    cell board i j = spaceByte ∨ cell board i j = xByte ∨ cell board i j = oByte

theorem three_le_usizeMax : (3 : Nat) ≤ Aeneas.Std.Usize.max := by
  simp [Aeneas.Std.Usize.max, Aeneas.Std.Usize.numBits]
  rcases System.Platform.numBits_eq with h | h <;> (rw [h]; norm_num)

def mkRow (a b c : Std.U8) : alloc.vec.Vec Std.U8 :=
  ⟨⟨3, Aeneas.Data.ListN.ListN.fromList [a, b, c], three_le_usizeMax⟩⟩

def mkBoard (r0 r1 r2 : alloc.vec.Vec Std.U8) : Board :=
  ⟨3, Aeneas.Data.ListN.ListN.fromList [r0, r1, r2], three_le_usizeMax⟩

def transpose (board : Board) : Board :=
  mkBoard
    (mkRow (cellByte board 0 0) (cellByte board 1 0) (cellByte board 2 0))
    (mkRow (cellByte board 0 1) (cellByte board 1 1) (cellByte board 2 1))
    (mkRow (cellByte board 0 2) (cellByte board 1 2) (cellByte board 2 2))

def flipH (board : Board) : Board :=
  mkBoard
    (mkRow (cellByte board 0 2) (cellByte board 0 1) (cellByte board 0 0))
    (mkRow (cellByte board 1 2) (cellByte board 1 1) (cellByte board 1 0))
    (mkRow (cellByte board 2 2) (cellByte board 2 1) (cellByte board 2 0))

/-- Let xCount(board) be the number of cells equal to 'X' and oCount(board) the number of cells equal to 'O'. A winning line for a character c is a row, column, or diagonal all of whose three cells equal c; say X wins if there is a winning line for 'X', and O wins if there is a winning line for 'O'. The function returns a result r, and r = true if and only if all of the following hold: (1) xCount(board) = oCount(board) or xCount(board) = oCount(board) + 1; (2) it is not the case that both X wins and O wins; (3) if X wins then xCount(board) = oCount(board) + 1; (4) if O wins then xCount(board) = oCount(board).
  Preconditions: len(board) = 3; for every i with 0 <= i < 3, len(board[i]) = 3; for every i, j with 0 <= i < 3 and 0 <= j < 3, board[i][j] is one of the bytes corresponding to ' ', 'X', or 'O'. -/
theorem spec_1 (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board) :
    ∃ r, valid_tic_tac_toe board = ok r ∧
      (r = true ↔
        ((xCount board = oCount board ∨ xCount board = oCount board + 1) ∧
          ¬ (XWins board ∧ OWins board) ∧
          (XWins board → xCount board = oCount board + 1) ∧
          (OWins board → xCount board = oCount board))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board), ∃ r, valid_tic_tac_toe board = ok r ∧
      (r = true ↔
        ((xCount board = oCount board ∨ xCount board = oCount board + 1) ∧
          ¬ (XWins board ∧ OWins board) ∧
          (XWins board → xCount board = oCount board + 1) ∧
          (OWins board → xCount board = oCount board)))) := by
  sorry

/-- The function returns a result (it does not fail) for every board satisfying the preconditions.
  Preconditions: len(board) = 3; for every i with 0 <= i < 3, len(board[i]) = 3; for every i, j with 0 <= i < 3 and 0 <= j < 3, board[i][j] is one of the bytes corresponding to ' ', 'X', or 'O'. -/
theorem spec_2 (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board) :
    ∃ r, valid_tic_tac_toe board = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board), ∃ r, valid_tic_tac_toe board = ok r) := by
  sorry

/-- Let xCount(board) be the number of cells equal to 'X' and oCount(board) the number of cells equal to 'O'. Whenever valid_tic_tac_toe(board) returns r, if r = true then xCount(board) = oCount(board) or xCount(board) = oCount(board) + 1.
  Preconditions: len(board) = 3; for every i with 0 <= i < 3, len(board[i]) = 3; for every i, j with 0 <= i < 3 and 0 <= j < 3, board[i][j] is one of the bytes corresponding to ' ', 'X', or 'O'. -/
theorem spec_3 (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board) :
    ∀ r, valid_tic_tac_toe board = ok r → r = true →
      xCount board = oCount board ∨ xCount board = oCount board + 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board), ∀ r, valid_tic_tac_toe board = ok r → r = true →
      xCount board = oCount board ∨ xCount board = oCount board + 1) := by
  sorry

/-- Let xCount(board) be the number of cells equal to 'X' and oCount(board) the number of cells equal to 'O'. Whenever valid_tic_tac_toe(board) returns r, if r = true then xCount(board) <= 5 and oCount(board) <= 4.
  Preconditions: len(board) = 3; for every i with 0 <= i < 3, len(board[i]) = 3; for every i, j with 0 <= i < 3 and 0 <= j < 3, board[i][j] is one of the bytes corresponding to ' ', 'X', or 'O'. -/
theorem spec_4 (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board) :
    ∀ r, valid_tic_tac_toe board = ok r → r = true →
      xCount board ≤ 5 ∧ oCount board ≤ 4 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board), ∀ r, valid_tic_tac_toe board = ok r → r = true →
      xCount board ≤ 5 ∧ oCount board ≤ 4) := by
  sorry

/-- A winning line for a character c is a row, column, or diagonal all of whose three cells equal c; say X wins if there is a winning line for 'X', and O wins if there is a winning line for 'O'. Whenever valid_tic_tac_toe(board) returns r, if r = true then it is not the case that both X wins and O wins.
  Preconditions: len(board) = 3; for every i with 0 <= i < 3, len(board[i]) = 3; for every i, j with 0 <= i < 3 and 0 <= j < 3, board[i][j] is one of the bytes corresponding to ' ', 'X', or 'O'. -/
theorem spec_5 (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board) :
    ∀ r, valid_tic_tac_toe board = ok r → r = true → ¬ (XWins board ∧ OWins board) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board), ∀ r, valid_tic_tac_toe board = ok r → r = true → ¬ (XWins board ∧ OWins board)) := by
  sorry

/-- Let xCount(board) be the number of cells equal to 'X' and oCount(board) the number of cells equal to 'O'. A winning line for a character c is a row, column, or diagonal all of whose three cells equal c; say X wins if there is a winning line for 'X'. Whenever valid_tic_tac_toe(board) returns r, if r = true and X wins then xCount(board) = oCount(board) + 1.
  Preconditions: len(board) = 3; for every i with 0 <= i < 3, len(board[i]) = 3; for every i, j with 0 <= i < 3 and 0 <= j < 3, board[i][j] is one of the bytes corresponding to ' ', 'X', or 'O'. -/
theorem spec_6 (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board) :
    ∀ r, valid_tic_tac_toe board = ok r → r = true → XWins board →
      xCount board = oCount board + 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board), ∀ r, valid_tic_tac_toe board = ok r → r = true → XWins board →
      xCount board = oCount board + 1) := by
  sorry

/-- Let xCount(board) be the number of cells equal to 'X' and oCount(board) the number of cells equal to 'O'. A winning line for a character c is a row, column, or diagonal all of whose three cells equal c; say O wins if there is a winning line for 'O'. Whenever valid_tic_tac_toe(board) returns r, if r = true and O wins then xCount(board) = oCount(board).
  Preconditions: len(board) = 3; for every i with 0 <= i < 3, len(board[i]) = 3; for every i, j with 0 <= i < 3 and 0 <= j < 3, board[i][j] is one of the bytes corresponding to ' ', 'X', or 'O'. -/
theorem spec_7 (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board) :
    ∀ r, valid_tic_tac_toe board = ok r → r = true → OWins board →
      xCount board = oCount board := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board), ∀ r, valid_tic_tac_toe board = ok r → r = true → OWins board →
      xCount board = oCount board) := by
  sorry

/-- Let xCount(board) be the number of cells equal to 'X' and oCount(board) the number of cells equal to 'O'. A winning line for a character c is a row, column, or diagonal all of whose three cells equal c; say X wins if there is a winning line for 'X', and O wins if there is a winning line for 'O'. Whenever valid_tic_tac_toe(board) returns r, if r = false then at least one of the following holds: (i) xCount(board) is not equal to oCount(board) and xCount(board) is not equal to oCount(board) + 1; (ii) X wins and O wins; (iii) X wins and xCount(board) is not equal to oCount(board) + 1; (iv) O wins and xCount(board) is not equal to oCount(board).
  Preconditions: len(board) = 3; for every i with 0 <= i < 3, len(board[i]) = 3; for every i, j with 0 <= i < 3 and 0 <= j < 3, board[i][j] is one of the bytes corresponding to ' ', 'X', or 'O'. -/
theorem spec_8 (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board) :
    ∀ r, valid_tic_tac_toe board = ok r → r = false →
      ((xCount board ≠ oCount board ∧ xCount board ≠ oCount board + 1) ∨
        (XWins board ∧ OWins board) ∨
        (XWins board ∧ xCount board ≠ oCount board + 1) ∨
        (OWins board ∧ xCount board ≠ oCount board)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board), ∀ r, valid_tic_tac_toe board = ok r → r = false →
      ((xCount board ≠ oCount board ∧ xCount board ≠ oCount board + 1) ∨
        (XWins board ∧ OWins board) ∨
        (XWins board ∧ xCount board ≠ oCount board + 1) ∨
        (OWins board ∧ xCount board ≠ oCount board))) := by
  sorry

/-- Let xCount(board) be the number of cells equal to 'X' and oCount(board) the number of cells equal to 'O'. A winning line for a character c is a row, column, or diagonal all of whose three cells equal c; say X wins if there is a winning line for 'X', and O wins if there is a winning line for 'O'. If neither X nor O wins and xCount(board) = oCount(board) or xCount(board) = oCount(board) + 1, then the function returns a result r with r = true.
  Preconditions: len(board) = 3; for every i with 0 <= i < 3, len(board[i]) = 3; for every i, j with 0 <= i < 3 and 0 <= j < 3, board[i][j] is one of the bytes corresponding to ' ', 'X', or 'O'. -/
theorem spec_9 (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board) :
    ¬ XWins board → ¬ OWins board →
      (xCount board = oCount board ∨ xCount board = oCount board + 1) →
      ∃ r, valid_tic_tac_toe board = ok r ∧ r = true := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board), ¬ XWins board → ¬ OWins board →
      (xCount board = oCount board ∨ xCount board = oCount board + 1) →
      ∃ r, valid_tic_tac_toe board = ok r ∧ r = true) := by
  sorry

/-- Let xCount(board) be the number of cells equal to 'X' and oCount(board) the number of cells equal to 'O'. A winning line for a character c is a row, column, or diagonal all of whose three cells equal c; say X wins if there is a winning line for 'X', and O wins if there is a winning line for 'O'. If X wins and O does not win and xCount(board) = oCount(board) + 1, then the function returns a result r with r = true.
  Preconditions: len(board) = 3; for every i with 0 <= i < 3, len(board[i]) = 3; for every i, j with 0 <= i < 3 and 0 <= j < 3, board[i][j] is one of the bytes corresponding to ' ', 'X', or 'O'. -/
theorem spec_10 (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board) :
    XWins board → ¬ OWins board → xCount board = oCount board + 1 →
      ∃ r, valid_tic_tac_toe board = ok r ∧ r = true := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board), XWins board → ¬ OWins board → xCount board = oCount board + 1 →
      ∃ r, valid_tic_tac_toe board = ok r ∧ r = true) := by
  sorry

/-- Let xCount(board) be the number of cells equal to 'X' and oCount(board) the number of cells equal to 'O'. A winning line for a character c is a row, column, or diagonal all of whose three cells equal c; say X wins if there is a winning line for 'X', and O wins if there is a winning line for 'O'. If O wins and X does not win and xCount(board) = oCount(board), then the function returns a result r with r = true.
  Preconditions: len(board) = 3; for every i with 0 <= i < 3, len(board[i]) = 3; for every i, j with 0 <= i < 3 and 0 <= j < 3, board[i][j] is one of the bytes corresponding to ' ', 'X', or 'O'. -/
theorem spec_11 (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board) :
    OWins board → ¬ XWins board → xCount board = oCount board →
      ∃ r, valid_tic_tac_toe board = ok r ∧ r = true := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board), OWins board → ¬ XWins board → xCount board = oCount board →
      ∃ r, valid_tic_tac_toe board = ok r ∧ r = true) := by
  sorry

/-- Let boardT be the 3x3 board defined by boardT[i][j] = board[j][i] for all 0 <= i < 3 and 0 <= j < 3. Whenever valid_tic_tac_toe(board) returns r and valid_tic_tac_toe(boardT) returns rT, we have r = rT.
  Preconditions: len(board) = 3; for every i with 0 <= i < 3, len(board[i]) = 3; for every i, j with 0 <= i < 3 and 0 <= j < 3, board[i][j] is one of the bytes corresponding to ' ', 'X', or 'O'. -/
theorem spec_12 (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board) :
    ∀ r rT, valid_tic_tac_toe board = ok r → valid_tic_tac_toe (transpose board) = ok rT →
      r = rT := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board), ∀ r rT, valid_tic_tac_toe board = ok r → valid_tic_tac_toe (transpose board) = ok rT →
      r = rT) := by
  sorry

/-- Let boardH be the 3x3 board defined by boardH[i][j] = board[i][2 - j] for all 0 <= i < 3 and 0 <= j < 3. Whenever valid_tic_tac_toe(board) returns r and valid_tic_tac_toe(boardH) returns rH, we have r = rH.
  Preconditions: len(board) = 3; for every i with 0 <= i < 3, len(board[i]) = 3; for every i, j with 0 <= i < 3 and 0 <= j < 3, board[i][j] is one of the bytes corresponding to ' ', 'X', or 'O'. -/
theorem spec_13 (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board) :
    ∀ r rH, valid_tic_tac_toe board = ok r → valid_tic_tac_toe (flipH board) = ok rH →
      r = rH := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (board : Board) (hshape : Shape3 board) (hvalid : CellsValid board), ∀ r rH, valid_tic_tac_toe board = ok r → valid_tic_tac_toe (flipH board) = ok rH →
      r = rH) := by
  sorry

end AegisSpec.ValidTicTacToe
