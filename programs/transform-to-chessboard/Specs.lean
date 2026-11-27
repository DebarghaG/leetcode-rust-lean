import Aegis.MovesToChessboard.Code.Funs

/-!
# Specifications of `Aegis.MovesToChessboard.moves_to_chessboard`

LeetCode problem `transform-to-chessboard`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MovesToChessboard

namespace AegisSpec.MovesToChessboard

def boardMat (board : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
  board.val.map (fun row => row.val.map (fun x => x.val))

def cell (b : List (List ℤ)) (i j : ℕ) : ℤ :=
  ((b[i]?).bind (fun row => row[j]?)).getD 0

def sameRow (b : List (List ℤ)) (n i : ℕ) : Prop :=
  ∀ j, j < n → cell b i j = cell b 0 j

def sameRowCompl (b : List (List ℤ)) (n i : ℕ) : Prop :=
  ∀ j, j < n → cell b i j = 1 - cell b 0 j

def sameCol (b : List (List ℤ)) (n j : ℕ) : Prop :=
  ∀ i, i < n → cell b i j = cell b i 0

def sameColCompl (b : List (List ℤ)) (n j : ℕ) : Prop :=
  ∀ i, i < n → cell b i j = 1 - cell b i 0

def IsChessboardN (n : ℕ) (b : List (List ℤ)) : Prop :=
  (∀ i j, i + 1 < n → j < n → cell b i j ≠ cell b (i + 1) j) ∧
    (∀ i j, i < n → j + 1 < n → cell b i j ≠ cell b i (j + 1))

def IsChessboard (b : List (List ℤ)) : Prop :=
  IsChessboardN b.length b

def onesCount (b : List (List ℤ)) : ℕ :=
  (b.flatten.filter (fun x => x = 1)).length

inductive Move where
  | row (i j : ℕ)
  | col (i j : ℕ)

def rowSwap (b : List (List ℤ)) (i j : ℕ) : List (List ℤ) :=
  b.mapIdx (fun k row =>
    if k = i then (b[j]?).getD row else if k = j then (b[i]?).getD row else row)

def colSwap (b : List (List ℤ)) (i j : ℕ) : List (List ℤ) :=
  b.map (fun r =>
    r.mapIdx (fun k x =>
      if k = i then (r[j]?).getD x else if k = j then (r[i]?).getD x else x))

def Move.apply (m : Move) (b : List (List ℤ)) : List (List ℤ) :=
  match m with
  | .row i j => rowSwap b i j
  | .col i j => colSwap b i j

def Move.Valid (m : Move) (n : ℕ) : Prop :=
  match m with
  | .row i j => i < n ∧ j < n ∧ i ≠ j
  | .col i j => i < n ∧ j < n ∧ i ≠ j

def applyMoves (b : List (List ℤ)) : List Move → List (List ℤ)
  | [] => b
  | m :: ms => applyMoves (m.apply b) ms

def SwapReach (n : ℕ) (b b' : List (List ℤ)) (k : ℕ) : Prop :=
  ∃ ms : List Move, (∀ m ∈ ms, m.Valid n) ∧ ms.length = k ∧ applyMoves b ms = b'

def ChessReach (n : ℕ) (b : List (List ℤ)) (k : ℕ) : Prop :=
  ∃ b' : List (List ℤ), SwapReach n b b' k ∧ IsChessboardN n b'

noncomputable def rowsEqCount (b : List (List ℤ)) (n : ℕ) : ℕ := by
  classical exact ((Finset.range n).filter (fun i => sameRow b n i)).card

noncomputable def rowsComplCount (b : List (List ℤ)) (n : ℕ) : ℕ := by
  classical exact ((Finset.range n).filter (fun i => sameRowCompl b n i)).card

noncomputable def colsEqCount (b : List (List ℤ)) (n : ℕ) : ℕ := by
  classical exact ((Finset.range n).filter (fun j => sameCol b n j)).card

noncomputable def colsComplCount (b : List (List ℤ)) (n : ℕ) : ℕ := by
  classical exact ((Finset.range n).filter (fun j => sameColCompl b n j)).card

def xorBit (c : ℤ) (k : ℕ) : ℤ :=
  if c = 0 then ((k % 2 : ℕ) : ℤ) else 1 - ((k % 2 : ℕ) : ℤ)

noncomputable def rowType (b : List (List ℤ)) (n i : ℕ) : ℤ := by
  classical exact if sameRow b n i then 0 else 1

noncomputable def colType (b : List (List ℤ)) (n j : ℕ) : ℤ := by
  classical exact if sameCol b n j then 0 else 1

noncomputable def rowMismatch (b : List (List ℤ)) (n : ℕ) (p : ℤ) : ℕ :=
  ((Finset.range n).filter (fun i => rowType b n i ≠ xorBit p i)).card

noncomputable def colMismatch (b : List (List ℤ)) (n : ℕ) (q : ℤ) : ℕ :=
  ((Finset.range n).filter (fun j => colType b n j ≠ xorBit q j)).card

noncomputable def rowAdmissible (b : List (List ℤ)) (n : ℕ) (p : ℤ) : Prop :=
  ((Finset.range n).filter (fun i => xorBit p i = 1)).card =
    ((Finset.range n).filter (fun i => rowType b n i = 1)).card

noncomputable def colAdmissible (b : List (List ℤ)) (n : ℕ) (q : ℤ) : Prop :=
  ((Finset.range n).filter (fun j => xorBit q j = 1)).card =
    ((Finset.range n).filter (fun j => colType b n j = 1)).card

/-- Whenever the function returns a result r, the following holds. A row/column-swap sequence is a finite sequence of moves, each move swapping two distinct rows or two distinct columns. If some row/column-swap sequence transforms board into a chessboard, meaning no two 4-directionally adjacent entries are equal, then r is the minimum length of such a sequence. If no such sequence exists, then r = -1. Equivalently: r = -1 exactly when no row/column-swap sequence reaches a chessboard; otherwise r >= 0 and there is a sequence of exactly r swaps reaching a chessboard, but no sequence of fewer than r swaps does so.
  Preconditions: Let n = len(board). Assume 2 <= n <= 30, every row board[i] has length n, and every entry board[i][j] is either 0 or 1. -/
theorem spec_1 (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r) :
    ((∃ k : ℕ, ChessReach n (boardMat board) k) →
        ∃ k : ℕ,
          ChessReach n (boardMat board) k ∧ r.val = (k : ℤ) ∧
            ∀ k' : ℕ, ChessReach n (boardMat board) k' → k ≤ k') ∧
      ((¬∃ k : ℕ, ChessReach n (boardMat board) k) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r), ((∃ k : ℕ, ChessReach n (boardMat board) k) →
        ∃ k : ℕ,
          ChessReach n (boardMat board) k ∧ r.val = (k : ℤ) ∧
            ∀ k' : ℕ, ChessReach n (boardMat board) k' → k ≤ k') ∧
      ((¬∃ k : ℕ, ChessReach n (boardMat board) k) → r.val = -1)) := by
  sorry

/-- For every such input board, the function returns a result r, i.e. the Lean Result is a successful value and is not a failure, panic, out-of-bounds access, or arithmetic overflow.
  Preconditions: Let n = len(board). Assume 2 <= n <= 30, every row board[i] has length n, and every entry board[i][j] is either 0 or 1. -/
theorem spec_2 (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1) :
    ∃ r : Std.I64, moves_to_chessboard board = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1), ∃ r : Std.I64, moves_to_chessboard board = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1, or 0 <= r <= 2*n - 2.
  Preconditions: Let n = len(board). Assume 2 <= n <= 30, every row board[i] has length n, and every entry board[i][j] is either 0 or 1. -/
theorem spec_3 (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r) :
    r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ 2 * (n : ℤ) - 2) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r), r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ 2 * (n : ℤ) - 2)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if board itself is already a chessboard: for all 0 <= i < n-1 and 0 <= j < n, board[i][j] != board[i+1][j], and for all 0 <= i < n and 0 <= j < n-1, board[i][j] != board[i][j+1].
  Preconditions: Let n = len(board). Assume 2 <= n <= 30, every row board[i] has length n, and every entry board[i][j] is either 0 or 1. -/
theorem spec_4 (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r) :
    (r.val = 0 ↔ IsChessboardN n (boardMat board)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r), (r.val = 0 ↔ IsChessboardN n (boardMat board))) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, the total number ones = #{ (i,j) : 0 <= i < n, 0 <= j < n, board[i][j] = 1 } satisfies |2*ones - n*n| <= 1. Equivalently, ones is floor(n*n/2) or ceil(n*n/2).
  Preconditions: Let n = len(board). Assume 2 <= n <= 30, every row board[i] has length n, and every entry board[i][j] is either 0 or 1. -/
theorem spec_5 (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r) (hr : 0 ≤ r.val) :
    Int.natAbs (2 * (onesCount (boardMat board) : ℤ) - (((n * n : ℕ) : ℤ))) ≤ 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r) (hr : 0 ≤ r.val), Int.natAbs (2 * (onesCount (boardMat board) : ℤ) - (((n * n : ℕ) : ℤ))) ≤ 1) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, every row is equal either to row 0 or to the bitwise complement of row 0: for every i with 0 <= i < n, either (for all j with 0 <= j < n, board[i][j] = board[0][j]) or (for all j with 0 <= j < n, board[i][j] = 1 - board[0][j]).
  Preconditions: Let n = len(board). Assume 2 <= n <= 30, every row board[i] has length n, and every entry board[i][j] is either 0 or 1. -/
theorem spec_6 (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r) (hr : 0 ≤ r.val) :
    ∀ i, i < n → sameRow (boardMat board) n i ∨ sameRowCompl (boardMat board) n i := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r) (hr : 0 ≤ r.val), ∀ i, i < n → sameRow (boardMat board) n i ∨ sameRowCompl (boardMat board) n i) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, every column is equal either to column 0 or to the bitwise complement of column 0: for every j with 0 <= j < n, either (for all i with 0 <= i < n, board[i][j] = board[i][0]) or (for all i with 0 <= i < n, board[i][j] = 1 - board[i][0]).
  Preconditions: Let n = len(board). Assume 2 <= n <= 30, every row board[i] has length n, and every entry board[i][j] is either 0 or 1. -/
theorem spec_7 (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r) (hr : 0 ≤ r.val) :
    ∀ j, j < n → sameCol (boardMat board) n j ∨ sameColCompl (boardMat board) n j := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r) (hr : 0 ≤ r.val), ∀ j, j < n → sameCol (boardMat board) n j ∨ sameColCompl (boardMat board) n j) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, let A be the number of rows i such that board[i][j] = board[0][j] for every j, and let B be the number of rows i such that board[i][j] = 1 - board[0][j] for every j. Then |A - B| <= 1.
  Preconditions: Let n = len(board). Assume 2 <= n <= 30, every row board[i] has length n, and every entry board[i][j] is either 0 or 1. -/
theorem spec_8 (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r) (hr : 0 ≤ r.val) :
    Int.natAbs ((rowsEqCount (boardMat board) n : ℤ) -
        (rowsComplCount (boardMat board) n : ℤ)) ≤ 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r) (hr : 0 ≤ r.val), Int.natAbs ((rowsEqCount (boardMat board) n : ℤ) -
        (rowsComplCount (boardMat board) n : ℤ)) ≤ 1) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, let C be the number of columns j such that board[i][j] = board[i][0] for every i, and let D be the number of columns j such that board[i][j] = 1 - board[i][0] for every i. Then |C - D| <= 1.
  Preconditions: Let n = len(board). Assume 2 <= n <= 30, every row board[i] has length n, and every entry board[i][j] is either 0 or 1. -/
theorem spec_9 (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r) (hr : 0 ≤ r.val) :
    Int.natAbs ((colsEqCount (boardMat board) n : ℤ) -
        (colsComplCount (boardMat board) n : ℤ)) ≤ 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r) (hr : 0 ≤ r.val), Int.natAbs ((colsEqCount (boardMat board) n : ℤ) -
        (colsComplCount (boardMat board) n : ℤ)) ≤ 1) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if at least one of the following holds: (a) there is a row i that is neither equal to row 0 nor equal to the bitwise complement of row 0; (b) there is a column j that is neither equal to column 0 nor equal to the bitwise complement of column 0; (c) letting A be the number of rows equal to row 0 and B the number of rows equal to the complement of row 0, we have |A - B| > 1; (d) letting C be the number of columns equal to column 0 and D the number of columns equal to the complement of column 0, we have |C - D| > 1. Equivalently, r >= 0 if and only if all rows are of the two allowed row types, all columns are of the two allowed column types, and both pairs of type counts are balanced with difference at most one.
  Preconditions: Let n = len(board). Assume 2 <= n <= 30, every row board[i] has length n, and every entry board[i][j] is either 0 or 1. -/
theorem spec_10 (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r) :
    (r.val = -1 ↔
      ((∃ i, i < n ∧ ¬sameRow (boardMat board) n i ∧
            ¬sameRowCompl (boardMat board) n i) ∨
        (∃ j, j < n ∧ ¬sameCol (boardMat board) n j ∧
            ¬sameColCompl (boardMat board) n j) ∨
        (1 < Int.natAbs ((rowsEqCount (boardMat board) n : ℤ) -
          (rowsComplCount (boardMat board) n : ℤ))) ∨
        (1 < Int.natAbs ((colsEqCount (boardMat board) n : ℤ) -
          (colsComplCount (boardMat board) n : ℤ))))) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r), (r.val = -1 ↔
      ((∃ i, i < n ∧ ¬sameRow (boardMat board) n i ∧
            ¬sameRowCompl (boardMat board) n i) ∨
        (∃ j, j < n ∧ ¬sameCol (boardMat board) n j ∧
            ¬sameColCompl (boardMat board) n j) ∨
        (1 < Int.natAbs ((rowsEqCount (boardMat board) n : ℤ) -
          (rowsComplCount (boardMat board) n : ℤ))) ∨
        (1 < Int.natAbs ((colsEqCount (boardMat board) n : ℤ) -
          (colsComplCount (boardMat board) n : ℤ)))))) := by
  sorry

/-- Let r be the result returned for board and let rT be the result returned for boardT. Then r = rT. In particular, both are -1, or both are nonnegative and equal.
  Preconditions: Let n = len(board). Assume 2 <= n <= 30, every row board[i] has length n, and every entry board[i][j] is either 0 or 1. Let boardT be the transpose, boardT[i][j] = board[j][i]. -/
theorem spec_11 (board boardT : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r rT : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hnT : (boardMat boardT).length = n)
    (hrowsT : ∀ row ∈ boardMat boardT, row.length = n)
    (hT : ∀ i j, i < n → j < n → cell (boardMat boardT) i j = cell (boardMat board) j i)
    (hres : moves_to_chessboard board = ok r)
    (hresT : moves_to_chessboard boardT = ok rT) :
    r.val = rT.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (board boardT : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r rT : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hnT : (boardMat boardT).length = n)
    (hrowsT : ∀ row ∈ boardMat boardT, row.length = n)
    (hT : ∀ i j, i < n → j < n → cell (boardMat boardT) i j = cell (boardMat board) j i)
    (hres : moves_to_chessboard board = ok r)
    (hresT : moves_to_chessboard boardT = ok rT), r.val = rT.val) := by
  sorry

/-- Let r be the result returned for board and let rC be the result returned for boardC. Then r = rC.
  Preconditions: Let n = len(board). Assume 2 <= n <= 30, every row board[i] has length n, and every entry board[i][j] is either 0 or 1. Let boardC be obtained by replacing every entry x with 1 - x. -/
theorem spec_12 (board boardC : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r rC : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hnC : (boardMat boardC).length = n)
    (hrowsC : ∀ row ∈ boardMat boardC, row.length = n)
    (hC : ∀ i j, i < n → j < n →
      cell (boardMat boardC) i j = 1 - cell (boardMat board) i j)
    (hres : moves_to_chessboard board = ok r)
    (hresC : moves_to_chessboard boardC = ok rC) :
    r.val = rC.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (board boardC : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r rC : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hnC : (boardMat boardC).length = n)
    (hrowsC : ∀ row ∈ boardMat boardC, row.length = n)
    (hC : ∀ i j, i < n → j < n →
      cell (boardMat boardC) i j = 1 - cell (boardMat board) i j)
    (hres : moves_to_chessboard board = ok r)
    (hresC : moves_to_chessboard boardC = ok rC), r.val = rC.val) := by
  sorry

/-- Let r be the result returned for board and let r2 be the result returned for board2. Then either both r and r2 are -1, or both are nonnegative and |r - r2| <= 1.
  Preconditions: Let n = len(board). Assume 2 <= n <= 30, every row board[i] has length n, and every entry board[i][j] is either 0 or 1. Let board2 be obtained from board by swapping two distinct rows or by swapping two distinct columns. -/
theorem spec_13 (board board2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r r2 : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (h2 : ∃ i j : ℕ, i < n ∧ j < n ∧ i ≠ j ∧
      (boardMat board2 = rowSwap (boardMat board) i j ∨
        boardMat board2 = colSwap (boardMat board) i j))
    (hres : moves_to_chessboard board = ok r)
    (hres2 : moves_to_chessboard board2 = ok r2) :
    (r.val = -1 ∧ r2.val = -1) ∨
      (0 ≤ r.val ∧ 0 ≤ r2.val ∧ Int.natAbs (r.val - r2.val) ≤ 1) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (board board2 : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r r2 : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (h2 : ∃ i j : ℕ, i < n ∧ j < n ∧ i ≠ j ∧
      (boardMat board2 = rowSwap (boardMat board) i j ∨
        boardMat board2 = colSwap (boardMat board) i j))
    (hres : moves_to_chessboard board = ok r)
    (hres2 : moves_to_chessboard board2 = ok r2), (r.val = -1 ∧ r2.val = -1) ∨
      (0 ≤ r.val ∧ 0 ≤ r2.val ∧ Int.natAbs (r.val - r2.val) ≤ 1)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if board is a chessboard, and r = -1 if board is not a chessboard. Thus for n = 2 no positive move count is ever returned.
  Preconditions: Let n = len(board). Assume n = 2, every row board[i] has length 2, and every entry board[i][j] is either 0 or 1. -/
theorem spec_14 (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : n = 2)
    (hrows : ∀ row ∈ boardMat board, row.length = 2)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r) :
    (IsChessboardN 2 (boardMat board) → r.val = 0) ∧
      (¬IsChessboardN 2 (boardMat board) → r.val = -1) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : n = 2)
    (hrows : ∀ row ∈ boardMat board, row.length = 2)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r), (IsChessboardN 2 (boardMat board) → r.val = 0) ∧
      (¬IsChessboardN 2 (boardMat board) → r.val = -1)) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, there exist a bit c in {0,1}, a permutation sigma of {0,...,n-1}, and a permutation tau of {0,...,n-1} such that for every i,j with 0 <= i < n and 0 <= j < n, board[sigma(i)][tau(j)] = c XOR ((i+j) mod 2). Here XOR is on bits 0 and 1.
  Preconditions: Let n = len(board). Assume 2 <= n <= 30, every row board[i] has length n, and every entry board[i][j] is either 0 or 1. -/
theorem spec_15 (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r) (hr : 0 ≤ r.val) :
    ∃ c : ℤ, (c = 0 ∨ c = 1) ∧
      ∃ σ τ : Equiv.Perm (Fin n),
        ∀ i j : Fin n,
          cell (boardMat board) (σ i).val (τ j).val = xorBit c (i.val + j.val) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r) (hr : 0 ≤ r.val), ∃ c : ℤ, (c = 0 ∨ c = 1) ∧
      ∃ σ τ : Equiv.Perm (Fin n),
        ∀ i j : Fin n,
          cell (boardMat board) (σ i).val (τ j).val = xorBit c (i.val + j.val)) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, let n = len(board). Define t_i = 0 if row i equals row 0 and t_i = 1 if row i is the bitwise complement of row 0; define u_j = 0 if column j equals column 0 and u_j = 1 if column j is the bitwise complement of column 0. For a bit p in {0,1}, let rowMismatch(p) = #{ i : 0 <= i < n and t_i != (p XOR (i mod 2)) }; call p row-admissible if #{ i : p XOR (i mod 2) = 1 } = #{ i : t_i = 1 }. Define colMismatch(q) and q col-admissible analogously using u. Then r = ( min_{p row-admissible} rowMismatch(p) + min_{q col-admissible} colMismatch(q) ) / 2.
  Preconditions: Let n = len(board). Assume 2 <= n <= 30, every row board[i] has length n, and every entry board[i][j] is either 0 or 1. -/
theorem spec_16 (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r) (hr : 0 ≤ r.val) :
    ∃ p q : ℤ,
      rowAdmissible (boardMat board) n p ∧ colAdmissible (boardMat board) n q ∧
        2 * r.val = (rowMismatch (boardMat board) n p : ℤ) +
          (colMismatch (boardMat board) n q : ℤ) ∧
        (∀ p' : ℤ,
          rowAdmissible (boardMat board) n p' →
            rowMismatch (boardMat board) n p ≤ rowMismatch (boardMat board) n p') ∧
        (∀ q' : ℤ,
          colAdmissible (boardMat board) n q' →
            colMismatch (boardMat board) n q ≤ colMismatch (boardMat board) n q') := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (r : Std.I64)
    (hn : n = (boardMat board).length) (hn2 : 2 ≤ n) (hn30 : n ≤ 30)
    (hrows : ∀ row ∈ boardMat board, row.length = n)
    (hentries : ∀ row ∈ boardMat board, ∀ x ∈ row, x = 0 ∨ x = 1)
    (hres : moves_to_chessboard board = ok r) (hr : 0 ≤ r.val), ∃ p q : ℤ,
      rowAdmissible (boardMat board) n p ∧ colAdmissible (boardMat board) n q ∧
        2 * r.val = (rowMismatch (boardMat board) n p : ℤ) +
          (colMismatch (boardMat board) n q : ℤ) ∧
        (∀ p' : ℤ,
          rowAdmissible (boardMat board) n p' →
            rowMismatch (boardMat board) n p ≤ rowMismatch (boardMat board) n p') ∧
        (∀ q' : ℤ,
          colAdmissible (boardMat board) n q' →
            colMismatch (boardMat board) n q ≤ colMismatch (boardMat board) n q')) := by
  sorry

end AegisSpec.MovesToChessboard
