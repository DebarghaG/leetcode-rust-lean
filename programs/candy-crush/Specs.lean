import Aegis.CandyCrush.Code.Funs

/-!
# Specifications of `Aegis.CandyCrush.candy_crush`

LeetCode problem `candy-crush`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CandyCrush

namespace AegisSpec.CandyCrush

attribute [local instance] Classical.propDecidable

abbrev Grid := List (List Int)

def rowsGrid (rows : List (alloc.vec.Vec Std.I64)) : Grid :=
  rows.map (fun row => row.val.map (fun x => x.val))

def rowAt (g : Grid) (i : Nat) : Option (List Int) := g[i]?

def cell (g : Grid) (i j : Nat) : Option Int :=
  (rowAt g i).bind (fun row => row[j]?)

def Rect (g : Grid) (m n : Nat) : Prop :=
  g.length = m ∧ ∀ i (row : List Int), rowAt g i = some row → row.length = n

def EntriesInRange (g : Grid) (m n : Nat) : Prop :=
  ∀ i j x, i < m → j < n → cell g i j = some x → 0 ≤ x ∧ x ≤ 2000

def HRun (g : Grid) (i j : Nat) (v : Int) : Prop :=
  ∃ a b : Nat, a ≤ j ∧ j < b ∧ 3 ≤ b - a ∧ ∀ t, a ≤ t → t < b → cell g i t = some v

def VRun (g : Grid) (i j : Nat) (v : Int) : Prop :=
  ∃ a b : Nat, a ≤ i ∧ i < b ∧ 3 ≤ b - a ∧ ∀ t, a ≤ t → t < b → cell g t j = some v

def Crushable (g : Grid) (i j : Nat) : Prop :=
  ∃ v : Int, v ≠ 0 ∧ cell g i j = some v ∧ (HRun g i j v ∨ VRun g i j v)

def Stable (g : Grid) : Prop := ∀ i j, ¬ Crushable g i j

noncomputable def crush (g : Grid) : Grid :=
  g.mapIdx (fun i row => row.mapIdx (fun j x => if Crushable g i j then 0 else x))

def column (g : Grid) (j : Nat) : List Int :=
  g.filterMap (fun row => row[j]?)

def dropColumn (c : List Int) (m : Nat) : List Int :=
  let nz := c.filter (fun x => decide (x ≠ 0))
  List.replicate (m - nz.length) 0 ++ nz

def drop (g : Grid) (m n : Nat) : Grid :=
  (List.range n).map (fun j => dropColumn (column g j) m)

noncomputable def step (g : Grid) (m n : Nat) : Grid :=
  if Stable g then g else drop (crush g) m n

def nzCount (g : Grid) : Nat :=
  (g.map (fun row => row.countP (fun x => decide (x ≠ 0)))).sum

def columnNZ (g : Grid) (j : Nat) : List (Nat × Int) :=
  (((List.range g.length).filterMap
      (fun i => (rowAt g i).bind (fun row => (row[j]?).map (fun x => (i, x))))).filter
    (fun p => decide (p.2 ≠ 0)))

def columnValues (g : Grid) (j : Nat) : List Int :=
  (columnNZ g j).map (fun p => p.2)

def ColMatching (inp out : List (Nat × Int)) : Prop :=
  ∃ f : Nat → Nat,
    (∀ a, a < out.length → f a < inp.length) ∧
    (∀ a b, a < b → b < out.length → f a < f b) ∧
    (∀ a, a < out.length →
      ∃ p q, inp[f a]? = some p ∧ out[a]? = some q ∧ p.1 ≤ q.1 ∧ q.2 = p.2)

/-- The function returns a result r. Call a cell (i,j) of a board B of these dimensions crushable if B[i][j] != 0 and either it belongs to a horizontal contiguous segment of at least 3 equal nonzero values, or it belongs to a vertical contiguous segment of at least 3 equal nonzero values. Let Stable(B) mean no cell is crushable. Let Crush(B) set every crushable cell to 0 and leave all other cells unchanged. Let Drop(C) be the board obtained column by column as follows: in column j, take the nonzero entries C[0][j],...,C[m-1][j] in top-to-bottom order, delete the zero entries, and place the remaining sequence in the bottom len(sequence) cells of that column in the same order, with zeros above. Let Step(B)=B if Stable(B), and Step(B)=Drop(Crush(B)) otherwise. Then len(r)=m, len(r[i])=n for every 0<=i<m, and there exist k>=0 and boards B_0,...,B_k with B_0=board, B_{t+1}=Step(B_t) for every 0<=t<k, B_k=r, and Stable(r).
  Preconditions: Let m = len(board) and n = len(board[0]). The board is rectangular with 3 <= m <= 50 and 3 <= n <= 50, i.e. len(board)=m and len(board[i])=n for every 0 <= i < m; moreover 0 <= board[i][j] <= 2000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_1 (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000) :
    ∃ (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (k : Nat) (B : Nat → Grid),
      candy_crush board = ok r ∧
      (rowsGrid r.val).length = m ∧
      (∀ i (row : List Int), rowAt (rowsGrid r.val) i = some row → row.length = n) ∧
      B 0 = rowsGrid board.val ∧
      (∀ t, t < k → B (t + 1) = step (B t) m n) ∧
      B k = rowsGrid r.val ∧
      Stable (B k) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000), ∃ (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (k : Nat) (B : Nat → Grid),
      candy_crush board = ok r ∧
      (rowsGrid r.val).length = m ∧
      (∀ i (row : List Int), rowAt (rowsGrid r.val) i = some row → row.length = n) ∧
      B 0 = rowsGrid board.val ∧
      (∀ t, t < k → B (t + 1) = step (B t) m n) ∧
      B k = rowsGrid r.val ∧
      Stable (B k)) := by
  sorry

/-- For every board satisfying the preconditions, candy_crush returns a result r; it does not panic, overflow, or otherwise fail.
  Preconditions: Let m = len(board) and n = len(board[0]). The board is rectangular with 3 <= m <= 50 and 3 <= n <= 50, i.e. len(board)=m and len(board[i])=n for every 0 <= i < m; moreover 0 <= board[i][j] <= 2000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_2 (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r)=len(board)=m and len(r[i])=n for every 0 <= i < m; no row or column is added or removed.
  Preconditions: Let m = len(board) and n = len(board[0]). The board is rectangular with 3 <= m <= 50 and 3 <= n <= 50, i.e. len(board)=m and len(board[i])=n for every 0 <= i < m; moreover 0 <= board[i][j] <= 2000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_3 (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      (rowsGrid r.val).length = m ∧
      (∀ i (row : List Int), rowAt (rowsGrid r.val) i = some row → row.length = n) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      (rowsGrid r.val).length = m ∧
      (∀ i (row : List Int), rowAt (rowsGrid r.val) i = some row → row.length = n)) := by
  sorry

/-- Whenever the function returns a result r, no cell of r is part of a horizontal or vertical contiguous run of at least 3 equal nonzero values. That is, for every cell (i,j) with r[i][j] != 0, there is no interval of length at least 3 in row i containing j all equal to r[i][j], and no interval of length at least 3 in column j containing i all equal to r[i][j].
  Preconditions: Let m = len(board) and n = len(board[0]). The board is rectangular with 3 <= m <= 50 and 3 <= n <= 50, i.e. len(board)=m and len(board[i])=n for every 0 <= i < m; moreover 0 <= board[i][j] <= 2000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_4 (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      Stable (rowsGrid r.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      Stable (rowsGrid r.val)) := by
  sorry

/-- Whenever the function returns a result r, if r is not equal to board, then every column of r is bottom-packed: for every column j and every pair of rows a<b, if r[a][j] != 0 then r[b][j] != 0.
  Preconditions: Let m = len(board) and n = len(board[0]). The board is rectangular with 3 <= m <= 50 and 3 <= n <= 50, i.e. len(board)=m and len(board[i])=n for every 0 <= i < m; moreover 0 <= board[i][j] <= 2000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_5 (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      rowsGrid r.val ≠ rowsGrid board.val →
      ∀ j a b, j < n → a < b → b < m →
        cell (rowsGrid r.val) a j ≠ some 0 → cell (rowsGrid r.val) b j ≠ some 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      rowsGrid r.val ≠ rowsGrid board.val →
      ∀ j a b, j < n → a < b → b < m →
        cell (rowsGrid r.val) a j ≠ some 0 → cell (rowsGrid r.val) b j ≠ some 0) := by
  sorry

/-- Whenever the function returns a result r, r equals board if and only if board has no crushable cell, where a cell is crushable when it is nonzero and belongs to a horizontal or vertical contiguous run of at least 3 equal nonzero values.
  Preconditions: Let m = len(board) and n = len(board[0]). The board is rectangular with 3 <= m <= 50 and 3 <= n <= 50, i.e. len(board)=m and len(board[i])=n for every 0 <= i < m; moreover 0 <= board[i][j] <= 2000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_6 (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      (rowsGrid r.val = rowsGrid board.val ↔ Stable (rowsGrid board.val)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      (rowsGrid r.val = rowsGrid board.val ↔ Stable (rowsGrid board.val))) := by
  sorry

/-- Whenever the function returns a result r, every nonzero value appearing in r also appears somewhere in board; no new candy type is created.
  Preconditions: Let m = len(board) and n = len(board[0]). The board is rectangular with 3 <= m <= 50 and 3 <= n <= 50, i.e. len(board)=m and len(board[i])=n for every 0 <= i < m; moreover 0 <= board[i][j] <= 2000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_7 (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      ∀ i j x, cell (rowsGrid r.val) i j = some x → x ≠ 0 →
        ∃ i' j', cell (rowsGrid board.val) i' j' = some x := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      ∀ i j x, cell (rowsGrid r.val) i j = some x → x ≠ 0 →
        ∃ i' j', cell (rowsGrid board.val) i' j' = some x) := by
  sorry

/-- Whenever the function returns a result r, for every column j there is an order-preserving matching from the nonzero entries of r in column j to the nonzero entries of board in column j that never moves a candy upward. Explicitly, if the input nonzero row positions in column j are p_0 < p_1 < ... < p_{K-1} and the output nonzero row positions in column j are q_0 < q_1 < ... < q_{L-1}, then there exist indices 0 <= t_0 < t_1 < ... < t_{L-1} < K such that r[q_a][j] = board[p_{t_a}][j] and q_a >= p_{t_a} for every 0 <= a < L.
  Preconditions: Let m = len(board) and n = len(board[0]). The board is rectangular with 3 <= m <= 50 and 3 <= n <= 50, i.e. len(board)=m and len(board[i])=n for every 0 <= i < m; moreover 0 <= board[i][j] <= 2000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_8 (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      ∀ j, j < n →
        ColMatching (columnNZ (rowsGrid board.val) j) (columnNZ (rowsGrid r.val) j) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      ∀ j, j < n →
        ColMatching (columnNZ (rowsGrid board.val) j) (columnNZ (rowsGrid r.val) j)) := by
  sorry

/-- Whenever the function returns a result r, if r differs from board then the total number of nonzero cells in r is at most the total number of nonzero cells in board minus 3; if r equals board, the two totals are equal.
  Preconditions: Let m = len(board) and n = len(board[0]). The board is rectangular with 3 <= m <= 50 and 3 <= n <= 50, i.e. len(board)=m and len(board[i])=n for every 0 <= i < m; moreover 0 <= board[i][j] <= 2000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_9 (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      (rowsGrid r.val ≠ rowsGrid board.val →
        nzCount (rowsGrid r.val) + 3 ≤ nzCount (rowsGrid board.val)) ∧
      (rowsGrid r.val = rowsGrid board.val →
        nzCount (rowsGrid r.val) = nzCount (rowsGrid board.val)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      (rowsGrid r.val ≠ rowsGrid board.val →
        nzCount (rowsGrid r.val) + 3 ≤ nzCount (rowsGrid board.val)) ∧
      (rowsGrid r.val = rowsGrid board.val →
        nzCount (rowsGrid r.val) = nzCount (rowsGrid board.val))) := by
  sorry

/-- Whenever the function returns a result r, every entry of r satisfies 0 <= r[i][j] <= 2000 for every 0 <= i < m and 0 <= j < n.
  Preconditions: Let m = len(board) and n = len(board[0]). The board is rectangular with 3 <= m <= 50 and 3 <= n <= 50, i.e. len(board)=m and len(board[i])=n for every 0 <= i < m; moreover 0 <= board[i][j] <= 2000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_10 (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      ∀ i j x, cell (rowsGrid r.val) i j = some x → 0 ≤ x ∧ x ≤ 2000 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      ∀ i j x, cell (rowsGrid r.val) i j = some x → 0 ≤ x ∧ x ≤ 2000) := by
  sorry

/-- For every board satisfying the preconditions, if candy_crush(board) = r then candy_crush(r) = r; the returned stable board is a fixed point (the function is idempotent).
  Preconditions: Let m = len(board) and n = len(board[0]) with 3 <= m,n <= 50, rectangular, and 0 <= board[i][j] <= 2000. -/
theorem spec_11 (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      candy_crush r.deref = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      candy_crush r.deref = ok r) := by
  sorry

/-- For every column j, the multiset of nonzero entries in column j of r equals the multiset of nonzero entries in column j of board with some entries deleted (candies never change columns or values); in particular the number of nonzero cells in column j of r is at most the number in column j of board.
  Preconditions: Let m = len(board) and n = len(board[0]) with 3 <= m,n <= 50, rectangular, and 0 <= board[i][j] <= 2000. -/
theorem spec_12 (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      ∀ j, j < n →
        (∃ l₁ l₂ : List Int,
          columnValues (rowsGrid board.val) j
            = l₁ ++ columnValues (rowsGrid r.val) j ++ l₂) ∧
        (columnValues (rowsGrid r.val) j).length
          ≤ (columnValues (rowsGrid board.val) j).length := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm3 : 3 ≤ m) (hm50 : m ≤ 50) (hn3 : 3 ≤ n) (hn50 : n ≤ 50)
    (hlen : (rowsGrid board.val).length = m)
    (hrows : ∀ i (row : List Int), rowAt (rowsGrid board.val) i = some row → row.length = n)
    (hbound : ∀ i j x, i < m → j < n → cell (rowsGrid board.val) i j = some x →
      0 ≤ x ∧ x ≤ 2000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), candy_crush board = ok r →
      ∀ j, j < n →
        (∃ l₁ l₂ : List Int,
          columnValues (rowsGrid board.val) j
            = l₁ ++ columnValues (rowsGrid r.val) j ++ l₂) ∧
        (columnValues (rowsGrid r.val) j).length
          ≤ (columnValues (rowsGrid board.val) j).length) := by
  sorry

end AegisSpec.CandyCrush
