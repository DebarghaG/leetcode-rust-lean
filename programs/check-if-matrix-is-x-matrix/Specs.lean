import Aegis.CheckXMatrix.Code.Funs

/-!
# Specifications of `Aegis.CheckXMatrix.check_x_matrix`

LeetCode problem `check-if-matrix-is-x-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CheckXMatrix

def rowVals (grid : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
  ((grid.val[i]?).map
      (fun (v : alloc.vec.Vec Std.I64) => v.val.map (fun (x : Std.I64) => x.val))).getD []

def entry (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  (rowVals grid i).getD j 0

def rowNonzero (grid : Slice (alloc.vec.Vec Std.I64)) (n i : Nat) : Nat :=
  ((List.range n).filter (fun j => entry grid i j != 0)).length

def colNonzero (grid : Slice (alloc.vec.Vec Std.I64)) (n j : Nat) : Nat :=
  ((List.range n).filter (fun i => entry grid i j != 0)).length

def nonzeroCount (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Nat :=
  ((List.range n).map (fun i => rowNonzero grid n i)).sum

def IsXMatrix (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Prop :=
  (∀ i, i < n → entry grid i i ≠ 0 ∧ entry grid i (n - 1 - i) ≠ 0) ∧
    (∀ i j, i < n → j < n → i ≠ j → i + j ≠ n - 1 → entry grid i j = 0)

/-- Whenever check_x_matrix returns a result r, r = true if and only if both of the following hold: (1) for every i with 0 <= i < n, grid[i][i] != 0 and grid[i][n-1-i] != 0; (2) for every i, j with 0 <= i < n and 0 <= j < n, if i != j and i + j != n - 1, then grid[i][j] = 0. Equivalently, r = false exactly when at least one of these two conditions fails.
  Preconditions: Let n = len(grid). The preconditions are: 3 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] <= 100000. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : grid.val.length = n) (hn3 : 3 ≤ n) (hn100 : n ≤ 100)
    (hrow : ∀ i, i < n → (rowVals grid i).length = n)
    (hval : ∀ i j, i < n → j < n → 0 ≤ entry grid i j ∧ entry grid i j ≤ 100000) :
    ∀ r, Aegis.CheckXMatrix.check_x_matrix grid = ok r → (r = true ↔ IsXMatrix grid n) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : grid.val.length = n) (hn3 : 3 ≤ n) (hn100 : n ≤ 100)
    (hrow : ∀ i, i < n → (rowVals grid i).length = n)
    (hval : ∀ i j, i < n → j < n → 0 ≤ entry grid i j ∧ entry grid i j ≤ 100000), ∀ r, Aegis.CheckXMatrix.check_x_matrix grid = ok r → (r = true ↔ IsXMatrix grid n)) := by
  sorry

/-- For every input satisfying the preconditions, check_x_matrix returns a result r; it does not fail (no overflow, out-of-bounds access, or panic).
  Preconditions: Let n = len(grid). The preconditions are: 3 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] <= 100000. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : grid.val.length = n) (hn3 : 3 ≤ n) (hn100 : n ≤ 100)
    (hrow : ∀ i, i < n → (rowVals grid i).length = n)
    (hval : ∀ i j, i < n → j < n → 0 ≤ entry grid i j ∧ entry grid i j ≤ 100000) :
    ∃ r, Aegis.CheckXMatrix.check_x_matrix grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : grid.val.length = n) (hn3 : 3 ≤ n) (hn100 : n ≤ 100)
    (hrow : ∀ i, i < n → (rowVals grid i).length = n)
    (hval : ∀ i j, i < n → j < n → 0 ≤ entry grid i j ∧ entry grid i j ≤ 100000), ∃ r, Aegis.CheckXMatrix.check_x_matrix grid = ok r) := by
  sorry

/-- Whenever check_x_matrix returns true, the number of pairs (i, j) with 0 <= i < n, 0 <= j < n, and grid[i][j] != 0 is 2*n - 1 if n is odd, and 2*n if n is even.
  Preconditions: Let n = len(grid). The preconditions are: 3 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] <= 100000. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : grid.val.length = n) (hn3 : 3 ≤ n) (hn100 : n ≤ 100)
    (hrow : ∀ i, i < n → (rowVals grid i).length = n)
    (hval : ∀ i j, i < n → j < n → 0 ≤ entry grid i j ∧ entry grid i j ≤ 100000) :
    ∀ r, Aegis.CheckXMatrix.check_x_matrix grid = ok r → r = true →
      nonzeroCount grid n = if n % 2 = 1 then 2 * n - 1 else 2 * n := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : grid.val.length = n) (hn3 : 3 ≤ n) (hn100 : n ≤ 100)
    (hrow : ∀ i, i < n → (rowVals grid i).length = n)
    (hval : ∀ i j, i < n → j < n → 0 ≤ entry grid i j ∧ entry grid i j ≤ 100000), ∀ r, Aegis.CheckXMatrix.check_x_matrix grid = ok r → r = true →
      nonzeroCount grid n = if n % 2 = 1 then 2 * n - 1 else 2 * n) := by
  sorry

/-- Whenever check_x_matrix returns true, for every row index i with 0 <= i < n, the number of columns j with 0 <= j < n and grid[i][j] != 0 is 1 if i = n - 1 - i, and is 2 otherwise.
  Preconditions: Let n = len(grid). The preconditions are: 3 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] <= 100000. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : grid.val.length = n) (hn3 : 3 ≤ n) (hn100 : n ≤ 100)
    (hrow : ∀ i, i < n → (rowVals grid i).length = n)
    (hval : ∀ i j, i < n → j < n → 0 ≤ entry grid i j ∧ entry grid i j ≤ 100000) :
    ∀ r, Aegis.CheckXMatrix.check_x_matrix grid = ok r → r = true →
      ∀ i, i < n → rowNonzero grid n i = if i = n - 1 - i then 1 else 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : grid.val.length = n) (hn3 : 3 ≤ n) (hn100 : n ≤ 100)
    (hrow : ∀ i, i < n → (rowVals grid i).length = n)
    (hval : ∀ i j, i < n → j < n → 0 ≤ entry grid i j ∧ entry grid i j ≤ 100000), ∀ r, Aegis.CheckXMatrix.check_x_matrix grid = ok r → r = true →
      ∀ i, i < n → rowNonzero grid n i = if i = n - 1 - i then 1 else 2) := by
  sorry

/-- Whenever check_x_matrix returns true, for every column index j with 0 <= j < n, the number of rows i with 0 <= i < n and grid[i][j] != 0 is 1 if j = n - 1 - j, and is 2 otherwise.
  Preconditions: Let n = len(grid). The preconditions are: 3 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] <= 100000. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : grid.val.length = n) (hn3 : 3 ≤ n) (hn100 : n ≤ 100)
    (hrow : ∀ i, i < n → (rowVals grid i).length = n)
    (hval : ∀ i j, i < n → j < n → 0 ≤ entry grid i j ∧ entry grid i j ≤ 100000) :
    ∀ r, Aegis.CheckXMatrix.check_x_matrix grid = ok r → r = true →
      ∀ j, j < n → colNonzero grid n j = if j = n - 1 - j then 1 else 2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : grid.val.length = n) (hn3 : 3 ≤ n) (hn100 : n ≤ 100)
    (hrow : ∀ i, i < n → (rowVals grid i).length = n)
    (hval : ∀ i j, i < n → j < n → 0 ≤ entry grid i j ∧ entry grid i j ≤ 100000), ∀ r, Aegis.CheckXMatrix.check_x_matrix grid = ok r → r = true →
      ∀ j, j < n → colNonzero grid n j = if j = n - 1 - j then 1 else 2) := by
  sorry

/-- Whenever check_x_matrix(grid) returns r1 and check_x_matrix(grid2) returns r2, r1 = r2.
  Preconditions: Let n = len(grid) = len(grid2). The preconditions are: 3 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n and len(grid2[i]) = n; for every i, j with 0 <= i < n and 0 <= j < n, 0 <= grid[i][j] <= 100000 and 0 <= grid2[i][j] <= 100000; and grid2 is the transpose of grid: for every i, j with 0 <= i < n and 0 <= j < n, grid2[i][j] = grid[j][i]. -/
theorem spec_6 (grid grid2 : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : grid.val.length = n) (hn2 : grid2.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100)
    (hrow : ∀ i, i < n → (rowVals grid i).length = n)
    (hrow2 : ∀ i, i < n → (rowVals grid2 i).length = n)
    (hval : ∀ i j, i < n → j < n → 0 ≤ entry grid i j ∧ entry grid i j ≤ 100000)
    (hval2 : ∀ i j, i < n → j < n → 0 ≤ entry grid2 i j ∧ entry grid2 i j ≤ 100000)
    (htrans : ∀ i j, i < n → j < n → entry grid2 i j = entry grid j i) :
    ∀ r1 r2, Aegis.CheckXMatrix.check_x_matrix grid = ok r1 →
      Aegis.CheckXMatrix.check_x_matrix grid2 = ok r2 → r1 = r2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid grid2 : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : grid.val.length = n) (hn2 : grid2.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100)
    (hrow : ∀ i, i < n → (rowVals grid i).length = n)
    (hrow2 : ∀ i, i < n → (rowVals grid2 i).length = n)
    (hval : ∀ i j, i < n → j < n → 0 ≤ entry grid i j ∧ entry grid i j ≤ 100000)
    (hval2 : ∀ i j, i < n → j < n → 0 ≤ entry grid2 i j ∧ entry grid2 i j ≤ 100000)
    (htrans : ∀ i j, i < n → j < n → entry grid2 i j = entry grid j i), ∀ r1 r2, Aegis.CheckXMatrix.check_x_matrix grid = ok r1 →
      Aegis.CheckXMatrix.check_x_matrix grid2 = ok r2 → r1 = r2) := by
  sorry

end AegisSpec.CheckXMatrix
