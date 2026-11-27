import Aegis.CountNegatives.Code.Funs

/-!
# Specifications of `Aegis.CountNegatives.count_negatives`

LeetCode problem `count-negative-numbers-in-a-sorted-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountNegatives

  def rows (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    grid.val.map (fun r => r.val.map (fun x => x.val))

  def rowAt (grid : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
    ((rows grid)[i]?).getD []

  def cell (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    ((rowAt grid i)[j]?).getD 0

  def negInRow (grid : Slice (alloc.vec.Vec Std.I64)) (i n : Nat) : Nat :=
    ((List.range n).filter (fun j => cell grid i j < 0)).length

  def nonnegInRow (grid : Slice (alloc.vec.Vec Std.I64)) (i n : Nat) : Nat :=
    ((List.range n).filter (fun j => 0 ≤ cell grid i j)).length

  def negInCol (grid : Slice (alloc.vec.Vec Std.I64)) (j m : Nat) : Nat :=
    ((List.range m).filter (fun i => cell grid i j < 0)).length

  def negPositions (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : List (Nat × Nat) :=
    ((List.range m).map (fun i =>
      ((List.range n).filter (fun j => cell grid i j < 0)).map (fun j => (i, j)))).flatten

  def nonnegPositions (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : List (Nat × Nat) :=
    ((List.range m).map (fun i =>
      ((List.range n).filter (fun j => 0 ≤ cell grid i j)).map (fun j => (i, j)))).flatten

  def negTotal (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Nat :=
    (negPositions grid m n).length

  def nonnegTotal (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Nat :=
    (nonnegPositions grid m n).length

  def rowNegSum (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Nat :=
    ((List.range m).map (fun i => negInRow grid i n)).sum

  def colNegSum (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Nat :=
    ((List.range n).map (fun j => negInCol grid j m)).sum

  /-- The function returns a result r (it does not fail), and r = |{(i,j) : 0 <= i < m and 0 <= j < n and grid[i][j] < 0}|. Equivalently, r is exactly the number of negative entries in grid.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume: 1 <= m <= 100; 1 <= n <= 100; every row grid[i] for 0 <= i < m has length n; for every i,j with 0 <= i < m and 0 <= j < n, -100 <= grid[i][j] <= 100; for every i,j with 0 <= i < m and j+1 < n, grid[i][j] >= grid[i][j+1]; and for every i,j with i+1 < m and 0 <= j < n, grid[i][j] >= grid[i+1][j]. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm_len : (rows grid).length = m)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 100) (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
      (hn_len : ∀ i, i < m → (rowAt grid i).length = n)
      (h_bound : ∀ i j, i < m → j < n → -100 ≤ cell grid i j ∧ cell grid i j ≤ 100)
      (h_row_sorted : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
      (h_col_sorted : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j) :
      ∃ r : Std.I64, Aegis.CountNegatives.count_negatives grid = Result.ok r ∧
        r.val = (negTotal grid m n : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm_len : (rows grid).length = m)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 100) (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
        (hn_len : ∀ i, i < m → (rowAt grid i).length = n)
        (h_bound : ∀ i j, i < m → j < n → -100 ≤ cell grid i j ∧ cell grid i j ≤ 100)
        (h_row_sorted : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
        (h_col_sorted : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j), ∃ r : Std.I64, Aegis.CountNegatives.count_negatives grid = Result.ok r ∧
          r.val = (negTotal grid m n : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, count_negatives(grid) returns a result r; it does not fail (no panic, arithmetic overflow, out-of-bounds access, or other failure).
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume: 1 <= m <= 100; 1 <= n <= 100; every row grid[i] for 0 <= i < m has length n; for every i,j with 0 <= i < m and 0 <= j < n, -100 <= grid[i][j] <= 100; for every i,j with 0 <= i < m and j+1 < n, grid[i][j] >= grid[i][j+1]; and for every i,j with i+1 < m and 0 <= j < n, grid[i][j] >= grid[i+1][j]. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm_len : (rows grid).length = m)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 100) (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
      (hn_len : ∀ i, i < m → (rowAt grid i).length = n)
      (h_bound : ∀ i j, i < m → j < n → -100 ≤ cell grid i j ∧ cell grid i j ≤ 100)
      (h_row_sorted : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
      (h_col_sorted : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j) :
      ∃ r : Std.I64, Aegis.CountNegatives.count_negatives grid = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm_len : (rows grid).length = m)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 100) (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
        (hn_len : ∀ i, i < m → (rowAt grid i).length = n)
        (h_bound : ∀ i j, i < m → j < n → -100 ≤ cell grid i j ∧ cell grid i j ≤ 100)
        (h_row_sorted : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
        (h_col_sorted : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j), ∃ r : Std.I64, Aegis.CountNegatives.count_negatives grid = Result.ok r) := by
    sorry

  /-- Whenever count_negatives(grid) returns a result r, r = 0 iff for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] >= 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume: 1 <= m <= 100; 1 <= n <= 100; every row grid[i] for 0 <= i < m has length n; for every i,j with 0 <= i < m and 0 <= j < n, -100 <= grid[i][j] <= 100; for every i,j with 0 <= i < m and j+1 < n, grid[i][j] >= grid[i][j+1]; and for every i,j with i+1 < m and 0 <= j < n, grid[i][j] >= grid[i+1][j]. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm_len : (rows grid).length = m)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 100) (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
      (hn_len : ∀ i, i < m → (rowAt grid i).length = n)
      (h_bound : ∀ i j, i < m → j < n → -100 ≤ cell grid i j ∧ cell grid i j ≤ 100)
      (h_row_sorted : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
      (h_col_sorted : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j) :
      ∀ r : Std.I64, Aegis.CountNegatives.count_negatives grid = Result.ok r →
        (r.val = 0 ↔ ∀ i j, i < m → j < n → 0 ≤ cell grid i j) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm_len : (rows grid).length = m)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 100) (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
        (hn_len : ∀ i, i < m → (rowAt grid i).length = n)
        (h_bound : ∀ i j, i < m → j < n → -100 ≤ cell grid i j ∧ cell grid i j ≤ 100)
        (h_row_sorted : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
        (h_col_sorted : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j), ∀ r : Std.I64, Aegis.CountNegatives.count_negatives grid = Result.ok r →
          (r.val = 0 ↔ ∀ i j, i < m → j < n → 0 ≤ cell grid i j)) := by
    sorry

  /-- Whenever count_negatives(grid) returns a result r, r = m*n iff for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] < 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume: 1 <= m <= 100; 1 <= n <= 100; every row grid[i] for 0 <= i < m has length n; for every i,j with 0 <= i < m and 0 <= j < n, -100 <= grid[i][j] <= 100; for every i,j with 0 <= i < m and j+1 < n, grid[i][j] >= grid[i][j+1]; and for every i,j with i+1 < m and 0 <= j < n, grid[i][j] >= grid[i+1][j]. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm_len : (rows grid).length = m)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 100) (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
      (hn_len : ∀ i, i < m → (rowAt grid i).length = n)
      (h_bound : ∀ i j, i < m → j < n → -100 ≤ cell grid i j ∧ cell grid i j ≤ 100)
      (h_row_sorted : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
      (h_col_sorted : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j) :
      ∀ r : Std.I64, Aegis.CountNegatives.count_negatives grid = Result.ok r →
        (r.val = ((m * n : Nat) : Int) ↔ ∀ i j, i < m → j < n → cell grid i j < 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm_len : (rows grid).length = m)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 100) (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
        (hn_len : ∀ i, i < m → (rowAt grid i).length = n)
        (h_bound : ∀ i j, i < m → j < n → -100 ≤ cell grid i j ∧ cell grid i j ≤ 100)
        (h_row_sorted : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
        (h_col_sorted : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j), ∀ r : Std.I64, Aegis.CountNegatives.count_negatives grid = Result.ok r →
          (r.val = ((m * n : Nat) : Int) ↔ ∀ i j, i < m → j < n → cell grid i j < 0)) := by
    sorry

  /-- Whenever count_negatives(grid) returns a result r, m*n - r = |{(i,j) : 0 <= i < m and 0 <= j < n and grid[i][j] >= 0}|.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume: 1 <= m <= 100; 1 <= n <= 100; every row grid[i] for 0 <= i < m has length n; for every i,j with 0 <= i < m and 0 <= j < n, -100 <= grid[i][j] <= 100; for every i,j with 0 <= i < m and j+1 < n, grid[i][j] >= grid[i][j+1]; and for every i,j with i+1 < m and 0 <= j < n, grid[i][j] >= grid[i+1][j]. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm_len : (rows grid).length = m)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 100) (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
      (hn_len : ∀ i, i < m → (rowAt grid i).length = n)
      (h_bound : ∀ i j, i < m → j < n → -100 ≤ cell grid i j ∧ cell grid i j ≤ 100)
      (h_row_sorted : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
      (h_col_sorted : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j) :
      ∀ r : Std.I64, Aegis.CountNegatives.count_negatives grid = Result.ok r →
        ((m * n : Nat) : Int) - r.val = (nonnegTotal grid m n : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm_len : (rows grid).length = m)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 100) (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
        (hn_len : ∀ i, i < m → (rowAt grid i).length = n)
        (h_bound : ∀ i j, i < m → j < n → -100 ≤ cell grid i j ∧ cell grid i j ≤ 100)
        (h_row_sorted : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
        (h_col_sorted : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j), ∀ r : Std.I64, Aegis.CountNegatives.count_negatives grid = Result.ok r →
          ((m * n : Nat) : Int) - r.val = (nonnegTotal grid m n : Int)) := by
    sorry

  /-- Whenever count_negatives(grid) returns a result r, r = sum_{i=0}^{m-1} R_i, where for each i, R_i = |{j : 0 <= j < n and grid[i][j] < 0}|.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume: 1 <= m <= 100; 1 <= n <= 100; every row grid[i] for 0 <= i < m has length n; for every i,j with 0 <= i < m and 0 <= j < n, -100 <= grid[i][j] <= 100; for every i,j with 0 <= i < m and j+1 < n, grid[i][j] >= grid[i][j+1]; and for every i,j with i+1 < m and 0 <= j < n, grid[i][j] >= grid[i+1][j]. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm_len : (rows grid).length = m)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 100) (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
      (hn_len : ∀ i, i < m → (rowAt grid i).length = n)
      (h_bound : ∀ i j, i < m → j < n → -100 ≤ cell grid i j ∧ cell grid i j ≤ 100)
      (h_row_sorted : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
      (h_col_sorted : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j) :
      ∀ r : Std.I64, Aegis.CountNegatives.count_negatives grid = Result.ok r →
        r.val = (rowNegSum grid m n : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm_len : (rows grid).length = m)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 100) (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
        (hn_len : ∀ i, i < m → (rowAt grid i).length = n)
        (h_bound : ∀ i j, i < m → j < n → -100 ≤ cell grid i j ∧ cell grid i j ≤ 100)
        (h_row_sorted : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
        (h_col_sorted : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j), ∀ r : Std.I64, Aegis.CountNegatives.count_negatives grid = Result.ok r →
          r.val = (rowNegSum grid m n : Int)) := by
    sorry

  /-- Whenever count_negatives(grid) returns a result r, r = sum_{j=0}^{n-1} C_j, where for each j, C_j = |{i : 0 <= i < m and grid[i][j] < 0}|.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume: 1 <= m <= 100; 1 <= n <= 100; every row grid[i] for 0 <= i < m has length n; for every i,j with 0 <= i < m and 0 <= j < n, -100 <= grid[i][j] <= 100; for every i,j with 0 <= i < m and j+1 < n, grid[i][j] >= grid[i][j+1]; and for every i,j with i+1 < m and 0 <= j < n, grid[i][j] >= grid[i+1][j]. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm_len : (rows grid).length = m)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 100) (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
      (hn_len : ∀ i, i < m → (rowAt grid i).length = n)
      (h_bound : ∀ i j, i < m → j < n → -100 ≤ cell grid i j ∧ cell grid i j ≤ 100)
      (h_row_sorted : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
      (h_col_sorted : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j) :
      ∀ r : Std.I64, Aegis.CountNegatives.count_negatives grid = Result.ok r →
        r.val = (colNegSum grid m n : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm_len : (rows grid).length = m)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 100) (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
        (hn_len : ∀ i, i < m → (rowAt grid i).length = n)
        (h_bound : ∀ i j, i < m → j < n → -100 ≤ cell grid i j ∧ cell grid i j ≤ 100)
        (h_row_sorted : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
        (h_col_sorted : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j), ∀ r : Std.I64, Aegis.CountNegatives.count_negatives grid = Result.ok r →
          r.val = (colNegSum grid m n : Int)) := by
    sorry

  /-- Whenever count_negatives(grid) returns a result r, r > 0 iff grid[m-1][n-1] < 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume: 1 <= m <= 100; 1 <= n <= 100; every row grid[i] for 0 <= i < m has length n; for every i,j with 0 <= i < m and 0 <= j < n, -100 <= grid[i][j] <= 100; for every i,j with 0 <= i < m and j+1 < n, grid[i][j] >= grid[i][j+1]; and for every i,j with i+1 < m and 0 <= j < n, grid[i][j] >= grid[i+1][j]. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm_len : (rows grid).length = m)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 100) (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
      (hn_len : ∀ i, i < m → (rowAt grid i).length = n)
      (h_bound : ∀ i j, i < m → j < n → -100 ≤ cell grid i j ∧ cell grid i j ≤ 100)
      (h_row_sorted : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
      (h_col_sorted : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j) :
      ∀ r : Std.I64, Aegis.CountNegatives.count_negatives grid = Result.ok r →
        (r.val > 0 ↔ cell grid (m - 1) (n - 1) < 0) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm_len : (rows grid).length = m)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 100) (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
        (hn_len : ∀ i, i < m → (rowAt grid i).length = n)
        (h_bound : ∀ i j, i < m → j < n → -100 ≤ cell grid i j ∧ cell grid i j ≤ 100)
        (h_row_sorted : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
        (h_col_sorted : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j), ∀ r : Std.I64, Aegis.CountNegatives.count_negatives grid = Result.ok r →
          (r.val > 0 ↔ cell grid (m - 1) (n - 1) < 0)) := by
    sorry

  /-- Whenever count_negatives(grid) returns a result r, r = m*n iff grid[0][0] < 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume: 1 <= m <= 100; 1 <= n <= 100; every row grid[i] for 0 <= i < m has length n; for every i,j with 0 <= i < m and 0 <= j < n, -100 <= grid[i][j] <= 100; for every i,j with 0 <= i < m and j+1 < n, grid[i][j] >= grid[i][j+1]; and for every i,j with i+1 < m and 0 <= j < n, grid[i][j] >= grid[i+1][j]. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm_len : (rows grid).length = m)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 100) (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
      (hn_len : ∀ i, i < m → (rowAt grid i).length = n)
      (h_bound : ∀ i j, i < m → j < n → -100 ≤ cell grid i j ∧ cell grid i j ≤ 100)
      (h_row_sorted : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
      (h_col_sorted : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j) :
      ∀ r : Std.I64, Aegis.CountNegatives.count_negatives grid = Result.ok r →
        (r.val = ((m * n : Nat) : Int) ↔ cell grid 0 0 < 0) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm_len : (rows grid).length = m)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 100) (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
        (hn_len : ∀ i, i < m → (rowAt grid i).length = n)
        (h_bound : ∀ i j, i < m → j < n → -100 ≤ cell grid i j ∧ cell grid i j ≤ 100)
        (h_row_sorted : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
        (h_col_sorted : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j), ∀ r : Std.I64, Aegis.CountNegatives.count_negatives grid = Result.ok r →
          (r.val = ((m * n : Nat) : Int) ↔ cell grid 0 0 < 0)) := by
    sorry

  end AegisSpec.CountNegatives
