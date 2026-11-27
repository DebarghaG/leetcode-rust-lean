import Aegis.MaxScore.Code.Funs

/-!
# Specifications of `Aegis.MaxScore.max_score`

LeetCode problem `maximum-difference-score-in-a-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxScore

  namespace AegisSpec.MaxScore

  def cell (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    match grid.val[i]? with
    | none => 0
    | some row => (row.val[j]?).map (fun x => x.val) |>.getD 0

  def positions (m n : Nat) : Finset (Nat × Nat) :=
    Finset.product (Finset.range m) (Finset.range n)

  def valueSet (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Finset Int :=
    (positions m n).image (fun p => cell grid p.1 p.2)

  def diffSet (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Finset Int :=
    ((positions m n).product (positions m n)).filter
        (fun p => p.1.1 ≤ p.2.1 ∧ p.1.2 ≤ p.2.2 ∧ p.1 ≠ p.2)
      |>.image (fun p => cell grid p.2.1 p.2.2 - cell grid p.1.1 p.1.2)

  def adjDiffSet (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Finset Int :=
    (positions m (n - 1)).image (fun p => cell grid p.1 (p.2 + 1) - cell grid p.1 p.2)
      ∪ (positions (m - 1) n).image
          (fun p => cell grid (p.1 + 1) p.2 - cell grid p.1 p.2)

  noncomputable def setMax (s : Finset Int) : Int :=
    if h : s.Nonempty then s.max' h else 0

  noncomputable def setMin (s : Finset Int) : Int :=
    if h : s.Nonempty then s.min' h else 0

  /-- Whenever the function returns a result r, r is equal to the maximum of the set { grid[k][l] - grid[i][j] | 0 <= i <= k < m, 0 <= j <= l < n, and (i,j) != (k,l) }.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies the problem constraints: 2 <= m <= 1000, 2 <= n <= 1000, every row of grid has length n, 4 <= m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 100000. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hn : ∀ row ∈ grid.val, row.val.length = n)
      (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
      (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
      (r : Std.I64) (hr : max_score grid = ok r) :
      r.val = setMax (diffSet grid m n) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hn : ∀ row ∈ grid.val, row.val.length = n)
        (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
        (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
        (r : Std.I64) (hr : max_score grid = ok r), r.val = setMax (diffSet grid m n)) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not panic, access out of bounds, or overflow.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies the problem constraints: 2 <= m <= 1000, 2 <= n <= 1000, every row of grid has length n, 4 <= m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 100000. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hn : ∀ row ∈ grid.val, row.val.length = n)
      (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
      (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000) :
      ∃ r : Std.I64, max_score grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hn : ∀ row ∈ grid.val, row.val.length = n)
        (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
        (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000), ∃ r : Std.I64, max_score grid = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every 0 <= i <= k < m and 0 <= j <= l < n with (i,j) != (k,l), we have r >= grid[k][l] - grid[i][j].
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies the problem constraints: 2 <= m <= 1000, 2 <= n <= 1000, every row of grid has length n, 4 <= m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 100000. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hn : ∀ row ∈ grid.val, row.val.length = n)
      (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
      (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
      (r : Std.I64) (hr : max_score grid = ok r) :
      ∀ i j k l : Nat, i ≤ k → k < m → j ≤ l → l < n → (i, j) ≠ (k, l) →
        r.val ≥ cell grid k l - cell grid i j := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hn : ∀ row ∈ grid.val, row.val.length = n)
        (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
        (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
        (r : Std.I64) (hr : max_score grid = ok r), ∀ i j k l : Nat, i ≤ k → k < m → j ≤ l → l < n → (i, j) ≠ (k, l) →
          r.val ≥ cell grid k l - cell grid i j) := by
    sorry

  /-- Whenever the function returns a result r, there exist cells (i,j) and (k,l) with 0 <= i <= k < m, 0 <= j <= l < n, and (i,j) != (k,l), such that r = grid[k][l] - grid[i][j].
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies the problem constraints: 2 <= m <= 1000, 2 <= n <= 1000, every row of grid has length n, 4 <= m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 100000. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hn : ∀ row ∈ grid.val, row.val.length = n)
      (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
      (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
      (r : Std.I64) (hr : max_score grid = ok r) :
      ∃ i j k l : Nat, i ≤ k ∧ k < m ∧ j ≤ l ∧ l < n ∧ (i, j) ≠ (k, l) ∧
        r.val = cell grid k l - cell grid i j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hn : ∀ row ∈ grid.val, row.val.length = n)
        (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
        (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
        (r : Std.I64) (hr : max_score grid = ok r), ∃ i j k l : Nat, i ≤ k ∧ k < m ∧ j ≤ l ∧ l < n ∧ (i, j) ≠ (k, l) ∧
          r.val = cell grid k l - cell grid i j) := by
    sorry

  /-- Whenever the function returns a result r, letting lo = min{grid[i][j] | 0 <= i < m and 0 <= j < n} and hi = max{grid[i][j] | 0 <= i < m and 0 <= j < n}, we have lo - hi <= r <= hi - lo.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies the problem constraints: 2 <= m <= 1000, 2 <= n <= 1000, every row of grid has length n, 4 <= m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 100000. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hn : ∀ row ∈ grid.val, row.val.length = n)
      (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
      (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
      (r : Std.I64) (hr : max_score grid = ok r) :
      let lo := setMin (valueSet grid m n)
      let hi := setMax (valueSet grid m n)
      lo - hi ≤ r.val ∧ r.val ≤ hi - lo := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hn : ∀ row ∈ grid.val, row.val.length = n)
        (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
        (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
        (r : Std.I64) (hr : max_score grid = ok r), let lo := setMin (valueSet grid m n)
        let hi := setMax (valueSet grid m n)
        lo - hi ≤ r.val ∧ r.val ≤ hi - lo) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0 if and only if there exist cells (i,j) and (k,l) with 0 <= i <= k < m, 0 <= j <= l < n, (i,j) != (k,l), and grid[k][l] >= grid[i][j].
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies the problem constraints: 2 <= m <= 1000, 2 <= n <= 1000, every row of grid has length n, 4 <= m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 100000. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hn : ∀ row ∈ grid.val, row.val.length = n)
      (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
      (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
      (r : Std.I64) (hr : max_score grid = ok r) :
      0 ≤ r.val ↔ ∃ i j k l : Nat,
        i ≤ k ∧ k < m ∧ j ≤ l ∧ l < n ∧ (i, j) ≠ (k, l) ∧
          cell grid k l ≥ cell grid i j := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hn : ∀ row ∈ grid.val, row.val.length = n)
        (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
        (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
        (r : Std.I64) (hr : max_score grid = ok r), 0 ≤ r.val ↔ ∃ i j k l : Nat,
          i ≤ k ∧ k < m ∧ j ≤ l ∧ l < n ∧ (i, j) ≠ (k, l) ∧
            cell grid k l ≥ cell grid i j) := by
    sorry

  /-- Whenever the function returns a result r, r = max( { grid[i][j+1] - grid[i][j] | 0 <= i < m and 0 <= j+1 < n } union { grid[i+1][j] - grid[i][j] | 0 <= i+1 < m and 0 <= j < n } ).
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies the problem constraints: 2 <= m <= 1000, 2 <= n <= 1000, every row of grid has length n, 4 <= m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 100000. In addition, grid is non-increasing to the right and downward: for all 0 <= i < m and 0 <= j+1 < n, grid[i][j] >= grid[i][j+1]; and for all 0 <= i+1 < m and 0 <= j < n, grid[i][j] >= grid[i+1][j]. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hn : ∀ row ∈ grid.val, row.val.length = n)
      (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
      (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
      (hmonoR : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
      (hmonoD : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j)
      (r : Std.I64) (hr : max_score grid = ok r) :
      r.val = setMax (adjDiffSet grid m n) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hn : ∀ row ∈ grid.val, row.val.length = n)
        (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
        (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
        (hmonoR : ∀ i j, i < m → j + 1 < n → cell grid i j ≥ cell grid i (j + 1))
        (hmonoD : ∀ i j, i + 1 < m → j < n → cell grid i j ≥ cell grid (i + 1) j)
        (r : Std.I64) (hr : max_score grid = ok r), r.val = setMax (adjDiffSet grid m n)) := by
    sorry

  /-- Whenever the function returns a result r, r = grid[m-1][n-1] - grid[0][0].
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies the problem constraints: 2 <= m <= 1000, 2 <= n <= 1000, every row of grid has length n, 4 <= m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 100000. In addition, grid is non-decreasing to the right and downward: for all 0 <= i < m and 0 <= j+1 < n, grid[i][j] <= grid[i][j+1]; and for all 0 <= i+1 < m and 0 <= j < n, grid[i][j] <= grid[i+1][j]. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hn : ∀ row ∈ grid.val, row.val.length = n)
      (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
      (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
      (hmonoR : ∀ i j, i < m → j + 1 < n → cell grid i j ≤ cell grid i (j + 1))
      (hmonoD : ∀ i j, i + 1 < m → j < n → cell grid i j ≤ cell grid (i + 1) j)
      (r : Std.I64) (hr : max_score grid = ok r) :
      r.val = cell grid (m - 1) (n - 1) - cell grid 0 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hn : ∀ row ∈ grid.val, row.val.length = n)
        (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
        (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
        (hmonoR : ∀ i j, i < m → j + 1 < n → cell grid i j ≤ cell grid i (j + 1))
        (hmonoD : ∀ i j, i + 1 < m → j < n → cell grid i j ≤ cell grid (i + 1) j)
        (r : Std.I64) (hr : max_score grid = ok r), r.val = cell grid (m - 1) (n - 1) - cell grid 0 0) := by
    sorry

  /-- Whenever max_score(grid) returns r and max_score(g') returns r', we have r' = r.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies the problem constraints: 2 <= m <= 1000, 2 <= n <= 1000, every row of grid has length n, 4 <= m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 100000. Let k be an integer such that the grid g' defined by g'[i][j] = grid[i][j] + k for all i,j also satisfies the problem constraints, i.e., 1 <= g'[i][j] <= 100000 for every i,j. -/
  theorem spec_9 (grid g' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (k : Int)
      (hm : grid.val.length = m)
      (hn : ∀ row ∈ grid.val, row.val.length = n)
      (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
      (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
      (hm' : g'.val.length = m)
      (hn' : ∀ row ∈ g'.val, row.val.length = n)
      (hbounds' : ∀ i j, i < m → j < n → 1 ≤ cell g' i j ∧ cell g' i j ≤ 100000)
      (hshift : ∀ i j, i < m → j < n → cell g' i j = cell grid i j + k)
      (r r' : Std.I64) (hr : max_score grid = ok r) (hr' : max_score g' = ok r') :
      r'.val = r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid g' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (k : Int)
        (hm : grid.val.length = m)
        (hn : ∀ row ∈ grid.val, row.val.length = n)
        (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
        (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
        (hm' : g'.val.length = m)
        (hn' : ∀ row ∈ g'.val, row.val.length = n)
        (hbounds' : ∀ i j, i < m → j < n → 1 ≤ cell g' i j ∧ cell g' i j ≤ 100000)
        (hshift : ∀ i j, i < m → j < n → cell g' i j = cell grid i j + k)
        (r r' : Std.I64) (hr : max_score grid = ok r) (hr' : max_score g' = ok r'), r'.val = r.val) := by
    sorry

  /-- Whenever max_score(grid) returns r and max_score(g') returns r', we have r' = c * r.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies the problem constraints: 2 <= m <= 1000, 2 <= n <= 1000, every row of grid has length n, 4 <= m*n <= 100000, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 100000. Let c be an integer with c >= 1 such that the grid g' defined by g'[i][j] = c * grid[i][j] for all i,j also satisfies the problem constraints, i.e., 1 <= g'[i][j] <= 100000 for every i,j. -/
  theorem spec_10 (grid g' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (c : Int)
      (hm : grid.val.length = m)
      (hn : ∀ row ∈ grid.val, row.val.length = n)
      (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
      (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
      (hc : 1 ≤ c)
      (hm' : g'.val.length = m)
      (hn' : ∀ row ∈ g'.val, row.val.length = n)
      (hbounds' : ∀ i j, i < m → j < n → 1 ≤ cell g' i j ∧ cell g' i j ≤ 100000)
      (hscale : ∀ i j, i < m → j < n → cell g' i j = c * cell grid i j)
      (r r' : Std.I64) (hr : max_score grid = ok r) (hr' : max_score g' = ok r') :
      r'.val = c * r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid g' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (c : Int)
        (hm : grid.val.length = m)
        (hn : ∀ row ∈ grid.val, row.val.length = n)
        (hm2 : 2 ≤ m) (hm1000 : m ≤ 1000) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hmn4 : 4 ≤ m * n) (hmn100000 : m * n ≤ 100000)
        (hbounds : ∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
        (hc : 1 ≤ c)
        (hm' : g'.val.length = m)
        (hn' : ∀ row ∈ g'.val, row.val.length = n)
        (hbounds' : ∀ i j, i < m → j < n → 1 ≤ cell g' i j ∧ cell g' i j ≤ 100000)
        (hscale : ∀ i j, i < m → j < n → cell g' i j = c * cell grid i j)
        (r r' : Std.I64) (hr : max_score grid = ok r) (hr' : max_score g' = ok r'), r'.val = c * r.val) := by
    sorry

  end AegisSpec.MaxScore
