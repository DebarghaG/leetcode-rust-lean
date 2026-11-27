import Aegis.MinimumObstacles.Code.Funs

/-!
# Specifications of `Aegis.MinimumObstacles.minimum_obstacles`

LeetCode problem `minimum-obstacle-removal-to-reach-corner`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumObstacles

abbrev Grid := Slice (alloc.vec.Vec Std.I64)

def cellValue (grid : Grid) (i j : Nat) : Int :=
  match grid.val[i]? with
  | none => 0
  | some row => ((row.val[j]?).map (fun (v : Std.I64) => v.val)).getD 0

def IsObstacleGrid (grid : Grid) (m n : Nat) : Prop :=
  grid.val.length = m ∧
  (∀ i, i < m → ∀ row : alloc.vec.Vec Std.I64, grid.val[i]? = some row → row.val.length = n) ∧
  (∀ i j, i < m → j < n → cellValue grid i j = 0 ∨ cellValue grid i j = 1)

def stepDist (p q : Nat × Nat) : Nat :=
  (p.1 - q.1) + (q.1 - p.1) + (p.2 - q.2) + (q.2 - p.2)

def IsGridPath (m n : Nat) (P : List (Nat × Nat)) : Prop :=
  P ≠ [] ∧
  P.head? = some (0, 0) ∧
  P.getLast? = some (m - 1, n - 1) ∧
  (∀ p ∈ P, p.1 < m ∧ p.2 < n) ∧
  (∀ (l : Nat) (p q : Nat × Nat), P[l]? = some p → P[l+1]? = some q → stepDist p q = 1)

def pathObstacleCount (grid : Grid) (P : List (Nat × Nat)) : Nat :=
  (P.dedup.filter (fun p => cellValue grid p.1 p.2 = 1)).length

def obstacleCells (grid : Grid) (m n : Nat) : Finset (Nat × Nat) :=
  ((Finset.range m).product (Finset.range n)).filter (fun p => cellValue grid p.1 p.2 = 1)

def IsPassable (grid : Grid) (R : Finset (Nat × Nat)) (p : Nat × Nat) : Prop :=
  cellValue grid p.1 p.2 = 0 ∨ p ∈ R

def CornersConnected (grid : Grid) (m n : Nat) (R : Finset (Nat × Nat)) : Prop :=
  ∃ P : List (Nat × Nat),
    P ≠ [] ∧
    P.head? = some (0, 0) ∧
    P.getLast? = some (m - 1, n - 1) ∧
    (∀ p ∈ P, p.1 < m ∧ p.2 < n ∧ IsPassable grid R p) ∧
    (∀ (l : Nat) (p q : Nat × Nat), P[l]? = some p → P[l+1]? = some q → stepDist p q = 1)

def IsFreePath (grid : Grid) (m n : Nat) : Prop :=
  ∃ P : List (Nat × Nat),
    P ≠ [] ∧
    P.head? = some (0, 0) ∧
    P.getLast? = some (m - 1, n - 1) ∧
    (∀ p ∈ P, p.1 < m ∧ p.2 < n ∧ cellValue grid p.1 p.2 = 0) ∧
    (∀ (l : Nat) (p q : Nat × Nat), P[l]? = some p → P[l+1]? = some q → stepDist p q = 1)

/-- Whenever the function returns a result r, r is the minimum, over all subsets R of the obstacle set O = {(i,j) | 0 <= i < m, 0 <= j < n, grid[i][j] = 1}, of |R| such that (0,0) and (m-1,n-1) are connected in the graph whose vertices are all cells (i,j) with 0 <= i < m and 0 <= j < n and (grid[i][j] = 0 or (i,j) in R), with an edge between two vertices exactly when they differ by 1 in exactly one coordinate. Equivalently, r is the minimum number of obstacle cells that must be removed so that an orthogonal path exists from the upper-left corner to the lower-right corner.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m * n >= 2, m <= 100000, n <= 100000, m * n <= 100000, grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n, and grid[0][0] = grid[m-1][n-1] = 0. -/
theorem spec_1 (grid : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (r : Std.I64) (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r) :
    ∃ R : Finset (Nat × Nat),
      R ⊆ obstacleCells grid m n ∧
      CornersConnected grid m n R ∧
      (R.card : Int) = r.val ∧
      ∀ R' : Finset (Nat × Nat),
        R' ⊆ obstacleCells grid m n → CornersConnected grid m n R' → r.val ≤ (R'.card : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (r : Std.I64) (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r), ∃ R : Finset (Nat × Nat),
      R ⊆ obstacleCells grid m n ∧
      CornersConnected grid m n R ∧
      (R.card : Int) = r.val ∧
      ∀ R' : Finset (Nat × Nat),
        R' ⊆ obstacleCells grid m n → CornersConnected grid m n R' → r.val ≤ (R'.card : Int)) := by
  sorry

/-- For every such grid, the function returns a result r; it does not fail, panic, overflow, or perform an out-of-bounds access.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m * n >= 2, m <= 100000, n <= 100000, m * n <= 100000, grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n, and grid[0][0] = grid[m-1][n-1] = 0. -/
theorem spec_2 (grid : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0) :
    ∃ r : Std.I64, Aegis.MinimumObstacles.minimum_obstacles grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0), ∃ r : Std.I64, Aegis.MinimumObstacles.minimum_obstacles grid = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= min(m + n - 3, |O|), where O = {(i,j) | 0 <= i < m, 0 <= j < n, grid[i][j] = 1}.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m * n >= 2, m <= 100000, n <= 100000, m * n <= 100000, grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n, and grid[0][0] = grid[m-1][n-1] = 0. -/
theorem spec_3 (grid : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (r : Std.I64) (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r) :
    0 ≤ r.val ∧ r.val ≤ min ((m + n - 3 : Nat) : Int) ((obstacleCells grid m n).card : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (r : Std.I64) (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r), 0 ≤ r.val ∧ r.val ≤ min ((m + n - 3 : Nat) : Int) ((obstacleCells grid m n).card : Int)) := by
  sorry

/-- Whenever the function returns a result r, there exists a finite sequence P = (p_0, ..., p_k) of cells with k >= 0, p_0 = (0,0), p_k = (m-1,n-1), each p_l = (i_l,j_l) satisfying 0 <= i_l < m and 0 <= j_l < n, and |i_{l+1}-i_l| + |j_{l+1}-j_l| = 1 for every 0 <= l < k, such that the number of distinct cells of P whose grid value is 1 is exactly r.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m * n >= 2, m <= 100000, n <= 100000, m * n <= 100000, grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n, and grid[0][0] = grid[m-1][n-1] = 0. -/
theorem spec_4 (grid : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (r : Std.I64) (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r) :
    ∃ P : List (Nat × Nat), IsGridPath m n P ∧ (pathObstacleCount grid P : Int) = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (r : Std.I64) (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r), ∃ P : List (Nat × Nat), IsGridPath m n P ∧ (pathObstacleCount grid P : Int) = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every finite sequence P = (p_0, ..., p_k) of cells with k >= 0, p_0 = (0,0), p_k = (m-1,n-1), each p_l = (i_l,j_l) satisfying 0 <= i_l < m and 0 <= j_l < n, and |i_{l+1}-i_l| + |j_{l+1}-j_l| = 1 for every 0 <= l < k, the number of distinct cells of P whose grid value is 1 is at least r.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m * n >= 2, m <= 100000, n <= 100000, m * n <= 100000, grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n, and grid[0][0] = grid[m-1][n-1] = 0. -/
theorem spec_5 (grid : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (r : Std.I64) (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r) :
    ∀ P : List (Nat × Nat), IsGridPath m n P → r.val ≤ (pathObstacleCount grid P : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (r : Std.I64) (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r), ∀ P : List (Nat × Nat), IsGridPath m n P → r.val ≤ (pathObstacleCount grid P : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there exists a finite sequence P = (p_0, ..., p_k) of cells with k >= 0, p_0 = (0,0), p_k = (m-1,n-1), each p_l = (i_l,j_l) satisfying 0 <= i_l < m and 0 <= j_l < n, |i_{l+1}-i_l| + |j_{l+1}-j_l| = 1 for every 0 <= l < k, and grid[i_l][j_l] = 0 for every 0 <= l <= k.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m * n >= 2, m <= 100000, n <= 100000, m * n <= 100000, grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n, and grid[0][0] = grid[m-1][n-1] = 0. -/
theorem spec_6 (grid : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (r : Std.I64) (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r) :
    (r.val = 0 ↔ IsFreePath grid m n) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (r : Std.I64) (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r), (r.val = 0 ↔ IsFreePath grid m n)) := by
  sorry

/-- Whenever the function returns a result r: if m = 1, then r equals the number of indices j with 0 <= j < n and grid[0][j] = 1; if n = 1, then r equals the number of indices i with 0 <= i < m and grid[i][0] = 1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m * n >= 2, m <= 100000, n <= 100000, m * n <= 100000, grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n, and grid[0][0] = grid[m-1][n-1] = 0. -/
theorem spec_7 (grid : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (r : Std.I64) (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r) :
    (m = 1 → r.val = (((Finset.range n).filter (fun j => cellValue grid 0 j = 1)).card : Int)) ∧
    (n = 1 → r.val = (((Finset.range m).filter (fun i => cellValue grid i 0 = 1)).card : Int)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (r : Std.I64) (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r), (m = 1 → r.val = (((Finset.range n).filter (fun j => cellValue grid 0 j = 1)).card : Int)) ∧
    (n = 1 → r.val = (((Finset.range m).filter (fun i => cellValue grid i 0 = 1)).card : Int))) := by
  sorry

/-- Whenever the function returns a result r, r = m + n - 3.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m * n >= 2, m <= 100000, n <= 100000, m * n <= 100000, grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n, grid[0][0] = grid[m-1][n-1] = 0, and in addition grid[i][j] = 1 for every cell (i,j) other than (0,0) and (m-1,n-1). -/
theorem spec_8 (grid : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (hobst : ∀ i j, i < m → j < n → ¬ (i = 0 ∧ j = 0) → ¬ (i = m - 1 ∧ j = n - 1) →
      cellValue grid i j = 1)
    (r : Std.I64) (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r) :
    r.val = ((m + n - 3 : Nat) : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (hobst : ∀ i j, i < m → j < n → ¬ (i = 0 ∧ j = 0) → ¬ (i = m - 1 ∧ j = n - 1) →
      cellValue grid i j = 1)
    (r : Std.I64) (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r), r.val = ((m + n - 3 : Nat) : Int)) := by
  sorry

/-- Whenever minimum_obstacles(grid) returns r and minimum_obstacles(gridT) returns rT, r = rT.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m * n >= 2, m <= 100000, n <= 100000, m * n <= 100000, grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n, and grid[0][0] = grid[m-1][n-1] = 0. Let gridT be the n x m grid defined by gridT[j][i] = grid[i][j] for 0 <= i < m and 0 <= j < n; gridT is also a well-formed obstacle grid. -/
theorem spec_9 (grid gridT : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (hgridT : IsObstacleGrid gridT n m)
    (htrans : ∀ i j, i < m → j < n → cellValue gridT j i = cellValue grid i j)
    (r rT : Std.I64)
    (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r)
    (hrT : Aegis.MinimumObstacles.minimum_obstacles gridT = ok rT) :
    r.val = rT.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid gridT : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (hgridT : IsObstacleGrid gridT n m)
    (htrans : ∀ i j, i < m → j < n → cellValue gridT j i = cellValue grid i j)
    (r rT : Std.I64)
    (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r)
    (hrT : Aegis.MinimumObstacles.minimum_obstacles gridT = ok rT), r.val = rT.val) := by
  sorry

/-- Whenever minimum_obstacles(grid) returns r and minimum_obstacles(gridR) returns rR, r = rR.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m * n >= 2, m <= 100000, n <= 100000, m * n <= 100000, grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n, and grid[0][0] = grid[m-1][n-1] = 0. Let gridR be the m x n grid defined by gridR[i][j] = grid[m-1-i][n-1-j] for 0 <= i < m and 0 <= j < n; gridR is also a well-formed obstacle grid. -/
theorem spec_10 (grid gridR : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (hgridR : IsObstacleGrid gridR m n)
    (hrot : ∀ i j, i < m → j < n → cellValue gridR i j = cellValue grid (m - 1 - i) (n - 1 - j))
    (r rR : Std.I64)
    (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r)
    (hrR : Aegis.MinimumObstacles.minimum_obstacles gridR = ok rR) :
    r.val = rR.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid gridR : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (hgridR : IsObstacleGrid gridR m n)
    (hrot : ∀ i j, i < m → j < n → cellValue gridR i j = cellValue grid (m - 1 - i) (n - 1 - j))
    (r rR : Std.I64)
    (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r)
    (hrR : Aegis.MinimumObstacles.minimum_obstacles gridR = ok rR), r.val = rR.val) := by
  sorry

/-- Whenever minimum_obstacles(g) returns r_g and minimum_obstacles(h) returns r_h, r_g <= r_h.
  Preconditions: Let g and h be two well-formed obstacle grids with the same dimensions m x n: m >= 1, n >= 1, m * n >= 2, m <= 100000, n <= 100000, m * n <= 100000, all entries are 0 or 1, g[0][0] = g[m-1][n-1] = 0, h[0][0] = h[m-1][n-1] = 0, and g[i][j] <= h[i][j] for all 0 <= i < m and 0 <= j < n. -/
theorem spec_11 (g h : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hg : IsObstacleGrid g m n) (hh : IsObstacleGrid h m n)
    (hgstart : cellValue g 0 0 = 0) (hgend : cellValue g (m - 1) (n - 1) = 0)
    (hhstart : cellValue h 0 0 = 0) (hhend : cellValue h (m - 1) (n - 1) = 0)
    (hle : ∀ i j, i < m → j < n → cellValue g i j ≤ cellValue h i j)
    (r_g r_h : Std.I64)
    (hr_g : Aegis.MinimumObstacles.minimum_obstacles g = ok r_g)
    (hr_h : Aegis.MinimumObstacles.minimum_obstacles h = ok r_h) :
    r_g.val ≤ r_h.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (g h : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hg : IsObstacleGrid g m n) (hh : IsObstacleGrid h m n)
    (hgstart : cellValue g 0 0 = 0) (hgend : cellValue g (m - 1) (n - 1) = 0)
    (hhstart : cellValue h 0 0 = 0) (hhend : cellValue h (m - 1) (n - 1) = 0)
    (hle : ∀ i j, i < m → j < n → cellValue g i j ≤ cellValue h i j)
    (r_g r_h : Std.I64)
    (hr_g : Aegis.MinimumObstacles.minimum_obstacles g = ok r_g)
    (hr_h : Aegis.MinimumObstacles.minimum_obstacles h = ok r_h), r_g.val ≤ r_h.val) := by
  sorry

/-- Whenever the function returns a result r, r = min(grid[0][1], grid[1][0]).
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m = 2, n = 2, grid[i][j] is either 0 or 1 for all 0 <= i < 2 and 0 <= j < 2, and grid[0][0] = grid[1][1] = 0. -/
theorem spec_12 (grid : Grid)
    (hgrid : IsObstacleGrid grid 2 2)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid 1 1 = 0)
    (r : Std.I64) (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r) :
    r.val = min (cellValue grid 0 1) (cellValue grid 1 0) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid : Grid)
    (hgrid : IsObstacleGrid grid 2 2)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid 1 1 = 0)
    (r : Std.I64) (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r), r.val = min (cellValue grid 0 1) (cellValue grid 1 0)) := by
  sorry

/-- Whenever the function returns a result r, r is the minimum, over all finite sequences P = (p_0, ..., p_k) of cells with k >= 0, p_0 = (0,0), p_k = (m-1,n-1), each p_l = (i_l,j_l) satisfying 0 <= i_l < m and 0 <= j_l < n, and |i_{l+1}-i_l| + |j_{l+1}-j_l| = 1 for every 0 <= l < k, of the number of distinct cells of P whose grid value is 1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m * n >= 2, m <= 100000, n <= 100000, m * n <= 100000, grid[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n, and grid[0][0] = grid[m-1][n-1] = 0. -/
theorem spec_13 (grid : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (r : Std.I64) (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r) :
    (∃ P : List (Nat × Nat), IsGridPath m n P ∧ (pathObstacleCount grid P : Int) = r.val) ∧
    ∀ P : List (Nat × Nat), IsGridPath m n P → r.val ≤ (pathObstacleCount grid P : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid : Grid) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hgrid : IsObstacleGrid grid m n)
    (hsize : 2 ≤ m * n) (hmle : m ≤ 100000) (hnle : n ≤ 100000) (hprodle : m * n ≤ 100000)
    (hstart : cellValue grid 0 0 = 0) (hend : cellValue grid (m - 1) (n - 1) = 0)
    (r : Std.I64) (hr : Aegis.MinimumObstacles.minimum_obstacles grid = ok r), (∃ P : List (Nat × Nat), IsGridPath m n P ∧ (pathObstacleCount grid P : Int) = r.val) ∧
    ∀ P : List (Nat × Nat), IsGridPath m n P → r.val ≤ (pathObstacleCount grid P : Int)) := by
  sorry

end AegisSpec.MinimumObstacles
