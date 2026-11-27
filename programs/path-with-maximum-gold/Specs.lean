import Aegis.GetMaximumGold.Code.Funs

/-!
# Specifications of `Aegis.GetMaximumGold.get_maximum_gold`

LeetCode problem `path-with-maximum-gold`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetMaximumGold

def cellVal (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  match grid.val[i]? with
  | none => 0
  | some row =>
    match row.val[j]? with
    | none => 0
    | some x => x.val

def cellList (m n : Nat) : List (Nat × Nat) :=
  (List.range m).flatMap fun i => (List.range n).map fun j => (i, j)

def Rect (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
  grid.val.length = m ∧ (∀ row ∈ grid.val, row.val.length = n) ∧
    1 ≤ m ∧ m ≤ 15 ∧ 1 ≤ n ∧ n ≤ 15

def CellsInRange (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (lo hi : Int) : Prop :=
  ∀ i j, i < m → j < n → lo ≤ cellVal grid i j ∧ cellVal grid i j ≤ hi

def positiveCells (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : List (Nat × Nat) :=
  (cellList m n).filter (fun c => decide (0 < cellVal grid c.1 c.2))

def OrthAdj (c c' : Nat × Nat) : Prop :=
  Int.natAbs ((c.1 : Int) - (c'.1 : Int)) + Int.natAbs ((c.2 : Int) - (c'.2 : Int)) = 1

def IsGoldPath (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (p : List (Nat × Nat)) : Prop :=
  (∀ c ∈ p, c.1 < m ∧ c.2 < n ∧ 0 < cellVal grid c.1 c.2) ∧
    p.Nodup ∧
    ∀ t, t + 1 < p.length → OrthAdj (p[t]!) (p[t + 1]!)

def pathValue (grid : Slice (alloc.vec.Vec Std.I64)) (p : List (Nat × Nat)) : Int :=
  (p.map fun c => cellVal grid c.1 c.2).sum

def IsMaxGold (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (r : Int) : Prop :=
  (∀ p, IsGoldPath grid m n p → pathValue grid p ≤ r) ∧
    ∃ p, IsGoldPath grid m n p ∧ pathValue grid p = r

def posSum (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Int :=
  (((cellList m n).map fun c => cellVal grid c.1 c.2).filter fun x => decide (0 < x)).sum

def cellMax (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Int :=
  ((cellList m n).map fun c => cellVal grid c.1 c.2).foldr max 0

def IsHRefl (grid gridH : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
  gridH.val.length = m ∧ (∀ row ∈ gridH.val, row.val.length = n) ∧
    ∀ i j, i < m → j < n → cellVal gridH i j = cellVal grid i (n - 1 - j)

def IsTranspose (grid gridT : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
  gridT.val.length = n ∧ (∀ row ∈ gridT.val, row.val.length = m) ∧
    ∀ i j, i < m → j < n → cellVal gridT j i = cellVal grid i j

/-- Whenever get_maximum_gold returns a result r, r equals the maximum value over all valid gold paths, where a valid gold path is a finite sequence p_0,...,p_{k-1} of cells (k >= 0) such that each p_t=(i_t,j_t) satisfies 0<=i_t<m, 0<=j_t<n and grid[i_t][j_t]>0, all p_t are distinct, and for each 0<=t<k-1 the cells p_t and p_{t+1} are orthogonally adjacent (|i_{t+1}-i_t|+|j_{t+1}-j_t|=1); its value is sum_{t=0}^{k-1} grid[i_t][j_t], and the empty path has value 0.
  Preconditions: grid is rectangular: m = len(grid), n = len(grid[0]), 1 <= m,n <= 15; for every i with 0 <= i < m and every j with 0 <= j < n, 0 <= grid[i][j] <= 100; at most 25 pairs (i,j) satisfy grid[i][j] > 0. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hgrid : Rect grid m n) (hrange : CellsInRange grid m n 0 100)
    (hpos : (positiveCells grid m n).length ≤ 25) (r : Std.I64)
    (hres : Aegis.GetMaximumGold.get_maximum_gold grid = ok r) :
    IsMaxGold grid m n r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hgrid : Rect grid m n) (hrange : CellsInRange grid m n 0 100)
    (hpos : (positiveCells grid m n).length ≤ 25) (r : Std.I64)
    (hres : Aegis.GetMaximumGold.get_maximum_gold grid = ok r), IsMaxGold grid m n r.val) := by
  sorry

/-- For every grid satisfying the preconditions, get_maximum_gold returns a result r; it does not fail because of arithmetic overflow, out-of-bounds indexing, or panic.
  Preconditions: grid is rectangular: m = len(grid), n = len(grid[0]), 1 <= m,n <= 15; for every i with 0 <= i < m and every j with 0 <= j < n, 0 <= grid[i][j] <= 100; at most 25 pairs (i,j) satisfy grid[i][j] > 0. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hgrid : Rect grid m n) (hrange : CellsInRange grid m n 0 100)
    (hpos : (positiveCells grid m n).length ≤ 25) :
    ∃ r : Std.I64, Aegis.GetMaximumGold.get_maximum_gold grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hgrid : Rect grid m n) (hrange : CellsInRange grid m n 0 100)
    (hpos : (positiveCells grid m n).length ≤ 25), ∃ r : Std.I64, Aegis.GetMaximumGold.get_maximum_gold grid = ok r) := by
  sorry

/-- Whenever get_maximum_gold returns r, there exists a valid gold path in grid whose value is exactly r. A valid gold path is a pairwise-distinct sequence of in-bounds cells with positive grid values, consecutive cells orthogonally adjacent; the empty path is allowed and has value 0.
  Preconditions: grid is rectangular: m = len(grid), n = len(grid[0]), 1 <= m,n <= 15; for every i with 0 <= i < m and every j with 0 <= j < n, 0 <= grid[i][j] <= 100; at most 25 pairs (i,j) satisfy grid[i][j] > 0. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hgrid : Rect grid m n) (hrange : CellsInRange grid m n 0 100)
    (hpos : (positiveCells grid m n).length ≤ 25) (r : Std.I64)
    (hres : Aegis.GetMaximumGold.get_maximum_gold grid = ok r) :
    ∃ p : List (Nat × Nat), IsGoldPath grid m n p ∧ pathValue grid p = r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hgrid : Rect grid m n) (hrange : CellsInRange grid m n 0 100)
    (hpos : (positiveCells grid m n).length ≤ 25) (r : Std.I64)
    (hres : Aegis.GetMaximumGold.get_maximum_gold grid = ok r), ∃ p : List (Nat × Nat), IsGoldPath grid m n p ∧ pathValue grid p = r.val) := by
  sorry

/-- Whenever get_maximum_gold returns r, every valid gold path in grid has value at most r. A valid gold path is a pairwise-distinct sequence of in-bounds cells with positive grid values, consecutive cells orthogonally adjacent; the empty path is allowed and has value 0.
  Preconditions: grid is rectangular: m = len(grid), n = len(grid[0]), 1 <= m,n <= 15; for every i with 0 <= i < m and every j with 0 <= j < n, 0 <= grid[i][j] <= 100; at most 25 pairs (i,j) satisfy grid[i][j] > 0. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hgrid : Rect grid m n) (hrange : CellsInRange grid m n 0 100)
    (hpos : (positiveCells grid m n).length ≤ 25) (r : Std.I64)
    (hres : Aegis.GetMaximumGold.get_maximum_gold grid = ok r) :
    ∀ p : List (Nat × Nat), IsGoldPath grid m n p → pathValue grid p ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hgrid : Rect grid m n) (hrange : CellsInRange grid m n 0 100)
    (hpos : (positiveCells grid m n).length ≤ 25) (r : Std.I64)
    (hres : Aegis.GetMaximumGold.get_maximum_gold grid = ok r), ∀ p : List (Nat × Nat), IsGoldPath grid m n p → pathValue grid p ≤ r.val) := by
  sorry

/-- Whenever get_maximum_gold returns r, 0 <= r <= sum of grid[i][j] over all cells (i,j) with 0 <= i < m, 0 <= j < n, and grid[i][j] > 0.
  Preconditions: grid is rectangular: m = len(grid), n = len(grid[0]), 1 <= m,n <= 15; for every i with 0 <= i < m and every j with 0 <= j < n, 0 <= grid[i][j] <= 100; at most 25 pairs (i,j) satisfy grid[i][j] > 0. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hgrid : Rect grid m n) (hrange : CellsInRange grid m n 0 100)
    (hpos : (positiveCells grid m n).length ≤ 25) (r : Std.I64)
    (hres : Aegis.GetMaximumGold.get_maximum_gold grid = ok r) :
    0 ≤ r.val ∧ r.val ≤ posSum grid m n := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hgrid : Rect grid m n) (hrange : CellsInRange grid m n 0 100)
    (hpos : (positiveCells grid m n).length ≤ 25) (r : Std.I64)
    (hres : Aegis.GetMaximumGold.get_maximum_gold grid = ok r), 0 ≤ r.val ∧ r.val ≤ posSum grid m n) := by
  sorry

/-- Whenever get_maximum_gold returns r, r >= max { grid[i][j] | 0 <= i < m, 0 <= j < n }, i.e. r is at least the largest cell value in the whole grid (which is 0 if all cells are zero).
  Preconditions: grid is rectangular: m = len(grid), n = len(grid[0]), 1 <= m,n <= 15; for every i with 0 <= i < m and every j with 0 <= j < n, 0 <= grid[i][j] <= 100; at most 25 pairs (i,j) satisfy grid[i][j] > 0. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hgrid : Rect grid m n) (hrange : CellsInRange grid m n 0 100)
    (hpos : (positiveCells grid m n).length ≤ 25) (r : Std.I64)
    (hres : Aegis.GetMaximumGold.get_maximum_gold grid = ok r) :
    cellMax grid m n ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hgrid : Rect grid m n) (hrange : CellsInRange grid m n 0 100)
    (hpos : (positiveCells grid m n).length ≤ 25) (r : Std.I64)
    (hres : Aegis.GetMaximumGold.get_maximum_gold grid = ok r), cellMax grid m n ≤ r.val) := by
  sorry

/-- Whenever get_maximum_gold(grid) returns r and get_maximum_gold(grid2) returns r2, we have r <= r2.
  Preconditions: grid and grid2 are rectangular with the same dimensions m = len(grid)=len(grid2) and n = len(grid[0])=len(grid2[0]), 1 <= m,n <= 15; all cells of both satisfy 0 <= grid[i][j] <= 100 and 0 <= grid2[i][j] <= 100; each grid has at most 25 positive cells; and grid[i][j] <= grid2[i][j] for every i,j. -/
theorem spec_7 (grid grid2 : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hgrid : Rect grid m n) (hgrid2 : Rect grid2 m n)
    (hrange : CellsInRange grid m n 0 100) (hrange2 : CellsInRange grid2 m n 0 100)
    (hpos : (positiveCells grid m n).length ≤ 25)
    (hpos2 : (positiveCells grid2 m n).length ≤ 25)
    (hle : ∀ i j, i < m → j < n → cellVal grid i j ≤ cellVal grid2 i j)
    (r r2 : Std.I64)
    (hres : Aegis.GetMaximumGold.get_maximum_gold grid = ok r)
    (hres2 : Aegis.GetMaximumGold.get_maximum_gold grid2 = ok r2) :
    r.val ≤ r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid grid2 : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hgrid : Rect grid m n) (hgrid2 : Rect grid2 m n)
    (hrange : CellsInRange grid m n 0 100) (hrange2 : CellsInRange grid2 m n 0 100)
    (hpos : (positiveCells grid m n).length ≤ 25)
    (hpos2 : (positiveCells grid2 m n).length ≤ 25)
    (hle : ∀ i j, i < m → j < n → cellVal grid i j ≤ cellVal grid2 i j)
    (r r2 : Std.I64)
    (hres : Aegis.GetMaximumGold.get_maximum_gold grid = ok r)
    (hres2 : Aegis.GetMaximumGold.get_maximum_gold grid2 = ok r2), r.val ≤ r2.val) := by
  sorry

/-- Let gridH be the horizontal reflection of grid: for 0 <= i < m and 0 <= j < n, gridH[i][j] = grid[i][n-1-j]. Whenever get_maximum_gold(grid) returns r and get_maximum_gold(gridH) returns rH, r = rH.
  Preconditions: grid is rectangular: m = len(grid), n = len(grid[0]), 1 <= m,n <= 15; for every i with 0 <= i < m and every j with 0 <= j < n, 0 <= grid[i][j] <= 100; at most 25 pairs (i,j) satisfy grid[i][j] > 0. -/
theorem spec_8 (grid gridH : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hgrid : Rect grid m n) (hh : IsHRefl grid gridH m n)
    (hrange : CellsInRange grid m n 0 100)
    (hpos : (positiveCells grid m n).length ≤ 25)
    (r rH : Std.I64)
    (hres : Aegis.GetMaximumGold.get_maximum_gold grid = ok r)
    (hresH : Aegis.GetMaximumGold.get_maximum_gold gridH = ok rH) :
    r.val = rH.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid gridH : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hgrid : Rect grid m n) (hh : IsHRefl grid gridH m n)
    (hrange : CellsInRange grid m n 0 100)
    (hpos : (positiveCells grid m n).length ≤ 25)
    (r rH : Std.I64)
    (hres : Aegis.GetMaximumGold.get_maximum_gold grid = ok r)
    (hresH : Aegis.GetMaximumGold.get_maximum_gold gridH = ok rH), r.val = rH.val) := by
  sorry

/-- Let gridT be the transpose of grid: gridT has len(gridT) = n and len(gridT[0]) = m, and for 0 <= i < m, 0 <= j < n, gridT[j][i] = grid[i][j]. Whenever get_maximum_gold(grid) returns r and get_maximum_gold(gridT) returns rT, r = rT.
  Preconditions: grid is rectangular: m = len(grid), n = len(grid[0]), 1 <= m,n <= 15; for every i with 0 <= i < m and every j with 0 <= j < n, 0 <= grid[i][j] <= 100; at most 25 pairs (i,j) satisfy grid[i][j] > 0. -/
theorem spec_9 (grid gridT : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hgrid : Rect grid m n) (ht : IsTranspose grid gridT m n)
    (hrange : CellsInRange grid m n 0 100)
    (hpos : (positiveCells grid m n).length ≤ 25)
    (r rT : Std.I64)
    (hres : Aegis.GetMaximumGold.get_maximum_gold grid = ok r)
    (hresT : Aegis.GetMaximumGold.get_maximum_gold gridT = ok rT) :
    r.val = rT.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid gridT : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hgrid : Rect grid m n) (ht : IsTranspose grid gridT m n)
    (hrange : CellsInRange grid m n 0 100)
    (hpos : (positiveCells grid m n).length ≤ 25)
    (r rT : Std.I64)
    (hres : Aegis.GetMaximumGold.get_maximum_gold grid = ok r)
    (hresT : Aegis.GetMaximumGold.get_maximum_gold gridT = ok rT), r.val = rT.val) := by
  sorry

end AegisSpec.GetMaximumGold
