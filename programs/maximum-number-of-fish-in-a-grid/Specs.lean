import Aegis.FindMaxFish.Code.Funs

/-!
# Specifications of `Aegis.FindMaxFish.find_max_fish`

LeetCode problem `maximum-number-of-fish-in-a-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindMaxFish

def gridVals (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  grid.val.map (fun row => row.val.map (fun v => v.val))

def cellVal (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Option Int :=
  match (gridVals grid)[i]? with
  | some row => row[j]?
  | none => none

def cellValD (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  (cellVal grid i j).getD 0

def WellFormed (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
  1 ≤ m ∧ m ≤ 10 ∧ 1 ≤ n ∧ n ≤ 10 ∧
  m = (Slice.len grid).val ∧
  (∀ i, i < m → ∃ row : List Int, (gridVals grid)[i]? = some row ∧ row.length = n) ∧
  (∀ i j v, i < m → j < n → cellVal grid i j = some v → 0 ≤ v ∧ v ≤ 10)

def IsWater (grid : Slice (alloc.vec.Vec Std.I64)) (m n i j : Nat) : Prop :=
  i < m ∧ j < n ∧ ∃ v : Int, cellVal grid i j = some v ∧ 0 < v

def EdgeAdj (p q : Nat × Nat) : Prop :=
  (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨
  (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1))

inductive Reach (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) :
    Nat × Nat → Nat × Nat → Prop where
  | refl {p : Nat × Nat} (hp : IsWater grid m n p.1 p.2) : Reach grid m n p p
  | step {p q r : Nat × Nat} (h : Reach grid m n p q) (hadj : EdgeAdj q r)
      (hr : IsWater grid m n r.1 r.2) : Reach grid m n p r

def cells (m n : Nat) : List (Nat × Nat) :=
  (List.range m).flatMap (fun i => (List.range n).map (fun j => (i, j)))

def sumCells (grid : Slice (alloc.vec.Vec Std.I64)) (cs : List (Nat × Nat)) : Int :=
  cs.foldr (fun c acc => cellValD grid c.1 c.2 + acc) 0

def totalSum (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Int :=
  sumCells grid (cells m n)

noncomputable def waterSum (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Int := by
  classical
  exact sumCells grid ((cells m n).filter (fun c => IsWater grid m n c.1 c.2))

noncomputable def compSum (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (p : Nat × Nat) : Int := by
  classical
  exact sumCells grid ((cells m n).filter (fun c => Reach grid m n p c))

def rowSegSum (grid : Slice (alloc.vec.Vec Std.I64)) (r l u : Nat) : Int :=
  sumCells grid ((List.range (u + 1 - l)).map (fun t => (r, l + t)))

def colSegSum (grid : Slice (alloc.vec.Vec Std.I64)) (c l u : Nat) : Int :=
  sumCells grid ((List.range (u + 1 - l)).map (fun t => (l + t, c)))

def IsMaxPosIntervalRow (grid : Slice (alloc.vec.Vec Std.I64)) (m n r l u : Nat) : Prop :=
  r < m ∧ l ≤ u ∧ u < n ∧
  (∀ k, l ≤ k → k ≤ u → 0 < cellValD grid r k) ∧
  (l = 0 ∨ cellValD grid r (l - 1) = 0) ∧
  (u = n - 1 ∨ cellValD grid r (u + 1) = 0)

def IsMaxPosIntervalCol (grid : Slice (alloc.vec.Vec Std.I64)) (m n c l u : Nat) : Prop :=
  c < n ∧ l ≤ u ∧ u < m ∧
  (∀ k, l ≤ k → k ≤ u → 0 < cellValD grid k c) ∧
  (l = 0 ∨ cellValD grid (l - 1) c = 0) ∧
  (u = m - 1 ∨ cellValD grid (u + 1) c = 0)

def IsTranspose (grid gridT : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
  (gridVals gridT).length = n ∧
  (∀ j, j < n → ∃ row : List Int, (gridVals gridT)[j]? = some row ∧ row.length = m) ∧
  (∀ i j, i < m → j < n → cellVal gridT j i = cellVal grid i j)

def IsRot180 (grid gridR : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
  (gridVals gridR).length = m ∧
  (∀ i, i < m → ∃ row : List Int, (gridVals gridR)[i]? = some row ∧ row.length = n) ∧
  (∀ i j, i < m → j < n → cellVal gridR i j = cellVal grid (m - 1 - i) (n - 1 - j))

/-- The function returns a result r equal to the maximum number of fish catchable from one connected water region. A water cell is a cell (i,j) with grid[i][j] > 0. Two water cells are edge-adjacent if they differ by 1 in exactly one coordinate and are equal in the other; the water component of a water cell p is the set of all water cells reachable from p by a finite sequence of edge-adjacent moves. If grid has no water cell, then r = 0. Otherwise, r is the largest value of sum_{(i,j) in C} grid[i][j] over all water components C of grid; equivalently, there exists a water cell p whose water component has sum r, and every water cell q has water-component sum at most r.
  Preconditions: Let m = len(grid). The grid is non-empty and rectangular: 1 <= m <= 10, every row has the same length n with 1 <= n <= 10, so len(grid[i]) = n for all 0 <= i < m, and 0 <= grid[i][j] <= 10 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n) :
    ∃ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      (((¬ ∃ p : Nat × Nat, IsWater grid m n p.1 p.2) ∧ r.val = 0) ∨
        ((∃ p : Nat × Nat, IsWater grid m n p.1 p.2 ∧ compSum grid m n p = r.val) ∧
          (∀ q : Nat × Nat, IsWater grid m n q.1 q.2 →
            compSum grid m n q ≤ r.val))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n), ∃ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      (((¬ ∃ p : Nat × Nat, IsWater grid m n p.1 p.2) ∧ r.val = 0) ∨
        ((∃ p : Nat × Nat, IsWater grid m n p.1 p.2 ∧ compSum grid m n p = r.val) ∧
          (∀ q : Nat × Nat, IsWater grid m n q.1 q.2 →
            compSum grid m n q ≤ r.val)))) := by
  sorry

/-- For every grid satisfying the preconditions, find_max_fish returns a result; it does not fail, panic, overflow, or go out of bounds.
  Preconditions: Let m = len(grid). The grid is non-empty and rectangular: 1 <= m <= 10, every row has the same length n with 1 <= n <= 10, so len(grid[i]) = n for all 0 <= i < m, and 0 <= grid[i][j] <= 10 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n) :
    ∃ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n), ∃ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r) := by
  sorry

/-- The function returns a result r with 0 <= r <= sum_{i=0}^{m-1} sum_{j=0}^{n-1} grid[i][j].
  Preconditions: Let m = len(grid). The grid is non-empty and rectangular: 1 <= m <= 10, every row has the same length n with 1 <= n <= 10, so len(grid[i]) = n for all 0 <= i < m, and 0 <= grid[i][j] <= 10 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n) :
    ∃ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      0 ≤ r.val ∧ r.val ≤ totalSum grid m n := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n), ∃ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      0 ≤ r.val ∧ r.val ≤ totalSum grid m n) := by
  sorry

/-- The function returns a result r, and for every cell (i,j) with 0 <= i < m and 0 <= j < n, grid[i][j] <= r.
  Preconditions: Let m = len(grid). The grid is non-empty and rectangular: 1 <= m <= 10, every row has the same length n with 1 <= n <= 10, so len(grid[i]) = n for all 0 <= i < m, and 0 <= grid[i][j] <= 10 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n) :
    ∃ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      ∀ i j, i < m → j < n → cellValD grid i j ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n), ∃ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      ∀ i j, i < m → j < n → cellValD grid i j ≤ r.val) := by
  sorry

/-- The function returns a result r, and r = 0 if and only if grid[i][j] = 0 for every 0 <= i < m and 0 <= j < n.
  Preconditions: Let m = len(grid). The grid is non-empty and rectangular: 1 <= m <= 10, every row has the same length n with 1 <= n <= 10, so len(grid[i]) = n for all 0 <= i < m, and 0 <= grid[i][j] <= 10 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n) :
    ∃ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      (r.val = 0 ↔ ∀ i, i < m → ∀ j, j < n → cellValD grid i j = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n), ∃ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      (r.val = 0 ↔ ∀ i, i < m → ∀ j, j < n → cellValD grid i j = 0)) := by
  sorry

/-- The function returns a result r equal to the sum of grid[i][j] over all water cells (i,j) of the grid.
  Preconditions: Let m = len(grid). The grid is non-empty and rectangular: 1 <= m <= 10, every row has the same length n with 1 <= n <= 10, so len(grid[i]) = n for all 0 <= i < m, and 0 <= grid[i][j] <= 10 for all 0 <= i < m and 0 <= j < n. Also, there is at least one water cell (a cell with positive value), and all water cells lie in a single water component, where two water cells are edge-adjacent if they differ by 1 in exactly one coordinate and are equal in the other. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n)
    (hne : ∃ p : Nat × Nat, IsWater grid m n p.1 p.2)
    (hconn : ∃ p : Nat × Nat, IsWater grid m n p.1 p.2 ∧
      ∀ q : Nat × Nat, IsWater grid m n q.1 q.2 → Reach grid m n p q) :
    ∃ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      r.val = waterSum grid m n := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n)
    (hne : ∃ p : Nat × Nat, IsWater grid m n p.1 p.2)
    (hconn : ∃ p : Nat × Nat, IsWater grid m n p.1 p.2 ∧
      ∀ q : Nat × Nat, IsWater grid m n q.1 q.2 → Reach grid m n p q), ∃ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      r.val = waterSum grid m n) := by
  sorry

/-- The function returns a result r. Call an interval [l,u] of column indices a maximal positive interval if 0 <= l <= u < n, grid[0][k] > 0 for every k with l <= k <= u, either l = 0 or grid[0][l-1] = 0, and either u = n-1 or grid[0][u+1] = 0. Then r is the maximum of the sums sum_{k=l}^{u} grid[0][k] over all maximal positive intervals [l,u], with the convention that this maximum is 0 if there is no maximal positive interval.
  Preconditions: Let m = len(grid). The grid is non-empty and rectangular: 1 <= m <= 10, every row has the same length n with 1 <= n <= 10, so len(grid[i]) = n for all 0 <= i < m, and 0 <= grid[i][j] <= 10 for all 0 <= i < m and 0 <= j < n. Additionally m = 1. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n) (hm : m = 1) :
    ∃ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      ((∃ l u, IsMaxPosIntervalRow grid m n 0 l u) →
        (∃ l u, IsMaxPosIntervalRow grid m n 0 l u ∧ rowSegSum grid 0 l u = r.val) ∧
        (∀ l u, IsMaxPosIntervalRow grid m n 0 l u → rowSegSum grid 0 l u ≤ r.val)) ∧
      ((¬ ∃ l u, IsMaxPosIntervalRow grid m n 0 l u) → r.val = 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n) (hm : m = 1), ∃ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      ((∃ l u, IsMaxPosIntervalRow grid m n 0 l u) →
        (∃ l u, IsMaxPosIntervalRow grid m n 0 l u ∧ rowSegSum grid 0 l u = r.val) ∧
        (∀ l u, IsMaxPosIntervalRow grid m n 0 l u → rowSegSum grid 0 l u ≤ r.val)) ∧
      ((¬ ∃ l u, IsMaxPosIntervalRow grid m n 0 l u) → r.val = 0)) := by
  sorry

/-- The function returns a result r. Call an interval [l,u] of row indices a maximal positive interval if 0 <= l <= u < m, grid[k][0] > 0 for every k with l <= k <= u, either l = 0 or grid[l-1][0] = 0, and either u = m-1 or grid[u+1][0] = 0. Then r is the maximum of the sums sum_{k=l}^{u} grid[k][0] over all maximal positive intervals [l,u], with the convention that this maximum is 0 if there is no maximal positive interval.
  Preconditions: Let m = len(grid). The grid is non-empty and rectangular: 1 <= m <= 10, every row has the same length n with 1 <= n <= 10, so len(grid[i]) = n for all 0 <= i < m, and 0 <= grid[i][j] <= 10 for all 0 <= i < m and 0 <= j < n. Additionally n = 1. -/
theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n) (hn : n = 1) :
    ∃ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      ((∃ l u, IsMaxPosIntervalCol grid m n 0 l u) →
        (∃ l u, IsMaxPosIntervalCol grid m n 0 l u ∧ colSegSum grid 0 l u = r.val) ∧
        (∀ l u, IsMaxPosIntervalCol grid m n 0 l u → colSegSum grid 0 l u ≤ r.val)) ∧
      ((¬ ∃ l u, IsMaxPosIntervalCol grid m n 0 l u) → r.val = 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n) (hn : n = 1), ∃ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      ((∃ l u, IsMaxPosIntervalCol grid m n 0 l u) →
        (∃ l u, IsMaxPosIntervalCol grid m n 0 l u ∧ colSegSum grid 0 l u = r.val) ∧
        (∀ l u, IsMaxPosIntervalCol grid m n 0 l u → colSegSum grid 0 l u ≤ r.val)) ∧
      ((¬ ∃ l u, IsMaxPosIntervalCol grid m n 0 l u) → r.val = 0)) := by
  sorry

/-- The function returns a result r for grid. Define gridT by gridT[j][i] = grid[i][j] for 0 <= i < m and 0 <= j < n. Then find_max_fish(gridT) returns a result rT with rT = r.
  Preconditions: Let m = len(grid). The grid is non-empty and rectangular: 1 <= m <= 10, every row has the same length n with 1 <= n <= 10, so len(grid[i]) = n for all 0 <= i < m, and 0 <= grid[i][j] <= 10 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_9 (grid gridT : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n) (hT : IsTranspose grid gridT m n) :
    ∃ r rT : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      Aegis.FindMaxFish.find_max_fish gridT = ok rT ∧ rT.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid gridT : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n) (hT : IsTranspose grid gridT m n), ∃ r rT : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      Aegis.FindMaxFish.find_max_fish gridT = ok rT ∧ rT.val = r.val) := by
  sorry

/-- The function returns a result r for grid. Define gridR by gridR[i][j] = grid[m-1-i][n-1-j] for 0 <= i < m and 0 <= j < n. Then find_max_fish(gridR) returns a result rR with rR = r.
  Preconditions: Let m = len(grid). The grid is non-empty and rectangular: 1 <= m <= 10, every row has the same length n with 1 <= n <= 10, so len(grid[i]) = n for all 0 <= i < m, and 0 <= grid[i][j] <= 10 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_10 (grid gridR : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n) (hR : IsRot180 grid gridR m n) :
    ∃ r rR : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      Aegis.FindMaxFish.find_max_fish gridR = ok rR ∧ rR.val = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid gridR : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n) (hR : IsRot180 grid gridR m n), ∃ r rR : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      Aegis.FindMaxFish.find_max_fish gridR = ok rR ∧ rR.val = r.val) := by
  sorry

/-- The call find_max_fish(grid) returns a result r, the call find_max_fish(h) returns a result r', and r <= r'.
  Preconditions: Let m = len(grid). Both grid and h are non-empty rectangular m x n matrices with 1 <= m <= 10 and 1 <= n <= 10, all entries lie in the range 0 to 10, and grid[i][j] <= h[i][j] for every 0 <= i < m and 0 <= j < n. -/
theorem spec_11 (grid h : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hg : WellFormed grid m n) (hh : WellFormed h m n)
    (hle : ∀ i j, i < m → j < n → cellValD grid i j ≤ cellValD h i j) :
    ∃ r r' : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      Aegis.FindMaxFish.find_max_fish h = ok r' ∧ r.val ≤ r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid h : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hg : WellFormed grid m n) (hh : WellFormed h m n)
    (hle : ∀ i j, i < m → j < n → cellValD grid i j ≤ cellValD h i j), ∃ r r' : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      Aegis.FindMaxFish.find_max_fish h = ok r' ∧ r.val ≤ r'.val) := by
  sorry

/-- The function returns a result r, and there exists a water cell (r0,c0) with 0 <= r0 < m, 0 <= c0 < n, and grid[r0][c0] > 0 such that r equals the sum of grid[i][j] over all water cells (i,j) reachable from (r0,c0) by a finite sequence of edge-adjacent water cells, including (r0,c0) itself. Two water cells are edge-adjacent if they differ by 1 in exactly one coordinate and are equal in the other.
  Preconditions: Let m = len(grid). The grid is non-empty and rectangular: 1 <= m <= 10, every row has the same length n with 1 <= n <= 10, so len(grid[i]) = n for all 0 <= i < m, and 0 <= grid[i][j] <= 10 for all 0 <= i < m and 0 <= j < n. Also, there is at least one water cell (a cell with positive value). -/
theorem spec_12 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n) (hne : ∃ p : Nat × Nat, IsWater grid m n p.1 p.2) :
    ∃ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      ∃ p : Nat × Nat, IsWater grid m n p.1 p.2 ∧ compSum grid m n p = r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n) (hne : ∃ p : Nat × Nat, IsWater grid m n p.1 p.2), ∃ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r ∧
      ∃ p : Nat × Nat, IsWater grid m n p.1 p.2 ∧ compSum grid m n p = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every cell (r0,c0) with 0 <= r0 < m, 0 <= c0 < n, and grid[r0][c0] > 0, the sum of grid[i][j] over all water cells (i,j) reachable from (r0,c0) by a finite sequence of edge-adjacent water cells, including (r0,c0) itself, is at most r. Two water cells are edge-adjacent if they differ by 1 in exactly one coordinate and are equal in the other.
  Preconditions: Let m = len(grid). The grid is non-empty and rectangular: 1 <= m <= 10, every row has the same length n with 1 <= n <= 10, so len(grid[i]) = n for all 0 <= i < m, and 0 <= grid[i][j] <= 10 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_13 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n) :
    ∀ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r →
      ∀ p : Nat × Nat, IsWater grid m n p.1 p.2 → compSum grid m n p ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : WellFormed grid m n), ∀ r : Std.I64, Aegis.FindMaxFish.find_max_fish grid = ok r →
      ∀ p : Nat × Nat, IsWater grid m n p.1 p.2 → compSum grid m n p ≤ r.val) := by
  sorry

end AegisSpec.FindMaxFish
