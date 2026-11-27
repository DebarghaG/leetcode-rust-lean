import Aegis.MaxDistance.Code.Funs

/-!
# Specifications of `Aegis.MaxDistance.max_distance`

LeetCode problem `as-far-from-land-as-possible`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxDistance

abbrev Grid := Aeneas.Std.Slice (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)

def gridLen (grid : Grid) : ℕ := grid.val.length

def rowLen (grid : Grid) (i : ℕ) : Option ℕ :=
  (grid.val[i]?).map (fun row => row.val.length)

def cellVal (grid : Grid) (i j : ℕ) : Option ℤ :=
  (grid.val[i]?).bind (fun row => (row.val[j]?).map (fun v => v.val))

def GridPre (grid : Grid) : Prop :=
  1 ≤ gridLen grid ∧
  gridLen grid ≤ 100 ∧
  (∀ i, i < gridLen grid → rowLen grid i = some (gridLen grid)) ∧
  (∀ i j, i < gridLen grid → j < gridLen grid →
    cellVal grid i j = some 0 ∨ cellVal grid i j = some 1)

def IsLand (grid : Grid) (i j : ℕ) : Prop :=
  i < gridLen grid ∧ j < gridLen grid ∧ cellVal grid i j = some 1

def IsWater (grid : Grid) (i j : ℕ) : Prop :=
  i < gridLen grid ∧ j < gridLen grid ∧ cellVal grid i j = some 0

instance decidableIsLand (grid : Grid) (i j : ℕ) : Decidable (IsLand grid i j) := by
  unfold IsLand
  infer_instance

instance decidableIsWater (grid : Grid) (i j : ℕ) : Decidable (IsWater grid i j) := by
  unfold IsWater
  infer_instance

def HasLand (grid : Grid) : Prop := ∃ i j, IsLand grid i j

def HasWater (grid : Grid) : Prop := ∃ i j, IsWater grid i j

def AllZero (grid : Grid) : Prop :=
  ∀ i j, i < gridLen grid → j < gridLen grid → cellVal grid i j = some 0

def AllOne (grid : Grid) : Prop :=
  ∀ i j, i < gridLen grid → j < gridLen grid → cellVal grid i j = some 1

def manhattan (i j i' j' : ℕ) : ℤ :=
  |(i : ℤ) - (i' : ℤ)| + |(j : ℤ) - (j' : ℤ)|

def cells (grid : Grid) : List (ℕ × ℕ) :=
  (List.range (gridLen grid)).flatMap
    (fun i => (List.range (gridLen grid)).map (fun j => (i, j)))

def landDists (grid : Grid) (i j : ℕ) : List ℤ :=
  (cells grid).filterMap
    (fun (p : ℕ × ℕ) =>
      if IsLand grid p.1 p.2 then some (manhattan i j p.1 p.2) else none)

def minLandDist (grid : Grid) (i j : ℕ) : Option ℤ := (landDists grid i j).min?

def waterMinLandDists (grid : Grid) : List ℤ :=
  (cells grid).filterMap
    (fun (p : ℕ × ℕ) =>
      if IsWater grid p.1 p.2 then minLandDist grid p.1 p.2 else none)

def maxWaterMinLand (grid : Grid) : Option ℤ := (waterMinLandDists grid).max?

def IsTranspose (gridT grid : Grid) : Prop :=
  gridLen gridT = gridLen grid ∧
  (∀ i j, i < gridLen grid → j < gridLen grid →
    cellVal gridT i j = cellVal grid j i)

def IsHorizontalFlip (gridH grid : Grid) : Prop :=
  gridLen gridH = gridLen grid ∧
  (∀ i j, i < gridLen grid → j < gridLen grid →
    cellVal gridH i j = cellVal grid i (gridLen grid - 1 - j))

def IsVerticalFlip (gridV grid : Grid) : Prop :=
  gridLen gridV = gridLen grid ∧
  (∀ i j, i < gridLen grid → j < gridLen grid →
    cellVal gridV i j = cellVal grid (gridLen grid - 1 - i) j)

/-- Let n = len(grid). A pair (i,j) is a land cell if 0 <= i < n, 0 <= j < n, and grid[i][j] = 1; it is a water cell if 0 <= i < n, 0 <= j < n, and grid[i][j] = 0. Whenever the function returns a result r, the following holds. If there is no land cell or no water cell, then r = -1. Otherwise, r = max over all water cells (i,j) of min over all land cells (i',j') of (|i - i'| + |j - j'|).
  Preconditions: Let n = len(grid). The grid satisfies: 1 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] = 0 or grid[i][j] = 1. All indices are 0-based. -/
theorem spec_1 (grid : Grid) (r : Aeneas.Std.I64)
    (hpre : GridPre grid)
    (hres : Aegis.MaxDistance.max_distance grid = ok r) :
    ((¬ HasLand grid ∨ ¬ HasWater grid) → r.val = -1) ∧
    (HasLand grid → HasWater grid →
      ∃ m : ℤ, maxWaterMinLand grid = some m ∧ r.val = m) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Grid) (r : Aeneas.Std.I64)
    (hpre : GridPre grid)
    (hres : Aegis.MaxDistance.max_distance grid = ok r), ((¬ HasLand grid ∨ ¬ HasWater grid) → r.val = -1) ∧
    (HasLand grid → HasWater grid →
      ∃ m : ℤ, maxWaterMinLand grid = some m ∧ r.val = m)) := by
  sorry

/-- For every grid satisfying the preconditions, the function returns a result r: the Lean Result is Ok r rather than an error, and no overflow, out-of-bounds access, or panic occurs.
  Preconditions: Let n = len(grid). The grid satisfies: 1 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] = 0 or grid[i][j] = 1. All indices are 0-based. -/
theorem spec_2 (grid : Grid) (hpre : GridPre grid) :
    ∃ r : Aeneas.Std.I64, Aegis.MaxDistance.max_distance grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid), ∃ r : Aeneas.Std.I64, Aegis.MaxDistance.max_distance grid = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 1 <= r.
  Preconditions: Let n = len(grid). The grid satisfies: 1 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] = 0 or grid[i][j] = 1. All indices are 0-based. -/
theorem spec_3 (grid : Grid) (r : Aeneas.Std.I64)
    (hpre : GridPre grid)
    (hres : Aegis.MaxDistance.max_distance grid = ok r) :
    r.val = -1 ∨ 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Grid) (r : Aeneas.Std.I64)
    (hpre : GridPre grid)
    (hres : Aegis.MaxDistance.max_distance grid = ok r), r.val = -1 ∨ 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= 2 * n - 2, where n = len(grid).
  Preconditions: Let n = len(grid). The grid satisfies: 1 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] = 0 or grid[i][j] = 1. All indices are 0-based. -/
theorem spec_4 (grid : Grid) (r : Aeneas.Std.I64)
    (hpre : GridPre grid)
    (hres : Aegis.MaxDistance.max_distance grid = ok r) :
    r.val ≤ 2 * (gridLen grid : ℤ) - 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Grid) (r : Aeneas.Std.I64)
    (hpre : GridPre grid)
    (hres : Aegis.MaxDistance.max_distance grid = ok r), r.val ≤ 2 * (gridLen grid : ℤ) - 2) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if (there is no land cell or there is no water cell). Equivalently, r = -1 if and only if either (for every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] = 0) or (for every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] = 1).
  Preconditions: Let n = len(grid). The grid satisfies: 1 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] = 0 or grid[i][j] = 1. All indices are 0-based. -/
theorem spec_5 (grid : Grid) (r : Aeneas.Std.I64)
    (hpre : GridPre grid)
    (hres : Aegis.MaxDistance.max_distance grid = ok r) :
    (r.val = -1 ↔ (¬ HasLand grid ∨ ¬ HasWater grid)) ∧
    (r.val = -1 ↔ (AllZero grid ∨ AllOne grid)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Grid) (r : Aeneas.Std.I64)
    (hpre : GridPre grid)
    (hres : Aegis.MaxDistance.max_distance grid = ok r), (r.val = -1 ↔ (¬ HasLand grid ∨ ¬ HasWater grid)) ∧
    (r.val = -1 ↔ (AllZero grid ∨ AllOne grid))) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, for every water cell (i,j) with 0 <= i < n, 0 <= j < n, and grid[i][j] = 0, there exists a land cell (i',j') with 0 <= i' < n, 0 <= j' < n, and grid[i'][j'] = 1, such that |i - i'| + |j - j'| <= r.
  Preconditions: Let n = len(grid). The grid satisfies: 1 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] = 0 or grid[i][j] = 1. All indices are 0-based. -/
theorem spec_6 (grid : Grid) (r : Aeneas.Std.I64)
    (hpre : GridPre grid)
    (hres : Aegis.MaxDistance.max_distance grid = ok r)
    (hr : 0 ≤ r.val) :
    ∀ i j, IsWater grid i j →
      ∃ i' j', IsLand grid i' j' ∧ manhattan i j i' j' ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Grid) (r : Aeneas.Std.I64)
    (hpre : GridPre grid)
    (hres : Aegis.MaxDistance.max_distance grid = ok r)
    (hr : 0 ≤ r.val), ∀ i j, IsWater grid i j →
      ∃ i' j', IsLand grid i' j' ∧ manhattan i j i' j' ≤ r.val) := by
  sorry

/-- Let gridT be defined by gridT[i][j] = grid[j][i] for 0 <= i < n and 0 <= j < n. Whenever the function returns a result r on input grid and a result rT on input gridT, r = rT.
  Preconditions: Let n = len(grid). The grid satisfies: 1 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] = 0 or grid[i][j] = 1. All indices are 0-based. -/
theorem spec_7 (grid gridT : Grid) (r rT : Aeneas.Std.I64)
    (hpre : GridPre grid)
    (hT : IsTranspose gridT grid)
    (hres : Aegis.MaxDistance.max_distance grid = ok r)
    (hresT : Aegis.MaxDistance.max_distance gridT = ok rT) :
    r.val = rT.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid gridT : Grid) (r rT : Aeneas.Std.I64)
    (hpre : GridPre grid)
    (hT : IsTranspose gridT grid)
    (hres : Aegis.MaxDistance.max_distance grid = ok r)
    (hresT : Aegis.MaxDistance.max_distance gridT = ok rT), r.val = rT.val) := by
  sorry

/-- Let gridH be defined by gridH[i][j] = grid[i][n - 1 - j] for 0 <= i < n and 0 <= j < n. Whenever the function returns a result r on input grid and a result rH on input gridH, r = rH.
  Preconditions: Let n = len(grid). The grid satisfies: 1 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] = 0 or grid[i][j] = 1. All indices are 0-based. -/
theorem spec_8 (grid gridH : Grid) (r rH : Aeneas.Std.I64)
    (hpre : GridPre grid)
    (hH : IsHorizontalFlip gridH grid)
    (hres : Aegis.MaxDistance.max_distance grid = ok r)
    (hresH : Aegis.MaxDistance.max_distance gridH = ok rH) :
    r.val = rH.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid gridH : Grid) (r rH : Aeneas.Std.I64)
    (hpre : GridPre grid)
    (hH : IsHorizontalFlip gridH grid)
    (hres : Aegis.MaxDistance.max_distance grid = ok r)
    (hresH : Aegis.MaxDistance.max_distance gridH = ok rH), r.val = rH.val) := by
  sorry

/-- Let gridV be defined by gridV[i][j] = grid[n - 1 - i][j] for 0 <= i < n and 0 <= j < n. Whenever the function returns a result r on input grid and a result rV on input gridV, r = rV.
  Preconditions: Let n = len(grid). The grid satisfies: 1 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] = 0 or grid[i][j] = 1. All indices are 0-based. -/
theorem spec_9 (grid gridV : Grid) (r rV : Aeneas.Std.I64)
    (hpre : GridPre grid)
    (hV : IsVerticalFlip gridV grid)
    (hres : Aegis.MaxDistance.max_distance grid = ok r)
    (hresV : Aegis.MaxDistance.max_distance gridV = ok rV) :
    r.val = rV.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid gridV : Grid) (r rV : Aeneas.Std.I64)
    (hpre : GridPre grid)
    (hV : IsVerticalFlip gridV grid)
    (hres : Aegis.MaxDistance.max_distance grid = ok r)
    (hresV : Aegis.MaxDistance.max_distance gridV = ok rV), r.val = rV.val) := by
  sorry

/-- If the function returns a result r on input g and a result r' on input g', then r' <= r.
  Preconditions: For two grids g and g' both satisfying the standard preconditions: let n = len(g); 1 <= n <= 100; for every i with 0 <= i < n, len(g[i]) = n and len(g'[i]) = n; for every i, j with 0 <= i < n and 0 <= j < n, g[i][j] and g'[i][j] are each 0 or 1; for every i, j with 0 <= i < n and 0 <= j < n, g[i][j] <= g'[i][j]; and there exists i, j with 0 <= i < n and 0 <= j < n such that g[i][j] = 1. All indices are 0-based. -/
theorem spec_10 (g g' : Grid) (r r' : Aeneas.Std.I64)
    (hpre : GridPre g)
    (hpre' : GridPre g')
    (hlen : gridLen g' = gridLen g)
    (hle : ∀ i j, i < gridLen g → j < gridLen g →
      ∃ x y : ℤ, cellVal g i j = some x ∧ cellVal g' i j = some y ∧ x ≤ y)
    (hland : HasLand g)
    (hres : Aegis.MaxDistance.max_distance g = ok r)
    (hres' : Aegis.MaxDistance.max_distance g' = ok r') :
    r'.val ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (g g' : Grid) (r r' : Aeneas.Std.I64)
    (hpre : GridPre g)
    (hpre' : GridPre g')
    (hlen : gridLen g' = gridLen g)
    (hle : ∀ i j, i < gridLen g → j < gridLen g →
      ∃ x y : ℤ, cellVal g i j = some x ∧ cellVal g' i j = some y ∧ x ≤ y)
    (hland : HasLand g)
    (hres : Aegis.MaxDistance.max_distance g = ok r)
    (hres' : Aegis.MaxDistance.max_distance g' = ok r'), r'.val ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, there exists a water cell (i,j) with 0 <= i < n, 0 <= j < n, and grid[i][j] = 0, such that the minimum over all land cells (i',j') with 0 <= i' < n, 0 <= j' < n, and grid[i'][j'] = 1, of (|i - i'| + |j - j'|) equals r.
  Preconditions: Let n = len(grid). The grid satisfies: 1 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] = 0 or grid[i][j] = 1. All indices are 0-based. -/
theorem spec_11 (grid : Grid) (r : Aeneas.Std.I64)
    (hpre : GridPre grid)
    (hres : Aegis.MaxDistance.max_distance grid = ok r)
    (hr : 0 ≤ r.val) :
    ∃ i j, IsWater grid i j ∧ minLandDist grid i j = some r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Grid) (r : Aeneas.Std.I64)
    (hpre : GridPre grid)
    (hres : Aegis.MaxDistance.max_distance grid = ok r)
    (hr : 0 ≤ r.val), ∃ i j, IsWater grid i j ∧ minLandDist grid i j = some r.val) := by
  sorry

end AegisSpec.MaxDistance
