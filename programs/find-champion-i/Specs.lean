import Aegis.FindChampion.Code.Funs

/-!
# Specifications of `Aegis.FindChampion.find_champion`

LeetCode problem `find-champion-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindChampion

open Aegis.FindChampion

def gridLen (grid : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  grid.val.length

def rowLen (grid : Slice (alloc.vec.Vec Std.I64)) (i : Int) : Nat :=
  ((grid.val[i.toNat]?).map (fun row => row.val.length)).getD 0

def cell (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Int) : Int :=
  (((grid.val[i.toNat]?).bind (fun row => row.val[j.toNat]?)).map (fun x => x.val)).getD 0

def Pre (grid : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  2 ≤ gridLen grid
  ∧ gridLen grid ≤ 100
  ∧ (∀ i : Int, 0 ≤ i → i < (gridLen grid : Int) → rowLen grid i = gridLen grid)
  ∧ (∀ i j : Int, 0 ≤ i → i < (gridLen grid : Int) → 0 ≤ j → j < (gridLen grid : Int) →
      cell grid i j = 0 ∨ cell grid i j = 1)
  ∧ (∀ i : Int, 0 ≤ i → i < (gridLen grid : Int) → cell grid i i = 0)
  ∧ (∀ i j : Int, 0 ≤ i → i < (gridLen grid : Int) → 0 ≤ j → j < (gridLen grid : Int) →
      i ≠ j → cell grid i j ≠ cell grid j i)
  ∧ (∀ a b c : Int, 0 ≤ a → a < (gridLen grid : Int) → 0 ≤ b → b < (gridLen grid : Int) →
      0 ≤ c → c < (gridLen grid : Int) → cell grid a b = 1 → cell grid b c = 1 →
      cell grid a c = 1)

def IsPermOn (n : Nat) (σ : Nat → Nat) : Prop :=
  (∀ i, i < n → σ i < n) ∧ ∀ j, j < n → ∃ i, i < n ∧ σ i = j

def rowOnes (grid : Slice (alloc.vec.Vec Std.I64)) (i : Int) : Nat :=
  ((List.range (gridLen grid)).filter (fun t => cell grid i (t : Int) = 1)).length

/-- The function returns a result r and r satisfies 0 <= r < n and, for every b with 0 <= b < n, grid[b][r] = 0. Equivalently, r is a team for which there is no team b that is stronger than r, where for b != r team b is stronger than r exactly when grid[b][r] = 1.
  Preconditions: Let n = len(grid). We assume 2 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1; for every i with 0 <= i < n, grid[i][i] = 0; for every i,j with 0 <= i < n, 0 <= j < n, and i != j, grid[i][j] != grid[j][i]; and for every a,b,c with 0 <= a,b,c < n, if grid[a][b] = 1 and grid[b][c] = 1 then grid[a][c] = 1. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid) :
    ∃ r : Std.I64, find_champion grid = ok r
      ∧ 0 ≤ r.val
      ∧ r.val < (gridLen grid : Int)
      ∧ ∀ b : Int, 0 ≤ b → b < (gridLen grid : Int) → cell grid b r.val = 0 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid), ∃ r : Std.I64, find_champion grid = ok r
      ∧ 0 ≤ r.val
      ∧ r.val < (gridLen grid : Int)
      ∧ ∀ b : Int, 0 ≤ b → b < (gridLen grid : Int) → cell grid b r.val = 0) := by
  sorry

/-- The function returns a result r; it does not fail, overflow, or panic.
  Preconditions: Let n = len(grid). We assume 2 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1; for every i with 0 <= i < n, grid[i][i] = 0; for every i,j with 0 <= i < n, 0 <= j < n, and i != j, grid[i][j] != grid[j][i]; and for every a,b,c with 0 <= a,b,c < n, if grid[a][b] = 1 and grid[b][c] = 1 then grid[a][c] = 1. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid) :
    ∃ r : Std.I64, find_champion grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid), ∃ r : Std.I64, find_champion grid = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r < n = len(grid).
  Preconditions: Let n = len(grid). We assume 2 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1; for every i with 0 <= i < n, grid[i][i] = 0; for every i,j with 0 <= i < n, 0 <= j < n, and i != j, grid[i][j] != grid[j][i]; and for every a,b,c with 0 <= a,b,c < n, if grid[a][b] = 1 and grid[b][c] = 1 then grid[a][c] = 1. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid) (r : Std.I64)
    (hr : find_champion grid = ok r) :
    0 ≤ r.val ∧ r.val < (gridLen grid : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid) (r : Std.I64)
    (hr : find_champion grid = ok r), 0 ≤ r.val ∧ r.val < (gridLen grid : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every b with 0 <= b < n, grid[b][r] = 0.
  Preconditions: Let n = len(grid). We assume 2 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1; for every i with 0 <= i < n, grid[i][i] = 0; for every i,j with 0 <= i < n, 0 <= j < n, and i != j, grid[i][j] != grid[j][i]; and for every a,b,c with 0 <= a,b,c < n, if grid[a][b] = 1 and grid[b][c] = 1 then grid[a][c] = 1. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid) (r : Std.I64)
    (hr : find_champion grid = ok r) :
    ∀ b : Int, 0 ≤ b → b < (gridLen grid : Int) → cell grid b r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid) (r : Std.I64)
    (hr : find_champion grid = ok r), ∀ b : Int, 0 ≤ b → b < (gridLen grid : Int) → cell grid b r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, for every t with 0 <= t < n and t != r, grid[r][t] = 1.
  Preconditions: Let n = len(grid). We assume 2 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1; for every i with 0 <= i < n, grid[i][i] = 0; for every i,j with 0 <= i < n, 0 <= j < n, and i != j, grid[i][j] != grid[j][i]; and for every a,b,c with 0 <= a,b,c < n, if grid[a][b] = 1 and grid[b][c] = 1 then grid[a][c] = 1. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid) (r : Std.I64)
    (hr : find_champion grid = ok r) :
    ∀ t : Int, 0 ≤ t → t < (gridLen grid : Int) → t ≠ r.val → cell grid r.val t = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid) (r : Std.I64)
    (hr : find_champion grid = ok r), ∀ t : Int, 0 ≤ t → t < (gridLen grid : Int) → t ≠ r.val → cell grid r.val t = 1) := by
  sorry

/-- Whenever the function returns a result r, for every c with 0 <= c < n, if for every b with 0 <= b < n grid[b][c] = 0, then c = r.
  Preconditions: Let n = len(grid). We assume 2 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1; for every i with 0 <= i < n, grid[i][i] = 0; for every i,j with 0 <= i < n, 0 <= j < n, and i != j, grid[i][j] != grid[j][i]; and for every a,b,c with 0 <= a,b,c < n, if grid[a][b] = 1 and grid[b][c] = 1 then grid[a][c] = 1. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid) (r : Std.I64)
    (hr : find_champion grid = ok r) :
    ∀ c : Int, 0 ≤ c → c < (gridLen grid : Int) →
      (∀ b : Int, 0 ≤ b → b < (gridLen grid : Int) → cell grid b c = 0) → c = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid) (r : Std.I64)
    (hr : find_champion grid = ok r), ∀ c : Int, 0 ≤ c → c < (gridLen grid : Int) →
      (∀ b : Int, 0 ≤ b → b < (gridLen grid : Int) → cell grid b c = 0) → c = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every s with 0 <= s < n and s != r, there exists b with 0 <= b < n such that grid[b][s] = 1.
  Preconditions: Let n = len(grid). We assume 2 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1; for every i with 0 <= i < n, grid[i][i] = 0; for every i,j with 0 <= i < n, 0 <= j < n, and i != j, grid[i][j] != grid[j][i]; and for every a,b,c with 0 <= a,b,c < n, if grid[a][b] = 1 and grid[b][c] = 1 then grid[a][c] = 1. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid) (r : Std.I64)
    (hr : find_champion grid = ok r) :
    ∀ s : Int, 0 ≤ s → s < (gridLen grid : Int) → s ≠ r.val →
      ∃ b : Int, 0 ≤ b ∧ b < (gridLen grid : Int) ∧ cell grid b s = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid) (r : Std.I64)
    (hr : find_champion grid = ok r), ∀ s : Int, 0 ≤ s → s < (gridLen grid : Int) → s ≠ r.val →
      ∃ b : Int, 0 ≤ b ∧ b < (gridLen grid : Int) ∧ cell grid b s = 1) := by
  sorry

/-- For every c with 0 <= c < n, if for every b with 0 <= b < n grid[b][c] = 0, then the function returns the result c.
  Preconditions: Let n = len(grid). We assume 2 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1; for every i with 0 <= i < n, grid[i][i] = 0; for every i,j with 0 <= i < n, 0 <= j < n, and i != j, grid[i][j] != grid[j][i]; and for every a,b,c with 0 <= a,b,c < n, if grid[a][b] = 1 and grid[b][c] = 1 then grid[a][c] = 1. -/
theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid) (c : Int)
    (hc0 : 0 ≤ c) (hcn : c < (gridLen grid : Int))
    (hc : ∀ b : Int, 0 ≤ b → b < (gridLen grid : Int) → cell grid b c = 0) :
    ∃ r : Std.I64, find_champion grid = ok r ∧ r.val = c := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid) (c : Int)
    (hc0 : 0 ≤ c) (hcn : c < (gridLen grid : Int))
    (hc : ∀ b : Int, 0 ≤ b → b < (gridLen grid : Int) → cell grid b c = 0), ∃ r : Std.I64, find_champion grid = ok r ∧ r.val = c) := by
  sorry

/-- For every c with 0 <= c < n, if for every t with 0 <= t < n and t != c grid[c][t] = 1, then the function returns the result c.
  Preconditions: Let n = len(grid). We assume 2 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1; for every i with 0 <= i < n, grid[i][i] = 0; for every i,j with 0 <= i < n, 0 <= j < n, and i != j, grid[i][j] != grid[j][i]; and for every a,b,c with 0 <= a,b,c < n, if grid[a][b] = 1 and grid[b][c] = 1 then grid[a][c] = 1. -/
theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid) (c : Int)
    (hc0 : 0 ≤ c) (hcn : c < (gridLen grid : Int))
    (hc : ∀ t : Int, 0 ≤ t → t < (gridLen grid : Int) → t ≠ c → cell grid c t = 1) :
    ∃ r : Std.I64, find_champion grid = ok r ∧ r.val = c := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid) (c : Int)
    (hc0 : 0 ≤ c) (hcn : c < (gridLen grid : Int))
    (hc : ∀ t : Int, 0 ≤ t → t < (gridLen grid : Int) → t ≠ c → cell grid c t = 1), ∃ r : Std.I64, find_champion grid = ok r ∧ r.val = c) := by
  sorry

/-- For every permutation p of {0,...,n-1}, let grid_p be the n by n matrix defined by grid_p[i][j] = grid[p(i)][p(j)] for all 0 <= i,j < n. If the function returns r on grid and s on grid_p, then p(s) = r.
  Preconditions: Let n = len(grid). We assume 2 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1; for every i with 0 <= i < n, grid[i][i] = 0; for every i,j with 0 <= i < n, 0 <= j < n, and i != j, grid[i][j] != grid[j][i]; and for every a,b,c with 0 <= a,b,c < n, if grid[a][b] = 1 and grid[b][c] = 1 then grid[a][c] = 1. -/
theorem spec_10 (grid gridp : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid)
    (hprep : Pre gridp) (hlen : gridLen gridp = gridLen grid) (σ : Nat → Nat)
    (hσ : IsPermOn (gridLen grid) σ)
    (hperm : ∀ i j : Nat, i < gridLen grid → j < gridLen grid →
      cell gridp (i : Int) (j : Int) = cell grid (σ i : Int) (σ j : Int))
    (r s : Std.I64) (hr : find_champion grid = ok r) (hs : find_champion gridp = ok s) :
    (σ s.val.toNat : Int) = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid gridp : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid)
    (hprep : Pre gridp) (hlen : gridLen gridp = gridLen grid) (σ : Nat → Nat)
    (hσ : IsPermOn (gridLen grid) σ)
    (hperm : ∀ i j : Nat, i < gridLen grid → j < gridLen grid →
      cell gridp (i : Int) (j : Int) = cell grid (σ i : Int) (σ j : Int))
    (r s : Std.I64) (hr : find_champion grid = ok r) (hs : find_champion gridp = ok s), (σ s.val.toNat : Int) = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every s with 0 <= s < n and s != r, the number of indices t with 0 <= t < n and grid[s][t] = 1 is strictly less than the number of indices t with 0 <= t < n and grid[r][t] = 1.
  Preconditions: Let n = len(grid). We assume 2 <= n <= 100; for every i with 0 <= i < n, len(grid[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1; for every i with 0 <= i < n, grid[i][i] = 0; for every i,j with 0 <= i < n, 0 <= j < n, and i != j, grid[i][j] != grid[j][i]; and for every a,b,c with 0 <= a,b,c < n, if grid[a][b] = 1 and grid[b][c] = 1 then grid[a][c] = 1. -/
theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid) (r : Std.I64)
    (hr : find_champion grid = ok r) :
    ∀ s : Int, 0 ≤ s → s < (gridLen grid : Int) → s ≠ r.val →
      rowOnes grid s < rowOnes grid r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (hpre : Pre grid) (r : Std.I64)
    (hr : find_champion grid = ok r), ∀ s : Int, 0 ≤ s → s < (gridLen grid : Int) → s ≠ r.val →
      rowOnes grid s < rowOnes grid r.val) := by
  sorry

end AegisSpec.FindChampion
