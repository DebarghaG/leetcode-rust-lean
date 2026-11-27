import Aegis.ShortestPath.Code.Funs

/-!
# Specifications of `Aegis.ShortestPath.shortest_path`

LeetCode problem `shortest-path-in-a-grid-with-obstacles-elimination`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ShortestPath

namespace AegisSpec.ShortestPath

def cellVal (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  match grid.val[i]? with
  | none => 0
  | some row =>
    match row.val[j]? with
    | none => 0
    | some x => x.val

def rowLen (grid : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Nat :=
  ((grid.val[i]?).map (fun row => row.val.length)).getD 0

def onesCount (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Nat :=
  (((Finset.range m).product (Finset.range n)).filter
    (fun c => cellVal grid c.1 c.2 = 1)).card

def onesInFirstRow (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Nat :=
  ((Finset.range n).filter (fun j => cellVal grid 0 j = 1)).card

def onesInFirstCol (grid : Slice (alloc.vec.Vec Std.I64)) (m : Nat) : Nat :=
  ((Finset.range m).filter (fun i => cellVal grid i 0 = 1)).card

def Adjacent (a b : Nat × Nat) : Prop :=
  ((a.1 : Int) - (b.1 : Int)).natAbs + ((a.2 : Int) - (b.2 : Int)).natAbs = 1

def IsWalk (m n L : Nat) (p : Nat → Nat × Nat) : Prop :=
  (∀ t, t ≤ L → (p t).1 < m ∧ (p t).2 < n) ∧
    p 0 = (0, 0) ∧
    p L = (m - 1, n - 1) ∧
    (∀ t, t < L → Adjacent (p t) (p (t + 1)))

def obstacleCount (grid : Slice (alloc.vec.Vec Std.I64)) (L : Nat)
    (p : Nat → Nat × Nat) : Nat :=
  (((Finset.range (L + 1)).filter
    (fun t => cellVal grid (p t).1 (p t).2 = 1)).image p).card

def Feasible (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (k : Int) (L : Nat)
    (p : Nat → Nat × Nat) : Prop :=
  IsWalk m n L p ∧ (obstacleCount grid L p : Int) ≤ k

def IsMonotoneWalk (m n : Nat) (p : Nat → Nat × Nat) : Prop :=
  (∀ t, t ≤ m + n - 2 → (p t).1 < m ∧ (p t).2 < n) ∧
    p 0 = (0, 0) ∧
    p (m + n - 2) = (m - 1, n - 1) ∧
    (∀ t, t < m + n - 2 →
      p (t + 1) = ((p t).1 + 1, (p t).2) ∨ p (t + 1) = ((p t).1, (p t).2 + 1))

def incSteps (p : Nat → Nat × Nat) (L : Nat) : Nat :=
  ((Finset.range L).filter
    (fun t => (p (t + 1)).1 + (p (t + 1)).2 = (p t).1 + (p t).2 + 1)).card

def decSteps (p : Nat → Nat × Nat) (L : Nat) : Nat :=
  ((Finset.range L).filter
    (fun t => (p (t + 1)).1 + (p (t + 1)).2 + 1 = (p t).1 + (p t).2)).card

/-- Whenever the function returns a result r, the following holds. Let a walk be a finite sequence of cells p_0,...,p_L inside the grid such that p_0=(0,0), p_L=(m-1,n-1), and for every t with 0 <= t < L the cells p_t and p_{t+1} are orthogonally adjacent (the sum of the absolute row difference and absolute column difference is 1). The obstacle count of the walk is the number of distinct cells (i,j) with 0 <= i < m, 0 <= j < n, grid[i][j]=1, and p_t=(i,j) for some t. The walk is feasible if its obstacle count is at most k. Then r is the minimum length L over all feasible walks if at least one feasible walk exists, and r = -1 if no feasible walk exists.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m, n <= 40; every row of grid has length n; grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n; grid[0][0] = grid[m-1][n-1] = 0; and 0 <= k <= m*n. -/
theorem spec_1
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r) :
    (∃ (L : Nat) (p : Nat → Nat × Nat),
        Feasible grid m n k.val L p ∧ r.val = (L : Int) ∧
          ∀ (L' : Nat) (p' : Nat → Nat × Nat), Feasible grid m n k.val L' p' → L ≤ L') ∨
      (r.val = -1 ∧ ∀ (L : Nat) (p : Nat → Nat × Nat), ¬ Feasible grid m n k.val L p) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r), (∃ (L : Nat) (p : Nat → Nat × Nat),
        Feasible grid m n k.val L p ∧ r.val = (L : Int) ∧
          ∀ (L' : Nat) (p' : Nat → Nat × Nat), Feasible grid m n k.val L' p' → L ≤ L') ∨
      (r.val = -1 ∧ ∀ (L : Nat) (p : Nat → Nat × Nat), ¬ Feasible grid m n k.val L p)) := by
  sorry

/-- Under the preconditions, the function returns a result (Result.ok) for every valid input; it does not fail due to arithmetic overflow, out-of-bounds indexing, or panic. The returned value may be -1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m, n <= 40; every row of grid has length n; grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n; grid[0][0] = grid[m-1][n-1] = 0; and 0 <= k <= m*n. -/
theorem spec_2
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int)) :
    ∃ r : Std.I64, shortest_path grid k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int)), ∃ r : Std.I64, shortest_path grid k = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or both 0 <= r and r <= m*n - 1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m, n <= 40; every row of grid has length n; grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n; grid[0][0] = grid[m-1][n-1] = 0; and 0 <= k <= m*n. -/
theorem spec_3
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r) :
    r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ ((m * n : Nat) : Int) - 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r), r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ ((m * n : Nat) : Int) - 1)) := by
  sorry

/-- Whenever the function returns a result r, if r != -1 then r >= m + n - 2.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m, n <= 40; every row of grid has length n; grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n; grid[0][0] = grid[m-1][n-1] = 0; and 0 <= k <= m*n. -/
theorem spec_4
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r) :
    r.val ≠ -1 → ((m : Int) + (n : Int) - 2) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r), r.val ≠ -1 → ((m : Int) + (n : Int) - 2) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exists a sequence p_0,...,p_r of cells inside the grid such that p_0=(0,0), p_r=(m-1,n-1), consecutive cells are orthogonally adjacent, and the number of distinct cells among p_0,...,p_r with grid value 1 is at most k.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m, n <= 40; every row of grid has length n; grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n; grid[0][0] = grid[m-1][n-1] = 0; and 0 <= k <= m*n. -/
theorem spec_5
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r) :
    r.val ≠ -1 →
      ∃ (L : Nat) (p : Nat → Nat × Nat), r.val = (L : Int) ∧ Feasible grid m n k.val L p := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r), r.val ≠ -1 →
      ∃ (L : Nat) (p : Nat → Nat × Nat), r.val = (L : Int) ∧ Feasible grid m n k.val L p) := by
  sorry

/-- Whenever the function returns a result r with r != -1, every sequence p_0,...,p_L of cells inside the grid with p_0=(0,0), p_L=(m-1,n-1), consecutive cells orthogonally adjacent, and at most k distinct visited cells having grid value 1 satisfies L >= r.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m, n <= 40; every row of grid has length n; grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n; grid[0][0] = grid[m-1][n-1] = 0; and 0 <= k <= m*n. -/
theorem spec_6
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r) :
    r.val ≠ -1 →
      ∀ (L : Nat) (p : Nat → Nat × Nat), Feasible grid m n k.val L p → r.val ≤ (L : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r), r.val ≠ -1 →
      ∀ (L : Nat) (p : Nat → Nat × Nat), Feasible grid m n k.val L p → r.val ≤ (L : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if there is no sequence p_0,...,p_L of cells inside the grid with p_0=(0,0), p_L=(m-1,n-1), consecutive cells orthogonally adjacent, and at most k distinct visited cells having grid value 1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m, n <= 40; every row of grid has length n; grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n; grid[0][0] = grid[m-1][n-1] = 0; and 0 <= k <= m*n. -/
theorem spec_7
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r) :
    (r.val = -1 ↔ ¬ ∃ (L : Nat) (p : Nat → Nat × Nat), Feasible grid m n k.val L p) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r), (r.val = -1 ↔ ¬ ∃ (L : Nat) (p : Nat → Nat × Nat), Feasible grid m n k.val L p)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, every sequence p_0,...,p_r of cells inside the grid with p_0=(0,0), p_r=(m-1,n-1), consecutive cells orthogonally adjacent, and at most k distinct visited cells with grid value 1 has all its cells p_0,...,p_r pairwise distinct.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m, n <= 40; every row of grid has length n; grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n; grid[0][0] = grid[m-1][n-1] = 0; and 0 <= k <= m*n. -/
theorem spec_8
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r) :
    r.val ≠ -1 →
      ∀ (L : Nat) (p : Nat → Nat × Nat), IsWalk m n L p →
        (obstacleCount grid L p : Int) ≤ k.val → r.val = (L : Int) →
          ∀ s t : Nat, s ≤ L → t ≤ L → p s = p t → s = t := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r), r.val ≠ -1 →
      ∀ (L : Nat) (p : Nat → Nat × Nat), IsWalk m n L p →
        (obstacleCount grid L p : Int) ≤ k.val → r.val = (L : Int) →
          ∀ s t : Nat, s ≤ L → t ≤ L → p s = p t → s = t) := by
  sorry

/-- Whenever the function returns a result r with r != -1, r and m+n-2 have the same parity; equivalently, r - (m+n-2) is even.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m, n <= 40; every row of grid has length n; grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n; grid[0][0] = grid[m-1][n-1] = 0; and 0 <= k <= m*n. -/
theorem spec_9
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r) :
    r.val ≠ -1 → Even (r.val - ((m : Int) + (n : Int) - 2)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r), r.val ≠ -1 → Even (r.val - ((m : Int) + (n : Int) - 2))) := by
  sorry

/-- Let c be the number of cells (i,j) with 0 <= i < m, 0 <= j < n and grid[i][j] = 1. If k >= c, then the function returns a result r and r = m+n-2.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m, n <= 40; every row of grid has length n; grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n; grid[0][0] = grid[m-1][n-1] = 0; and 0 <= k <= m*n. -/
theorem spec_10
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hbig : (onesCount grid m n : Int) ≤ k.val) :
    ∃ r : Std.I64, shortest_path grid k = ok r ∧ r.val = ((m : Int) + (n : Int) - 2) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hbig : (onesCount grid m n : Int) ≤ k.val), ∃ r : Std.I64, shortest_path grid k = ok r ∧ r.val = ((m : Int) + (n : Int) - 2)) := by
  sorry

/-- Let c be the number of columns j with 0 <= j < n and grid[0][j] = 1. The function returns a result r, and r = n-1 if c <= k, while r = -1 if c > k.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m, n <= 40; every row of grid has length n; grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n; grid[0][0] = grid[m-1][n-1] = 0; and 0 <= k <= m*n. In addition, m = 1. -/
theorem spec_11
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hmone : m = 1) :
    ∃ r : Std.I64, shortest_path grid k = ok r ∧
      (((onesInFirstRow grid n : Int) ≤ k.val → r.val = (n : Int) - 1) ∧
        ((onesInFirstRow grid n : Int) > k.val → r.val = -1)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hmone : m = 1), ∃ r : Std.I64, shortest_path grid k = ok r ∧
      (((onesInFirstRow grid n : Int) ≤ k.val → r.val = (n : Int) - 1) ∧
        ((onesInFirstRow grid n : Int) > k.val → r.val = -1))) := by
  sorry

/-- Let c be the number of rows i with 0 <= i < m and grid[i][0] = 1. The function returns a result r, and r = m-1 if c <= k, while r = -1 if c > k.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m, n <= 40; every row of grid has length n; grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n; grid[0][0] = grid[m-1][n-1] = 0; and 0 <= k <= m*n. In addition, n = 1. -/
theorem spec_12
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hnone : n = 1) :
    ∃ r : Std.I64, shortest_path grid k = ok r ∧
      (((onesInFirstCol grid m : Int) ≤ k.val → r.val = (m : Int) - 1) ∧
        ((onesInFirstCol grid m : Int) > k.val → r.val = -1)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hnone : n = 1), ∃ r : Std.I64, shortest_path grid k = ok r ∧
      (((onesInFirstCol grid m : Int) ≤ k.val → r.val = (m : Int) - 1) ∧
        ((onesInFirstCol grid m : Int) > k.val → r.val = -1))) := by
  sorry

/-- Whenever the function returns a result r, r = m+n-2 if and only if there exists a sequence p_0,...,p_{m+n-2} of cells inside the grid such that p_0=(0,0), p_{m+n-2}=(m-1,n-1), every step is either (i,j) to (i+1,j) or (i,j) to (i,j+1), and the number of distinct cells among p_0,...,p_{m+n-2} with grid value 1 is at most k.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m, n <= 40; every row of grid has length n; grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n; grid[0][0] = grid[m-1][n-1] = 0; and 0 <= k <= m*n. -/
theorem spec_13
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r) :
    (r.val = ((m : Int) + (n : Int) - 2) ↔
      ∃ p : Nat → Nat × Nat,
        IsMonotoneWalk m n p ∧ (obstacleCount grid (m + n - 2) p : Int) ≤ k.val) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r), (r.val = ((m : Int) + (n : Int) - 2) ↔
      ∃ p : Nat → Nat × Nat,
        IsMonotoneWalk m n p ∧ (obstacleCount grid (m + n - 2) p : Int) ≤ k.val)) := by
  sorry

/-- For any two bounds k1 and k2 with 0 <= k1 <= k2 <= m*n, let r1 be the result of shortest_path(grid,k1) and r2 the result of shortest_path(grid,k2). Whenever both evaluations return results, if r1 != -1 then r2 != -1 and r2 <= r1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m, n <= 40; every row of grid has length n; grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n; grid[0][0] = grid[m-1][n-1] = 0; and 0 <= k1 <= k2 <= m*n. -/
theorem spec_14
    (grid : Slice (alloc.vec.Vec Std.I64)) (k1 k2 : Std.I64) (m n : Nat)
    (r1 r2 : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk10 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
    (hk2m : k2.val ≤ ((m * n : Nat) : Int))
    (h1 : shortest_path grid k1 = ok r1) (h2 : shortest_path grid k2 = ok r2) :
    r1.val ≠ -1 → r2.val ≠ -1 ∧ r2.val ≤ r1.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k1 k2 : Std.I64) (m n : Nat)
    (r1 r2 : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk10 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
    (hk2m : k2.val ≤ ((m * n : Nat) : Int))
    (h1 : shortest_path grid k1 = ok r1) (h2 : shortest_path grid k2 = ok r2), r1.val ≠ -1 → r2.val ≠ -1 ∧ r2.val ≤ r1.val) := by
  sorry

/-- Whenever the function returns a result r with r != -1, every sequence p_0,...,p_r of cells inside the grid with p_0=(0,0), p_r=(m-1,n-1), and consecutive cells orthogonally adjacent has exactly (r + m + n - 2)/2 steps t for which (row(p_{t+1}) + col(p_{t+1})) - (row(p_t) + col(p_t)) = 1, and exactly (r - (m + n - 2))/2 steps t for which this difference is -1. Here row(p) and col(p) denote the row and column indices of cell p.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: 1 <= m, n <= 40; every row of grid has length n; grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n; grid[0][0] = grid[m-1][n-1] = 0; and 0 <= k <= m*n. -/
theorem spec_15
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r) :
    r.val ≠ -1 →
      ∀ (L : Nat) (p : Nat → Nat × Nat), IsWalk m n L p → r.val = (L : Int) →
        incSteps p L = (L + m + n - 2) / 2 ∧ decSteps p L = (L - (m + n - 2)) / 2 := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat) (r : Std.I64)
    (hmlen : grid.val.length = m) (hm1 : 1 ≤ m) (hm40 : m ≤ 40)
    (hn1 : 1 ≤ n) (hn40 : n ≤ 40)
    (hrows : ∀ i, i < m → rowLen grid i = n)
    (hbin : ∀ i, i < m → ∀ j, j < n → cellVal grid i j = 0 ∨ cellVal grid i j = 1)
    (hstart : cellVal grid 0 0 = 0) (hend : cellVal grid (m - 1) (n - 1) = 0)
    (hk0 : 0 ≤ k.val) (hkm : k.val ≤ ((m * n : Nat) : Int))
    (hr : shortest_path grid k = ok r), r.val ≠ -1 →
      ∀ (L : Nat) (p : Nat → Nat × Nat), IsWalk m n L p → r.val = (L : Int) →
        incSteps p L = (L + m + n - 2) / 2 ∧ decSteps p L = (L - (m + n - 2)) / 2) := by
  sorry

end AegisSpec.ShortestPath
