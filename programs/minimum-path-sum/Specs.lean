import Aegis.MinPathSum.Code.Funs

/-!
# Specifications of `Aegis.MinPathSum.min_path_sum`

LeetCode problem `minimum-path-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinPathSum

open Aegis.MinPathSum

def numRows (grid : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  grid.val.length

def numCols (grid : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  ((grid.val[0]?).map (fun row => row.val.length)).getD 0

def rowLen (grid : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Nat :=
  ((grid.val[i]?).map (fun row => row.val.length)).getD 0

def cell (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  (((grid.val[i]?).bind (fun row => row.val[j]?)).map (fun x => x.val)).getD 0

def IsMonotonePath (m n : Nat) (p : List (Nat × Nat)) : Prop :=
  p.head? = some (0, 0) ∧
    p.getLast? = some (m - 1, n - 1) ∧
      ∀ (t : Nat) (a b : Nat × Nat),
        p[t]? = some a → p[t + 1]? = some b →
          b = (a.1 + 1, a.2) ∨ b = (a.1, a.2 + 1)

def pathSum (grid : Slice (alloc.vec.Vec Std.I64)) (p : List (Nat × Nat)) : Int :=
  (p.map (fun c => cell grid c.1 c.2)).sum

def pathSums (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Set Int :=
  {s | ∃ p : List (Nat × Nat), IsMonotonePath m n p ∧ s = pathSum grid p}

def TransposeOf (gt g : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  numRows gt = numCols g ∧ numCols gt = numRows g ∧
    (∀ j, j < numRows gt → rowLen gt j = numCols gt) ∧
      ∀ j i, j < numRows g → i < numCols g → cell gt j i = cell g i j

def FlipOf (gr g : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  numRows gr = numRows g ∧ numCols gr = numCols g ∧
    (∀ i, i < numRows gr → rowLen gr i = numCols gr) ∧
      ∀ i j, i < numRows g → j < numCols g →
        cell gr i j = cell g (numRows g - 1 - i) (numCols g - 1 - j)

def ShiftOf (gs g : Slice (alloc.vec.Vec Std.I64)) (c : Int) : Prop :=
  numRows gs = numRows g ∧ numCols gs = numCols g ∧
    (∀ i, i < numRows gs → rowLen gs i = numCols gs) ∧
      ∀ i j, i < numRows g → j < numCols g → cell gs i j = cell g i j + c

/-- Whenever the function returns a result r, r is the minimum path sum from the top-left cell (0,0) to the bottom-right cell (m-1,n-1). Formally, r = min { sum(P) | P is a monotone path from (0,0) to (m-1,n-1) }, where a monotone path is a sequence of cells (r_0,c_0),...,(r_k,c_k) with (r_0,c_0)=(0,0), (r_k,c_k)=(m-1,n-1), and for every t with 0 <= t < k either (r_{t+1},c_{t+1})=(r_t+1,c_t) or (r_{t+1},c_{t+1})=(r_t,c_t+1); and sum(P)=Σ_{t=0}^{k} grid[r_t][c_t].
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 200 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200) :
    ∀ r : Std.I64, min_path_sum grid = Result.ok r →
      IsLeast (pathSums grid (numRows grid) (numCols grid)) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200), ∀ r : Std.I64, min_path_sum grid = Result.ok r →
      IsLeast (pathSums grid (numRows grid) (numCols grid)) r.val) := by
  sorry

/-- The function returns a result (it does not fail, panic, overflow, or perform an out-of-bounds access) for every input satisfying the preconditions.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 200 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200) :
    ∃ r : Std.I64, min_path_sum grid = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200), ∃ r : Std.I64, min_path_sum grid = Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= grid[0][0] and r >= grid[m-1][n-1].
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 200 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200) :
    ∀ r : Std.I64, min_path_sum grid = Result.ok r →
      r.val ≥ cell grid 0 0 ∧ r.val ≥ cell grid (numRows grid - 1) (numCols grid - 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200), ∀ r : Std.I64, min_path_sum grid = Result.ok r →
      r.val ≥ cell grid 0 0 ∧ r.val ≥ cell grid (numRows grid - 1) (numCols grid - 1)) := by
  sorry

/-- Whenever the function returns a result r, r <= (Σ_{j=0}^{n-1} grid[0][j]) + (Σ_{i=1}^{m-1} grid[i][n-1]).
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 200 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200) :
    ∀ r : Std.I64, min_path_sum grid = Result.ok r →
      r.val ≤ (∑ j ∈ Finset.range (numCols grid), cell grid 0 j)
        + (∑ i ∈ Finset.range (numRows grid - 1), cell grid (i + 1) (numCols grid - 1)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200), ∀ r : Std.I64, min_path_sum grid = Result.ok r →
      r.val ≤ (∑ j ∈ Finset.range (numCols grid), cell grid 0 j)
        + (∑ i ∈ Finset.range (numRows grid - 1), cell grid (i + 1) (numCols grid - 1))) := by
  sorry

/-- Whenever the function returns a result r, r = Σ_{j=0}^{n-1} grid[0][j].
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, 0 <= grid[i][j] <= 200 for every 0 <= i < m and 0 <= j < n, and m = 1. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200)
    (hm : numRows grid = 1) :
    ∀ r : Std.I64, min_path_sum grid = Result.ok r →
      r.val = ∑ j ∈ Finset.range (numCols grid), cell grid 0 j := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200)
    (hm : numRows grid = 1), ∀ r : Std.I64, min_path_sum grid = Result.ok r →
      r.val = ∑ j ∈ Finset.range (numCols grid), cell grid 0 j) := by
  sorry

/-- Whenever the function returns a result r, r = Σ_{i=0}^{m-1} grid[i][0].
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, 0 <= grid[i][j] <= 200 for every 0 <= i < m and 0 <= j < n, and n = 1. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200)
    (hn : numCols grid = 1) :
    ∀ r : Std.I64, min_path_sum grid = Result.ok r →
      r.val = ∑ i ∈ Finset.range (numRows grid), cell grid i 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200)
    (hn : numCols grid = 1), ∀ r : Std.I64, min_path_sum grid = Result.ok r →
      r.val = ∑ i ∈ Finset.range (numRows grid), cell grid i 0) := by
  sorry

/-- Whenever the function returns a result r, there exists a monotone path P from (0,0) to (m-1,n-1) such that r = sum(P), where sum(P) is the sum of grid entries on the cells of P, counted once per cell.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 200 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200) :
    ∀ r : Std.I64, min_path_sum grid = Result.ok r →
      ∃ p : List (Nat × Nat),
        IsMonotonePath (numRows grid) (numCols grid) p ∧ r.val = pathSum grid p := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200), ∀ r : Std.I64, min_path_sum grid = Result.ok r →
      ∃ p : List (Nat × Nat),
        IsMonotonePath (numRows grid) (numCols grid) p ∧ r.val = pathSum grid p) := by
  sorry

/-- Whenever the function returns a result r, for every monotone path P from (0,0) to (m-1,n-1), r <= sum(P), where sum(P) is the sum of grid entries on P.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 200 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200) :
    ∀ r : Std.I64, min_path_sum grid = Result.ok r →
      ∀ p : List (Nat × Nat),
        IsMonotonePath (numRows grid) (numCols grid) p → r.val ≤ pathSum grid p := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200), ∀ r : Std.I64, min_path_sum grid = Result.ok r →
      ∀ p : List (Nat × Nat),
        IsMonotonePath (numRows grid) (numCols grid) p → r.val ≤ pathSum grid p) := by
  sorry

/-- Let G^T be the n x m grid defined by G^T[j][i] = grid[i][j] for 0 <= i < m and 0 <= j < n. Whenever the function returns a result r on grid and a result r^T on G^T, r = r^T.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 200 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_9 (grid gridT : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200)
    (hT : TransposeOf gridT grid) :
    ∀ r rT : Std.I64,
      min_path_sum grid = Result.ok r → min_path_sum gridT = Result.ok rT → r = rT := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid gridT : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200)
    (hT : TransposeOf gridT grid), ∀ r rT : Std.I64,
      min_path_sum grid = Result.ok r → min_path_sum gridT = Result.ok rT → r = rT) := by
  sorry

/-- Let G^R be the m x n grid defined by G^R[i][j] = grid[m-1-i][n-1-j] for 0 <= i < m and 0 <= j < n. Whenever the function returns a result r on grid and a result r^R on G^R, r = r^R.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 200 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_10 (grid gridR : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200)
    (hR : FlipOf gridR grid) :
    ∀ r rR : Std.I64,
      min_path_sum grid = Result.ok r → min_path_sum gridR = Result.ok rR → r = rR := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid gridR : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200)
    (hR : FlipOf gridR grid), ∀ r rR : Std.I64,
      min_path_sum grid = Result.ok r → min_path_sum gridR = Result.ok rR → r = rR) := by
  sorry

/-- Whenever the function returns a result r_G on G and a result r_H on H, r_G <= r_H.
  Preconditions: Let G and H be grids. Let m = len(G) = len(H) and n = len(G[0]) = len(H[0]). Assume 1 <= m <= 200, 1 <= n <= 200, every row of G and H has length n, 0 <= G[i][j] <= 200 and 0 <= H[i][j] <= 200 for all 0 <= i < m and 0 <= j < n, and G[i][j] <= H[i][j] for all 0 <= i < m and 0 <= j < n. -/
theorem spec_11 (G H : Slice (alloc.vec.Vec Std.I64))
    (hGm_pos : 1 ≤ numRows G) (hGm_le : numRows G ≤ 200)
    (hGn_pos : 1 ≤ numCols G) (hGn_le : numCols G ≤ 200)
    (hGrows : ∀ i, i < numRows G → rowLen G i = numCols G)
    (hGentries : ∀ i j, i < numRows G → j < numCols G →
      0 ≤ cell G i j ∧ cell G i j ≤ 200)
    (hHm_pos : 1 ≤ numRows H) (hHm_le : numRows H ≤ 200)
    (hHn_pos : 1 ≤ numCols H) (hHn_le : numCols H ≤ 200)
    (hHrows : ∀ i, i < numRows H → rowLen H i = numCols H)
    (hHentries : ∀ i j, i < numRows H → j < numCols H →
      0 ≤ cell H i j ∧ cell H i j ≤ 200)
    (hm : numRows G = numRows H) (hn : numCols G = numCols H)
    (hle : ∀ i j, i < numRows G → j < numCols G → cell G i j ≤ cell H i j) :
    ∀ rG rH : Std.I64,
      min_path_sum G = Result.ok rG → min_path_sum H = Result.ok rH → rG.val ≤ rH.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (G H : Slice (alloc.vec.Vec Std.I64))
    (hGm_pos : 1 ≤ numRows G) (hGm_le : numRows G ≤ 200)
    (hGn_pos : 1 ≤ numCols G) (hGn_le : numCols G ≤ 200)
    (hGrows : ∀ i, i < numRows G → rowLen G i = numCols G)
    (hGentries : ∀ i j, i < numRows G → j < numCols G →
      0 ≤ cell G i j ∧ cell G i j ≤ 200)
    (hHm_pos : 1 ≤ numRows H) (hHm_le : numRows H ≤ 200)
    (hHn_pos : 1 ≤ numCols H) (hHn_le : numCols H ≤ 200)
    (hHrows : ∀ i, i < numRows H → rowLen H i = numCols H)
    (hHentries : ∀ i j, i < numRows H → j < numCols H →
      0 ≤ cell H i j ∧ cell H i j ≤ 200)
    (hm : numRows G = numRows H) (hn : numCols G = numCols H)
    (hle : ∀ i j, i < numRows G → j < numCols G → cell G i j ≤ cell H i j), ∀ rG rH : Std.I64,
      min_path_sum G = Result.ok rG → min_path_sum H = Result.ok rH → rG.val ≤ rH.val) := by
  sorry

/-- Let G' be the m x n grid with G'[i][j] = grid[i][j]+c for all i,j. Whenever the function returns a result r on grid and a result r' on G', r' = r + c*(m+n-1).
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 200 for every 0 <= i < m and 0 <= j < n. Let c be an integer such that 0 <= grid[i][j]+c <= 200 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_12 (grid gridS : Slice (alloc.vec.Vec Std.I64)) (c : Int)
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200)
    (hS : ShiftOf gridS grid c)
    (hc : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j + c ∧ cell grid i j + c ≤ 200) :
    ∀ r rS : Std.I64,
      min_path_sum grid = Result.ok r → min_path_sum gridS = Result.ok rS →
        rS.val = r.val + c * ((numRows grid : Int) + (numCols grid : Int) - 1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid gridS : Slice (alloc.vec.Vec Std.I64)) (c : Int)
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200)
    (hS : ShiftOf gridS grid c)
    (hc : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j + c ∧ cell grid i j + c ≤ 200), ∀ r rS : Std.I64,
      min_path_sum grid = Result.ok r → min_path_sum gridS = Result.ok rS →
        rS.val = r.val + c * ((numRows grid : Int) + (numCols grid : Int) - 1)) := by
  sorry

/-- Whenever the function returns a result r, r <= (Σ_{i=0}^{m-1} grid[i][0]) + (Σ_{j=1}^{n-1} grid[m-1][j]).
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 200 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_13 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200) :
    ∀ r : Std.I64, min_path_sum grid = Result.ok r →
      r.val ≤ (∑ i ∈ Finset.range (numRows grid), cell grid i 0)
        + (∑ j ∈ Finset.range (numCols grid - 1), cell grid (numRows grid - 1) (j + 1)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm_pos : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 200)
    (hn_pos : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 200)
    (hrows : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hentries : ∀ i j, i < numRows grid → j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 200), ∀ r : Std.I64, min_path_sum grid = Result.ok r →
      r.val ≤ (∑ i ∈ Finset.range (numRows grid), cell grid i 0)
        + (∑ j ∈ Finset.range (numCols grid - 1), cell grid (numRows grid - 1) (j + 1))) := by
  sorry

end AegisSpec.MinPathSum
