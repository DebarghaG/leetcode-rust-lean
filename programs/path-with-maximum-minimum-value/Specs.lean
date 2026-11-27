import Aegis.MaximumMinimumPath.Code.Funs

/-!
# Specifications of `Aegis.MaximumMinimumPath.maximum_minimum_path`

LeetCode problem `path-with-maximum-minimum-value`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumMinimumPath

  open Aegis.MaximumMinimumPath (maximum_minimum_path)

  def numRows (grid : Slice (alloc.vec.Vec I64)) : Nat :=
    grid.val.length

  def rowLen (grid : Slice (alloc.vec.Vec I64)) (i : Nat) : Nat :=
    match grid.val[i]? with
    | some v => v.val.length
    | none => 0

  def numCols (grid : Slice (alloc.vec.Vec I64)) : Nat :=
    rowLen grid 0

  def cell? (grid : Slice (alloc.vec.Vec I64)) (i j : Nat) : Option Int :=
    match grid.val[i]? with
    | some v => (v.val[j]?).map (fun x => x.val)
    | none => none

  def cell (grid : Slice (alloc.vec.Vec I64)) (i j : Nat) : Int :=
    (cell? grid i j).getD 0

  def ValidGrid (grid : Slice (alloc.vec.Vec I64)) : Prop :=
    1 ≤ numRows grid ∧ numRows grid ≤ 100 ∧
    1 ≤ numCols grid ∧ numCols grid ≤ 100 ∧
    (∀ i, i < numRows grid → rowLen grid i = numCols grid) ∧
    (∀ i, i < numRows grid → ∀ j, j < numCols grid →
      0 ≤ cell grid i j ∧ cell grid i j ≤ 10 ^ 9)

  def AdjacentSteps : List (Nat × Nat) → Prop
    | [] => True
    | [_] => True
    | p :: q :: rest =>
        (Int.natAbs ((q.1 : Int) - (p.1 : Int)) +
           Int.natAbs ((q.2 : Int) - (p.2 : Int)) = 1) ∧
        AdjacentSteps (q :: rest)

  def IsGridPath (grid : Slice (alloc.vec.Vec I64)) (P : List (Nat × Nat)) : Prop :=
    P ≠ [] ∧
    P.head? = some (0, 0) ∧
    P.getLast? = some (numRows grid - 1, numCols grid - 1) ∧
    (∀ p ∈ P, p.1 < numRows grid ∧ p.2 < numCols grid) ∧
    AdjacentSteps P

  def pathVals (grid : Slice (alloc.vec.Vec I64)) (P : List (Nat × Nat)) : List Int :=
    P.map (fun p => cell grid p.1 p.2)

  def IsPathScore (grid : Slice (alloc.vec.Vec I64)) (P : List (Nat × Nat)) (s : Int) : Prop :=
    s ∈ pathVals grid P ∧ ∀ x ∈ pathVals grid P, s ≤ x

  def IsMaxPathScore (grid : Slice (alloc.vec.Vec I64)) (r : Int) : Prop :=
    (∃ P, IsGridPath grid P ∧ IsPathScore grid P r) ∧
    ∀ P s, IsGridPath grid P → IsPathScore grid P s → s ≤ r

  def IsMinimum (n : Nat) (f : Nat → Int) (r : Int) : Prop :=
    (∃ i, i < n ∧ f i = r) ∧ ∀ i, i < n → r ≤ f i

  /-- Let m = len(grid) and n = len(grid[0]). A grid path is a finite sequence P = ((r_0,c_0), ..., (r_k,c_k)) with k >= 0 such that (r_0,c_0) = (0,0), (r_k,c_k) = (m-1,n-1), every term satisfies 0 <= r_i < m and 0 <= c_i < n, and for every i < k, |r_{i+1}-r_i| + |c_{i+1}-c_i| = 1. The score of P is min_{0 <= i <= k} grid[r_i][c_i]. The function returns a result r and r = max { score(P) | P is a grid path }.
    Preconditions: The input satisfies the problem constraints: let m = len(grid) and n = len(grid[0]); then 1 <= m <= 100, 1 <= n <= 100, for every i with 0 <= i < m we have len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= grid[i][j] <= 10^9. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid) :
      ∃ r : I64, maximum_minimum_path grid = ok r ∧ IsMaxPathScore grid r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid), ∃ r : I64, maximum_minimum_path grid = ok r ∧ IsMaxPathScore grid r.val) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, overflow, or go out of bounds on any input satisfying the preconditions.
    Preconditions: The input satisfies the problem constraints: let m = len(grid) and n = len(grid[0]); then 1 <= m <= 100, 1 <= n <= 100, for every i with 0 <= i < m we have len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= grid[i][j] <= 10^9. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid) :
      ∃ r : I64, maximum_minimum_path grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid), ∃ r : I64, maximum_minimum_path grid = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= 10^9.
    Preconditions: The input satisfies the problem constraints: let m = len(grid) and n = len(grid[0]); then 1 <= m <= 100, 1 <= n <= 100, for every i with 0 <= i < m we have len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= grid[i][j] <= 10^9. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
      (r : I64) (hr : maximum_minimum_path grid = ok r) :
      0 ≤ r.val ∧ r.val ≤ 10 ^ 9 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
        (r : I64) (hr : maximum_minimum_path grid = ok r), 0 ≤ r.val ∧ r.val ≤ 10 ^ 9) := by
    sorry

  /-- Whenever the function returns a result r, r <= min(grid[0][0], grid[m-1][n-1]), where m = len(grid) and n = len(grid[0]).
    Preconditions: The input satisfies the problem constraints: let m = len(grid) and n = len(grid[0]); then 1 <= m <= 100, 1 <= n <= 100, for every i with 0 <= i < m we have len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= grid[i][j] <= 10^9. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
      (r : I64) (hr : maximum_minimum_path grid = ok r) :
      r.val ≤ min (cell grid 0 0) (cell grid (numRows grid - 1) (numCols grid - 1)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
        (r : I64) (hr : maximum_minimum_path grid = ok r), r.val ≤ min (cell grid 0 0) (cell grid (numRows grid - 1) (numCols grid - 1))) := by
    sorry

  /-- Let m = len(grid) and n = len(grid[0]). Whenever the function returns a result r, there exists a finite sequence P = ((r_0,c_0), ..., (r_k,c_k)) with k >= 0 such that (r_0,c_0) = (0,0), (r_k,c_k) = (m-1,n-1), 0 <= r_i < m and 0 <= c_i < n for every 0 <= i <= k, |r_{i+1}-r_i| + |c_{i+1}-c_i| = 1 for every 0 <= i < k, and r = min_{0 <= i <= k} grid[r_i][c_i].
    Preconditions: The input satisfies the problem constraints: let m = len(grid) and n = len(grid[0]); then 1 <= m <= 100, 1 <= n <= 100, for every i with 0 <= i < m we have len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= grid[i][j] <= 10^9. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
      (r : I64) (hr : maximum_minimum_path grid = ok r) :
      ∃ P, IsGridPath grid P ∧ IsPathScore grid P r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
        (r : I64) (hr : maximum_minimum_path grid = ok r), ∃ P, IsGridPath grid P ∧ IsPathScore grid P r.val) := by
    sorry

  /-- Let m = len(grid) and n = len(grid[0]). Whenever the function returns a result r, for every finite sequence P = ((r_0,c_0), ..., (r_k,c_k)) with k >= 0 such that (r_0,c_0) = (0,0), (r_k,c_k) = (m-1,n-1), 0 <= r_i < m and 0 <= c_i < n for every 0 <= i <= k, and |r_{i+1}-r_i| + |c_{i+1}-c_i| = 1 for every 0 <= i < k, we have min_{0 <= i <= k} grid[r_i][c_i] <= r.
    Preconditions: The input satisfies the problem constraints: let m = len(grid) and n = len(grid[0]); then 1 <= m <= 100, 1 <= n <= 100, for every i with 0 <= i < m we have len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= grid[i][j] <= 10^9. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
      (r : I64) (hr : maximum_minimum_path grid = ok r) :
      ∀ P s, IsGridPath grid P → IsPathScore grid P s → s ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
        (r : I64) (hr : maximum_minimum_path grid = ok r), ∀ P s, IsGridPath grid P → IsPathScore grid P s → s ≤ r.val) := by
    sorry

  /-- Let m = len(grid) and n = len(grid[0]). Whenever the function returns a result r, for every integer t, r >= t if and only if there exists a finite sequence P = ((r_0,c_0), ..., (r_k,c_k)) with k >= 0 such that (r_0,c_0) = (0,0), (r_k,c_k) = (m-1,n-1), 0 <= r_i < m and 0 <= c_i < n for every 0 <= i <= k, |r_{i+1}-r_i| + |c_{i+1}-c_i| = 1 for every 0 <= i < k, and grid[r_i][c_i] >= t for every 0 <= i <= k.
    Preconditions: The input satisfies the problem constraints: let m = len(grid) and n = len(grid[0]); then 1 <= m <= 100, 1 <= n <= 100, for every i with 0 <= i < m we have len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= grid[i][j] <= 10^9. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
      (r : I64) (hr : maximum_minimum_path grid = ok r) (t : Int) :
      (t ≤ r.val ↔ ∃ P, IsGridPath grid P ∧ ∀ x ∈ pathVals grid P, t ≤ x) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
        (r : I64) (hr : maximum_minimum_path grid = ok r) (t : Int), (t ≤ r.val ↔ ∃ P, IsGridPath grid P ∧ ∀ x ∈ pathVals grid P, t ≤ x)) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices i,j with 0 <= i < m and 0 <= j < n such that grid[i][j] = r, where m = len(grid) and n = len(grid[0]).
    Preconditions: The input satisfies the problem constraints: let m = len(grid) and n = len(grid[0]); then 1 <= m <= 100, 1 <= n <= 100, for every i with 0 <= i < m we have len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= grid[i][j] <= 10^9. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
      (r : I64) (hr : maximum_minimum_path grid = ok r) :
      ∃ i j, i < numRows grid ∧ j < numCols grid ∧ cell grid i j = r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
        (r : I64) (hr : maximum_minimum_path grid = ok r), ∃ i j, i < numRows grid ∧ j < numCols grid ∧ cell grid i j = r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = min_{0 <= j < n} grid[0][j], where n = len(grid[0]).
    Preconditions: The input satisfies the problem constraints: let m = len(grid) and n = len(grid[0]); then 1 <= m <= 100, 1 <= n <= 100, for every i with 0 <= i < m we have len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= grid[i][j] <= 10^9. Additionally, m = 1. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
      (hrow : numRows grid = 1)
      (r : I64) (hr : maximum_minimum_path grid = ok r) :
      IsMinimum (numCols grid) (fun j => cell grid 0 j) r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
        (hrow : numRows grid = 1)
        (r : I64) (hr : maximum_minimum_path grid = ok r), IsMinimum (numCols grid) (fun j => cell grid 0 j) r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = min_{0 <= i < m} grid[i][0], where m = len(grid).
    Preconditions: The input satisfies the problem constraints: let m = len(grid) and n = len(grid[0]); then 1 <= m <= 100, 1 <= n <= 100, for every i with 0 <= i < m we have len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= grid[i][j] <= 10^9. Additionally, n = 1. -/
  theorem spec_10 (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
      (hcol : numCols grid = 1)
      (r : I64) (hr : maximum_minimum_path grid = ok r) :
      IsMinimum (numRows grid) (fun i => cell grid i 0) r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
        (hcol : numCols grid = 1)
        (r : I64) (hr : maximum_minimum_path grid = ok r), IsMinimum (numRows grid) (fun i => cell grid i 0) r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = grid[0][0].
    Preconditions: The input satisfies the problem constraints: let m = len(grid) and n = len(grid[0]); then 1 <= m <= 100, 1 <= n <= 100, for every i with 0 <= i < m we have len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= grid[i][j] <= 10^9. Additionally, grid[0][0] <= grid[i][j] for every i,j with 0 <= i < m and 0 <= j < n. -/
  theorem spec_11 (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
      (hmin : ∀ i j, i < numRows grid → j < numCols grid → cell grid 0 0 ≤ cell grid i j)
      (r : I64) (hr : maximum_minimum_path grid = ok r) :
      r.val = cell grid 0 0 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
        (hmin : ∀ i j, i < numRows grid → j < numCols grid → cell grid 0 0 ≤ cell grid i j)
        (r : I64) (hr : maximum_minimum_path grid = ok r), r.val = cell grid 0 0) := by
    sorry

  /-- Whenever the function returns a result r, r = grid[m-1][n-1], where m = len(grid) and n = len(grid[0]).
    Preconditions: The input satisfies the problem constraints: let m = len(grid) and n = len(grid[0]); then 1 <= m <= 100, 1 <= n <= 100, for every i with 0 <= i < m we have len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= grid[i][j] <= 10^9. Additionally, grid[m-1][n-1] <= grid[i][j] for every i,j with 0 <= i < m and 0 <= j < n. -/
  theorem spec_12 (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
      (hmin : ∀ i j, i < numRows grid → j < numCols grid →
        cell grid (numRows grid - 1) (numCols grid - 1) ≤ cell grid i j)
      (r : I64) (hr : maximum_minimum_path grid = ok r) :
      r.val = cell grid (numRows grid - 1) (numCols grid - 1) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
        (hmin : ∀ i j, i < numRows grid → j < numCols grid →
          cell grid (numRows grid - 1) (numCols grid - 1) ≤ cell grid i j)
        (r : I64) (hr : maximum_minimum_path grid = ok r), r.val = cell grid (numRows grid - 1) (numCols grid - 1)) := by
    sorry

  /-- Whenever the function returns a result r, r >= min_{0 <= i < m, 0 <= j < n} grid[i][j], where m = len(grid) and n = len(grid[0]).
    Preconditions: The input satisfies the problem constraints: let m = len(grid) and n = len(grid[0]); then 1 <= m <= 100, 1 <= n <= 100, for every i with 0 <= i < m we have len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= grid[i][j] <= 10^9. -/
  theorem spec_13 (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
      (r : I64) (hr : maximum_minimum_path grid = ok r) :
      ∃ i j, i < numRows grid ∧ j < numCols grid ∧ cell grid i j ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
        (r : I64) (hr : maximum_minimum_path grid = ok r), ∃ i j, i < numRows grid ∧ j < numCols grid ∧ cell grid i j ≤ r.val) := by
    sorry

  /-- Whenever maximum_minimum_path g returns r_g and maximum_minimum_path h returns r_h, we have r_g <= r_h.
    Preconditions: The input consists of two grids g and h satisfying the problem constraints with the same dimensions: let m = len(g) = len(h) and n = len(g[0]) = len(h[0]); 1 <= m,n <= 100, and 0 <= g[i][j] <= h[i][j] <= 10^9 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_14 (g h : Slice (alloc.vec.Vec I64)) (hg : ValidGrid g) (hh : ValidGrid h)
      (hdimR : numRows g = numRows h) (hdimC : numCols g = numCols h)
      (hle : ∀ i j, i < numRows g → j < numCols g → cell g i j ≤ cell h i j)
      (rg rh : I64)
      (hrg : maximum_minimum_path g = ok rg) (hrh : maximum_minimum_path h = ok rh) :
      rg.val ≤ rh.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (g h : Slice (alloc.vec.Vec I64)) (hg : ValidGrid g) (hh : ValidGrid h)
        (hdimR : numRows g = numRows h) (hdimC : numCols g = numCols h)
        (hle : ∀ i j, i < numRows g → j < numCols g → cell g i j ≤ cell h i j)
        (rg rh : I64)
        (hrg : maximum_minimum_path g = ok rg) (hrh : maximum_minimum_path h = ok rh), rg.val ≤ rh.val) := by
    sorry

  /-- Let grid' be the matrix with grid'[i][j] = grid[i][j] + d. Whenever maximum_minimum_path grid returns r and maximum_minimum_path grid' returns r', we have r' = r + d.
    Preconditions: The input grid satisfies the problem constraints, and d is an integer such that 0 <= grid[i][j] + d <= 10^9 for every 0 <= i < m and 0 <= j < n, where m = len(grid) and n = len(grid[0]). -/
  theorem spec_15 (grid grid' : Slice (alloc.vec.Vec I64)) (d : Int)
      (hgrid : ValidGrid grid) (hgrid' : ValidGrid grid')
      (hdimR : numRows grid' = numRows grid) (hdimC : numCols grid' = numCols grid)
      (hshift : ∀ i j, i < numRows grid → j < numCols grid → cell grid' i j = cell grid i j + d)
      (r r' : I64)
      (hr : maximum_minimum_path grid = ok r) (hr' : maximum_minimum_path grid' = ok r') :
      r'.val = r.val + d := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (grid grid' : Slice (alloc.vec.Vec I64)) (d : Int)
        (hgrid : ValidGrid grid) (hgrid' : ValidGrid grid')
        (hdimR : numRows grid' = numRows grid) (hdimC : numCols grid' = numCols grid)
        (hshift : ∀ i j, i < numRows grid → j < numCols grid → cell grid' i j = cell grid i j + d)
        (r r' : I64)
        (hr : maximum_minimum_path grid = ok r) (hr' : maximum_minimum_path grid' = ok r'), r'.val = r.val + d) := by
    sorry

  /-- Let grid^T be the n x m matrix with grid^T[j][i] = grid[i][j]. Whenever maximum_minimum_path grid returns r and maximum_minimum_path grid^T returns r^T, we have r = r^T.
    Preconditions: The input grid satisfies the problem constraints: let m = len(grid) and n = len(grid[0]); then 1 <= m <= 100, 1 <= n <= 100, for every i with 0 <= i < m we have len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= grid[i][j] <= 10^9. -/
  theorem spec_16 (grid gridT : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
      (hdimR : numRows gridT = numCols grid) (hdimC : numCols gridT = numRows grid)
      (htrans : ∀ i j, i < numRows grid → j < numCols grid → cell gridT j i = cell grid i j)
      (r rT : I64)
      (hr : maximum_minimum_path grid = ok r) (hrT : maximum_minimum_path gridT = ok rT) :
      r.val = rT.val := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (grid gridT : Slice (alloc.vec.Vec I64)) (hgrid : ValidGrid grid)
        (hdimR : numRows gridT = numCols grid) (hdimC : numCols gridT = numRows grid)
        (htrans : ∀ i j, i < numRows grid → j < numCols grid → cell gridT j i = cell grid i j)
        (r rT : I64)
        (hr : maximum_minimum_path grid = ok r) (hrT : maximum_minimum_path gridT = ok rT), r.val = rT.val) := by
    sorry

  end AegisSpec.MaximumMinimumPath
