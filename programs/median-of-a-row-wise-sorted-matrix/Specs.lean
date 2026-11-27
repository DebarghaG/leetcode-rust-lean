import Aegis.MatrixMedian.Code.Funs

/-!
# Specifications of `Aegis.MatrixMedian.matrix_median`

LeetCode problem `median-of-a-row-wise-sorted-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MatrixMedian (matrix_median)

namespace AegisSpec.MatrixMedian

def rowVals (row : alloc.vec.Vec I64) : List ℤ := row.val.map (fun x => x.val)

def flatVals (grid : Slice (alloc.vec.Vec I64)) : List ℤ := grid.val.flatMap rowVals

def numRows (grid : Slice (alloc.vec.Vec I64)) : ℕ := grid.val.length

def numCols (grid : Slice (alloc.vec.Vec I64)) : ℕ :=
  match grid.val with
  | [] => 0
  | row :: _ => row.val.length

def totalEntries (grid : Slice (alloc.vec.Vec I64)) : ℕ := numRows grid * numCols grid

def medianIndex (grid : Slice (alloc.vec.Vec I64)) : ℕ := (totalEntries grid - 1) / 2

def halfTarget (grid : Slice (alloc.vec.Vec I64)) : ℕ := (totalEntries grid + 1) / 2

def SortedNondec : List ℤ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a ≤ b ∧ SortedNondec (b :: rest)

def sortedVals (grid : Slice (alloc.vec.Vec I64)) : List ℤ := (flatVals grid).mergeSort

def entryAt (grid : Slice (alloc.vec.Vec I64)) (i j : ℕ) : Option ℤ :=
  match grid.val[i]? with
  | none => none
  | some row => (rowVals row)[j]?

def midVals (grid : Slice (alloc.vec.Vec I64)) : List ℤ :=
  grid.val.filterMap (fun row => (rowVals row)[(numCols grid - 1) / 2]?)

def occursIn (grid : Slice (alloc.vec.Vec I64)) (v : ℤ) : Prop := v ∈ flatVals grid

def IsMinOf (l : List ℤ) (lo : ℤ) : Prop := (∀ v ∈ l, lo ≤ v) ∧ lo ∈ l

def IsMaxOf (l : List ℤ) (hi : ℤ) : Prop := (∀ v ∈ l, v ≤ hi) ∧ hi ∈ l

def countLT (grid : Slice (alloc.vec.Vec I64)) (v : ℤ) : ℕ :=
  (flatVals grid).countP (fun x => decide (x < v))

def countLE (grid : Slice (alloc.vec.Vec I64)) (v : ℤ) : ℕ :=
  (flatVals grid).countP (fun x => decide (x ≤ v))

def countGT (grid : Slice (alloc.vec.Vec I64)) (v : ℤ) : ℕ :=
  (flatVals grid).countP (fun x => decide (v < x))

def countGE (grid : Slice (alloc.vec.Vec I64)) (v : ℤ) : ℕ :=
  (flatVals grid).countP (fun x => decide (v ≤ x))

def ValidInput (grid : Slice (alloc.vec.Vec I64)) : Prop :=
  1 ≤ numRows grid ∧ numRows grid ≤ 500 ∧ numRows grid % 2 = 1 ∧
  1 ≤ numCols grid ∧ numCols grid ≤ 500 ∧ numCols grid % 2 = 1 ∧
  (∀ row ∈ grid.val, row.val.length = numCols grid ∧ SortedNondec (rowVals row)) ∧
  (∀ v ∈ flatVals grid, 1 ≤ v ∧ v ≤ 1000000)

/-- Let total = m*n, k = (total - 1)/2, and let flat be the list of length total obtained by sorting, in non-decreasing order, all entries grid[i][j] (0 <= i < m, 0 <= j < n) counted with multiplicity. The function returns a result r and r = flat[k] (0-indexed), i.e. r is the k-th smallest matrix entry counted with multiplicity. Equivalently, at most k entries are strictly less than r and at most k entries are strictly greater than r.
  Preconditions: Let m = len(grid) and n = len(grid[i]) for each i (all rows of grid have common length n). Assume 1 <= m <= 500, 1 <= n <= 500, m is odd, n is odd, each row grid[i] is sorted in non-decreasing order (grid[i][j] <= grid[i][j+1] for all 0 <= j < n-1), and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid) :
    ∃ r : I64,
      matrix_median grid = ok r ∧
        (sortedVals grid)[medianIndex grid]? = some r.val ∧
        countLT grid r.val ≤ medianIndex grid ∧
        countGT grid r.val ≤ medianIndex grid := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid), ∃ r : I64,
      matrix_median grid = ok r ∧
        (sortedVals grid)[medianIndex grid]? = some r.val ∧
        countLT grid r.val ≤ medianIndex grid ∧
        countGT grid r.val ≤ medianIndex grid) := by
  sorry

/-- For every grid satisfying the preconditions, the function returns a result r; it does not fail (no panic, arithmetic overflow, or out-of-bounds access).
  Preconditions: Let m = len(grid) and n = len(grid[i]) for each i (all rows of grid have common length n). Assume 1 <= m <= 500, 1 <= n <= 500, m is odd, n is odd, each row grid[i] is sorted in non-decreasing order (grid[i][j] <= grid[i][j+1] for all 0 <= j < n-1), and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid) :
    ∃ r : I64, matrix_median grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid), ∃ r : I64, matrix_median grid = ok r) := by
  sorry

/-- Whenever the function returns a result r, there exist indices i and j with 0 <= i < m and 0 <= j < n such that grid[i][j] = r.
  Preconditions: Let m = len(grid) and n = len(grid[i]) for each i (all rows of grid have common length n). Assume 1 <= m <= 500, 1 <= n <= 500, m is odd, n is odd, each row grid[i] is sorted in non-decreasing order (grid[i][j] <= grid[i][j+1] for all 0 <= j < n-1), and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid) (r : I64)
    (hr : matrix_median grid = ok r) :
    ∃ i j : ℕ, i < numRows grid ∧ j < numCols grid ∧ entryAt grid i j = some r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid) (r : I64)
    (hr : matrix_median grid = ok r), ∃ i j : ℕ, i < numRows grid ∧ j < numCols grid ∧ entryAt grid i j = some r.val) := by
  sorry

/-- Whenever the function returns a result r, lo <= r <= hi, where lo = min{grid[i][j] : 0 <= i < m, 0 <= j < n} and hi = max{grid[i][j] : 0 <= i < m, 0 <= j < n}.
  Preconditions: Let m = len(grid) and n = len(grid[i]) for each i (all rows of grid have common length n). Assume 1 <= m <= 500, 1 <= n <= 500, m is odd, n is odd, each row grid[i] is sorted in non-decreasing order (grid[i][j] <= grid[i][j+1] for all 0 <= j < n-1), and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid) (r : I64)
    (hr : matrix_median grid = ok r) (lo hi : ℤ)
    (hlo : IsMinOf (flatVals grid) lo) (hhi : IsMaxOf (flatVals grid) hi) :
    lo ≤ r.val ∧ r.val ≤ hi := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid) (r : I64)
    (hr : matrix_median grid = ok r) (lo hi : ℤ)
    (hlo : IsMinOf (flatVals grid) lo) (hhi : IsMaxOf (flatVals grid) hi), lo ≤ r.val ∧ r.val ≤ hi) := by
  sorry

/-- For each i with 0 <= i < m let a_i = grid[i][(n-1)/2], the middle entry of the sorted row i (n is odd, so this index is valid). Whenever the function returns a result r, min{a_i : 0 <= i < m} <= r <= max{a_i : 0 <= i < m}.
  Preconditions: Let m = len(grid) and n = len(grid[i]) for each i (all rows of grid have common length n). Assume 1 <= m <= 500, 1 <= n <= 500, m is odd, n is odd, each row grid[i] is sorted in non-decreasing order (grid[i][j] <= grid[i][j+1] for all 0 <= j < n-1), and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid) (r : I64)
    (hr : matrix_median grid = ok r) (lo hi : ℤ)
    (hlo : IsMinOf (midVals grid) lo) (hhi : IsMaxOf (midVals grid) hi) :
    lo ≤ r.val ∧ r.val ≤ hi := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid) (r : I64)
    (hr : matrix_median grid = ok r) (lo hi : ℤ)
    (hlo : IsMinOf (midVals grid) lo) (hhi : IsMaxOf (midVals grid) hi), lo ≤ r.val ∧ r.val ≤ hi) := by
  sorry

/-- Whenever the function returns a result r, the number of pairs (i,j) with 0 <= i < m, 0 <= j < n and grid[i][j] <= r is at least (m*n + 1)/2.
  Preconditions: Let m = len(grid) and n = len(grid[i]) for each i (all rows of grid have common length n). Assume 1 <= m <= 500, 1 <= n <= 500, m is odd, n is odd, each row grid[i] is sorted in non-decreasing order (grid[i][j] <= grid[i][j+1] for all 0 <= j < n-1), and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid) (r : I64)
    (hr : matrix_median grid = ok r) :
    halfTarget grid ≤ countLE grid r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid) (r : I64)
    (hr : matrix_median grid = ok r), halfTarget grid ≤ countLE grid r.val) := by
  sorry

/-- Whenever the function returns a result r, the number of pairs (i,j) with 0 <= i < m, 0 <= j < n and grid[i][j] < r is at most (m*n - 1)/2.
  Preconditions: Let m = len(grid) and n = len(grid[i]) for each i (all rows of grid have common length n). Assume 1 <= m <= 500, 1 <= n <= 500, m is odd, n is odd, each row grid[i] is sorted in non-decreasing order (grid[i][j] <= grid[i][j+1] for all 0 <= j < n-1), and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid) (r : I64)
    (hr : matrix_median grid = ok r) :
    countLT grid r.val ≤ medianIndex grid := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid) (r : I64)
    (hr : matrix_median grid = ok r), countLT grid r.val ≤ medianIndex grid) := by
  sorry

/-- Whenever the function returns a result r, the number of pairs (i,j) with 0 <= i < m, 0 <= j < n and grid[i][j] > r is at most (m*n - 1)/2.
  Preconditions: Let m = len(grid) and n = len(grid[i]) for each i (all rows of grid have common length n). Assume 1 <= m <= 500, 1 <= n <= 500, m is odd, n is odd, each row grid[i] is sorted in non-decreasing order (grid[i][j] <= grid[i][j+1] for all 0 <= j < n-1), and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_8 (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid) (r : I64)
    (hr : matrix_median grid = ok r) :
    countGT grid r.val ≤ medianIndex grid := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid) (r : I64)
    (hr : matrix_median grid = ok r), countGT grid r.val ≤ medianIndex grid) := by
  sorry

/-- Whenever the function returns a result r, r is the smallest integer v such that the number of pairs (i,j) with 0 <= i < m, 0 <= j < n and grid[i][j] <= v is at least (m*n + 1)/2.
  Preconditions: Let m = len(grid) and n = len(grid[i]) for each i (all rows of grid have common length n). Assume 1 <= m <= 500, 1 <= n <= 500, m is odd, n is odd, each row grid[i] is sorted in non-decreasing order (grid[i][j] <= grid[i][j+1] for all 0 <= j < n-1), and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_9 (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid) (r : I64)
    (hr : matrix_median grid = ok r) :
    halfTarget grid ≤ countLE grid r.val ∧
      ∀ v : ℤ, halfTarget grid ≤ countLE grid v → r.val ≤ v := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid) (r : I64)
    (hr : matrix_median grid = ok r), halfTarget grid ≤ countLE grid r.val ∧
      ∀ v : ℤ, halfTarget grid ≤ countLE grid v → r.val ≤ v) := by
  sorry

/-- Let π be any permutation of {0, 1, ..., m-1}, and let grid' be the length-m slice defined by grid'[i] = grid[π(i)] for 0 <= i < m. Then grid' satisfies the preconditions, and whenever the function returns r on grid and r' on grid', one has r = r'.
  Preconditions: Let m = len(grid) and n = len(grid[i]) for each i (all rows of grid have common length n). Assume 1 <= m <= 500, 1 <= n <= 500, m is odd, n is odd, each row grid[i] is sorted in non-decreasing order (grid[i][j] <= grid[i][j+1] for all 0 <= j < n-1), and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_10 (grid grid' : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid)
    (hperm : List.Perm grid'.val grid.val) (r r' : I64)
    (hr : matrix_median grid = ok r) (hr' : matrix_median grid' = ok r') :
    ValidInput grid' ∧ r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid)
    (hperm : List.Perm grid'.val grid.val) (r r' : I64)
    (hr : matrix_median grid = ok r) (hr' : matrix_median grid' = ok r'), ValidInput grid' ∧ r = r') := by
  sorry

/-- Whenever the function returns a result r, r is the largest integer v such that the number of pairs (i,j) with 0 <= i < m, 0 <= j < n and grid[i][j] >= v is at least (m*n + 1)/2.
  Preconditions: Let m = len(grid) and n = len(grid[i]) for each i (all rows of grid have common length n). Assume 1 <= m <= 500, 1 <= n <= 500, m is odd, n is odd, each row grid[i] is sorted in non-decreasing order (grid[i][j] <= grid[i][j+1] for all 0 <= j < n-1), and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_11 (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid) (r : I64)
    (hr : matrix_median grid = ok r) :
    halfTarget grid ≤ countGE grid r.val ∧
      ∀ v : ℤ, halfTarget grid ≤ countGE grid v → v ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid) (r : I64)
    (hr : matrix_median grid = ok r), halfTarget grid ≤ countGE grid r.val ∧
      ∀ v : ℤ, halfTarget grid ≤ countGE grid v → v ≤ r.val) := by
  sorry

/-- Whenever the function returns r on grid and r' on grid', we have r <= r'.
  Preconditions: Let grid and grid' both satisfy the common preconditions: same odd dimensions 1 <= m,n <= 500, all rows have length n and are non-decreasing, and all entries lie in [1,1000000]. Assume grid[i][j] <= grid'[i][j] for all 0 <= i < m and 0 <= j < n. -/
theorem spec_12 (grid grid' : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid)
    (hpre' : ValidInput grid') (hrows : numRows grid = numRows grid')
    (hcols : numCols grid = numCols grid')
    (hmono : ∀ (i j : ℕ) (v w : ℤ), entryAt grid i j = some v → entryAt grid' i j = some w →
      v ≤ w)
    (r r' : I64) (hr : matrix_median grid = ok r) (hr' : matrix_median grid' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec I64)) (hpre : ValidInput grid)
    (hpre' : ValidInput grid') (hrows : numRows grid = numRows grid')
    (hcols : numCols grid = numCols grid')
    (hmono : ∀ (i j : ℕ) (v w : ℤ), entryAt grid i j = some v → entryAt grid' i j = some w →
      v ≤ w)
    (r r' : I64) (hr : matrix_median grid = ok r) (hr' : matrix_median grid' = ok r'), r.val ≤ r'.val) := by
  sorry

end AegisSpec.MatrixMedian
