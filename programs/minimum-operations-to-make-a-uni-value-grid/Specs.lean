import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-make-a-uni-value-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinOperations

  def rows (grid : Slice (alloc.vec.Vec I64)) : List (List ℤ) :=
    grid.val.map (fun row => row.val.map (fun v => v.val))

  def entries (grid : Slice (alloc.vec.Vec I64)) : List ℤ :=
    (rows grid).flatten

  def cell (grid : Slice (alloc.vec.Vec I64)) (i j : ℕ) : Option ℤ :=
    match (rows grid)[i]? with
    | some row => row[j]?
    | none => none

  def numRows (grid : Slice (alloc.vec.Vec I64)) : ℕ :=
    (rows grid).length

  def rowLen (grid : Slice (alloc.vec.Vec I64)) : ℕ :=
    ((rows grid).head?).getD [] |>.length

  def numCells (grid : Slice (alloc.vec.Vec I64)) : ℕ :=
    numRows grid * rowLen grid

  def shape (grid : Slice (alloc.vec.Vec I64)) : List ℕ :=
    (rows grid).map List.length

  def Congruent (grid : Slice (alloc.vec.Vec I64)) (x : ℤ) : Prop :=
    ∀ (i j k l : ℕ) (a b : ℤ), cell grid i j = some a → cell grid k l = some b → x ∣ a - b

  def AllEqual (grid : Slice (alloc.vec.Vec I64)) : Prop :=
    ∀ a ∈ entries grid, ∀ b ∈ entries grid, a = b

  def sortedEntries (grid : Slice (alloc.vec.Vec I64)) : List ℤ :=
    (entries grid).mergeSort (· ≤ ·)

  def costAt (s : List ℤ) (k : ℕ) : ℤ :=
    (s.map (fun v => |v - s.getD k 0|)).sum

  def medianCost (grid : Slice (alloc.vec.Vec I64)) : ℤ :=
    costAt (sortedEntries grid) ((entries grid).length / 2)

  def minOpt : List ℤ → Option ℤ
    | [] => none
    | a :: l => some (l.foldr min a)

  def maxOpt : List ℤ → Option ℤ
    | [] => none
    | a :: l => some (l.foldr max a)

  def CommonPre (grid : Slice (alloc.vec.Vec I64)) (x : I64) : Prop :=
    1 ≤ numRows grid ∧
    (∀ r ∈ rows grid, r ≠ []) ∧
    (∀ r ∈ rows grid, r.length = rowLen grid) ∧
    1 ≤ numCells grid ∧ numCells grid ≤ 100000 ∧
    1 ≤ x.val ∧ x.val ≤ 10000 ∧
    (∀ a ∈ entries grid, 1 ≤ a ∧ a ≤ 10000)

  /-- The function returns a result r and does not fail. Let N = m*n and let s[0] <= s[1] <= ... <= s[N-1] be the nondecreasing list of all entries of grid over all cells. If not all entries of grid are congruent modulo x (that is, some difference grid[i][j] - grid[k][l] is not divisible by x), then r = -1. If all entries of grid are congruent modulo x, then r = (sum_{i=0}^{N-1} abs(s[i] - s[floor(N/2)])) / x.
    Preconditions: Let m = len(grid). It is assumed that m >= 1, every row of grid is nonempty, all rows of grid have the same length n = len(grid[0]), 1 <= m*n <= 100000, x is an integer with 1 <= x <= 10000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 10000. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec I64)) (x : I64) (h : CommonPre grid x) :
      ∃ r, Aegis.MinOperations.min_operations grid x = ok r ∧
        (¬ Congruent grid x.val → r.val = -1) ∧
        (Congruent grid x.val → r.val = medianCost grid / x.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (x : I64) (h : CommonPre grid x), ∃ r, Aegis.MinOperations.min_operations grid x = ok r ∧
          (¬ Congruent grid x.val → r.val = -1) ∧
          (Congruent grid x.val → r.val = medianCost grid / x.val)) := by
    sorry

  /-- The function returns a result r; it does not fail (no panic, no arithmetic overflow, no out-of-bounds access) for every input satisfying the preconditions.
    Preconditions: Let m = len(grid). It is assumed that m >= 1, every row of grid is nonempty, all rows of grid have the same length n = len(grid[0]), 1 <= m*n <= 100000, x is an integer with 1 <= x <= 10000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 10000. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec I64)) (x : I64) (h : CommonPre grid x) :
      ∃ r, Aegis.MinOperations.min_operations grid x = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (x : I64) (h : CommonPre grid x), ∃ r, Aegis.MinOperations.min_operations grid x = ok r) := by
    sorry

  /-- The function returns a result r, and r = -1 if and only if there exist indices (i,j) and (k,l) with 0 <= i,k < m and 0 <= j,l < n such that x does not divide grid[i][j] - grid[k][l].
    Preconditions: Let m = len(grid). It is assumed that m >= 1, every row of grid is nonempty, all rows of grid have the same length n = len(grid[0]), 1 <= m*n <= 100000, x is an integer with 1 <= x <= 10000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 10000. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec I64)) (x : I64) (h : CommonPre grid x) :
      ∃ r, Aegis.MinOperations.min_operations grid x = ok r ∧
        (r.val = -1 ↔
          ∃ (i j k l : ℕ) (a b : ℤ), cell grid i j = some a ∧ cell grid k l = some b ∧
            ¬ (x.val ∣ a - b)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (x : I64) (h : CommonPre grid x), ∃ r, Aegis.MinOperations.min_operations grid x = ok r ∧
          (r.val = -1 ↔
            ∃ (i j k l : ℕ) (a b : ℤ), cell grid i j = some a ∧ cell grid k l = some b ∧
              ¬ (x.val ∣ a - b))) := by
    sorry

  /-- The function returns a result r, and r = 0 if and only if all entries of grid are equal to each other.
    Preconditions: Let m = len(grid). It is assumed that m >= 1, every row of grid is nonempty, all rows of grid have the same length n = len(grid[0]), 1 <= m*n <= 100000, x is an integer with 1 <= x <= 10000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 10000. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec I64)) (x : I64) (h : CommonPre grid x) :
      ∃ r, Aegis.MinOperations.min_operations grid x = ok r ∧
        (r.val = 0 ↔ AllEqual grid) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (x : I64) (h : CommonPre grid x), ∃ r, Aegis.MinOperations.min_operations grid x = ok r ∧
          (r.val = 0 ↔ AllEqual grid)) := by
    sorry

  /-- The function returns a result r, and for every integer t such that x divides grid[i][j] - t for every cell (i,j), we have r <= (sum_{i=0}^{m-1} sum_{j=0}^{n-1} abs(grid[i][j] - t)) / x.
    Preconditions: Let m = len(grid). It is assumed that m >= 1, every row of grid is nonempty, all rows of grid have the same length n = len(grid[0]), 1 <= m*n <= 100000, x is an integer with 1 <= x <= 10000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 10000. Also assume all entries of grid are congruent modulo x. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec I64)) (x : I64) (h : CommonPre grid x)
      (hc : Congruent grid x.val) :
      ∃ r, Aegis.MinOperations.min_operations grid x = ok r ∧
        ∀ t : ℤ,
          (∀ (i j : ℕ) (a : ℤ), cell grid i j = some a → x.val ∣ a - t) →
            r.val ≤ ((entries grid).map (fun a => |a - t|)).sum / x.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (x : I64) (h : CommonPre grid x)
        (hc : Congruent grid x.val), ∃ r, Aegis.MinOperations.min_operations grid x = ok r ∧
          ∀ t : ℤ,
            (∀ (i j : ℕ) (a : ℤ), cell grid i j = some a → x.val ∣ a - t) →
              r.val ≤ ((entries grid).map (fun a => |a - t|)).sum / x.val) := by
    sorry

  /-- Let N = m*n and let s[0] <= s[1] <= ... <= s[N-1] be all entries of grid sorted nondecreasingly. The function returns a result r, and there exists a median index k with 0 <= k < N (if N is odd then k = (N-1)/2, and if N is even then k = N/2 - 1 or k = N/2) such that r = (sum_{i=0}^{N-1} abs(s[i] - s[k])) / x.
    Preconditions: Let m = len(grid). It is assumed that m >= 1, every row of grid is nonempty, all rows of grid have the same length n = len(grid[0]), 1 <= m*n <= 100000, x is an integer with 1 <= x <= 10000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 10000. Also assume all entries of grid are congruent modulo x. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec I64)) (x : I64) (h : CommonPre grid x)
      (hc : Congruent grid x.val) :
      ∃ r, Aegis.MinOperations.min_operations grid x = ok r ∧
        ∃ k, k < (entries grid).length ∧
          ((entries grid).length % 2 = 1 → k = ((entries grid).length - 1) / 2) ∧
          ((entries grid).length % 2 = 0 →
            (k = (entries grid).length / 2 - 1 ∨ k = (entries grid).length / 2)) ∧
          r.val = costAt (sortedEntries grid) k / x.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (x : I64) (h : CommonPre grid x)
        (hc : Congruent grid x.val), ∃ r, Aegis.MinOperations.min_operations grid x = ok r ∧
          ∃ k, k < (entries grid).length ∧
            ((entries grid).length % 2 = 1 → k = ((entries grid).length - 1) / 2) ∧
            ((entries grid).length % 2 = 0 →
              (k = (entries grid).length / 2 - 1 ∨ k = (entries grid).length / 2)) ∧
            r.val = costAt (sortedEntries grid) k / x.val) := by
    sorry

  /-- Let N = m*n, lo = min_{i,j} grid[i][j], and hi = max_{i,j} grid[i][j]. The function returns a result r, and whenever r != -1, 0 <= r <= ((N-1)*(hi-lo))/x.
    Preconditions: Let m = len(grid). It is assumed that m >= 1, every row of grid is nonempty, all rows of grid have the same length n = len(grid[0]), 1 <= m*n <= 100000, x is an integer with 1 <= x <= 10000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 10000. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec I64)) (x : I64) (h : CommonPre grid x) :
      ∃ r, Aegis.MinOperations.min_operations grid x = ok r ∧
        ∀ (lo hi : ℤ), minOpt (entries grid) = some lo → maxOpt (entries grid) = some hi →
          r.val ≠ -1 → 0 ≤ r.val ∧ r.val ≤ ((numCells grid : ℤ) - 1) * (hi - lo) / x.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (x : I64) (h : CommonPre grid x), ∃ r, Aegis.MinOperations.min_operations grid x = ok r ∧
          ∀ (lo hi : ℤ), minOpt (entries grid) = some lo → maxOpt (entries grid) = some hi →
            r.val ≠ -1 → 0 ≤ r.val ∧ r.val ≤ ((numCells grid : ℤ) - 1) * (hi - lo) / x.val) := by
    sorry

  /-- Both min_operations(grid, x) and min_operations(grid2, x) return results, and min_operations(grid2, x) = min_operations(grid, x).
    Preconditions: Let m = len(grid). It is assumed that m >= 1, every row of grid is nonempty, all rows of grid have the same length n = len(grid[0]), 1 <= m*n <= 100000, x is an integer with 1 <= x <= 10000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 10000. Let c be an integer, and define grid2 by grid2[i][j] = grid[i][j] + c*x for all i,j. Assume grid2 also satisfies the same common preconditions with the same m,n,x. -/
  theorem spec_8 (grid grid2 : Slice (alloc.vec.Vec I64)) (x : I64) (c : ℤ)
      (h : CommonPre grid x) (h2 : CommonPre grid2 x) (hshape : shape grid2 = shape grid)
      (hval : ∀ (i j : ℕ) (a : ℤ), cell grid i j = some a → cell grid2 i j = some (a + c * x.val)) :
      ∃ r, Aegis.MinOperations.min_operations grid x = ok r ∧
        Aegis.MinOperations.min_operations grid2 x = ok r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid grid2 : Slice (alloc.vec.Vec I64)) (x : I64) (c : ℤ)
        (h : CommonPre grid x) (h2 : CommonPre grid2 x) (hshape : shape grid2 = shape grid)
        (hval : ∀ (i j : ℕ) (a : ℤ), cell grid i j = some a → cell grid2 i j = some (a + c * x.val)), ∃ r, Aegis.MinOperations.min_operations grid x = ok r ∧
          Aegis.MinOperations.min_operations grid2 x = ok r) := by
    sorry

  /-- Both min_operations(grid, x) and min_operations(grid2, x2) return results, and min_operations(grid2, x2) = min_operations(grid, x).
    Preconditions: Let m = len(grid). It is assumed that m >= 1, every row of grid is nonempty, all rows of grid have the same length n = len(grid[0]), 1 <= m*n <= 100000, x is an integer with 1 <= x <= 10000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 10000. Let c be an integer with c >= 1. Define grid2[i][j] = c * grid[i][j] for all i,j and x2 = c * x. Assume grid2 and x2 satisfy the common preconditions. -/
  theorem spec_9 (grid grid2 : Slice (alloc.vec.Vec I64)) (x x2 : I64) (c : ℤ)
      (h : CommonPre grid x) (h2 : CommonPre grid2 x2) (hc : 1 ≤ c) (hx2 : x2.val = c * x.val)
      (hshape : shape grid2 = shape grid)
      (hval : ∀ (i j : ℕ) (a : ℤ), cell grid i j = some a → cell grid2 i j = some (c * a)) :
      ∃ r, Aegis.MinOperations.min_operations grid x = ok r ∧
        Aegis.MinOperations.min_operations grid2 x2 = ok r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid grid2 : Slice (alloc.vec.Vec I64)) (x x2 : I64) (c : ℤ)
        (h : CommonPre grid x) (h2 : CommonPre grid2 x2) (hc : 1 ≤ c) (hx2 : x2.val = c * x.val)
        (hshape : shape grid2 = shape grid)
        (hval : ∀ (i j : ℕ) (a : ℤ), cell grid i j = some a → cell grid2 i j = some (c * a)), ∃ r, Aegis.MinOperations.min_operations grid x = ok r ∧
          Aegis.MinOperations.min_operations grid2 x2 = ok r) := by
    sorry

  end AegisSpec.MinOperations
