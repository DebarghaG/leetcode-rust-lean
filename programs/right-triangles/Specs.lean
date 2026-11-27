import Aegis.NumberOfRightTriangles.Code.Funs

/-!
# Specifications of `Aegis.NumberOfRightTriangles.number_of_right_triangles`

LeetCode problem `right-triangles`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberOfRightTriangles

abbrev nrt : Slice (alloc.vec.Vec I64) → Result I64 :=
  Aegis.NumberOfRightTriangles.number_of_right_triangles

def rowList (grid : Slice (alloc.vec.Vec I64)) : List (List I64) :=
  grid.val.map (fun row => row.val)

def numRows (grid : Slice (alloc.vec.Vec I64)) : ℕ :=
  grid.val.length

def rowLen (grid : Slice (alloc.vec.Vec I64)) (i : ℕ) : ℕ :=
  ((rowList grid).getD i []).length

def numCols (grid : Slice (alloc.vec.Vec I64)) : ℕ :=
  rowLen grid 0

def entry (grid : Slice (alloc.vec.Vec I64)) (i j : ℕ) : ℤ :=
  (((rowList grid).getD i []).getD j 0#i64).val

def IsMatrix (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) : Prop :=
  numRows grid = m ∧ ∀ i, i < m → rowLen grid i = n

def IsZeroOne (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) : Prop :=
  ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1

def oneCells (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range m).product (Finset.range n)).filter (fun p => entry grid p.1 p.2 = 1)

def numOnesInRow (grid : Slice (alloc.vec.Vec I64)) (m n i : ℕ) : ℕ :=
  ((oneCells grid m n).filter (fun p => p.1 = i)).card

def numOnesInCol (grid : Slice (alloc.vec.Vec I64)) (m n j : ℕ) : ℕ :=
  ((oneCells grid m n).filter (fun p => p.2 = j)).card

def contribution (grid : Slice (alloc.vec.Vec I64)) (m n i j : ℕ) : ℤ :=
  ((numOnesInRow grid m n i : ℤ) - 1) * ((numOnesInCol grid m n j : ℤ) - 1)

noncomputable def triangleSum (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) : ℤ :=
  ∑ p ∈ oneCells grid m n, contribution grid m n p.1 p.2

def IsRightAngleTriple (S : Finset (ℕ × ℕ)) : Prop :=
  ∃ i0 j0 i1 j1,
    (i0, j0) ∈ S ∧ (i0, j1) ∈ S ∧ (i1, j0) ∈ S ∧ j0 ≠ j1 ∧ i0 ≠ i1

noncomputable def numRightAngleTriples (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) : ℕ :=
  by
  classical
  exact (((oneCells grid m n).powersetCard 3).filter (fun S => IsRightAngleTriple S)).card

def InsertZeroRow (grid grid' : Slice (alloc.vec.Vec I64)) (m n k : ℕ) : Prop :=
  k ≤ m ∧ IsMatrix grid' (m + 1) n ∧
    (∀ j, j < n → entry grid' k j = 0) ∧
    (∀ i, i < m → ∀ j, j < n →
      entry grid' (if i < k then i else i + 1) j = entry grid i j)

def InsertZeroCol (grid grid' : Slice (alloc.vec.Vec I64)) (m n k : ℕ) : Prop :=
  k ≤ n ∧ IsMatrix grid' m (n + 1) ∧
    (∀ i, i < m → entry grid' i k = 0) ∧
    (∀ i, i < m → ∀ j, j < n →
      entry grid' i (if j < k then j else j + 1) = entry grid i j)

/-- Whenever the function returns a result r, r is exactly the number of 3-element sets S of cells (i,j) of grid such that every cell in S has grid[i][j] = 1 and there is a cell (i0,j0) in S that has the same row as one other cell of S and the same column as the remaining cell of S. Equivalently, r = Σ_{0 <= i < m, 0 <= j < n, grid[i][j] = 1} (R_i - 1) * (C_j - 1), where R_i is the number of columns j' with 0 <= j' < n and grid[i][j'] = 1, and C_j is the number of rows i' with 0 <= i' < m and grid[i'][j] = 1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hres : nrt grid = ok r) :
    r.val = (numRightAngleTriples grid m n : ℤ) ∧ r.val = triangleSum grid m n := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hres : nrt grid = ok r), r.val = (numRightAngleTriples grid m n : ℤ) ∧ r.val = triangleSum grid m n) := by
  sorry

/-- The function returns a result r; for every input satisfying the preconditions it does not fail (no arithmetic overflow, out-of-bounds access, or panic).
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n) :
    ∃ r : I64, nrt grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n), ∃ r : I64, nrt grid = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = m*n*(m-1)*(n-1).
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. Additionally, for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] = 1. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hall : ∀ i j, i < m → j < n → entry grid i j = 1)
    (hres : nrt grid = ok r) :
    r.val = (m : ℤ) * (n : ℤ) * ((m : ℤ) - 1) * ((n : ℤ) - 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hall : ∀ i j, i < m → j < n → entry grid i j = 1)
    (hres : nrt grid = ok r), r.val = (m : ℤ) * (n : ℤ) * ((m : ℤ) - 1) * ((n : ℤ) - 1)) := by
  sorry

/-- Let K be the number of pairs (i,j) with 0 <= i < m, 0 <= j < n, and grid[i][j] = 1. Whenever the function returns a result r, r <= (m-1)*(n-1)*K.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hres : nrt grid = ok r) :
    r.val ≤ ((m : ℤ) - 1) * ((n : ℤ) - 1) * ((oneCells grid m n).card : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hres : nrt grid = ok r), r.val ≤ ((m : ℤ) - 1) * ((n : ℤ) - 1) * ((oneCells grid m n).card : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, if grid[i0][j0] = 1 then r = (R_i0 - 1)*(C_j0 - 1), and if grid[i0][j0] = 0 then r = 0, where R_i0 is the number of 1s in row i0 and C_j0 is the number of 1s in column j0.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. There is exactly one row i0 containing at least two 1s, and exactly one column j0 containing at least two 1s. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec I64)) (m n i0 j0 : ℕ) (r : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hi0 : i0 < m) (hj0 : j0 < n)
    (hrow : ∀ i, i < m → (2 ≤ numOnesInRow grid m n i ↔ i = i0))
    (hcol : ∀ j, j < n → (2 ≤ numOnesInCol grid m n j ↔ j = j0))
    (hres : nrt grid = ok r) :
    (entry grid i0 j0 = 1 →
        r.val = ((numOnesInRow grid m n i0 : ℤ) - 1) * ((numOnesInCol grid m n j0 : ℤ) - 1)) ∧
      (entry grid i0 j0 = 0 → r.val = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n i0 j0 : ℕ) (r : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hi0 : i0 < m) (hj0 : j0 < n)
    (hrow : ∀ i, i < m → (2 ≤ numOnesInRow grid m n i ↔ i = i0))
    (hcol : ∀ j, j < n → (2 ≤ numOnesInCol grid m n j ↔ j = j0))
    (hres : nrt grid = ok r), (entry grid i0 j0 = 1 →
        r.val = ((numOnesInRow grid m n i0 : ℤ) - 1) * ((numOnesInCol grid m n j0 : ℤ) - 1)) ∧
      (entry grid i0 j0 = 0 → r.val = 0)) := by
  sorry

/-- Whenever the function returns a result r, if either every row i has at most one j with grid[i][j] = 1, or every column j has at most one i with grid[i][j] = 1, then r = 0.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hsparse : (∀ i, i < m → numOnesInRow grid m n i ≤ 1) ∨
      (∀ j, j < n → numOnesInCol grid m n j ≤ 1))
    (hres : nrt grid = ok r) :
    r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hsparse : (∀ i, i < m → numOnesInRow grid m n i ≤ 1) ∨
      (∀ j, j < n → numOnesInCol grid m n j ≤ 1))
    (hres : nrt grid = ok r), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r with r > 0, there exist rows i != i' and columns j != j' such that grid[i][j] = 1, grid[i][j'] = 1, and grid[i'][j] = 1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hres : nrt grid = ok r) (hpos : 0 < r.val) :
    ∃ i i' j j', i < m ∧ i' < m ∧ j < n ∧ j' < n ∧ i ≠ i' ∧ j ≠ j' ∧
      entry grid i j = 1 ∧ entry grid i j' = 1 ∧ entry grid i' j = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hres : nrt grid = ok r) (hpos : 0 < r.val), ∃ i i' j j', i < m ∧ i' < m ∧ j < n ∧ j' < n ∧ i ≠ i' ∧ j ≠ j' ∧
      entry grid i j = 1 ∧ entry grid i j' = 1 ∧ entry grid i' j = 1) := by
  sorry

/-- Let gridT be the n by m matrix defined by gridT[j][i] = grid[i][j] for 0 <= i < m and 0 <= j < n. Whenever the function returns r on grid and rT on gridT, r = rT.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. -/
theorem spec_8 (grid gridT : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r rT : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hTmatrix : IsMatrix gridT n m)
    (hT : ∀ i j, i < n → j < m → entry gridT i j = entry grid j i)
    (hres : nrt grid = ok r) (hresT : nrt gridT = ok rT) :
    r.val = rT.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid gridT : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r rT : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hTmatrix : IsMatrix gridT n m)
    (hT : ∀ i j, i < n → j < m → entry gridT i j = entry grid j i)
    (hres : nrt grid = ok r) (hresT : nrt gridT = ok rT), r.val = rT.val) := by
  sorry

/-- For every permutation p of {0,...,m-1} and every permutation q of {0,...,n-1}, let grid' be the m by n matrix defined by grid'[i][j] = grid[p(i)][q(j)] for 0 <= i < m and 0 <= j < n. Whenever the function returns r on grid and r' on grid', r = r'.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. -/
theorem spec_9 (grid grid' : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r r' : I64)
    (p q : ℕ → ℕ)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hp : ∀ i, i < m → p i < m) (hp_surj : ∀ i, i < m → ∃ i', i' < m ∧ p i' = i)
    (hq : ∀ j, j < n → q j < n) (hq_surj : ∀ j, j < n → ∃ j', j' < n ∧ q j' = j)
    (hmatrix' : IsMatrix grid' m n)
    (hcell : ∀ i j, i < m → j < n → entry grid' i j = entry grid (p i) (q j))
    (hres : nrt grid = ok r) (hres' : nrt grid' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r r' : I64)
    (p q : ℕ → ℕ)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hp : ∀ i, i < m → p i < m) (hp_surj : ∀ i, i < m → ∃ i', i' < m ∧ p i' = i)
    (hq : ∀ j, j < n → q j < n) (hq_surj : ∀ j, j < n → ∃ j', j' < n ∧ q j' = j)
    (hmatrix' : IsMatrix grid' m n)
    (hcell : ∀ i j, i < m → j < n → entry grid' i j = entry grid (p i) (q j))
    (hres : nrt grid = ok r) (hres' : nrt grid' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns r on grid and r' on grid', r <= r'.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Both grid and grid' are m by n matrices satisfying 1 <= m <= 1000, 1 <= n <= 1000, every row has length n, every entry is 0 or 1, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] <= grid'[i][j]. -/
theorem spec_10 (grid grid' : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r r' : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hmatrix' : IsMatrix grid' m n) (hzeroone' : IsZeroOne grid' m n)
    (hle : ∀ i j, i < m → j < n → entry grid i j ≤ entry grid' i j)
    (hres : nrt grid = ok r) (hres' : nrt grid' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r r' : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hmatrix' : IsMatrix grid' m n) (hzeroone' : IsZeroOne grid' m n)
    (hle : ∀ i j, i < m → j < n → entry grid i j ≤ entry grid' i j)
    (hres : nrt grid = ok r) (hres' : nrt grid' = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever the function returns r on grid and r' on grid', r = r'.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. Let grid' be obtained from grid either by inserting one all-zero row (giving an (m+1) by n matrix with m < 1000) or by inserting one all-zero column (giving an m by (n+1) matrix with n < 1000); the old rows or columns appear in the same relative order. -/
theorem spec_11 (grid grid' : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r r' : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hins : (m < 1000 ∧ ∃ k, InsertZeroRow grid grid' m n k) ∨
      (n < 1000 ∧ ∃ k, InsertZeroCol grid grid' m n k))
    (hres : nrt grid = ok r) (hres' : nrt grid' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r r' : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hins : (m < 1000 ∧ ∃ k, InsertZeroRow grid grid' m n k) ∨
      (n < 1000 ∧ ∃ k, InsertZeroCol grid grid' m n k))
    (hres : nrt grid = ok r) (hres' : nrt grid' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every cell (i,j) with 0 <= i < m, 0 <= j < n, and grid[i][j] = 1, either R_i = 1 or C_j = 1, where R_i is the number of 1s in row i and C_j is the number of 1s in column j. Equivalently, r > 0 if and only if there exist i,i',j,j' with 0 <= i < m, 0 <= i' < m, i != i', 0 <= j < n, 0 <= j' < n, j != j', and grid[i][j] = grid[i][j'] = grid[i'][j] = 1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. -/
theorem spec_12 (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hres : nrt grid = ok r) :
    (r.val = 0 ↔ ∀ i j, i < m → j < n → entry grid i j = 1 →
      (numOnesInRow grid m n i = 1 ∨ numOnesInCol grid m n j = 1)) ∧
      (0 < r.val ↔ ∃ i i' j j', i < m ∧ i' < m ∧ j < n ∧ j' < n ∧ i ≠ i' ∧ j ≠ j' ∧
        entry grid i j = 1 ∧ entry grid i j' = 1 ∧ entry grid i' j = 1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (r : I64)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hmatrix : IsMatrix grid m n) (hzeroone : IsZeroOne grid m n)
    (hres : nrt grid = ok r), (r.val = 0 ↔ ∀ i j, i < m → j < n → entry grid i j = 1 →
      (numOnesInRow grid m n i = 1 ∨ numOnesInCol grid m n j = 1)) ∧
      (0 < r.val ↔ ∃ i i' j j', i < m ∧ i' < m ∧ j < n ∧ j' < n ∧ i ≠ i' ∧ j ≠ j' ∧
        entry grid i j = 1 ∧ entry grid i j' = 1 ∧ entry grid i' j = 1)) := by
  sorry

end AegisSpec.NumberOfRightTriangles
