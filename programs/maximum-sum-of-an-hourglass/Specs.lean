import Aegis.MaxSum.Code.Funs

/-!
# Specifications of `Aegis.MaxSum.max_sum`

LeetCode problem `maximum-sum-of-an-hourglass`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxSum

open Aeneas Aeneas.Std Result
open Aegis.MaxSum

abbrev Grid := Slice (alloc.vec.Vec I64)

def row (grid : Grid) (i : ℕ) : List ℤ :=
  match grid.val[i]? with
  | some v => v.val.map (fun x => x.val)
  | none => []

def cell (grid : Grid) (i j : ℕ) : ℤ :=
  (row grid i)[j]?.getD 0

def septomino (grid : Grid) (i j : ℕ) : ℤ :=
  cell grid i j + cell grid i (j + 1) + cell grid i (j + 2) + cell grid (i + 1) (j + 1) +
    cell grid (i + 2) j + cell grid (i + 2) (j + 1) + cell grid (i + 2) (j + 2)

def IsMaxPyramid (grid : Grid) (m n : ℕ) (r : ℤ) : Prop :=
  (∀ i j, i + 3 ≤ m → j + 3 ≤ n → septomino grid i j ≤ r) ∧
    ∃ i j, i + 3 ≤ m ∧ j + 3 ≤ n ∧ septomino grid i j = r

def IsMaxPyramidRow (grid : Grid) (i n : ℕ) (r : ℤ) : Prop :=
  (∀ j, j + 3 ≤ n → septomino grid i j ≤ r) ∧
    ∃ j, j + 3 ≤ n ∧ septomino grid i j = r

def IsMaxPyramidCol (grid : Grid) (m j : ℕ) (r : ℤ) : Prop :=
  (∀ i, i + 3 ≤ m → septomino grid i j ≤ r) ∧
    ∃ i, i + 3 ≤ m ∧ septomino grid i j = r

def totalSum (grid : Grid) (m n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, cell grid i j

def revVec (v : alloc.vec.Vec I64) : alloc.vec.Vec I64 :=
  ⟨⟨v.val.reverse.length, Aeneas.Data.ListN.ListN.fromList v.val.reverse, by simp⟩⟩

def mirrorLR (grid : Grid) : Grid :=
  let l := grid.val.map revVec
  ⟨l.length, Aeneas.Data.ListN.ListN.fromList l, by simp [l]⟩

def mirrorUD (grid : Grid) : Grid :=
  let l := grid.val.reverse
  ⟨l.length, Aeneas.Data.ListN.ListN.fromList l, by simp [l]⟩

/-- The function returns a result r and r = max { grid[i][j] + grid[i][j+1] + grid[i][j+2] + grid[i+1][j+1] + grid[i+2][j] + grid[i+2][j+1] + grid[i+2][j+2] | 0 <= i <= m-3 and 0 <= j <= n-3 }.
  Preconditions: Writing m = len(grid) and n = len(grid[0]), the input satisfies m >= 3, n >= 3, m <= 150, n <= 150, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 1_000_000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_1 (grid : Grid) (m n : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000) :
    ∃ r, max_sum grid = ok r ∧ IsMaxPyramid grid m n r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000), ∃ r, max_sum grid = ok r ∧ IsMaxPyramid grid m n r.val) := by
  sorry

/-- The function returns a result r; in particular it does not fail, panic, or overflow.
  Preconditions: Writing m = len(grid) and n = len(grid[0]), the input satisfies m >= 3, n >= 3, m <= 150, n <= 150, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 1_000_000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_2 (grid : Grid) (m n : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000) :
    ∃ r, max_sum grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000), ∃ r, max_sum grid = ok r) := by
  sorry

/-- The function returns a result r and r >= 0.
  Preconditions: Writing m = len(grid) and n = len(grid[0]), the input satisfies m >= 3, n >= 3, m <= 150, n <= 150, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 1_000_000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_3 (grid : Grid) (m n : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000) :
    ∃ r, max_sum grid = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000), ∃ r, max_sum grid = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= 7_000_000.
  Preconditions: Writing m = len(grid) and n = len(grid[0]), the input satisfies m >= 3, n >= 3, m <= 150, n <= 150, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 1_000_000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_4 (grid : Grid) (m n : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000) :
    ∃ r, max_sum grid = ok r ∧ r.val ≤ 7000000 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000), ∃ r, max_sum grid = ok r ∧ r.val ≤ 7000000) := by
  sorry

/-- The function returns a result r and, for every i and j with 0 <= i <= m-3 and 0 <= j <= n-3, grid[i][j] + grid[i][j+1] + grid[i][j+2] + grid[i+1][j+1] + grid[i+2][j] + grid[i+2][j+1] + grid[i+2][j+2] <= r.
  Preconditions: Writing m = len(grid) and n = len(grid[0]), the input satisfies m >= 3, n >= 3, m <= 150, n <= 150, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 1_000_000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_5 (grid : Grid) (m n : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000) :
    ∃ r, max_sum grid = ok r ∧ ∀ i j, i + 3 ≤ m → j + 3 ≤ n → septomino grid i j ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000), ∃ r, max_sum grid = ok r ∧ ∀ i j, i + 3 ≤ m → j + 3 ≤ n → septomino grid i j ≤ r.val) := by
  sorry

/-- The function returns a result r and there exist i and j with 0 <= i <= m-3 and 0 <= j <= n-3 such that grid[i][j] + grid[i][j+1] + grid[i][j+2] + grid[i+1][j+1] + grid[i+2][j] + grid[i+2][j+1] + grid[i+2][j+2] = r.
  Preconditions: Writing m = len(grid) and n = len(grid[0]), the input satisfies m >= 3, n >= 3, m <= 150, n <= 150, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 1_000_000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_6 (grid : Grid) (m n : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000) :
    ∃ r, max_sum grid = ok r ∧ ∃ i j, i + 3 ≤ m ∧ j + 3 ≤ n ∧ septomino grid i j = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000), ∃ r, max_sum grid = ok r ∧ ∃ i j, i + 3 ≤ m ∧ j + 3 ≤ n ∧ septomino grid i j = r.val) := by
  sorry

/-- The function returns a result r and r = grid[0][0] + grid[0][1] + grid[0][2] + grid[1][1] + grid[2][0] + grid[2][1] + grid[2][2].
  Preconditions: Writing m = len(grid) and n = len(grid[0]), the input satisfies m = 3, n = 3, len(grid[i]) = 3 for every 0 <= i < 3, and 0 <= grid[i][j] <= 1_000_000 for every 0 <= i < 3 and 0 <= j < 3. -/
theorem spec_7 (grid : Grid)
    (hm : grid.val.length = 3)
    (hlen : ∀ i, i < 3 → (row grid i).length = 3)
    (hval : ∀ i j, i < 3 → j < 3 → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000) :
    ∃ r, max_sum grid = ok r ∧
      r.val = cell grid 0 0 + cell grid 0 1 + cell grid 0 2 + cell grid 1 1 +
        cell grid 2 0 + cell grid 2 1 + cell grid 2 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Grid)
    (hm : grid.val.length = 3)
    (hlen : ∀ i, i < 3 → (row grid i).length = 3)
    (hval : ∀ i j, i < 3 → j < 3 → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000), ∃ r, max_sum grid = ok r ∧
      r.val = cell grid 0 0 + cell grid 0 1 + cell grid 0 2 + cell grid 1 1 +
        cell grid 2 0 + cell grid 2 1 + cell grid 2 2) := by
  sorry

/-- The function returns a result r and r = 7*c.
  Preconditions: Writing m = len(grid) and n = len(grid[0]), the input satisfies m >= 3, n >= 3, m <= 150, n <= 150, len(grid[i]) = n for every 0 <= i < m, and there exists an integer c with 0 <= c <= 1_000_000 such that grid[i][j] = c for every 0 <= i < m and 0 <= j < n. -/
theorem spec_8 (grid : Grid) (m n : ℕ) (c : ℤ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1000000)
    (hconst : ∀ i j, i < m → j < n → cell grid i j = c) :
    ∃ r, max_sum grid = ok r ∧ r.val = 7 * c := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (c : ℤ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1000000)
    (hconst : ∀ i j, i < m → j < n → cell grid i j = c), ∃ r, max_sum grid = ok r ∧ r.val = 7 * c) := by
  sorry

/-- Let grid_rev be the matrix of the same dimensions with grid_rev[i][j] = grid[i][n-1-j] for all 0 <= i < m and 0 <= j < n. The function returns r on grid, returns r' on grid_rev, and r = r'.
  Preconditions: Writing m = len(grid) and n = len(grid[0]), the input satisfies m >= 3, n >= 3, m <= 150, n <= 150, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 1_000_000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_9 (grid : Grid) (m n : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000) :
    ∃ r r', max_sum grid = ok r ∧ max_sum (mirrorLR grid) = ok r' ∧ r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000), ∃ r r', max_sum grid = ok r ∧ max_sum (mirrorLR grid) = ok r' ∧ r = r') := by
  sorry

/-- Let grid_rev be the matrix of the same dimensions with grid_rev[i][j] = grid[m-1-i][j] for all 0 <= i < m and 0 <= j < n. The function returns r on grid, returns r' on grid_rev, and r = r'.
  Preconditions: Writing m = len(grid) and n = len(grid[0]), the input satisfies m >= 3, n >= 3, m <= 150, n <= 150, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 1_000_000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_10 (grid : Grid) (m n : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000) :
    ∃ r r', max_sum grid = ok r ∧ max_sum (mirrorUD grid) = ok r' ∧ r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000), ∃ r r', max_sum grid = ok r ∧ max_sum (mirrorUD grid) = ok r' ∧ r = r') := by
  sorry

/-- The call max_sum(A) returns r_A, the call max_sum(B) returns r_B, and r_A <= r_B.
  Preconditions: Let A and B be rectangular matrices of the same dimensions m x n, with m >= 3, n >= 3, m <= 150, n <= 150, all rows of length n, and 0 <= A[i][j] <= B[i][j] <= 1_000_000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_11 (A B : Grid) (m n : ℕ)
    (hmA : m = A.val.length)
    (hmB : m = B.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlenA : ∀ i, i < m → (row A i).length = n)
    (hlenB : ∀ i, i < m → (row B i).length = n)
    (hAB : ∀ i j, i < m → j < n →
      0 ≤ cell A i j ∧ cell A i j ≤ cell B i j ∧ cell B i j ≤ 1000000) :
    ∃ rA rB, max_sum A = ok rA ∧ max_sum B = ok rB ∧ rA.val ≤ rB.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (A B : Grid) (m n : ℕ)
    (hmA : m = A.val.length)
    (hmB : m = B.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlenA : ∀ i, i < m → (row A i).length = n)
    (hlenB : ∀ i, i < m → (row B i).length = n)
    (hAB : ∀ i j, i < m → j < n →
      0 ≤ cell A i j ∧ cell A i j ≤ cell B i j ∧ cell B i j ≤ 1000000), ∃ rA rB, max_sum A = ok rA ∧ max_sum B = ok rB ∧ rA.val ≤ rB.val) := by
  sorry

/-- If max_sum(grid) returns r and max_sum(grid') returns r', then r' = r + 7*c.
  Preconditions: Writing m = len(grid) and n = len(grid[0]), the input satisfies m >= 3, n >= 3, m <= 150, n <= 150, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 1_000_000 for every 0 <= i < m and 0 <= j < n. Let c be an integer such that 0 <= grid[i][j] + c <= 1_000_000 for every 0 <= i < m and 0 <= j < n, and define grid'[i][j] = grid[i][j] + c. -/
theorem spec_12 (grid grid' : Grid) (m n : ℕ) (c : ℤ)
    (hm : m = grid.val.length)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hm' : m = grid'.val.length)
    (hlen' : ∀ i, i < m → (row grid' i).length = n)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000)
    (hc : ∀ i j, i < m → j < n → 0 ≤ cell grid i j + c ∧ cell grid i j + c ≤ 1000000)
    (hshift : ∀ i j, i < m → j < n → cell grid' i j = cell grid i j + c) :
    ∀ r r', max_sum grid = ok r → max_sum grid' = ok r' → r'.val = r.val + 7 * c := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid grid' : Grid) (m n : ℕ) (c : ℤ)
    (hm : m = grid.val.length)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hm' : m = grid'.val.length)
    (hlen' : ∀ i, i < m → (row grid' i).length = n)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000)
    (hc : ∀ i j, i < m → j < n → 0 ≤ cell grid i j + c ∧ cell grid i j + c ≤ 1000000)
    (hshift : ∀ i j, i < m → j < n → cell grid' i j = cell grid i j + c), ∀ r r', max_sum grid = ok r → max_sum grid' = ok r' → r'.val = r.val + 7 * c) := by
  sorry

/-- The function returns a result r and r <= sum_{i=0}^{m-1} sum_{j=0}^{n-1} grid[i][j].
  Preconditions: Writing m = len(grid) and n = len(grid[0]), the input satisfies m >= 3, n >= 3, m <= 150, n <= 150, len(grid[i]) = n for every 0 <= i < m, and 0 <= grid[i][j] <= 1_000_000 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_13 (grid : Grid) (m n : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000) :
    ∃ r, max_sum grid = ok r ∧ r.val ≤ totalSum grid m n := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hn3 : 3 ≤ n) (hm150 : m ≤ 150) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = n)
    (hval : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000), ∃ r, max_sum grid = ok r ∧ r.val ≤ totalSum grid m n) := by
  sorry

/-- The function returns a result r and r = max { grid[0][j] + grid[0][j+1] + grid[0][j+2] + grid[1][j+1] + grid[2][j] + grid[2][j+1] + grid[2][j+2] | 0 <= j <= n-3 }.
  Preconditions: Writing m = len(grid) and n = len(grid[0]), the input satisfies m = 3, n >= 3, n <= 150, len(grid[i]) = n for every 0 <= i < 3, and 0 <= grid[i][j] <= 1_000_000 for every 0 <= i < 3 and 0 <= j < n. -/
theorem spec_14 (grid : Grid) (n : ℕ)
    (hm : grid.val.length = 3)
    (hn3 : 3 ≤ n) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < 3 → (row grid i).length = n)
    (hval : ∀ i j, i < 3 → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000) :
    ∃ r, max_sum grid = ok r ∧ IsMaxPyramidRow grid 0 n r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (grid : Grid) (n : ℕ)
    (hm : grid.val.length = 3)
    (hn3 : 3 ≤ n) (hn150 : n ≤ 150)
    (hlen : ∀ i, i < 3 → (row grid i).length = n)
    (hval : ∀ i j, i < 3 → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000), ∃ r, max_sum grid = ok r ∧ IsMaxPyramidRow grid 0 n r.val) := by
  sorry

/-- The function returns a result r and r = max { grid[i][0] + grid[i][1] + grid[i][2] + grid[i+1][1] + grid[i+2][0] + grid[i+2][1] + grid[i+2][2] | 0 <= i <= m-3 }.
  Preconditions: Writing m = len(grid) and n = len(grid[0]), the input satisfies m >= 3, m <= 150, n = 3, len(grid[i]) = 3 for every 0 <= i < m, and 0 <= grid[i][j] <= 1_000_000 for every 0 <= i < m and 0 <= j < 3. -/
theorem spec_15 (grid : Grid) (m : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hm150 : m ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = 3)
    (hval : ∀ i j, i < m → j < 3 → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000) :
    ∃ r, max_sum grid = ok r ∧ IsMaxPyramidCol grid m 0 r.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (grid : Grid) (m : ℕ)
    (hm : m = grid.val.length)
    (hm3 : 3 ≤ m) (hm150 : m ≤ 150)
    (hlen : ∀ i, i < m → (row grid i).length = 3)
    (hval : ∀ i j, i < m → j < 3 → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000000), ∃ r, max_sum grid = ok r ∧ IsMaxPyramidCol grid m 0 r.val) := by
  sorry

end AegisSpec.MaxSum
