import Aegis.DifferenceOfDistinctValues.Code.Funs

/-!
# Specifications of `Aegis.DifferenceOfDistinctValues.difference_of_distinct_values`

LeetCode problem `difference-of-number-of-distinct-values-on-diagonals`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DifferenceOfDistinctValues

abbrev Grid : Type := Aeneas.Std.Slice (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)

abbrev Ans : Type := Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)

def toMat (v : List (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)) : List (List ℤ) :=
  v.map fun row => row.val.map fun x => x.val

def gridMat (grid : Grid) : List (List ℤ) := toMat grid.val

def outMat (r : Ans) : List (List ℤ) := toMat r.val

def cell (M : List (List ℤ)) (i j : ℕ) : ℤ := (M.getD i []).getD j 0

def rowLen (M : List (List ℤ)) (i : ℕ) : ℕ := (M.getD i []).length

def distinctCount (l : List ℤ) : ℕ := l.dedup.length

def leftDiag (M : List (List ℤ)) (i j : ℕ) : List ℤ :=
  (List.range i).flatMap fun x =>
    (List.range j).filterMap fun y => if x + j = y + i then some (cell M x y) else none

def rightDiag (M : List (List ℤ)) (i j : ℕ) : List ℤ :=
  (List.range M.length).flatMap fun x =>
    (List.range (rowLen M 0)).filterMap fun y =>
      if i < x ∧ j < y ∧ x + j = y + i then some (cell M x y) else none

def leftCount (M : List (List ℤ)) (i j : ℕ) : ℕ := distinctCount (leftDiag M i j)

def rightCount (M : List (List ℤ)) (i j : ℕ) : ℕ := distinctCount (rightDiag M i j)

def indicatorLeft (M : List (List ℤ)) (i j : ℕ) : ℕ := if leftDiag M i j = [] then 0 else 1

def indicatorRight (M : List (List ℤ)) (i j : ℕ) : ℕ := if rightDiag M i j = [] then 0 else 1

def HasDims (M : List (List ℤ)) (m n : ℕ) : Prop :=
  M.length = m ∧ ∀ i, i < m → rowLen M i = n

def GridSpec (M : List (List ℤ)) (m n : ℕ) : Prop :=
  1 ≤ m ∧ m ≤ 50 ∧ 1 ≤ n ∧ n ≤ 50 ∧ HasDims M m n ∧
    ∀ i j, i < m → j < n → 1 ≤ cell M i j ∧ cell M i j ≤ 50

def rot180 (M : List (List ℤ)) : List (List ℤ) := M.reverse.map fun row => row.reverse

/-- Whenever difference_of_distinct_values grid returns a result r, the following holds: len(r) = m, every row r[i] has length n for 0 <= i < m, and for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] = |L(i,j) - R(i,j)|, where L(i,j) is the number of distinct integer values among the set { grid[x][y] | 0 <= x < i, 0 <= y < j, x - y = i - j }, and R(i,j) is the number of distinct integer values among the set { grid[x][y] | i < x < m, j < y < n, x - y = i - j }. Here |z| denotes the absolute value of the integer z.
  Preconditions: Let m = len(grid). Assume 1 <= m <= 50. Let n = len(grid[0]); assume 1 <= n <= 50. Assume every row grid[i] has length n for 0 <= i < m. Assume for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 50. -/
theorem spec_1 (grid : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n) :
    ∀ r : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        HasDims (outMat r) m n ∧
          ∀ i j, i < m → j < n →
            cell (outMat r) i j =
              |((leftCount (gridMat grid) i j : ℕ) : ℤ) -
                ((rightCount (gridMat grid) i j : ℕ) : ℤ)| := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n), ∀ r : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        HasDims (outMat r) m n ∧
          ∀ i j, i < m → j < n →
            cell (outMat r) i j =
              |((leftCount (gridMat grid) i j : ℕ) : ℤ) -
                ((rightCount (gridMat grid) i j : ℕ) : ℤ)|) := by
  sorry

/-- For every grid satisfying the preconditions, difference_of_distinct_values grid returns a result r (it does not fail).
  Preconditions: Let m = len(grid). Assume 1 <= m <= 50. Let n = len(grid[0]); assume 1 <= n <= 50. Assume every row grid[i] has length n for 0 <= i < m. Assume for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 50. -/
theorem spec_2 (grid : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n) :
    ∃ r : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
        = Aeneas.Std.Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n), ∃ r : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
        = Aeneas.Std.Result.ok r) := by
  sorry

/-- Whenever difference_of_distinct_values grid returns a result r of the same dimensions as grid (len(r) = m and len(r[i]) = n for all 0 <= i < m), then for every i,j with 0 <= i < m and 0 <= j < n, 0 <= r[i][j].
  Preconditions: Let m = len(grid). Assume 1 <= m <= 50. Let n = len(grid[0]); assume 1 <= n <= 50. Assume every row grid[i] has length n for 0 <= i < m. Assume for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 50. -/
theorem spec_3 (grid : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n) :
    ∀ r : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        HasDims (outMat r) m n →
          ∀ i j, i < m → j < n → 0 ≤ cell (outMat r) i j := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n), ∀ r : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        HasDims (outMat r) m n →
          ∀ i j, i < m → j < n → 0 ≤ cell (outMat r) i j) := by
  sorry

/-- Whenever difference_of_distinct_values grid returns a result r of the same dimensions as grid, for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] <= max(min(i,j), min(m - 1 - i, n - 1 - j)).
  Preconditions: Let m = len(grid). Assume 1 <= m <= 50. Let n = len(grid[0]); assume 1 <= n <= 50. Assume every row grid[i] has length n for 0 <= i < m. Assume for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 50. -/
theorem spec_4 (grid : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n) :
    ∀ r : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        HasDims (outMat r) m n →
          ∀ i j, i < m → j < n →
            cell (outMat r) i j
              ≤ ((max (min i j) (min (m - 1 - i) (n - 1 - j)) : ℕ) : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n), ∀ r : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        HasDims (outMat r) m n →
          ∀ i j, i < m → j < n →
            cell (outMat r) i j
              ≤ ((max (min i j) (min (m - 1 - i) (n - 1 - j)) : ℕ) : ℤ)) := by
  sorry

/-- Whenever difference_of_distinct_values grid returns a result r of the same dimensions as grid, if m = 1 or n = 1, then for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] = 0.
  Preconditions: Let m = len(grid). Assume 1 <= m <= 50. Let n = len(grid[0]); assume 1 <= n <= 50. Assume every row grid[i] has length n for 0 <= i < m. Assume for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 50. -/
theorem spec_5 (grid : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n) :
    ∀ r : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        HasDims (outMat r) m n →
          (m = 1 ∨ n = 1) →
            ∀ i j, i < m → j < n → cell (outMat r) i j = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n), ∀ r : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        HasDims (outMat r) m n →
          (m = 1 ∨ n = 1) →
            ∀ i j, i < m → j < n → cell (outMat r) i j = 0) := by
  sorry

/-- Whenever difference_of_distinct_values grid returns a result r of the same dimensions as grid, if m = 2 and n = 2, then r[0][0] = 1, r[0][1] = 0, r[1][0] = 0, and r[1][1] = 1.
  Preconditions: Let m = len(grid). Assume 1 <= m <= 50. Let n = len(grid[0]); assume 1 <= n <= 50. Assume every row grid[i] has length n for 0 <= i < m. Assume for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 50. -/
theorem spec_6 (grid : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n) :
    ∀ r : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        HasDims (outMat r) m n →
          m = 2 → n = 2 →
            cell (outMat r) 0 0 = 1 ∧ cell (outMat r) 0 1 = 0 ∧
              cell (outMat r) 1 0 = 0 ∧ cell (outMat r) 1 1 = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n), ∀ r : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        HasDims (outMat r) m n →
          m = 2 → n = 2 →
            cell (outMat r) 0 0 = 1 ∧ cell (outMat r) 0 1 = 0 ∧
              cell (outMat r) 1 0 = 0 ∧ cell (outMat r) 1 1 = 1) := by
  sorry

/-- Whenever difference_of_distinct_values grid returns a result r and difference_of_distinct_values rot returns a result r', and both r and r' have the same dimensions as their inputs (len(r) = m, len(r[i]) = n, len(r') = m, len(r'[x]) = n), then for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] = r'[m - 1 - i][n - 1 - j].
  Preconditions: Let m = len(grid). Assume 1 <= m <= 50. Let n = len(grid[0]); assume 1 <= n <= 50. Assume every row grid[i] has length n for 0 <= i < m. Assume for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 50. Let rot be the m x n grid defined by rot[x][y] = grid[m - 1 - x][n - 1 - y] for 0 <= x < m and 0 <= y < n. -/
theorem spec_7 (grid rot : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n)
    (hrot : GridSpec (gridMat rot) m n) (hrot180 : gridMat rot = rot180 (gridMat grid)) :
    ∀ r r' : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        Aegis.DifferenceOfDistinctValues.difference_of_distinct_values rot
            = Aeneas.Std.Result.ok r' →
          HasDims (outMat r) m n →
            HasDims (outMat r') m n →
              ∀ i j, i < m → j < n →
                cell (outMat r) i j = cell (outMat r') (m - 1 - i) (n - 1 - j) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid rot : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n)
    (hrot : GridSpec (gridMat rot) m n) (hrot180 : gridMat rot = rot180 (gridMat grid)), ∀ r r' : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        Aegis.DifferenceOfDistinctValues.difference_of_distinct_values rot
            = Aeneas.Std.Result.ok r' →
          HasDims (outMat r) m n →
            HasDims (outMat r') m n →
              ∀ i j, i < m → j < n →
                cell (outMat r) i j = cell (outMat r') (m - 1 - i) (n - 1 - j)) := by
  sorry

/-- Whenever difference_of_distinct_values g returns r and difference_of_distinct_values g' returns r', and both r and r' have the same dimensions as their inputs, then for every i,j with 0 <= i < m and 0 <= j < n, if for every x,y with 0 <= x < m and 0 <= y < n and x - y = i - j we have g[x][y] = g'[x][y], then r[i][j] = r'[i][j].
  Preconditions: Let g and g' be two grids satisfying the problem constraints with the same dimensions: let m = len(g) = len(g'), n = len(g[0]) = len(g'[0]), with 1 <= m <= 50 and 1 <= n <= 50; every row of g and of g' has length n, and all entries of both grids are between 1 and 50 inclusive. -/
theorem spec_8 (g g' : Grid) (m n : ℕ) (hg : GridSpec (gridMat g) m n)
    (hg' : GridSpec (gridMat g') m n) :
    ∀ r r' : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values g
          = Aeneas.Std.Result.ok r →
        Aegis.DifferenceOfDistinctValues.difference_of_distinct_values g'
            = Aeneas.Std.Result.ok r' →
          HasDims (outMat r) m n →
            HasDims (outMat r') m n →
              ∀ i j, i < m → j < n →
                (∀ x y, x < m → y < n → x + j = y + i →
                    cell (gridMat g) x y = cell (gridMat g') x y) →
                  cell (outMat r) i j = cell (outMat r') i j := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (g g' : Grid) (m n : ℕ) (hg : GridSpec (gridMat g) m n)
    (hg' : GridSpec (gridMat g') m n), ∀ r r' : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values g
          = Aeneas.Std.Result.ok r →
        Aegis.DifferenceOfDistinctValues.difference_of_distinct_values g'
            = Aeneas.Std.Result.ok r' →
          HasDims (outMat r) m n →
            HasDims (outMat r') m n →
              ∀ i j, i < m → j < n →
                (∀ x y, x < m → y < n → x + j = y + i →
                    cell (gridMat g) x y = cell (gridMat g') x y) →
                  cell (outMat r) i j = cell (outMat r') i j) := by
  sorry

/-- Whenever difference_of_distinct_values g returns r and difference_of_distinct_values g' returns r', and both r and r' have the same dimensions as their inputs, then r[p][q] = r'[p][q].
  Preconditions: Let g be a grid satisfying the problem constraints with m = len(g), n = len(g[0]), 1 <= m <= 50, 1 <= n <= 50, every row length n, and all entries between 1 and 50 inclusive. Let p,q satisfy 0 <= p < m and 0 <= q < n. Let g' be another grid satisfying the same constraints with the same m,n and with g'[i][j] = g[i][j] for every (i,j) except possibly (i,j) = (p,q). -/
theorem spec_9 (g g' : Grid) (m n : ℕ) (hg : GridSpec (gridMat g) m n)
    (hg' : GridSpec (gridMat g') m n) (p q : ℕ) (hp : p < m) (hq : q < n)
    (hagree : ∀ i j, i < m → j < n → (i ≠ p ∨ j ≠ q) →
      cell (gridMat g') i j = cell (gridMat g) i j) :
    ∀ r r' : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values g
          = Aeneas.Std.Result.ok r →
        Aegis.DifferenceOfDistinctValues.difference_of_distinct_values g'
            = Aeneas.Std.Result.ok r' →
          HasDims (outMat r) m n →
            HasDims (outMat r') m n →
              cell (outMat r) p q = cell (outMat r') p q := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (g g' : Grid) (m n : ℕ) (hg : GridSpec (gridMat g) m n)
    (hg' : GridSpec (gridMat g') m n) (p q : ℕ) (hp : p < m) (hq : q < n)
    (hagree : ∀ i j, i < m → j < n → (i ≠ p ∨ j ≠ q) →
      cell (gridMat g') i j = cell (gridMat g) i j), ∀ r r' : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values g
          = Aeneas.Std.Result.ok r →
        Aegis.DifferenceOfDistinctValues.difference_of_distinct_values g'
            = Aeneas.Std.Result.ok r' →
          HasDims (outMat r) m n →
            HasDims (outMat r') m n →
              cell (outMat r) p q = cell (outMat r') p q) := by
  sorry

/-- Whenever difference_of_distinct_values g returns r and difference_of_distinct_values g' returns r', and both r and r' have the same dimensions as their inputs, then for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] = r'[i][j].
  Preconditions: Let g be a grid satisfying the problem constraints with m = len(g), n = len(g[0]), 1 <= m <= 50, 1 <= n <= 50, every row length n, and all entries between 1 and 50 inclusive. Let t be an integer such that 1 <= g[i][j] + t <= 50 for every i,j. Let g' be the grid defined by g'[i][j] = g[i][j] + t for every i,j. -/
theorem spec_10 (g g' : Grid) (m n : ℕ) (t : ℤ) (hg : GridSpec (gridMat g) m n)
    (hg' : GridSpec (gridMat g') m n)
    (ht : ∀ i j, i < m → j < n →
      1 ≤ cell (gridMat g) i j + t ∧ cell (gridMat g) i j + t ≤ 50)
    (hshift : ∀ i j, i < m → j < n → cell (gridMat g') i j = cell (gridMat g) i j + t) :
    ∀ r r' : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values g
          = Aeneas.Std.Result.ok r →
        Aegis.DifferenceOfDistinctValues.difference_of_distinct_values g'
            = Aeneas.Std.Result.ok r' →
          HasDims (outMat r) m n →
            HasDims (outMat r') m n →
              ∀ i j, i < m → j < n → cell (outMat r) i j = cell (outMat r') i j := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (g g' : Grid) (m n : ℕ) (t : ℤ) (hg : GridSpec (gridMat g) m n)
    (hg' : GridSpec (gridMat g') m n)
    (ht : ∀ i j, i < m → j < n →
      1 ≤ cell (gridMat g) i j + t ∧ cell (gridMat g) i j + t ≤ 50)
    (hshift : ∀ i j, i < m → j < n → cell (gridMat g') i j = cell (gridMat g) i j + t), ∀ r r' : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values g
          = Aeneas.Std.Result.ok r →
        Aegis.DifferenceOfDistinctValues.difference_of_distinct_values g'
            = Aeneas.Std.Result.ok r' →
          HasDims (outMat r) m n →
            HasDims (outMat r') m n →
              ∀ i j, i < m → j < n → cell (outMat r) i j = cell (outMat r') i j) := by
  sorry

/-- Whenever difference_of_distinct_values grid returns a result r of the same dimensions as grid, for every i,j with 0 <= i < m and 0 <= j < n, if for all x,y with 0 <= x < m and 0 <= y < n and x - y = i - j we have grid[x][y] = grid[i][j], then r[i][j] = |A(i,j) - B(i,j)|, where A(i,j) = 1 if there exist x,y with 0 <= x < i, 0 <= y < j, and x - y = i - j, and A(i,j) = 0 otherwise; and B(i,j) = 1 if there exist x,y with i < x < m, j < y < n, and x - y = i - j, and B(i,j) = 0 otherwise.
  Preconditions: Let m = len(grid). Assume 1 <= m <= 50. Let n = len(grid[0]); assume 1 <= n <= 50. Assume every row grid[i] has length n for 0 <= i < m. Assume for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 50. -/
theorem spec_11 (grid : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n) :
    ∀ r : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        HasDims (outMat r) m n →
          ∀ i j, i < m → j < n →
            (∀ x y, x < m → y < n → x + j = y + i →
                cell (gridMat grid) x y = cell (gridMat grid) i j) →
              cell (outMat r) i j =
                |((indicatorLeft (gridMat grid) i j : ℕ) : ℤ) -
                  ((indicatorRight (gridMat grid) i j : ℕ) : ℤ)| := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n), ∀ r : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        HasDims (outMat r) m n →
          ∀ i j, i < m → j < n →
            (∀ x y, x < m → y < n → x + j = y + i →
                cell (gridMat grid) x y = cell (gridMat grid) i j) →
              cell (outMat r) i j =
                |((indicatorLeft (gridMat grid) i j : ℕ) : ℤ) -
                  ((indicatorRight (gridMat grid) i j : ℕ) : ℤ)|) := by
  sorry

/-- Whenever difference_of_distinct_values grid returns a result r of the same dimensions as grid, r[0][n - 1] = 0 and r[m - 1][0] = 0.
  Preconditions: Let m = len(grid). Assume 1 <= m <= 50. Let n = len(grid[0]); assume 1 <= n <= 50. Assume every row grid[i] has length n for 0 <= i < m. Assume for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 50. -/
theorem spec_12 (grid : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n) :
    ∀ r : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        HasDims (outMat r) m n →
          cell (outMat r) 0 (n - 1) = 0 ∧ cell (outMat r) (m - 1) 0 = 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n), ∀ r : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        HasDims (outMat r) m n →
          cell (outMat r) 0 (n - 1) = 0 ∧ cell (outMat r) (m - 1) 0 = 0) := by
  sorry

/-- Whenever difference_of_distinct_values grid returns r and difference_of_distinct_values gridT returns rT, and both have the same dimensions as their inputs (len(r) = m, len(r[i]) = n, len(rT) = n, len(rT[x]) = m), then for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] = rT[j][i].
  Preconditions: Let m = len(grid). Assume 1 <= m <= 50. Let n = len(grid[0]); assume 1 <= n <= 50. Assume every row grid[i] has length n for 0 <= i < m. Assume for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 50. Let gridT be the n x m grid defined by gridT[x][y] = grid[y][x] for 0 <= x < n and 0 <= y < m. -/
theorem spec_13 (grid gridT : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n)
    (hgridT : GridSpec (gridMat gridT) n m)
    (htranspose : ∀ x y, x < n → y < m →
      cell (gridMat gridT) x y = cell (gridMat grid) y x) :
    ∀ r rT : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        Aegis.DifferenceOfDistinctValues.difference_of_distinct_values gridT
            = Aeneas.Std.Result.ok rT →
          HasDims (outMat r) m n →
            HasDims (outMat rT) n m →
              ∀ i j, i < m → j < n → cell (outMat r) i j = cell (outMat rT) j i := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid gridT : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n)
    (hgridT : GridSpec (gridMat gridT) n m)
    (htranspose : ∀ x y, x < n → y < m →
      cell (gridMat gridT) x y = cell (gridMat grid) y x), ∀ r rT : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        Aegis.DifferenceOfDistinctValues.difference_of_distinct_values gridT
            = Aeneas.Std.Result.ok rT →
          HasDims (outMat r) m n →
            HasDims (outMat rT) n m →
              ∀ i j, i < m → j < n → cell (outMat r) i j = cell (outMat rT) j i) := by
  sorry

/-- Whenever difference_of_distinct_values grid returns a result r of the same dimensions as grid, for every i,j with 0 <= i < m and 0 <= j < n, if the values on the diagonal x - y = i - j are pairwise distinct (that is, for all (x,y) and (u,v) with 0 <= x,u < m, 0 <= y,v < n, x - y = i - j, u - v = i - j, and (x,y) != (u,v), we have grid[x][y] != grid[u][v]), then r[i][j] = |min(i,j) - min(m - 1 - i, n - 1 - j)|.
  Preconditions: Let m = len(grid). Assume 1 <= m <= 50. Let n = len(grid[0]); assume 1 <= n <= 50. Assume every row grid[i] has length n for 0 <= i < m. Assume for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 50. -/
theorem spec_14 (grid : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n) :
    ∀ r : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        HasDims (outMat r) m n →
          ∀ i j, i < m → j < n →
            (∀ x y u v, x < m → y < n → u < m → v < n → x + j = y + i → u + j = v + i →
                (x ≠ u ∨ y ≠ v) → cell (gridMat grid) x y ≠ cell (gridMat grid) u v) →
              cell (outMat r) i j =
                |((min i j : ℕ) : ℤ) - ((min (m - 1 - i) (n - 1 - j) : ℕ) : ℤ)| := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (grid : Grid) (m n : ℕ) (hgrid : GridSpec (gridMat grid) m n), ∀ r : Ans,
      Aegis.DifferenceOfDistinctValues.difference_of_distinct_values grid
          = Aeneas.Std.Result.ok r →
        HasDims (outMat r) m n →
          ∀ i j, i < m → j < n →
            (∀ x y u v, x < m → y < n → u < m → v < n → x + j = y + i → u + j = v + i →
                (x ≠ u ∨ y ≠ v) → cell (gridMat grid) x y ≠ cell (gridMat grid) u v) →
              cell (outMat r) i j =
                |((min i j : ℕ) : ℤ) - ((min (m - 1 - i) (n - 1 - j) : ℕ) : ℤ)|) := by
  sorry

end AegisSpec.DifferenceOfDistinctValues
