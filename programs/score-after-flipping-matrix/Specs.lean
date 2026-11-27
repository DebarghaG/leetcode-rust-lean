import Aegis.MatrixScore.Code.Funs

/-!
# Specifications of `Aegis.MatrixScore.matrix_score`

LeetCode problem `score-after-flipping-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MatrixScore (matrix_score)

namespace AegisSpec.MatrixScore

def rows (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  grid.val.map fun row => row.val.map fun x => x.val

def numRows (grid : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  (rows grid).length

def numCols (grid : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  ((rows grid)[0]?).getD [] |>.length

def entry (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  (((rows grid)[i]?).getD [])[j]?.getD 0

def score (A : Nat → Nat → Int) (m n : Nat) : Int :=
  ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, A i j * (2 : Int) ^ (n - 1 - j)

def toggledEntry (grid : Slice (alloc.vec.Vec Std.I64)) (a b : Nat → Fin 2) (i j : Nat) : Int :=
  (entry grid i j + ((a i : Nat) : Int) + ((b j : Nat) : Int)) % 2

def toggledScore (grid : Slice (alloc.vec.Vec Std.I64)) (a b : Nat → Fin 2) : Int :=
  score (toggledEntry grid a b) (numRows grid) (numCols grid)

def sameAsFirst (grid : Slice (alloc.vec.Vec Std.I64)) (j : Nat) : Nat :=
  ((Finset.range (numRows grid)).filter (fun i => entry grid i j = entry grid i 0)).card

def flipRow (G : List (List Int)) (i0 : Nat) : List (List Int) :=
  G.mapIdx fun i row => if i = i0 then row.map (fun x => 1 - x) else row

/-- The function returns a result r (it does not fail). For bits a_0,...,a_{m-1} in {0,1} and b_0,...,b_{n-1} in {0,1}, let A[i][j] = (grid[i][j] + a_i + b_j) mod 2 for 0 <= i < m and 0 <= j < n, and let score(A) = sum_{i=0}^{m-1} sum_{j=0}^{n-1} A[i][j] * 2^(n-1-j). Then (i) score(A) <= r for every choice of the bits a_i, b_j, and (ii) score(A) = r for some choice of the bits a_i, b_j. Equivalently, r is the maximum score over all matrices obtainable from grid by any number of row/column toggles, where the score of a matrix is the sum of its rows read as binary numbers with the leftmost entry most significant (weight 2^(n-1-j) for column j).
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is non-empty (m >= 1), 1 <= n <= 20 and 1 <= m <= 20, every row of grid has length n (for every i with 0 <= i < m, len(grid[i]) = n), and every entry is binary (for every i, j with 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1). -/
theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1) :
    ∃ r : Std.I64,
      matrix_score grid = ok r ∧
      (∀ a b : Nat → Fin 2,
        score (fun i j => (entry grid i j + ((a i : Nat) : Int) + ((b j : Nat) : Int)) % 2)
          (numRows grid) (numCols grid) ≤ r.val) ∧
      (∃ a b : Nat → Fin 2,
        score (fun i j => (entry grid i j + ((a i : Nat) : Int) + ((b j : Nat) : Int)) % 2)
          (numRows grid) (numCols grid) = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1), ∃ r : Std.I64,
      matrix_score grid = ok r ∧
      (∀ a b : Nat → Fin 2,
        score (fun i j => (entry grid i j + ((a i : Nat) : Int) + ((b j : Nat) : Int)) % 2)
          (numRows grid) (numCols grid) ≤ r.val) ∧
      (∃ a b : Nat → Fin 2,
        score (fun i j => (entry grid i j + ((a i : Nat) : Int) + ((b j : Nat) : Int)) % 2)
          (numRows grid) (numCols grid) = r.val)) := by
  sorry

/-- Whenever the function returns a result r, we have r <= m * (2^n - 1), where m = len(grid) and n = len(grid[0]).
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is non-empty (m >= 1), 1 <= n <= 20 and 1 <= m <= 20, every row of grid has length n, and every entry is binary. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (r : Std.I64) (hr : matrix_score grid = ok r) :
    r.val ≤ (numRows grid : Int) * ((2 : Int) ^ numCols grid - 1) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (r : Std.I64) (hr : matrix_score grid = ok r), r.val ≤ (numRows grid : Int) * ((2 : Int) ^ numCols grid - 1)) := by
  sorry

/-- Whenever the function returns a result r, we have r >= m * 2^(n-1), where m = len(grid) and n = len(grid[0]).
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is non-empty (m >= 1), 1 <= n <= 20 and 1 <= m <= 20, every row of grid has length n, and every entry is binary. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (r : Std.I64) (hr : matrix_score grid = ok r) :
    (numRows grid : Int) * (2 : Int) ^ (numCols grid - 1) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (r : Std.I64) (hr : matrix_score grid = ok r), (numRows grid : Int) * (2 : Int) ^ (numCols grid - 1) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, we have r >= sum_{i=0}^{m-1} sum_{j=0}^{n-1} grid[i][j] * 2^(n-1-j), i.e., the answer is at least the score of the input matrix itself.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is non-empty (m >= 1), 1 <= n <= 20 and 1 <= m <= 20, every row of grid has length n, and every entry is binary. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (r : Std.I64) (hr : matrix_score grid = ok r) :
    (∑ i ∈ Finset.range (numRows grid), ∑ j ∈ Finset.range (numCols grid),
        entry grid i j * (2 : Int) ^ (numCols grid - 1 - j)) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (r : Std.I64) (hr : matrix_score grid = ok r), (∑ i ∈ Finset.range (numRows grid), ∑ j ∈ Finset.range (numCols grid),
        entry grid i j * (2 : Int) ^ (numCols grid - 1 - j)) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exist bits a_0,...,a_{m-1} in {0,1} and b_0,...,b_{n-1} in {0,1} such that the matrix A defined by A[i][j] = (grid[i][j] + a_i + b_j) mod 2 for 0 <= i < m and 0 <= j < n satisfies sum_{i=0}^{m-1} sum_{j=0}^{n-1} A[i][j] * 2^(n-1-j) = r. Thus the maximum is attained by some sequence of moves.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is non-empty (m >= 1), 1 <= n <= 20 and 1 <= m <= 20, every row of grid has length n, and every entry is binary. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (r : Std.I64) (hr : matrix_score grid = ok r) :
    ∃ a b : Nat → Fin 2, toggledScore grid a b = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (r : Std.I64) (hr : matrix_score grid = ok r), ∃ a b : Nat → Fin 2, toggledScore grid a b = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every choice of bits a_0,...,a_{m-1} in {0,1} and b_0,...,b_{n-1} in {0,1}, the matrix A defined by A[i][j] = (grid[i][j] + a_i + b_j) mod 2 for 0 <= i < m and 0 <= j < n satisfies sum_{i=0}^{m-1} sum_{j=0}^{n-1} A[i][j] * 2^(n-1-j) <= r. Thus no sequence of moves yields a strictly larger score.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is non-empty (m >= 1), 1 <= n <= 20 and 1 <= m <= 20, every row of grid has length n, and every entry is binary. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (r : Std.I64) (hr : matrix_score grid = ok r) :
    ∀ a b : Nat → Fin 2, toggledScore grid a b ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (r : Std.I64) (hr : matrix_score grid = ok r), ∀ a b : Nat → Fin 2, toggledScore grid a b ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r and m = len(grid) = 1, we have r = 2^n - 1, where n = len(grid[0]).
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is non-empty (m >= 1), 1 <= n <= 20 and 1 <= m <= 20, every row of grid has length n, and every entry is binary. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (hm1 : numRows grid = 1)
    (r : Std.I64) (hr : matrix_score grid = ok r) :
    r.val = (2 : Int) ^ numCols grid - 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (hm1 : numRows grid = 1)
    (r : Std.I64) (hr : matrix_score grid = ok r), r.val = (2 : Int) ^ numCols grid - 1) := by
  sorry

/-- Whenever the function returns a result r and n = len(grid[0]) = 1, we have r = m, where m = len(grid).
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is non-empty (m >= 1), 1 <= n <= 20 and 1 <= m <= 20, every row of grid has length n, and every entry is binary. -/
theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (hn1' : numCols grid = 1)
    (r : Std.I64) (hr : matrix_score grid = ok r) :
    r.val = (numRows grid : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (hn1' : numCols grid = 1)
    (r : Std.I64) (hr : matrix_score grid = ok r), r.val = (numRows grid : Int)) := by
  sorry

/-- Whenever the function returns a result r and grid[i][j] = 0 for every 0 <= i < m and 0 <= j < n, we have r = m * (2^n - 1).
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is non-empty (m >= 1), 1 <= n <= 20 and 1 <= m <= 20, every row of grid has length n, and every entry is binary. -/
theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (hzero : ∀ i j, i < numRows grid → j < numCols grid → entry grid i j = 0)
    (r : Std.I64) (hr : matrix_score grid = ok r) :
    r.val = (numRows grid : Int) * ((2 : Int) ^ numCols grid - 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (hzero : ∀ i j, i < numRows grid → j < numCols grid → entry grid i j = 0)
    (r : Std.I64) (hr : matrix_score grid = ok r), r.val = (numRows grid : Int) * ((2 : Int) ^ numCols grid - 1)) := by
  sorry

/-- Whenever matrix_score(grid) returns a result r and matrix_score(grid') returns a result r', we have r = r'.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is non-empty (m >= 1), 1 <= n <= 20 and 1 <= m <= 20, every row of grid has length n, and every entry is binary. Fix an index i0 with 0 <= i0 < m and define grid' by grid'[i][j] = 1 - grid[i][j] if i = i0, and grid'[i][j] = grid[i][j] otherwise (so grid' is again an m x n binary matrix satisfying the preconditions). -/
theorem spec_10 (grid grid' : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (i0 : Nat) (hi0 : i0 < numRows grid)
    (hflip : rows grid' = flipRow (rows grid) i0)
    (r r' : Std.I64) (hr : matrix_score grid = ok r) (hr' : matrix_score grid' = ok r') :
    r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (i0 : Nat) (hi0 : i0 < numRows grid)
    (hflip : rows grid' = flipRow (rows grid) i0)
    (r r' : Std.I64) (hr : matrix_score grid = ok r) (hr' : matrix_score grid' = ok r'), r = r') := by
  sorry

/-- Whenever the function returns a result r, there exist bits a_0,...,a_{m-1} in {0,1} and b_0,...,b_{n-1} in {0,1} such that the matrix A defined by A[i][j] = (grid[i][j] + a_i + b_j) mod 2 for 0 <= i < m and 0 <= j < n satisfies sum_{i=0}^{m-1} sum_{j=0}^{n-1} A[i][j] * 2^(n-1-j) = r and additionally A[i][0] = 1 for every 0 <= i < m.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is non-empty (m >= 1), 1 <= n <= 20 and 1 <= m <= 20, every row of grid has length n, and every entry is binary. -/
theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (r : Std.I64) (hr : matrix_score grid = ok r) :
    ∃ a b : Nat → Fin 2,
      toggledScore grid a b = r.val ∧
      (∀ i, i < numRows grid → toggledEntry grid a b i 0 = 1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1)
    (r : Std.I64) (hr : matrix_score grid = ok r), ∃ a b : Nat → Fin 2,
      toggledScore grid a b = r.val ∧
      (∀ i, i < numRows grid → toggledEntry grid a b i 0 = 1)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result (it does not fail): no 64-bit signed integer arithmetic overflows, no list index goes out of bounds, and no panic is raised.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is non-empty (m >= 1), 1 <= n <= 20 and 1 <= m <= 20, every row of grid has length n, and every entry is binary. -/
theorem spec_12 (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1) :
    ∃ r : Std.I64, matrix_score grid = ok r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1), ∃ r : Std.I64, matrix_score grid = ok r) := by
  sorry

/-- The function returns a result r (it does not fail). For each column j with 0 <= j < n, let c_j = |{ i : 0 <= i < m and grid[i][j] = grid[i][0] }|. Then r = sum_{j=0}^{n-1} max(c_j, m - c_j) * 2^(n-1-j).
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume grid is non-empty (m >= 1), 1 <= n <= 20 and 1 <= m <= 20, every row of grid has length n, and every entry is binary. -/
theorem spec_13 (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1) :
    ∃ r : Std.I64,
      matrix_score grid = ok r ∧
      r.val = ∑ j ∈ Finset.range (numCols grid),
        max (sameAsFirst grid j : Int)
            ((numRows grid : Int) - (sameAsFirst grid j : Int)) *
          (2 : Int) ^ (numCols grid - 1 - j) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hne : 1 ≤ numRows grid) (hm20 : numRows grid ≤ 20)
    (hn1 : 1 ≤ numCols grid) (hn20 : numCols grid ≤ 20)
    (hlen : ∀ i, i < numRows grid → ((rows grid)[i]!).length = numCols grid)
    (hbin : ∀ i j, i < numRows grid → j < numCols grid →
      entry grid i j = 0 ∨ entry grid i j = 1), ∃ r : Std.I64,
      matrix_score grid = ok r ∧
      r.val = ∑ j ∈ Finset.range (numCols grid),
        max (sameAsFirst grid j : Int)
            ((numRows grid : Int) - (sameAsFirst grid j : Int)) *
          (2 : Int) ^ (numCols grid - 1 - j)) := by
  sorry

end AegisSpec.MatrixScore
