import Aegis.MinimumVisitedCells.Code.Funs

/-!
# Specifications of `Aegis.MinimumVisitedCells.minimum_visited_cells`

LeetCode problem `minimum-number-of-visited-cells-in-a-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumVisitedCells

  def cellVal (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    match grid.val[i]? with
    | none => 0
    | some row =>
      match row.val[j]? with
      | none => 0
      | some x => x.val

  def LegalMove (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) :
      Nat × Nat → Nat × Nat → Prop
    | (i, j), (i', j') =>
      i < m ∧ j < n ∧
        ((i' = i ∧ j < j' ∧ j' < n ∧ (j' : Int) - (j : Int) ≤ cellVal grid i j) ∨
         (j' = j ∧ i < i' ∧ i' < m ∧ (i' : Int) - (i : Int) ≤ cellVal grid i j))

  def ChainRel {α : Type} (R : α → α → Prop) : List α → Prop
    | [] => True
    | [_] => True
    | a :: b :: rest => R a b ∧ ChainRel R (b :: rest)

  def IsPath (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (p : List (Nat × Nat)) : Prop :=
    ChainRel (LegalMove grid m n) p ∧
      (∀ c ∈ p, c.1 < m ∧ c.2 < n) ∧
      p.head? = some (0, 0) ∧
      p.getLast? = some (m - 1, n - 1)

  /-- Define a cell to be a pair (i,j) with 0 <= i < m and 0 <= j < n. Define a legal move as either ((i,j),(i,k)) with j < k < n and k - j <= grid[i][j], or ((i,j),(k,j)) with i < k < m and k - i <= grid[i][j]. Define a path as a finite sequence of cells (i_0,j_0),...,(i_t,j_t) with t >= 0, (i_0,j_0) = (0,0), (i_t,j_t) = (m-1,n-1), such that every consecutive pair is a legal move; its visited-cell count is t+1. The function returns a result r and: if at least one such path exists, then r is the minimum visited-cell count over all such paths; if no such path exists, then r = -1.
    Preconditions: Let m = len(grid). The slice is nonempty, so let n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m*n <= 100000, for every i with 0 <= i < m and every j with 0 <= j < n we have 0 <= grid[i][j] < m*n, and grid[m-1][n-1] = 0. -/
  theorem spec_1
      (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hm1 : 1 ≤ m)
      (hn : ∀ v ∈ grid.val, v.val.length = n)
      (hn1 : 1 ≤ n)
      (hsize : m * n ≤ 100000)
      (hval : ∀ i j, i < m → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < ((m * n : Nat) : Int))
      (hend : cellVal grid (m - 1) (n - 1) = 0) :
      ∃ r, Aegis.MinimumVisitedCells.minimum_visited_cells grid = ok r ∧
        ((∃ p, IsPath grid m n p) →
          ∃ p, IsPath grid m n p ∧ r.val = (p.length : Int) ∧
            ∀ q, IsPath grid m n q → (p.length : Int) ≤ (q.length : Int)) ∧
        ((¬ ∃ p, IsPath grid m n p) → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hm1 : 1 ≤ m)
        (hn : ∀ v ∈ grid.val, v.val.length = n)
        (hn1 : 1 ≤ n)
        (hsize : m * n ≤ 100000)
        (hval : ∀ i j, i < m → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < ((m * n : Nat) : Int))
        (hend : cellVal grid (m - 1) (n - 1) = 0), ∃ r, Aegis.MinimumVisitedCells.minimum_visited_cells grid = ok r ∧
          ((∃ p, IsPath grid m n p) →
            ∃ p, IsPath grid m n p ∧ r.val = (p.length : Int) ∧
              ∀ q, IsPath grid m n q → (p.length : Int) ≤ (q.length : Int)) ∧
          ((¬ ∃ p, IsPath grid m n p) → r.val = -1)) := by
    sorry

  /-- The function returns a result r and does not fail: there is no panic, out-of-bounds access, or arithmetic overflow.
    Preconditions: Let m = len(grid). The slice is nonempty, so let n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m*n <= 100000, for every i with 0 <= i < m and every j with 0 <= j < n we have 0 <= grid[i][j] < m*n, and grid[m-1][n-1] = 0. -/
  theorem spec_2
      (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hm1 : 1 ≤ m)
      (hn : ∀ v ∈ grid.val, v.val.length = n)
      (hn1 : 1 ≤ n)
      (hsize : m * n ≤ 100000)
      (hval : ∀ i j, i < m → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < ((m * n : Nat) : Int))
      (hend : cellVal grid (m - 1) (n - 1) = 0) :
      ∃ r, Aegis.MinimumVisitedCells.minimum_visited_cells grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hm1 : 1 ≤ m)
        (hn : ∀ v ∈ grid.val, v.val.length = n)
        (hn1 : 1 ≤ n)
        (hsize : m * n ≤ 100000)
        (hval : ∀ i j, i < m → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < ((m * n : Nat) : Int))
        (hend : cellVal grid (m - 1) (n - 1) = 0), ∃ r, Aegis.MinimumVisitedCells.minimum_visited_cells grid = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 1 <= r <= m*n.
    Preconditions: Let m = len(grid). The slice is nonempty, so let n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m*n <= 100000, for every i with 0 <= i < m and every j with 0 <= j < n we have 0 <= grid[i][j] < m*n, and grid[m-1][n-1] = 0. -/
  theorem spec_3
      (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hm1 : 1 ≤ m)
      (hn : ∀ v ∈ grid.val, v.val.length = n)
      (hn1 : 1 ≤ n)
      (hsize : m * n ≤ 100000)
      (hval : ∀ i j, i < m → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < ((m * n : Nat) : Int))
      (hend : cellVal grid (m - 1) (n - 1) = 0) :
      ∀ r, Aegis.MinimumVisitedCells.minimum_visited_cells grid = ok r →
        r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ ((m * n : Nat) : Int)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hm1 : 1 ≤ m)
        (hn : ∀ v ∈ grid.val, v.val.length = n)
        (hn1 : 1 ≤ n)
        (hsize : m * n ≤ 100000)
        (hval : ∀ i j, i < m → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < ((m * n : Nat) : Int))
        (hend : cellVal grid (m - 1) (n - 1) = 0), ∀ r, Aegis.MinimumVisitedCells.minimum_visited_cells grid = ok r →
          r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ ((m * n : Nat) : Int))) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, r <= m + n - 1.
    Preconditions: Let m = len(grid). The slice is nonempty, so let n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m*n <= 100000, for every i with 0 <= i < m and every j with 0 <= j < n we have 0 <= grid[i][j] < m*n, and grid[m-1][n-1] = 0. -/
  theorem spec_4
      (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hm1 : 1 ≤ m)
      (hn : ∀ v ∈ grid.val, v.val.length = n)
      (hn1 : 1 ≤ n)
      (hsize : m * n ≤ 100000)
      (hval : ∀ i j, i < m → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < ((m * n : Nat) : Int))
      (hend : cellVal grid (m - 1) (n - 1) = 0) :
      ∀ r, Aegis.MinimumVisitedCells.minimum_visited_cells grid = ok r → r.val ≠ -1 →
        r.val ≤ (m : Int) + (n : Int) - 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hm1 : 1 ≤ m)
        (hn : ∀ v ∈ grid.val, v.val.length = n)
        (hn1 : 1 ≤ n)
        (hsize : m * n ≤ 100000)
        (hval : ∀ i j, i < m → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < ((m * n : Nat) : Int))
        (hend : cellVal grid (m - 1) (n - 1) = 0), ∀ r, Aegis.MinimumVisitedCells.minimum_visited_cells grid = ok r → r.val ≠ -1 →
          r.val ≤ (m : Int) + (n : Int) - 1) := by
    sorry

  /-- Define a legal move as either from (i,j) to (i,k) with j < k < n and k - j <= grid[i][j], or from (i,j) to (k,j) with i < k < m and k - i <= grid[i][j]. The function returns a result r and r = -1 if and only if no finite sequence of cells (i_0,j_0),...,(i_t,j_t) exists with t >= 0, (i_0,j_0) = (0,0), (i_t,j_t) = (m-1,n-1), and every consecutive pair a legal move.
    Preconditions: Let m = len(grid). The slice is nonempty, so let n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m*n <= 100000, for every i with 0 <= i < m and every j with 0 <= j < n we have 0 <= grid[i][j] < m*n, and grid[m-1][n-1] = 0. -/
  theorem spec_5
      (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hm1 : 1 ≤ m)
      (hn : ∀ v ∈ grid.val, v.val.length = n)
      (hn1 : 1 ≤ n)
      (hsize : m * n ≤ 100000)
      (hval : ∀ i j, i < m → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < ((m * n : Nat) : Int))
      (hend : cellVal grid (m - 1) (n - 1) = 0) :
      ∃ r, Aegis.MinimumVisitedCells.minimum_visited_cells grid = ok r ∧
        (r.val = -1 ↔ ¬ ∃ p, IsPath grid m n p) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hm1 : 1 ≤ m)
        (hn : ∀ v ∈ grid.val, v.val.length = n)
        (hn1 : 1 ≤ n)
        (hsize : m * n ≤ 100000)
        (hval : ∀ i j, i < m → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < ((m * n : Nat) : Int))
        (hend : cellVal grid (m - 1) (n - 1) = 0), ∃ r, Aegis.MinimumVisitedCells.minimum_visited_cells grid = ok r ∧
          (r.val = -1 ↔ ¬ ∃ p, IsPath grid m n p)) := by
    sorry

  /-- Whenever m > 1, n > 1, and the function returns a result r with r != -1, we have r >= 3.
    Preconditions: Let m = len(grid). The slice is nonempty, so let n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m*n <= 100000, for every i with 0 <= i < m and every j with 0 <= j < n we have 0 <= grid[i][j] < m*n, and grid[m-1][n-1] = 0. -/
  theorem spec_6
      (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hm1 : 1 ≤ m)
      (hn : ∀ v ∈ grid.val, v.val.length = n)
      (hn1 : 1 ≤ n)
      (hsize : m * n ≤ 100000)
      (hval : ∀ i j, i < m → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < ((m * n : Nat) : Int))
      (hend : cellVal grid (m - 1) (n - 1) = 0)
      (hm2 : 1 < m) (hn2 : 1 < n) :
      ∀ r, Aegis.MinimumVisitedCells.minimum_visited_cells grid = ok r → r.val ≠ -1 →
        3 ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hm1 : 1 ≤ m)
        (hn : ∀ v ∈ grid.val, v.val.length = n)
        (hn1 : 1 ≤ n)
        (hsize : m * n ≤ 100000)
        (hval : ∀ i j, i < m → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < ((m * n : Nat) : Int))
        (hend : cellVal grid (m - 1) (n - 1) = 0)
        (hm2 : 1 < m) (hn2 : 1 < n), ∀ r, Aegis.MinimumVisitedCells.minimum_visited_cells grid = ok r → r.val ≠ -1 →
          3 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, there exists a finite sequence of cells (i_0,j_0),...,(i_t,j_t) such that t >= 0, t+1 = r, every (i_q,j_q) satisfies 0 <= i_q < m and 0 <= j_q < n, (i_0,j_0) = (0,0), (i_t,j_t) = (m-1,n-1), and for each q < t either i_{q+1} = i_q, j_q < j_{q+1}, and j_{q+1} - j_q <= grid[i_q][j_q], or j_{q+1} = j_q, i_q < i_{q+1}, and i_{q+1} - i_q <= grid[i_q][j_q].
    Preconditions: Let m = len(grid). The slice is nonempty, so let n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m*n <= 100000, for every i with 0 <= i < m and every j with 0 <= j < n we have 0 <= grid[i][j] < m*n, and grid[m-1][n-1] = 0. -/
  theorem spec_7
      (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hm1 : 1 ≤ m)
      (hn : ∀ v ∈ grid.val, v.val.length = n)
      (hn1 : 1 ≤ n)
      (hsize : m * n ≤ 100000)
      (hval : ∀ i j, i < m → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < ((m * n : Nat) : Int))
      (hend : cellVal grid (m - 1) (n - 1) = 0) :
      ∀ r, Aegis.MinimumVisitedCells.minimum_visited_cells grid = ok r → r.val ≠ -1 →
        ∃ p, IsPath grid m n p ∧ (p.length : Int) = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hm1 : 1 ≤ m)
        (hn : ∀ v ∈ grid.val, v.val.length = n)
        (hn1 : 1 ≤ n)
        (hsize : m * n ≤ 100000)
        (hval : ∀ i j, i < m → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < ((m * n : Nat) : Int))
        (hend : cellVal grid (m - 1) (n - 1) = 0), ∀ r, Aegis.MinimumVisitedCells.minimum_visited_cells grid = ok r → r.val ≠ -1 →
          ∃ p, IsPath grid m n p ∧ (p.length : Int) = r.val) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, every finite sequence of cells (i_0,j_0),...,(i_t,j_t) with t >= 0, all cells inside the m by n grid, (i_0,j_0) = (0,0), (i_t,j_t) = (m-1,n-1), and each consecutive pair either being on the same row with increasing column and column increase at most grid[i_q][j_q], or on the same column with increasing row and row increase at most grid[i_q][j_q], satisfies t+1 >= r.
    Preconditions: Let m = len(grid). The slice is nonempty, so let n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m*n <= 100000, for every i with 0 <= i < m and every j with 0 <= j < n we have 0 <= grid[i][j] < m*n, and grid[m-1][n-1] = 0. -/
  theorem spec_8
      (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : m = grid.val.length)
      (hm1 : 1 ≤ m)
      (hn : ∀ v ∈ grid.val, v.val.length = n)
      (hn1 : 1 ≤ n)
      (hsize : m * n ≤ 100000)
      (hval : ∀ i j, i < m → j < n →
        0 ≤ cellVal grid i j ∧ cellVal grid i j < ((m * n : Nat) : Int))
      (hend : cellVal grid (m - 1) (n - 1) = 0) :
      ∀ r, Aegis.MinimumVisitedCells.minimum_visited_cells grid = ok r → r.val ≠ -1 →
        ∀ p, IsPath grid m n p → r.val ≤ (p.length : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : m = grid.val.length)
        (hm1 : 1 ≤ m)
        (hn : ∀ v ∈ grid.val, v.val.length = n)
        (hn1 : 1 ≤ n)
        (hsize : m * n ≤ 100000)
        (hval : ∀ i j, i < m → j < n →
          0 ≤ cellVal grid i j ∧ cellVal grid i j < ((m * n : Nat) : Int))
        (hend : cellVal grid (m - 1) (n - 1) = 0), ∀ r, Aegis.MinimumVisitedCells.minimum_visited_cells grid = ok r → r.val ≠ -1 →
          ∀ p, IsPath grid m n p → r.val ≤ (p.length : Int)) := by
    sorry

  end AegisSpec.MinimumVisitedCells
