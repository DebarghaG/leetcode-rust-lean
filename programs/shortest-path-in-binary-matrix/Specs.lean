import Aegis.ShortestPathBinaryMatrix.Code.Funs

/-!
# Specifications of `Aegis.ShortestPathBinaryMatrix.shortest_path_binary_matrix`

LeetCode problem `shortest-path-in-binary-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ShortestPathBinaryMatrix

  open Aegis.ShortestPathBinaryMatrix (shortest_path_binary_matrix)

  def dim (grid : Slice (alloc.vec.Vec Std.I64)) : Nat := grid.val.length

  def cell (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    ((grid.val[i]?).bind (fun row => (row.val[j]?).map (fun x => x.val))).getD 0

  theorem cell_eq {grid : Slice (alloc.vec.Vec Std.I64)} {i j : Nat}
      (hi : i < grid.val.length) (hj : j < (grid.val[i]).val.length) :
      cell grid i j = ((grid.val[i]).val[j]).val := by
    have h1 : grid.val[i]? = some grid.val[i] := List.getElem?_eq_getElem hi
    have h2 : (grid.val[i]).val[j]? = some ((grid.val[i]).val[j]) :=
      List.getElem?_eq_getElem hj
    simp [cell, h1, h2]

  def validGrid (grid : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    1 ≤ grid.val.length ∧
    grid.val.length ≤ 100 ∧
    (∀ (i : Nat) (hi : i < grid.val.length), (grid.val[i]).val.length = grid.val.length) ∧
    (∀ (i : Nat) (hi : i < grid.val.length) (j : Nat) (hj : j < (grid.val[i]).val.length),
      ((grid.val[i]).val[j]).val = 0 ∨ ((grid.val[i]).val[j]).val = 1)

  def adiff (a b : Nat) : Nat := if a ≤ b then b - a else a - b

  def adjacent8 (p q : Nat × Nat) : Prop := max (adiff p.1 q.1) (adiff p.2 q.2) = 1

  def clearPath (grid : Slice (alloc.vec.Vec Std.I64)) (P : List (Nat × Nat)) : Prop :=
    1 ≤ P.length ∧
    P.head? = some (0, 0) ∧
    P.getLast? = some (dim grid - 1, dim grid - 1) ∧
    (∀ p ∈ P, p.1 < dim grid ∧ p.2 < dim grid ∧ cell grid p.1 p.2 = 0) ∧
    (∀ q ∈ P.zip P.tail, adjacent8 q.1 q.2)

  def hasClearPath (grid : Slice (alloc.vec.Vec Std.I64)) : Prop := ∃ P, clearPath grid P

  def zeroCells (grid : Slice (alloc.vec.Vec Std.I64)) : Nat :=
    ((List.range (dim grid)).map
      (fun i => ((List.range (dim grid)).map
        (fun j => if cell grid i j = 0 then 1 else 0)).sum)).sum

  /-- Whenever the function returns a result r, the following holds. If there is no clear path from (0,0) to (n-1,n-1) in grid, then r = -1. If there is at least one clear path, then r is the minimum length of a clear path; equivalently, r >= 1, there exists a clear path P with len(P) = r, and every clear path P has r <= len(P). A clear path is a finite sequence of cells (r_0,c_0),...,(r_{k-1},c_{k-1}) with k >= 1 such that (r_0,c_0) = (0,0), (r_{k-1},c_{k-1}) = (n-1,n-1), grid[r_t][c_t] = 0 for every 0 <= t < k, and for every 0 <= t < k-1 the cells (r_t,c_t) and (r_{t+1},c_{t+1}) are 8-directionally adjacent, meaning max(|r_{t+1}-r_t|, |c_{t+1}-c_t|) = 1. The length len(P) of such a path is k.
    Preconditions: Let n = len(grid). The input is a valid n x n binary matrix: 1 <= n <= 100; every row grid[i] has length n for 0 <= i < n; and every entry grid[i][j] is 0 or 1 for 0 <= i < n and 0 <= j < n. Indices are 0-based. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid) :
      ∀ r, shortest_path_binary_matrix grid = ok r →
        (¬ hasClearPath grid → r.val = -1) ∧
        (hasClearPath grid →
          1 ≤ r.val ∧
            (∃ P, clearPath grid P ∧ (P.length : Int) = r.val) ∧
            (∀ P, clearPath grid P → r.val ≤ (P.length : Int))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid), ∀ r, shortest_path_binary_matrix grid = ok r →
          (¬ hasClearPath grid → r.val = -1) ∧
          (hasClearPath grid →
            1 ≤ r.val ∧
              (∃ P, clearPath grid P ∧ (P.length : Int) = r.val) ∧
              (∀ P, clearPath grid P → r.val ≤ (P.length : Int)))) := by
    sorry

  /-- The function returns a result r for every input grid satisfying the preconditions; it does not fail, panic, or overflow.
    Preconditions: Let n = len(grid). The input is a valid n x n binary matrix: 1 <= n <= 100; every row grid[i] has length n for 0 <= i < n; and every entry grid[i][j] is 0 or 1 for 0 <= i < n and 0 <= j < n. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid) :
      ∃ r : Std.I64, shortest_path_binary_matrix grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid), ∃ r : Std.I64, shortest_path_binary_matrix grid = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or n <= r <= n*n.
    Preconditions: Let n = len(grid). The input is a valid n x n binary matrix: 1 <= n <= 100; every row grid[i] has length n for 0 <= i < n; and every entry grid[i][j] is 0 or 1 for 0 <= i < n and 0 <= j < n. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid) :
      ∀ r, shortest_path_binary_matrix grid = ok r →
        r.val = -1 ∨ ((dim grid : Int) ≤ r.val ∧ r.val ≤ (dim grid : Int) * (dim grid : Int)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid), ∀ r, shortest_path_binary_matrix grid = ok r →
          r.val = -1 ∨ ((dim grid : Int) ≤ r.val ∧ r.val ≤ (dim grid : Int) * (dim grid : Int))) := by
    sorry

  /-- Whenever the function returns a result r, if grid[0][0] = 1, then r = -1.
    Preconditions: Let n = len(grid). The input is a valid n x n binary matrix: 1 <= n <= 100; every row grid[i] has length n for 0 <= i < n; and every entry grid[i][j] is 0 or 1 for 0 <= i < n and 0 <= j < n. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid) :
      ∀ r, shortest_path_binary_matrix grid = ok r → cell grid 0 0 = 1 → r.val = -1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid), ∀ r, shortest_path_binary_matrix grid = ok r → cell grid 0 0 = 1 → r.val = -1) := by
    sorry

  /-- Whenever the function returns a result r, if grid[n-1][n-1] = 1, then r = -1.
    Preconditions: Let n = len(grid). The input is a valid n x n binary matrix: 1 <= n <= 100; every row grid[i] has length n for 0 <= i < n; and every entry grid[i][j] is 0 or 1 for 0 <= i < n and 0 <= j < n. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid) :
      ∀ r, shortest_path_binary_matrix grid = ok r →
        cell grid (dim grid - 1) (dim grid - 1) = 1 → r.val = -1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid), ∀ r, shortest_path_binary_matrix grid = ok r →
          cell grid (dim grid - 1) (dim grid - 1) = 1 → r.val = -1) := by
    sorry

  /-- Whenever the function returns a result r, if n = 1, then r = 1 if grid[0][0] = 0, and r = -1 if grid[0][0] = 1.
    Preconditions: Let n = len(grid). The input is a valid n x n binary matrix: 1 <= n <= 100; every row grid[i] has length n for 0 <= i < n; and every entry grid[i][j] is 0 or 1 for 0 <= i < n and 0 <= j < n. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid) :
      ∀ r, shortest_path_binary_matrix grid = ok r → dim grid = 1 →
        (cell grid 0 0 = 0 → r.val = 1) ∧ (cell grid 0 0 = 1 → r.val = -1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid), ∀ r, shortest_path_binary_matrix grid = ok r → dim grid = 1 →
          (cell grid 0 0 = 0 → r.val = 1) ∧ (cell grid 0 0 = 1 → r.val = -1)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if n = 1 and grid[0][0] = 0.
    Preconditions: Let n = len(grid). The input is a valid n x n binary matrix: 1 <= n <= 100; every row grid[i] has length n for 0 <= i < n; and every entry grid[i][j] is 0 or 1 for 0 <= i < n and 0 <= j < n. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid) :
      ∀ r, shortest_path_binary_matrix grid = ok r →
        (r.val = 1 ↔ dim grid = 1 ∧ cell grid 0 0 = 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid), ∀ r, shortest_path_binary_matrix grid = ok r →
          (r.val = 1 ↔ dim grid = 1 ∧ cell grid 0 0 = 0)) := by
    sorry

  /-- Whenever the function returns a result r, if r >= 1, then grid[0][0] = 0 and grid[n-1][n-1] = 0.
    Preconditions: Let n = len(grid). The input is a valid n x n binary matrix: 1 <= n <= 100; every row grid[i] has length n for 0 <= i < n; and every entry grid[i][j] is 0 or 1 for 0 <= i < n and 0 <= j < n. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid) :
      ∀ r, shortest_path_binary_matrix grid = ok r → 1 ≤ r.val →
        cell grid 0 0 = 0 ∧ cell grid (dim grid - 1) (dim grid - 1) = 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid), ∀ r, shortest_path_binary_matrix grid = ok r → 1 ≤ r.val →
          cell grid 0 0 = 0 ∧ cell grid (dim grid - 1) (dim grid - 1) = 0) := by
    sorry

  /-- Whenever the function returns a result r, r >= 1 if and only if there exists a clear path from (0,0) to (n-1,n-1) in grid. A clear path here is a sequence of cells from (0,0) to (n-1,n-1), all with grid value 0, with consecutive cells distinct and 8-directionally adjacent; its length is its number of cells.
    Preconditions: Let n = len(grid). The input is a valid n x n binary matrix: 1 <= n <= 100; every row grid[i] has length n for 0 <= i < n; and every entry grid[i][j] is 0 or 1 for 0 <= i < n and 0 <= j < n. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid) :
      ∀ r, shortest_path_binary_matrix grid = ok r → (1 ≤ r.val ↔ hasClearPath grid) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid), ∀ r, shortest_path_binary_matrix grid = ok r → (1 ≤ r.val ↔ hasClearPath grid)) := by
    sorry

  /-- Whenever the function returns a result r, if r >= 1, then there exists a clear path P from (0,0) to (n-1,n-1) in grid with len(P) = r. Here clear path and len are as in spec_1: a sequence of zero cells with consecutive cells distinct and 8-directionally adjacent, and length is the number of cells.
    Preconditions: Let n = len(grid). The input is a valid n x n binary matrix: 1 <= n <= 100; every row grid[i] has length n for 0 <= i < n; and every entry grid[i][j] is 0 or 1 for 0 <= i < n and 0 <= j < n. -/
  theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid) :
      ∀ r, shortest_path_binary_matrix grid = ok r → 1 ≤ r.val →
        ∃ P : List (Nat × Nat), clearPath grid P ∧ (P.length : Int) = r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid), ∀ r, shortest_path_binary_matrix grid = ok r → 1 ≤ r.val →
          ∃ P : List (Nat × Nat), clearPath grid P ∧ (P.length : Int) = r.val) := by
    sorry

  /-- Whenever the function returns a result r, if r >= 1, then for every clear path P from (0,0) to (n-1,n-1) in grid, r <= len(P). Here clear path and len are as in spec_1: a sequence of zero cells with consecutive cells distinct and 8-directionally adjacent, and length is the number of cells.
    Preconditions: Let n = len(grid). The input is a valid n x n binary matrix: 1 <= n <= 100; every row grid[i] has length n for 0 <= i < n; and every entry grid[i][j] is 0 or 1 for 0 <= i < n and 0 <= j < n. -/
  theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid) :
      ∀ r, shortest_path_binary_matrix grid = ok r → 1 ≤ r.val →
        ∀ P : List (Nat × Nat), clearPath grid P → r.val ≤ (P.length : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid), ∀ r, shortest_path_binary_matrix grid = ok r → 1 ≤ r.val →
          ∀ P : List (Nat × Nat), clearPath grid P → r.val ≤ (P.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, if grid[i][j] = 0 for every 0 <= i < n and 0 <= j < n, then r = n.
    Preconditions: Let n = len(grid). The input is a valid n x n binary matrix: 1 <= n <= 100; every row grid[i] has length n for 0 <= i < n; and every entry grid[i][j] is 0 or 1 for 0 <= i < n and 0 <= j < n. -/
  theorem spec_12 (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid) :
      ∀ r, shortest_path_binary_matrix grid = ok r →
        (∀ (i j : Nat), i < dim grid → j < dim grid → cell grid i j = 0) →
          r.val = (dim grid : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid), ∀ r, shortest_path_binary_matrix grid = ok r →
          (∀ (i j : Nat), i < dim grid → j < dim grid → cell grid i j = 0) →
            r.val = (dim grid : Int)) := by
    sorry

  /-- Whenever the function returns a result r, if n = 2, then r = 2 if grid[0][0] = 0 and grid[1][1] = 0, and r = -1 otherwise.
    Preconditions: Let n = len(grid). The input is a valid n x n binary matrix: 1 <= n <= 100; every row grid[i] has length n for 0 <= i < n; and every entry grid[i][j] is 0 or 1 for 0 <= i < n and 0 <= j < n. -/
  theorem spec_13 (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid) :
      ∀ r, shortest_path_binary_matrix grid = ok r → dim grid = 2 →
        (cell grid 0 0 = 0 ∧ cell grid 1 1 = 0 → r.val = 2) ∧
          (¬ (cell grid 0 0 = 0 ∧ cell grid 1 1 = 0) → r.val = -1) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid), ∀ r, shortest_path_binary_matrix grid = ok r → dim grid = 2 →
          (cell grid 0 0 = 0 ∧ cell grid 1 1 = 0 → r.val = 2) ∧
            (¬ (cell grid 0 0 = 0 ∧ cell grid 1 1 = 0) → r.val = -1)) := by
    sorry

  /-- Whenever the function returns a result r, if r >= 1, then r <= z, where z is the number of cells (i,j) with 0 <= i < n, 0 <= j < n, and grid[i][j] = 0.
    Preconditions: Let n = len(grid). The input is a valid n x n binary matrix: 1 <= n <= 100; every row grid[i] has length n for 0 <= i < n; and every entry grid[i][j] is 0 or 1 for 0 <= i < n and 0 <= j < n. -/
  theorem spec_14 (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid) :
      ∀ r, shortest_path_binary_matrix grid = ok r → 1 ≤ r.val →
        r.val ≤ (zeroCells grid : Int) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (h : validGrid grid), ∀ r, shortest_path_binary_matrix grid = ok r → 1 ≤ r.val →
          r.val ≤ (zeroCells grid : Int)) := by
    sorry

  /-- Whenever the function returns a result r on input grid and a result r' on input grid', if r >= 1, then r' >= 1 and r' <= r.
    Preconditions: Let n = len(grid). The input grid is a valid n x n binary matrix: 1 <= n <= 100; every row grid[i] has length n for 0 <= i < n; and every entry grid[i][j] is 0 or 1 for 0 <= i < n and 0 <= j < n. Also let grid' be any second valid n x n binary matrix with grid'[i][j] <= grid[i][j] for every 0 <= i < n and 0 <= j < n; that is, grid' is obtained from grid by changing zero or more 1 entries to 0. -/
  theorem spec_15 (grid grid' : Slice (alloc.vec.Vec Std.I64))
      (h : validGrid grid) (h' : validGrid grid') (hn : dim grid' = dim grid)
      (hle : ∀ (i j : Nat), i < dim grid → j < dim grid → cell grid' i j ≤ cell grid i j) :
      ∀ r r', shortest_path_binary_matrix grid = ok r →
        shortest_path_binary_matrix grid' = ok r' → 1 ≤ r.val → 1 ≤ r'.val ∧ r'.val ≤ r.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64))
        (h : validGrid grid) (h' : validGrid grid') (hn : dim grid' = dim grid)
        (hle : ∀ (i j : Nat), i < dim grid → j < dim grid → cell grid' i j ≤ cell grid i j), ∀ r r', shortest_path_binary_matrix grid = ok r →
          shortest_path_binary_matrix grid' = ok r' → 1 ≤ r.val → 1 ≤ r'.val ∧ r'.val ≤ r.val) := by
    sorry

  end AegisSpec.ShortestPathBinaryMatrix
