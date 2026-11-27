import Aegis.MaxProductPath.Code.Funs

/-!
# Specifications of `Aegis.MaxProductPath.max_product_path`

LeetCode problem `maximum-non-negative-product-in-a-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxProductPath

  def gridCells (grid : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    grid.val.map (fun row => row.val.map (fun x => x.val))

  def cell (g : List (List ℤ)) (i j : ℕ) : ℤ :=
    (g.getD i []).getD j 0

  def numCols (g : List (List ℤ)) : ℕ :=
    (g.headD []).length

  def pathProducts (g : List (List ℤ)) (i j : ℕ) : List ℤ :=
    match i, j with
    | 0, 0 => [cell g 0 0]
    | 0, j + 1 => (pathProducts g 0 j).map (fun p => p * cell g 0 (j + 1))
    | i + 1, 0 => (pathProducts g i 0).map (fun p => p * cell g (i + 1) 0)
    | i + 1, j + 1 =>
        (pathProducts g i (j + 1)).map (fun p => p * cell g (i + 1) (j + 1)) ++
          (pathProducts g (i + 1) j).map (fun p => p * cell g (i + 1) (j + 1))
  termination_by i + j

  def pathProductSet (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) : List ℤ :=
    pathProducts (gridCells grid) (m - 1) (n - 1)

  def IsGreatestNonneg (S : List ℤ) (q : ℤ) : Prop :=
    0 ≤ q ∧ q ∈ S ∧ ∀ p ∈ S, 0 ≤ p → p ≤ q

  def transposeCells (g : List (List ℤ)) : List (List ℤ) :=
    (List.range (numCols g)).map (fun j => (List.range g.length).map (fun i => cell g i j))

  def rotateCells (g : List (List ℤ)) : List (List ℤ) :=
    g.reverse.map List.reverse

  def IsValidMatrix (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) : Prop :=
    grid.val.length = m ∧
      1 ≤ m ∧ m ≤ 15 ∧ 1 ≤ n ∧ n ≤ 15 ∧
        (∀ i : ℕ, i < m → ∀ row, grid.val[i]? = some row → row.val.length = n) ∧
          (∀ i j : ℕ, i < m → j < n →
            -4 ≤ cell (gridCells grid) i j ∧ cell (gridCells grid) i j ≤ 4)

  /-- Let S be the set of products of all monotone paths from (0,0) to (m-1,n-1) that move only right or down, where the product of a path is the product of grid[i][j] over all cells (i,j) visited by the path. The function returns a result r. If S has no element p with p >= 0, then r = -1. Otherwise r = (max {p in S | p >= 0}) mod 1000000007.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The matrix is rectangular with 1 <= m <= 15, 1 <= n <= 15, every row grid[i] has length n, and -4 <= grid[i][j] <= 4 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : IsValidMatrix grid m n) :
      ∃ r : Std.I64,
        Aegis.MaxProductPath.max_product_path grid = ok r ∧
          ((∀ p : ℤ, p ∈ pathProductSet grid m n → p < 0) → r.val = -1) ∧
            (∀ q : ℤ, IsGreatestNonneg (pathProductSet grid m n) q →
              r.val = q % 1000000007) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : IsValidMatrix grid m n), ∃ r : Std.I64,
          Aegis.MaxProductPath.max_product_path grid = ok r ∧
            ((∀ p : ℤ, p ∈ pathProductSet grid m n → p < 0) → r.val = -1) ∧
              (∀ q : ℤ, IsGreatestNonneg (pathProductSet grid m n) q →
                r.val = q % 1000000007)) := by
    sorry

  /-- The function returns some result r; it does not fail because of overflow, out-of-bounds indexing, or any other panic.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The matrix is rectangular with 1 <= m <= 15, 1 <= n <= 15, every row grid[i] has length n, and -4 <= grid[i][j] <= 4 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : IsValidMatrix grid m n) :
      ∃ r : Std.I64, Aegis.MaxProductPath.max_product_path grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : IsValidMatrix grid m n), ∃ r : Std.I64, Aegis.MaxProductPath.max_product_path grid = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 0 <= r < 1000000007.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The matrix is rectangular with 1 <= m <= 15, 1 <= n <= 15, every row grid[i] has length n, and -4 <= grid[i][j] <= 4 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : IsValidMatrix grid m n) :
      ∀ r : Std.I64, Aegis.MaxProductPath.max_product_path grid = ok r →
        r.val = -1 ∨ (0 ≤ r.val ∧ r.val < 1000000007) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : IsValidMatrix grid m n), ∀ r : Std.I64, Aegis.MaxProductPath.max_product_path grid = ok r →
          r.val = -1 ∨ (0 ≤ r.val ∧ r.val < 1000000007)) := by
    sorry

  /-- The function returns r = -1 if and only if every monotone path from (0,0) to (m-1,n-1) moving only right or down has a strictly negative product, where the product of a path is the product of grid[i][j] over all cells visited by the path.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The matrix is rectangular with 1 <= m <= 15, 1 <= n <= 15, every row grid[i] has length n, and -4 <= grid[i][j] <= 4 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : IsValidMatrix grid m n) :
      ∀ r : Std.I64, Aegis.MaxProductPath.max_product_path grid = ok r →
        (r.val = -1 ↔ ∀ p : ℤ, p ∈ pathProductSet grid m n → p < 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : IsValidMatrix grid m n), ∀ r : Std.I64, Aegis.MaxProductPath.max_product_path grid = ok r →
          (r.val = -1 ↔ ∀ p : ℤ, p ∈ pathProductSet grid m n → p < 0)) := by
    sorry

  /-- Let gridT be the n by m matrix defined by gridT[j][i] = grid[i][j] for 0 <= i < m and 0 <= j < n. Then max_product_path(gridT) = max_product_path(grid).
    Preconditions: Let m = len(grid) and n = len(grid[0]). The matrix is rectangular with 1 <= m <= 15, 1 <= n <= 15, every row grid[i] has length n, and -4 <= grid[i][j] <= 4 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_5 (grid gridT : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : IsValidMatrix grid m n) (hvalidT : IsValidMatrix gridT n m)
      (htranspose : gridCells gridT = transposeCells (gridCells grid)) :
      Aegis.MaxProductPath.max_product_path gridT = Aegis.MaxProductPath.max_product_path grid := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid gridT : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : IsValidMatrix grid m n) (hvalidT : IsValidMatrix gridT n m)
        (htranspose : gridCells gridT = transposeCells (gridCells grid)), Aegis.MaxProductPath.max_product_path gridT = Aegis.MaxProductPath.max_product_path grid) := by
    sorry

  /-- Let gridR be the m by n matrix defined by gridR[i][j] = grid[m-1-i][n-1-j] for 0 <= i < m and 0 <= j < n. Then max_product_path(gridR) = max_product_path(grid).
    Preconditions: Let m = len(grid) and n = len(grid[0]). The matrix is rectangular with 1 <= m <= 15, 1 <= n <= 15, every row grid[i] has length n, and -4 <= grid[i][j] <= 4 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_6 (grid gridR : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : IsValidMatrix grid m n) (hvalidR : IsValidMatrix gridR m n)
      (hrotate : gridCells gridR = rotateCells (gridCells grid)) :
      Aegis.MaxProductPath.max_product_path gridR = Aegis.MaxProductPath.max_product_path grid := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid gridR : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : IsValidMatrix grid m n) (hvalidR : IsValidMatrix gridR m n)
        (hrotate : gridCells gridR = rotateCells (gridCells grid)), Aegis.MaxProductPath.max_product_path gridR = Aegis.MaxProductPath.max_product_path grid) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, there exists a monotone path from (0,0) to (m-1,n-1) moving only right or down whose product P satisfies P >= 0 and P mod 1000000007 = r.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The matrix is rectangular with 1 <= m <= 15, 1 <= n <= 15, every row grid[i] has length n, and -4 <= grid[i][j] <= 4 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : IsValidMatrix grid m n) :
      ∀ r : Std.I64, Aegis.MaxProductPath.max_product_path grid = ok r → r.val ≠ -1 →
        ∃ P : ℤ, P ∈ pathProductSet grid m n ∧ 0 ≤ P ∧ P % 1000000007 = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : IsValidMatrix grid m n), ∀ r : Std.I64, Aegis.MaxProductPath.max_product_path grid = ok r → r.val ≠ -1 →
          ∃ P : ℤ, P ∈ pathProductSet grid m n ∧ 0 ≤ P ∧ P % 1000000007 = r.val) := by
    sorry

  end AegisSpec.MaxProductPath
