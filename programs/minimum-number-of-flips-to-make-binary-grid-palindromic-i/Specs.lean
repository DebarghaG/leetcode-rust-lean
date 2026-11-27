import Aegis.MinFlips.Code.Funs

/-!
# Specifications of `Aegis.MinFlips.min_flips`

LeetCode problem `minimum-number-of-flips-to-make-binary-grid-palindromic-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinFlips

  namespace AegisSpec.MinFlips

  def numRows (grid : Slice (alloc.vec.Vec I64)) : Nat :=
    grid.val.length

  def numCols (grid : Slice (alloc.vec.Vec I64)) : Nat :=
    ((grid.val[0]?).map (fun row => row.val.length)).getD 0

  def cell (grid : Slice (alloc.vec.Vec I64)) (i j : Nat) : Int :=
    match grid.val[i]? with
    | none => 0
    | some row => ((row.val[j]?).map (fun v => v.val)).getD 0

  def RowPal (c : Nat → Nat → Int) (n i : Nat) : Prop :=
    ∀ j, j < n / 2 → c i j = c i (n - 1 - j)

  def ColPal (c : Nat → Nat → Int) (m j : Nat) : Prop :=
    ∀ i, i < m / 2 → c i j = c (m - 1 - i) j

  def RowPalindromic (grid : Slice (alloc.vec.Vec I64)) (i : Nat) : Prop :=
    RowPal (cell grid) (numCols grid) i

  def ColPalindromic (grid : Slice (alloc.vec.Vec I64)) (j : Nat) : Prop :=
    ColPal (cell grid) (numRows grid) j

  def rowCost (grid : Slice (alloc.vec.Vec I64)) : Nat :=
    (((Finset.range (numRows grid)).product (Finset.range (numCols grid / 2))).filter
      (fun p => cell grid p.1 p.2 ≠ cell grid p.1 (numCols grid - 1 - p.2))).card

  def colCost (grid : Slice (alloc.vec.Vec I64)) : Nat :=
    (((Finset.range (numRows grid / 2)).product (Finset.range (numCols grid))).filter
      (fun p => cell grid p.1 p.2 ≠ cell grid (numRows grid - 1 - p.1) p.2)).card

  def flippedCell (grid : Slice (alloc.vec.Vec I64)) (S : Finset (Nat × Nat)) (i j : Nat) : Int :=
    if (i, j) ∈ S then 1 - cell grid i j else cell grid i j

  def IsValid (grid : Slice (alloc.vec.Vec I64)) : Prop :=
    1 ≤ numRows grid ∧
    1 ≤ numCols grid ∧
    numRows grid * numCols grid ≤ 200000 ∧
    (∀ i, i < numRows grid →
      (grid.val[i]?).map (fun row => row.val.length) = some (numCols grid)) ∧
    (∀ i j, i < numRows grid → j < numCols grid → cell grid i j = 0 ∨ cell grid i j = 1)

  def IsTranspose (grid GT : Slice (alloc.vec.Vec I64)) : Prop :=
    numRows GT = numCols grid ∧
    numCols GT = numRows grid ∧
    ∀ i j, i < numRows grid → j < numCols grid → cell GT j i = cell grid i j

  def IsComplement (grid grid' : Slice (alloc.vec.Vec I64)) : Prop :=
    numRows grid' = numRows grid ∧
    numCols grid' = numCols grid ∧
    ∀ i j, i < numRows grid → j < numCols grid → cell grid' i j = 1 - cell grid i j

  /-- Whenever the function returns a result r, r = min(R, C). Equivalently, r is the minimum number of cell flips needed either to make every row palindromic or to make every column palindromic; the two goals are alternatives and r is the smaller of their two separate minimum costs.
    Preconditions: Let m = len(grid). Assume m >= 1. Let n = len(grid[0]). The grid is valid: n >= 1, m*n <= 200000, for every i with 0 <= i < m, len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. Define R as the number of pairs (i,j) with 0 <= i < m and 0 <= j < floor(n/2) such that grid[i][j] != grid[i][n-1-j]. Define C as the number of pairs (i,j) with 0 <= i < floor(m/2) and 0 <= j < n such that grid[i][j] != grid[m-1-i][j]. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid) :
      ∀ r : I64, min_flips grid = ok r →
        r.val = ((min (rowCost grid) (colCost grid) : Nat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid), ∀ r : I64, min_flips grid = ok r →
          r.val = ((min (rowCost grid) (colCost grid) : Nat) : Int)) := by
    sorry

  /-- For every valid grid, the function returns a result r and does not fail: it does not panic, read out of bounds, or overflow.
    Preconditions: Let m = len(grid). Assume m >= 1. Let n = len(grid[0]). The grid is valid: n >= 1, m*n <= 200000, for every i with 0 <= i < m, len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid) :
      ∃ r : I64, min_flips grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid), ∃ r : I64, min_flips grid = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r <= R.
    Preconditions: Let m = len(grid). Assume m >= 1. Let n = len(grid[0]). The grid is valid: n >= 1, m*n <= 200000, for every i with 0 <= i < m, len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. Let R be the number of pairs (i,j) with 0 <= i < m and 0 <= j < floor(n/2) such that grid[i][j] != grid[i][n-1-j]. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid) :
      ∀ r : I64, min_flips grid = ok r → r.val ≤ ((rowCost grid : Nat) : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid), ∀ r : I64, min_flips grid = ok r → r.val ≤ ((rowCost grid : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r <= C.
    Preconditions: Let m = len(grid). Assume m >= 1. Let n = len(grid[0]). The grid is valid: n >= 1, m*n <= 200000, for every i with 0 <= i < m, len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. Let C be the number of pairs (i,j) with 0 <= i < floor(m/2) and 0 <= j < n such that grid[i][j] != grid[m-1-i][j]. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid) :
      ∀ r : I64, min_flips grid = ok r → r.val ≤ ((colCost grid : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid), ∀ r : I64, min_flips grid = ok r → r.val ≤ ((colCost grid : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = R.
    Preconditions: Let m = len(grid). Assume m >= 1. Let n = len(grid[0]). The grid is valid: n >= 1, m*n <= 200000, for every i with 0 <= i < m, len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. Let R be the number of pairs (i,j) with 0 <= i < m and 0 <= j < floor(n/2) such that grid[i][j] != grid[i][n-1-j]. Let C be the number of pairs (i,j) with 0 <= i < floor(m/2) and 0 <= j < n such that grid[i][j] != grid[m-1-i][j]. Assume R <= C. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid)
      (hle : rowCost grid ≤ colCost grid) :
      ∀ r : I64, min_flips grid = ok r → r.val = ((rowCost grid : Nat) : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid)
        (hle : rowCost grid ≤ colCost grid), ∀ r : I64, min_flips grid = ok r → r.val = ((rowCost grid : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = C.
    Preconditions: Let m = len(grid). Assume m >= 1. Let n = len(grid[0]). The grid is valid: n >= 1, m*n <= 200000, for every i with 0 <= i < m, len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. Let R be the number of pairs (i,j) with 0 <= i < m and 0 <= j < floor(n/2) such that grid[i][j] != grid[i][n-1-j]. Let C be the number of pairs (i,j) with 0 <= i < floor(m/2) and 0 <= j < n such that grid[i][j] != grid[m-1-i][j]. Assume C <= R. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid)
      (hle : colCost grid ≤ rowCost grid) :
      ∀ r : I64, min_flips grid = ok r → r.val = ((colCost grid : Nat) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid)
        (hle : colCost grid ≤ rowCost grid), ∀ r : I64, min_flips grid = ok r → r.val = ((colCost grid : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r <= m * floor(n/2).
    Preconditions: Let m = len(grid). Assume m >= 1. Let n = len(grid[0]). The grid is valid: n >= 1, m*n <= 200000, for every i with 0 <= i < m, len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid) :
      ∀ r : I64, min_flips grid = ok r →
        r.val ≤ ((numRows grid * (numCols grid / 2) : Nat) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid), ∀ r : I64, min_flips grid = ok r →
          r.val ≤ ((numRows grid * (numCols grid / 2) : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r <= n * floor(m/2).
    Preconditions: Let m = len(grid). Assume m >= 1. Let n = len(grid[0]). The grid is valid: n >= 1, m*n <= 200000, for every i with 0 <= i < m, len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid) :
      ∀ r : I64, min_flips grid = ok r →
        r.val ≤ ((numCols grid * (numRows grid / 2) : Nat) : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid), ∀ r : I64, min_flips grid = ok r →
          r.val ≤ ((numCols grid * (numRows grid / 2) : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if either every row is already palindromic or every column is already palindromic. A row i is palindromic when grid[i][j] = grid[i][n-1-j] for every j with 0 <= j < floor(n/2). A column j is palindromic when grid[i][j] = grid[m-1-i][j] for every i with 0 <= i < floor(m/2).
    Preconditions: Let m = len(grid). Assume m >= 1. Let n = len(grid[0]). The grid is valid: n >= 1, m*n <= 200000, for every i with 0 <= i < m, len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid) :
      ∀ r : I64, min_flips grid = ok r →
        (r.val = 0 ↔
          ((∀ i, i < numRows grid → RowPalindromic grid i) ∨
            (∀ j, j < numCols grid → ColPalindromic grid j))) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid), ∀ r : I64, min_flips grid = ok r →
          (r.val = 0 ↔
            ((∀ i, i < numRows grid → RowPalindromic grid i) ∨
              (∀ j, j < numCols grid → ColPalindromic grid j)))) := by
    sorry

  /-- Whenever the function returns a result r, there exists a set S of cell positions (i,j) with 0 <= i < m and 0 <= j < n such that |S| = r and, after flipping every cell in S, in the resulting matrix either every row is palindromic or every column is palindromic.
    Preconditions: Let m = len(grid). Assume m >= 1. Let n = len(grid[0]). The grid is valid: n >= 1, m*n <= 200000, for every i with 0 <= i < m, len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. -/
  theorem spec_10 (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid) :
      ∀ r : I64, min_flips grid = ok r →
        ∃ S : Finset (Nat × Nat),
          (∀ p ∈ S, p.1 < numRows grid ∧ p.2 < numCols grid) ∧
          ((S.card : Nat) : Int) = r.val ∧
          ((∀ i, i < numRows grid → RowPal (flippedCell grid S) (numCols grid) i) ∨
            (∀ j, j < numCols grid → ColPal (flippedCell grid S) (numRows grid) j)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid), ∀ r : I64, min_flips grid = ok r →
          ∃ S : Finset (Nat × Nat),
            (∀ p ∈ S, p.1 < numRows grid ∧ p.2 < numCols grid) ∧
            ((S.card : Nat) : Int) = r.val ∧
            ((∀ i, i < numRows grid → RowPal (flippedCell grid S) (numCols grid) i) ∨
              (∀ j, j < numCols grid → ColPal (flippedCell grid S) (numRows grid) j))) := by
    sorry

  /-- Let GT be the n by m matrix with GT[j][i] = grid[i][j] for every i with 0 <= i < m and every j with 0 <= j < n. Whenever min_flips(grid) returns a result r and min_flips(GT) returns a result rT, r = rT.
    Preconditions: Let m = len(grid). Assume m >= 1. Let n = len(grid[0]). The grid is valid: n >= 1, m*n <= 200000, for every i with 0 <= i < m, len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. -/
  theorem spec_11 (grid GT : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid)
      (htrans : IsTranspose grid GT) :
      ∀ r rT : I64, min_flips grid = ok r → min_flips GT = ok rT → r.val = rT.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid GT : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid)
        (htrans : IsTranspose grid GT), ∀ r rT : I64, min_flips grid = ok r → min_flips GT = ok rT → r.val = rT.val) := by
    sorry

  /-- Let grid' be the m by n matrix with grid'[i][j] = 1 - grid[i][j] for every i with 0 <= i < m and every j with 0 <= j < n. Whenever min_flips(grid) returns a result r and min_flips(grid') returns a result r', r = r'.
    Preconditions: Let m = len(grid). Assume m >= 1. Let n = len(grid[0]). The grid is valid: n >= 1, m*n <= 200000, for every i with 0 <= i < m, len(grid[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. -/
  theorem spec_12 (grid grid' : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid)
      (hcompl : IsComplement grid grid') :
      ∀ r r' : I64, min_flips grid = ok r → min_flips grid' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid grid' : Slice (alloc.vec.Vec I64)) (hvalid : IsValid grid)
        (hcompl : IsComplement grid grid'), ∀ r r' : I64, min_flips grid = ok r → min_flips grid' = ok r' → r.val = r'.val) := by
    sorry

  end AegisSpec.MinFlips
