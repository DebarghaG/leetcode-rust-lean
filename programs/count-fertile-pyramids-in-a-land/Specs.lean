import Aegis.CountPyramids.Code.Funs

/-!
# Specifications of `Aegis.CountPyramids.count_pyramids`

LeetCode problem `count-fertile-pyramids-in-a-land`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open scoped Classical

  namespace AegisSpec.CountPyramids

  open Aegis.CountPyramids

  def rowOf (grid : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
    match grid.val[i]? with
    | some v => v.val
    | none => []

  def cell (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    (rowOf grid i).getD j 0

  def PyramidPlot (grid : Slice (alloc.vec.Vec Std.I64)) (m n a b h : Nat) : Prop :=
    a < m ∧ b < n ∧ 2 ≤ h ∧ a + (h - 1) < m ∧ h - 1 ≤ b ∧ b + (h - 1) < n ∧
      ∀ i j, a ≤ i → i ≤ a + (h - 1) → b - (i - a) ≤ j → j ≤ b + (i - a) →
        cell grid i j = 1

  def InvPyramidPlot (grid : Slice (alloc.vec.Vec Std.I64)) (m n a b h : Nat) : Prop :=
    a < m ∧ b < n ∧ 2 ≤ h ∧ h - 1 ≤ a ∧ h - 1 ≤ b ∧ b + (h - 1) < n ∧
      ∀ i j, a - (h - 1) ≤ i → i ≤ a → b - (a - i) ≤ j → j ≤ b + (a - i) →
        cell grid i j = 1

  noncomputable def countTriples (m n H : Nat) (P : Nat → Nat → Nat → Prop) : Int :=
    (((Finset.range m).product ((Finset.range n).product (Finset.range H))).filter
      (fun t => P t.1 t.2.1 t.2.2)).card

  noncomputable def numPyramidPlots (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Int :=
    countTriples m n (m + 1) (fun a b h => PyramidPlot grid m n a b h)

  noncomputable def numInvPyramidPlots (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Int :=
    countTriples m n (m + 1) (fun a b h => InvPyramidPlot grid m n a b h)

  def heightCap (m n : Nat) : Nat :=
    min m ((n + 1) / 2)

  noncomputable def U (m n : Nat) : Int :=
    2 * ∑ h ∈ Finset.Icc 2 (heightCap m n),
      (((m : Int) - (h : Int) + 1) * ((n : Int) - 2 * (h : Int) + 2))

  noncomputable def N2P (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Int :=
    (((Finset.range (m - 1)).product (Finset.Icc 1 (n - 2))).filter
      (fun q => cell grid q.1 q.2 = 1 ∧ cell grid (q.1 + 1) (q.2 - 1) = 1 ∧
        cell grid (q.1 + 1) q.2 = 1 ∧ cell grid (q.1 + 1) (q.2 + 1) = 1)).card

  noncomputable def N2I (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Int :=
    (((Finset.range (m - 1)).product (Finset.Icc 1 (n - 2))).filter
      (fun q => cell grid q.1 (q.2 - 1) = 1 ∧ cell grid q.1 q.2 = 1 ∧
        cell grid q.1 (q.2 + 1) = 1 ∧ cell grid (q.1 + 1) q.2 = 1)).card

  /-- Whenever the function returns a result r, r equals the following number. A pyramid plot is a triple (a,b,h) of integers with 0 <= a < m, 0 <= b < n, h >= 2, a+h-1 < m, b-(h-1) >= 0, b+(h-1) < n, and grid[i][j] = 1 for every i,j with a <= i <= a+h-1 and b-(i-a) <= j <= b+(i-a). An inverse pyramid plot is a triple (a,b,h) with 0 <= a < m, 0 <= b < n, h >= 2, a-h+1 >= 0, b-(h-1) >= 0, b+(h-1) < n, and grid[i][j] = 1 for every i,j with a-h+1 <= i <= a and b-(a-i) <= j <= b+(a-i). Then r is the number of pyramid plots plus the number of inverse pyramid plots.
    Preconditions: Let m = len(grid). Assume grid is rectangular: there is an integer n >= 1 such that len(grid[i]) = n for every i with 0 <= i < m. Assume 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and grid[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrect : ∀ i, i < m → (rowOf grid i).length = n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1) :
      ∀ r, count_pyramids grid = ok r →
        r.val = numPyramidPlots grid m n + numInvPyramidPlots grid m n := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrect : ∀ i, i < m → (rowOf grid i).length = n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1), ∀ r, count_pyramids grid = ok r →
          r.val = numPyramidPlots grid m n + numInvPyramidPlots grid m n) := by
    sorry

  /-- The function returns a result r for every admissible grid; it does not panic, access an out-of-bounds index, or overflow i64 while computing r.
    Preconditions: Let m = len(grid). Assume grid is rectangular with common row length n, 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and every grid[i][j] is 0 or 1. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrect : ∀ i, i < m → (rowOf grid i).length = n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1) :
      ∃ r, count_pyramids grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrect : ∀ i, i < m → (rowOf grid i).length = n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1), ∃ r, count_pyramids grid = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: Let m = len(grid). Assume grid is rectangular with common row length n, 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and every grid[i][j] is 0 or 1. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrect : ∀ i, i < m → (rowOf grid i).length = n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1) :
      ∀ r, count_pyramids grid = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrect : ∀ i, i < m → (rowOf grid i).length = n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1), ∀ r, count_pyramids grid = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= U(m,n), where U(m,n) = 2 * sum for h from 2 to H of (m-h+1)*(n-2h+2), with H = min(m, (n+1) div 2) and with the sum equal to 0 when H < 2. Here div is integer division. The number U(m,n) counts all pyramid and inverse-pyramid shapes of height at least 2 that fit entirely in an m by n grid, ignoring whether their cells are fertile.
    Preconditions: Let m = len(grid). Assume grid is rectangular with common row length n, 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and every grid[i][j] is 0 or 1. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrect : ∀ i, i < m → (rowOf grid i).length = n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1) :
      ∀ r, count_pyramids grid = ok r → r.val ≤ U m n := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrect : ∀ i, i < m → (rowOf grid i).length = n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1), ∀ r, count_pyramids grid = ok r → r.val ≤ U m n) := by
    sorry

  /-- Let r1 be the result returned for grid and r2 the result returned for grid2. Then r1 <= r2.
    Preconditions: Let grid and grid2 be two admissible grids with the same number of rows m and columns n, and assume grid[i][j] <= grid2[i][j] for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_5 (grid grid2 : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrect : ∀ i, i < m → (rowOf grid i).length = n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
      (hm' : grid2.val.length = m)
      (hrect' : ∀ i, i < m → (rowOf grid2 i).length = n)
      (hbin' : ∀ i j, i < m → j < n → cell grid2 i j = 0 ∨ cell grid2 i j = 1)
      (hle : ∀ i j, i < m → j < n → cell grid i j ≤ cell grid2 i j) :
      ∀ r1 r2, count_pyramids grid = ok r1 → count_pyramids grid2 = ok r2 → r1.val ≤ r2.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid grid2 : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrect : ∀ i, i < m → (rowOf grid i).length = n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
        (hm' : grid2.val.length = m)
        (hrect' : ∀ i, i < m → (rowOf grid2 i).length = n)
        (hbin' : ∀ i j, i < m → j < n → cell grid2 i j = 0 ∨ cell grid2 i j = 1)
        (hle : ∀ i j, i < m → j < n → cell grid i j ≤ cell grid2 i j), ∀ r1 r2, count_pyramids grid = ok r1 → count_pyramids grid2 = ok r2 → r1.val ≤ r2.val) := by
    sorry

  /-- The result returned for grid2 equals the result returned for grid.
    Preconditions: Let grid be admissible with m rows and n columns. Let grid2 be the m-by-n grid defined by grid2[i][j] = grid[i][n-1-j] for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_6 (grid grid2 : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrect : ∀ i, i < m → (rowOf grid i).length = n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
      (hm' : grid2.val.length = m)
      (hrect' : ∀ i, i < m → (rowOf grid2 i).length = n)
      (hflip : ∀ i j, i < m → j < n → cell grid2 i j = cell grid i (n - 1 - j)) :
      ∀ r1 r2, count_pyramids grid = ok r1 → count_pyramids grid2 = ok r2 → r1.val = r2.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid grid2 : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrect : ∀ i, i < m → (rowOf grid i).length = n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
        (hm' : grid2.val.length = m)
        (hrect' : ∀ i, i < m → (rowOf grid2 i).length = n)
        (hflip : ∀ i j, i < m → j < n → cell grid2 i j = cell grid i (n - 1 - j)), ∀ r1 r2, count_pyramids grid = ok r1 → count_pyramids grid2 = ok r2 → r1.val = r2.val) := by
    sorry

  /-- If m < 2 or n < 3, then the function returns 0.
    Preconditions: Let m = len(grid). Assume grid is rectangular with common row length n, 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and every grid[i][j] is 0 or 1. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrect : ∀ i, i < m → (rowOf grid i).length = n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
      (hsmall : m < 2 ∨ n < 3) :
      ∀ r, count_pyramids grid = ok r → r.val = 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrect : ∀ i, i < m → (rowOf grid i).length = n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
        (hsmall : m < 2 ∨ n < 3), ∀ r, count_pyramids grid = ok r → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, there exist integers i,j such that 0 <= i < m-1 and 1 <= j < n-1, and either (1) grid[i][j] = 1, grid[i+1][j-1] = 1, grid[i+1][j] = 1, grid[i+1][j+1] = 1, or (2) grid[i][j-1] = 1, grid[i][j] = 1, grid[i][j+1] = 1, grid[i+1][j] = 1.
    Preconditions: Let m = len(grid). Assume grid is rectangular with common row length n, 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and every grid[i][j] is 0 or 1. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrect : ∀ i, i < m → (rowOf grid i).length = n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1) :
      ∀ r, count_pyramids grid = ok r → 0 < r.val →
        ∃ i j, i < m - 1 ∧ 1 ≤ j ∧ j < n - 1 ∧
          ((cell grid i j = 1 ∧ cell grid (i + 1) (j - 1) = 1 ∧
              cell grid (i + 1) j = 1 ∧ cell grid (i + 1) (j + 1) = 1) ∨
            (cell grid i (j - 1) = 1 ∧ cell grid i j = 1 ∧
              cell grid i (j + 1) = 1 ∧ cell grid (i + 1) j = 1)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrect : ∀ i, i < m → (rowOf grid i).length = n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1), ∀ r, count_pyramids grid = ok r → 0 < r.val →
          ∃ i j, i < m - 1 ∧ 1 ≤ j ∧ j < n - 1 ∧
            ((cell grid i j = 1 ∧ cell grid (i + 1) (j - 1) = 1 ∧
                cell grid (i + 1) j = 1 ∧ cell grid (i + 1) (j + 1) = 1) ∨
              (cell grid i (j - 1) = 1 ∧ cell grid i j = 1 ∧
                cell grid i (j + 1) = 1 ∧ cell grid (i + 1) j = 1))) := by
    sorry

  /-- Let N2P be the number of pairs (i,j) with 0 <= i < m-1 and 1 <= j < n-1 such that grid[i][j] = 1, grid[i+1][j-1] = 1, grid[i+1][j] = 1, and grid[i+1][j+1] = 1. Let N2I be the number of pairs (i,j) with 0 <= i < m-1 and 1 <= j < n-1 such that grid[i][j-1] = 1, grid[i][j] = 1, grid[i][j+1] = 1, and grid[i+1][j] = 1. Whenever the function returns a result r, r >= N2P + N2I.
    Preconditions: Let m = len(grid). Assume grid is rectangular with common row length n, 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and every grid[i][j] is 0 or 1. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrect : ∀ i, i < m → (rowOf grid i).length = n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1) :
      ∀ r, count_pyramids grid = ok r → N2P grid m n + N2I grid m n ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrect : ∀ i, i < m → (rowOf grid i).length = n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1), ∀ r, count_pyramids grid = ok r → N2P grid m n + N2I grid m n ≤ r.val) := by
    sorry

  /-- The function returns 0.
    Preconditions: Let m = len(grid). Assume grid is rectangular with common row length n, 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and every grid[i][j] is 0 or 1. Assume that for every row i and every j with 0 <= i < m and 0 <= j < n-2, it is not the case that grid[i][j] = 1, grid[i][j+1] = 1, and grid[i][j+2] = 1. -/
  theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrect : ∀ i, i < m → (rowOf grid i).length = n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
      (hno3 : ∀ i j, i < m → j < n - 2 →
        ¬ (cell grid i j = 1 ∧ cell grid i (j + 1) = 1 ∧ cell grid i (j + 2) = 1)) :
      ∀ r, count_pyramids grid = ok r → r.val = 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrect : ∀ i, i < m → (rowOf grid i).length = n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
        (hno3 : ∀ i j, i < m → j < n - 2 →
          ¬ (cell grid i j = 1 ∧ cell grid i (j + 1) = 1 ∧ cell grid i (j + 2) = 1)), ∀ r, count_pyramids grid = ok r → r.val = 0) := by
    sorry

  end AegisSpec.CountPyramids
