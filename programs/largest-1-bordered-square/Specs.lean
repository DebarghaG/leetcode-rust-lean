import Aegis.Largest1BorderedSquare.Code.Funs

/-!
# Specifications of `Aegis.Largest1BorderedSquare.largest1_bordered_square`

LeetCode problem `largest-1-bordered-square`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.Largest1BorderedSquare

  open Classical Aegis.Largest1BorderedSquare

  def rowAt (grid : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : Option (alloc.vec.Vec Std.I64) :=
    grid.val[i]?

  def cell (grid : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : Option ℤ :=
    (rowAt grid i).bind (fun row => (row.val[j]?).map (fun x => x.val))

  def rowLen (grid : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : Option ℕ :=
    (rowAt grid i).map (fun row => row.val.length)

  def Bordered (grid : Slice (alloc.vec.Vec Std.I64)) (k a b : ℕ) : Prop :=
    0 < k ∧
      (∀ t, t < k → cell grid a (b + t) = some 1) ∧
      (∀ t, t < k → cell grid (a + k - 1) (b + t) = some 1) ∧
      (∀ t, t < k → cell grid (a + t) b = some 1) ∧
      (∀ t, t < k → cell grid (a + t) (b + k - 1) = some 1)

  def HasBorderedSquare (grid : Slice (alloc.vec.Vec Std.I64)) (m n k : ℕ) : Prop :=
    1 ≤ k ∧ k ≤ min m n ∧ ∃ a b, a ≤ m - k ∧ b ≤ n - k ∧ Bordered grid k a b

  noncomputable def largestArea (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) : ℕ :=
    (Finset.range (min m n + 1)).sup
      (fun k => if HasBorderedSquare grid m n k then k * k else 0)

  def HasRowRun (grid : Slice (alloc.vec.Vec Std.I64)) (m n k : ℕ) : Prop :=
    ∃ i j, i < m ∧ j + k ≤ n ∧ ∀ t, t < k → cell grid i (j + t) = some 1

  def HasColRun (grid : Slice (alloc.vec.Vec Std.I64)) (m n k : ℕ) : Prop :=
    ∃ i j, i + k ≤ m ∧ j < n ∧ ∀ t, t < k → cell grid (i + t) j = some 1

  /-- The function returns a result r and r = max( {0} union { k*k | k is an integer with 1 <= k <= min(m,n) and there exist integers a,b with 0 <= a <= m-k and 0 <= b <= n-k such that, for every integer t with 0 <= t < k, grid[a][b+t] = 1 and grid[a+k-1][b+t] = 1 and grid[a+t][b] = 1 and grid[a+t][b+k-1] = 1 } ). Thus r is the largest area, side length squared, of a contiguous axis-aligned square subgrid whose four sides are all 1, and r = 0 if no such square exists.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 100, every row of grid has length n, 1 <= n <= 100, and grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
      (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
      (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1) :
      ∃ r, largest1_bordered_square grid = ok r ∧ r.val = ((largestArea grid m n : ℕ) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
        (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
        (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1), ∃ r, largest1_bordered_square grid = ok r ∧ r.val = ((largestArea grid m n : ℕ) : ℤ)) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, return an error, or overflow for any grid satisfying the preconditions.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 100, every row of grid has length n, 1 <= n <= 100, and grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
      (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
      (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1) :
      ∃ r, largest1_bordered_square grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
        (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
        (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1), ∃ r, largest1_bordered_square grid = ok r) := by
    sorry

  /-- The function returns a result r and 0 <= r <= (min(m,n))*(min(m,n)).
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 100, every row of grid has length n, 1 <= n <= 100, and grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
      (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
      (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1) :
      ∃ r, largest1_bordered_square grid = ok r ∧
        0 ≤ r.val ∧ r.val ≤ ((min m n * min m n : ℕ) : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
        (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
        (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1), ∃ r, largest1_bordered_square grid = ok r ∧
          0 ≤ r.val ∧ r.val ≤ ((min m n * min m n : ℕ) : ℤ)) := by
    sorry

  /-- The function returns a result r and either r = 0 or there exists an integer k with 1 <= k <= min(m,n) such that r = k*k.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 100, every row of grid has length n, 1 <= n <= 100, and grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
      (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
      (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1) :
      ∃ r, largest1_bordered_square grid = ok r ∧
        (r.val = 0 ∨ ∃ k, 1 ≤ k ∧ k ≤ min m n ∧ r.val = ((k * k : ℕ) : ℤ)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
        (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
        (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1), ∃ r, largest1_bordered_square grid = ok r ∧
          (r.val = 0 ∨ ∃ k, 1 ≤ k ∧ k ≤ min m n ∧ r.val = ((k * k : ℕ) : ℤ))) := by
    sorry

  /-- The function returns a result r and r = 0 if and only if grid[i][j] = 0 for every 0 <= i < m and 0 <= j < n.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 100, every row of grid has length n, 1 <= n <= 100, and grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
      (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
      (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1) :
      ∃ r, largest1_bordered_square grid = ok r ∧
        (r.val = 0 ↔ ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
        (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
        (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1), ∃ r, largest1_bordered_square grid = ok r ∧
          (r.val = 0 ↔ ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0)) := by
    sorry

  /-- The function returns a result r and, if r > 0, there exist integers k,a,b such that 1 <= k <= min(m,n), r = k*k, 0 <= a <= m-k, 0 <= b <= n-k, and for every integer t with 0 <= t < k, grid[a][b+t] = 1 and grid[a+k-1][b+t] = 1 and grid[a+t][b] = 1 and grid[a+t][b+k-1] = 1.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 100, every row of grid has length n, 1 <= n <= 100, and grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
      (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
      (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1) :
      ∃ r, largest1_bordered_square grid = ok r ∧
        (0 < r.val → ∃ k a b, 1 ≤ k ∧ k ≤ min m n ∧ r.val = ((k * k : ℕ) : ℤ) ∧
          a ≤ m - k ∧ b ≤ n - k ∧ Bordered grid k a b) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
        (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
        (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1), ∃ r, largest1_bordered_square grid = ok r ∧
          (0 < r.val → ∃ k a b, 1 ≤ k ∧ k ≤ min m n ∧ r.val = ((k * k : ℕ) : ℤ) ∧
            a ≤ m - k ∧ b ≤ n - k ∧ Bordered grid k a b)) := by
    sorry

  /-- The function returns a result r and, for all integers k,a,b with 1 <= k <= min(m,n), 0 <= a <= m-k, and 0 <= b <= n-k, if for every integer t with 0 <= t < k we have grid[a][b+t] = 1 and grid[a+k-1][b+t] = 1 and grid[a+t][b] = 1 and grid[a+t][b+k-1] = 1, then k*k <= r.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 100, every row of grid has length n, 1 <= n <= 100, and grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
      (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
      (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1) :
      ∃ r, largest1_bordered_square grid = ok r ∧
        ∀ k a b, 1 ≤ k → k ≤ min m n → a ≤ m - k → b ≤ n - k →
          Bordered grid k a b → ((k * k : ℕ) : ℤ) ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
        (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
        (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1), ∃ r, largest1_bordered_square grid = ok r ∧
          ∀ k a b, 1 ≤ k → k ≤ min m n → a ≤ m - k → b ≤ n - k →
            Bordered grid k a b → ((k * k : ℕ) : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns a result r and r = (min(m,n))*(min(m,n)).
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 100, every row of grid has length n, 1 <= n <= 100, and grid[i][j] = 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
      (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
      (hones : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 1) :
      ∃ r, largest1_bordered_square grid = ok r ∧ r.val = ((min m n * min m n : ℕ) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
        (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
        (hones : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 1), ∃ r, largest1_bordered_square grid = ok r ∧ r.val = ((min m n * min m n : ℕ) : ℤ)) := by
    sorry

  /-- The function returns a result r and r = 1 if there exist integers i,j with 0 <= i < m and 0 <= j < n such that grid[i][j] = 1; otherwise r = 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 100, every row of grid has length n, 1 <= n <= 100, grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n, and m = 1 or n = 1. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
      (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
      (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1)
      (hthin : m = 1 ∨ n = 1) :
      ∃ r, largest1_bordered_square grid = ok r ∧
        r.val = if (∃ i, i < m ∧ ∃ j, j < n ∧ cell grid i j = some 1) then 1 else 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
        (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
        (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1)
        (hthin : m = 1 ∨ n = 1), ∃ r, largest1_bordered_square grid = ok r ∧
          r.val = if (∃ i, i < m ∧ ∃ j, j < n ∧ cell grid i j = some 1) then 1 else 0) := by
    sorry

  /-- The function returns a result r and, if there exist integers a,b with 0 <= a <= m-min(m,n) and 0 <= b <= n-min(m,n) such that for every integer t with 0 <= t < min(m,n), grid[a][b+t] = 1 and grid[a+min(m,n)-1][b+t] = 1 and grid[a+t][b] = 1 and grid[a+t][b+min(m,n)-1] = 1, then r = (min(m,n))*(min(m,n)).
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 100, every row of grid has length n, 1 <= n <= 100, and grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
      (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
      (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1) :
      ∃ r, largest1_bordered_square grid = ok r ∧
        ((∃ a b, a ≤ m - min m n ∧ b ≤ n - min m n ∧ Bordered grid (min m n) a b) →
          r.val = ((min m n * min m n : ℕ) : ℤ)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
        (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
        (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1), ∃ r, largest1_bordered_square grid = ok r ∧
          ((∃ a b, a ≤ m - min m n ∧ b ≤ n - min m n ∧ Bordered grid (min m n) a b) →
            r.val = ((min m n * min m n : ℕ) : ℤ))) := by
    sorry

  /-- The function returns a result r and r = 1 if and only if (there exist integers i,j with 0 <= i < m and 0 <= j < n such that grid[i][j] = 1) and (there do not exist integers k,a,b with 2 <= k <= min(m,n), 0 <= a <= m-k, and 0 <= b <= n-k such that for every integer t with 0 <= t < k, grid[a][b+t] = 1 and grid[a+k-1][b+t] = 1 and grid[a+t][b] = 1 and grid[a+t][b+k-1] = 1).
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 100, every row of grid has length n, 1 <= n <= 100, and grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
      (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
      (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1) :
      ∃ r, largest1_bordered_square grid = ok r ∧
        (r.val = 1 ↔
          (∃ i, i < m ∧ ∃ j, j < n ∧ cell grid i j = some 1) ∧
            ¬ (∃ k a b, 2 ≤ k ∧ k ≤ min m n ∧ a ≤ m - k ∧ b ≤ n - k ∧
                Bordered grid k a b)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
        (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
        (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1), ∃ r, largest1_bordered_square grid = ok r ∧
          (r.val = 1 ↔
            (∃ i, i < m ∧ ∃ j, j < n ∧ cell grid i j = some 1) ∧
              ¬ (∃ k a b, 2 ≤ k ∧ k ≤ min m n ∧ a ≤ m - k ∧ b ≤ n - k ∧
                  Bordered grid k a b))) := by
    sorry

  /-- The function returns a result r and, for every integer k with 1 <= k <= min(m,n), if r >= k*k then there exists a row containing k consecutive 1s and there exists a column containing k consecutive 1s.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies 1 <= m <= 100, every row of grid has length n, 1 <= n <= 100, and grid[i][j] is 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_12 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
      (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
      (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1) :
      ∃ r, largest1_bordered_square grid = ok r ∧
        ∀ k, 1 ≤ k → k ≤ min m n → ((k * k : ℕ) : ℤ) ≤ r.val →
          HasRowRun grid m n k ∧ HasColRun grid m n k := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = grid.val.length) (hm1 : 1 ≤ m) (hm100 : m ≤ 100)
        (hrow : ∀ i, i < m → rowLen grid i = some n) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
        (hbits : ∀ i, i < m → ∀ j, j < n → cell grid i j = some 0 ∨ cell grid i j = some 1), ∃ r, largest1_bordered_square grid = ok r ∧
          ∀ k, 1 ≤ k → k ≤ min m n → ((k * k : ℕ) : ℤ) ≤ r.val →
            HasRowRun grid m n k ∧ HasColRun grid m n k) := by
    sorry

  end AegisSpec.Largest1BorderedSquare
