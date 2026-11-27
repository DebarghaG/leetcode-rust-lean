import Aegis.CountSubmatrices.Code.Funs

/-!
# Specifications of `Aegis.CountSubmatrices.count_submatrices`

LeetCode problem `find-sorted-submatrices-with-maximum-element-at-most-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountSubmatrices

  namespace AegisSpec.CountSubmatrices

  def gridRows (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    grid.val.map (fun row => row.val.map (fun x => x.val))

  def rowAt (grid : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
    (gridRows grid).getD i []

  def entry (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    (rowAt grid i).getD j 0

  def mOf (grid : Slice (alloc.vec.Vec Std.I64)) : Nat := grid.val.length

  def nOf (grid : Slice (alloc.vec.Vec Std.I64)) : Nat := (rowAt grid 0).length

  def HasShape (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
    mOf grid = m ∧ ∀ i, i < m → (rowAt grid i).length = n

  def EntriesInRange (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
    ∀ i, i < m → ∀ j, j < n → 1 ≤ entry grid i j ∧ entry grid i j ≤ 10 ^ 9

  def ValidGrid (grid : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    1 ≤ mOf grid ∧ mOf grid ≤ 1000 ∧
      1 ≤ nOf grid ∧ nOf grid ≤ 1000 ∧
        HasShape grid (mOf grid) (nOf grid) ∧ EntriesInRange grid (mOf grid) (nOf grid)

  def ValidK (k : Std.I64) : Prop := 1 ≤ k.val ∧ k.val ≤ 10 ^ 9

  def ValidInput (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) : Prop :=
    ValidGrid grid ∧ ValidK k

  def allQuads (m n : Nat) : Finset (Nat × Nat × Nat × Nat) :=
    (Finset.range m) ×ˢ (Finset.range m) ×ˢ (Finset.range n) ×ˢ (Finset.range n)

  def allPairs (len : Nat) : Finset (Nat × Nat) :=
    (Finset.range len) ×ˢ (Finset.range len)

  noncomputable def countQuads (m n : Nat) (P : Nat → Nat → Nat → Nat → Prop) : Nat := by
    classical
    exact ((allQuads m n).filter (fun q => P q.1 q.2.1 q.2.2.1 q.2.2.2)).card

  noncomputable def countPairs (len : Nat) (P : Nat → Nat → Prop) : Nat := by
    classical
    exact ((allPairs len).filter (fun q => P q.1 q.2)).card

  noncomputable def countEntriesLe
      (grid : Slice (alloc.vec.Vec Std.I64)) (k : Int) (m n : Nat) : Nat := by
    classical
    exact (((Finset.range m) ×ˢ (Finset.range n)).filter
      (fun p => entry grid p.1 p.2 ≤ k)).card

  def maxCount (m n : Nat) : Nat := (m * (m + 1) / 2) * (n * (n + 1) / 2)

  def RectLe (grid : Slice (alloc.vec.Vec Std.I64)) (k : Int)
      (x1 x2 y1 y2 : Nat) : Prop :=
    ∀ i, x1 ≤ i → i ≤ x2 → ∀ j, y1 ≤ j → j ≤ y2 → entry grid i j ≤ k

  def RectNonIncr (grid : Slice (alloc.vec.Vec Std.I64))
      (x1 x2 y1 y2 : Nat) : Prop :=
    ∀ i, x1 ≤ i → i ≤ x2 → ∀ j, y1 ≤ j → j < y2 → entry grid i (j + 1) ≤ entry grid i j

  def RowsNonIncr (grid : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ i, i < mOf grid → ∀ j, j < nOf grid - 1 → entry grid i (j + 1) ≤ entry grid i j

  /-- The function returns a result r and r equals the number of quadruples (x1, x2, y1, y2) of integers such that 0 <= x1 <= x2 < m, 0 <= y1 <= y2 < n, for every i with x1 <= i <= x2 and every j with y1 <= j <= y2 we have grid[i][j] <= k, and for every i with x1 <= i <= x2 and every j with y1 <= j < y2 we have grid[i][j] >= grid[i][j+1]. Each such quadruple represents exactly one nonempty contiguous submatrix; empty submatrices are not counted.
    Preconditions: Let m = len(grid) and n = len(grid[0]). We assume 1 <= m <= 1000, 1 <= n <= 1000, every row grid[i] has length n, for every 0 <= i < m and 0 <= j < n we have 1 <= grid[i][j] <= 10^9, and 1 <= k <= 10^9. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (h : ValidInput grid k) :
      ∃ r, count_submatrices grid k = .ok r ∧
        r.val = ((countQuads (mOf grid) (nOf grid) (fun x1 x2 y1 y2 =>
          x1 ≤ x2 ∧ y1 ≤ y2 ∧ RectLe grid k.val x1 x2 y1 y2 ∧
            RectNonIncr grid x1 x2 y1 y2) : Nat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (h : ValidInput grid k), ∃ r, count_submatrices grid k = Result.ok r ∧
          r.val = ((countQuads (mOf grid) (nOf grid) (fun x1 x2 y1 y2 =>
            x1 ≤ x2 ∧ y1 ≤ y2 ∧ RectLe grid k.val x1 x2 y1 y2 ∧
              RectNonIncr grid x1 x2 y1 y2) : Nat) : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, go out of bounds, or overflow.
    Preconditions: Let m = len(grid) and n = len(grid[0]). We assume 1 <= m <= 1000, 1 <= n <= 1000, every row grid[i] has length n, for every 0 <= i < m and 0 <= j < n we have 1 <= grid[i][j] <= 10^9, and 1 <= k <= 10^9. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (h : ValidInput grid k) :
      ∃ r, count_submatrices grid k = .ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (h : ValidInput grid k), ∃ r, count_submatrices grid k = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, we have 0 <= r <= (m*(m+1)/2) * (n*(n+1)/2).
    Preconditions: Let m = len(grid) and n = len(grid[0]). We assume 1 <= m <= 1000, 1 <= n <= 1000, every row grid[i] has length n, for every 0 <= i < m and 0 <= j < n we have 1 <= grid[i][j] <= 10^9, and 1 <= k <= 10^9. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (h : ValidInput grid k) :
      ∀ r, count_submatrices grid k = .ok r →
        0 ≤ r.val ∧ r.val ≤ ((maxCount (mOf grid) (nOf grid) : Nat) : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (h : ValidInput grid k), ∀ r, count_submatrices grid k = Result.ok r →
          0 ≤ r.val ∧ r.val ≤ ((maxCount (mOf grid) (nOf grid) : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, let N be the number of pairs (i, j) with 0 <= i < m and 0 <= j < n such that grid[i][j] <= k. Then r >= N.
    Preconditions: Let m = len(grid) and n = len(grid[0]). We assume 1 <= m <= 1000, 1 <= n <= 1000, every row grid[i] has length n, for every 0 <= i < m and 0 <= j < n we have 1 <= grid[i][j] <= 10^9, and 1 <= k <= 10^9. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (h : ValidInput grid k) :
      ∀ r, count_submatrices grid k = .ok r →
        ((countEntriesLe grid k.val (mOf grid) (nOf grid) : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (h : ValidInput grid k), ∀ r, count_submatrices grid k = Result.ok r →
          ((countEntriesLe grid k.val (mOf grid) (nOf grid) : Nat) : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, if for every 0 <= i < m and 0 <= j < n we have grid[i][j] > k, then r = 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). We assume 1 <= m <= 1000, 1 <= n <= 1000, every row grid[i] has length n, for every 0 <= i < m and 0 <= j < n we have 1 <= grid[i][j] <= 10^9, and 1 <= k <= 10^9. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (h : ValidInput grid k)
      (hall : ∀ i, i < mOf grid → ∀ j, j < nOf grid → k.val < entry grid i j) :
      ∀ r, count_submatrices grid k = .ok r → r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (h : ValidInput grid k)
        (hall : ∀ i, i < mOf grid → ∀ j, j < nOf grid → k.val < entry grid i j), ∀ r, count_submatrices grid k = Result.ok r → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, if n = 1, then r equals the number of pairs (x1, x2) with 0 <= x1 <= x2 < m such that for every i with x1 <= i <= x2 we have grid[i][0] <= k.
    Preconditions: Let m = len(grid) and n = len(grid[0]). We assume 1 <= m <= 1000, 1 <= n <= 1000, every row grid[i] has length n, for every 0 <= i < m and 0 <= j < n we have 1 <= grid[i][j] <= 10^9, and 1 <= k <= 10^9. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (h : ValidInput grid k) (hn : nOf grid = 1) :
      ∀ r, count_submatrices grid k = .ok r →
        r.val = ((countPairs (mOf grid) (fun x1 x2 =>
          x1 ≤ x2 ∧ ∀ i, x1 ≤ i → i ≤ x2 → entry grid i 0 ≤ k.val) : Nat) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (h : ValidInput grid k) (hn : nOf grid = 1), ∀ r, count_submatrices grid k = Result.ok r →
          r.val = ((countPairs (mOf grid) (fun x1 x2 =>
            x1 ≤ x2 ∧ ∀ i, x1 ≤ i → i ≤ x2 → entry grid i 0 ≤ k.val) : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, if m = 1, then r equals the number of pairs (y1, y2) with 0 <= y1 <= y2 < n such that (1) for every j with y1 <= j <= y2 we have grid[0][j] <= k, and (2) for every j with y1 <= j < y2 we have grid[0][j] >= grid[0][j+1].
    Preconditions: Let m = len(grid) and n = len(grid[0]). We assume 1 <= m <= 1000, 1 <= n <= 1000, every row grid[i] has length n, for every 0 <= i < m and 0 <= j < n we have 1 <= grid[i][j] <= 10^9, and 1 <= k <= 10^9. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (h : ValidInput grid k) (hm : mOf grid = 1) :
      ∀ r, count_submatrices grid k = .ok r →
        r.val = ((countPairs (nOf grid) (fun y1 y2 =>
          y1 ≤ y2 ∧ RectLe grid k.val 0 0 y1 y2 ∧
            RectNonIncr grid 0 0 y1 y2) : Nat) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (h : ValidInput grid k) (hm : mOf grid = 1), ∀ r, count_submatrices grid k = Result.ok r →
          r.val = ((countPairs (nOf grid) (fun y1 y2 =>
            y1 ≤ y2 ∧ RectLe grid k.val 0 0 y1 y2 ∧
              RectNonIncr grid 0 0 y1 y2) : Nat) : Int)) := by
    sorry

  /-- If count_submatrices(grid, k1) returns r1 and count_submatrices(grid, k2) returns r2, then r1 <= r2.
    Preconditions: Let grid satisfy the grid constraints: 1 <= len(grid) <= 1000, every row has a common length n with 1 <= n <= 1000, and every entry grid[i][j] satisfies 1 <= grid[i][j] <= 10^9. Let k1 and k2 be integers with 1 <= k1 <= k2 <= 10^9. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (k1 k2 : Std.I64)
      (hg : ValidGrid grid)
      (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 10 ^ 9) :
      ∀ r1 r2, count_submatrices grid k1 = .ok r1 →
        count_submatrices grid k2 = .ok r2 → r1.val ≤ r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k1 k2 : Std.I64)
        (hg : ValidGrid grid)
        (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 10 ^ 9), ∀ r1 r2, count_submatrices grid k1 = Result.ok r1 →
          count_submatrices grid k2 = Result.ok r2 → r1.val ≤ r2.val) := by
    sorry

  /-- Whenever the function returns a result r, if k is at least every entry of grid, then r equals the number of quadruples (x1, x2, y1, y2) with 0 <= x1 <= x2 < m, 0 <= y1 <= y2 < n, and for every i with x1 <= i <= x2 and every j with y1 <= j < y2 we have grid[i][j] >= grid[i][j+1].
    Preconditions: Let m = len(grid) and n = len(grid[0]). We assume 1 <= m <= 1000, 1 <= n <= 1000, every row grid[i] has length n, for every 0 <= i < m and 0 <= j < n we have 1 <= grid[i][j] <= 10^9, and 1 <= k <= 10^9. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (h : ValidInput grid k)
      (hk : ∀ i, i < mOf grid → ∀ j, j < nOf grid → entry grid i j ≤ k.val) :
      ∀ r, count_submatrices grid k = .ok r →
        r.val = ((countQuads (mOf grid) (nOf grid) (fun x1 x2 y1 y2 =>
          x1 ≤ x2 ∧ y1 ≤ y2 ∧ RectNonIncr grid x1 x2 y1 y2) : Nat) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (h : ValidInput grid k)
        (hk : ∀ i, i < mOf grid → ∀ j, j < nOf grid → entry grid i j ≤ k.val), ∀ r, count_submatrices grid k = Result.ok r →
          r.val = ((countQuads (mOf grid) (nOf grid) (fun x1 x2 y1 y2 =>
            x1 ≤ x2 ∧ y1 ≤ y2 ∧ RectNonIncr grid x1 x2 y1 y2) : Nat) : Int)) := by
    sorry

  /-- If count_submatrices(grid, k) returns r and count_submatrices(grid', k) returns r', then r = r'.
    Preconditions: Let grid and grid' be two inputs satisfying the grid constraints with the same m and n, and suppose every entry of both grids is at most k, where 1 <= k <= 10^9. Suppose also that for every i with 0 <= i < m and every j with 0 <= j < n-1, grid[i][j] >= grid[i][j+1] if and only if grid'[i][j] >= grid'[i][j+1]. -/
  theorem spec_10 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (k : Std.I64)
      (hshape : HasShape grid m n) (hshape' : HasShape grid' m n)
      (hm : 1 ≤ m ∧ m ≤ 1000) (hn : 1 ≤ n ∧ n ≤ 1000)
      (hrange : EntriesInRange grid m n) (hrange' : EntriesInRange grid' m n)
      (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
      (hle : ∀ i, i < m → ∀ j, j < n →
        entry grid i j ≤ k.val ∧ entry grid' i j ≤ k.val)
      (hmono : ∀ i, i < m → ∀ j, j < n - 1 →
        (entry grid i (j + 1) ≤ entry grid i j ↔
          entry grid' i (j + 1) ≤ entry grid' i j)) :
      ∀ r r', count_submatrices grid k = .ok r →
        count_submatrices grid' k = .ok r' → r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (k : Std.I64)
        (hshape : HasShape grid m n) (hshape' : HasShape grid' m n)
        (hm : 1 ≤ m ∧ m ≤ 1000) (hn : 1 ≤ n ∧ n ≤ 1000)
        (hrange : EntriesInRange grid m n) (hrange' : EntriesInRange grid' m n)
        (hk : 1 ≤ k.val ∧ k.val ≤ 10 ^ 9)
        (hle : ∀ i, i < m → ∀ j, j < n →
          entry grid i j ≤ k.val ∧ entry grid' i j ≤ k.val)
        (hmono : ∀ i, i < m → ∀ j, j < n - 1 →
          (entry grid i (j + 1) ≤ entry grid i j ↔
            entry grid' i (j + 1) ≤ entry grid' i j)), ∀ r r', count_submatrices grid k = Result.ok r →
          count_submatrices grid' k = Result.ok r' → r = r') := by
    sorry

  /-- Whenever the function returns a result r, if every row is non-increasing, meaning for every 0 <= i < m and every 0 <= j < n-1 we have grid[i][j] >= grid[i][j+1], then r equals the number of quadruples (x1, x2, y1, y2) with 0 <= x1 <= x2 < m, 0 <= y1 <= y2 < n, and for every i with x1 <= i <= x2 and every j with y1 <= j <= y2 we have grid[i][j] <= k.
    Preconditions: Let m = len(grid) and n = len(grid[0]). We assume 1 <= m <= 1000, 1 <= n <= 1000, every row grid[i] has length n, for every 0 <= i < m and 0 <= j < n we have 1 <= grid[i][j] <= 10^9, and 1 <= k <= 10^9. -/
  theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (h : ValidInput grid k) (hnonincr : RowsNonIncr grid) :
      ∀ r, count_submatrices grid k = .ok r →
        r.val = ((countQuads (mOf grid) (nOf grid) (fun x1 x2 y1 y2 =>
          x1 ≤ x2 ∧ y1 ≤ y2 ∧ RectLe grid k.val x1 x2 y1 y2) : Nat) : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (h : ValidInput grid k) (hnonincr : RowsNonIncr grid), ∀ r, count_submatrices grid k = Result.ok r →
          r.val = ((countQuads (mOf grid) (nOf grid) (fun x1 x2 y1 y2 =>
            x1 ≤ x2 ∧ y1 ≤ y2 ∧ RectLe grid k.val x1 x2 y1 y2) : Nat) : Int)) := by
    sorry

  end AegisSpec.CountSubmatrices
