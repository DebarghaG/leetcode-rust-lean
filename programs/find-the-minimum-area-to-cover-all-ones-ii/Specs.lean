import Aegis.MinimumSum.Code.Funs

/-!
# Specifications of `Aegis.MinimumSum.minimum_sum`

LeetCode problem `find-the-minimum-area-to-cover-all-ones-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumSum

  abbrev Grid := Slice (alloc.vec.Vec I64)

  def cells (g : Grid) : List (List ℤ) :=
    g.val.map (fun row => row.val.map (fun x => x.val))

  def cell (g : Grid) (i j : ℕ) : ℤ :=
    ((((cells g)[i]?).bind (fun row => row[j]?))).getD 0

  def IsBinaryGrid (g : Grid) (m n : ℕ) : Prop :=
    1 ≤ m ∧ m ≤ 30 ∧ 1 ≤ n ∧ n ≤ 30 ∧
      (cells g).length = m ∧
      (∀ i, i < m → ((cells g)[i]?).map List.length = some n) ∧
      (∀ i j, i < m → j < n → cell g i j = 0 ∨ cell g i j = 1)

  def onesCount (g : Grid) (m n : ℕ) : ℕ :=
    ((List.range m).map (fun i => ((List.range n).filter (fun j => cell g i j = 1)).length)).sum

  structure Rect where

    a : ℕ

    b : ℕ

    c : ℕ

    d : ℕ
  deriving DecidableEq, Repr

  def rectWF (m n : ℕ) (R : Rect) : Prop :=
    R.a ≤ R.b ∧ R.b < m ∧ R.c ≤ R.d ∧ R.d < n

  def rectArea (R : Rect) : ℕ :=
    (R.b - R.a + 1) * (R.d - R.c + 1)

  def rectMem (R : Rect) (i j : ℕ) : Prop :=
    R.a ≤ i ∧ i ≤ R.b ∧ R.c ≤ j ∧ j ≤ R.d

  def rectDisjoint (R S : Rect) : Prop :=
    ∀ i j, rectMem R i j → rectMem S i j → False

  def tripleDisjoint (R0 R1 R2 : Rect) : Prop :=
    rectDisjoint R0 R1 ∧ rectDisjoint R0 R2 ∧ rectDisjoint R1 R2

  def coversOnes (g : Grid) (m n : ℕ) (R0 R1 R2 : Rect) : Prop :=
    ∀ i j, i < m → j < n → cell g i j = 1 → rectMem R0 i j ∨ rectMem R1 i j ∨ rectMem R2 i j

  def tripleArea (R0 R1 R2 : Rect) : ℕ :=
    rectArea R0 + rectArea R1 + rectArea R2

  def ValidTriple (g : Grid) (m n : ℕ) (R0 R1 R2 : Rect) : Prop :=
    rectWF m n R0 ∧ rectWF m n R1 ∧ rectWF m n R2 ∧
      tripleDisjoint R0 R1 R2 ∧ coversOnes g m n R0 R1 R2

  def rectHasOne (g : Grid) (R : Rect) : Prop :=
    ∃ i j, rectMem R i j ∧ cell g i j = 1

  def rectTight (g : Grid) (R : Rect) : Prop :=
    (∃ j, R.c ≤ j ∧ j ≤ R.d ∧ cell g R.a j = 1) ∧
      (∃ j, R.c ≤ j ∧ j ≤ R.d ∧ cell g R.b j = 1) ∧
      (∃ i, R.a ≤ i ∧ i ≤ R.b ∧ cell g i R.c = 1) ∧
      (∃ i, R.a ≤ i ∧ i ≤ R.b ∧ cell g i R.d = 1)

  def IsBoundingBox (g : Grid) (m n rmin rmax cmin cmax : ℕ) : Prop :=
    rmin ≤ rmax ∧ cmin ≤ cmax ∧ rmax < m ∧ cmax < n ∧
      (∃ j, j < n ∧ cell g rmin j = 1) ∧
      (∃ j, j < n ∧ cell g rmax j = 1) ∧
      (∃ i, i < m ∧ cell g i cmin = 1) ∧
      (∃ i, i < m ∧ cell g i cmax = 1) ∧
      (∀ i j, i < m → j < n → cell g i j = 1 → rmin ≤ i) ∧
      (∀ i j, i < m → j < n → cell g i j = 1 → i ≤ rmax) ∧
      (∀ i j, i < m → j < n → cell g i j = 1 → cmin ≤ j) ∧
      (∀ i j, i < m → j < n → cell g i j = 1 → j ≤ cmax)

  def bboxArea (rmin rmax cmin cmax : ℕ) : ℕ :=
    (rmax - rmin + 1) * (cmax - cmin + 1)

  def transposeCells (g : Grid) (m n : ℕ) : List (List ℤ) :=
    (List.range n).map (fun j => (List.range m).map (fun i => cell g i j))

  def mirrorLRCells (g : Grid) : List (List ℤ) :=
    (cells g).map (fun row => row.reverse)

  def mirrorUDCells (g : Grid) : List (List ℤ) :=
    (cells g).reverse

  def cropCells (g : Grid) (rmin rmax cmin cmax : ℕ) : List (List ℤ) :=
    (List.range (rmax - rmin + 1)).map (fun i =>
      (List.range (cmax - cmin + 1)).map (fun j => cell g (rmin + i) (cmin + j)))

  def twoLargestSum (l : List ℕ) : ℕ :=
    let best := l.foldr max 0
    best + (l.eraseIdx (l.idxOf best)).foldr max 0

  def gaps (l : List ℕ) : List ℕ :=
    (l.zip l.tail).map (fun pq => pq.2 - pq.1 - 1)

  def edgeAnswer (l : List ℕ) : ℤ :=
    match l with
    | [] => 0
    | p0 :: _ =>
      ((l.getLast?.getD p0 : ℤ) - (p0 : ℤ) + 1) - (twoLargestSum (gaps l) : ℤ)

  /-- The function returns Result.ok r and r is the least integer S for which there exist three non-empty axis-aligned subrectangles R0, R1, R2 of the m by n grid such that: each Rq is a set of cells with row range aq..bq and column range cq..dq, where 0 <= aq <= bq < m and 0 <= cq <= dq < n; the three cell sets are pairwise disjoint; every cell (i,j) with grid[i][j] = 1 lies in R0 union R1 union R2; and S = area(R0) + area(R1) + area(R2), where area of a rectangle is (bq-aq+1)*(dq-cq+1). Equivalently, r is the minimum possible sum of the areas of three non-overlapping non-zero rectangles covering all 1s.
    Preconditions: Let m = len(grid). There exists n with 1 <= m <= 30, 1 <= n <= 30, and len(grid[i]) = n for every 0 <= i < m. For every 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. The number of pairs (i,j) with grid[i][j] = 1 is at least 3. -/
  theorem spec_1 (grid : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
      (h3 : 3 ≤ onesCount grid m n) :
      ∃ r : I64,
        Aegis.MinimumSum.minimum_sum grid = ok r ∧
          (∃ R0 R1 R2 : Rect,
            ValidTriple grid m n R0 R1 R2 ∧ (tripleArea R0 R1 R2 : ℤ) = r.val) ∧
          (∀ R0 R1 R2 : Rect,
            ValidTriple grid m n R0 R1 R2 → r.val ≤ (tripleArea R0 R1 R2 : ℤ)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
        (h3 : 3 ≤ onesCount grid m n), ∃ r : I64,
          Aegis.MinimumSum.minimum_sum grid = ok r ∧
            (∃ R0 R1 R2 : Rect,
              ValidTriple grid m n R0 R1 R2 ∧ (tripleArea R0 R1 R2 : ℤ) = r.val) ∧
            (∀ R0 R1 R2 : Rect,
              ValidTriple grid m n R0 R1 R2 → r.val ≤ (tripleArea R0 R1 R2 : ℤ))) := by
    sorry

  /-- The function returns Result.ok r for some integer r; in particular, it does not return Result.error (and hence does not fail because of out-of-bounds access or arithmetic overflow).
    Preconditions: Let m = len(grid). There exists n with 1 <= m <= 30, 1 <= n <= 30, and len(grid[i]) = n for every 0 <= i < m. For every 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. The number of pairs (i,j) with grid[i][j] = 1 is at least 3. -/
  theorem spec_2 (grid : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
      (h3 : 3 ≤ onesCount grid m n) :
      ∃ r : I64, Aegis.MinimumSum.minimum_sum grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
        (h3 : 3 ≤ onesCount grid m n), ∃ r : I64, Aegis.MinimumSum.minimum_sum grid = ok r) := by
    sorry

  /-- The function returns Result.ok r and r >= K, where K is the number of pairs (i,j) with 0 <= i < m, 0 <= j < n, and grid[i][j] = 1.
    Preconditions: Let m = len(grid). There exists n with 1 <= m <= 30, 1 <= n <= 30, and len(grid[i]) = n for every 0 <= i < m. For every 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. The number of pairs (i,j) with grid[i][j] = 1 is at least 3. -/
  theorem spec_3 (grid : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
      (h3 : 3 ≤ onesCount grid m n) :
      ∃ r : I64,
        Aegis.MinimumSum.minimum_sum grid = ok r ∧ (onesCount grid m n : ℤ) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
        (h3 : 3 ≤ onesCount grid m n), ∃ r : I64,
          Aegis.MinimumSum.minimum_sum grid = ok r ∧ (onesCount grid m n : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns Result.ok r and r <= B, where B = (rmax-rmin+1)*(cmax-cmin+1); here rmin and rmax are the minimum and maximum row indices of 1-cells, and cmin and cmax are the minimum and maximum column indices of 1-cells.
    Preconditions: Let m = len(grid). There exists n with 1 <= m <= 30, 1 <= n <= 30, and len(grid[i]) = n for every 0 <= i < m. For every 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. The number of pairs (i,j) with grid[i][j] = 1 is at least 3. -/
  theorem spec_4 (grid : Grid) (m n rmin rmax cmin cmax : ℕ) (h : IsBinaryGrid grid m n)
      (h3 : 3 ≤ onesCount grid m n) (hbox : IsBoundingBox grid m n rmin rmax cmin cmax) :
      ∃ r : I64,
        Aegis.MinimumSum.minimum_sum grid = ok r ∧
          r.val ≤ (bboxArea rmin rmax cmin cmax : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Grid) (m n rmin rmax cmin cmax : ℕ) (h : IsBinaryGrid grid m n)
        (h3 : 3 ≤ onesCount grid m n) (hbox : IsBoundingBox grid m n rmin rmax cmin cmax), ∃ r : I64,
          Aegis.MinimumSum.minimum_sum grid = ok r ∧
            r.val ≤ (bboxArea rmin rmax cmin cmax : ℤ)) := by
    sorry

  /-- The function returns Result.ok r and r = 3.
    Preconditions: Let m = len(grid). There exists n with 1 <= m <= 30, 1 <= n <= 30, and len(grid[i]) = n for every 0 <= i < m. For every 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. The number of pairs (i,j) with grid[i][j] = 1 is exactly 3. -/
  theorem spec_5 (grid : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
      (h3 : onesCount grid m n = 3) :
      ∃ r : I64, Aegis.MinimumSum.minimum_sum grid = ok r ∧ r.val = (3 : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
        (h3 : onesCount grid m n = 3), ∃ r : I64, Aegis.MinimumSum.minimum_sum grid = ok r ∧ r.val = (3 : ℤ)) := by
    sorry

  /-- The function returns Result.ok r and r = B, where B = (rmax-rmin+1)*(cmax-cmin+1).
    Preconditions: Let m = len(grid). There exists n with 1 <= m <= 30, 1 <= n <= 30, and len(grid[i]) = n for every 0 <= i < m. For every 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. Let rmin and rmax be the minimum and maximum row indices of 1-cells, and let cmin and cmax be the minimum and maximum column indices of 1-cells. Assume that for every i,j with rmin <= i <= rmax and cmin <= j <= cmax, grid[i][j] = 1. -/
  theorem spec_6 (grid : Grid) (m n rmin rmax cmin cmax : ℕ) (h : IsBinaryGrid grid m n)
      (hbox : IsBoundingBox grid m n rmin rmax cmin cmax)
      (hfull : ∀ i j, rmin ≤ i → i ≤ rmax → cmin ≤ j → j ≤ cmax → cell grid i j = 1) :
      ∃ r : I64,
        Aegis.MinimumSum.minimum_sum grid = ok r ∧
          r.val = (bboxArea rmin rmax cmin cmax : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Grid) (m n rmin rmax cmin cmax : ℕ) (h : IsBinaryGrid grid m n)
        (hbox : IsBoundingBox grid m n rmin rmax cmin cmax)
        (hfull : ∀ i j, rmin ≤ i → i ≤ rmax → cmin ≤ j → j ≤ cmax → cell grid i j = 1), ∃ r : I64,
          Aegis.MinimumSum.minimum_sum grid = ok r ∧
            r.val = (bboxArea rmin rmax cmin cmax : ℤ)) := by
    sorry

  /-- The function returns Result.ok r and there exist three non-empty axis-aligned subrectangles R0, R1, R2 of the grid such that their cell sets are pairwise disjoint, every 1-cell lies in their union, and area(R0)+area(R1)+area(R2) = r, where area(Rq) is the number of cells in Rq.
    Preconditions: Let m = len(grid). There exists n with 1 <= m <= 30, 1 <= n <= 30, and len(grid[i]) = n for every 0 <= i < m. For every 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. The number of pairs (i,j) with grid[i][j] = 1 is at least 3. -/
  theorem spec_7 (grid : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
      (h3 : 3 ≤ onesCount grid m n) :
      ∃ r : I64,
        Aegis.MinimumSum.minimum_sum grid = ok r ∧
          ∃ R0 R1 R2 : Rect,
            ValidTriple grid m n R0 R1 R2 ∧ (tripleArea R0 R1 R2 : ℤ) = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
        (h3 : 3 ≤ onesCount grid m n), ∃ r : I64,
          Aegis.MinimumSum.minimum_sum grid = ok r ∧
            ∃ R0 R1 R2 : Rect,
              ValidTriple grid m n R0 R1 R2 ∧ (tripleArea R0 R1 R2 : ℤ) = r.val) := by
    sorry

  /-- Whenever the function returns Result.ok r, for every triple of three non-empty axis-aligned subrectangles R0, R1, R2 of the grid whose cell sets are pairwise disjoint and whose union contains every 1-cell, we have r <= area(R0)+area(R1)+area(R2), where area(Rq) is the number of cells in Rq.
    Preconditions: Let m = len(grid). There exists n with 1 <= m <= 30, 1 <= n <= 30, and len(grid[i]) = n for every 0 <= i < m. For every 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. The number of pairs (i,j) with grid[i][j] = 1 is at least 3. -/
  theorem spec_8 (grid : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
      (h3 : 3 ≤ onesCount grid m n) :
      ∀ r : I64,
        Aegis.MinimumSum.minimum_sum grid = ok r →
          ∀ R0 R1 R2 : Rect,
            ValidTriple grid m n R0 R1 R2 → r.val ≤ (tripleArea R0 R1 R2 : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
        (h3 : 3 ≤ onesCount grid m n), ∀ r : I64,
          Aegis.MinimumSum.minimum_sum grid = ok r →
            ∀ R0 R1 R2 : Rect,
              ValidTriple grid m n R0 R1 R2 → r.val ≤ (tripleArea R0 R1 R2 : ℤ)) := by
    sorry

  /-- Let gridT be the n by m grid defined by gridT[j][i] = grid[i][j] for 0 <= i < m and 0 <= j < n. If minimum_sum(grid) returns Result.ok r and minimum_sum(gridT) returns Result.ok rT, then r = rT.
    Preconditions: Let m = len(grid). There exists n with 1 <= m <= 30, 1 <= n <= 30, and len(grid[i]) = n for every 0 <= i < m. For every 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. The number of pairs (i,j) with grid[i][j] = 1 is at least 3. -/
  theorem spec_9 (grid gridT : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
      (h3 : 3 ≤ onesCount grid m n) (hT : cells gridT = transposeCells grid m n) :
      ∀ r rT : I64,
        Aegis.MinimumSum.minimum_sum grid = ok r →
          Aegis.MinimumSum.minimum_sum gridT = ok rT → r.val = rT.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid gridT : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
        (h3 : 3 ≤ onesCount grid m n) (hT : cells gridT = transposeCells grid m n), ∀ r rT : I64,
          Aegis.MinimumSum.minimum_sum grid = ok r →
            Aegis.MinimumSum.minimum_sum gridT = ok rT → r.val = rT.val) := by
    sorry

  /-- Let gridLR be the m by n grid defined by gridLR[i][j] = grid[i][n-1-j]. If minimum_sum(grid) returns Result.ok r and minimum_sum(gridLR) returns Result.ok rLR, then r = rLR.
    Preconditions: Let m = len(grid). There exists n with 1 <= m <= 30, 1 <= n <= 30, and len(grid[i]) = n for every 0 <= i < m. For every 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. The number of pairs (i,j) with grid[i][j] = 1 is at least 3. -/
  theorem spec_10 (grid gridLR : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
      (h3 : 3 ≤ onesCount grid m n) (hT : cells gridLR = mirrorLRCells grid) :
      ∀ r rLR : I64,
        Aegis.MinimumSum.minimum_sum grid = ok r →
          Aegis.MinimumSum.minimum_sum gridLR = ok rLR → r.val = rLR.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid gridLR : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
        (h3 : 3 ≤ onesCount grid m n) (hT : cells gridLR = mirrorLRCells grid), ∀ r rLR : I64,
          Aegis.MinimumSum.minimum_sum grid = ok r →
            Aegis.MinimumSum.minimum_sum gridLR = ok rLR → r.val = rLR.val) := by
    sorry

  /-- Let gridUD be the m by n grid defined by gridUD[i][j] = grid[m-1-i][j]. If minimum_sum(grid) returns Result.ok r and minimum_sum(gridUD) returns Result.ok rUD, then r = rUD.
    Preconditions: Let m = len(grid). There exists n with 1 <= m <= 30, 1 <= n <= 30, and len(grid[i]) = n for every 0 <= i < m. For every 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. The number of pairs (i,j) with grid[i][j] = 1 is at least 3. -/
  theorem spec_11 (grid gridUD : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
      (h3 : 3 ≤ onesCount grid m n) (hT : cells gridUD = mirrorUDCells grid) :
      ∀ r rUD : I64,
        Aegis.MinimumSum.minimum_sum grid = ok r →
          Aegis.MinimumSum.minimum_sum gridUD = ok rUD → r.val = rUD.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid gridUD : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
        (h3 : 3 ≤ onesCount grid m n) (hT : cells gridUD = mirrorUDCells grid), ∀ r rUD : I64,
          Aegis.MinimumSum.minimum_sum grid = ok r →
            Aegis.MinimumSum.minimum_sum gridUD = ok rUD → r.val = rUD.val) := by
    sorry

  /-- Let p_0 < p_1 < ... < p_{K-1} be the column indices j with grid[0][j] = 1, where K is the number of 1s. For t = 0,...,K-2 let g_t = p_{t+1} - p_t - 1. Let G be the sum of the two largest values among g_0,...,g_{K-2}, counted with multiplicity. The function returns Result.ok r and r = (p_{K-1} - p_0 + 1) - G.
    Preconditions: Let m = len(grid). There exists n with 1 <= m <= 30, 1 <= n <= 30, and len(grid[i]) = n for every 0 <= i < m. For every 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. The number of pairs (i,j) with grid[i][j] = 1 is at least 3, and m = 1. -/
  theorem spec_12 (grid : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
      (h3 : 3 ≤ onesCount grid m n) (hm : m = 1) :
      ∃ r : I64,
        Aegis.MinimumSum.minimum_sum grid = ok r ∧
          r.val = edgeAnswer ((List.range n).filter (fun j => cell grid 0 j = 1)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
        (h3 : 3 ≤ onesCount grid m n) (hm : m = 1), ∃ r : I64,
          Aegis.MinimumSum.minimum_sum grid = ok r ∧
            r.val = edgeAnswer ((List.range n).filter (fun j => cell grid 0 j = 1))) := by
    sorry

  /-- Let q_0 < q_1 < ... < q_{K-1} be the row indices i with grid[i][0] = 1, where K is the number of 1s. For t = 0,...,K-2 let h_t = q_{t+1} - q_t - 1. Let H be the sum of the two largest values among h_0,...,h_{K-2}, counted with multiplicity. The function returns Result.ok r and r = (q_{K-1} - q_0 + 1) - H.
    Preconditions: Let m = len(grid). There exists n with 1 <= m <= 30, 1 <= n <= 30, and len(grid[i]) = n for every 0 <= i < m. For every 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. The number of pairs (i,j) with grid[i][j] = 1 is at least 3, and n = 1. -/
  theorem spec_13 (grid : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
      (h3 : 3 ≤ onesCount grid m n) (hn : n = 1) :
      ∃ r : I64,
        Aegis.MinimumSum.minimum_sum grid = ok r ∧
          r.val = edgeAnswer ((List.range m).filter (fun i => cell grid i 0 = 1)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (grid : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
        (h3 : 3 ≤ onesCount grid m n) (hn : n = 1), ∃ r : I64,
          Aegis.MinimumSum.minimum_sum grid = ok r ∧
            r.val = edgeAnswer ((List.range m).filter (fun i => cell grid i 0 = 1))) := by
    sorry

  /-- If minimum_sum(A) returns Result.ok rA and minimum_sum(B) returns Result.ok rB, then rA <= rB.
    Preconditions: Let A and B be two m by n binary grids with 1 <= m <= 30 and 1 <= n <= 30, each having at least three 1-cells, and assume A[i][j] <= B[i][j] for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_14 (A B : Grid) (m n : ℕ) (hA : IsBinaryGrid A m n) (hB : IsBinaryGrid B m n)
      (h3A : 3 ≤ onesCount A m n) (h3B : 3 ≤ onesCount B m n)
      (hle : ∀ i j, i < m → j < n → cell A i j ≤ cell B i j) :
      ∀ rA rB : I64,
        Aegis.MinimumSum.minimum_sum A = ok rA →
          Aegis.MinimumSum.minimum_sum B = ok rB → rA.val ≤ rB.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (A B : Grid) (m n : ℕ) (hA : IsBinaryGrid A m n) (hB : IsBinaryGrid B m n)
        (h3A : 3 ≤ onesCount A m n) (h3B : 3 ≤ onesCount B m n)
        (hle : ∀ i j, i < m → j < n → cell A i j ≤ cell B i j), ∀ rA rB : I64,
          Aegis.MinimumSum.minimum_sum A = ok rA →
            Aegis.MinimumSum.minimum_sum B = ok rB → rA.val ≤ rB.val) := by
    sorry

  /-- Let rmin and rmax be the minimum and maximum row indices of 1-cells, and let cmin and cmax be the minimum and maximum column indices of 1-cells. Let grid2 be the (rmax-rmin+1) by (cmax-cmin+1) grid defined by grid2[i][j] = grid[rmin+i][cmin+j]. If minimum_sum(grid) returns Result.ok r and minimum_sum(grid2) returns Result.ok r2, then r = r2.
    Preconditions: Let m = len(grid). There exists n with 1 <= m <= 30, 1 <= n <= 30, and len(grid[i]) = n for every 0 <= i < m. For every 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. The number of pairs (i,j) with grid[i][j] = 1 is at least 3. -/
  theorem spec_15 (grid grid2 : Grid) (m n rmin rmax cmin cmax : ℕ) (h : IsBinaryGrid grid m n)
      (h3 : 3 ≤ onesCount grid m n) (hbox : IsBoundingBox grid m n rmin rmax cmin cmax)
      (h2 : cells grid2 = cropCells grid rmin rmax cmin cmax) :
      ∀ r r2 : I64,
        Aegis.MinimumSum.minimum_sum grid = ok r →
          Aegis.MinimumSum.minimum_sum grid2 = ok r2 → r.val = r2.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (grid grid2 : Grid) (m n rmin rmax cmin cmax : ℕ) (h : IsBinaryGrid grid m n)
        (h3 : 3 ≤ onesCount grid m n) (hbox : IsBoundingBox grid m n rmin rmax cmin cmax)
        (h2 : cells grid2 = cropCells grid rmin rmax cmin cmax), ∀ r r2 : I64,
          Aegis.MinimumSum.minimum_sum grid = ok r →
            Aegis.MinimumSum.minimum_sum grid2 = ok r2 → r.val = r2.val) := by
    sorry

  /-- The function returns Result.ok r and there exist three non-empty pairwise cell-disjoint axis-aligned subrectangles R0, R1, R2 of the m by n grid such that every 1-cell lies in R0 union R1 union R2, area(R0)+area(R1)+area(R2)=r, each Rq contains at least one 1-cell, and for each Rq with row range aq..bq and column range cq..dq, each of the rows aq and bq and each of the columns cq and dq contains at least one 1-cell lying in Rq.
    Preconditions: Let m = len(grid). There exists n with 1 <= m <= 30, 1 <= n <= 30, and len(grid[i]) = n for every 0 <= i < m. For every 0 <= i < m and 0 <= j < n, grid[i][j] is 0 or 1. The number of pairs (i,j) with grid[i][j] = 1 is at least 3. -/
  theorem spec_16 (grid : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
      (h3 : 3 ≤ onesCount grid m n) :
      ∃ r : I64,
        Aegis.MinimumSum.minimum_sum grid = ok r ∧
          ∃ R0 R1 R2 : Rect,
            ValidTriple grid m n R0 R1 R2 ∧ (tripleArea R0 R1 R2 : ℤ) = r.val ∧
              rectHasOne grid R0 ∧ rectHasOne grid R1 ∧ rectHasOne grid R2 ∧
                rectTight grid R0 ∧ rectTight grid R1 ∧ rectTight grid R2 := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (grid : Grid) (m n : ℕ) (h : IsBinaryGrid grid m n)
        (h3 : 3 ≤ onesCount grid m n), ∃ r : I64,
          Aegis.MinimumSum.minimum_sum grid = ok r ∧
            ∃ R0 R1 R2 : Rect,
              ValidTriple grid m n R0 R1 R2 ∧ (tripleArea R0 R1 R2 : ℤ) = r.val ∧
                rectHasOne grid R0 ∧ rectHasOne grid R1 ∧ rectHasOne grid R2 ∧
                  rectTight grid R0 ∧ rectTight grid R1 ∧ rectTight grid R2) := by
    sorry

  end AegisSpec.MinimumSum
