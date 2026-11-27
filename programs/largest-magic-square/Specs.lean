import Aegis.LargestMagicSquare.Code.Funs

/-!
# Specifications of `Aegis.LargestMagicSquare.largest_magic_square`

LeetCode problem `largest-magic-square`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.LargestMagicSquare

  namespace AegisSpec.LargestMagicSquare

  abbrev Grid := Aeneas.Std.Slice (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)

  def numRows (g : Grid) : ℕ := g.val.length

  def numCols (g : Grid) : ℕ :=
    match g.val with
    | [] => 0
    | r :: _ => r.val.length

  def rowVals (g : Grid) (i : ℕ) : List ℤ :=
    match g.val[i]? with
    | none => []
    | some r => r.val.map (fun x => x.val)

  def cell (g : Grid) (i : ℕ) (j : ℕ) : ℤ := (rowVals g i).getD j 0

  def rowSum (g : Grid) (a b i k : ℕ) : ℤ := ∑ j ∈ Finset.range k, cell g (a + i) (b + j)

  def colSum (g : Grid) (a b j k : ℕ) : ℤ := ∑ i ∈ Finset.range k, cell g (a + i) (b + j)

  def diagSum (g : Grid) (a b k : ℕ) : ℤ := ∑ t ∈ Finset.range k, cell g (a + t) (b + t)

  def antiDiagSum (g : Grid) (a b k : ℕ) : ℤ :=
    ∑ t ∈ Finset.range k, cell g (a + t) (b + (k - 1 - t))

  def IsMagic (g : Grid) (a b k : ℕ) (S : ℤ) : Prop :=
    (∀ i, i < k → rowSum g a b i k = S) ∧
    (∀ j, j < k → colSum g a b j k = S) ∧
    diagSum g a b k = S ∧ antiDiagSum g a b k = S

  def HasMagic (g : Grid) (a b k : ℕ) : Prop := ∃ S : ℤ, IsMagic g a b k S

  def IsLargestMagic (g : Grid) (k : ℕ) : Prop :=
    (∃ a b : ℕ, HasMagic g a b k ∧ a + k ≤ numRows g ∧ b + k ≤ numCols g) ∧
    (∀ k' : ℕ, k < k' →
      ∀ a b : ℕ, a + k' ≤ numRows g → b + k' ≤ numCols g → ¬ HasMagic g a b k')

  def sizeOf (r : Aeneas.Std.I64) : ℕ := r.val.toNat

  def ValidGrid (g : Grid) : Prop :=
    1 ≤ numRows g ∧ numRows g ≤ 50 ∧
    1 ≤ numCols g ∧ numCols g ≤ 50 ∧
    (∀ i, i < numRows g → (rowVals g i).length = numCols g) ∧
    (∀ i j, i < numRows g → j < numCols g → 1 ≤ cell g i j ∧ cell g i j ≤ 1000000)

  def IsSubgrid (H g : Grid) : Prop :=
    ∃ u v p q : ℕ,
      u + p ≤ numRows g ∧ v + q ≤ numCols g ∧ 1 ≤ p ∧ 1 ≤ q ∧
      numRows H = p ∧ numCols H = q ∧
      (∀ i, i < p → ∀ j, j < q → cell H i j = cell g (u + i) (v + j))

  def IsTranspose (gT g : Grid) : Prop :=
    numRows gT = numCols g ∧ numCols gT = numRows g ∧
    ∀ i j, i < numRows gT → j < numCols gT → cell gT i j = cell g j i

  def IsShift (g' g : Grid) (c : ℤ) : Prop :=
    numRows g' = numRows g ∧ numCols g' = numCols g ∧
    ∀ i j, i < numRows g → j < numCols g → cell g' i j = cell g i j + c

  def IsRowFlip (gR g : Grid) : Prop :=
    numRows gR = numRows g ∧ numCols gR = numCols g ∧
    ∀ i j, i < numRows g → j < numCols g → cell gR i j = cell g (numRows g - 1 - i) j

  def IsColFlip (gC g : Grid) : Prop :=
    numRows gC = numRows g ∧ numCols gC = numCols g ∧
    ∀ i j, i < numRows g → j < numCols g → cell gC i j = cell g i (numCols g - 1 - j)

  /-- The function returns a result r and r is the largest k such that there exist integers a, b, S with 0 <= a <= m-k and 0 <= b <= n-k and, for the subgrid A[i][j] = grid[a+i][b+j] with 0 <= i < k and 0 <= j < k, all of the following hold: for every i with 0 <= i < k, sum_{j=0}^{k-1} A[i][j] = S; for every j with 0 <= j < k, sum_{i=0}^{k-1} A[i][j] = S; sum_{i=0}^{k-1} A[i][i] = S; and sum_{i=0}^{k-1} A[i][k-1-i] = S. Equivalently: 1 <= r <= min(m,n), such an r x r magic subgrid exists, and no k x k magic subgrid exists for any k with r < k <= min(m,n).
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input is a valid grid: 1 <= m <= 50, every row grid[i] has length n with 1 <= n <= 50, and 1 <= grid[i][j] <= 1000000 for every 0 <= i < m and 0 <= j < n. All sums in the statement are mathematical integer sums, not machine wrap-around. -/
  theorem spec_1 (grid : Grid) (hgrid : ValidGrid grid) :
      ∃ r : Aeneas.Std.I64,
        largest_magic_square grid = ok r ∧
        1 ≤ r.val ∧
        r.val ≤ ((min (numRows grid) (numCols grid) : ℕ) : ℤ) ∧
        IsLargestMagic grid (sizeOf r) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Grid) (hgrid : ValidGrid grid), ∃ r : Aeneas.Std.I64,
          largest_magic_square grid = ok r ∧
          1 ≤ r.val ∧
          r.val ≤ ((min (numRows grid) (numCols grid) : ℕ) : ℤ) ∧
          IsLargestMagic grid (sizeOf r)) := by
    sorry

  /-- The function returns a result for every valid grid; it does not fail, panic, or return an error.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input is a valid grid: 1 <= m <= 50, every row grid[i] has length n with 1 <= n <= 50, and 1 <= grid[i][j] <= 1000000 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_2 (grid : Grid) (hgrid : ValidGrid grid) :
      ∃ r : Aeneas.Std.I64, largest_magic_square grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Grid) (hgrid : ValidGrid grid), ∃ r : Aeneas.Std.I64, largest_magic_square grid = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input is a valid grid: 1 <= m <= 50, every row grid[i] has length n with 1 <= n <= 50, and 1 <= grid[i][j] <= 1000000 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_3 (grid : Grid) (hgrid : ValidGrid grid) :
      ∀ r : Aeneas.Std.I64, largest_magic_square grid = ok r → 1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Grid) (hgrid : ValidGrid grid), ∀ r : Aeneas.Std.I64, largest_magic_square grid = ok r → 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= min(m,n).
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input is a valid grid: 1 <= m <= 50, every row grid[i] has length n with 1 <= n <= 50, and 1 <= grid[i][j] <= 1000000 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_4 (grid : Grid) (hgrid : ValidGrid grid) :
      ∀ r : Aeneas.Std.I64,
        largest_magic_square grid = ok r →
          r.val ≤ ((min (numRows grid) (numCols grid) : ℕ) : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Grid) (hgrid : ValidGrid grid), ∀ r : Aeneas.Std.I64,
          largest_magic_square grid = ok r →
            r.val ≤ ((min (numRows grid) (numCols grid) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, there exist integers a, b, S with 0 <= a <= m-r and 0 <= b <= n-r such that the r x r subgrid with top-left corner (a,b) is magic with common sum S: every row sum, every column sum, the main diagonal sum, and the anti-diagonal sum of that subgrid all equal S.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input is a valid grid: 1 <= m <= 50, every row grid[i] has length n with 1 <= n <= 50, and 1 <= grid[i][j] <= 1000000 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_5 (grid : Grid) (hgrid : ValidGrid grid) :
      ∀ r : Aeneas.Std.I64,
        largest_magic_square grid = ok r →
          ∃ a b : ℕ, ∃ S : ℤ,
            a + sizeOf r ≤ numRows grid ∧ b + sizeOf r ≤ numCols grid ∧
            IsMagic grid a b (sizeOf r) S := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Grid) (hgrid : ValidGrid grid), ∀ r : Aeneas.Std.I64,
          largest_magic_square grid = ok r →
            ∃ a b : ℕ, ∃ S : ℤ,
              a + sizeOf r ≤ numRows grid ∧ b + sizeOf r ≤ numCols grid ∧
              IsMagic grid a b (sizeOf r) S) := by
    sorry

  /-- Whenever the function returns a result r, for every k with r < k <= min(m,n) and every a, b with 0 <= a <= m-k and 0 <= b <= n-k, the k x k subgrid with top-left corner (a,b) is not magic: there is no integer S equal to all its row sums, all its column sums, and its two diagonal sums.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input is a valid grid: 1 <= m <= 50, every row grid[i] has length n with 1 <= n <= 50, and 1 <= grid[i][j] <= 1000000 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_6 (grid : Grid) (hgrid : ValidGrid grid) :
      ∀ r : Aeneas.Std.I64,
        largest_magic_square grid = ok r →
          ∀ k : ℕ,
            sizeOf r < k →
            k ≤ min (numRows grid) (numCols grid) →
            ∀ a b : ℕ,
              a + k ≤ numRows grid →
              b + k ≤ numCols grid →
              ¬ HasMagic grid a b k := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Grid) (hgrid : ValidGrid grid), ∀ r : Aeneas.Std.I64,
          largest_magic_square grid = ok r →
            ∀ k : ℕ,
              sizeOf r < k →
              k ≤ min (numRows grid) (numCols grid) →
              ∀ a b : ℕ,
                a + k ≤ numRows grid →
                b + k ≤ numCols grid →
                ¬ HasMagic grid a b k) := by
    sorry

  /-- The function returns 1.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input is a valid grid: 1 <= m <= 50, every row grid[i] has length n with 1 <= n <= 50, and 1 <= grid[i][j] <= 1000000 for every 0 <= i < m and 0 <= j < n. Additionally, m = 1 or n = 1. -/
  theorem spec_7 (grid : Grid) (hgrid : ValidGrid grid)
      (hthin : numRows grid = 1 ∨ numCols grid = 1) :
      ∃ r : Aeneas.Std.I64, largest_magic_square grid = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Grid) (hgrid : ValidGrid grid)
        (hthin : numRows grid = 1 ∨ numCols grid = 1), ∃ r : Aeneas.Std.I64, largest_magic_square grid = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns min(m,n).
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input is a valid grid: 1 <= m <= 50, every row grid[i] has length n with 1 <= n <= 50, and 1 <= grid[i][j] <= 1000000 for every 0 <= i < m and 0 <= j < n. Additionally, there exists an integer v such that grid[i][j] = v for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_8 (grid : Grid) (hgrid : ValidGrid grid)
      (hconst : ∃ v : ℤ, ∀ i j, i < numRows grid → j < numCols grid → cell grid i j = v) :
      ∃ r : Aeneas.Std.I64,
        largest_magic_square grid = ok r ∧
          r.val = ((min (numRows grid) (numCols grid) : ℕ) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Grid) (hgrid : ValidGrid grid)
        (hconst : ∃ v : ℤ, ∀ i j, i < numRows grid → j < numCols grid → cell grid i j = v), ∃ r : Aeneas.Std.I64,
          largest_magic_square grid = ok r ∧
            r.val = ((min (numRows grid) (numCols grid) : ℕ) : ℤ)) := by
    sorry

  /-- The function returns m.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input is a valid grid: 1 <= m <= 50, every row grid[i] has length n with 1 <= n <= 50, and 1 <= grid[i][j] <= 1000000 for every 0 <= i < m and 0 <= j < n. Additionally, m = n and the whole grid with top-left corner (0,0) and side m is magic with some common sum S. -/
  theorem spec_9 (grid : Grid) (hgrid : ValidGrid grid) (hsquare : numRows grid = numCols grid)
      (hwhole : ∃ S : ℤ, IsMagic grid 0 0 (numRows grid) S) :
      ∃ r : Aeneas.Std.I64, largest_magic_square grid = ok r ∧ r.val = ((numRows grid : ℕ) : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Grid) (hgrid : ValidGrid grid) (hsquare : numRows grid = numCols grid)
        (hwhole : ∃ S : ℤ, IsMagic grid 0 0 (numRows grid) S), ∃ r : Aeneas.Std.I64, largest_magic_square grid = ok r ∧ r.val = ((numRows grid : ℕ) : ℤ)) := by
    sorry

  /-- Whenever largest_magic_square(grid) returns r and largest_magic_square(H) returns rH, we have rH <= r.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input is a valid grid: 1 <= m <= 50, every row grid[i] has length n with 1 <= n <= 50, and 1 <= grid[i][j] <= 1000000 for every 0 <= i < m and 0 <= j < n. Let H be a nonempty contiguous subgrid of grid: there exist integers u, v, p, q with 0 <= u, 0 <= v, 1 <= p <= 50, 1 <= q <= 50, u+p <= m, v+q <= n, and H[i][j] = grid[u+i][v+j] for 0 <= i < p and 0 <= j < q. Thus H also satisfies the same input constraints. -/
  theorem spec_10 (grid H : Grid) (hgrid : ValidGrid grid) (hHvalid : ValidGrid H)
      (hH : IsSubgrid H grid) :
      ∀ r rH : Aeneas.Std.I64,
        largest_magic_square grid = ok r →
          largest_magic_square H = ok rH → rH.val ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid H : Grid) (hgrid : ValidGrid grid) (hHvalid : ValidGrid H)
        (hH : IsSubgrid H grid), ∀ r rH : Aeneas.Std.I64,
          largest_magic_square grid = ok r →
            largest_magic_square H = ok rH → rH.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if there is no k with 2 <= k <= min(m,n) for which some k x k subgrid of grid is magic with some common sum S.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input is a valid grid: 1 <= m <= 50, every row grid[i] has length n with 1 <= n <= 50, and 1 <= grid[i][j] <= 1000000 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_11 (grid : Grid) (hgrid : ValidGrid grid) :
      ∀ r : Aeneas.Std.I64,
        largest_magic_square grid = ok r →
          (r.val = 1 ↔
            ∀ k : ℕ,
              2 ≤ k →
              k ≤ min (numRows grid) (numCols grid) →
              ∀ a b : ℕ,
                a + k ≤ numRows grid → b + k ≤ numCols grid → ¬ HasMagic grid a b k) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid : Grid) (hgrid : ValidGrid grid), ∀ r : Aeneas.Std.I64,
          largest_magic_square grid = ok r →
            (r.val = 1 ↔
              ∀ k : ℕ,
                2 ≤ k →
                k ≤ min (numRows grid) (numCols grid) →
                ∀ a b : ℕ,
                  a + k ≤ numRows grid → b + k ≤ numCols grid → ¬ HasMagic grid a b k)) := by
    sorry

  /-- Whenever largest_magic_square(grid) returns r and largest_magic_square(gridT) returns rT, we have r = rT.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input is a valid grid: 1 <= m <= 50, every row grid[i] has length n with 1 <= n <= 50, and 1 <= grid[i][j] <= 1000000 for every 0 <= i < m and 0 <= j < n. Let gridT be the n x m grid defined by gridT[i][j] = grid[j][i] for 0 <= i < n and 0 <= j < m; gridT is also a valid grid. -/
  theorem spec_12 (grid gT : Grid) (hgrid : ValidGrid grid) (hgT : ValidGrid gT)
      (hT : IsTranspose gT grid) :
      ∀ r rT : Aeneas.Std.I64,
        largest_magic_square grid = ok r →
          largest_magic_square gT = ok rT → r.val = rT.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid gT : Grid) (hgrid : ValidGrid grid) (hgT : ValidGrid gT)
        (hT : IsTranspose gT grid), ∀ r rT : Aeneas.Std.I64,
          largest_magic_square grid = ok r →
            largest_magic_square gT = ok rT → r.val = rT.val) := by
    sorry

  /-- Whenever largest_magic_square(grid) returns r and largest_magic_square(grid2) returns r2, we have r = r2.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input is a valid grid: 1 <= m <= 50, every row grid[i] has length n with 1 <= n <= 50, and 1 <= grid[i][j] <= 1000000 for every 0 <= i < m and 0 <= j < n. Let c be an integer such that 1 <= grid[i][j] + c <= 1000000 for every i,j, and let grid2[i][j] = grid[i][j] + c; grid2 is also a valid grid. -/
  theorem spec_13 (grid grid2 : Grid) (c : ℤ) (hgrid : ValidGrid grid) (hg2 : ValidGrid grid2)
      (hc : ∀ i j, i < numRows grid → j < numCols grid →
        1 ≤ cell grid i j + c ∧ cell grid i j + c ≤ 1000000)
      (hshift : IsShift grid2 grid c) :
      ∀ r r2 : Aeneas.Std.I64,
        largest_magic_square grid = ok r →
          largest_magic_square grid2 = ok r2 → r.val = r2.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (grid grid2 : Grid) (c : ℤ) (hgrid : ValidGrid grid) (hg2 : ValidGrid grid2)
        (hc : ∀ i j, i < numRows grid → j < numCols grid →
          1 ≤ cell grid i j + c ∧ cell grid i j + c ≤ 1000000)
        (hshift : IsShift grid2 grid c), ∀ r r2 : Aeneas.Std.I64,
          largest_magic_square grid = ok r →
            largest_magic_square grid2 = ok r2 → r.val = r2.val) := by
    sorry

  /-- Whenever largest_magic_square(grid) returns r and largest_magic_square(gridR) returns rR, we have r = rR.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input is a valid grid: 1 <= m <= 50, every row grid[i] has length n with 1 <= n <= 50, and 1 <= grid[i][j] <= 1000000 for every 0 <= i < m and 0 <= j < n. Let gridR be the m x n grid defined by gridR[i][j] = grid[m-1-i][j] for 0 <= i < m and 0 <= j < n; gridR is also a valid grid. -/
  theorem spec_14 (grid gridR : Grid) (hgrid : ValidGrid grid) (hgR : ValidGrid gridR)
      (hR : IsRowFlip gridR grid) :
      ∀ r rR : Aeneas.Std.I64,
        largest_magic_square grid = ok r →
          largest_magic_square gridR = ok rR → r.val = rR.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (grid gridR : Grid) (hgrid : ValidGrid grid) (hgR : ValidGrid gridR)
        (hR : IsRowFlip gridR grid), ∀ r rR : Aeneas.Std.I64,
          largest_magic_square grid = ok r →
            largest_magic_square gridR = ok rR → r.val = rR.val) := by
    sorry

  /-- Whenever largest_magic_square(grid) returns r and largest_magic_square(gridC) returns rC, we have r = rC.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input is a valid grid: 1 <= m <= 50, every row grid[i] has length n with 1 <= n <= 50, and 1 <= grid[i][j] <= 1000000 for every 0 <= i < m and 0 <= j < n. Let gridC be the m x n grid defined by gridC[i][j] = grid[i][n-1-j] for 0 <= i < m and 0 <= j < n; gridC is also a valid grid. -/
  theorem spec_15 (grid gridC : Grid) (hgrid : ValidGrid grid) (hgC : ValidGrid gridC)
      (hC : IsColFlip gridC grid) :
      ∀ r rC : Aeneas.Std.I64,
        largest_magic_square grid = ok r →
          largest_magic_square gridC = ok rC → r.val = rC.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (grid gridC : Grid) (hgrid : ValidGrid grid) (hgC : ValidGrid gridC)
        (hC : IsColFlip gridC grid), ∀ r rC : Aeneas.Std.I64,
          largest_magic_square grid = ok r →
            largest_magic_square gridC = ok rC → r.val = rC.val) := by
    sorry

  end AegisSpec.LargestMagicSquare
