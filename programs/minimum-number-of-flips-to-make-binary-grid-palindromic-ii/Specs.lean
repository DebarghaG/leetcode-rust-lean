import Aegis.MinFlips.Code.Funs

/-!
# Specifications of `Aegis.MinFlips.min_flips`

LeetCode problem `minimum-number-of-flips-to-make-binary-grid-palindromic-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinFlips (min_flips)

  namespace AegisSpec.MinFlips

  abbrev Grid : Type := Slice (alloc.vec.Vec Std.I64)

  def row (grid : Grid) (i : ℕ) : List ℤ :=
    match grid.val[i]? with
    | none => []
    | some r => r.val.map (fun x => x.val)

  def cell (grid : Grid) (i j : ℕ) : ℤ :=
    (row grid i)[j]?.getD 0

  def ValidGrid (grid : Grid) (m n : ℕ) : Prop :=
    grid.val.length = m ∧
    1 ≤ m ∧
    1 ≤ n ∧
    (∀ i, i < m → (row grid i).length = n) ∧
    (∀ i, i < m → ∀ j, j < n → cell grid i j = 0 ∨ cell grid i j = 1) ∧
    m * n ≤ 200000

  def Is01 (m n : ℕ) (T : ℕ → ℕ → ℤ) : Prop :=
    ∀ i, i < m → ∀ j, j < n → T i j = 0 ∨ T i j = 1

  def RowPal (m n : ℕ) (T : ℕ → ℕ → ℤ) : Prop :=
    ∀ i, i < m → ∀ j, j < n → T i j = T i (n - 1 - j)

  def ColPal (m n : ℕ) (T : ℕ → ℕ → ℤ) : Prop :=
    ∀ i, i < m → ∀ j, j < n → T i j = T (m - 1 - i) j

  def Palindromic (m n : ℕ) (T : ℕ → ℕ → ℤ) : Prop :=
    Is01 m n T ∧ RowPal m n T ∧ ColPal m n T

  def ones (m n : ℕ) (T : ℕ → ℕ → ℤ) : ℕ :=
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, if T i j = 1 then 1 else 0

  def Admissible (m n : ℕ) (T : ℕ → ℕ → ℤ) : Prop :=
    Palindromic m n T ∧ 4 ∣ ones m n T

  def gridOnes (grid : Grid) (m n : ℕ) : ℕ :=
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, if cell grid i j = 1 then 1 else 0

  def gridZeros (grid : Grid) (m n : ℕ) : ℕ :=
    m * n - gridOnes grid m n

  def cost (grid : Grid) (m n : ℕ) (T : ℕ → ℕ → ℤ) : ℕ :=
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, if T i j = cell grid i j then 0 else 1

  def dist (g h : Grid) (m n : ℕ) : ℕ :=
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, if cell g i j = cell h i j then 0 else 1

  def gridRowPal (grid : Grid) (m n : ℕ) : Prop :=
    ∀ i, i < m → ∀ j, j < n → cell grid i j = cell grid i (n - 1 - j)

  def gridColPal (grid : Grid) (m n : ℕ) : Prop :=
    ∀ i, i < m → ∀ j, j < n → cell grid i j = cell grid (m - 1 - i) j

  def IsRowReverse (g gR : Grid) (m n : ℕ) : Prop :=
    ∀ i, i < m → ∀ j, j < n → cell gR i j = cell g (m - 1 - i) j

  def IsColReverse (g gC : Grid) (m n : ℕ) : Prop :=
    ∀ i, i < m → ∀ j, j < n → cell gC i j = cell g i (n - 1 - j)

  def IsComplement (g gX : Grid) (m n : ℕ) : Prop :=
    ∀ i, i < m → ∀ j, j < n → cell gX i j = 1 - cell g i j

  def IsTranspose (g gT : Grid) (m n : ℕ) : Prop :=
    ∀ i, i < m → ∀ j, j < n → cell gT j i = cell g i j

  /-- For a 0/1 matrix T of size m by n, call T admissible when (1) every row of T is palindromic, meaning T[i][j] = T[i][n-1-j] for all 0 <= i < m and 0 <= j < n, (2) every column of T is palindromic, meaning T[i][j] = T[m-1-i][j] for all 0 <= i < m and 0 <= j < n, and (3) the total number of 1 entries of T is divisible by 4. Let C(T) be the number of positions (i,j) with T[i][j] != grid[i][j]. The function returns a result r and r = min { C(T) : T is admissible }. The minimum is over a nonempty set because the all-zero matrix is admissible.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is valid: m >= 1, n >= 1, every row grid[i] has length n, every entry grid[i][j] is 0 or 1, and m*n <= 200000. -/
  theorem spec_1 (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n) :
      ∃ r : Std.I64,
        min_flips grid = ok r ∧
        (∀ T, Admissible m n T → r.val ≤ (cost grid m n T : ℤ)) ∧
        ∃ T, Admissible m n T ∧ (cost grid m n T : ℤ) = r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n), ∃ r : Std.I64,
          min_flips grid = ok r ∧
          (∀ T, Admissible m n T → r.val ≤ (cost grid m n T : ℤ)) ∧
          ∃ T, Admissible m n T ∧ (cost grid m n T : ℤ) = r.val) := by
    sorry

  /-- The function returns a Result value r, not an error: no valid input causes a panic, out-of-bounds access, division by zero, or signed 64-bit overflow.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is valid: m >= 1, n >= 1, every row grid[i] has length n, every entry grid[i][j] is 0 or 1, and m*n <= 200000. -/
  theorem spec_2 (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n) :
      ∃ r : Std.I64, min_flips grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n), ∃ r : Std.I64, min_flips grid = ok r) := by
    sorry

  /-- Let r be the returned value. Then 0 <= r <= m*n.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is valid: m >= 1, n >= 1, every row grid[i] has length n, every entry grid[i][j] is 0 or 1, and m*n <= 200000. -/
  theorem spec_3 (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n) (r : Std.I64)
      (hr : min_flips grid = ok r) :
      0 ≤ r.val ∧ r.val ≤ (m * n : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n) (r : Std.I64)
        (hr : min_flips grid = ok r), 0 ≤ r.val ∧ r.val ≤ (m * n : ℤ)) := by
    sorry

  /-- Let r be the returned value. Then r = 0 if and only if the given grid itself is row-palindromic and column-palindromic and the total number of 1 entries in grid is divisible by 4.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is valid: m >= 1, n >= 1, every row grid[i] has length n, every entry grid[i][j] is 0 or 1, and m*n <= 200000. -/
  theorem spec_4 (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n) (r : Std.I64)
      (hr : min_flips grid = ok r) :
      (r.val = 0 ↔
        gridRowPal grid m n ∧ gridColPal grid m n ∧ 4 ∣ gridOnes grid m n) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n) (r : Std.I64)
        (hr : min_flips grid = ok r), (r.val = 0 ↔
          gridRowPal grid m n ∧ gridColPal grid m n ∧ 4 ∣ gridOnes grid m n)) := by
    sorry

  /-- Let ones = #{ (i,j) : 0 <= i < m, 0 <= j < n, grid[i][j] = 1 } and let r be the returned value. Then r <= ones.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is valid: m >= 1, n >= 1, every row grid[i] has length n, every entry grid[i][j] is 0 or 1, and m*n <= 200000. -/
  theorem spec_5 (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n) (r : Std.I64)
      (hr : min_flips grid = ok r) :
      r.val ≤ (gridOnes grid m n : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n) (r : Std.I64)
        (hr : min_flips grid = ok r), r.val ≤ (gridOnes grid m n : ℤ)) := by
    sorry

  /-- Let ones be the number of 1 entries in grid, let zeros = m*n - ones, and let r be the returned value. Then r <= zeros.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is valid: m >= 1, n >= 1, every row grid[i] has length n, every entry grid[i][j] is 0 or 1, and m*n <= 200000. Assume 4 divides m*n. -/
  theorem spec_6 (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n)
      (hd : 4 ∣ m * n) (r : Std.I64) (hr : min_flips grid = ok r) :
      r.val ≤ (gridZeros grid m n : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n)
        (hd : 4 ∣ m * n) (r : Std.I64) (hr : min_flips grid = ok r), r.val ≤ (gridZeros grid m n : ℤ)) := by
    sorry

  /-- Let ones be the number of 1 entries in grid and let r be the returned value. Then r = ones.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is valid: m >= 1, n >= 1, every row grid[i] has length n, every entry grid[i][j] is 0 or 1, and m*n <= 200000. Assume m*n <= 3. -/
  theorem spec_7 (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n)
      (hsmall : m * n ≤ 3) (r : Std.I64) (hr : min_flips grid = ok r) :
      r.val = (gridOnes grid m n : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n)
        (hsmall : m * n ≤ 3) (r : Std.I64) (hr : min_flips grid = ok r), r.val = (gridOnes grid m n : ℤ)) := by
    sorry

  /-- Let ones be the number of 1 entries in grid and let r be the returned value. Then r = min(ones, 4 - ones).
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is valid: m >= 1, n >= 1, every row grid[i] has length n, every entry grid[i][j] is 0 or 1, m*n <= 200000, and additionally m = n = 2. -/
  theorem spec_8 (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n)
      (hm : m = 2) (hn : n = 2) (r : Std.I64) (hr : min_flips grid = ok r) :
      r.val = ((min (gridOnes grid m n) (4 - gridOnes grid m n) : ℕ) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n)
        (hm : m = 2) (hn : n = 2) (r : Std.I64) (hr : min_flips grid = ok r), r.val = ((min (gridOnes grid m n) (4 - gridOnes grid m n) : ℕ) : ℤ)) := by
    sorry

  /-- Let r be the returned value. Then r = min { C(T) : T is a 0/1 m by n matrix whose every row and every column is palindromic }, where C(T)=#{ (i,j) : T[i][j] != grid[i][j] }. The divisibility-by-4 condition is automatic for every row/column-palindromic T when m and n are both even, so no admissible target is excluded by it.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is valid: m >= 1, n >= 1, every row grid[i] has length n, every entry grid[i][j] is 0 or 1, and m*n <= 200000. Assume m and n are both even. -/
  theorem spec_9 (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n)
      (hm : Even m) (hn : Even n) (r : Std.I64) (hr : min_flips grid = ok r) :
      (∀ T, Palindromic m n T → r.val ≤ (cost grid m n T : ℤ)) ∧
      ∃ T, Palindromic m n T ∧ (cost grid m n T : ℤ) = r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n)
        (hm : Even m) (hn : Even n) (r : Std.I64) (hr : min_flips grid = ok r), (∀ T, Palindromic m n T → r.val ≤ (cost grid m n T : ℤ)) ∧
        ∃ T, Palindromic m n T ∧ (cost grid m n T : ℤ) = r.val) := by
    sorry

  /-- Let gridR be the m by n matrix defined by gridR[i][j] = grid[m-1-i][j]. Let r = min_flips(grid) and rR = min_flips(gridR) be the returned values. Then r = rR.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is valid: m >= 1, n >= 1, every row grid[i] has length n, every entry grid[i][j] is 0 or 1, and m*n <= 200000. -/
  theorem spec_10 (g gR : Grid) (m n : ℕ) (hg : ValidGrid g m n)
      (hgR : ValidGrid gR m n) (hrev : IsRowReverse g gR m n)
      (r rR : Std.I64) (hr : min_flips g = ok r) (hrR : min_flips gR = ok rR) :
      r.val = rR.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (g gR : Grid) (m n : ℕ) (hg : ValidGrid g m n)
        (hgR : ValidGrid gR m n) (hrev : IsRowReverse g gR m n)
        (r rR : Std.I64) (hr : min_flips g = ok r) (hrR : min_flips gR = ok rR), r.val = rR.val) := by
    sorry

  /-- Let gridC be the m by n matrix defined by gridC[i][j] = grid[i][n-1-j]. Let r = min_flips(grid) and rC = min_flips(gridC) be the returned values. Then r = rC.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is valid: m >= 1, n >= 1, every row grid[i] has length n, every entry grid[i][j] is 0 or 1, and m*n <= 200000. -/
  theorem spec_11 (g gC : Grid) (m n : ℕ) (hg : ValidGrid g m n)
      (hgC : ValidGrid gC m n) (hrev : IsColReverse g gC m n)
      (r rC : Std.I64) (hr : min_flips g = ok r) (hrC : min_flips gC = ok rC) :
      r.val = rC.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (g gC : Grid) (m n : ℕ) (hg : ValidGrid g m n)
        (hgC : ValidGrid gC m n) (hrev : IsColReverse g gC m n)
        (r rC : Std.I64) (hr : min_flips g = ok r) (hrC : min_flips gC = ok rC), r.val = rC.val) := by
    sorry

  /-- Let gridT be the n by m matrix defined by gridT[j][i] = grid[i][j]. Let r = min_flips(grid) and rT = min_flips(gridT) be the returned values. Then r = rT.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is valid: m >= 1, n >= 1, every row grid[i] has length n, every entry grid[i][j] is 0 or 1, and m*n <= 200000. -/
  theorem spec_12 (g gT : Grid) (m n : ℕ) (hg : ValidGrid g m n)
      (hgT : ValidGrid gT n m) (htr : IsTranspose g gT m n)
      (r rT : Std.I64) (hr : min_flips g = ok r) (hrT : min_flips gT = ok rT) :
      r.val = rT.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (g gT : Grid) (m n : ℕ) (hg : ValidGrid g m n)
        (hgT : ValidGrid gT n m) (htr : IsTranspose g gT m n)
        (r rT : Std.I64) (hr : min_flips g = ok r) (hrT : min_flips gT = ok rT), r.val = rT.val) := by
    sorry

  /-- Let gridX be defined by gridX[i][j] = 1 - grid[i][j] for all i,j. Let r = min_flips(grid) and rX = min_flips(gridX) be the returned values. Then r = rX.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is valid: m >= 1, n >= 1, every row grid[i] has length n, every entry grid[i][j] is 0 or 1, and m*n <= 200000. Assume 4 divides m*n. -/
  theorem spec_13 (g gX : Grid) (m n : ℕ) (hg : ValidGrid g m n)
      (hgX : ValidGrid gX m n) (hd : 4 ∣ m * n) (hX : IsComplement g gX m n)
      (r rX : Std.I64) (hr : min_flips g = ok r) (hrX : min_flips gX = ok rX) :
      r.val = rX.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (g gX : Grid) (m n : ℕ) (hg : ValidGrid g m n)
        (hgX : ValidGrid gX m n) (hd : 4 ∣ m * n) (hX : IsComplement g gX m n)
        (r rX : Std.I64) (hr : min_flips g = ok r) (hrX : min_flips gX = ok rX), r.val = rX.val) := by
    sorry

  /-- Let rg = min_flips(g) and rh = min_flips(h) be the returned values. Then |rg - rh| <= H(g,h), where H(g,h) = #{ (i,j) : g[i][j] != h[i][j] }.
    Preconditions: Let m >= 1 and n >= 1 with m*n <= 200000. Let g and h be any two valid m by n binary matrices, so every entry is 0 or 1. -/
  theorem spec_14 (g h : Grid) (m n : ℕ) (hg : ValidGrid g m n)
      (hh : ValidGrid h m n) (rg rh : Std.I64)
      (hrg : min_flips g = ok rg) (hrh : min_flips h = ok rh) :
      |rg.val - rh.val| ≤ (dist g h m n : ℤ) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (g h : Grid) (m n : ℕ) (hg : ValidGrid g m n)
        (hh : ValidGrid h m n) (rg rh : Std.I64)
        (hrg : min_flips g = ok rg) (hrh : min_flips h = ok rh), |rg.val - rh.val| ≤ (dist g h m n : ℤ)) := by
    sorry

  /-- Let r be the returned value. There exists a 0/1 m by n matrix T such that every row and every column of T is palindromic, the total number of 1 entries of T is divisible by 4, and exactly r positions (i,j) satisfy T[i][j] != grid[i][j].
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is valid: m >= 1, n >= 1, every row grid[i] has length n, every entry grid[i][j] is 0 or 1, and m*n <= 200000. -/
  theorem spec_15 (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n) (r : Std.I64)
      (hr : min_flips grid = ok r) :
      ∃ T, Admissible m n T ∧ (cost grid m n T : ℤ) = r.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (grid : Grid) (m n : ℕ) (h : ValidGrid grid m n) (r : Std.I64)
        (hr : min_flips grid = ok r), ∃ T, Admissible m n T ∧ (cost grid m n T : ℤ) = r.val) := by
    sorry

  end AegisSpec.MinFlips
