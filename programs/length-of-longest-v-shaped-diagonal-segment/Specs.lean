import Aegis.LenOfVDiagonal.Code.Funs

/-!
# Specifications of `Aegis.LenOfVDiagonal.len_of_v_diagonal`

LeetCode problem `length-of-longest-v-shaped-diagonal-segment`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LenOfVDiagonal

  def cellAt (grid : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : Option ℤ :=
    ((grid.val[i]?).bind (fun row => row.val[j]?)).map (fun x => x.val)

  def cellValue (grid : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
    (cellAt grid i j).getD 0

  def seqVal (k : ℕ) : ℤ :=
    if k = 0 then 1 else if k % 2 = 1 then 2 else 0

  def isDiagDir (di dj : ℤ) : Prop :=
    (di = 1 ∨ di = -1) ∧ (dj = 1 ∨ dj = -1)

  def diagStep (p q : ℕ × ℕ) (di dj : ℤ) : Prop :=
    (q.1 : ℤ) = (p.1 : ℤ) + di ∧ (q.2 : ℤ) = (p.2 : ℤ) + dj

  def isGrid (grid : Slice (alloc.vec.Vec Std.I64)) (n m : ℕ) : Prop :=
    1 ≤ n ∧ n ≤ 500 ∧ 1 ≤ m ∧ m ≤ 500 ∧
    grid.val.length = n ∧
    (∀ (i : ℕ), i < n →
      ∃ row : alloc.vec.Vec Std.I64, grid.val[i]? = some row ∧ row.val.length = m) ∧
    (∀ (i j : ℕ) (x : ℤ), i < n → j < m → cellAt grid i j = some x → x = 0 ∨ x = 1 ∨ x = 2)

  def hasCellOne (grid : Slice (alloc.vec.Vec Std.I64)) (n m : ℕ) : Prop :=
    ∃ i j : ℕ, i < n ∧ j < m ∧ cellValue grid i j = 1

  def hasDiagOneTwo (grid : Slice (alloc.vec.Vec Std.I64)) (n m : ℕ) : Prop :=
    ∃ i j i' j' : ℕ,
      i < n ∧ i' < n ∧ j < m ∧ j' < m ∧
      (i' = i + 1 ∨ i = i' + 1) ∧ (j' = j + 1 ∨ j = j' + 1) ∧
      cellValue grid i j = 1 ∧ cellValue grid i' j' = 2

  def isVSegment (grid : Slice (alloc.vec.Vec Std.I64)) (n m : ℕ) (L : ℕ)
      (p : ℕ → ℕ × ℕ) : Prop :=
    1 ≤ L ∧
    (∀ k : ℕ, k < L → (p k).1 < n ∧ (p k).2 < m) ∧
    (∀ k : ℕ, k < L → cellValue grid (p k).1 (p k).2 = seqVal k) ∧
    ∃ (di dj si sj : ℤ) (t : ℕ),
      isDiagDir di dj ∧
      ((si = di ∧ sj = dj) ∨ (si = dj ∧ sj = -di)) ∧
      t ≤ L - 1 ∧
      (∀ k : ℕ, k < t → diagStep (p k) (p (k + 1)) di dj) ∧
      (∀ k : ℕ, t ≤ k → k + 1 < L → diagStep (p k) (p (k + 1)) si sj)

  /-- Let seq(0)=1, seq(k)=2 for odd k, and seq(k)=0 for even k>=2. A V-shaped diagonal segment is a sequence of cells p_0,...,p_{L-1}, L>=1, such that: (a) each p_k=(i_k,j_k) is a valid cell (0<=i_k<n, 0<=j_k<m); (b) grid[i_k][j_k]=seq(k) for all 0<=k<L; (c) there exist a direction d=(di,dj) with di,dj in {-1,1}, a direction d' with either d'=d or d'=(dj,-di), and an integer t with 0<=t<=L-1 such that p_{k+1}-p_k=d for every 0<=k<t and p_{k+1}-p_k=d' for every t<=k<L-1. The turn, if any, occurs at p_t. The function returns an integer r such that: (1) r=0 if and only if there is no cell (i,j) with grid[i][j]=1; (2) if r>0, there exists a V-shaped diagonal segment in grid of length r; (3) every V-shaped diagonal segment in grid has length at most r.
    Preconditions: grid is a non-empty rectangular matrix: len(grid) = n with 1 <= n <= 500, and for every i with 0 <= i < n, len(grid[i]) = m with 1 <= m <= 500, and every entry grid[i][j] is either 0, 1, or 2. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (n m : ℕ) (hg : isGrid grid n m) :
      ∃ r : Std.I64,
        Aegis.LenOfVDiagonal.len_of_v_diagonal grid = Result.ok r ∧
        (r.val = 0 ↔ ¬ hasCellOne grid n m) ∧
        (0 < r.val →
          ∃ (L : ℕ) (p : ℕ → ℕ × ℕ), isVSegment grid n m L p ∧ (L : ℤ) = r.val) ∧
        (∀ (L : ℕ) (p : ℕ → ℕ × ℕ), isVSegment grid n m L p → (L : ℤ) ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n m : ℕ) (hg : isGrid grid n m), ∃ r : Std.I64,
          Aegis.LenOfVDiagonal.len_of_v_diagonal grid = Result.ok r ∧
          (r.val = 0 ↔ ¬ hasCellOne grid n m) ∧
          (0 < r.val →
            ∃ (L : ℕ) (p : ℕ → ℕ × ℕ), isVSegment grid n m L p ∧ (L : ℤ) = r.val) ∧
          (∀ (L : ℕ) (p : ℕ → ℕ × ℕ), isVSegment grid n m L p → (L : ℤ) ≤ r.val)) := by
    sorry

  /-- The function returns a result r and does not fail (no panic, no out-of-bounds access, no arithmetic overflow).
    Preconditions: grid is a non-empty rectangular matrix: len(grid) = n with 1 <= n <= 500, and for every i with 0 <= i < n, len(grid[i]) = m with 1 <= m <= 500, and every entry grid[i][j] is either 0, 1, or 2. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (n m : ℕ) (hg : isGrid grid n m) :
      ∃ r : Std.I64, Aegis.LenOfVDiagonal.len_of_v_diagonal grid = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n m : ℕ) (hg : isGrid grid n m), ∃ r : Std.I64, Aegis.LenOfVDiagonal.len_of_v_diagonal grid = Result.ok r) := by
    sorry

  /-- 0 <= r <= max(n, m), where n = len(grid) and m = len(grid[0]).
    Preconditions: grid is a non-empty rectangular matrix: len(grid) = n with 1 <= n <= 500, and for every i with 0 <= i < n, len(grid[i]) = m with 1 <= m <= 500, and every entry grid[i][j] is either 0, 1, or 2. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (n m : ℕ) (hg : isGrid grid n m) :
      ∃ r : Std.I64,
        Aegis.LenOfVDiagonal.len_of_v_diagonal grid = Result.ok r ∧
        0 ≤ r.val ∧ r.val ≤ (max n m : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n m : ℕ) (hg : isGrid grid n m), ∃ r : Std.I64,
          Aegis.LenOfVDiagonal.len_of_v_diagonal grid = Result.ok r ∧
          0 ≤ r.val ∧ r.val ≤ (max n m : ℤ)) := by
    sorry

  /-- If n = 1 or m = 1, then r = 1 if there exists a cell with value 1, and r = 0 otherwise.
    Preconditions: grid is a non-empty rectangular matrix: len(grid) = n with 1 <= n <= 500, and for every i with 0 <= i < n, len(grid[i]) = m with 1 <= m <= 500, and every entry grid[i][j] is either 0, 1, or 2. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (n m : ℕ) (hg : isGrid grid n m) :
      ∃ r : Std.I64,
        Aegis.LenOfVDiagonal.len_of_v_diagonal grid = Result.ok r ∧
        ((n = 1 ∨ m = 1) →
          ((hasCellOne grid n m → r.val = 1) ∧ (¬ hasCellOne grid n m → r.val = 0))) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n m : ℕ) (hg : isGrid grid n m), ∃ r : Std.I64,
          Aegis.LenOfVDiagonal.len_of_v_diagonal grid = Result.ok r ∧
          ((n = 1 ∨ m = 1) →
            ((hasCellOne grid n m → r.val = 1) ∧ (¬ hasCellOne grid n m → r.val = 0)))) := by
    sorry

  /-- r >= 2 if and only if there exist indices (i,j) and (i',j') such that 0 <= i,i' < n, 0 <= j,j' < m, |i'-i|=1, |j'-j|=1, grid[i][j]=1, and grid[i'][j']=2.
    Preconditions: grid is a non-empty rectangular matrix: len(grid) = n with 1 <= n <= 500, and for every i with 0 <= i < n, len(grid[i]) = m with 1 <= m <= 500, and every entry grid[i][j] is either 0, 1, or 2. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (n m : ℕ) (hg : isGrid grid n m) :
      ∃ r : Std.I64,
        Aegis.LenOfVDiagonal.len_of_v_diagonal grid = Result.ok r ∧
        (2 ≤ r.val ↔ hasDiagOneTwo grid n m) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n m : ℕ) (hg : isGrid grid n m), ∃ r : Std.I64,
          Aegis.LenOfVDiagonal.len_of_v_diagonal grid = Result.ok r ∧
          (2 ≤ r.val ↔ hasDiagOneTwo grid n m)) := by
    sorry

  /-- Let G' be the grid of the same dimensions defined by G'[i][j] = grid[n-1-i][m-1-j] for all 0 <= i < n and 0 <= j < m. Then the value returned by the function on G' equals r.
    Preconditions: grid is a non-empty rectangular matrix: len(grid) = n with 1 <= n <= 500, and for every i with 0 <= i < n, len(grid[i]) = m with 1 <= m <= 500, and every entry grid[i][j] is either 0, 1, or 2. -/
  theorem spec_6 (grid other : Slice (alloc.vec.Vec Std.I64)) (n m : ℕ)
      (hg : isGrid grid n m) (hother : isGrid other n m)
      (hmirror : ∀ i j : ℕ, i < n → j < m →
        cellValue other i j = cellValue grid (n - 1 - i) (m - 1 - j)) :
      ∀ r : Std.I64, Aegis.LenOfVDiagonal.len_of_v_diagonal grid = Result.ok r →
        ∃ r' : Std.I64,
          Aegis.LenOfVDiagonal.len_of_v_diagonal other = Result.ok r' ∧ r'.val = r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid other : Slice (alloc.vec.Vec Std.I64)) (n m : ℕ)
        (hg : isGrid grid n m) (hother : isGrid other n m)
        (hmirror : ∀ i j : ℕ, i < n → j < m →
          cellValue other i j = cellValue grid (n - 1 - i) (m - 1 - j)), ∀ r : Std.I64, Aegis.LenOfVDiagonal.len_of_v_diagonal grid = Result.ok r →
          ∃ r' : Std.I64,
            Aegis.LenOfVDiagonal.len_of_v_diagonal other = Result.ok r' ∧ r'.val = r.val) := by
    sorry

  end AegisSpec.LenOfVDiagonal
