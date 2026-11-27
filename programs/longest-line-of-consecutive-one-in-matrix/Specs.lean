import Aegis.LongestLine.Code.Funs

/-!
# Specifications of `Aegis.LongestLine.longest_line`

LeetCode problem `longest-line-of-consecutive-one-in-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestLine

  open scoped Classical

  inductive Dir : Type

    | horiz

    | vert

    | diag

    | anti
    deriving DecidableEq, Repr

  namespace Dir

  def di : Dir → ℤ
    | horiz => 0
    | vert => 1
    | diag => 1
    | anti => 1

  def dj : Dir → ℤ
    | horiz => 1
    | vert => 0
    | diag => 1
    | anti => -1

  end Dir

  def cell (mat : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
    ((mat.val[i]?).bind (fun row => (row.val[j]?).map (fun x => x.val))).getD 0

  structure IsBinaryMatrix (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) : Prop where

    m_pos : 1 ≤ m

    n_pos : 1 ≤ n

    rows_len : mat.val.length = m

    row_len : ∀ i : ℕ, i < m →
      ∃ row : alloc.vec.Vec Std.I64, mat.val[i]? = some row ∧ row.val.length = n

    size_ok : m * n ≤ 10000

    binary : ∀ i j : ℕ, i < m → j < n → cell mat i j = 0 ∨ cell mat i j = 1

  def HasLine (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (O : Dir) (i0 j0 k : ℕ) : Prop :=
    ∀ t : ℕ, t < k →
      ∃ i j : ℕ,
        i < m ∧ j < n ∧
        (i : ℤ) = (i0 : ℤ) + O.di * (t : ℤ) ∧
        (j : ℤ) = (j0 : ℤ) + O.dj * (t : ℤ) ∧
        cell mat i j = 1

  noncomputable def maxLineLength (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) : ℕ :=
    Nat.findGreatest
      (fun k => k = 0 ∨ (1 ≤ k ∧ ∃ (O : Dir) (i0 j0 : ℕ), HasLine mat m n O i0 j0 k))
      (m * n)

  noncomputable def maxRun (f : ℕ → ℤ) (L : ℕ) : ℕ :=
    Nat.findGreatest
      (fun k => k = 0 ∨
        ∃ a b : ℕ, a ≤ b ∧ b < L ∧ b - a + 1 = k ∧ ∀ t : ℕ, a ≤ t → t ≤ b → f t = 1)
      L

  def onesCount (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) : ℕ :=
    (((Finset.range m).product (Finset.range n)).filter (fun p : ℕ × ℕ => cell mat p.1 p.2 = 1)).card

  /-- Whenever the function returns a result r, r equals the maximum of the set {0} union {k | k >= 1 and there exist a direction O in {horizontal, vertical, diagonal, anti-diagonal} and a starting cell (i0,j0) such that the k cells (i0 + di(O)*t, j0 + dj(O)*t) for t = 0,...,k-1 are all within bounds and have value 1}, where (di(O),dj(O)) is (0,1) for horizontal, (1,0) for vertical, (1,1) for diagonal, and (1,-1) for anti-diagonal. Equivalently, r is the length of the longest line of consecutive 1s in mat among horizontal, vertical, diagonal, and anti-diagonal lines.
    Preconditions: mat is a nonempty rectangular binary matrix: let m = len(mat) and n = len(mat[0]); m >= 1, n >= 1, every row of mat has length n, m*n <= 10000, and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_1 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n) :
      ∀ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r →
        r.val = (maxLineLength mat m n : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n), ∀ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r →
          r.val = (maxLineLength mat m n : ℤ)) := by
    sorry

  /-- For every mat satisfying the preconditions, the function does not fail; it returns a result r of type i64.
    Preconditions: mat is a nonempty rectangular binary matrix: let m = len(mat) and n = len(mat[0]); m >= 1, n >= 1, every row of mat has length n, m*n <= 10000, and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_2 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n) :
      ∃ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n), ∃ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= max(m,n).
    Preconditions: mat is a nonempty rectangular binary matrix: let m = len(mat) and n = len(mat[0]); m >= 1, n >= 1, every row of mat has length n, m*n <= 10000, and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_3 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n) :
      ∀ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r →
        0 ≤ r.val ∧ r.val ≤ ((max m n : ℕ) : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n), ∀ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r →
          0 ≤ r.val ∧ r.val ≤ ((max m n : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if mat[i][j] = 0 for every i,j with 0 <= i < m and 0 <= j < n.
    Preconditions: mat is a nonempty rectangular binary matrix: let m = len(mat) and n = len(mat[0]); m >= 1, n >= 1, every row of mat has length n, m*n <= 10000, and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_4 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n) :
      ∀ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r →
        (r.val = 0 ↔ ∀ i j : ℕ, i < m → j < n → cell mat i j = 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n), ∀ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r →
          (r.val = 0 ↔ ∀ i j : ℕ, i < m → j < n → cell mat i j = 0)) := by
    sorry

  /-- Whenever the function returns a result r, if mat[i][j] = 1 for every i,j with 0 <= i < m and 0 <= j < n, then r = max(m,n).
    Preconditions: mat is a nonempty rectangular binary matrix: let m = len(mat) and n = len(mat[0]); m >= 1, n >= 1, every row of mat has length n, m*n <= 10000, and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_5 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n) :
      ∀ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r →
        (∀ i j : ℕ, i < m → j < n → cell mat i j = 1) → r.val = ((max m n : ℕ) : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n), ∀ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r →
          (∀ i j : ℕ, i < m → j < n → cell mat i j = 1) → r.val = ((max m n : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if m = 1 then r = max({0} union {b - a + 1 | 0 <= a <= b < n and mat[0][t] = 1 for every t with a <= t <= b}).
    Preconditions: mat is a nonempty rectangular binary matrix: let m = len(mat) and n = len(mat[0]); m >= 1, n >= 1, every row of mat has length n, m*n <= 10000, and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_6 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n) :
      ∀ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r → m = 1 →
        r.val = ((maxRun (fun t => cell mat 0 t) n : ℕ) : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n), ∀ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r → m = 1 →
          r.val = ((maxRun (fun t => cell mat 0 t) n : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if n = 1 then r = max({0} union {b - a + 1 | 0 <= a <= b < m and mat[t][0] = 1 for every t with a <= t <= b}).
    Preconditions: mat is a nonempty rectangular binary matrix: let m = len(mat) and n = len(mat[0]); m >= 1, n >= 1, every row of mat has length n, m*n <= 10000, and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_7 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n) :
      ∀ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r → n = 1 →
        r.val = ((maxRun (fun t => cell mat t 0) m : ℕ) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n), ∀ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r → n = 1 →
          r.val = ((maxRun (fun t => cell mat t 0) m : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, there exist a direction O in {horizontal, vertical, diagonal, anti-diagonal}, a starting cell (i0,j0), and cells (i0 + di(O)*t, j0 + dj(O)*t) for t = 0,...,r-1 that all lie within mat and have value 1, where the direction increments (di(O),dj(O)) are (0,1), (1,0), (1,1), and (1,-1) respectively.
    Preconditions: mat is a nonempty rectangular binary matrix: let m = len(mat) and n = len(mat[0]); m >= 1, n >= 1, every row of mat has length n, m*n <= 10000, and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_8 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n) :
      ∀ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r → 0 < r.val →
        ∃ (O : Dir) (i0 j0 k : ℕ), 1 ≤ k ∧ (k : ℤ) = r.val ∧ HasLine mat m n O i0 j0 k := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n), ∀ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r → 0 < r.val →
          ∃ (O : Dir) (i0 j0 k : ℕ), 1 ≤ k ∧ (k : ℤ) = r.val ∧ HasLine mat m n O i0 j0 k) := by
    sorry

  /-- Whenever the function returns a result r, for every direction O in {horizontal, vertical, diagonal, anti-diagonal}, every starting cell (i0,j0), and every k >= 1 such that the k cells (i0 + di(O)*t, j0 + dj(O)*t) for t = 0,...,k-1 are within bounds and have value 1, we have k <= r, where the direction increments (di(O),dj(O)) are (0,1), (1,0), (1,1), and (1,-1) respectively.
    Preconditions: mat is a nonempty rectangular binary matrix: let m = len(mat) and n = len(mat[0]); m >= 1, n >= 1, every row of mat has length n, m*n <= 10000, and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_9 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n) :
      ∀ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r →
        ∀ (O : Dir) (i0 j0 k : ℕ), 1 ≤ k → HasLine mat m n O i0 j0 k → (k : ℤ) ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n), ∀ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r →
          ∀ (O : Dir) (i0 j0 k : ℕ), 1 ≤ k → HasLine mat m n O i0 j0 k → (k : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= the number of pairs (i,j) with 0 <= i < m and 0 <= j < n such that mat[i][j] = 1.
    Preconditions: mat is a nonempty rectangular binary matrix: let m = len(mat) and n = len(mat[0]); m >= 1, n >= 1, every row of mat has length n, m*n <= 10000, and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_10 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n) :
      ∀ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r →
        r.val ≤ ((onesCount mat m n : ℕ) : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (hmat : IsBinaryMatrix mat m n), ∀ r : Std.I64, Aegis.LongestLine.longest_line mat = ok r →
          r.val ≤ ((onesCount mat m n : ℕ) : ℤ)) := by
    sorry

  /-- longest_line(A) <= longest_line(B). That is, flipping 0-entries to 1 can never decrease the answer.
    Preconditions: A and B are nonempty rectangular binary matrices of the same dimensions m x n (satisfying the constraints), and A[i][j] <= B[i][j] for every 0 <= i < m, 0 <= j < n. -/
  theorem spec_11 (A B : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hA : IsBinaryMatrix A m n) (hB : IsBinaryMatrix B m n)
      (hle : ∀ i j : ℕ, i < m → j < n → cell A i j ≤ cell B i j) :
      ∀ rA rB : Std.I64, Aegis.LongestLine.longest_line A = ok rA →
        Aegis.LongestLine.longest_line B = ok rB → rA.val ≤ rB.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (A B : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hA : IsBinaryMatrix A m n) (hB : IsBinaryMatrix B m n)
        (hle : ∀ i j : ℕ, i < m → j < n → cell A i j ≤ cell B i j), ∀ rA rB : Std.I64, Aegis.LongestLine.longest_line A = ok rA →
          Aegis.LongestLine.longest_line B = ok rB → rA.val ≤ rB.val) := by
    sorry

  /-- longest_line(mat) = longest_line(matT). Transposing swaps horizontal with vertical and preserves both diagonal directions, so the set of achievable line lengths is unchanged.
    Preconditions: mat is a nonempty rectangular binary matrix, and matT is its n x m transpose (matT[j][i] = mat[i][j]). -/
  theorem spec_12 (mat matT : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hmat : IsBinaryMatrix mat m n) (hT : IsBinaryMatrix matT n m)
      (htrans : ∀ i j : ℕ, i < m → j < n → cell matT j i = cell mat i j) :
      ∀ r rT : Std.I64, Aegis.LongestLine.longest_line mat = ok r →
        Aegis.LongestLine.longest_line matT = ok rT → r = rT := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (mat matT : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hmat : IsBinaryMatrix mat m n) (hT : IsBinaryMatrix matT n m)
        (htrans : ∀ i j : ℕ, i < m → j < n → cell matT j i = cell mat i j), ∀ r rT : Std.I64, Aegis.LongestLine.longest_line mat = ok r →
          Aegis.LongestLine.longest_line matT = ok rT → r = rT) := by
    sorry

  /-- longest_line(mat) = longest_line(matR). A 180-degree rotation maps each allowed direction to the same line read in reverse, so no line length changes.
    Preconditions: mat is a nonempty rectangular binary matrix, and matR is mat rotated 180 degrees (matR[i][j] = mat[m-1-i][n-1-j]). -/
  theorem spec_13 (mat matR : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hmat : IsBinaryMatrix mat m n) (hR : IsBinaryMatrix matR m n)
      (hrot : ∀ i j : ℕ, i < m → j < n → cell matR i j = cell mat (m - 1 - i) (n - 1 - j)) :
      ∀ r rR : Std.I64, Aegis.LongestLine.longest_line mat = ok r →
        Aegis.LongestLine.longest_line matR = ok rR → r = rR := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (mat matR : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hmat : IsBinaryMatrix mat m n) (hR : IsBinaryMatrix matR m n)
        (hrot : ∀ i j : ℕ, i < m → j < n → cell matR i j = cell mat (m - 1 - i) (n - 1 - j)), ∀ r rR : Std.I64, Aegis.LongestLine.longest_line mat = ok r →
          Aegis.LongestLine.longest_line matR = ok rR → r = rR) := by
    sorry

  end AegisSpec.LongestLine
