import Aegis.MatrixBlockSum.Code.Funs

/-!
# Specifications of `Aegis.MatrixBlockSum.matrix_block_sum`

LeetCode problem `matrix-block-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MatrixBlockSum

open Aegis.MatrixBlockSum (matrix_block_sum)

def rowVals (row : alloc.vec.Vec Std.I64) : List ℤ := row.val.map (fun x => x.val)

def cell (rows : List (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
  (rowVals (rows.getD i (alloc.vec.Vec.new Std.I64))).getD j 0

def matCell (mat : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ := cell mat.val i j

def rowLen (rows : List (alloc.vec.Vec Std.I64)) (i : ℕ) : ℕ :=
  (rows.getD i (alloc.vec.Vec.new Std.I64)).val.length

def firstRowLen (mat : Slice (alloc.vec.Vec Std.I64)) : ℕ := rowLen mat.val 0

def kNat (k : Std.I64) : ℕ := k.val.toNat

def window (len k i : ℕ) : ℤ := ((min (len - 1) (i + k) - (i - k) + 1 : ℕ) : ℤ)

def blockSum (mat : Slice (alloc.vec.Vec Std.I64)) (m n k : ℕ) (i j : ℕ) : ℤ :=
  ∑ a ∈ Finset.Icc (i - k) (min (m - 1) (i + k)),
    ∑ b ∈ Finset.Icc (j - k) (min (n - 1) (j + k)), matCell mat a b

def rowBandSum (mat : Slice (alloc.vec.Vec Std.I64)) (m n k : ℕ) (i : ℕ) : ℤ :=
  ∑ a ∈ Finset.Icc (i - k) (min (m - 1) (i + k)),
    ∑ b ∈ Finset.range n, matCell mat a b

def colBandSum (mat : Slice (alloc.vec.Vec Std.I64)) (m n k : ℕ) (j : ℕ) : ℤ :=
  ∑ a ∈ Finset.range m,
    ∑ b ∈ Finset.Icc (j - k) (min (n - 1) (j + k)), matCell mat a b

def totalSum (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) : ℤ :=
  ∑ a ∈ Finset.range m, ∑ b ∈ Finset.range n, matCell mat a b

/-- Whenever the function returns a result r, len(r) = m, for every i with 0 <= i < m we have len(r[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] = sum_{a = max(0, i-k)}^{min(m-1, i+k)} sum_{b = max(0, j-k)}^{min(n-1, j+k)} mat[a][b].
  Preconditions: Let m = len(mat) and n = len(mat[0]). The slice mat is nonempty, every row of mat has length n, 1 <= m,n <= 100, 0 <= k <= 100, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
theorem spec_1 (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100) :
    ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n → cell r.val i j = blockSum mat m n (kNat k) i j) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100), ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n → cell r.val i j = blockSum mat m n (kNat k) i j)) := by
  sorry

/-- The function returns a result r; it does not fail.
  Preconditions: Let m = len(mat) and n = len(mat[0]). The slice mat is nonempty, every row of mat has length n, 1 <= m,n <= 100, 0 <= k <= 100, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
theorem spec_2 (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100) :
    ∃ r, matrix_block_sum mat k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100), ∃ r, matrix_block_sum mat k = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(mat) and for every i with 0 <= i < len(mat), len(r[i]) = len(mat[i]).
  Preconditions: Let m = len(mat) and n = len(mat[0]). The slice mat is nonempty, every row of mat has length n, 1 <= m,n <= 100, 0 <= k <= 100, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
theorem spec_3 (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100) :
    ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = mat.val.length ∧
      (∀ i, i < mat.val.length → rowLen r.val i = rowLen mat.val i) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100), ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = mat.val.length ∧
      (∀ i, i < mat.val.length → rowLen r.val i = rowLen mat.val i)) := by
  sorry

/-- Whenever the function returns a result r, len(r) = m, each row of r has length n, and for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] >= mat[i][j].
  Preconditions: Let m = len(mat) and n = len(mat[0]). The slice mat is nonempty, every row of mat has length n, 1 <= m,n <= 100, 0 <= k <= 100, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
theorem spec_4 (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100) :
    ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n → matCell mat i j ≤ cell r.val i j) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100), ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n → matCell mat i j ≤ cell r.val i j)) := by
  sorry

/-- Whenever the function returns a result r, len(r) = m, each row of r has length n, and for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] <= T, where T = sum_{a=0}^{m-1} sum_{b=0}^{n-1} mat[a][b].
  Preconditions: Let m = len(mat) and n = len(mat[0]). The slice mat is nonempty, every row of mat has length n, 1 <= m,n <= 100, 0 <= k <= 100, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
theorem spec_5 (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100) :
    ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n → cell r.val i j ≤ totalSum mat m n) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100), ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n → cell r.val i j ≤ totalSum mat m n)) := by
  sorry

/-- Whenever the function returns a result r, len(r) = m, each row of r has length n, and sum_{i=0}^{m-1} sum_{j=0}^{n-1} r[i][j] = sum_{a=0}^{m-1} sum_{b=0}^{n-1} mat[a][b] * (min(m-1, a+k) - max(0, a-k) + 1) * (min(n-1, b+k) - max(0, b-k) + 1).
  Preconditions: Let m = len(mat) and n = len(mat[0]). The slice mat is nonempty, every row of mat has length n, 1 <= m,n <= 100, 0 <= k <= 100, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
theorem spec_6 (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100) :
    ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, cell r.val i j) =
        ∑ a ∈ Finset.range m, ∑ b ∈ Finset.range n,
          matCell mat a b * window m (kNat k) a * window n (kNat k) b := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100), ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, cell r.val i j) =
        ∑ a ∈ Finset.range m, ∑ b ∈ Finset.range n,
          matCell mat a b * window m (kNat k) a * window n (kNat k) b) := by
  sorry

/-- Whenever the function returns a result r, len(r) = m, each row of r has length n, and for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] = c * (min(m-1, i+k) - max(0, i-k) + 1) * (min(n-1, j+k) - max(0, j-k) + 1).
  Preconditions: Let m = len(mat) and n = len(mat[0]). The slice mat is nonempty, every row of mat has length n, 1 <= m,n <= 100, 0 <= k <= 100, for every i,j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100, and there exists an integer c such that for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] = c. -/
theorem spec_7 (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ) (c : ℤ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100)
    (hconst : ∀ i j, i < m → j < n → matCell mat i j = c) :
    ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n →
        cell r.val i j = c * window m (kNat k) i * window n (kNat k) j) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ) (c : ℤ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100)
    (hconst : ∀ i j, i < m → j < n → matCell mat i j = c), ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n →
        cell r.val i j = c * window m (kNat k) i * window n (kNat k) j)) := by
  sorry

/-- Whenever the function returns a result r, len(r) = m, each row of r has length n, and for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] = r[i][n-1-j].
  Preconditions: Let m = len(mat) and n = len(mat[0]). The slice mat is nonempty, every row of mat has length n, 1 <= m,n <= 100, 0 <= k <= 100, for every i,j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100, and for every i with 0 <= i < m and j with 0 <= j < n, mat[i][j] = mat[i][n-1-j]. -/
theorem spec_8 (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100)
    (hsymm : ∀ i j, i < m → j < n → matCell mat i j = matCell mat i (n - 1 - j)) :
    ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n → cell r.val i j = cell r.val i (n - 1 - j)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100)
    (hsymm : ∀ i j, i < m → j < n → matCell mat i j = matCell mat i (n - 1 - j)), ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n → cell r.val i j = cell r.val i (n - 1 - j))) := by
  sorry

/-- Whenever the function returns a result r, len(r) = m, each row of r has length n, and for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] = r[j][i].
  Preconditions: Let m = len(mat) and n = len(mat[0]). The slice mat is nonempty, every row of mat has length n, 1 <= m,n <= 100, 0 <= k <= 100, for every i,j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100, m = n, and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] = mat[j][i]. -/
theorem spec_9 (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100)
    (hmn : m = n) (hsymm : ∀ i j, i < m → j < n → matCell mat i j = matCell mat j i) :
    ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n → cell r.val i j = cell r.val j i) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100)
    (hmn : m = n) (hsymm : ∀ i j, i < m → j < n → matCell mat i j = matCell mat j i), ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n → cell r.val i j = cell r.val j i)) := by
  sorry

/-- Whenever the function returns a result r, len(r) = m, each row of r has length n, and for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] = S_i, where S_i = sum_{a = max(0, i-k)}^{min(m-1, i+k)} sum_{b=0}^{n-1} mat[a][b].
  Preconditions: Let m = len(mat) and n = len(mat[0]). The slice mat is nonempty, every row of mat has length n, 1 <= m,n <= 100, 0 <= k <= 100, n - 1 <= k, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
theorem spec_10 (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100)
    (hnk : n - 1 ≤ kNat k) :
    ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n → cell r.val i j = rowBandSum mat m n (kNat k) i) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100)
    (hnk : n - 1 ≤ kNat k), ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n → cell r.val i j = rowBandSum mat m n (kNat k) i)) := by
  sorry

/-- Whenever the function returns a result r, len(r) = m, each row of r has length n, and for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] = C_j, where C_j = sum_{a=0}^{m-1} sum_{b = max(0, j-k)}^{min(n-1, j+k)} mat[a][b].
  Preconditions: Let m = len(mat) and n = len(mat[0]). The slice mat is nonempty, every row of mat has length n, 1 <= m,n <= 100, 0 <= k <= 100, m - 1 <= k, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
theorem spec_11 (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100)
    (hmk : m - 1 ≤ kNat k) :
    ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n → cell r.val i j = colBandSum mat m n (kNat k) j) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100)
    (hmk : m - 1 ≤ kNat k), ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n → cell r.val i j = colBandSum mat m n (kNat k) j)) := by
  sorry

/-- Whenever the function returns a result r, len(r) = m, each row of r has length n, and for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] <= 100 * (min(m-1, i+k) - max(0, i-k) + 1) * (min(n-1, j+k) - max(0, j-k) + 1).
  Preconditions: Let m = len(mat) and n = len(mat[0]). The slice mat is nonempty, every row of mat has length n, 1 <= m,n <= 100, 0 <= k <= 100, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
theorem spec_12 (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100) :
    ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n →
        cell r.val i j ≤ 100 * window m (kNat k) i * window n (kNat k) j) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100), ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n →
        cell r.val i j ≤ 100 * window m (kNat k) i * window n (kNat k) j)) := by
  sorry

/-- Whenever the function returns a result r, len(r) = m, each row of r has length n, and for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] >= (min(m-1, i+k) - max(0, i-k) + 1) * (min(n-1, j+k) - max(0, j-k) + 1).
  Preconditions: Let m = len(mat) and n = len(mat[0]). The slice mat is nonempty, every row of mat has length n, 1 <= m,n <= 100, 0 <= k <= 100, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
theorem spec_13 (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100) :
    ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n →
        window m (kNat k) i * window n (kNat k) j ≤ cell r.val i j) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100), ∀ r, matrix_block_sum mat k = ok r →
      r.val.length = m ∧
      (∀ i, i < m → rowLen r.val i = n) ∧
      (∀ i j, i < m → j < n →
        window m (kNat k) i * window n (kNat k) j ≤ cell r.val i j)) := by
  sorry

/-- Whenever the function returns r1 for k1 and r2 for k2, len(r1) = len(r2) = m, every row of r1 and r2 has length n, and for every i,j with 0 <= i < m and 0 <= j < n, r1[i][j] <= r2[i][j].
  Preconditions: Let m = len(mat) and n = len(mat[0]). The slice mat is nonempty, every row of mat has length n, 1 <= m,n <= 100, 0 <= k1 <= k2 <= 100, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
theorem spec_14 (mat : Slice (alloc.vec.Vec Std.I64)) (k1 k2 : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk1_0 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_100 : k2.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100) :
    ∀ r1 r2, matrix_block_sum mat k1 = ok r1 → matrix_block_sum mat k2 = ok r2 →
      r1.val.length = m ∧
      r2.val.length = m ∧
      (∀ i, i < m → rowLen r1.val i = n ∧ rowLen r2.val i = n) ∧
      (∀ i j, i < m → j < n → cell r1.val i j ≤ cell r2.val i j) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (k1 k2 : Std.I64) (m n : ℕ)
    (hne : mat.val ≠ []) (hm : m = mat.val.length) (hn : n = firstRowLen mat)
    (hm1 : 1 ≤ m) (hm100 : m ≤ 100) (hn1 : 1 ≤ n) (hn100 : n ≤ 100)
    (hrows : ∀ row, row ∈ mat.val → row.val.length = n)
    (hk1_0 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_100 : k2.val ≤ 100)
    (hentries : ∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100), ∀ r1 r2, matrix_block_sum mat k1 = ok r1 → matrix_block_sum mat k2 = ok r2 →
      r1.val.length = m ∧
      r2.val.length = m ∧
      (∀ i, i < m → rowLen r1.val i = n ∧ rowLen r2.val i = n) ∧
      (∀ i j, i < m → j < n → cell r1.val i j ≤ cell r2.val i j)) := by
  sorry

end AegisSpec.MatrixBlockSum
