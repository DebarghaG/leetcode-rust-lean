import Aegis.MaxIncreasingCells.Code.Funs

/-!
# Specifications of `Aegis.MaxIncreasingCells.max_increasing_cells`

LeetCode problem `maximum-strictly-increasing-cells-in-a-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxIncreasingCells

def cell (mat : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  ((mat.val[i]!).val[j]!).val

def IsValidMatrix (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
  mat.val.length = m ∧
  1 ≤ m ∧ m ≤ 100000 ∧
  1 ≤ n ∧ n ≤ 100000 ∧
  (∀ row ∈ mat.val, row.val.length = n) ∧
  m * n ≤ 100000 ∧
  (∀ row ∈ mat.val, ∀ x ∈ row.val, -100000 ≤ x.val ∧ x.val ≤ 100000)

noncomputable def greatestUpTo (P : Nat → Prop) (b : Nat) : Nat :=
  @Nat.findGreatest P (Classical.decPred P) b

def Step (mat : Slice (alloc.vec.Vec Std.I64)) (c d : Nat × Nat) : Prop :=
  (c.1 = d.1 ∨ c.2 = d.2) ∧ cell mat c.1 c.2 < cell mat d.1 d.2

def IsValidSeq (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (s : List (Nat × Nat)) : Prop :=
  (∀ c ∈ s, c.1 < m ∧ c.2 < n) ∧
  (∀ p ∈ s.zip s.tail, Step mat p.1 p.2)

noncomputable def maxSeqLen (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Nat :=
  greatestUpTo (fun k => ∃ s : List (Nat × Nat), IsValidSeq mat m n s ∧ s.length = k) (m * n)

def distinctEntries (mat : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  (mat.val.flatMap (fun row => row.val)).dedup.length

def rowDistinct (mat : Slice (alloc.vec.Vec Std.I64)) (n i : Nat) : Nat :=
  ((List.range n).map (fun j => cell mat i j)).dedup.length

def colDistinct (mat : Slice (alloc.vec.Vec Std.I64)) (m j : Nat) : Nat :=
  ((List.range m).map (fun i => cell mat i j)).dedup.length

noncomputable def dpCell (mat : Slice (alloc.vec.Vec Std.I64)) (m n i j : Nat) : Nat :=
  greatestUpTo
    (fun k => ∃ s : List (Nat × Nat), IsValidSeq mat m n s ∧ s.getLast? = some (i, j) ∧
      s.length = k) (m * n)

noncomputable def dpRowMax (mat : Slice (alloc.vec.Vec Std.I64)) (m n i j : Nat) : Nat :=
  greatestUpTo (fun M => ∃ l, l < n ∧ cell mat i l < cell mat i j ∧ dpCell mat m n i l = M)
    (m * n)

noncomputable def dpColMax (mat : Slice (alloc.vec.Vec Std.I64)) (m n i j : Nat) : Nat :=
  greatestUpTo (fun M => ∃ k, k < m ∧ cell mat k j < cell mat i j ∧ dpCell mat m n k j = M)
    (m * n)

noncomputable def dpOverall (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Nat :=
  greatestUpTo (fun M => ∃ i, i < m ∧ ∃ j, j < n ∧ dpCell mat m n i j = M) (m * n)

def IsTranspose (mat matT : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
  matT.val.length = n ∧
  (∀ row ∈ matT.val, row.val.length = m) ∧
  (∀ i, i < m → ∀ j, j < n → cell matT j i = cell mat i j)

/-- Let m = len(mat) and n = len(mat[0]). A valid cell sequence of length k is a sequence of cell indices (i_0,j_0),...,(i_{k-1},j_{k-1}) such that 0 <= i_t < m and 0 <= j_t < n for every t, and for every t with 0 <= t < k-1, (i_t = i_{t+1} or j_t = j_{t+1}) and mat[i_t][j_t] < mat[i_{t+1}][j_{t+1}]. A single cell is a valid sequence of length 1. Let L be the largest k for which a valid cell sequence of length k exists. Whenever the function returns a result r, r = L.
  Preconditions: Let m = len(mat) and n = len(mat[0]). The matrix is non-empty and rectangular: 1 <= m <= 100000, 1 <= n <= 100000, every row of mat has length n, m*n <= 100000, and every entry mat[i][j] with 0 <= i < m and 0 <= j < n satisfies -100000 <= mat[i][j] <= 100000. -/
theorem spec_1 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n) :
    ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      r.val = (maxSeqLen mat m n : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n), ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      r.val = (maxSeqLen mat m n : Int)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; equivalently, it does not fail by panic, arithmetic overflow, or out-of-bounds access.
  Preconditions: Let m = len(mat) and n = len(mat[0]). The matrix is non-empty and rectangular: 1 <= m <= 100000, 1 <= n <= 100000, every row of mat has length n, m*n <= 100000, and every entry mat[i][j] with 0 <= i < m and 0 <= j < n satisfies -100000 <= mat[i][j] <= 100000. -/
theorem spec_2 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n) :
    ∃ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n), ∃ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r <= m*n.
  Preconditions: Let m = len(mat) and n = len(mat[0]). The matrix is non-empty and rectangular: 1 <= m <= 100000, 1 <= n <= 100000, every row of mat has length n, m*n <= 100000, and every entry mat[i][j] with 0 <= i < m and 0 <= j < n satisfies -100000 <= mat[i][j] <= 100000. -/
theorem spec_3 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n) :
    ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      1 ≤ r.val ∧ r.val ≤ ((m * n : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n), ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      1 ≤ r.val ∧ r.val ≤ ((m * n : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r <= D, where D is the number of distinct values among all entries mat[i][j] with 0 <= i < m and 0 <= j < n.
  Preconditions: Let m = len(mat) and n = len(mat[0]). The matrix is non-empty and rectangular: 1 <= m <= 100000, 1 <= n <= 100000, every row of mat has length n, m*n <= 100000, and every entry mat[i][j] with 0 <= i < m and 0 <= j < n satisfies -100000 <= mat[i][j] <= 100000. -/
theorem spec_4 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n) :
    ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      r.val ≤ (distinctEntries mat : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n), ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      r.val ≤ (distinctEntries mat : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if all entries of mat are equal, that is, mat[i][j] = mat[0][0] for every 0 <= i < m and 0 <= j < n.
  Preconditions: Let m = len(mat) and n = len(mat[0]). The matrix is non-empty and rectangular: 1 <= m <= 100000, 1 <= n <= 100000, every row of mat has length n, m*n <= 100000, and every entry mat[i][j] with 0 <= i < m and 0 <= j < n satisfies -100000 <= mat[i][j] <= 100000. -/
theorem spec_5 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n) :
    ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      (r.val = 1 ↔ ∀ i, i < m → ∀ j, j < n → cell mat i j = cell mat 0 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n), ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      (r.val = 1 ↔ ∀ i, i < m → ∀ j, j < n → cell mat i j = cell mat 0 0)) := by
  sorry

/-- Whenever the function returns a result r, r = max_{0 <= j < n} d_j, where d_j is the number of distinct values among mat[0][j], mat[1][j], ..., mat[m-1][j].
  Preconditions: Let m = len(mat) and n = len(mat[0]). The matrix is non-empty and rectangular: 1 <= m <= 100000, 1 <= n <= 100000, every row of mat has length n, m*n <= 100000, and every entry mat[i][j] satisfies -100000 <= mat[i][j] <= 100000. In addition, every row is constant: for every 0 <= i < m and 0 <= j < n, mat[i][j] = mat[i][0]. -/
theorem spec_6 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n)
    (hrow : ∀ i, i < m → ∀ j, j < n → cell mat i j = cell mat i 0) :
    ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      (∀ j, j < n → (colDistinct mat m j : Int) ≤ r.val) ∧
      (∃ j, j < n ∧ r.val = (colDistinct mat m j : Int)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n)
    (hrow : ∀ i, i < m → ∀ j, j < n → cell mat i j = cell mat i 0), ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      (∀ j, j < n → (colDistinct mat m j : Int) ≤ r.val) ∧
      (∃ j, j < n ∧ r.val = (colDistinct mat m j : Int))) := by
  sorry

/-- Whenever the function returns a result r, r = max_{0 <= i < m} e_i, where e_i is the number of distinct values among mat[i][0], mat[i][1], ..., mat[i][n-1].
  Preconditions: Let m = len(mat) and n = len(mat[0]). The matrix is non-empty and rectangular: 1 <= m <= 100000, 1 <= n <= 100000, every row of mat has length n, m*n <= 100000, and every entry mat[i][j] satisfies -100000 <= mat[i][j] <= 100000. In addition, every column is constant: for every 0 <= i < m and 0 <= j < n, mat[i][j] = mat[0][j]. -/
theorem spec_7 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n)
    (hcol : ∀ i, i < m → ∀ j, j < n → cell mat i j = cell mat 0 j) :
    ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      (∀ i, i < m → (rowDistinct mat n i : Int) ≤ r.val) ∧
      (∃ i, i < m ∧ r.val = (rowDistinct mat n i : Int)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n)
    (hcol : ∀ i, i < m → ∀ j, j < n → cell mat i j = cell mat 0 j), ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      (∀ i, i < m → (rowDistinct mat n i : Int) ≤ r.val) ∧
      (∃ i, i < m ∧ r.val = (rowDistinct mat n i : Int))) := by
  sorry

/-- Let matT be the n x m matrix defined by matT[j][i] = mat[i][j] for 0 <= i < m and 0 <= j < n. Whenever the function returns a result r on input mat and a result rT on input matT, r = rT.
  Preconditions: Let m = len(mat) and n = len(mat[0]). The matrix is non-empty and rectangular: 1 <= m <= 100000, 1 <= n <= 100000, every row of mat has length n, m*n <= 100000, and every entry mat[i][j] satisfies -100000 <= mat[i][j] <= 100000. -/
theorem spec_8 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n) (matT : Slice (alloc.vec.Vec Std.I64))
    (hT : IsTranspose mat matT m n) :
    ∀ r rT, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      Aegis.MaxIncreasingCells.max_increasing_cells matT = ok rT → r = rT := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n) (matT : Slice (alloc.vec.Vec Std.I64))
    (hT : IsTranspose mat matT m n), ∀ r rT, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      Aegis.MaxIncreasingCells.max_increasing_cells matT = ok rT → r = rT) := by
  sorry

/-- Let alpha be any bijection from {0,...,m-1} to itself and beta any bijection from {0,...,n-1} to itself. Let matP be the m x n matrix defined by matP[i][j] = mat[alpha(i)][beta(j)]. Whenever the function returns a result r on input mat and a result rP on input matP, r = rP.
  Preconditions: Let m = len(mat) and n = len(mat[0]). The matrix is non-empty and rectangular: 1 <= m <= 100000, 1 <= n <= 100000, every row of mat has length n, m*n <= 100000, and every entry mat[i][j] satisfies -100000 <= mat[i][j] <= 100000. -/
theorem spec_9 (mat matP : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n)
    (alpha beta : Nat → Nat)
    (halpha_maps : ∀ i, i < m → alpha i < m)
    (halpha_inj : ∀ i, i < m → ∀ k, k < m → alpha i = alpha k → i = k)
    (hbeta_maps : ∀ j, j < n → beta j < n)
    (hbeta_inj : ∀ j, j < n → ∀ l, l < n → beta j = beta l → j = l)
    (hP_shape : matP.val.length = m ∧ ∀ row ∈ matP.val, row.val.length = n)
    (hP_cell : ∀ i, i < m → ∀ j, j < n → cell matP i j = cell mat (alpha i) (beta j)) :
    ∀ r rP, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      Aegis.MaxIncreasingCells.max_increasing_cells matP = ok rP → r = rP := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (mat matP : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n)
    (alpha beta : Nat → Nat)
    (halpha_maps : ∀ i, i < m → alpha i < m)
    (halpha_inj : ∀ i, i < m → ∀ k, k < m → alpha i = alpha k → i = k)
    (hbeta_maps : ∀ j, j < n → beta j < n)
    (hbeta_inj : ∀ j, j < n → ∀ l, l < n → beta j = beta l → j = l)
    (hP_shape : matP.val.length = m ∧ ∀ row ∈ matP.val, row.val.length = n)
    (hP_cell : ∀ i, i < m → ∀ j, j < n → cell matP i j = cell mat (alpha i) (beta j)), ∀ r rP, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      Aegis.MaxIncreasingCells.max_increasing_cells matP = ok rP → r = rP) := by
  sorry

/-- Let mat2 be another valid m x n matrix satisfying the same bounds on its entries. If for all 0 <= i,k < m and 0 <= j,l < n, mat[i][j] < mat[k][l] if and only if mat2[i][j] < mat2[k][l], then whenever the function returns a result r on input mat and a result r2 on input mat2, r = r2.
  Preconditions: Let m = len(mat) and n = len(mat[0]). The matrix is non-empty and rectangular: 1 <= m <= 100000, 1 <= n <= 100000, every row of mat has length n, m*n <= 100000, and every entry mat[i][j] satisfies -100000 <= mat[i][j] <= 100000. -/
theorem spec_10 (mat mat2 : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n) (hmat2 : IsValidMatrix mat2 m n)
    (hord : ∀ i, i < m → ∀ k, k < m → ∀ j, j < n → ∀ l, l < n →
      (cell mat i j < cell mat k l ↔ cell mat2 i j < cell mat2 k l)) :
    ∀ r r2, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      Aegis.MaxIncreasingCells.max_increasing_cells mat2 = ok r2 → r = r2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (mat mat2 : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n) (hmat2 : IsValidMatrix mat2 m n)
    (hord : ∀ i, i < m → ∀ k, k < m → ∀ j, j < n → ∀ l, l < n →
      (cell mat i j < cell mat k l ↔ cell mat2 i j < cell mat2 k l)), ∀ r r2, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      Aegis.MaxIncreasingCells.max_increasing_cells mat2 = ok r2 → r = r2) := by
  sorry

/-- Let drow_i be the number of distinct values among mat[i][0],...,mat[i][n-1] for 0 <= i < m, and let dcol_j be the number of distinct values among mat[0][j],...,mat[m-1][j] for 0 <= j < n. Let D = max( {drow_i : 0 <= i < m} union {dcol_j : 0 <= j < n} ). Whenever the function returns a result r, r >= D.
  Preconditions: Let m = len(mat) and n = len(mat[0]). The matrix is non-empty and rectangular: 1 <= m <= 100000, 1 <= n <= 100000, every row of mat has length n, m*n <= 100000, and every entry mat[i][j] satisfies -100000 <= mat[i][j] <= 100000. -/
theorem spec_11 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n) :
    ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      (∀ i, i < m → (rowDistinct mat n i : Int) ≤ r.val) ∧
      (∀ j, j < n → (colDistinct mat m j : Int) ≤ r.val) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n), ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      (∀ i, i < m → (rowDistinct mat n i : Int) ≤ r.val) ∧
      (∀ j, j < n → (colDistinct mat m j : Int) ≤ r.val)) := by
  sorry

/-- Whenever the function returns a result r, there exist cells (i_0,j_0),...,(i_{r-1},j_{r-1}) such that 0 <= i_t < m and 0 <= j_t < n for every 0 <= t < r, and for every 0 <= t < r-1, (i_t = i_{t+1} or j_t = j_{t+1}) and mat[i_t][j_t] < mat[i_{t+1}][j_{t+1}].
  Preconditions: Let m = len(mat) and n = len(mat[0]). The matrix is non-empty and rectangular: 1 <= m <= 100000, 1 <= n <= 100000, every row of mat has length n, m*n <= 100000, and every entry mat[i][j] satisfies -100000 <= mat[i][j] <= 100000. -/
theorem spec_12 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n) :
    ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      ∃ s : List (Nat × Nat), IsValidSeq mat m n s ∧ r.val = (s.length : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n), ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      ∃ s : List (Nat × Nat), IsValidSeq mat m n s ∧ r.val = (s.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every k >= 0 and every sequence of cells (i_0,j_0),...,(i_{k-1},j_{k-1}) satisfying 0 <= i_t < m and 0 <= j_t < n for all t, and for every 0 <= t < k-1, (i_t = i_{t+1} or j_t = j_{t+1}) and mat[i_t][j_t] < mat[i_{t+1}][j_{t+1}], we have k <= r.
  Preconditions: Let m = len(mat) and n = len(mat[0]). The matrix is non-empty and rectangular: 1 <= m <= 100000, 1 <= n <= 100000, every row of mat has length n, m*n <= 100000, and every entry mat[i][j] satisfies -100000 <= mat[i][j] <= 100000. -/
theorem spec_13 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n) :
    ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      ∀ s : List (Nat × Nat), IsValidSeq mat m n s → (s.length : Int) ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n), ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      ∀ s : List (Nat × Nat), IsValidSeq mat m n s → (s.length : Int) ≤ r.val) := by
  sorry

/-- For 0 <= i < m and 0 <= j < n, let dp(i,j) be the maximum length of a valid cell sequence ending at cell (i,j). Then dp(i,j) = 1 + max( { dp(i,l) | 0 <= l < n and mat[i][l] < mat[i][j] } union { dp(k,j) | 0 <= k < m and mat[k][j] < mat[i][j] } ), where the maximum of the empty set is 0. Whenever the function returns a result r, r = max_{0 <= i < m, 0 <= j < n} dp(i,j).
  Preconditions: Let m = len(mat) and n = len(mat[0]). The matrix is non-empty and rectangular: 1 <= m <= 100000, 1 <= n <= 100000, every row of mat has length n, m*n <= 100000, and every entry mat[i][j] with 0 <= i < m and 0 <= j < n satisfies -100000 <= mat[i][j] <= 100000. -/
theorem spec_14 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n) :
    ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      (∀ i, i < m → ∀ j, j < n →
        dpCell mat m n i j = 1 + max (dpRowMax mat m n i j) (dpColMax mat m n i j)) ∧
      r.val = (dpOverall mat m n : Int) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hmat : IsValidMatrix mat m n), ∀ r, Aegis.MaxIncreasingCells.max_increasing_cells mat = ok r →
      (∀ i, i < m → ∀ j, j < n →
        dpCell mat m n i j = 1 + max (dpRowMax mat m n i j) (dpColMax mat m n i j)) ∧
      r.val = (dpOverall mat m n : Int)) := by
  sorry

end AegisSpec.MaxIncreasingCells
