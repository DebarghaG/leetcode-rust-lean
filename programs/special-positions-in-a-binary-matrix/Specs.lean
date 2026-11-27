import Aegis.NumSpecial.Code.Funs

/-!
# Specifications of `Aegis.NumSpecial.num_special`

LeetCode problem `special-positions-in-a-binary-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumSpecial

abbrev Mat : Type := Slice (alloc.vec.Vec I64)

def rowOf (mat : Mat) (i : ℕ) : List ℤ :=
  ((mat.val[i]?).map fun row => row.val.map fun x => x.val).getD []

def entry (mat : Mat) (i j : ℕ) : ℤ := (rowOf mat i).getD j 0

def numRows (mat : Mat) : ℕ := mat.val.length

def numCols (mat : Mat) : ℕ := (rowOf mat 0).length

def rowSum (mat : Mat) (i n : ℕ) : ℤ := ((List.range n).map fun j => entry mat i j).sum

def colSum (mat : Mat) (j m : ℕ) : ℤ := ((List.range m).map fun i => entry mat i j).sum

def IsSpecial (mat : Mat) (m n i j : ℕ) : Prop :=
  entry mat i j = 1 ∧
    (∀ k ∈ List.range n, k ≠ j → entry mat i k = 0) ∧
    (∀ k ∈ List.range m, k ≠ i → entry mat k j = 0)

instance (mat : Mat) (m n i j : ℕ) : Decidable (IsSpecial mat m n i j) := by
  unfold IsSpecial
  infer_instance

def specialPositions (mat : Mat) (m n : ℕ) : List (ℕ × ℕ) :=
  ((List.range m).product (List.range n)).filter fun p => decide (IsSpecial mat m n p.1 p.2)

def specialCount (mat : Mat) (m n : ℕ) : ℕ :=
  (specialPositions mat m n).length

def IsUniqueOneInRow (mat : Mat) (n i j : ℕ) : Prop :=
  j < n ∧ entry mat i j = 1 ∧ ∀ k ∈ List.range n, entry mat i k = 1 → k = j

def IsUniqueOneInCol (mat : Mat) (m j i : ℕ) : Prop :=
  i < m ∧ entry mat i j = 1 ∧ ∀ k ∈ List.range m, entry mat k j = 1 → k = i

instance (mat : Mat) (n i j : ℕ) : Decidable (IsUniqueOneInRow mat n i j) := by
  unfold IsUniqueOneInRow
  infer_instance

instance (mat : Mat) (m j i : ℕ) : Decidable (IsUniqueOneInCol mat m j i) := by
  unfold IsUniqueOneInCol
  infer_instance

def rowsWithExactlyOneOne (mat : Mat) (m n : ℕ) : ℕ :=
  ((List.range m).filter fun i => decide (rowSum mat i n = 1)).length

def colsWithExactlyOneOne (mat : Mat) (m n : ℕ) : ℕ :=
  ((List.range n).filter fun j => decide (colSum mat j m = 1)).length

def RowHasUniqueOneInSingleColumn (mat : Mat) (m n i : ℕ) : Prop :=
  rowSum mat i n = 1 ∧ ∃ j ∈ List.range n, IsUniqueOneInRow mat n i j ∧ colSum mat j m = 1

def ColHasUniqueOneInSingleRow (mat : Mat) (m n j : ℕ) : Prop :=
  colSum mat j m = 1 ∧ ∃ i ∈ List.range m, IsUniqueOneInCol mat m j i ∧ rowSum mat i n = 1

instance (mat : Mat) (m n i : ℕ) : Decidable (RowHasUniqueOneInSingleColumn mat m n i) := by
  unfold RowHasUniqueOneInSingleColumn IsUniqueOneInRow
  infer_instance

instance (mat : Mat) (m n j : ℕ) : Decidable (ColHasUniqueOneInSingleRow mat m n j) := by
  unfold ColHasUniqueOneInSingleRow IsUniqueOneInCol
  infer_instance

def rowsWithUniqueOneInSingleColumn (mat : Mat) (m n : ℕ) : ℕ :=
  ((List.range m).filter fun i => decide (RowHasUniqueOneInSingleColumn mat m n i)).length

def colsWithUniqueOneInSingleRow (mat : Mat) (m n : ℕ) : ℕ :=
  ((List.range n).filter fun j => decide (ColHasUniqueOneInSingleRow mat m n j)).length

/-- The function returns a result r and r equals the number of pairs (i,j) with 0 <= i < m and 0 <= j < n such that mat[i][j] = 1, for every k with 0 <= k < n and k != j mat[i][k] = 0, and for every k with 0 <= k < m and k != i mat[k][j] = 0. In other words, r is the number of special positions in mat.
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 100, 1 <= n <= 100, every row mat[i] for 0 <= i < m has length n, and every entry mat[i][j] for 0 <= i < m and 0 <= j < n is either 0 or 1. -/
theorem spec_1 (mat : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1) :
    ∃ r, Aegis.NumSpecial.num_special mat = ok r ∧ r.val = (specialCount mat m n : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (mat : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1), ∃ r, Aegis.NumSpecial.num_special mat = ok r ∧ r.val = (specialCount mat m n : ℤ)) := by
  sorry

/-- The call num_special mat returns a result r; it does not panic, go out of bounds, or overflow.
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 100, 1 <= n <= 100, every row mat[i] for 0 <= i < m has length n, and every entry mat[i][j] for 0 <= i < m and 0 <= j < n is either 0 or 1. -/
theorem spec_2 (mat : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1) :
    ∃ r, Aegis.NumSpecial.num_special mat = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (mat : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1), ∃ r, Aegis.NumSpecial.num_special mat = ok r) := by
  sorry

/-- Whenever num_special mat returns a result r, 0 <= r <= min(m,n).
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 100, 1 <= n <= 100, every row mat[i] for 0 <= i < m has length n, and every entry mat[i][j] for 0 <= i < m and 0 <= j < n is either 0 or 1. -/
theorem spec_3 (mat : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1) :
    ∀ r, Aegis.NumSpecial.num_special mat = ok r → 0 ≤ r.val ∧ r.val ≤ ((min m n : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (mat : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1), ∀ r, Aegis.NumSpecial.num_special mat = ok r → 0 ≤ r.val ∧ r.val ≤ ((min m n : ℕ) : ℤ)) := by
  sorry

/-- Whenever num_special mat returns a result r, the r positions (i,j) with 0 <= i < m, 0 <= j < n, mat[i][j] = 1, all other entries in row i equal to 0, and all other entries in column j equal to 0 have pairwise distinct row indices and pairwise distinct column indices.
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 100, 1 <= n <= 100, every row mat[i] for 0 <= i < m has length n, and every entry mat[i][j] for 0 <= i < m and 0 <= j < n is either 0 or 1. -/
theorem spec_4 (mat : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1) :
    ∀ r, Aegis.NumSpecial.num_special mat = ok r →
      ((specialPositions mat m n).length : ℤ) = r.val ∧
        ((specialPositions mat m n).map (·.1)).Nodup ∧
        ((specialPositions mat m n).map (·.2)).Nodup := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (mat : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1), ∀ r, Aegis.NumSpecial.num_special mat = ok r →
      ((specialPositions mat m n).length : ℤ) = r.val ∧
        ((specialPositions mat m n).map (·.1)).Nodup ∧
        ((specialPositions mat m n).map (·.2)).Nodup) := by
  sorry

/-- Whenever num_special mat returns a result r, r equals the number of rows i with 0 <= i < m such that sum_{j=0}^{n-1} mat[i][j] = 1 and, letting j be the unique column with mat[i][j] = 1, sum_{k=0}^{m-1} mat[k][j] = 1.
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 100, 1 <= n <= 100, every row mat[i] for 0 <= i < m has length n, and every entry mat[i][j] for 0 <= i < m and 0 <= j < n is either 0 or 1. -/
theorem spec_5 (mat : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1) :
    ∀ r, Aegis.NumSpecial.num_special mat = ok r →
      r.val = (rowsWithUniqueOneInSingleColumn mat m n : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (mat : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1), ∀ r, Aegis.NumSpecial.num_special mat = ok r →
      r.val = (rowsWithUniqueOneInSingleColumn mat m n : ℤ)) := by
  sorry

/-- Whenever num_special mat returns a result r, r <= R1, where R1 is the number of rows i with 0 <= i < m such that row i contains exactly one entry equal to 1.
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 100, 1 <= n <= 100, every row mat[i] for 0 <= i < m has length n, and every entry mat[i][j] for 0 <= i < m and 0 <= j < n is either 0 or 1. -/
theorem spec_6 (mat : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1) :
    ∀ r, Aegis.NumSpecial.num_special mat = ok r →
      r.val ≤ (rowsWithExactlyOneOne mat m n : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (mat : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1), ∀ r, Aegis.NumSpecial.num_special mat = ok r →
      r.val ≤ (rowsWithExactlyOneOne mat m n : ℤ)) := by
  sorry

/-- Whenever num_special mat returns a result r, r <= C1, where C1 is the number of columns j with 0 <= j < n such that column j contains exactly one entry equal to 1.
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 100, 1 <= n <= 100, every row mat[i] for 0 <= i < m has length n, and every entry mat[i][j] for 0 <= i < m and 0 <= j < n is either 0 or 1. -/
theorem spec_7 (mat : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1) :
    ∀ r, Aegis.NumSpecial.num_special mat = ok r →
      r.val ≤ (colsWithExactlyOneOne mat m n : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (mat : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1), ∀ r, Aegis.NumSpecial.num_special mat = ok r →
      r.val ≤ (colsWithExactlyOneOne mat m n : ℤ)) := by
  sorry

/-- Whenever num_special mat returns a result r, if r > 0 then there exist indices i and j with 0 <= i < m and 0 <= j < n such that mat[i][j] = 1, all other entries in row i are 0, and all other entries in column j are 0.
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 100, 1 <= n <= 100, every row mat[i] for 0 <= i < m has length n, and every entry mat[i][j] for 0 <= i < m and 0 <= j < n is either 0 or 1. -/
theorem spec_8 (mat : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1) :
    ∀ r, Aegis.NumSpecial.num_special mat = ok r → 0 < r.val →
      ∃ i j, i < m ∧ j < n ∧ IsSpecial mat m n i j := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (mat : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1), ∀ r, Aegis.NumSpecial.num_special mat = ok r → 0 < r.val →
      ∃ i j, i < m ∧ j < n ∧ IsSpecial mat m n i j) := by
  sorry

/-- Let matT be any matrix with len(matT) = n, every row of matT of length m, and matT[j][i] = mat[i][j] for every 0 <= i < m and 0 <= j < n. Whenever num_special mat returns a result r and num_special matT returns a result rT, r = rT.
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 100, 1 <= n <= 100, every row mat[i] for 0 <= i < m has length n, and every entry mat[i][j] for 0 <= i < m and 0 <= j < n is either 0 or 1. -/
theorem spec_9 (mat matT : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1)
    (hT_len : matT.val.length = n)
    (hT_row : ∀ j, j < n → (rowOf matT j).length = m)
    (hT_transpose : ∀ i j, i < m → j < n → entry matT j i = entry mat i j) :
    ∀ r rT, Aegis.NumSpecial.num_special mat = ok r →
      Aegis.NumSpecial.num_special matT = ok rT → r.val = rT.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (mat matT : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1)
    (hT_len : matT.val.length = n)
    (hT_row : ∀ j, j < n → (rowOf matT j).length = m)
    (hT_transpose : ∀ i j, i < m → j < n → entry matT j i = entry mat i j), ∀ r rT, Aegis.NumSpecial.num_special mat = ok r →
      Aegis.NumSpecial.num_special matT = ok rT → r.val = rT.val) := by
  sorry

/-- Whenever num_special mat returns a result r, r equals the number of columns j with 0 <= j < n such that sum_{i=0}^{m-1} mat[i][j] = 1 and, letting i be the unique row with mat[i][j] = 1, sum_{k=0}^{n-1} mat[i][k] = 1.
  Preconditions: Let m = len(mat) and n = len(mat[0]). Assume 1 <= m <= 100, 1 <= n <= 100, every row mat[i] for 0 <= i < m has length n, and every entry mat[i][j] for 0 <= i < m and 0 <= j < n is either 0 or 1. -/
theorem spec_10 (mat : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1) :
    ∀ r, Aegis.NumSpecial.num_special mat = ok r →
      r.val = (colsWithUniqueOneInSingleRow mat m n : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (mat : Mat) (m n : ℕ)
    (hm : mat.val.length = m) (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
    (hrow : ∀ i, i < m → (rowOf mat i).length = n)
    (hentry : ∀ i j, i < m → j < n → entry mat i j = 0 ∨ entry mat i j = 1), ∀ r, Aegis.NumSpecial.num_special mat = ok r →
      r.val = (colsWithUniqueOneInSingleRow mat m n : ℤ)) := by
  sorry

end AegisSpec.NumSpecial
