import Aegis.DiagonalSum.Code.Funs

/-!
# Specifications of `Aegis.DiagonalSum.diagonal_sum`

LeetCode problem `matrix-diagonal-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DiagonalSum

open scoped BigOperators

abbrev Mat := Slice (alloc.vec.Vec I64)

def entry (mat : List (alloc.vec.Vec I64)) (i j : ℕ) : ℤ :=
  match mat[i]? with
  | none => 0
  | some row => (row.val[j]?).map (fun x => x.val) |>.getD 0

def mainDiagSum (mat : List (alloc.vec.Vec I64)) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, entry mat i i

def antiDiagSum (mat : List (alloc.vec.Vec I64)) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, entry mat i (n - 1 - i)

def centerEntry (mat : List (alloc.vec.Vec I64)) (n : ℕ) : ℤ :=
  if n % 2 = 1 then entry mat ((n - 1) / 2) ((n - 1) / 2) else 0

def diagCount (n : ℕ) : ℕ := 2 * n - if n % 2 = 1 then 1 else 0

def IsTransposeOf (matT mat : List (alloc.vec.Vec I64)) (n : ℕ) : Prop :=
  ∀ i j : ℕ, i < n → j < n → entry matT i j = entry mat j i

def IsRot180Of (matR mat : List (alloc.vec.Vec I64)) (n : ℕ) : Prop :=
  ∀ i j : ℕ, i < n → j < n → entry matR i j = entry mat (n - 1 - i) (n - 1 - j)

def IsRowsReversedOf (matRowsRev mat : List (alloc.vec.Vec I64)) (n : ℕ) : Prop :=
  ∀ i j : ℕ, i < n → j < n → entry matRowsRev i j = entry mat (n - 1 - i) j

def AgreesOnDiagonals (mat2 mat : List (alloc.vec.Vec I64)) (n : ℕ) : Prop :=
  ∀ i j : ℕ, i < n → j < n → (j = i ∨ j = n - 1 - i) → entry mat i j = entry mat2 i j

def DiagonalsLe (mat2 mat : List (alloc.vec.Vec I64)) (n : ℕ) : Prop :=
  ∀ i j : ℕ, i < n → j < n → (j = i ∨ j = n - 1 - i) → entry mat i j ≤ entry mat2 i j

/-- Whenever diagonal_sum(mat) returns a result r, r = P + S - C, where P = sum over i from 0 to n-1 of mat[i][i], S = sum over i from 0 to n-1 of mat[i][n-1-i], and C = mat[(n-1)/2][(n-1)/2] if n is odd, or C = 0 if n is even.
  Preconditions: Let n = len(mat). Assume 1 <= n <= 100; for every i with 0 <= i < n, len(mat[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, 1 <= mat[i][j] <= 100. All indices below are 0-based. -/
theorem spec_1 (mat : Mat)
    (hn_pos : 1 ≤ mat.val.length) (hn_le : mat.val.length ≤ 100)
    (hrows : ∀ (i : ℕ) (hi : i < mat.val.length),
      (mat.val.get ⟨i, hi⟩).val.length = mat.val.length)
    (hentries : ∀ i j : ℕ, i < mat.val.length → j < mat.val.length →
      1 ≤ entry mat.val i j ∧ entry mat.val i j ≤ 100)
    (r : I64) (hr : Aegis.DiagonalSum.diagonal_sum mat = ok r) :
    r.val = mainDiagSum mat.val mat.val.length + antiDiagSum mat.val mat.val.length
      - centerEntry mat.val mat.val.length := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (mat : Mat)
    (hn_pos : 1 ≤ mat.val.length) (hn_le : mat.val.length ≤ 100)
    (hrows : ∀ (i : ℕ) (hi : i < mat.val.length),
      (mat.val.get ⟨i, hi⟩).val.length = mat.val.length)
    (hentries : ∀ i j : ℕ, i < mat.val.length → j < mat.val.length →
      1 ≤ entry mat.val i j ∧ entry mat.val i j ≤ 100)
    (r : I64) (hr : Aegis.DiagonalSum.diagonal_sum mat = ok r), r.val = mainDiagSum mat.val mat.val.length + antiDiagSum mat.val mat.val.length
      - centerEntry mat.val mat.val.length) := by
  sorry

/-- Under these preconditions, diagonal_sum(mat) returns a result r; it does not fail due to out-of-bounds indexing, arithmetic overflow, panic, or any other runtime error.
  Preconditions: Let n = len(mat). Assume 1 <= n <= 100; for every i with 0 <= i < n, len(mat[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
theorem spec_2 (mat : Mat)
    (hn_pos : 1 ≤ mat.val.length) (hn_le : mat.val.length ≤ 100)
    (hrows : ∀ (i : ℕ) (hi : i < mat.val.length),
      (mat.val.get ⟨i, hi⟩).val.length = mat.val.length)
    (hentries : ∀ i j : ℕ, i < mat.val.length → j < mat.val.length →
      1 ≤ entry mat.val i j ∧ entry mat.val i j ≤ 100) :
    ∃ r : I64, Aegis.DiagonalSum.diagonal_sum mat = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (mat : Mat)
    (hn_pos : 1 ≤ mat.val.length) (hn_le : mat.val.length ≤ 100)
    (hrows : ∀ (i : ℕ) (hi : i < mat.val.length),
      (mat.val.get ⟨i, hi⟩).val.length = mat.val.length)
    (hentries : ∀ i j : ℕ, i < mat.val.length → j < mat.val.length →
      1 ≤ entry mat.val i j ∧ entry mat.val i j ≤ 100), ∃ r : I64, Aegis.DiagonalSum.diagonal_sum mat = ok r) := by
  sorry

/-- Let m = 2*n - (1 if n is odd else 0). Whenever diagonal_sum(mat) returns r, m <= r <= 100*m.
  Preconditions: Let n = len(mat). Assume 1 <= n <= 100; for every i with 0 <= i < n, len(mat[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
theorem spec_3 (mat : Mat)
    (hn_pos : 1 ≤ mat.val.length) (hn_le : mat.val.length ≤ 100)
    (hrows : ∀ (i : ℕ) (hi : i < mat.val.length),
      (mat.val.get ⟨i, hi⟩).val.length = mat.val.length)
    (hentries : ∀ i j : ℕ, i < mat.val.length → j < mat.val.length →
      1 ≤ entry mat.val i j ∧ entry mat.val i j ≤ 100)
    (r : I64) (hr : Aegis.DiagonalSum.diagonal_sum mat = ok r) :
    (diagCount mat.val.length : ℤ) ≤ r.val
      ∧ r.val ≤ 100 * (diagCount mat.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (mat : Mat)
    (hn_pos : 1 ≤ mat.val.length) (hn_le : mat.val.length ≤ 100)
    (hrows : ∀ (i : ℕ) (hi : i < mat.val.length),
      (mat.val.get ⟨i, hi⟩).val.length = mat.val.length)
    (hentries : ∀ i j : ℕ, i < mat.val.length → j < mat.val.length →
      1 ≤ entry mat.val i j ∧ entry mat.val i j ≤ 100)
    (r : I64) (hr : Aegis.DiagonalSum.diagonal_sum mat = ok r), (diagCount mat.val.length : ℤ) ≤ r.val
      ∧ r.val ≤ 100 * (diagCount mat.val.length : ℤ)) := by
  sorry

/-- Let matT be the n by n matrix defined by matT[i][j] = mat[j][i] for 0 <= i,j < n. Whenever diagonal_sum(mat) returns r and diagonal_sum(matT) returns rT, r = rT.
  Preconditions: Let n = len(mat). Assume 1 <= n <= 100; for every i with 0 <= i < n, len(mat[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, 1 <= mat[i][j] <= 100. All indices below are 0-based. -/
theorem spec_4 (mat matT : Mat)
    (hn_pos : 1 ≤ mat.val.length) (hn_le : mat.val.length ≤ 100)
    (hrows : ∀ (i : ℕ) (hi : i < mat.val.length),
      (mat.val.get ⟨i, hi⟩).val.length = mat.val.length)
    (hentries : ∀ i j : ℕ, i < mat.val.length → j < mat.val.length →
      1 ≤ entry mat.val i j ∧ entry mat.val i j ≤ 100)
    (hnT : matT.val.length = mat.val.length)
    (hrowsT : ∀ (i : ℕ) (hi : i < matT.val.length),
      (matT.val.get ⟨i, hi⟩).val.length = matT.val.length)
    (hT : IsTransposeOf matT.val mat.val mat.val.length)
    (r rT : I64)
    (hr : Aegis.DiagonalSum.diagonal_sum mat = ok r)
    (hrT : Aegis.DiagonalSum.diagonal_sum matT = ok rT) :
    r.val = rT.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (mat matT : Mat)
    (hn_pos : 1 ≤ mat.val.length) (hn_le : mat.val.length ≤ 100)
    (hrows : ∀ (i : ℕ) (hi : i < mat.val.length),
      (mat.val.get ⟨i, hi⟩).val.length = mat.val.length)
    (hentries : ∀ i j : ℕ, i < mat.val.length → j < mat.val.length →
      1 ≤ entry mat.val i j ∧ entry mat.val i j ≤ 100)
    (hnT : matT.val.length = mat.val.length)
    (hrowsT : ∀ (i : ℕ) (hi : i < matT.val.length),
      (matT.val.get ⟨i, hi⟩).val.length = matT.val.length)
    (hT : IsTransposeOf matT.val mat.val mat.val.length)
    (r rT : I64)
    (hr : Aegis.DiagonalSum.diagonal_sum mat = ok r)
    (hrT : Aegis.DiagonalSum.diagonal_sum matT = ok rT), r.val = rT.val) := by
  sorry

/-- Let matR be the n by n matrix defined by matR[i][j] = mat[n-1-i][n-1-j] for 0 <= i,j < n. Whenever diagonal_sum(mat) returns r and diagonal_sum(matR) returns rR, r = rR.
  Preconditions: Let n = len(mat). Assume 1 <= n <= 100; for every i with 0 <= i < n, len(mat[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, 1 <= mat[i][j] <= 100. All indices below are 0-based. -/
theorem spec_5 (mat matR : Mat)
    (hn_pos : 1 ≤ mat.val.length) (hn_le : mat.val.length ≤ 100)
    (hrows : ∀ (i : ℕ) (hi : i < mat.val.length),
      (mat.val.get ⟨i, hi⟩).val.length = mat.val.length)
    (hentries : ∀ i j : ℕ, i < mat.val.length → j < mat.val.length →
      1 ≤ entry mat.val i j ∧ entry mat.val i j ≤ 100)
    (hnR : matR.val.length = mat.val.length)
    (hrowsR : ∀ (i : ℕ) (hi : i < matR.val.length),
      (matR.val.get ⟨i, hi⟩).val.length = matR.val.length)
    (hR : IsRot180Of matR.val mat.val mat.val.length)
    (r rR : I64)
    (hr : Aegis.DiagonalSum.diagonal_sum mat = ok r)
    (hrR : Aegis.DiagonalSum.diagonal_sum matR = ok rR) :
    r.val = rR.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (mat matR : Mat)
    (hn_pos : 1 ≤ mat.val.length) (hn_le : mat.val.length ≤ 100)
    (hrows : ∀ (i : ℕ) (hi : i < mat.val.length),
      (mat.val.get ⟨i, hi⟩).val.length = mat.val.length)
    (hentries : ∀ i j : ℕ, i < mat.val.length → j < mat.val.length →
      1 ≤ entry mat.val i j ∧ entry mat.val i j ≤ 100)
    (hnR : matR.val.length = mat.val.length)
    (hrowsR : ∀ (i : ℕ) (hi : i < matR.val.length),
      (matR.val.get ⟨i, hi⟩).val.length = matR.val.length)
    (hR : IsRot180Of matR.val mat.val mat.val.length)
    (r rR : I64)
    (hr : Aegis.DiagonalSum.diagonal_sum mat = ok r)
    (hrR : Aegis.DiagonalSum.diagonal_sum matR = ok rR), r.val = rR.val) := by
  sorry

/-- Let matRowsRev be the n by n matrix defined by matRowsRev[i][j] = mat[n-1-i][j] for 0 <= i,j < n. Whenever diagonal_sum(mat) returns r and diagonal_sum(matRowsRev) returns rRowsRev, r = rRowsRev.
  Preconditions: Let n = len(mat). Assume 1 <= n <= 100; for every i with 0 <= i < n, len(mat[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, 1 <= mat[i][j] <= 100. All indices below are 0-based. -/
theorem spec_6 (mat matRowsRev : Mat)
    (hn_pos : 1 ≤ mat.val.length) (hn_le : mat.val.length ≤ 100)
    (hrows : ∀ (i : ℕ) (hi : i < mat.val.length),
      (mat.val.get ⟨i, hi⟩).val.length = mat.val.length)
    (hentries : ∀ i j : ℕ, i < mat.val.length → j < mat.val.length →
      1 ≤ entry mat.val i j ∧ entry mat.val i j ≤ 100)
    (hnRowsRev : matRowsRev.val.length = mat.val.length)
    (hrowsRowsRev : ∀ (i : ℕ) (hi : i < matRowsRev.val.length),
      (matRowsRev.val.get ⟨i, hi⟩).val.length = matRowsRev.val.length)
    (hRowsRev : IsRowsReversedOf matRowsRev.val mat.val mat.val.length)
    (r rRowsRev : I64)
    (hr : Aegis.DiagonalSum.diagonal_sum mat = ok r)
    (hrRowsRev : Aegis.DiagonalSum.diagonal_sum matRowsRev = ok rRowsRev) :
    r.val = rRowsRev.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (mat matRowsRev : Mat)
    (hn_pos : 1 ≤ mat.val.length) (hn_le : mat.val.length ≤ 100)
    (hrows : ∀ (i : ℕ) (hi : i < mat.val.length),
      (mat.val.get ⟨i, hi⟩).val.length = mat.val.length)
    (hentries : ∀ i j : ℕ, i < mat.val.length → j < mat.val.length →
      1 ≤ entry mat.val i j ∧ entry mat.val i j ≤ 100)
    (hnRowsRev : matRowsRev.val.length = mat.val.length)
    (hrowsRowsRev : ∀ (i : ℕ) (hi : i < matRowsRev.val.length),
      (matRowsRev.val.get ⟨i, hi⟩).val.length = matRowsRev.val.length)
    (hRowsRev : IsRowsReversedOf matRowsRev.val mat.val mat.val.length)
    (r rRowsRev : I64)
    (hr : Aegis.DiagonalSum.diagonal_sum mat = ok r)
    (hrRowsRev : Aegis.DiagonalSum.diagonal_sum matRowsRev = ok rRowsRev), r.val = rRowsRev.val) := by
  sorry

/-- Whenever diagonal_sum(mat) returns r and diagonal_sum(mat2) returns r2, r = r2.
  Preconditions: Let n = len(mat). Assume 1 <= n <= 100; for every i with 0 <= i < n, len(mat[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, 1 <= mat[i][j] <= 100. Let mat2 be any slice of vectors with len(mat2)=n, len(mat2[i])=n for every 0 <= i < n, and 1 <= mat2[i][j] <= 100 for every 0 <= i,j < n. Suppose that for every i,j with 0 <= i < n and 0 <= j < n and (j = i or j = n-1-i), mat[i][j] = mat2[i][j]. All indices are 0-based. -/
theorem spec_7 (mat mat2 : Mat)
    (hn_pos : 1 ≤ mat.val.length) (hn_le : mat.val.length ≤ 100)
    (hrows : ∀ (i : ℕ) (hi : i < mat.val.length),
      (mat.val.get ⟨i, hi⟩).val.length = mat.val.length)
    (hentries : ∀ i j : ℕ, i < mat.val.length → j < mat.val.length →
      1 ≤ entry mat.val i j ∧ entry mat.val i j ≤ 100)
    (hn2 : mat2.val.length = mat.val.length)
    (hrows2 : ∀ (i : ℕ) (hi : i < mat2.val.length),
      (mat2.val.get ⟨i, hi⟩).val.length = mat2.val.length)
    (hentries2 : ∀ i j : ℕ, i < mat2.val.length → j < mat2.val.length →
      1 ≤ entry mat2.val i j ∧ entry mat2.val i j ≤ 100)
    (hdiag : AgreesOnDiagonals mat2.val mat.val mat.val.length)
    (r r2 : I64)
    (hr : Aegis.DiagonalSum.diagonal_sum mat = ok r)
    (hr2 : Aegis.DiagonalSum.diagonal_sum mat2 = ok r2) :
    r.val = r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (mat mat2 : Mat)
    (hn_pos : 1 ≤ mat.val.length) (hn_le : mat.val.length ≤ 100)
    (hrows : ∀ (i : ℕ) (hi : i < mat.val.length),
      (mat.val.get ⟨i, hi⟩).val.length = mat.val.length)
    (hentries : ∀ i j : ℕ, i < mat.val.length → j < mat.val.length →
      1 ≤ entry mat.val i j ∧ entry mat.val i j ≤ 100)
    (hn2 : mat2.val.length = mat.val.length)
    (hrows2 : ∀ (i : ℕ) (hi : i < mat2.val.length),
      (mat2.val.get ⟨i, hi⟩).val.length = mat2.val.length)
    (hentries2 : ∀ i j : ℕ, i < mat2.val.length → j < mat2.val.length →
      1 ≤ entry mat2.val i j ∧ entry mat2.val i j ≤ 100)
    (hdiag : AgreesOnDiagonals mat2.val mat.val mat.val.length)
    (r r2 : I64)
    (hr : Aegis.DiagonalSum.diagonal_sum mat = ok r)
    (hr2 : Aegis.DiagonalSum.diagonal_sum mat2 = ok r2), r.val = r2.val) := by
  sorry

/-- Whenever diagonal_sum(mat) returns r and diagonal_sum(mat2) returns r2, r <= r2.
  Preconditions: Let n = len(mat). Assume 1 <= n <= 100; for every i with 0 <= i < n, len(mat[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, 1 <= mat[i][j] <= 100. Let mat2 be any slice of vectors with len(mat2)=n, len(mat2[i])=n for every 0 <= i < n, and 1 <= mat2[i][j] <= 100 for every 0 <= i,j < n. Suppose that for every i,j with 0 <= i < n and 0 <= j < n and (j = i or j = n-1-i), mat[i][j] <= mat2[i][j]. All indices are 0-based. -/
theorem spec_8 (mat mat2 : Mat)
    (hn_pos : 1 ≤ mat.val.length) (hn_le : mat.val.length ≤ 100)
    (hrows : ∀ (i : ℕ) (hi : i < mat.val.length),
      (mat.val.get ⟨i, hi⟩).val.length = mat.val.length)
    (hentries : ∀ i j : ℕ, i < mat.val.length → j < mat.val.length →
      1 ≤ entry mat.val i j ∧ entry mat.val i j ≤ 100)
    (hn2 : mat2.val.length = mat.val.length)
    (hrows2 : ∀ (i : ℕ) (hi : i < mat2.val.length),
      (mat2.val.get ⟨i, hi⟩).val.length = mat2.val.length)
    (hentries2 : ∀ i j : ℕ, i < mat2.val.length → j < mat2.val.length →
      1 ≤ entry mat2.val i j ∧ entry mat2.val i j ≤ 100)
    (hm_le : DiagonalsLe mat2.val mat.val mat.val.length)
    (r r2 : I64)
    (hr : Aegis.DiagonalSum.diagonal_sum mat = ok r)
    (hr2 : Aegis.DiagonalSum.diagonal_sum mat2 = ok r2) :
    r.val ≤ r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (mat mat2 : Mat)
    (hn_pos : 1 ≤ mat.val.length) (hn_le : mat.val.length ≤ 100)
    (hrows : ∀ (i : ℕ) (hi : i < mat.val.length),
      (mat.val.get ⟨i, hi⟩).val.length = mat.val.length)
    (hentries : ∀ i j : ℕ, i < mat.val.length → j < mat.val.length →
      1 ≤ entry mat.val i j ∧ entry mat.val i j ≤ 100)
    (hn2 : mat2.val.length = mat.val.length)
    (hrows2 : ∀ (i : ℕ) (hi : i < mat2.val.length),
      (mat2.val.get ⟨i, hi⟩).val.length = mat2.val.length)
    (hentries2 : ∀ i j : ℕ, i < mat2.val.length → j < mat2.val.length →
      1 ≤ entry mat2.val i j ∧ entry mat2.val i j ≤ 100)
    (hm_le : DiagonalsLe mat2.val mat.val mat.val.length)
    (r r2 : I64)
    (hr : Aegis.DiagonalSum.diagonal_sum mat = ok r)
    (hr2 : Aegis.DiagonalSum.diagonal_sum mat2 = ok r2), r.val ≤ r2.val) := by
  sorry

end AegisSpec.DiagonalSum
