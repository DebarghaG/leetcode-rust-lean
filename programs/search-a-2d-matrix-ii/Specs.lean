import Aegis.SearchMatrix.Code.Funs

/-!
# Specifications of `Aegis.SearchMatrix.search_matrix`

LeetCode problem `search-a-2d-matrix-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SearchMatrix

abbrev MatrixTy : Type := Slice (alloc.vec.Vec Std.I64)

def rowsOf (matrix : MatrixTy) : List (List Int) :=
  matrix.val.map (fun row => row.val.map (fun x => x.val))

def numRows (matrix : MatrixTy) : Nat := matrix.val.length

def numCols (matrix : MatrixTy) : Nat :=
  match rowsOf matrix with
  | [] => 0
  | row :: _ => row.length

def entry (rows : List (List Int)) (i j : Nat) : Option Int :=
  (rows[i]?).bind (fun row => row[j]?)

def inRange (x : Int) : Prop := -1000000000 ≤ x ∧ x ≤ 1000000000

/-- The function returns a result r (it does not fail), and r = true if and only if there exist indices i, j with 0 <= i < m and 0 <= j < n such that matrix[i][j] = target.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). 1 <= m <= 300, 1 <= n <= 300, and len(matrix[i]) = n for every i with 0 <= i < m. For every i, j with 0 <= i < m and 0 <= j < n: -10^9 <= matrix[i][j] <= 10^9; if j + 1 < n then matrix[i][j] <= matrix[i][j+1] (rows are non-decreasing left to right); if i + 1 < m then matrix[i][j] <= matrix[i+1][j] (columns are non-decreasing top to bottom). Also -10^9 <= target <= 10^9. -/
theorem spec_1 (matrix : MatrixTy) (target : Std.I64)
    (hm_ge : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 300)
    (hn_ge : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 300)
    (h_row_len : ∀ row ∈ rowsOf matrix, row.length = numCols matrix)
    (h_range : ∀ i j x, i < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → inRange x)
    (h_row_sorted : ∀ i j x y, i < numRows matrix → j + 1 < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) i (j + 1) = some y →
      x ≤ y)
    (h_col_sorted : ∀ i j x y, i + 1 < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) (i + 1) j = some y →
      x ≤ y)
    (h_target : inRange target.val) :
    ∃ r, Aegis.SearchMatrix.search_matrix matrix target = ok r ∧
      (r = true ↔ ∃ i j, i < numRows matrix ∧ j < numCols matrix ∧
        entry (rowsOf matrix) i j = some target.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (matrix : MatrixTy) (target : Std.I64)
    (hm_ge : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 300)
    (hn_ge : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 300)
    (h_row_len : ∀ row ∈ rowsOf matrix, row.length = numCols matrix)
    (h_range : ∀ i j x, i < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → inRange x)
    (h_row_sorted : ∀ i j x y, i < numRows matrix → j + 1 < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) i (j + 1) = some y →
      x ≤ y)
    (h_col_sorted : ∀ i j x y, i + 1 < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) (i + 1) j = some y →
      x ≤ y)
    (h_target : inRange target.val), ∃ r, Aegis.SearchMatrix.search_matrix matrix target = ok r ∧
      (r = true ↔ ∃ i j, i < numRows matrix ∧ j < numCols matrix ∧
        entry (rowsOf matrix) i j = some target.val)) := by
  sorry

/-- The function returns a result for every input satisfying the preconditions: it never fails, panics, accesses an out-of-bounds index, or performs overflow.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). 1 <= m <= 300, 1 <= n <= 300, and len(matrix[i]) = n for every i with 0 <= i < m. For every i, j with 0 <= i < m and 0 <= j < n: -10^9 <= matrix[i][j] <= 10^9; if j + 1 < n then matrix[i][j] <= matrix[i][j+1]; if i + 1 < m then matrix[i][j] <= matrix[i+1][j]. Also -10^9 <= target <= 10^9. -/
theorem spec_2 (matrix : MatrixTy) (target : Std.I64)
    (hm_ge : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 300)
    (hn_ge : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 300)
    (h_row_len : ∀ row ∈ rowsOf matrix, row.length = numCols matrix)
    (h_range : ∀ i j x, i < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → inRange x)
    (h_row_sorted : ∀ i j x y, i < numRows matrix → j + 1 < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) i (j + 1) = some y →
      x ≤ y)
    (h_col_sorted : ∀ i j x y, i + 1 < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) (i + 1) j = some y →
      x ≤ y)
    (h_target : inRange target.val) :
    ∃ r, Aegis.SearchMatrix.search_matrix matrix target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (matrix : MatrixTy) (target : Std.I64)
    (hm_ge : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 300)
    (hn_ge : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 300)
    (h_row_len : ∀ row ∈ rowsOf matrix, row.length = numCols matrix)
    (h_range : ∀ i j x, i < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → inRange x)
    (h_row_sorted : ∀ i j x y, i < numRows matrix → j + 1 < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) i (j + 1) = some y →
      x ≤ y)
    (h_col_sorted : ∀ i j x y, i + 1 < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) (i + 1) j = some y →
      x ≤ y)
    (h_target : inRange target.val), ∃ r, Aegis.SearchMatrix.search_matrix matrix target = ok r) := by
  sorry

/-- Whenever the function returns a result r with r = true, there exist indices i, j with 0 <= i < m and 0 <= j < n such that matrix[i][j] = target: every true answer is backed by an actual occurrence of target at a concrete position in the matrix.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). 1 <= m <= 300, 1 <= n <= 300, and len(matrix[i]) = n for every i with 0 <= i < m. For every i, j with 0 <= i < m and 0 <= j < n: -10^9 <= matrix[i][j] <= 10^9; if j + 1 < n then matrix[i][j] <= matrix[i][j+1]; if i + 1 < m then matrix[i][j] <= matrix[i+1][j]. Also -10^9 <= target <= 10^9. -/
theorem spec_3 (matrix : MatrixTy) (target : Std.I64)
    (hm_ge : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 300)
    (hn_ge : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 300)
    (h_row_len : ∀ row ∈ rowsOf matrix, row.length = numCols matrix)
    (h_range : ∀ i j x, i < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → inRange x)
    (h_row_sorted : ∀ i j x y, i < numRows matrix → j + 1 < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) i (j + 1) = some y →
      x ≤ y)
    (h_col_sorted : ∀ i j x y, i + 1 < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) (i + 1) j = some y →
      x ≤ y)
    (h_target : inRange target.val) :
    ∀ r, Aegis.SearchMatrix.search_matrix matrix target = ok r → r = true →
      ∃ i j, i < numRows matrix ∧ j < numCols matrix ∧
        entry (rowsOf matrix) i j = some target.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (matrix : MatrixTy) (target : Std.I64)
    (hm_ge : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 300)
    (hn_ge : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 300)
    (h_row_len : ∀ row ∈ rowsOf matrix, row.length = numCols matrix)
    (h_range : ∀ i j x, i < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → inRange x)
    (h_row_sorted : ∀ i j x y, i < numRows matrix → j + 1 < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) i (j + 1) = some y →
      x ≤ y)
    (h_col_sorted : ∀ i j x y, i + 1 < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) (i + 1) j = some y →
      x ≤ y)
    (h_target : inRange target.val), ∀ r, Aegis.SearchMatrix.search_matrix matrix target = ok r → r = true →
      ∃ i j, i < numRows matrix ∧ j < numCols matrix ∧
        entry (rowsOf matrix) i j = some target.val) := by
  sorry

/-- Whenever there exist indices i, j with 0 <= i < m and 0 <= j < n such that matrix[i][j] = target, the function returns a result r with r = true: every occurrence of target in the matrix forces a true answer.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). 1 <= m <= 300, 1 <= n <= 300, and len(matrix[i]) = n for every i with 0 <= i < m. For every i, j with 0 <= i < m and 0 <= j < n: -10^9 <= matrix[i][j] <= 10^9; if j + 1 < n then matrix[i][j] <= matrix[i][j+1]; if i + 1 < m then matrix[i][j] <= matrix[i+1][j]. Also -10^9 <= target <= 10^9. -/
theorem spec_4 (matrix : MatrixTy) (target : Std.I64)
    (hm_ge : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 300)
    (hn_ge : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 300)
    (h_row_len : ∀ row ∈ rowsOf matrix, row.length = numCols matrix)
    (h_range : ∀ i j x, i < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → inRange x)
    (h_row_sorted : ∀ i j x y, i < numRows matrix → j + 1 < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) i (j + 1) = some y →
      x ≤ y)
    (h_col_sorted : ∀ i j x y, i + 1 < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) (i + 1) j = some y →
      x ≤ y)
    (h_target : inRange target.val)
    (h_occurs : ∃ i j, i < numRows matrix ∧ j < numCols matrix ∧
      entry (rowsOf matrix) i j = some target.val) :
    ∃ r, Aegis.SearchMatrix.search_matrix matrix target = ok r ∧ r = true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (matrix : MatrixTy) (target : Std.I64)
    (hm_ge : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 300)
    (hn_ge : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 300)
    (h_row_len : ∀ row ∈ rowsOf matrix, row.length = numCols matrix)
    (h_range : ∀ i j x, i < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → inRange x)
    (h_row_sorted : ∀ i j x y, i < numRows matrix → j + 1 < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) i (j + 1) = some y →
      x ≤ y)
    (h_col_sorted : ∀ i j x y, i + 1 < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) (i + 1) j = some y →
      x ≤ y)
    (h_target : inRange target.val)
    (h_occurs : ∃ i j, i < numRows matrix ∧ j < numCols matrix ∧
      entry (rowsOf matrix) i j = some target.val), ∃ r, Aegis.SearchMatrix.search_matrix matrix target = ok r ∧ r = true) := by
  sorry

/-- For every matrix T with len(T) = n, len(T[j]) = m for every j with 0 <= j < n, and T[j][i] = matrix[i][j] for all i with 0 <= i < m and all j with 0 <= j < n (so T is the transpose of matrix), whenever search_matrix(matrix, target) returns r, the call search_matrix(T, target) returns a result r' with r' = r.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). 1 <= m <= 300, 1 <= n <= 300, and len(matrix[i]) = n for every i with 0 <= i < m. For every i, j with 0 <= i < m and 0 <= j < n: -10^9 <= matrix[i][j] <= 10^9; if j + 1 < n then matrix[i][j] <= matrix[i][j+1]; if i + 1 < m then matrix[i][j] <= matrix[i+1][j]. Also -10^9 <= target <= 10^9. -/
theorem spec_5 (matrix : MatrixTy) (target : Std.I64)
    (hm_ge : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 300)
    (hn_ge : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 300)
    (h_row_len : ∀ row ∈ rowsOf matrix, row.length = numCols matrix)
    (h_range : ∀ i j x, i < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → inRange x)
    (h_row_sorted : ∀ i j x y, i < numRows matrix → j + 1 < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) i (j + 1) = some y →
      x ≤ y)
    (h_col_sorted : ∀ i j x y, i + 1 < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) (i + 1) j = some y →
      x ≤ y)
    (h_target : inRange target.val)
    (T : MatrixTy)
    (hT_len : numRows T = numCols matrix)
    (hT_row_len : ∀ row ∈ rowsOf T, row.length = numRows matrix)
    (hT_transpose : ∀ i j, i < numRows matrix → j < numCols matrix →
      entry (rowsOf T) j i = entry (rowsOf matrix) i j) :
    ∀ r, Aegis.SearchMatrix.search_matrix matrix target = ok r →
      ∃ r', Aegis.SearchMatrix.search_matrix T target = ok r' ∧ r' = r := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (matrix : MatrixTy) (target : Std.I64)
    (hm_ge : 1 ≤ numRows matrix) (hm_le : numRows matrix ≤ 300)
    (hn_ge : 1 ≤ numCols matrix) (hn_le : numCols matrix ≤ 300)
    (h_row_len : ∀ row ∈ rowsOf matrix, row.length = numCols matrix)
    (h_range : ∀ i j x, i < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → inRange x)
    (h_row_sorted : ∀ i j x y, i < numRows matrix → j + 1 < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) i (j + 1) = some y →
      x ≤ y)
    (h_col_sorted : ∀ i j x y, i + 1 < numRows matrix → j < numCols matrix →
      entry (rowsOf matrix) i j = some x → entry (rowsOf matrix) (i + 1) j = some y →
      x ≤ y)
    (h_target : inRange target.val)
    (T : MatrixTy)
    (hT_len : numRows T = numCols matrix)
    (hT_row_len : ∀ row ∈ rowsOf T, row.length = numRows matrix)
    (hT_transpose : ∀ i j, i < numRows matrix → j < numCols matrix →
      entry (rowsOf T) j i = entry (rowsOf matrix) i j), ∀ r, Aegis.SearchMatrix.search_matrix matrix target = ok r →
      ∃ r', Aegis.SearchMatrix.search_matrix T target = ok r' ∧ r' = r) := by
  sorry

end AegisSpec.SearchMatrix
