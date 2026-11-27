import Aegis.IsToeplitzMatrix.Code.Funs

/-!
# Specifications of `Aegis.IsToeplitzMatrix.is_toeplitz_matrix`

LeetCode problem `toeplitz-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsToeplitzMatrix

def nrows (matrix : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  matrix.val.length

def entry (matrix : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  match matrix.val[i]? with
  | none => 0
  | some row =>
    match row.val[j]? with
    | none => 0
    | some x => x.val

def rowLen (matrix : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Nat :=
  match matrix.val[i]? with
  | none => 0
  | some row => row.val.length

def transposeEntry (matrix : Slice (alloc.vec.Vec Std.I64)) (a b : Nat) : Int :=
  entry matrix b a

def rot180Entry (matrix : Slice (alloc.vec.Vec Std.I64)) (n i j : Nat) : Int :=
  entry matrix (nrows matrix - 1 - i) (n - 1 - j)

def IsToeplitz (M : Nat → Nat → Int) (rows cols : Nat) : Prop :=
  ∀ i j k, i < rows → j < cols → i + k < rows → j + k < cols → M i j = M (i + k) (j + k)

def validInput (matrix : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Prop :=
  1 ≤ nrows matrix ∧
  nrows matrix ≤ 20 ∧
  1 ≤ n ∧ n ≤ 20 ∧
  (∀ i, i < nrows matrix → rowLen matrix i = n) ∧
  (∀ i j, i < nrows matrix → j < n → 0 ≤ entry matrix i j ∧ entry matrix i j ≤ 99)

/-- Whenever the function returns a result r, r = true if and only if for every i, j, k with 0 <= i < m, 0 <= j < n, k >= 0, i + k < m, and j + k < n, matrix[i][j] = matrix[i+k][j+k].
  Preconditions: Let m = len(matrix). The input satisfies the problem constraints: m >= 1; there exists an integer n with 1 <= n <= 20 such that every row matrix[i] has length n for 0 <= i < m; m <= 20; and every entry satisfies 0 <= matrix[i][j] <= 99 for 0 <= i < m and 0 <= j < n. -/
theorem spec_1 (matrix : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (h : validInput matrix n) :
    ∀ r, Aegis.IsToeplitzMatrix.is_toeplitz_matrix matrix = ok r →
      (r = true ↔
        ∀ i j k, i < matrix.val.length → j < n →
          i + k < matrix.val.length → j + k < n →
          entry matrix i j = entry matrix (i + k) (j + k)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (h : validInput matrix n), ∀ r, Aegis.IsToeplitzMatrix.is_toeplitz_matrix matrix = ok r →
      (r = true ↔
        ∀ i j k, i < matrix.val.length → j < n →
          i + k < matrix.val.length → j + k < n →
          entry matrix i j = entry matrix (i + k) (j + k))) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: Let m = len(matrix). The input satisfies the problem constraints: m >= 1; there exists an integer n with 1 <= n <= 20 such that every row matrix[i] has length n for 0 <= i < m; m <= 20; and every entry satisfies 0 <= matrix[i][j] <= 99 for 0 <= i < m and 0 <= j < n. -/
theorem spec_2 (matrix : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (h : validInput matrix n) :
    ∃ r, Aegis.IsToeplitzMatrix.is_toeplitz_matrix matrix = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (h : validInput matrix n), ∃ r, Aegis.IsToeplitzMatrix.is_toeplitz_matrix matrix = ok r) := by
  sorry

/-- Whenever the function returns a result r, if for every i and j with 0 <= i < m - 1 and 0 <= j < n - 1 we have matrix[i][j] = matrix[i+1][j+1], then r = true.
  Preconditions: Let m = len(matrix). The input satisfies the problem constraints: m >= 1; there exists an integer n with 1 <= n <= 20 such that every row matrix[i] has length n for 0 <= i < m; m <= 20; and every entry satisfies 0 <= matrix[i][j] <= 99 for 0 <= i < m and 0 <= j < n. -/
theorem spec_3 (matrix : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (h : validInput matrix n) :
    ∀ r, Aegis.IsToeplitzMatrix.is_toeplitz_matrix matrix = ok r →
      (∀ i j, i < matrix.val.length - 1 → j < n - 1 →
        entry matrix i j = entry matrix (i + 1) (j + 1)) →
      r = true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (h : validInput matrix n), ∀ r, Aegis.IsToeplitzMatrix.is_toeplitz_matrix matrix = ok r →
      (∀ i j, i < matrix.val.length - 1 → j < n - 1 →
        entry matrix i j = entry matrix (i + 1) (j + 1)) →
      r = true) := by
  sorry

/-- Whenever the function returns a result r, r = false if and only if there exist i and j with 0 <= i < m - 1 and 0 <= j < n - 1 such that matrix[i][j] != matrix[i+1][j+1].
  Preconditions: Let m = len(matrix). The input satisfies the problem constraints: m >= 1; there exists an integer n with 1 <= n <= 20 such that every row matrix[i] has length n for 0 <= i < m; m <= 20; and every entry satisfies 0 <= matrix[i][j] <= 99 for 0 <= i < m and 0 <= j < n. -/
theorem spec_4 (matrix : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (h : validInput matrix n) :
    ∀ r, Aegis.IsToeplitzMatrix.is_toeplitz_matrix matrix = ok r →
      (r = false ↔
        ∃ i j, i < matrix.val.length - 1 ∧ j < n - 1 ∧
          entry matrix i j ≠ entry matrix (i + 1) (j + 1)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (h : validInput matrix n), ∀ r, Aegis.IsToeplitzMatrix.is_toeplitz_matrix matrix = ok r →
      (r = false ↔
        ∃ i j, i < matrix.val.length - 1 ∧ j < n - 1 ∧
          entry matrix i j ≠ entry matrix (i + 1) (j + 1))) := by
  sorry

/-- Whenever the function returns a result r, r = true.
  Preconditions: Let m = len(matrix). The input satisfies the problem constraints: m >= 1; there exists an integer n with 1 <= n <= 20 such that every row matrix[i] has length n for 0 <= i < m; m <= 20; and every entry satisfies 0 <= matrix[i][j] <= 99 for 0 <= i < m and 0 <= j < n. In addition, m = 1. -/
theorem spec_5 (matrix : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (h : validInput matrix n) (hm : matrix.val.length = 1) :
    ∀ r, Aegis.IsToeplitzMatrix.is_toeplitz_matrix matrix = ok r → r = true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (h : validInput matrix n) (hm : matrix.val.length = 1), ∀ r, Aegis.IsToeplitzMatrix.is_toeplitz_matrix matrix = ok r → r = true) := by
  sorry

/-- Whenever the function returns a result r and r = true, then for every i and j with 0 <= i < m and 0 <= j < n: if i <= j then matrix[i][j] = matrix[0][j-i], and if i > j then matrix[i][j] = matrix[i-j][0].
  Preconditions: Let m = len(matrix). The input satisfies the problem constraints: m >= 1; there exists an integer n with 1 <= n <= 20 such that every row matrix[i] has length n for 0 <= i < m; m <= 20; and every entry satisfies 0 <= matrix[i][j] <= 99 for 0 <= i < m and 0 <= j < n. -/
theorem spec_6 (matrix : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (h : validInput matrix n) :
    ∀ r, Aegis.IsToeplitzMatrix.is_toeplitz_matrix matrix = ok r → r = true →
      ∀ i j, i < matrix.val.length → j < n →
        (i ≤ j → entry matrix i j = entry matrix 0 (j - i)) ∧
        (i > j → entry matrix i j = entry matrix (i - j) 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (h : validInput matrix n), ∀ r, Aegis.IsToeplitzMatrix.is_toeplitz_matrix matrix = ok r → r = true →
      ∀ i j, i < matrix.val.length → j < n →
        (i ≤ j → entry matrix i j = entry matrix 0 (j - i)) ∧
        (i > j → entry matrix i j = entry matrix (i - j) 0)) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if the n by m transpose B, defined by B[a][b] = matrix[b][a] for 0 <= a < n and 0 <= b < m, is Toeplitz: for every a, b, k with 0 <= a < n, 0 <= b < m, k >= 0, a + k < n, and b + k < m, B[a][b] = B[a+k][b+k].
  Preconditions: Let m = len(matrix). The input satisfies the problem constraints: m >= 1; there exists an integer n with 1 <= n <= 20 such that every row matrix[i] has length n for 0 <= i < m; m <= 20; and every entry satisfies 0 <= matrix[i][j] <= 99 for 0 <= i < m and 0 <= j < n. -/
theorem spec_7 (matrix : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (h : validInput matrix n) :
    ∀ r, Aegis.IsToeplitzMatrix.is_toeplitz_matrix matrix = ok r →
      (r = true ↔ IsToeplitz (transposeEntry matrix) n matrix.val.length) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (h : validInput matrix n), ∀ r, Aegis.IsToeplitzMatrix.is_toeplitz_matrix matrix = ok r →
      (r = true ↔ IsToeplitz (transposeEntry matrix) n matrix.val.length)) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if the 180-degree rotation C, defined by C[i][j] = matrix[m-1-i][n-1-j] for 0 <= i < m and 0 <= j < n, is Toeplitz: for every i, j, k with 0 <= i < m, 0 <= j < n, k >= 0, i + k < m, and j + k < n, C[i][j] = C[i+k][j+k].
  Preconditions: Let m = len(matrix). The input satisfies the problem constraints: m >= 1; there exists an integer n with 1 <= n <= 20 such that every row matrix[i] has length n for 0 <= i < m; m <= 20; and every entry satisfies 0 <= matrix[i][j] <= 99 for 0 <= i < m and 0 <= j < n. -/
theorem spec_8 (matrix : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (h : validInput matrix n) :
    ∀ r, Aegis.IsToeplitzMatrix.is_toeplitz_matrix matrix = ok r →
      (r = true ↔ IsToeplitz (rot180Entry matrix n) matrix.val.length n) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (h : validInput matrix n), ∀ r, Aegis.IsToeplitzMatrix.is_toeplitz_matrix matrix = ok r →
      (r = true ↔ IsToeplitz (rot180Entry matrix n) matrix.val.length n)) := by
  sorry

end AegisSpec.IsToeplitzMatrix
