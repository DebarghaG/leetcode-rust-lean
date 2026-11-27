import Aegis.NumSubmatrixSumTarget.Code.Funs

/-!
# Specifications of `Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target`

LeetCode problem `number-of-submatrices-that-sum-to-target`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open scoped BigOperators

namespace AegisSpec.NumSubmatrixSumTarget

def row (matrix : Slice (alloc.vec.Vec I64)) (i : Nat) : List I64 :=
  match matrix.val[i]? with
  | some v => v.val
  | none => []

def entry (matrix : Slice (alloc.vec.Vec I64)) (i j : Nat) : Int :=
  match (row matrix i)[j]? with
  | some x => x.val
  | none => 0

def rectSum (matrix : Slice (alloc.vec.Vec I64)) (x1 x2 y1 y2 : Nat) : Int :=
  ∑ i ∈ Finset.Icc x1 x2, ∑ j ∈ Finset.Icc y1 y2, entry matrix i j

def countSubrectangles (matrix : Slice (alloc.vec.Vec I64)) (target : Int) (m n : Nat) : Nat :=
  ((((Finset.range m).product (Finset.range m)).product
        ((Finset.range n).product (Finset.range n))).filter
      (fun q : (Nat × Nat) × (Nat × Nat) =>
        q.1.1 ≤ q.1.2 ∧ q.2.1 ≤ q.2.2 ∧ rectSum matrix q.1.1 q.1.2 q.2.1 q.2.2 = target)).card

def numIndexPairs (k : Nat) : Nat :=
  k * (k + 1) / 2

def numSubrectangles (m n : Nat) : Nat :=
  numIndexPairs m * numIndexPairs n

def countEntriesEq (matrix : Slice (alloc.vec.Vec I64)) (target : Int) (m n : Nat) : Nat :=
  (((Finset.range m).product (Finset.range n)).filter
      (fun p : Nat × Nat => entry matrix p.1 p.2 = target)).card

def matrixSum (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat) : Int :=
  ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, entry matrix i j

def countRowRanges (matrix : Slice (alloc.vec.Vec I64)) (target : Int) (n : Nat) : Nat :=
  (((Finset.range n).product (Finset.range n)).filter
      (fun p : Nat × Nat =>
        p.1 ≤ p.2 ∧ (∑ j ∈ Finset.Icc p.1 p.2, entry matrix 0 j) = target)).card

def countColRanges (matrix : Slice (alloc.vec.Vec I64)) (target : Int) (m : Nat) : Nat :=
  (((Finset.range m).product (Finset.range m)).filter
      (fun p : Nat × Nat =>
        p.1 ≤ p.2 ∧ (∑ i ∈ Finset.Icc p.1 p.2, entry matrix i 0) = target)).card

def IsRowFlip (matrixR matrix : Slice (alloc.vec.Vec I64)) (m n : Nat) : Prop :=
  matrixR.val.length = m ∧
    (∀ i, i < m → (row matrixR i).length = n) ∧
    (∀ i j, i < m → j < n → entry matrixR i j = entry matrix (m - 1 - i) j)

def IsColFlip (matrixC matrix : Slice (alloc.vec.Vec I64)) (m n : Nat) : Prop :=
  matrixC.val.length = m ∧
    (∀ i, i < m → (row matrixC i).length = n) ∧
    (∀ i j, i < m → j < n → entry matrixC i j = entry matrix i (n - 1 - j))

def IsNeg (matrixN matrix : Slice (alloc.vec.Vec I64)) (m n : Nat) : Prop :=
  matrixN.val.length = m ∧
    (∀ i, i < m → (row matrixN i).length = n) ∧
    (∀ i j, i < m → j < n → entry matrixN i j = -entry matrix i j)

def IsTranspose (matrixT matrix : Slice (alloc.vec.Vec I64)) (m n : Nat) : Prop :=
  matrixT.val.length = n ∧
    (∀ i, i < n → (row matrixT i).length = m) ∧
    (∀ i j, i < n → j < m → entry matrixT i j = entry matrix j i)

/-- Whenever the function returns a result r, r equals the number of quadruples (x1,y1,x2,y2) of integers such that 0 <= x1 <= x2 < m, 0 <= y1 <= y2 < n, and sum_{i=x1}^{x2} sum_{j=y1}^{y2} matrix[i][j] = target.
  Preconditions: m = len(matrix) >= 1; n = len(matrix[0]) >= 1; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= matrix[i][j] <= 1000; -10^8 <= target <= 10^8. -/
theorem spec_1
    (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000) :
    ∀ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      r.val = (countSubrectangles matrix target.val m n : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000), ∀ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      r.val = (countSubrectangles matrix target.val m n : Int)) := by
  sorry

/-- The function returns a result r (it does not fail).
  Preconditions: m = len(matrix) >= 1; n = len(matrix[0]) >= 1; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= matrix[i][j] <= 1000; -10^8 <= target <= 10^8. -/
theorem spec_2
    (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000) :
    ∃ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000), ∃ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: m = len(matrix) >= 1; n = len(matrix[0]) >= 1; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= matrix[i][j] <= 1000; -10^8 <= target <= 10^8. -/
theorem spec_3
    (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000) :
    ∀ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000), ∀ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= (m*(m+1)/2) * (n*(n+1)/2).
  Preconditions: m = len(matrix) >= 1; n = len(matrix[0]) >= 1; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= matrix[i][j] <= 1000; -10^8 <= target <= 10^8. -/
theorem spec_4
    (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000) :
    ∀ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      r.val ≤ (numSubrectangles m n : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000), ∀ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      r.val ≤ (numSubrectangles m n : Int)) := by
  sorry

/-- Whenever the function returns a result r, r >= T, where T is the number of pairs (i,j) with 0 <= i < m, 0 <= j < n, and matrix[i][j] = target.
  Preconditions: m = len(matrix) >= 1; n = len(matrix[0]) >= 1; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= matrix[i][j] <= 1000; -10^8 <= target <= 10^8. -/
theorem spec_5
    (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000) :
    ∀ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      (countEntriesEq matrix target.val m n : Int) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000), ∀ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      (countEntriesEq matrix target.val m n : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: m = len(matrix) >= 1; n = len(matrix[0]) >= 1; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= matrix[i][j] <= 1000; -10^8 <= target <= 10^8; let T = sum_{i=0}^{m-1} sum_{j=0}^{n-1} matrix[i][j]; assume T = target. -/
theorem spec_6
    (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000)
    (htotal : matrixSum matrix m n = target.val) :
    ∀ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r → 1 ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000)
    (htotal : matrixSum matrix m n = target.val), ∀ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r equals the number of pairs (y1,y2) of integers such that 0 <= y1 <= y2 < n and sum_{j=y1}^{y2} matrix[0][j] = target.
  Preconditions: m = len(matrix) >= 1; n = len(matrix[0]) >= 1; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= matrix[i][j] <= 1000; -10^8 <= target <= 10^8; m = 1. -/
theorem spec_7
    (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000)
    (hm_one : m = 1) :
    ∀ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      r.val = (countRowRanges matrix target.val n : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000)
    (hm_one : m = 1), ∀ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      r.val = (countRowRanges matrix target.val n : Int)) := by
  sorry

/-- Whenever the function returns a result r, r equals the number of pairs (x1,x2) of integers such that 0 <= x1 <= x2 < m and sum_{i=x1}^{x2} matrix[i][0] = target.
  Preconditions: m = len(matrix) >= 1; n = len(matrix[0]) >= 1; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= matrix[i][j] <= 1000; -10^8 <= target <= 10^8; n = 1. -/
theorem spec_8
    (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000)
    (hn_one : n = 1) :
    ∀ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      r.val = (countColRanges matrix target.val m : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000)
    (hn_one : n = 1), ∀ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      r.val = (countColRanges matrix target.val m : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = (m*(m+1)/2) * (n*(n+1)/2).
  Preconditions: m = len(matrix) >= 1; n = len(matrix[0]) >= 1; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= matrix[i][j] <= 1000; -10^8 <= target <= 10^8; for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] = 0; target = 0. -/
theorem spec_9
    (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000)
    (hzero : ∀ i j, i < m → j < n → entry matrix i j = 0) (htarget_zero : target.val = 0) :
    ∀ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      r.val = (numSubrectangles m n : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000)
    (hzero : ∀ i j, i < m → j < n → entry matrix i j = 0) (htarget_zero : target.val = 0), ∀ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      r.val = (numSubrectangles m n : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: m = len(matrix) >= 1; n = len(matrix[0]) >= 1; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= matrix[i][j] <= 1000; -10^8 <= target <= 10^8; for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] > 0; target <= 0. -/
theorem spec_10
    (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000)
    (hpos : ∀ i j, i < m → j < n → 0 < entry matrix i j) (htarget_nonpos : target.val ≤ 0) :
    ∀ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r → r.val = 0 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000)
    (hpos : ∀ i j, i < m → j < n → 0 < entry matrix i j) (htarget_nonpos : target.val ≤ 0), ∀ r, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r → r.val = 0) := by
  sorry

/-- Let matrixR be the m x n matrix with matrixR[i][j] = matrix[m-1-i][j] for 0 <= i < m and 0 <= j < n. If r is the result returned for (matrix,target) and rR is the result returned for (matrixR,target), then r = rR.
  Preconditions: m = len(matrix) >= 1; n = len(matrix[0]) >= 1; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= matrix[i][j] <= 1000; -10^8 <= target <= 10^8. -/
theorem spec_11
    (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000)
    (matrixR : Slice (alloc.vec.Vec I64)) (hR : IsRowFlip matrixR matrix m n) :
    ∀ r rR, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrixR target = ok rR → r = rR := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000)
    (matrixR : Slice (alloc.vec.Vec I64)) (hR : IsRowFlip matrixR matrix m n), ∀ r rR, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrixR target = ok rR → r = rR) := by
  sorry

/-- Let matrixC be the m x n matrix with matrixC[i][j] = matrix[i][n-1-j] for 0 <= i < m and 0 <= j < n. If r is the result returned for (matrix,target) and rC is the result returned for (matrixC,target), then r = rC.
  Preconditions: m = len(matrix) >= 1; n = len(matrix[0]) >= 1; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= matrix[i][j] <= 1000; -10^8 <= target <= 10^8. -/
theorem spec_12
    (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000)
    (matrixC : Slice (alloc.vec.Vec I64)) (hC : IsColFlip matrixC matrix m n) :
    ∀ r rC, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrixC target = ok rC → r = rC := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000)
    (matrixC : Slice (alloc.vec.Vec I64)) (hC : IsColFlip matrixC matrix m n), ∀ r rC, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrixC target = ok rC → r = rC) := by
  sorry

/-- Let matrixN be the m x n matrix with matrixN[i][j] = -matrix[i][j] for 0 <= i < m and 0 <= j < n. If r is the result returned for (matrix,target) and rN is the result returned for (matrixN,-target), then r = rN.
  Preconditions: m = len(matrix) >= 1; n = len(matrix[0]) >= 1; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= matrix[i][j] <= 1000; -10^8 <= target <= 10^8. -/
theorem spec_13
    (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000)
    (matrixN : Slice (alloc.vec.Vec I64)) (targetN : I64)
    (hN : IsNeg matrixN matrix m n) (htargetN : targetN.val = -target.val) :
    ∀ r rN, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrixN targetN = ok rN → r = rN := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000)
    (matrixN : Slice (alloc.vec.Vec I64)) (targetN : I64)
    (hN : IsNeg matrixN matrix m n) (htargetN : targetN.val = -target.val), ∀ r rN, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrixN targetN = ok rN → r = rN) := by
  sorry

/-- Let matrixT be the n x m matrix with matrixT[i][j] = matrix[j][i] for 0 <= i < n and 0 <= j < m. If r is the result returned for (matrix,target) and rT is the result returned for (matrixT,target), then r = rT.
  Preconditions: m = len(matrix) >= 1; n = len(matrix[0]) >= 1; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= matrix[i][j] <= 1000; -10^8 <= target <= 10^8. -/
theorem spec_14
    (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000)
    (matrixT : Slice (alloc.vec.Vec I64)) (hT : IsTranspose matrixT matrix m n) :
    ∀ r rT, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrixT target = ok rT → r = rT := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (target : I64) (m n : Nat)
    (hm : m = matrix.val.length) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n)
    (hrow_len : ∀ i, i < m → (row matrix i).length = n)
    (hentry_bounds : ∀ i j, i < m → j < n → -1000 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000)
    (htarget_bounds : -100000000 ≤ target.val ∧ target.val ≤ 100000000)
    (matrixT : Slice (alloc.vec.Vec I64)) (hT : IsTranspose matrixT matrix m n), ∀ r rT, Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrix target = ok r →
      Aegis.NumSubmatrixSumTarget.num_submatrix_sum_target matrixT target = ok rT → r = rT) := by
  sorry

end AegisSpec.NumSubmatrixSumTarget
