import Aegis.KthLargestValue.Code.Funs

/-!
# Specifications of `Aegis.KthLargestValue.kth_largest_value`

LeetCode problem `find-kth-largest-xor-coordinate-value`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
  open Aegis.KthLargestValue

  namespace AegisSpec.KthLargestValue

  def ncols (matrix : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
    match matrix.val with
    | [] => 0
    | row :: _ => row.val.length

  def entry (matrix : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
    match matrix.val[i]? with
    | none => 0
    | some row =>
      match row.val[j]? with
      | none => 0
      | some x => x.val

  def xorInt (x y : ℤ) : ℤ := ((x.toNat ^^^ y.toNat : ℕ) : ℤ)

  def coordXor (matrix : Slice (alloc.vec.Vec Std.I64)) (a b : ℕ) : ℤ :=
    (((List.range (a + 1)).product (List.range (b + 1))).map
        (fun p => entry matrix p.1 p.2)).foldl xorInt 0

  def coordValues (matrix : Slice (alloc.vec.Vec Std.I64)) : List ℤ :=
    ((List.range matrix.val.length).product (List.range (ncols matrix))).map
      (fun p => coordXor matrix p.1 p.2)

  def countGreater (matrix : Slice (alloc.vec.Vec Std.I64)) (v : ℤ) : ℤ :=
    ((coordValues matrix).countP (fun x => decide (v < x)) : ℤ)

  def countAtLeast (matrix : Slice (alloc.vec.Vec Std.I64)) (v : ℤ) : ℤ :=
    ((coordValues matrix).countP (fun x => decide (v ≤ x)) : ℤ)

  def maxCoord (matrix : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    (coordValues matrix).foldr max 0

  def minCoord (matrix : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    (coordValues matrix).foldr min 0

  def nthLargest (l : List ℤ) (k : ℕ) : ℤ :=
    (l.mergeSort (fun a b => decide (b ≤ a))).getD (k - 1) 0

  /-- Define V(a,b) = XOR of matrix[i][j] over all i,j with 0 <= i <= a < m and 0 <= j <= b < n. Let G(v) = the number of pairs (a,b) with 0 <= a < m, 0 <= b < n and V(a,b) > v, and let C(v) = the number of pairs (a,b) with 0 <= a < m, 0 <= b < n and V(a,b) >= v. The function returns a result r such that G(r) < k and C(r) >= k. Equivalently, if the m*n coordinate values V(a,b) are sorted in non-increasing order (one entry per coordinate, duplicates kept), then r is the k-th entry of that sorted list.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The slice matrix is non-empty (m >= 1), every row is non-empty and has the same length n (so n >= 1), m <= 1000, n <= 1000, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= matrix[i][j] <= 10^6, and 1 <= k <= m*n. -/
  theorem spec_1 (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ matrix.val.length)
      (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
      (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
      (hm_le : matrix.val.length ≤ 1000)
      (hn_le : ncols matrix ≤ 1000)
      (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
        0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
      (hk_lo : 1 ≤ k.val)
      (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))) :
      ∃ r, kth_largest_value matrix k = ok r ∧
        countGreater matrix r.val < k.val ∧ k.val ≤ countAtLeast matrix r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ matrix.val.length)
        (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
        (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
        (hm_le : matrix.val.length ≤ 1000)
        (hn_le : ncols matrix ≤ 1000)
        (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
          0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
        (hk_lo : 1 ≤ k.val)
        (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))), ∃ r, kth_largest_value matrix k = ok r ∧
          countGreater matrix r.val < k.val ∧ k.val ≤ countAtLeast matrix r.val) := by
    sorry

  /-- The function does not fail: for every input satisfying the preconditions it returns a result r.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The slice matrix is non-empty (m >= 1), every row is non-empty and has the same length n (so n >= 1), m <= 1000, n <= 1000, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= matrix[i][j] <= 10^6, and 1 <= k <= m*n. -/
  theorem spec_2 (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ matrix.val.length)
      (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
      (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
      (hm_le : matrix.val.length ≤ 1000)
      (hn_le : ncols matrix ≤ 1000)
      (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
        0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
      (hk_lo : 1 ≤ k.val)
      (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))) :
      ∃ r, kth_largest_value matrix k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ matrix.val.length)
        (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
        (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
        (hm_le : matrix.val.length ≤ 1000)
        (hn_le : ncols matrix ≤ 1000)
        (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
          0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
        (hk_lo : 1 ≤ k.val)
        (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))), ∃ r, kth_largest_value matrix k = ok r) := by
    sorry

  /-- The function returns a result r and r >= 0.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The slice matrix is non-empty (m >= 1), every row is non-empty and has the same length n (so n >= 1), m <= 1000, n <= 1000, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= matrix[i][j] <= 10^6, and 1 <= k <= m*n. -/
  theorem spec_3 (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ matrix.val.length)
      (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
      (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
      (hm_le : matrix.val.length ≤ 1000)
      (hn_le : ncols matrix ≤ 1000)
      (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
        0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
      (hk_lo : 1 ≤ k.val)
      (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))) :
      ∃ r, kth_largest_value matrix k = ok r ∧ 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ matrix.val.length)
        (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
        (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
        (hm_le : matrix.val.length ≤ 1000)
        (hn_le : ncols matrix ≤ 1000)
        (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
          0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
        (hk_lo : 1 ≤ k.val)
        (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))), ∃ r, kth_largest_value matrix k = ok r ∧ 0 ≤ r.val) := by
    sorry

  /-- The function returns a result r and r < 2^20 = 1,048,576 (equivalently r <= 1,048,575).
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The slice matrix is non-empty (m >= 1), every row is non-empty and has the same length n (so n >= 1), m <= 1000, n <= 1000, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= matrix[i][j] <= 10^6, and 1 <= k <= m*n. -/
  theorem spec_4 (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ matrix.val.length)
      (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
      (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
      (hm_le : matrix.val.length ≤ 1000)
      (hn_le : ncols matrix ≤ 1000)
      (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
        0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
      (hk_lo : 1 ≤ k.val)
      (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))) :
      ∃ r, kth_largest_value matrix k = ok r ∧ r.val < 2 ^ 20 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ matrix.val.length)
        (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
        (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
        (hm_le : matrix.val.length ≤ 1000)
        (hn_le : ncols matrix ≤ 1000)
        (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
          0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
        (hk_lo : 1 ≤ k.val)
        (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))), ∃ r, kth_largest_value matrix k = ok r ∧ r.val < 2 ^ 20) := by
    sorry

  /-- The function returns a result r and there exist indices a,b with 0 <= a < m and 0 <= b < n such that r = V(a,b), where V(a,b) is the XOR of matrix[i][j] over all i,j with 0 <= i <= a and 0 <= j <= b.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The slice matrix is non-empty (m >= 1), every row is non-empty and has the same length n (so n >= 1), m <= 1000, n <= 1000, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= matrix[i][j] <= 10^6, and 1 <= k <= m*n. -/
  theorem spec_5 (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ matrix.val.length)
      (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
      (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
      (hm_le : matrix.val.length ≤ 1000)
      (hn_le : ncols matrix ≤ 1000)
      (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
        0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
      (hk_lo : 1 ≤ k.val)
      (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))) :
      ∃ r, kth_largest_value matrix k = ok r ∧
        ∃ a b, a < matrix.val.length ∧ b < ncols matrix ∧ r.val = coordXor matrix a b := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ matrix.val.length)
        (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
        (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
        (hm_le : matrix.val.length ≤ 1000)
        (hn_le : ncols matrix ≤ 1000)
        (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
          0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
        (hk_lo : 1 ≤ k.val)
        (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))), ∃ r, kth_largest_value matrix k = ok r ∧
          ∃ a b, a < matrix.val.length ∧ b < ncols matrix ∧ r.val = coordXor matrix a b) := by
    sorry

  /-- The function returns a result r and r <= maxCoord, where maxCoord = max { V(a,b) : 0 <= a < m, 0 <= b < n } and V(a,b) is the XOR of matrix[i][j] over all i,j with 0 <= i <= a and 0 <= j <= b.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The slice matrix is non-empty (m >= 1), every row is non-empty and has the same length n (so n >= 1), m <= 1000, n <= 1000, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= matrix[i][j] <= 10^6, and 1 <= k <= m*n. -/
  theorem spec_6 (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ matrix.val.length)
      (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
      (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
      (hm_le : matrix.val.length ≤ 1000)
      (hn_le : ncols matrix ≤ 1000)
      (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
        0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
      (hk_lo : 1 ≤ k.val)
      (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))) :
      ∃ r, kth_largest_value matrix k = ok r ∧ r.val ≤ maxCoord matrix := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ matrix.val.length)
        (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
        (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
        (hm_le : matrix.val.length ≤ 1000)
        (hn_le : ncols matrix ≤ 1000)
        (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
          0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
        (hk_lo : 1 ≤ k.val)
        (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))), ∃ r, kth_largest_value matrix k = ok r ∧ r.val ≤ maxCoord matrix) := by
    sorry

  /-- The function returns a result r and r >= minCoord, where minCoord = min { V(a,b) : 0 <= a < m, 0 <= b < n } and V(a,b) is the XOR of matrix[i][j] over all i,j with 0 <= i <= a and 0 <= j <= b.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The slice matrix is non-empty (m >= 1), every row is non-empty and has the same length n (so n >= 1), m <= 1000, n <= 1000, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= matrix[i][j] <= 10^6, and 1 <= k <= m*n. -/
  theorem spec_7 (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ matrix.val.length)
      (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
      (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
      (hm_le : matrix.val.length ≤ 1000)
      (hn_le : ncols matrix ≤ 1000)
      (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
        0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
      (hk_lo : 1 ≤ k.val)
      (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))) :
      ∃ r, kth_largest_value matrix k = ok r ∧ minCoord matrix ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ matrix.val.length)
        (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
        (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
        (hm_le : matrix.val.length ≤ 1000)
        (hn_le : ncols matrix ≤ 1000)
        (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
          0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
        (hk_lo : 1 ≤ k.val)
        (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))), ∃ r, kth_largest_value matrix k = ok r ∧ minCoord matrix ≤ r.val) := by
    sorry

  /-- The function returns a result r and G(r) < k, where G(v) = the number of pairs (a,b) with 0 <= a < m, 0 <= b < n and V(a,b) > v, and V(a,b) is the XOR of matrix[i][j] over all i,j with 0 <= i <= a and 0 <= j <= b.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The slice matrix is non-empty (m >= 1), every row is non-empty and has the same length n (so n >= 1), m <= 1000, n <= 1000, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= matrix[i][j] <= 10^6, and 1 <= k <= m*n. -/
  theorem spec_8 (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ matrix.val.length)
      (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
      (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
      (hm_le : matrix.val.length ≤ 1000)
      (hn_le : ncols matrix ≤ 1000)
      (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
        0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
      (hk_lo : 1 ≤ k.val)
      (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))) :
      ∃ r, kth_largest_value matrix k = ok r ∧ countGreater matrix r.val < k.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ matrix.val.length)
        (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
        (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
        (hm_le : matrix.val.length ≤ 1000)
        (hn_le : ncols matrix ≤ 1000)
        (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
          0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
        (hk_lo : 1 ≤ k.val)
        (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))), ∃ r, kth_largest_value matrix k = ok r ∧ countGreater matrix r.val < k.val) := by
    sorry

  /-- The function returns a result r and C(r) >= k, where C(v) = the number of pairs (a,b) with 0 <= a < m, 0 <= b < n and V(a,b) >= v, and V(a,b) is the XOR of matrix[i][j] over all i,j with 0 <= i <= a and 0 <= j <= b.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The slice matrix is non-empty (m >= 1), every row is non-empty and has the same length n (so n >= 1), m <= 1000, n <= 1000, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= matrix[i][j] <= 10^6, and 1 <= k <= m*n. -/
  theorem spec_9 (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ matrix.val.length)
      (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
      (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
      (hm_le : matrix.val.length ≤ 1000)
      (hn_le : ncols matrix ≤ 1000)
      (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
        0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
      (hk_lo : 1 ≤ k.val)
      (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))) :
      ∃ r, kth_largest_value matrix k = ok r ∧ k.val ≤ countAtLeast matrix r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ matrix.val.length)
        (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
        (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
        (hm_le : matrix.val.length ≤ 1000)
        (hn_le : ncols matrix ≤ 1000)
        (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
          0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
        (hk_lo : 1 ≤ k.val)
        (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))), ∃ r, kth_largest_value matrix k = ok r ∧ k.val ≤ countAtLeast matrix r.val) := by
    sorry

  /-- Whenever kth_largest_value(matrix, k1) returns r1 and kth_largest_value(matrix, k2) returns r2, we have r1 >= r2.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The slice matrix is non-empty (m >= 1), every row is non-empty and has the same length n (so n >= 1), m <= 1000, n <= 1000, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= matrix[i][j] <= 10^6. Let k1 and k2 be integers with 1 <= k1 <= k2 <= m*n. -/
  theorem spec_10 (matrix : Slice (alloc.vec.Vec Std.I64)) (k1 : Std.I64) (k2 : Std.I64)
      (hm_pos : 1 ≤ matrix.val.length)
      (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
      (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
      (hm_le : matrix.val.length ≤ 1000)
      (hn_le : ncols matrix ≤ 1000)
      (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
        0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
      (hk1 : 1 ≤ k1.val)
      (hk12 : k1.val ≤ k2.val)
      (hk2 : k2.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))) :
      ∀ r1 r2, kth_largest_value matrix k1 = ok r1 → kth_largest_value matrix k2 = ok r2 →
        r1.val ≥ r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (k1 : Std.I64) (k2 : Std.I64)
        (hm_pos : 1 ≤ matrix.val.length)
        (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
        (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
        (hm_le : matrix.val.length ≤ 1000)
        (hn_le : ncols matrix ≤ 1000)
        (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
          0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
        (hk1 : 1 ≤ k1.val)
        (hk12 : k1.val ≤ k2.val)
        (hk2 : k2.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))), ∀ r1 r2, kth_largest_value matrix k1 = ok r1 → kth_largest_value matrix k2 = ok r2 →
          r1.val ≥ r2.val) := by
    sorry

  /-- Let T be the n x m matrix defined by T[b][a] = matrix[a][b] for all 0 <= a < m and 0 <= b < n. Whenever kth_largest_value(matrix, k) returns r and kth_largest_value(T, k) returns r_T, we have r = r_T.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The slice matrix is non-empty (m >= 1), every row is non-empty and has the same length n (so n >= 1), m <= 1000, n <= 1000, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= matrix[i][j] <= 10^6, and 1 <= k <= m*n. -/
  theorem spec_11 (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ matrix.val.length)
      (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
      (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
      (hm_le : matrix.val.length ≤ 1000)
      (hn_le : ncols matrix ≤ 1000)
      (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
        0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
      (hk_lo : 1 ≤ k.val)
      (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))) :
      ∀ (T : Slice (alloc.vec.Vec Std.I64)),
        T.val.length = ncols matrix →
        (∀ row ∈ T.val, row.val.length = matrix.val.length) →
        (∀ a b, a < matrix.val.length → b < ncols matrix →
          entry T b a = entry matrix a b) →
        ∀ r rT, kth_largest_value matrix k = ok r → kth_largest_value T k = ok rT →
          r.val = rT.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ matrix.val.length)
        (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
        (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
        (hm_le : matrix.val.length ≤ 1000)
        (hn_le : ncols matrix ≤ 1000)
        (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
          0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
        (hk_lo : 1 ≤ k.val)
        (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ))), ∀ (T : Slice (alloc.vec.Vec Std.I64)),
          T.val.length = ncols matrix →
          (∀ row ∈ T.val, row.val.length = matrix.val.length) →
          (∀ a b, a < matrix.val.length → b < ncols matrix →
            entry T b a = entry matrix a b) →
          ∀ r rT, kth_largest_value matrix k = ok r → kth_largest_value T k = ok rT →
            r.val = rT.val) := by
    sorry

  /-- The function returns a result r and r = matrix[0][0].
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The slice matrix is non-empty (m >= 1), every row is non-empty and has the same length n (so n >= 1), m <= 1000, n <= 1000, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= matrix[i][j] <= 10^6, and 1 <= k <= m*n. In addition, m = 1 and n = 1. -/
  theorem spec_12 (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ matrix.val.length)
      (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
      (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
      (hm_le : matrix.val.length ≤ 1000)
      (hn_le : ncols matrix ≤ 1000)
      (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
        0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
      (hk_lo : 1 ≤ k.val)
      (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ)))
      (hm1 : matrix.val.length = 1)
      (hn1 : ncols matrix = 1) :
      ∃ r, kth_largest_value matrix k = ok r ∧ r.val = entry matrix 0 0 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ matrix.val.length)
        (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
        (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
        (hm_le : matrix.val.length ≤ 1000)
        (hn_le : ncols matrix ≤ 1000)
        (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
          0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
        (hk_lo : 1 ≤ k.val)
        (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ)))
        (hm1 : matrix.val.length = 1)
        (hn1 : ncols matrix = 1), ∃ r, kth_largest_value matrix k = ok r ∧ r.val = entry matrix 0 0) := by
    sorry

  /-- The function returns a result r and r is the maximum of the coordinate values V(a,b): for every a,b with 0 <= a < m and 0 <= b < n we have V(a,b) <= r, and there exist a,b with 0 <= a < m and 0 <= b < n such that V(a,b) = r, where V(a,b) is the XOR of matrix[i][j] over all i,j with 0 <= i <= a and 0 <= j <= b.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The slice matrix is non-empty (m >= 1), every row is non-empty and has the same length n (so n >= 1), m <= 1000, n <= 1000, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= matrix[i][j] <= 10^6, and 1 <= k <= m*n. In addition, k = 1. -/
  theorem spec_13 (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ matrix.val.length)
      (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
      (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
      (hm_le : matrix.val.length ≤ 1000)
      (hn_le : ncols matrix ≤ 1000)
      (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
        0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
      (hk_lo : 1 ≤ k.val)
      (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ)))
      (hk1 : k.val = 1) :
      ∃ r, kth_largest_value matrix k = ok r ∧
        (∀ a b, a < matrix.val.length → b < ncols matrix → coordXor matrix a b ≤ r.val) ∧
        (∃ a b, a < matrix.val.length ∧ b < ncols matrix ∧ coordXor matrix a b = r.val) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ matrix.val.length)
        (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
        (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
        (hm_le : matrix.val.length ≤ 1000)
        (hn_le : ncols matrix ≤ 1000)
        (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
          0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
        (hk_lo : 1 ≤ k.val)
        (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ)))
        (hk1 : k.val = 1), ∃ r, kth_largest_value matrix k = ok r ∧
          (∀ a b, a < matrix.val.length → b < ncols matrix → coordXor matrix a b ≤ r.val) ∧
          (∃ a b, a < matrix.val.length ∧ b < ncols matrix ∧ coordXor matrix a b = r.val)) := by
    sorry

  /-- The function returns a result r and r is the minimum of the coordinate values V(a,b): for every a,b with 0 <= a < m and 0 <= b < n we have V(a,b) >= r, and there exist a,b with 0 <= a < m and 0 <= b < n such that V(a,b) = r, where V(a,b) is the XOR of matrix[i][j] over all i,j with 0 <= i <= a and 0 <= j <= b.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The slice matrix is non-empty (m >= 1), every row is non-empty and has the same length n (so n >= 1), m <= 1000, n <= 1000, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= matrix[i][j] <= 10^6, and 1 <= k <= m*n. In addition, k = m*n. -/
  theorem spec_14 (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ matrix.val.length)
      (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
      (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
      (hm_le : matrix.val.length ≤ 1000)
      (hn_le : ncols matrix ≤ 1000)
      (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
        0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
      (hk_lo : 1 ≤ k.val)
      (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ)))
      (hkn : k.val = ((matrix.val.length : ℤ) * (ncols matrix : ℤ))) :
      ∃ r, kth_largest_value matrix k = ok r ∧
        (∀ a b, a < matrix.val.length → b < ncols matrix → coordXor matrix a b ≥ r.val) ∧
        (∃ a b, a < matrix.val.length ∧ b < ncols matrix ∧ coordXor matrix a b = r.val) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ matrix.val.length)
        (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
        (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
        (hm_le : matrix.val.length ≤ 1000)
        (hn_le : ncols matrix ≤ 1000)
        (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
          0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
        (hk_lo : 1 ≤ k.val)
        (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ)))
        (hkn : k.val = ((matrix.val.length : ℤ) * (ncols matrix : ℤ))), ∃ r, kth_largest_value matrix k = ok r ∧
          (∀ a b, a < matrix.val.length → b < ncols matrix → coordXor matrix a b ≥ r.val) ∧
          (∃ a b, a < matrix.val.length ∧ b < ncols matrix ∧ coordXor matrix a b = r.val)) := by
    sorry

  /-- Let p_b = XOR of matrix[0][j] for 0 <= j <= b, for each b with 0 <= b < n. The function returns a result r and r is the k-th largest value among p_0, p_1, ..., p_{n-1} (with multiplicity, sorted non-increasing).
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The slice matrix is non-empty (m >= 1), every row is non-empty and has the same length n (so n >= 1), m <= 1000, n <= 1000, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= matrix[i][j] <= 10^6, and 1 <= k <= m*n. In addition, m = 1. -/
  theorem spec_15 (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ matrix.val.length)
      (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
      (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
      (hm_le : matrix.val.length ≤ 1000)
      (hn_le : ncols matrix ≤ 1000)
      (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
        0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
      (hk_lo : 1 ≤ k.val)
      (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ)))
      (hm1 : matrix.val.length = 1) :
      ∃ r, kth_largest_value matrix k = ok r ∧
        r.val = nthLargest ((List.range (ncols matrix)).map
          (fun b => coordXor matrix 0 b)) k.val.toNat := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ matrix.val.length)
        (hrow_pos : ∀ row ∈ matrix.val, 1 ≤ row.val.length)
        (hrow_len : ∀ row ∈ matrix.val, row.val.length = ncols matrix)
        (hm_le : matrix.val.length ≤ 1000)
        (hn_le : ncols matrix ≤ 1000)
        (hval : ∀ i j, i < matrix.val.length → j < ncols matrix →
          0 ≤ entry matrix i j ∧ entry matrix i j ≤ 1000000)
        (hk_lo : 1 ≤ k.val)
        (hk_hi : k.val ≤ ((matrix.val.length : ℤ) * (ncols matrix : ℤ)))
        (hm1 : matrix.val.length = 1), ∃ r, kth_largest_value matrix k = ok r ∧
          r.val = nthLargest ((List.range (ncols matrix)).map
            (fun b => coordXor matrix 0 b)) k.val.toNat) := by
    sorry

  end AegisSpec.KthLargestValue
