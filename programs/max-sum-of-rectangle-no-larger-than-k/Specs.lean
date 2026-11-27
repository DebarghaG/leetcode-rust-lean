import Aegis.MaxSumSubmatrix.Code.Funs

/-!
# Specifications of `Aegis.MaxSumSubmatrix.max_sum_submatrix`

LeetCode problem `max-sum-of-rectangle-no-larger-than-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxSumSubmatrix

open Aegis.MaxSumSubmatrix

def entries (matrix : Slice (alloc.vec.Vec I64)) : List (List Int) :=
  matrix.val.map (fun row => row.val.map (fun x => x.val))

def ncols (M : List (List Int)) : Nat := (M.headD []).length

def entry (M : List (List Int)) (i j : Nat) : Int := (M.getD i []).getD j 0

def rowLeng (M : List (List Int)) (i : Nat) : Nat := (M.getD i []).length

def rectSum (M : List (List Int)) (a b c d : Nat) : Int :=
  ((M.drop a).take (b + 1 - a)).foldl
    (fun acc row => acc + ((row.drop c).take (d + 1 - c)).sum) 0

def totalSum (M : List (List Int)) : Int := M.foldl (fun acc row => acc + row.sum) 0

def transpose (M : List (List Int)) : List (List Int) :=
  (List.range (ncols M)).map (fun j => M.map (fun row => row.getD j 0))

def RectValid (M : List (List Int)) (a b c d : Nat) : Prop :=
  a ≤ b ∧ b < M.length ∧ c ≤ d ∧ ∀ i, a ≤ i → i ≤ b → d < (M.getD i []).length

def RectOk (M : List (List Int)) : Prop :=
  1 ≤ M.length ∧ M.length ≤ 100 ∧
    (∀ row ∈ M, 1 ≤ row.length) ∧
    (∀ row ∈ M, row.length = ncols M) ∧
    (∀ row ∈ M, row.length ≤ 100)

def SmallEntries (M : List (List Int)) : Prop := ∀ row ∈ M, ∀ x ∈ row, -100 ≤ x ∧ x ≤ 100

def NonnegEntries (M : List (List Int)) : Prop := ∀ row ∈ M, ∀ x ∈ row, 0 ≤ x

def KOk (k : I64) : Prop := -100000 ≤ k.val ∧ k.val ≤ 100000

def HasEligible (M : List (List Int)) (k : Int) : Prop :=
  ∃ a b c d, RectValid M a b c d ∧ rectSum M a b c d ≤ k

def Pre (matrix : Slice (alloc.vec.Vec I64)) (k : I64) : Prop :=
  RectOk (entries matrix) ∧ SmallEntries (entries matrix) ∧ KOk k ∧
    HasEligible (entries matrix) k.val

def PreLE (matrix : Slice (alloc.vec.Vec I64)) (k1 k2 : I64) : Prop :=
  RectOk (entries matrix) ∧ SmallEntries (entries matrix) ∧
    -100000 ≤ k1.val ∧ k1.val ≤ k2.val ∧ k2.val ≤ 100000 ∧
    HasEligible (entries matrix) k1.val

/-- Let S(a,b,c,d) = sum_{i=a..b} sum_{j=c..d} matrix[i][j] for 0 <= a <= b < m and 0 <= c <= d < n. The function returns a result r (it does not fail). The value r is exactly the maximum of the finite non-empty set { S(a,b,c,d) | 0 <= a <= b < m, 0 <= c <= d < n, and S(a,b,c,d) <= k }. Equivalently, r is an eligible rectangle sum and every eligible rectangle sum is at most r.
  Preconditions: Let m = len(matrix) and let n be the common length of the rows. matrix is a non-empty rectangular matrix of integers: 1 <= m <= 100, 1 <= n <= 100, every row matrix[i] has length n for 0 <= i < m, and -100 <= matrix[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. k is an integer with -100000 <= k <= 100000. It is guaranteed that there is at least one non-empty axis-aligned rectangle whose sum is at most k, i.e. there exist 0 <= a <= b < m and 0 <= c <= d < n with sum_{i=a..b} sum_{j=c..d} matrix[i][j] <= k. -/
theorem spec_1 (matrix : Slice (alloc.vec.Vec I64)) (k : I64) (h : Pre matrix k) :
    ∃ r : I64, max_sum_submatrix matrix k = ok r ∧
      (∃ a b c d, RectValid (entries matrix) a b c d ∧
        rectSum (entries matrix) a b c d ≤ k.val ∧
        rectSum (entries matrix) a b c d = r.val) ∧
      (∀ a b c d, RectValid (entries matrix) a b c d →
        rectSum (entries matrix) a b c d ≤ k.val →
        rectSum (entries matrix) a b c d ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (k : I64) (h : Pre matrix k), ∃ r : I64, max_sum_submatrix matrix k = ok r ∧
      (∃ a b c d, RectValid (entries matrix) a b c d ∧
        rectSum (entries matrix) a b c d ≤ k.val ∧
        rectSum (entries matrix) a b c d = r.val) ∧
      (∀ a b c d, RectValid (entries matrix) a b c d →
        rectSum (entries matrix) a b c d ≤ k.val →
        rectSum (entries matrix) a b c d ≤ r.val)) := by
  sorry

/-- The function returns a result r on every input satisfying the preconditions; it does not fail, panic, or overflow.
  Preconditions: Let m = len(matrix) and let n be the common length of the rows. matrix is a non-empty rectangular matrix of integers: 1 <= m <= 100, 1 <= n <= 100, every row matrix[i] has length n for 0 <= i < m, and -100 <= matrix[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. k is an integer with -100000 <= k <= 100000. It is guaranteed that there is at least one non-empty axis-aligned rectangle whose sum is at most k. -/
theorem spec_2 (matrix : Slice (alloc.vec.Vec I64)) (k : I64) (h : Pre matrix k) :
    ∃ r : I64, max_sum_submatrix matrix k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (k : I64) (h : Pre matrix k), ∃ r : I64, max_sum_submatrix matrix k = ok r) := by
  sorry

/-- The function returns a result r and r <= k.
  Preconditions: Let m = len(matrix) and let n be the common length of the rows. matrix is a non-empty rectangular matrix of integers: 1 <= m <= 100, 1 <= n <= 100, every row matrix[i] has length n for 0 <= i < m, and -100 <= matrix[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. k is an integer with -100000 <= k <= 100000. It is guaranteed that there is at least one non-empty axis-aligned rectangle whose sum is at most k. -/
theorem spec_3 (matrix : Slice (alloc.vec.Vec I64)) (k : I64) (h : Pre matrix k) :
    ∃ r : I64, max_sum_submatrix matrix k = ok r ∧ r.val ≤ k.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (k : I64) (h : Pre matrix k), ∃ r : I64, max_sum_submatrix matrix k = ok r ∧ r.val ≤ k.val) := by
  sorry

/-- Let S(a,b,c,d) = sum_{i=a..b} sum_{j=c..d} matrix[i][j]. The function returns a result r and there exist indices 0 <= a <= b < m and 0 <= c <= d < n such that S(a,b,c,d) = r.
  Preconditions: Let m = len(matrix) and let n be the common length of the rows. matrix is a non-empty rectangular matrix of integers: 1 <= m <= 100, 1 <= n <= 100, every row matrix[i] has length n for 0 <= i < m, and -100 <= matrix[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. k is an integer with -100000 <= k <= 100000. It is guaranteed that there is at least one non-empty axis-aligned rectangle whose sum is at most k. -/
theorem spec_4 (matrix : Slice (alloc.vec.Vec I64)) (k : I64) (h : Pre matrix k) :
    ∃ r : I64, max_sum_submatrix matrix k = ok r ∧
      ∃ a b c d, RectValid (entries matrix) a b c d ∧
        rectSum (entries matrix) a b c d = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (k : I64) (h : Pre matrix k), ∃ r : I64, max_sum_submatrix matrix k = ok r ∧
      ∃ a b c d, RectValid (entries matrix) a b c d ∧
        rectSum (entries matrix) a b c d = r.val) := by
  sorry

/-- Let S(a,b,c,d) = sum_{i=a..b} sum_{j=c..d} matrix[i][j]. The function returns a result r and for every 0 <= a <= b < m and 0 <= c <= d < n, if S(a,b,c,d) <= k then S(a,b,c,d) <= r.
  Preconditions: Let m = len(matrix) and let n be the common length of the rows. matrix is a non-empty rectangular matrix of integers: 1 <= m <= 100, 1 <= n <= 100, every row matrix[i] has length n for 0 <= i < m, and -100 <= matrix[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. k is an integer with -100000 <= k <= 100000. It is guaranteed that there is at least one non-empty axis-aligned rectangle whose sum is at most k. -/
theorem spec_5 (matrix : Slice (alloc.vec.Vec I64)) (k : I64) (h : Pre matrix k) :
    ∃ r : I64, max_sum_submatrix matrix k = ok r ∧
      ∀ a b c d, RectValid (entries matrix) a b c d →
        rectSum (entries matrix) a b c d ≤ k.val →
        rectSum (entries matrix) a b c d ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (k : I64) (h : Pre matrix k), ∃ r : I64, max_sum_submatrix matrix k = ok r ∧
      ∀ a b c d, RectValid (entries matrix) a b c d →
        rectSum (entries matrix) a b c d ≤ k.val →
        rectSum (entries matrix) a b c d ≤ r.val) := by
  sorry

/-- The function returns a result r and for every 0 <= i < m and 0 <= j < n, if matrix[i][j] <= k then r >= matrix[i][j].
  Preconditions: Let m = len(matrix) and let n be the common length of the rows. matrix is a non-empty rectangular matrix of integers: 1 <= m <= 100, 1 <= n <= 100, every row matrix[i] has length n for 0 <= i < m, and -100 <= matrix[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. k is an integer with -100000 <= k <= 100000. It is guaranteed that there is at least one non-empty axis-aligned rectangle whose sum is at most k. -/
theorem spec_6 (matrix : Slice (alloc.vec.Vec I64)) (k : I64) (h : Pre matrix k) :
    ∃ r : I64, max_sum_submatrix matrix k = ok r ∧
      ∀ i j, i < (entries matrix).length → j < rowLeng (entries matrix) i →
        entry (entries matrix) i j ≤ k.val → entry (entries matrix) i j ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (k : I64) (h : Pre matrix k), ∃ r : I64, max_sum_submatrix matrix k = ok r ∧
      ∀ i j, i < (entries matrix).length → j < rowLeng (entries matrix) i →
        entry (entries matrix) i j ≤ k.val → entry (entries matrix) i j ≤ r.val) := by
  sorry

/-- For 0 <= c <= d < n, let T(c,d) = sum_{j=c..d} matrix[0][j]. The function returns a result r and r is the maximum of the finite non-empty set { T(c,d) | 0 <= c <= d < n and T(c,d) <= k }.
  Preconditions: Let m = len(matrix) and let n be the common length of the rows. matrix is a non-empty rectangular matrix of integers: 1 <= m <= 100, 1 <= n <= 100, every row matrix[i] has length n for 0 <= i < m, and -100 <= matrix[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. k is an integer with -100000 <= k <= 100000. It is guaranteed that there is at least one non-empty axis-aligned rectangle whose sum is at most k. Additionally m = 1. -/
theorem spec_7 (matrix : Slice (alloc.vec.Vec I64)) (k : I64) (h : Pre matrix k)
    (hm : (entries matrix).length = 1) :
    ∃ r : I64, max_sum_submatrix matrix k = ok r ∧
      (∃ c d, RectValid (entries matrix) 0 0 c d ∧
        rectSum (entries matrix) 0 0 c d ≤ k.val ∧
        rectSum (entries matrix) 0 0 c d = r.val) ∧
      (∀ c d, RectValid (entries matrix) 0 0 c d →
        rectSum (entries matrix) 0 0 c d ≤ k.val →
        rectSum (entries matrix) 0 0 c d ≤ r.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (k : I64) (h : Pre matrix k)
    (hm : (entries matrix).length = 1), ∃ r : I64, max_sum_submatrix matrix k = ok r ∧
      (∃ c d, RectValid (entries matrix) 0 0 c d ∧
        rectSum (entries matrix) 0 0 c d ≤ k.val ∧
        rectSum (entries matrix) 0 0 c d = r.val) ∧
      (∀ c d, RectValid (entries matrix) 0 0 c d →
        rectSum (entries matrix) 0 0 c d ≤ k.val →
        rectSum (entries matrix) 0 0 c d ≤ r.val)) := by
  sorry

/-- For 0 <= a <= b < m, let U(a,b) = sum_{i=a..b} matrix[i][0]. The function returns a result r and r is the maximum of the finite non-empty set { U(a,b) | 0 <= a <= b < m and U(a,b) <= k }.
  Preconditions: Let m = len(matrix) and let n be the common length of the rows. matrix is a non-empty rectangular matrix of integers: 1 <= m <= 100, 1 <= n <= 100, every row matrix[i] has length n for 0 <= i < m, and -100 <= matrix[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. k is an integer with -100000 <= k <= 100000. It is guaranteed that there is at least one non-empty axis-aligned rectangle whose sum is at most k. Additionally n = 1. -/
theorem spec_8 (matrix : Slice (alloc.vec.Vec I64)) (k : I64) (h : Pre matrix k)
    (hn : ncols (entries matrix) = 1) :
    ∃ r : I64, max_sum_submatrix matrix k = ok r ∧
      (∃ a b, RectValid (entries matrix) a b 0 0 ∧
        rectSum (entries matrix) a b 0 0 ≤ k.val ∧
        rectSum (entries matrix) a b 0 0 = r.val) ∧
      (∀ a b, RectValid (entries matrix) a b 0 0 →
        rectSum (entries matrix) a b 0 0 ≤ k.val →
        rectSum (entries matrix) a b 0 0 ≤ r.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (k : I64) (h : Pre matrix k)
    (hn : ncols (entries matrix) = 1), ∃ r : I64, max_sum_submatrix matrix k = ok r ∧
      (∃ a b, RectValid (entries matrix) a b 0 0 ∧
        rectSum (entries matrix) a b 0 0 ≤ k.val ∧
        rectSum (entries matrix) a b 0 0 = r.val) ∧
      (∀ a b, RectValid (entries matrix) a b 0 0 →
        rectSum (entries matrix) a b 0 0 ≤ k.val →
        rectSum (entries matrix) a b 0 0 ≤ r.val)) := by
  sorry

/-- Let matrixT be the n-by-m transpose of matrix, defined by matrixT[j][i] = matrix[i][j] for 0 <= i < m and 0 <= j < n. The function returns a result r on matrix and a result rT on matrixT, both with the same k; then r = rT.
  Preconditions: Let m = len(matrix) and let n be the common length of the rows. matrix is a non-empty rectangular matrix of integers: 1 <= m <= 100, 1 <= n <= 100, every row matrix[i] has length n for 0 <= i < m, and -100 <= matrix[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. k is an integer with -100000 <= k <= 100000. It is guaranteed that there is at least one non-empty axis-aligned rectangle whose sum is at most k. -/
theorem spec_9 (matrix matrixT : Slice (alloc.vec.Vec I64)) (k : I64)
    (h : Pre matrix k) (hT : entries matrixT = transpose (entries matrix)) :
    ∃ r rT : I64, max_sum_submatrix matrix k = ok r ∧
      max_sum_submatrix matrixT k = ok rT ∧ r = rT := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (matrix matrixT : Slice (alloc.vec.Vec I64)) (k : I64)
    (h : Pre matrix k) (hT : entries matrixT = transpose (entries matrix)), ∃ r rT : I64, max_sum_submatrix matrix k = ok r ∧
      max_sum_submatrix matrixT k = ok rT ∧ r = rT) := by
  sorry

/-- The function returns a result r1 on (matrix,k1) and a result r2 on (matrix,k2), and r1 <= r2.
  Preconditions: Let m = len(matrix) and let n be the common length of the rows. matrix is a non-empty rectangular matrix of integers: 1 <= m <= 100, 1 <= n <= 100, every row matrix[i] has length n for 0 <= i < m, and -100 <= matrix[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. k1 and k2 are integers with -100000 <= k1 <= k2 <= 100000. It is guaranteed that there is at least one non-empty axis-aligned rectangle whose sum is at most k1; this also guarantees one whose sum is at most k2. -/
theorem spec_10 (matrix : Slice (alloc.vec.Vec I64)) (k1 k2 : I64)
    (h : PreLE matrix k1 k2) :
    ∃ r1 r2 : I64, max_sum_submatrix matrix k1 = ok r1 ∧
      max_sum_submatrix matrix k2 = ok r2 ∧ r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (k1 k2 : I64)
    (h : PreLE matrix k1 k2), ∃ r1 r2 : I64, max_sum_submatrix matrix k1 = ok r1 ∧
      max_sum_submatrix matrix k2 = ok r2 ∧ r1.val ≤ r2.val) := by
  sorry

/-- Let S(a,b,c,d) = sum_{i=a..b} sum_{j=c..d} matrix[i][j]. Let M be the maximum of S(a,b,c,d) over all 0 <= a <= b < m and 0 <= c <= d < n. The function returns a result r and r = M.
  Preconditions: Let m = len(matrix) and let n be the common length of the rows. matrix is a non-empty rectangular matrix of integers: 1 <= m <= 100, 1 <= n <= 100, every row matrix[i] has length n for 0 <= i < m, and -100 <= matrix[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. k is an integer with -100000 <= k <= 100000. Every non-empty axis-aligned rectangle sum is at most k, i.e. for all 0 <= a <= b < m and 0 <= c <= d < n, sum_{i=a..b} sum_{j=c..d} matrix[i][j] <= k. -/
theorem spec_11 (matrix : Slice (alloc.vec.Vec I64)) (k : I64)
    (hR : RectOk (entries matrix)) (he : SmallEntries (entries matrix)) (hk : KOk k)
    (hall : ∀ a b c d, RectValid (entries matrix) a b c d →
      rectSum (entries matrix) a b c d ≤ k.val) :
    ∃ r : I64, max_sum_submatrix matrix k = ok r ∧
      (∃ a b c d, RectValid (entries matrix) a b c d ∧
        rectSum (entries matrix) a b c d = r.val) ∧
      (∀ a b c d, RectValid (entries matrix) a b c d →
        rectSum (entries matrix) a b c d ≤ r.val) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (k : I64)
    (hR : RectOk (entries matrix)) (he : SmallEntries (entries matrix)) (hk : KOk k)
    (hall : ∀ a b c d, RectValid (entries matrix) a b c d →
      rectSum (entries matrix) a b c d ≤ k.val), ∃ r : I64, max_sum_submatrix matrix k = ok r ∧
      (∃ a b c d, RectValid (entries matrix) a b c d ∧
        rectSum (entries matrix) a b c d = r.val) ∧
      (∀ a b c d, RectValid (entries matrix) a b c d →
        rectSum (entries matrix) a b c d ≤ r.val)) := by
  sorry

/-- The function returns a result r and r = sum_{i=0..m-1} sum_{j=0..n-1} matrix[i][j].
  Preconditions: Let m = len(matrix) and let n be the common length of the rows. matrix is a non-empty rectangular matrix of integers: 1 <= m <= 100, 1 <= n <= 100, every row matrix[i] has length n for 0 <= i < m, and -100 <= matrix[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. k is an integer with -100000 <= k <= 100000. Every entry is non-negative, matrix[i][j] >= 0 for all 0 <= i < m and 0 <= j < n, and the sum of the entire matrix is at most k: sum_{i=0..m-1} sum_{j=0..n-1} matrix[i][j] <= k. -/
theorem spec_12 (matrix : Slice (alloc.vec.Vec I64)) (k : I64)
    (hR : RectOk (entries matrix)) (he : SmallEntries (entries matrix)) (hk : KOk k)
    (hnn : NonnegEntries (entries matrix)) (htot : totalSum (entries matrix) ≤ k.val) :
    ∃ r : I64, max_sum_submatrix matrix k = ok r ∧ r.val = totalSum (entries matrix) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (k : I64)
    (hR : RectOk (entries matrix)) (he : SmallEntries (entries matrix)) (hk : KOk k)
    (hnn : NonnegEntries (entries matrix)) (htot : totalSum (entries matrix) ≤ k.val), ∃ r : I64, max_sum_submatrix matrix k = ok r ∧ r.val = totalSum (entries matrix)) := by
  sorry

/-- The function returns a result r and r = k.
  Preconditions: Let m = len(matrix) and let n be the common length of the rows. matrix is a non-empty rectangular matrix of integers: 1 <= m <= 100, 1 <= n <= 100, every row matrix[i] has length n for 0 <= i < m, and -100 <= matrix[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. k is an integer with -100000 <= k <= 100000. It is guaranteed that there is at least one non-empty axis-aligned rectangle whose sum is at most k. Additionally there exist 0 <= a <= b < m and 0 <= c <= d < n such that sum_{i=a..b} sum_{j=c..d} matrix[i][j] = k. -/
theorem spec_13 (matrix : Slice (alloc.vec.Vec I64)) (k : I64) (h : Pre matrix k)
    (hk : ∃ a b c d, RectValid (entries matrix) a b c d ∧
      rectSum (entries matrix) a b c d = k.val) :
    ∃ r : I64, max_sum_submatrix matrix k = ok r ∧ r.val = k.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (k : I64) (h : Pre matrix k)
    (hk : ∃ a b c d, RectValid (entries matrix) a b c d ∧
      rectSum (entries matrix) a b c d = k.val), ∃ r : I64, max_sum_submatrix matrix k = ok r ∧ r.val = k.val) := by
  sorry

end AegisSpec.MaxSumSubmatrix
