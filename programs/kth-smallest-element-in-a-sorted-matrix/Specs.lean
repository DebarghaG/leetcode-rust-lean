import Aegis.KthSmallest.Code.Funs

/-!
# Specifications of `Aegis.KthSmallest.kth_smallest`

LeetCode problem `kth-smallest-element-in-a-sorted-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.KthSmallest

abbrev Mat : Type := Slice (alloc.vec.Vec Std.I64)

def rows (M : Mat) : List (List Int) := M.val.map (fun row => row.val.map (fun x => x.val))

def n (M : Mat) : Nat := (rows M).length

def rowOf (M : Mat) (i : Nat) : List Int := (rows M).getD i []

def cell (M : Mat) (i j : Nat) : Int := (rowOf M i).getD j 0

def entries (M : Mat) : List Int := (rows M).flatten

def countLt (M : Mat) (v : Int) : Nat := (entries M).countP (fun x => decide (x < v))

def countLe (M : Mat) (v : Int) : Nat := (entries M).countP (fun x => decide (x ≤ v))

def countEq (M : Mat) (v : Int) : Nat := (entries M).countP (fun x => decide (x = v))

def ValidInput (M : Mat) (k : Std.I64) : Prop :=
  1 ≤ n M ∧
  n M ≤ 300 ∧
  (∀ i, i < n M → (rowOf M i).length = n M) ∧
  (∀ i, i < n M → ∀ j, j < n M →
    (-1000000000 : Int) ≤ cell M i j ∧ cell M i j ≤ 1000000000) ∧
  (∀ i, i < n M → ∀ j, j + 1 < n M → cell M i j ≤ cell M i (j + 1)) ∧
  (∀ j, j < n M → ∀ i, i + 1 < n M → cell M i j ≤ cell M (i + 1) j) ∧
  1 ≤ k.val ∧
  k.val ≤ (n M : Int) ^ 2

/-- Under the preconditions, the function returns a result r and r is the kth smallest entry of the multiset of all n^2 entries of matrix, counted with multiplicity and indexed from 1. Equivalently: the number of entries strictly less than r is less than k, and the number of entries less than or equal to r is at least k.
  Preconditions: Let n = len(matrix). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(matrix[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, -10^9 <= matrix[i][j] <= 10^9; for every i with 0 <= i < n and every j with 0 <= j < n-1, matrix[i][j] <= matrix[i][j+1]; for every j with 0 <= j < n and every i with 0 <= i < n-1, matrix[i][j] <= matrix[i+1][j]; and 1 <= k <= n^2. -/
theorem spec_1 (M : Mat) (k : Std.I64) (hM : ValidInput M k) :
    ∃ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r ∧
        (countLt M r.val : Int) < k.val ∧ k.val ≤ (countLe M r.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (M : Mat) (k : Std.I64) (hM : ValidInput M k), ∃ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r ∧
        (countLt M r.val : Int) < k.val ∧ k.val ≤ (countLe M r.val : Int)) := by
  sorry

/-- Under the preconditions, the function returns a result r; it does not fail (no arithmetic overflow, no out-of-bounds access, no panic).
  Preconditions: Let n = len(matrix). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(matrix[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, -10^9 <= matrix[i][j] <= 10^9; for every i with 0 <= i < n and every j with 0 <= j < n-1, matrix[i][j] <= matrix[i][j+1]; for every j with 0 <= j < n and every i with 0 <= i < n-1, matrix[i][j] <= matrix[i+1][j]; and 1 <= k <= n^2. -/
theorem spec_2 (M : Mat) (k : Std.I64) (hM : ValidInput M k) :
    ∃ r : Std.I64, Aegis.KthSmallest.kth_smallest M k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (M : Mat) (k : Std.I64) (hM : ValidInput M k), ∃ r : Std.I64, Aegis.KthSmallest.kth_smallest M k = ok r) := by
  sorry

/-- Under the preconditions, if the function returns r, then matrix[0][0] <= r <= matrix[n-1][n-1].
  Preconditions: Let n = len(matrix). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(matrix[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, -10^9 <= matrix[i][j] <= 10^9; for every i with 0 <= i < n and every j with 0 <= j < n-1, matrix[i][j] <= matrix[i][j+1]; for every j with 0 <= j < n and every i with 0 <= i < n-1, matrix[i][j] <= matrix[i+1][j]; and 1 <= k <= n^2. -/
theorem spec_3 (M : Mat) (k : Std.I64) (hM : ValidInput M k) :
    ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r →
        cell M 0 0 ≤ r.val ∧ r.val ≤ cell M (n M - 1) (n M - 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (M : Mat) (k : Std.I64) (hM : ValidInput M k), ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r →
        cell M 0 0 ≤ r.val ∧ r.val ≤ cell M (n M - 1) (n M - 1)) := by
  sorry

/-- Under the preconditions, if the function returns r, then there exist indices i and j with 0 <= i < n and 0 <= j < n such that matrix[i][j] = r.
  Preconditions: Let n = len(matrix). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(matrix[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, -10^9 <= matrix[i][j] <= 10^9; for every i with 0 <= i < n and every j with 0 <= j < n-1, matrix[i][j] <= matrix[i][j+1]; for every j with 0 <= j < n and every i with 0 <= i < n-1, matrix[i][j] <= matrix[i+1][j]; and 1 <= k <= n^2. -/
theorem spec_4 (M : Mat) (k : Std.I64) (hM : ValidInput M k) :
    ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r →
        ∃ i j : Nat, i < n M ∧ j < n M ∧ cell M i j = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (M : Mat) (k : Std.I64) (hM : ValidInput M k), ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r →
        ∃ i j : Nat, i < n M ∧ j < n M ∧ cell M i j = r.val) := by
  sorry

/-- Under the preconditions, if the function returns r, then the number of pairs (i,j) with 0 <= i < n, 0 <= j < n and matrix[i][j] < r is at most k-1 (equivalently, strictly less than k).
  Preconditions: Let n = len(matrix). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(matrix[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, -10^9 <= matrix[i][j] <= 10^9; for every i with 0 <= i < n and every j with 0 <= j < n-1, matrix[i][j] <= matrix[i][j+1]; for every j with 0 <= j < n and every i with 0 <= i < n-1, matrix[i][j] <= matrix[i+1][j]; and 1 <= k <= n^2. -/
theorem spec_5 (M : Mat) (k : Std.I64) (hM : ValidInput M k) :
    ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r → (countLt M r.val : Int) ≤ k.val - 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (M : Mat) (k : Std.I64) (hM : ValidInput M k), ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r → (countLt M r.val : Int) ≤ k.val - 1) := by
  sorry

/-- Under the preconditions, if the function returns r, then the number of pairs (i,j) with 0 <= i < n, 0 <= j < n and matrix[i][j] <= r is at least k.
  Preconditions: Let n = len(matrix). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(matrix[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, -10^9 <= matrix[i][j] <= 10^9; for every i with 0 <= i < n and every j with 0 <= j < n-1, matrix[i][j] <= matrix[i][j+1]; for every j with 0 <= j < n and every i with 0 <= i < n-1, matrix[i][j] <= matrix[i+1][j]; and 1 <= k <= n^2. -/
theorem spec_6 (M : Mat) (k : Std.I64) (hM : ValidInput M k) :
    ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r → k.val ≤ (countLe M r.val : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (M : Mat) (k : Std.I64) (hM : ValidInput M k), ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r → k.val ≤ (countLe M r.val : Int)) := by
  sorry

/-- Under the preconditions, if the function returns r, then for every integer v with v < r, the number of entries of matrix that are less than or equal to v is less than k.
  Preconditions: Let n = len(matrix). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(matrix[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, -10^9 <= matrix[i][j] <= 10^9; for every i with 0 <= i < n and every j with 0 <= j < n-1, matrix[i][j] <= matrix[i][j+1]; for every j with 0 <= j < n and every i with 0 <= i < n-1, matrix[i][j] <= matrix[i+1][j]; and 1 <= k <= n^2. -/
theorem spec_7 (M : Mat) (k : Std.I64) (hM : ValidInput M k) :
    ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r →
        ∀ v : Int, v < r.val → (countLe M v : Int) < k.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (M : Mat) (k : Std.I64) (hM : ValidInput M k), ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r →
        ∀ v : Int, v < r.val → (countLe M v : Int) < k.val) := by
  sorry

/-- Under the preconditions, if the function returns r, then for every integer v with v > r, the number of entries of matrix that are strictly less than v is at least k.
  Preconditions: Let n = len(matrix). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(matrix[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, -10^9 <= matrix[i][j] <= 10^9; for every i with 0 <= i < n and every j with 0 <= j < n-1, matrix[i][j] <= matrix[i][j+1]; for every j with 0 <= j < n and every i with 0 <= i < n-1, matrix[i][j] <= matrix[i+1][j]; and 1 <= k <= n^2. -/
theorem spec_8 (M : Mat) (k : Std.I64) (hM : ValidInput M k) :
    ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r →
        ∀ v : Int, r.val < v → k.val ≤ (countLt M v : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (M : Mat) (k : Std.I64) (hM : ValidInput M k), ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r →
        ∀ v : Int, r.val < v → k.val ≤ (countLt M v : Int)) := by
  sorry

/-- Under the preconditions, if the function returns r, let L be the number of entries strictly less than r and let E be the number of entries equal to r. Then L < k <= L + E.
  Preconditions: Let n = len(matrix). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(matrix[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, -10^9 <= matrix[i][j] <= 10^9; for every i with 0 <= i < n and every j with 0 <= j < n-1, matrix[i][j] <= matrix[i][j+1]; for every j with 0 <= j < n and every i with 0 <= i < n-1, matrix[i][j] <= matrix[i+1][j]; and 1 <= k <= n^2. -/
theorem spec_9 (M : Mat) (k : Std.I64) (hM : ValidInput M k) :
    ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r →
        (countLt M r.val : Int) < k.val ∧
          k.val ≤ (countLt M r.val : Int) + (countEq M r.val : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (M : Mat) (k : Std.I64) (hM : ValidInput M k), ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r →
        (countLt M r.val : Int) < k.val ∧
          k.val ≤ (countLt M r.val : Int) + (countEq M r.val : Int)) := by
  sorry

/-- Under the preconditions, if the function returns r, then for every integer v, if the number of entries strictly less than v is less than k and the number of entries less than or equal to v is at least k, then v = r.
  Preconditions: Let n = len(matrix). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(matrix[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, -10^9 <= matrix[i][j] <= 10^9; for every i with 0 <= i < n and every j with 0 <= j < n-1, matrix[i][j] <= matrix[i][j+1]; for every j with 0 <= j < n and every i with 0 <= i < n-1, matrix[i][j] <= matrix[i+1][j]; and 1 <= k <= n^2. -/
theorem spec_10 (M : Mat) (k : Std.I64) (hM : ValidInput M k) :
    ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r →
        ∀ v : Int,
          (countLt M v : Int) < k.val → k.val ≤ (countLe M v : Int) → v = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (M : Mat) (k : Std.I64) (hM : ValidInput M k), ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r →
        ∀ v : Int,
          (countLt M v : Int) < k.val → k.val ≤ (countLe M v : Int) → v = r.val) := by
  sorry

/-- Under the preconditions, if the function returns r, then for every integer v, if the number of entries strictly less than v is at least k, then r < v.
  Preconditions: Let n = len(matrix). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(matrix[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, -10^9 <= matrix[i][j] <= 10^9; for every i with 0 <= i < n and every j with 0 <= j < n-1, matrix[i][j] <= matrix[i][j+1]; for every j with 0 <= j < n and every i with 0 <= i < n-1, matrix[i][j] <= matrix[i+1][j]; and 1 <= k <= n^2. -/
theorem spec_11 (M : Mat) (k : Std.I64) (hM : ValidInput M k) :
    ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r →
        ∀ v : Int, k.val ≤ (countLt M v : Int) → r.val < v := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (M : Mat) (k : Std.I64) (hM : ValidInput M k), ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r →
        ∀ v : Int, k.val ≤ (countLt M v : Int) → r.val < v) := by
  sorry

/-- Under the preconditions, if the function returns r, then for every integer v, if the number of entries less than or equal to v is less than k, then r > v.
  Preconditions: Let n = len(matrix). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(matrix[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, -10^9 <= matrix[i][j] <= 10^9; for every i with 0 <= i < n and every j with 0 <= j < n-1, matrix[i][j] <= matrix[i][j+1]; for every j with 0 <= j < n and every i with 0 <= i < n-1, matrix[i][j] <= matrix[i+1][j]; and 1 <= k <= n^2. -/
theorem spec_12 (M : Mat) (k : Std.I64) (hM : ValidInput M k) :
    ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r →
        ∀ v : Int, (countLe M v : Int) < k.val → v < r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (M : Mat) (k : Std.I64) (hM : ValidInput M k), ∀ r : Std.I64,
      Aegis.KthSmallest.kth_smallest M k = ok r →
        ∀ v : Int, (countLe M v : Int) < k.val → v < r.val) := by
  sorry

/-- If M1 and M2 have the same multiset of entries (for every integer v, the number of entries equal to v is the same in M1 and M2), and if kth_smallest(M1, k) returns r1 and kth_smallest(M2, k) returns r2, then r1 = r2.
  Preconditions: Let M1 and M2 be two matrices each satisfying the preconditions above with the same n, and let k satisfy 1 <= k <= n^2. -/
theorem spec_13 (M1 M2 : Mat) (k : Std.I64) (hM1 : ValidInput M1 k) (hM2 : ValidInput M2 k)
    (hsame : ∀ v : Int, countEq M1 v = countEq M2 v) :
    ∀ r1 r2 : Std.I64,
      Aegis.KthSmallest.kth_smallest M1 k = ok r1 →
        Aegis.KthSmallest.kth_smallest M2 k = ok r2 → r1.val = r2.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (M1 M2 : Mat) (k : Std.I64) (hM1 : ValidInput M1 k) (hM2 : ValidInput M2 k)
    (hsame : ∀ v : Int, countEq M1 v = countEq M2 v), ∀ r1 r2 : Std.I64,
      Aegis.KthSmallest.kth_smallest M1 k = ok r1 →
        Aegis.KthSmallest.kth_smallest M2 k = ok r2 → r1.val = r2.val) := by
  sorry

/-- Under the preconditions, if kth_smallest(matrix, k1) returns r1 and kth_smallest(matrix, k2) returns r2, then r1 <= r2.
  Preconditions: Let n = len(matrix). The input satisfies: 1 <= n <= 300; each row has length n; entries are between -10^9 and 10^9; rows and columns are non-decreasing; and 1 <= k1 <= k2 <= n^2. -/
theorem spec_14 (M : Mat) (k1 k2 : Std.I64) (h1 : ValidInput M k1) (h2 : ValidInput M k2)
    (hk : k1.val ≤ k2.val) :
    ∀ r1 r2 : Std.I64,
      Aegis.KthSmallest.kth_smallest M k1 = ok r1 →
        Aegis.KthSmallest.kth_smallest M k2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (M : Mat) (k1 k2 : Std.I64) (h1 : ValidInput M k1) (h2 : ValidInput M k2)
    (hk : k1.val ≤ k2.val), ∀ r1 r2 : Std.I64,
      Aegis.KthSmallest.kth_smallest M k1 = ok r1 →
        Aegis.KthSmallest.kth_smallest M k2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

end AegisSpec.KthSmallest
