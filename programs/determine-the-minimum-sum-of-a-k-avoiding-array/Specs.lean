import Aegis.MinimumSum.Code.Funs

/-!
# Specifications of `Aegis.MinimumSum.minimum_sum`

LeetCode problem `determine-the-minimum-sum-of-a-k-avoiding-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas.Std
open Aeneas.Std.Result

namespace AegisSpec.MinimumSum

def half (k : ℤ) : ℤ := k / 2

def AllPositive (A : List ℤ) : Prop := ∀ x ∈ A, 0 < x

def KAvoiding (k : ℤ) (A : List ℤ) : Prop :=
  ∀ i j, (hi : i < A.length) → (hj : j < A.length) → i ≠ j → A[i] + A[j] ≠ k

def IsValidArray (n k : ℤ) (A : List ℤ) : Prop :=
  (A.length : ℤ) = n ∧ A.Nodup ∧ AllPositive A ∧ KAvoiding k A

def minSum (n k : ℤ) : ℤ :=
  if n ≤ half k then
    n * (n + 1) / 2
  else
    half k * (half k + 1) / 2 + (n - half k) * k + (n - half k) * (n - half k - 1) / 2

def optimalSet (n k : ℤ) : Set ℤ :=
  if n ≤ half k then
    Set.Icc 1 n
  else
    Set.Icc 1 (half k) ∪ Set.Icc k (k + n - half k - 1)

def maxEntry (n k : ℤ) : ℤ :=
  if n ≤ half k then n else k + n - half k - 1

/-- The function returns a result r, and r is the minimum possible sum of a length-n k-avoiding array of pairwise distinct positive integers. Equivalently, letting m = floor(k/2): if n <= m then r = n*(n+1)/2; if n > m then r = m*(m+1)/2 + (n-m)*k + (n-m)*(n-m-1)/2.
  Preconditions: n and k are integers satisfying 1 <= n <= 50 and 1 <= k <= 50. -/
theorem spec_1 (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50) :
    ∃ r, Aegis.MinimumSum.minimum_sum n k = ok r ∧ r.val = minSum n.val k.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50), ∃ r, Aegis.MinimumSum.minimum_sum n k = ok r ∧ r.val = minSum n.val k.val) := by
  sorry

/-- For every such n and k, the function returns a result r; it does not fail, overflow, or panic.
  Preconditions: n and k are integers satisfying 1 <= n <= 50 and 1 <= k <= 50. -/
theorem spec_2 (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50) :
    ∃ r, Aegis.MinimumSum.minimum_sum n k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50), ∃ r, Aegis.MinimumSum.minimum_sum n k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= n*(n+1)/2.
  Preconditions: n and k are integers satisfying 1 <= n <= 50 and 1 <= k <= 50. -/
theorem spec_3 (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50) :
    ∀ r, Aegis.MinimumSum.minimum_sum n k = ok r → n.val * (n.val + 1) / 2 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50), ∀ r, Aegis.MinimumSum.minimum_sum n k = ok r → n.val * (n.val + 1) / 2 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= n*(2*k + n - 1)/2.
  Preconditions: n and k are integers satisfying 1 <= n <= 50 and 1 <= k <= 50. -/
theorem spec_4 (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50) :
    ∀ r, Aegis.MinimumSum.minimum_sum n k = ok r →
      r.val ≤ n.val * (2 * k.val + n.val - 1) / 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50), ∀ r, Aegis.MinimumSum.minimum_sum n k = ok r →
      r.val ≤ n.val * (2 * k.val + n.val - 1) / 2) := by
  sorry

/-- Whenever the function returns a result r, there exists a sequence A of length n such that: every A[i] is a positive integer; A[i] != A[j] for all 0 <= i < j < n; A[i] + A[j] != k for all 0 <= i < n and 0 <= j < n with i != j; and the sum of A[0] through A[n-1] equals r.
  Preconditions: n and k are integers satisfying 1 <= n <= 50 and 1 <= k <= 50. -/
theorem spec_5 (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50) :
    ∀ r, Aegis.MinimumSum.minimum_sum n k = ok r →
      ∃ A : List ℤ, IsValidArray n.val k.val A ∧ A.sum = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50), ∀ r, Aegis.MinimumSum.minimum_sum n k = ok r →
      ∃ A : List ℤ, IsValidArray n.val k.val A ∧ A.sum = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every sequence A of length n of positive integers with all entries pairwise distinct and with A[i] + A[j] != k for all 0 <= i < n and 0 <= j < n with i != j, the sum of the entries of A is at least r.
  Preconditions: n and k are integers satisfying 1 <= n <= 50 and 1 <= k <= 50. -/
theorem spec_6 (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50) :
    ∀ r, Aegis.MinimumSum.minimum_sum n k = ok r →
      ∀ A : List ℤ, IsValidArray n.val k.val A → r.val ≤ A.sum := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50), ∀ r, Aegis.MinimumSum.minimum_sum n k = ok r →
      ∀ A : List ℤ, IsValidArray n.val k.val A → r.val ≤ A.sum) := by
  sorry

/-- Whenever the function returns a result r, every sequence A of length n of pairwise distinct positive integers that is k-avoiding and has sum exactly r has its set of entries equal to S, where S is defined as follows. If n <= floor(k/2), S = {1,2,...,n}. If n > floor(k/2), let m = floor(k/2); S = {1,2,...,m} union {k, k+1, ..., k + n - m - 1}, with the first block empty when m = 0.
  Preconditions: n and k are integers satisfying 1 <= n <= 50 and 1 <= k <= 50. -/
theorem spec_7 (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50) :
    ∀ r, Aegis.MinimumSum.minimum_sum n k = ok r →
      ∀ A : List ℤ, IsValidArray n.val k.val A → A.sum = r.val →
        (A.toFinset : Set ℤ) = optimalSet n.val k.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50), ∀ r, Aegis.MinimumSum.minimum_sum n k = ok r →
      ∀ A : List ℤ, IsValidArray n.val k.val A → A.sum = r.val →
        (A.toFinset : Set ℤ) = optimalSet n.val k.val) := by
  sorry

/-- Whenever the function returns a result r, every sequence A of length n of pairwise distinct positive integers that is k-avoiding and has sum exactly r contains exactly min(n, floor(k/2)) entries whose value is strictly less than k.
  Preconditions: n and k are integers satisfying 1 <= n <= 50 and 1 <= k <= 50. -/
theorem spec_8 (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50) :
    ∀ r, Aegis.MinimumSum.minimum_sum n k = ok r →
      ∀ A : List ℤ, IsValidArray n.val k.val A → A.sum = r.val →
        ((A.filter (fun x => decide (x < k.val))).length : ℤ) = min n.val (half k.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50), ∀ r, Aegis.MinimumSum.minimum_sum n k = ok r →
      ∀ A : List ℤ, IsValidArray n.val k.val A → A.sum = r.val →
        ((A.filter (fun x => decide (x < k.val))).length : ℤ) = min n.val (half k.val)) := by
  sorry

/-- Whenever the function returns a result r, every sequence A of length n of pairwise distinct positive integers that is k-avoiding and has sum exactly r has maximum entry M given by: M = n if n <= floor(k/2); M = k + n - floor(k/2) - 1 if n > floor(k/2).
  Preconditions: n and k are integers satisfying 1 <= n <= 50 and 1 <= k <= 50. -/
theorem spec_9 (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50) :
    ∀ r, Aegis.MinimumSum.minimum_sum n k = ok r →
      ∀ A : List ℤ, IsValidArray n.val k.val A → A.sum = r.val →
        (∀ x ∈ A, x ≤ maxEntry n.val k.val) ∧ maxEntry n.val k.val ∈ A := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50), ∀ r, Aegis.MinimumSum.minimum_sum n k = ok r →
      ∀ A : List ℤ, IsValidArray n.val k.val A → A.sum = r.val →
        (∀ x ∈ A, x ≤ maxEntry n.val k.val) ∧ maxEntry n.val k.val ∈ A) := by
  sorry

/-- Whenever the function returns a result r, r = n*(n+1)/2 if and only if k <= 2 or k >= 2*n.
  Preconditions: n and k are integers satisfying 1 <= n <= 50 and 1 <= k <= 50. -/
theorem spec_10 (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50) :
    ∀ r, Aegis.MinimumSum.minimum_sum n k = ok r →
      (r.val = n.val * (n.val + 1) / 2 ↔ k.val ≤ 2 ∨ 2 * n.val ≤ k.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50), ∀ r, Aegis.MinimumSum.minimum_sum n k = ok r →
      (r.val = n.val * (n.val + 1) / 2 ↔ k.val ≤ 2 ∨ 2 * n.val ≤ k.val)) := by
  sorry

/-- Let r1 be the result returned by minimum_sum(n,k) and r2 be the result returned by minimum_sum(n+1,k). Both calls return results and r2 > r1.
  Preconditions: n and k are integers satisfying 1 <= n < 50 and 1 <= k <= 50. -/
theorem spec_11 (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val < 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50) :
    ∃ r1 r2, Aegis.MinimumSum.minimum_sum n k = ok r1 ∧
      Aegis.MinimumSum.minimum_sum (I64.ofInt (n.val + 1) (by scalar_tac)) k = ok r2 ∧
        r1.val < r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n k : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val < 50)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 50), ∃ r1 r2, Aegis.MinimumSum.minimum_sum n k = ok r1 ∧
      Aegis.MinimumSum.minimum_sum (I64.ofInt (n.val + 1) (by scalar_tac)) k = ok r2 ∧
        r1.val < r2.val) := by
  sorry

end AegisSpec.MinimumSum
