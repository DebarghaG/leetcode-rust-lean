import Aegis.SumDigitDifferences.Code.Funs

/-!
# Specifications of `Aegis.SumDigitDifferences.sum_digit_differences`

LeetCode problem `sum-of-digit-differences-of-all-pairs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SumDigitDifferences

def digit (p : ℕ) (x : ℤ) : ℤ := (x / (10 : ℤ) ^ p) % 10

def entry (nums : Slice I64) (i : ℕ) : ℤ :=
  match nums.val[i]? with
  | some x => x.val
  | none => 0

def diff (L : ℕ) (a b : ℤ) : ℤ :=
  (((Finset.range L).filter (fun p => digit p a ≠ digit p b)).card : ℤ)

def choosePairs (c : ℕ) : ℤ := ((c : ℤ) * ((c : ℤ) - 1)) / 2

def nePairs (nums : Slice I64) (n p : ℕ) : ℤ :=
  ((∑ i ∈ Finset.range n,
      ((Finset.Ico (i + 1) n).filter
          (fun j => digit p (entry nums i) ≠ digit p (entry nums j))).card) : ℤ)

def eqPairs (nums : Slice I64) (n p : ℕ) : ℤ :=
  ((∑ i ∈ Finset.range n,
      ((Finset.Ico (i + 1) n).filter
          (fun j => digit p (entry nums i) = digit p (entry nums j))).card) : ℤ)

def countDigit (nums : Slice I64) (n p : ℕ) (d : ℤ) : ℕ :=
  ((Finset.range n).filter (fun i => digit p (entry nums i) = d)).card

/-- Whenever the function returns a result r, r = sum_{0 <= i < j < n} diff(nums[i], nums[j]), where, for p >= 0, digit_p(x) = (floor(x / 10^p)) mod 10, and for positive a,b with the common L decimal digits, diff(a,b) = |{ p in {0,...,L-1} : digit_p(a) != digit_p(b) }|.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] < 10^9; and there is an integer L with 1 <= L <= 9 such that for every i with 0 <= i < n, 10^(L-1) <= nums[i] < 10^L (so all entries have the same number L of decimal digits). -/
theorem spec_1 (nums : Slice I64) (n L : ℕ) (r : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r) :
    r.val = ∑ i ∈ Finset.range n,
      ∑ j ∈ Finset.Ico (i + 1) n, diff L (entry nums i) (entry nums j) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (n L : ℕ) (r : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r), r.val = ∑ i ∈ Finset.range n,
      ∑ j ∈ Finset.Ico (i + 1) n, diff L (entry nums i) (entry nums j)) := by
  sorry

/-- The function returns a result r; it does not fail (no panic, overflow, or out-of-bounds) on any input satisfying the preconditions.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] < 10^9; and there is an integer L with 1 <= L <= 9 such that for every i with 0 <= i < n, 10^(L-1) <= nums[i] < 10^L. -/
theorem spec_2 (nums : Slice I64) (n L : ℕ)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L) :
    ∃ r : I64, Aegis.SumDigitDifferences.sum_digit_differences nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (n L : ℕ)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L), ∃ r : I64, Aegis.SumDigitDifferences.sum_digit_differences nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] < 10^9; and there is an integer L with 1 <= L <= 9 such that for every i with 0 <= i < n, 10^(L-1) <= nums[i] < 10^L. -/
theorem spec_3 (nums : Slice I64) (n L : ℕ) (r : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (n L : ℕ) (r : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= L * n * (n-1) / 2, where L is the common number of decimal digits from the preconditions.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] < 10^9; and there is an integer L with 1 <= L <= 9 such that for every i with 0 <= i < n, 10^(L-1) <= nums[i] < 10^L. -/
theorem spec_4 (nums : Slice I64) (n L : ℕ) (r : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r) :
    r.val ≤ (L : ℤ) * choosePairs n := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (n L : ℕ) (r : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r), r.val ≤ (L : ℤ) * choosePairs n) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if all entries of nums are equal, i.e. nums[0] = nums[1] = ... = nums[n-1].
  Preconditions: Let n = len(nums). Assume 2 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] < 10^9; and there is an integer L with 1 <= L <= 9 such that for every i with 0 <= i < n, 10^(L-1) <= nums[i] < 10^L. -/
theorem spec_5 (nums : Slice I64) (n L : ℕ) (r : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r) :
    r.val = 0 ↔ ∀ i, i < n → ∀ j, j < n → entry nums i = entry nums j := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (n L : ℕ) (r : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r), r.val = 0 ↔ ∀ i, i < n → ∀ j, j < n → entry nums i = entry nums j) := by
  sorry

/-- Whenever the function returns a result r, r = sum_{p=0}^{L-1} C_p, where C_p = |{(i,j) : 0 <= i < j < n and digit_p(nums[i]) != digit_p(nums[j])}|, with digit_p(x) = (floor(x / 10^p)) mod 10.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] < 10^9; and there is an integer L with 1 <= L <= 9 such that for every i with 0 <= i < n, 10^(L-1) <= nums[i] < 10^L. -/
theorem spec_6 (nums : Slice I64) (n L : ℕ) (r : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r) :
    r.val = ∑ p ∈ Finset.range L, nePairs nums n p := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (n L : ℕ) (r : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r), r.val = ∑ p ∈ Finset.range L, nePairs nums n p) := by
  sorry

/-- Whenever the function returns a result r, 2*r = sum_{0 <= i < n} sum_{0 <= j < n, i != j} diff(nums[i], nums[j]), where digit_p(x) = (floor(x / 10^p)) mod 10 and diff(a,b) = |{ p in {0,...,L-1} : digit_p(a) != digit_p(b) }|.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] < 10^9; and there is an integer L with 1 <= L <= 9 such that for every i with 0 <= i < n, 10^(L-1) <= nums[i] < 10^L. -/
theorem spec_7 (nums : Slice I64) (n L : ℕ) (r : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r) :
    2 * r.val = ∑ i ∈ Finset.range n,
      ∑ j ∈ (Finset.range n).erase i, diff L (entry nums i) (entry nums j) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (n L : ℕ) (r : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r), 2 * r.val = ∑ i ∈ Finset.range n,
      ∑ j ∈ (Finset.range n).erase i, diff L (entry nums i) (entry nums j)) := by
  sorry

/-- If nums' is any array satisfying the same preconditions and having the same multiset of entries as nums (i.e. nums' is a permutation of nums), and if the function returns r on nums and r' on nums', then r = r'.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] < 10^9; and there is an integer L with 1 <= L <= 9 such that for every i with 0 <= i < n, 10^(L-1) <= nums[i] < 10^L. -/
theorem spec_8 (nums nums' : Slice I64) (n L : ℕ) (r r' : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hn' : n = nums'.val.length)
    (hperm : nums'.val.Perm nums.val)
    (hpos' : ∀ i, i < n → 1 ≤ entry nums' i)
    (hlt' : ∀ i, i < n → entry nums' i < (10 : ℤ) ^ 9)
    (hLdig' : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums' i ∧ entry nums' i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r)
    (hr' : Aegis.SumDigitDifferences.sum_digit_differences nums' = ok r') :
    r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice I64) (n L : ℕ) (r r' : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hn' : n = nums'.val.length)
    (hperm : nums'.val.Perm nums.val)
    (hpos' : ∀ i, i < n → 1 ≤ entry nums' i)
    (hlt' : ∀ i, i < n → entry nums' i < (10 : ℤ) ^ 9)
    (hLdig' : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums' i ∧ entry nums' i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r)
    (hr' : Aegis.SumDigitDifferences.sum_digit_differences nums' = ok r'), r = r') := by
  sorry

/-- Whenever the function returns a result r, for every pair of indices i,j with 0 <= i < j < n, diff(nums[i], nums[j]) <= r, where digit_p(x) = (floor(x / 10^p)) mod 10 and diff(a,b) = |{ p in {0,...,L-1} : digit_p(a) != digit_p(b) }|.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] < 10^9; and there is an integer L with 1 <= L <= 9 such that for every i with 0 <= i < n, 10^(L-1) <= nums[i] < 10^L. -/
theorem spec_9 (nums : Slice I64) (n L : ℕ) (r : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r) :
    ∀ i, i < n → ∀ j, i < j → j < n → diff L (entry nums i) (entry nums j) ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (n L : ℕ) (r : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r), ∀ i, i < n → ∀ j, i < j → j < n → diff L (entry nums i) (entry nums j) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = L * n * (n-1) / 2 - sum_{p=0}^{L-1} E_p, where E_p = |{(i,j) : 0 <= i < j < n and digit_p(nums[i]) = digit_p(nums[j])}|, with digit_p(x) = (floor(x / 10^p)) mod 10.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] < 10^9; and there is an integer L with 1 <= L <= 9 such that for every i with 0 <= i < n, 10^(L-1) <= nums[i] < 10^L. -/
theorem spec_10 (nums : Slice I64) (n L : ℕ) (r : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r) :
    r.val = (L : ℤ) * choosePairs n - ∑ p ∈ Finset.range L, eqPairs nums n p := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (n L : ℕ) (r : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r), r.val = (L : ℤ) * choosePairs n - ∑ p ∈ Finset.range L, eqPairs nums n p) := by
  sorry

/-- Let k be any index with 0 <= k < n, and assume n < 10^5. Let nums' be the length n+1 array with nums'[i] = nums[i] for 0 <= i < n and nums'[n] = nums[k]. Whenever the function returns r on nums and r' on nums', r' = r + sum_{i=0}^{n-1} diff(nums[i], nums[k]), where digit_p(x) = (floor(x / 10^p)) mod 10 and diff(a,b) = |{ p in {0,...,L-1} : digit_p(a) != digit_p(b) }|.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] < 10^9; and there is an integer L with 1 <= L <= 9 such that for every i with 0 <= i < n, 10^(L-1) <= nums[i] < 10^L. -/
theorem spec_11 (nums nums' : Slice I64) (n L k : ℕ) (r r' : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hk : k < n) (hn6 : n < 10 ^ 5)
    (hn' : nums'.val.length = n + 1)
    (hagree : ∀ i, i < n → entry nums' i = entry nums i)
    (hlast : entry nums' n = entry nums k)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r)
    (hr' : Aegis.SumDigitDifferences.sum_digit_differences nums' = ok r') :
    r'.val = r.val + ∑ i ∈ Finset.range n, diff L (entry nums i) (entry nums k) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums' : Slice I64) (n L k : ℕ) (r r' : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hk : k < n) (hn6 : n < 10 ^ 5)
    (hn' : nums'.val.length = n + 1)
    (hagree : ∀ i, i < n → entry nums' i = entry nums i)
    (hlast : entry nums' n = entry nums k)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r)
    (hr' : Aegis.SumDigitDifferences.sum_digit_differences nums' = ok r'), r'.val = r.val + ∑ i ∈ Finset.range n, diff L (entry nums i) (entry nums k)) := by
  sorry

/-- Assume L <= 8. For any integer d with 1 <= d <= 9, let nums' be the length-n array with nums'[i] = nums[i] + d * 10^L for 0 <= i < n. Then all entries of nums' have the same number L+1 of decimal digits, and whenever the function returns r on nums and r' on nums', r' = r.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] < 10^9; and there is an integer L with 1 <= L <= 9 such that for every i with 0 <= i < n, 10^(L-1) <= nums[i] < 10^L. -/
theorem spec_12 (nums nums' : Slice I64) (n L d : ℕ) (r r' : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hL8 : L ≤ 8) (hd1 : 1 ≤ d) (hd9 : d ≤ 9)
    (hn' : nums'.val.length = n)
    (hshift : ∀ i, i < n → entry nums' i = entry nums i + (d : ℤ) * (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r)
    (hr' : Aegis.SumDigitDifferences.sum_digit_differences nums' = ok r') :
    (∀ i, i < n → (10 : ℤ) ^ L ≤ entry nums' i ∧ entry nums' i < (10 : ℤ) ^ (L + 1)) ∧
      r'.val = r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums' : Slice I64) (n L d : ℕ) (r r' : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hL8 : L ≤ 8) (hd1 : 1 ≤ d) (hd9 : d ≤ 9)
    (hn' : nums'.val.length = n)
    (hshift : ∀ i, i < n → entry nums' i = entry nums i + (d : ℤ) * (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r)
    (hr' : Aegis.SumDigitDifferences.sum_digit_differences nums' = ok r'), (∀ i, i < n → (10 : ℤ) ^ L ≤ entry nums' i ∧ entry nums' i < (10 : ℤ) ^ (L + 1)) ∧
      r'.val = r.val) := by
  sorry

/-- Whenever the function returns a result r, r = sum_{p=0}^{L-1} ( (n*(n-1))/2 - sum_{d=0}^{9} (c_{p,d}*(c_{p,d}-1))/2 ), where c_{p,d} = |{ i : 0 <= i < n and digit_p(nums[i]) = d }| and digit_p(x) = (floor(x / 10^p)) mod 10.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 10^5; for every i with 0 <= i < n, 1 <= nums[i] < 10^9; and there is an integer L with 1 <= L <= 9 such that for every i with 0 <= i < n, 10^(L-1) <= nums[i] < 10^L (so all entries have the same number L of decimal digits). -/
theorem spec_13 (nums : Slice I64) (n L : ℕ) (r : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r) :
    r.val = ∑ p ∈ Finset.range L,
      (choosePairs n - ∑ d ∈ Finset.range 10, choosePairs (countDigit nums n p (d : ℤ))) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64) (n L : ℕ) (r : I64)
    (hn2 : 2 ≤ n) (hn5 : n ≤ 10 ^ 5) (hn : n = nums.val.length)
    (hpos : ∀ i, i < n → 1 ≤ entry nums i)
    (hlt : ∀ i, i < n → entry nums i < (10 : ℤ) ^ 9)
    (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hLdig : ∀ i, i < n →
      (10 : ℤ) ^ (L - 1) ≤ entry nums i ∧ entry nums i < (10 : ℤ) ^ L)
    (hr : Aegis.SumDigitDifferences.sum_digit_differences nums = ok r), r.val = ∑ p ∈ Finset.range L,
      (choosePairs n - ∑ d ∈ Finset.range 10, choosePairs (countDigit nums n p (d : ℤ)))) := by
  sorry

end AegisSpec.SumDigitDifferences
