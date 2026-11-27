import Aegis.SumCounts.Code.Funs

/-!
# Specifications of `Aegis.SumCounts.sum_counts`

LeetCode problem `subarrays-distinct-element-sum-of-squares-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SumCounts

open scoped BigOperators

def M : ℤ := 1000000007

theorem M_eq_MOD : M = Aegis.SumCounts.MOD.val := by
  simp [M, Aegis.SumCounts.MOD]

def vals (s : Slice I64) : List ℤ := s.val.map (fun x => x.val)

def len (s : Slice I64) : ℕ := s.val.length

def entry (s : Slice I64) (i : ℕ) : ℤ := (vals s).getD i 0

def distinctCount (l : List ℤ) : ℕ := l.dedup.length

def D (l : List ℤ) (i j : ℕ) : ℕ := distinctCount ((l.drop i).take (j + 1 - i))

def T (l : List ℤ) : ℕ :=
  ∑ i ∈ Finset.range l.length,
    ∑ j ∈ Finset.range l.length, if i ≤ j then D l i j ^ 2 else 0

def suffixDistinctCount (l : List ℤ) (i : ℕ) : ℕ := distinctCount (l.drop i)

def dropLast (s : Slice I64) : List ℤ := (vals s).take (len s - 1)

/-- Let M = 1000000007. For 0 <= i <= j < n, let D(i,j) be the number of distinct values in the contiguous subarray nums[i], nums[i+1], ..., nums[j]. Let T = sum_{i=0}^{n-1} sum_{j=i}^{n-1} D(i,j)^2. Whenever sum_counts(nums) returns a result r, r is the unique integer such that 0 <= r < M and r ≡ T (mod M).
  Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_1 (nums : Slice I64) (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000) :
    ∀ r, Aegis.SumCounts.sum_counts nums = ok r →
      0 ≤ r.val ∧ r.val < M ∧ Int.ModEq M r.val (T (vals nums) : ℤ) ∧
        ∀ k : ℤ, 0 ≤ k → k < M → Int.ModEq M k (T (vals nums) : ℤ) → k = r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000), ∀ r, Aegis.SumCounts.sum_counts nums = ok r →
      0 ≤ r.val ∧ r.val < M ∧ Int.ModEq M r.val (T (vals nums) : ℤ) ∧
        ∀ k : ℤ, 0 ≤ k → k < M → Int.ModEq M k (T (vals nums) : ℤ) → k = r.val) := by
  sorry

/-- sum_counts(nums) returns a result r; in particular, execution does not fail by panic, out-of-bounds access, or 64-bit integer overflow.
  Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_2 (nums : Slice I64) (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000) :
    ∃ r, Aegis.SumCounts.sum_counts nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000), ∃ r, Aegis.SumCounts.sum_counts nums = ok r) := by
  sorry

/-- sum_counts(nums) returns a result r and r = 1.
  Preconditions: Let n = len(nums). 1 <= n <= 100000, for every i with 0 <= i < n, 1 <= nums[i] <= 100000, and n = 1. -/
theorem spec_3 (nums : Slice I64) (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
    (h_len : len nums = 1) :
    ∃ r, Aegis.SumCounts.sum_counts nums = ok r ∧ r.val = 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
    (h_len : len nums = 1), ∃ r, Aegis.SumCounts.sum_counts nums = ok r ∧ r.val = 1) := by
  sorry

/-- sum_counts(nums) returns a result r, and r = 3 if nums[0] = nums[1], while r = 6 if nums[0] != nums[1].
  Preconditions: Let n = len(nums). 1 <= n <= 100000, for every i with 0 <= i < n, 1 <= nums[i] <= 100000, and n = 2. -/
theorem spec_4 (nums : Slice I64) (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
    (h_len : len nums = 2) :
    ∃ r, Aegis.SumCounts.sum_counts nums = ok r ∧
      (entry nums 0 = entry nums 1 → r.val = 3) ∧
      (entry nums 0 ≠ entry nums 1 → r.val = 6) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
    (h_len : len nums = 2), ∃ r, Aegis.SumCounts.sum_counts nums = ok r ∧
      (entry nums 0 = entry nums 1 → r.val = 3) ∧
      (entry nums 0 ≠ entry nums 1 → r.val = 6)) := by
  sorry

/-- sum_counts(nums) returns a result r and r = ((n * (n + 1)) / 2) mod 1000000007.
  Preconditions: Let n = len(nums). 1 <= n <= 100000, for every i with 0 <= i < n, 1 <= nums[i] <= 100000, and for all i,j with 0 <= i < n and 0 <= j < n, nums[i] = nums[j]. -/
theorem spec_5 (nums : Slice I64) (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
    (h_const : ∀ i j : ℕ, i < len nums → j < len nums → entry nums i = entry nums j) :
    ∃ r, Aegis.SumCounts.sum_counts nums = ok r ∧
      r.val = (((len nums * (len nums + 1)) / 2 : ℕ) : ℤ) % M := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
    (h_const : ∀ i j : ℕ, i < len nums → j < len nums → entry nums i = entry nums j), ∃ r, Aegis.SumCounts.sum_counts nums = ok r ∧
      r.val = (((len nums * (len nums + 1)) / 2 : ℕ) : ℤ) % M) := by
  sorry

/-- sum_counts(nums) returns a result r and r = (sum_{l=1}^{n} (n - l + 1) * l * l) mod 1000000007.
  Preconditions: Let n = len(nums). 1 <= n <= 100000, for every i with 0 <= i < n, 1 <= nums[i] <= 100000, and for all i,j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_6 (nums : Slice I64) (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
    (h_neq : ∀ i j : ℕ, i < j → j < len nums → entry nums i ≠ entry nums j) :
    ∃ r, Aegis.SumCounts.sum_counts nums = ok r ∧
      r.val = (((∑ l ∈ Finset.Icc 1 (len nums), (len nums - l + 1) * l * l) : ℕ) : ℤ) % M := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
    (h_neq : ∀ i j : ℕ, i < j → j < len nums → entry nums i ≠ entry nums j), ∃ r, Aegis.SumCounts.sum_counts nums = ok r ∧
      r.val = (((∑ l ∈ Finset.Icc 1 (len nums), (len nums - l + 1) * l * l) : ℕ) : ℤ) % M) := by
  sorry

/-- Whenever sum_counts(nums) returns r and sum_counts(other) returns r_other, r = r_other.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= nums[i] <= 100000 for every 0 <= i < n, and let other be any slice of length n with 1 <= other[i] <= 100000 for every 0 <= i < n such that for all i,j with 0 <= i < n and 0 <= j < n, nums[i] = nums[j] iff other[i] = other[j]. -/
theorem spec_7 (nums other : Slice I64) (h_len_ge : 1 ≤ len nums)
    (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
    (h_len_other : len other = len nums)
    (h_bounds_other : ∀ i : ℕ, i < len other → 1 ≤ entry other i ∧ entry other i ≤ 100000)
    (h_pattern : ∀ i j : ℕ, i < len nums → j < len nums →
      (entry nums i = entry nums j ↔ entry other i = entry other j)) :
    ∀ r r_other, Aegis.SumCounts.sum_counts nums = ok r →
      Aegis.SumCounts.sum_counts other = ok r_other → r = r_other := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums other : Slice I64) (h_len_ge : 1 ≤ len nums)
    (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
    (h_len_other : len other = len nums)
    (h_bounds_other : ∀ i : ℕ, i < len other → 1 ≤ entry other i ∧ entry other i ≤ 100000)
    (h_pattern : ∀ i j : ℕ, i < len nums → j < len nums →
      (entry nums i = entry nums j ↔ entry other i = entry other j)), ∀ r r_other, Aegis.SumCounts.sum_counts nums = ok r →
      Aegis.SumCounts.sum_counts other = ok r_other → r = r_other) := by
  sorry

/-- Whenever sum_counts(nums) returns a result r, r = (T(A) + sum_{i=0}^{m} (d_i + 1)^2) mod 1000000007.
  Preconditions: Let n = len(nums) and m = n - 1. Assume 1 <= n <= 100000 and 1 <= nums[i] <= 100000 for every 0 <= i < n. Let A be the prefix of nums of length m, so A[i] = nums[i] for 0 <= i < m, and let x = nums[m]. Assume x != A[i] for every 0 <= i < m. For 0 <= i <= m define d_i as the number of distinct values in A[i], A[i+1], ..., A[m-1] when i < m, and d_m = 0 for the empty suffix. Let T(A) be the sum over all nonempty contiguous subarrays of A of the square of their distinct count, with T(A) = 0 if m = 0. -/
theorem spec_8 (nums : Slice I64) (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
    (h_new : ∀ i : ℕ, i < len nums - 1 → entry nums i ≠ entry nums (len nums - 1)) :
    ∀ r, Aegis.SumCounts.sum_counts nums = ok r →
      r.val = (((T (dropLast nums) +
          ∑ i ∈ Finset.range (len nums - 1 + 1),
            (suffixDistinctCount (dropLast nums) i + 1) ^ 2) : ℕ) : ℤ) % M := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
    (h_new : ∀ i : ℕ, i < len nums - 1 → entry nums i ≠ entry nums (len nums - 1)), ∀ r, Aegis.SumCounts.sum_counts nums = ok r →
      r.val = (((T (dropLast nums) +
          ∑ i ∈ Finset.range (len nums - 1 + 1),
            (suffixDistinctCount (dropLast nums) i + 1) ^ 2) : ℕ) : ℤ) % M) := by
  sorry

/-- Whenever sum_counts(nums) returns a result r, r = (T(A) + sum_{i=0}^{m-1} d_i^2 + 1) mod 1000000007.
  Preconditions: Let n = len(nums), m = n - 1, and assume n >= 2. Assume 1 <= n <= 100000 and 1 <= nums[i] <= 100000 for every 0 <= i < n. Let A be the prefix of nums of length m, so A[i] = nums[i] for 0 <= i < m. Assume nums[m] = nums[m-1]. For 0 <= i < m define d_i as the number of distinct values in A[i], A[i+1], ..., A[m-1]. Let T(A) be the sum over all nonempty contiguous subarrays of A of the square of their distinct count. -/
theorem spec_9 (nums : Slice I64) (h_len_ge : 2 ≤ len nums) (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
    (h_last : entry nums (len nums - 1) = entry nums (len nums - 2)) :
    ∀ r, Aegis.SumCounts.sum_counts nums = ok r →
      r.val = (((T (dropLast nums) +
          ∑ i ∈ Finset.range (len nums - 1), suffixDistinctCount (dropLast nums) i ^ 2) +
          1 : ℕ) : ℤ) % M := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (h_len_ge : 2 ≤ len nums) (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000)
    (h_last : entry nums (len nums - 1) = entry nums (len nums - 2)), ∀ r, Aegis.SumCounts.sum_counts nums = ok r →
      r.val = (((T (dropLast nums) +
          ∑ i ∈ Finset.range (len nums - 1), suffixDistinctCount (dropLast nums) i ^ 2) +
          1 : ℕ) : ℤ) % M) := by
  sorry

/-- Whenever sum_counts(nums) returns a result r, r = T(rev) mod 1000000007.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and 1 <= nums[i] <= 100000 for every 0 <= i < n. Let rev be the slice of length n defined by rev[i] = nums[n - 1 - i] for 0 <= i < n. Let T(rev) be the sum over all 0 <= i <= j < n of the square of the number of distinct values in rev[i], rev[i+1], ..., rev[j]. -/
theorem spec_10 (nums : Slice I64) (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000) :
    ∀ r, Aegis.SumCounts.sum_counts nums = ok r →
      r.val = (((T (vals nums).reverse) : ℕ) : ℤ) % M := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (h_len_ge : 1 ≤ len nums) (h_len_le : len nums ≤ 100000)
    (h_bounds : ∀ i : ℕ, i < len nums → 1 ≤ entry nums i ∧ entry nums i ≤ 100000), ∀ r, Aegis.SumCounts.sum_counts nums = ok r →
      r.val = (((T (vals nums).reverse) : ℕ) : ℤ) % M) := by
  sorry

end AegisSpec.SumCounts
