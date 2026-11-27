import Aegis.CountMatchingSubarrays.Code.Funs

/-!
# Specifications of `Aegis.CountMatchingSubarrays.count_matching_subarrays`

LeetCode problem `number-of-subarrays-that-match-a-pattern-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountMatchingSubarrays

open Aegis.CountMatchingSubarrays

def stepOK (p a b : Std.I64) : Prop :=
  (p.val = 1 → b.val > a.val) ∧ (p.val = 0 → b.val = a.val) ∧ (p.val = -1 → b.val < a.val)

def matchesAt (nums pattern : Slice Std.I64) (i : ℕ) : Prop :=
  ∀ (hbound : i + pattern.val.length < nums.val.length) (k : ℕ) (hk : k < pattern.val.length),
    stepOK (pattern.val[k]) (nums.val[i + k]) (nums.val[i + k + 1])

noncomputable def countMatches (nums pattern : Slice Std.I64) : ℕ := by
  classical
  exact ((Finset.range (nums.val.length - pattern.val.length)).filter
    (fun i => matchesAt nums pattern i)).card

/-- The function returns a result r, and r equals the number of integers i with 0 <= i < n - m such that, for every k with 0 <= k < m: if pattern[k] = 1 then nums[i + k + 1] > nums[i + k]; if pattern[k] = 0 then nums[i + k + 1] = nums[i + k]; and if pattern[k] = -1 then nums[i + k + 1] < nums[i + k].
  Preconditions: Let n = len(nums) and m = len(pattern). The preconditions are 2 <= n <= 100, 1 <= m < n, for every i with 0 <= i < n, 1 <= nums[i] <= 10^9, and for every k with 0 <= k < m, pattern[k] is -1, 0, or 1. -/
theorem spec_1 (nums pattern : Slice Std.I64)
    (hna : 2 ≤ nums.val.length) (hnb : nums.val.length ≤ 100)
    (hma : 1 ≤ pattern.val.length) (hmb : pattern.val.length < nums.val.length)
    (hnum : ∀ i (hi : i < nums.val.length), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hpat : ∀ k (hk : k < pattern.val.length),
      (pattern.val[k]).val = -1 ∨ (pattern.val[k]).val = 0 ∨ (pattern.val[k]).val = 1) :
    ∃ r : Std.I64, count_matching_subarrays nums pattern = ok r ∧
      r.val = (countMatches nums pattern : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums pattern : Slice Std.I64)
    (hna : 2 ≤ nums.val.length) (hnb : nums.val.length ≤ 100)
    (hma : 1 ≤ pattern.val.length) (hmb : pattern.val.length < nums.val.length)
    (hnum : ∀ i (hi : i < nums.val.length), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hpat : ∀ k (hk : k < pattern.val.length),
      (pattern.val[k]).val = -1 ∨ (pattern.val[k]).val = 0 ∨ (pattern.val[k]).val = 1), ∃ r : Std.I64, count_matching_subarrays nums pattern = ok r ∧
      r.val = (countMatches nums pattern : ℤ)) := by
  sorry

/-- The function returns a result r and 0 <= r <= len(nums) - len(pattern).
  Preconditions: Let n = len(nums) and m = len(pattern). The preconditions are 2 <= n <= 100, 1 <= m < n, for every i with 0 <= i < n, 1 <= nums[i] <= 10^9, and for every k with 0 <= k < m, pattern[k] is -1, 0, or 1. -/
theorem spec_2 (nums pattern : Slice Std.I64)
    (hna : 2 ≤ nums.val.length) (hnb : nums.val.length ≤ 100)
    (hma : 1 ≤ pattern.val.length) (hmb : pattern.val.length < nums.val.length)
    (hnum : ∀ i (hi : i < nums.val.length), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hpat : ∀ k (hk : k < pattern.val.length),
      (pattern.val[k]).val = -1 ∨ (pattern.val[k]).val = 0 ∨ (pattern.val[k]).val = 1) :
    ∃ r : Std.I64, count_matching_subarrays nums pattern = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) - (pattern.val.length : ℤ) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums pattern : Slice Std.I64)
    (hna : 2 ≤ nums.val.length) (hnb : nums.val.length ≤ 100)
    (hma : 1 ≤ pattern.val.length) (hmb : pattern.val.length < nums.val.length)
    (hnum : ∀ i (hi : i < nums.val.length), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hpat : ∀ k (hk : k < pattern.val.length),
      (pattern.val[k]).val = -1 ∨ (pattern.val[k]).val = 0 ∨ (pattern.val[k]).val = 1), ∃ r : Std.I64, count_matching_subarrays nums pattern = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) - (pattern.val.length : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result and does not fail: there is no panic, out-of-bounds access, or arithmetic overflow.
  Preconditions: Let n = len(nums) and m = len(pattern). The preconditions are 2 <= n <= 100, 1 <= m < n, for every i with 0 <= i < n, 1 <= nums[i] <= 10^9, and for every k with 0 <= k < m, pattern[k] is -1, 0, or 1. -/
theorem spec_3 (nums pattern : Slice Std.I64)
    (hna : 2 ≤ nums.val.length) (hnb : nums.val.length ≤ 100)
    (hma : 1 ≤ pattern.val.length) (hmb : pattern.val.length < nums.val.length)
    (hnum : ∀ i (hi : i < nums.val.length), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hpat : ∀ k (hk : k < pattern.val.length),
      (pattern.val[k]).val = -1 ∨ (pattern.val[k]).val = 0 ∨ (pattern.val[k]).val = 1) :
    ∃ r : Std.I64, count_matching_subarrays nums pattern = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums pattern : Slice Std.I64)
    (hna : 2 ≤ nums.val.length) (hnb : nums.val.length ≤ 100)
    (hma : 1 ≤ pattern.val.length) (hmb : pattern.val.length < nums.val.length)
    (hnum : ∀ i (hi : i < nums.val.length), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hpat : ∀ k (hk : k < pattern.val.length),
      (pattern.val[k]).val = -1 ∨ (pattern.val[k]).val = 0 ∨ (pattern.val[k]).val = 1), ∃ r : Std.I64, count_matching_subarrays nums pattern = ok r) := by
  sorry

/-- Whenever the function returns a result r, r > 0 if and only if there exists an integer i with 0 <= i < len(nums) - len(pattern) such that, for every k with 0 <= k < len(pattern), the comparison between nums[i+k+1] and nums[i+k] is >, =, or < according as pattern[k] is 1, 0, or -1 respectively.
  Preconditions: Let n = len(nums) and m = len(pattern). The preconditions are 2 <= n <= 100, 1 <= m < n, for every i with 0 <= i < n, 1 <= nums[i] <= 10^9, and for every k with 0 <= k < m, pattern[k] is -1, 0, or 1. -/
theorem spec_4 (nums pattern : Slice Std.I64)
    (hna : 2 ≤ nums.val.length) (hnb : nums.val.length ≤ 100)
    (hma : 1 ≤ pattern.val.length) (hmb : pattern.val.length < nums.val.length)
    (hnum : ∀ i (hi : i < nums.val.length), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hpat : ∀ k (hk : k < pattern.val.length),
      (pattern.val[k]).val = -1 ∨ (pattern.val[k]).val = 0 ∨ (pattern.val[k]).val = 1) :
    ∀ r : Std.I64, count_matching_subarrays nums pattern = ok r →
      (r.val > 0 ↔
        ∃ i : ℕ, i < nums.val.length - pattern.val.length ∧ matchesAt nums pattern i) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums pattern : Slice Std.I64)
    (hna : 2 ≤ nums.val.length) (hnb : nums.val.length ≤ 100)
    (hma : 1 ≤ pattern.val.length) (hmb : pattern.val.length < nums.val.length)
    (hnum : ∀ i (hi : i < nums.val.length), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hpat : ∀ k (hk : k < pattern.val.length),
      (pattern.val[k]).val = -1 ∨ (pattern.val[k]).val = 0 ∨ (pattern.val[k]).val = 1), ∀ r : Std.I64, count_matching_subarrays nums pattern = ok r →
      (r.val > 0 ↔
        ∃ i : ℕ, i < nums.val.length - pattern.val.length ∧ matchesAt nums pattern i)) := by
  sorry

/-- Whenever the function returns a result r, r = len(nums) - len(pattern) if and only if every integer i with 0 <= i < len(nums) - len(pattern) satisfies the matching condition: for every k with 0 <= k < len(pattern), nums[i+k+1] > nums[i+k] when pattern[k] = 1, nums[i+k+1] = nums[i+k] when pattern[k] = 0, and nums[i+k+1] < nums[i+k] when pattern[k] = -1.
  Preconditions: Let n = len(nums) and m = len(pattern). The preconditions are 2 <= n <= 100, 1 <= m < n, for every i with 0 <= i < n, 1 <= nums[i] <= 10^9, and for every k with 0 <= k < m, pattern[k] is -1, 0, or 1. -/
theorem spec_5 (nums pattern : Slice Std.I64)
    (hna : 2 ≤ nums.val.length) (hnb : nums.val.length ≤ 100)
    (hma : 1 ≤ pattern.val.length) (hmb : pattern.val.length < nums.val.length)
    (hnum : ∀ i (hi : i < nums.val.length), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hpat : ∀ k (hk : k < pattern.val.length),
      (pattern.val[k]).val = -1 ∨ (pattern.val[k]).val = 0 ∨ (pattern.val[k]).val = 1) :
    ∀ r : Std.I64, count_matching_subarrays nums pattern = ok r →
      (r.val = (nums.val.length : ℤ) - (pattern.val.length : ℤ) ↔
        ∀ i : ℕ, i < nums.val.length - pattern.val.length → matchesAt nums pattern i) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums pattern : Slice Std.I64)
    (hna : 2 ≤ nums.val.length) (hnb : nums.val.length ≤ 100)
    (hma : 1 ≤ pattern.val.length) (hmb : pattern.val.length < nums.val.length)
    (hnum : ∀ i (hi : i < nums.val.length), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hpat : ∀ k (hk : k < pattern.val.length),
      (pattern.val[k]).val = -1 ∨ (pattern.val[k]).val = 0 ∨ (pattern.val[k]).val = 1), ∀ r : Std.I64, count_matching_subarrays nums pattern = ok r →
      (r.val = (nums.val.length : ℤ) - (pattern.val.length : ℤ) ↔
        ∀ i : ℕ, i < nums.val.length - pattern.val.length → matchesAt nums pattern i)) := by
  sorry

/-- For every such c, if the function returns r on (nums, pattern) and returns r' on (nums', pattern), where nums'[i] = nums[i] + c for every i with 0 <= i < n, then r = r'.
  Preconditions: Let n = len(nums) and m = len(pattern). The preconditions are 2 <= n <= 100, 1 <= m < n, for every i with 0 <= i < n, 1 <= nums[i] <= 10^9, and for every k with 0 <= k < m, pattern[k] is -1, 0, or 1. Let c be an integer such that for every i with 0 <= i < n, nums[i] + c is between 1 and 10^9 inclusive. -/
theorem spec_6 (nums nums' pattern : Slice Std.I64) (c : ℤ)
    (hna : 2 ≤ nums.val.length) (hnb : nums.val.length ≤ 100)
    (hma : 1 ≤ pattern.val.length) (hmb : pattern.val.length < nums.val.length)
    (hnum : ∀ i (hi : i < nums.val.length), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hpat : ∀ k (hk : k < pattern.val.length),
      (pattern.val[k]).val = -1 ∨ (pattern.val[k]).val = 0 ∨ (pattern.val[k]).val = 1)
    (hc : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val + c ∧ (nums.val[i]).val + c ≤ 10 ^ 9)
    (hlen : nums'.val.length = nums.val.length)
    (hval : ∀ i (hi : i < nums.val.length), (nums'.val[i]).val = (nums.val[i]).val + c) :
    ∀ r r' : Std.I64, count_matching_subarrays nums pattern = ok r →
      count_matching_subarrays nums' pattern = ok r' → r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums nums' pattern : Slice Std.I64) (c : ℤ)
    (hna : 2 ≤ nums.val.length) (hnb : nums.val.length ≤ 100)
    (hma : 1 ≤ pattern.val.length) (hmb : pattern.val.length < nums.val.length)
    (hnum : ∀ i (hi : i < nums.val.length), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hpat : ∀ k (hk : k < pattern.val.length),
      (pattern.val[k]).val = -1 ∨ (pattern.val[k]).val = 0 ∨ (pattern.val[k]).val = 1)
    (hc : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val + c ∧ (nums.val[i]).val + c ≤ 10 ^ 9)
    (hlen : nums'.val.length = nums.val.length)
    (hval : ∀ i (hi : i < nums.val.length), (nums'.val[i]).val = (nums.val[i]).val + c), ∀ r r' : Std.I64, count_matching_subarrays nums pattern = ok r →
      count_matching_subarrays nums' pattern = ok r' → r = r') := by
  sorry

/-- For every such c, if the function returns r on (nums, pattern) and returns r' on (nums', pattern), where nums'[i] = c * nums[i] for every i with 0 <= i < n, then r = r'.
  Preconditions: Let n = len(nums) and m = len(pattern). The preconditions are 2 <= n <= 100, 1 <= m < n, for every i with 0 <= i < n, 1 <= nums[i] <= 10^9, and for every k with 0 <= k < m, pattern[k] is -1, 0, or 1. Let c be a positive integer such that for every i with 0 <= i < n, c * nums[i] is between 1 and 10^9 inclusive. -/
theorem spec_7 (nums nums' pattern : Slice Std.I64) (c : ℤ)
    (hna : 2 ≤ nums.val.length) (hnb : nums.val.length ≤ 100)
    (hma : 1 ≤ pattern.val.length) (hmb : pattern.val.length < nums.val.length)
    (hnum : ∀ i (hi : i < nums.val.length), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hpat : ∀ k (hk : k < pattern.val.length),
      (pattern.val[k]).val = -1 ∨ (pattern.val[k]).val = 0 ∨ (pattern.val[k]).val = 1)
    (hcpos : 0 < c)
    (hc : ∀ i (hi : i < nums.val.length),
      1 ≤ c * (nums.val[i]).val ∧ c * (nums.val[i]).val ≤ 10 ^ 9)
    (hlen : nums'.val.length = nums.val.length)
    (hval : ∀ i (hi : i < nums.val.length), (nums'.val[i]).val = c * (nums.val[i]).val) :
    ∀ r r' : Std.I64, count_matching_subarrays nums pattern = ok r →
      count_matching_subarrays nums' pattern = ok r' → r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums nums' pattern : Slice Std.I64) (c : ℤ)
    (hna : 2 ≤ nums.val.length) (hnb : nums.val.length ≤ 100)
    (hma : 1 ≤ pattern.val.length) (hmb : pattern.val.length < nums.val.length)
    (hnum : ∀ i (hi : i < nums.val.length), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hpat : ∀ k (hk : k < pattern.val.length),
      (pattern.val[k]).val = -1 ∨ (pattern.val[k]).val = 0 ∨ (pattern.val[k]).val = 1)
    (hcpos : 0 < c)
    (hc : ∀ i (hi : i < nums.val.length),
      1 ≤ c * (nums.val[i]).val ∧ c * (nums.val[i]).val ≤ 10 ^ 9)
    (hlen : nums'.val.length = nums.val.length)
    (hval : ∀ i (hi : i < nums.val.length), (nums'.val[i]).val = c * (nums.val[i]).val), ∀ r r' : Std.I64, count_matching_subarrays nums pattern = ok r →
      count_matching_subarrays nums' pattern = ok r' → r = r') := by
  sorry

/-- Define revnums[i] = nums[n-1-i] for 0 <= i < n, and revpattern[k] = -pattern[m-1-k] for 0 <= k < m. If the function returns r on (nums, pattern) and returns r' on (revnums, revpattern), then r = r'.
  Preconditions: Let n = len(nums) and m = len(pattern). The preconditions are 2 <= n <= 100, 1 <= m < n, for every i with 0 <= i < n, 1 <= nums[i] <= 10^9, and for every k with 0 <= k < m, pattern[k] is -1, 0, or 1. -/
theorem spec_8 (nums revnums pattern revpattern : Slice Std.I64)
    (hna : 2 ≤ nums.val.length) (hnb : nums.val.length ≤ 100)
    (hma : 1 ≤ pattern.val.length) (hmb : pattern.val.length < nums.val.length)
    (hnum : ∀ i (hi : i < nums.val.length), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hpat : ∀ k (hk : k < pattern.val.length),
      (pattern.val[k]).val = -1 ∨ (pattern.val[k]).val = 0 ∨ (pattern.val[k]).val = 1)
    (hrevn_len : revnums.val.length = nums.val.length)
    (hrevn : ∀ i (hi : i < nums.val.length),
      (revnums.val[i]).val = (nums.val[nums.val.length - 1 - i]).val)
    (hrevp_len : revpattern.val.length = pattern.val.length)
    (hrevp : ∀ k (hk : k < pattern.val.length),
      (revpattern.val[k]).val = -(pattern.val[pattern.val.length - 1 - k]).val) :
    ∀ r r' : Std.I64, count_matching_subarrays nums pattern = ok r →
      count_matching_subarrays revnums revpattern = ok r' → r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums revnums pattern revpattern : Slice Std.I64)
    (hna : 2 ≤ nums.val.length) (hnb : nums.val.length ≤ 100)
    (hma : 1 ≤ pattern.val.length) (hmb : pattern.val.length < nums.val.length)
    (hnum : ∀ i (hi : i < nums.val.length), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hpat : ∀ k (hk : k < pattern.val.length),
      (pattern.val[k]).val = -1 ∨ (pattern.val[k]).val = 0 ∨ (pattern.val[k]).val = 1)
    (hrevn_len : revnums.val.length = nums.val.length)
    (hrevn : ∀ i (hi : i < nums.val.length),
      (revnums.val[i]).val = (nums.val[nums.val.length - 1 - i]).val)
    (hrevp_len : revpattern.val.length = pattern.val.length)
    (hrevp : ∀ k (hk : k < pattern.val.length),
      (revpattern.val[k]).val = -(pattern.val[pattern.val.length - 1 - k]).val), ∀ r r' : Std.I64, count_matching_subarrays nums pattern = ok r →
      count_matching_subarrays revnums revpattern = ok r' → r = r') := by
  sorry

end AegisSpec.CountMatchingSubarrays
