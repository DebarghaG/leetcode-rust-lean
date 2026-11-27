import Aegis.MinimumDifference.Code.Funs

/-!
# Specifications of `Aegis.MinimumDifference.minimum_difference`

LeetCode problem `partition-array-into-two-arrays-to-minimize-sum-difference`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumDifference

def valAt (nums : Slice Std.I64) (i : ℕ) : ℤ :=
  match nums.val[i]? with
  | some x => x.val
  | none => 0

def subsetSum (nums : Slice Std.I64) (S : Finset ℕ) : ℤ :=
  ∑ i ∈ S, valAt nums i

def totalSum (nums : Slice Std.I64) : ℤ :=
  ∑ i ∈ Finset.range nums.val.length, valAt nums i

def subsetDiff (nums : Slice Std.I64) (S : Finset ℕ) : ℤ :=
  |subsetSum nums S - ∑ i ∈ Finset.range nums.val.length \ S, valAt nums i|

def subsetsOfCard (nums : Slice Std.I64) (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.range nums.val.length).powerset.filter (fun S => S.card = n)

def diffSet (nums : Slice Std.I64) (n : ℕ) : Finset ℤ :=
  (subsetsOfCard nums n).image (subsetDiff nums)

def IsMinOf (x : ℤ) (s : Finset ℤ) : Prop :=
  x ∈ s ∧ ∀ y ∈ s, x ≤ y

def totalAbsSum (nums : Slice Std.I64) : ℤ :=
  ∑ i ∈ Finset.range nums.val.length, |valAt nums i|

theorem valAt_of_lt (nums : Slice Std.I64) (i : ℕ) (h : i < nums.val.length) :
    valAt nums i = (nums.val[i]).val := by
  simp only [valAt, List.getElem?_eq_getElem h]

theorem valAt_of_le (nums : Slice Std.I64) (i : ℕ) (h : nums.val.length ≤ i) :
    valAt nums i = 0 := by
  simp [valAt, List.getElem?_eq_none_iff.mpr h]

theorem totalSum_eq_subsetSum_range (nums : Slice Std.I64) :
    totalSum nums = subsetSum nums (Finset.range nums.val.length) := by
  simp [totalSum, subsetSum]

theorem diffSet_nonempty (nums : Slice Std.I64)
    (hm_even : nums.val.length % 2 = 0) (hn_pos : 1 ≤ nums.val.length / 2) :
    (diffSet nums (nums.val.length / 2)).Nonempty := by
  have hsub : Finset.range (nums.val.length / 2) ⊆ Finset.range nums.val.length := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hmem : Finset.range (nums.val.length / 2) ∈ subsetsOfCard nums (nums.val.length / 2) := by
    simp only [subsetsOfCard, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hsub, Finset.card_range _⟩
  exact ⟨_, Finset.mem_image.mpr ⟨_, hmem, rfl⟩⟩

/-- Whenever the function returns a result r, r is the minimum of the set { | (sum_{i in S} nums[i]) - (sum_{i notin S} nums[i]) | : S is a subset of {0,...,m-1} and |S| = n }, where m = len(nums) and n = m/2.
  Preconditions: Let m = len(nums) and n = m/2. The precondition is: m is even, 1 <= n <= 15, and for every i with 0 <= i < m, -10000000 <= nums[i] <= 10000000. -/
theorem spec_1 (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r) :
    IsMinOf r.val (diffSet nums (nums.val.length / 2)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r), IsMinOf r.val (diffSet nums (nums.val.length / 2))) := by
  sorry

/-- The function returns a result r; it does not fail (no overflow, out-of-bounds access, or panic).
  Preconditions: Let m = len(nums) and n = m/2. The precondition is: m is even, 1 <= n <= 15, and for every i with 0 <= i < m, -10000000 <= nums[i] <= 10000000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000) :
    ∃ r : Std.I64, Aegis.MinimumDifference.minimum_difference nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000), ∃ r : Std.I64, Aegis.MinimumDifference.minimum_difference nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: Let m = len(nums) and n = m/2. The precondition is: m is even, 1 <= n <= 15, and for every i with 0 <= i < m, -10000000 <= nums[i] <= 10000000. -/
theorem spec_3 (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= sum_{i=0}^{m-1} |nums[i]|, where m = len(nums).
  Preconditions: Let m = len(nums) and n = m/2. The precondition is: m is even, 1 <= n <= 15, and for every i with 0 <= i < m, -10000000 <= nums[i] <= 10000000. -/
theorem spec_4 (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r) :
    r.val ≤ totalAbsSum nums := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r), r.val ≤ totalAbsSum nums) := by
  sorry

/-- Whenever the function returns a result r, the integer T - r is even, where T = sum_{i=0}^{m-1} nums[i] and m = len(nums).
  Preconditions: Let m = len(nums) and n = m/2. The precondition is: m is even, 1 <= n <= 15, and for every i with 0 <= i < m, -10000000 <= nums[i] <= 10000000. -/
theorem spec_5 (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r) :
    2 ∣ (totalSum nums - r.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r), 2 ∣ (totalSum nums - r.val)) := by
  sorry

/-- Whenever the function returns a result r, there exists a subset S of {0,...,m-1} with |S| = n such that r = | (sum_{i in S} nums[i]) - (sum_{i notin S} nums[i]) |, where m = len(nums) and n = m/2.
  Preconditions: Let m = len(nums) and n = m/2. The precondition is: m is even, 1 <= n <= 15, and for every i with 0 <= i < m, -10000000 <= nums[i] <= 10000000. -/
theorem spec_6 (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r) :
    ∃ S : Finset ℕ, S ⊆ Finset.range nums.val.length ∧ S.card = nums.val.length / 2 ∧
      r.val = subsetDiff nums S := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r), ∃ S : Finset ℕ, S ⊆ Finset.range nums.val.length ∧ S.card = nums.val.length / 2 ∧
      r.val = subsetDiff nums S) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there exists a subset S of {0,...,m-1} with |S| = n and 2 * (sum_{i in S} nums[i]) = T, where m = len(nums), n = m/2, and T = sum_{i=0}^{m-1} nums[i].
  Preconditions: Let m = len(nums) and n = m/2. The precondition is: m is even, 1 <= n <= 15, and for every i with 0 <= i < m, -10000000 <= nums[i] <= 10000000. -/
theorem spec_7 (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r) :
    (r.val = 0 ↔ ∃ S : Finset ℕ, S ⊆ Finset.range nums.val.length ∧
      S.card = nums.val.length / 2 ∧ 2 * subsetSum nums S = totalSum nums) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r), (r.val = 0 ↔ ∃ S : Finset ℕ, S ⊆ Finset.range nums.val.length ∧
      S.card = nums.val.length / 2 ∧ 2 * subsetSum nums S = totalSum nums)) := by
  sorry

/-- Whenever the function returns a result r, r = |nums[0] - nums[1]|.
  Preconditions: Let m = len(nums) and n = m/2. The precondition is: m is even, 1 <= n <= 15, and for every i with 0 <= i < m, -10000000 <= nums[i] <= 10000000. In addition, len(nums) = 2 (so n = 1). -/
theorem spec_8 (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hlen : nums.val.length = 2)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r) :
    r.val = |valAt nums 0 - valAt nums 1| := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hlen : nums.val.length = 2)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r), r.val = |valAt nums 0 - valAt nums 1|) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: Let m = len(nums) and n = m/2. The precondition is: m is even, 1 <= n <= 15, and for every i with 0 <= i < m, -10000000 <= nums[i] <= 10000000. In addition, for every i and j with 0 <= i < m and 0 <= j < m, nums[i] = nums[j]. -/
theorem spec_9 (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hconst : ∀ i, i < nums.val.length → ∀ j, j < nums.val.length →
      valAt nums i = valAt nums j)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r) :
    r.val = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hconst : ∀ i, i < nums.val.length → ∀ j, j < nums.val.length →
      valAt nums i = valAt nums j)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: Let m = len(nums) and n = m/2. The precondition is: m is even, 1 <= n <= 15, and for every i with 0 <= i < m, -10000000 <= nums[i] <= 10000000. In addition, T = sum_{i=0}^{m-1} nums[i] is odd. -/
theorem spec_10 (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hT_odd : ¬ 2 ∣ totalSum nums)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r) :
    1 ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hT_odd : ¬ 2 ∣ totalSum nums)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r), 1 ≤ r.val) := by
  sorry

/-- Whenever minimum_difference(nums) returns r and minimum_difference(nums2) returns r2, we have r2 = r.
  Preconditions: Let m = len(nums) and n = m/2. The precondition is: m is even, 1 <= n <= 15, and for every i with 0 <= i < m, -10000000 <= nums[i] <= 10000000. Let nums2 be any Slice Std.I64 with len(nums2) = m and nums2[i] = -nums[i] for every i with 0 <= i < m; these values also satisfy the same bounds. -/
theorem spec_11 (nums nums2 : Slice Std.I64) (r r2 : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (h2_len : nums2.val.length = nums.val.length)
    (h2_val : ∀ i, i < nums.val.length → valAt nums2 i = - valAt nums i)
    (h2_bounds : ∀ i, i < nums2.val.length →
      -10000000 ≤ valAt nums2 i ∧ valAt nums2 i ≤ 10000000)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r)
    (hr2 : Aegis.MinimumDifference.minimum_difference nums2 = ok r2) :
    r2.val = r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (r r2 : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (h2_len : nums2.val.length = nums.val.length)
    (h2_val : ∀ i, i < nums.val.length → valAt nums2 i = - valAt nums i)
    (h2_bounds : ∀ i, i < nums2.val.length →
      -10000000 ≤ valAt nums2 i ∧ valAt nums2 i ≤ 10000000)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r)
    (hr2 : Aegis.MinimumDifference.minimum_difference nums2 = ok r2), r2.val = r.val) := by
  sorry

/-- Whenever minimum_difference(nums) returns r and minimum_difference(nums2) returns r2, we have r2 = k * r.
  Preconditions: Let m = len(nums) and n = m/2. The precondition is: m is even, 1 <= n <= 15, and for every i with 0 <= i < m, -10000000 <= nums[i] <= 10000000. Let k be an integer with k >= 0 and nums2 any Slice Std.I64 with len(nums2) = m, nums2[i] = k * nums[i] for every i with 0 <= i < m, and -10000000 <= nums2[i] <= 10000000 for all i. -/
theorem spec_12 (nums nums2 : Slice Std.I64) (k : ℤ) (r r2 : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hk : 0 ≤ k)
    (h2_len : nums2.val.length = nums.val.length)
    (h2_val : ∀ i, i < nums.val.length → valAt nums2 i = k * valAt nums i)
    (h2_bounds : ∀ i, i < nums2.val.length →
      -10000000 ≤ valAt nums2 i ∧ valAt nums2 i ≤ 10000000)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r)
    (hr2 : Aegis.MinimumDifference.minimum_difference nums2 = ok r2) :
    r2.val = k * r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (k : ℤ) (r r2 : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hk : 0 ≤ k)
    (h2_len : nums2.val.length = nums.val.length)
    (h2_val : ∀ i, i < nums.val.length → valAt nums2 i = k * valAt nums i)
    (h2_bounds : ∀ i, i < nums2.val.length →
      -10000000 ≤ valAt nums2 i ∧ valAt nums2 i ≤ 10000000)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r)
    (hr2 : Aegis.MinimumDifference.minimum_difference nums2 = ok r2), r2.val = k * r.val) := by
  sorry

/-- Whenever the function returns a result r, for every subset S of {0,...,m-1} with |S| = n, r <= | (sum_{i in S} nums[i]) - (sum_{i notin S} nums[i]) |, where m = len(nums) and n = m/2.
  Preconditions: Let m = len(nums) and n = m/2. The precondition is: m is even, 1 <= n <= 15, and for every i with 0 <= i < m, -10000000 <= nums[i] <= 10000000. -/
theorem spec_13 (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r) :
    ∀ S : Finset ℕ, S ⊆ Finset.range nums.val.length → S.card = nums.val.length / 2 →
      r.val ≤ |subsetDiff nums S| := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hm_even : nums.val.length % 2 = 0)
    (hn_pos : 1 ≤ nums.val.length / 2)
    (hn_le : nums.val.length / 2 ≤ 15)
    (hbounds : ∀ i, i < nums.val.length →
      -10000000 ≤ valAt nums i ∧ valAt nums i ≤ 10000000)
    (hr : Aegis.MinimumDifference.minimum_difference nums = ok r), ∀ S : Finset ℕ, S ⊆ Finset.range nums.val.length → S.card = nums.val.length / 2 →
      r.val ≤ |subsetDiff nums S|) := by
  sorry

end AegisSpec.MinimumDifference
