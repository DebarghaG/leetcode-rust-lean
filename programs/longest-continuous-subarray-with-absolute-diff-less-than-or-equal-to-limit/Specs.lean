import Aegis.LongestSubarray.Code.Funs

/-!
# Specifications of `Aegis.LongestSubarray.longest_subarray`

LeetCode problem `longest-continuous-subarray-with-absolute-diff-less-than-or-equal-to-limit`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestSubarray

  def valAt (nums : Slice Std.I64) (i : ℕ) : ℤ := (nums.val.getD i default).val

  def ValidWindow (nums : Slice Std.I64) (limit : ℤ) (i j : ℕ) : Prop :=
    ∀ p q : ℕ, i ≤ p → p ≤ j → i ≤ q → q ≤ j → |valAt nums p - valAt nums q| ≤ limit

  def ConstWindow (nums : Slice Std.I64) (i j : ℕ) : Prop :=
    ∀ k : ℕ, i ≤ k → k ≤ j → valAt nums k = valAt nums i

  def winLen (i j : ℕ) : ℤ := ((j - i + 1 : ℕ) : ℤ)

  def Nondecreasing (nums : Slice Std.I64) : Prop :=
    ∀ i : ℕ, i + 1 < nums.val.length → valAt nums i ≤ valAt nums (i + 1)

  /-- Let a subarray nums[i..j] (with 0 <= i <= j < len(nums)) be called valid for limit when |nums[p]-nums[q]| <= limit for every p,q with i <= p <= j and i <= q <= j. The function returns a result r, and r is the largest integer L such that L = j-i+1 for some valid subarray nums[i..j].
    Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000. -/
  theorem spec_1
      (nums : Slice Std.I64) (limit : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
      (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.LongestSubarray.longest_subarray nums limit = ok r ∧
          (∃ i j : ℕ,
            i ≤ j ∧ j < nums.val.length ∧
              ValidWindow nums limit.val i j ∧ r.val = winLen i j) ∧
          (∀ i j : ℕ,
            i ≤ j → j < nums.val.length → ValidWindow nums limit.val i j →
              winLen i j ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
        (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000), ∃ r : Std.I64,
          Aegis.LongestSubarray.longest_subarray nums limit = ok r ∧
            (∃ i j : ℕ,
              i ≤ j ∧ j < nums.val.length ∧
                ValidWindow nums limit.val i j ∧ r.val = winLen i j) ∧
            (∀ i j : ℕ,
              i ≤ j → j < nums.val.length → ValidWindow nums limit.val i j →
                winLen i j ≤ r.val)) := by
    sorry

  /-- The function returns a result r; it does not panic, overflow, go out of bounds, or otherwise fail.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000. -/
  theorem spec_2
      (nums : Slice Std.I64) (limit : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
      (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000) :
      ∃ r : Std.I64, Aegis.LongestSubarray.longest_subarray nums limit = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
        (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000), ∃ r : Std.I64, Aegis.LongestSubarray.longest_subarray nums limit = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 1.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000. -/
  theorem spec_3
      (nums : Slice Std.I64) (limit : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
      (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000) :
      ∀ r : Std.I64, Aegis.LongestSubarray.longest_subarray nums limit = ok r → 1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
        (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000), ∀ r : Std.I64, Aegis.LongestSubarray.longest_subarray nums limit = ok r → 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= len(nums).
    Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000. -/
  theorem spec_4
      (nums : Slice Std.I64) (limit : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
      (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.LongestSubarray.longest_subarray nums limit = ok r →
          r.val ≤ (nums.val.length : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
        (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.LongestSubarray.longest_subarray nums limit = ok r →
            r.val ≤ (nums.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices i,j with 0 <= i <= j < len(nums) such that j-i+1 = r and |nums[p]-nums[q]| <= limit for every p,q with i <= p <= j and i <= q <= j.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000. -/
  theorem spec_5
      (nums : Slice Std.I64) (limit : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
      (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.LongestSubarray.longest_subarray nums limit = ok r →
          ∃ i j : ℕ,
            i ≤ j ∧ j < nums.val.length ∧
              ValidWindow nums limit.val i j ∧ winLen i j = r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
        (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.LongestSubarray.longest_subarray nums limit = ok r →
            ∃ i j : ℕ,
              i ≤ j ∧ j < nums.val.length ∧
                ValidWindow nums limit.val i j ∧ winLen i j = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every i,j with 0 <= i <= j < len(nums), if |nums[p]-nums[q]| <= limit for every p,q with i <= p <= j and i <= q <= j, then j-i+1 <= r.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000. -/
  theorem spec_6
      (nums : Slice Std.I64) (limit : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
      (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.LongestSubarray.longest_subarray nums limit = ok r →
          ∀ i j : ℕ,
            i ≤ j → j < nums.val.length → ValidWindow nums limit.val i j →
              winLen i j ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
        (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.LongestSubarray.longest_subarray nums limit = ok r →
            ∀ i j : ℕ,
              i ≤ j → j < nums.val.length → ValidWindow nums limit.val i j →
                winLen i j ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 1.
    Preconditions: len(nums) = 1; 1 <= nums[0] <= 1000000000; 0 <= limit <= 1000000000. -/
  theorem spec_7
      (nums : Slice Std.I64) (limit : Std.I64)
      (hlen : nums.val.length = 1)
      (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
      (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000) :
      ∀ r : Std.I64, Aegis.LongestSubarray.longest_subarray nums limit = ok r → r.val = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
        (hlen : nums.val.length = 1)
        (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
        (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000), ∀ r : Std.I64, Aegis.LongestSubarray.longest_subarray nums limit = ok r → r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, r is the largest integer L such that there exist indices i,j with 0 <= i <= j < len(nums), j-i+1 = L, and nums[k] = nums[i] for every k with i <= k <= j.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; limit = 0. -/
  theorem spec_8
      (nums : Slice Std.I64) (limit : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
      (hlimit : limit.val = 0) :
      ∀ r : Std.I64,
        Aegis.LongestSubarray.longest_subarray nums limit = ok r →
          (∃ i j : ℕ,
            i ≤ j ∧ j < nums.val.length ∧ ConstWindow nums i j ∧ r.val = winLen i j) ∧
          (∀ i j : ℕ,
            i ≤ j → j < nums.val.length → ConstWindow nums i j → winLen i j ≤ r.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
        (hlimit : limit.val = 0), ∀ r : Std.I64,
          Aegis.LongestSubarray.longest_subarray nums limit = ok r →
            (∃ i j : ℕ,
              i ≤ j ∧ j < nums.val.length ∧ ConstWindow nums i j ∧ r.val = winLen i j) ∧
            (∀ i j : ℕ,
              i ≤ j → j < nums.val.length → ConstWindow nums i j → winLen i j ≤ r.val)) := by
    sorry

  /-- Whenever the function returns a result r, r = len(nums).
    Preconditions: len(nums) >= 2 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000; for every i,j with 0 <= i < len(nums) and 0 <= j < len(nums), |nums[i]-nums[j]| <= limit. -/
  theorem spec_9
      (nums : Slice Std.I64) (limit : Std.I64)
      (hlen1 : 2 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
      (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000)
      (hall : ∀ i j : ℕ, i < nums.val.length → j < nums.val.length →
        |valAt nums i - valAt nums j| ≤ limit.val) :
      ∀ r : Std.I64,
        Aegis.LongestSubarray.longest_subarray nums limit = ok r → r.val = (nums.val.length : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
        (hlen1 : 2 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
        (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000)
        (hall : ∀ i j : ℕ, i < nums.val.length → j < nums.val.length →
          |valAt nums i - valAt nums j| ≤ limit.val), ∀ r : Std.I64,
          Aegis.LongestSubarray.longest_subarray nums limit = ok r → r.val = (nums.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r1 on input (nums, limit1) and a result r2 on input (nums, limit2), r1 <= r2.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit1 <= limit2 <= 1000000000. -/
  theorem spec_10
      (nums : Slice Std.I64) (limit1 : Std.I64) (limit2 : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
      (hlimit1 : 0 ≤ limit1.val) (hlimit2 : limit1.val ≤ limit2.val)
      (hlimit3 : limit2.val ≤ 1000000000) :
      ∀ r1 r2 : Std.I64,
        Aegis.LongestSubarray.longest_subarray nums limit1 = ok r1 →
          Aegis.LongestSubarray.longest_subarray nums limit2 = ok r2 → r1.val ≤ r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit1 : Std.I64) (limit2 : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
        (hlimit1 : 0 ≤ limit1.val) (hlimit2 : limit1.val ≤ limit2.val)
        (hlimit3 : limit2.val ≤ 1000000000), ∀ r1 r2 : Std.I64,
          Aegis.LongestSubarray.longest_subarray nums limit1 = ok r1 →
            Aegis.LongestSubarray.longest_subarray nums limit2 = ok r2 → r1.val ≤ r2.val) := by
    sorry

  /-- Let rev be the slice of length len(nums) with rev[k] = nums[len(nums)-1-k] for every 0 <= k < len(nums). Whenever the function returns a result r on input (nums, limit) and a result r_rev on input (rev, limit), r = r_rev.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000. -/
  theorem spec_11
      (nums rev : Slice Std.I64) (limit : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
      (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000)
      (hrev_len : rev.val.length = nums.val.length)
      (hrev : ∀ (k : ℕ), k < nums.val.length → valAt rev k = valAt nums (nums.val.length - 1 - k)) :
      ∀ r r_rev : Std.I64,
        Aegis.LongestSubarray.longest_subarray nums limit = ok r →
          Aegis.LongestSubarray.longest_subarray rev limit = ok r_rev → r.val = r_rev.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums rev : Slice Std.I64) (limit : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
        (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000)
        (hrev_len : rev.val.length = nums.val.length)
        (hrev : ∀ (k : ℕ), k < nums.val.length → valAt rev k = valAt nums (nums.val.length - 1 - k)), ∀ r r_rev : Std.I64,
          Aegis.LongestSubarray.longest_subarray nums limit = ok r →
            Aegis.LongestSubarray.longest_subarray rev limit = ok r_rev → r.val = r_rev.val) := by
    sorry

  /-- Whenever the function returns a result r on input (nums, limit) and a result r2 on input (nums2, limit), r = r2.
    Preconditions: nums and nums2 are slices with len(nums) = len(nums2) >= 1 and len(nums) <= 100000; every element of nums and of nums2 lies in [1,1000000000]; 0 <= limit <= 1000000000; there exists an integer c such that nums2[i] = nums[i] + c for every i with 0 <= i < len(nums). -/
  theorem spec_12
      (nums nums2 : Slice Std.I64) (limit : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hlen_eq : nums2.val.length = nums.val.length)
      (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
      (helems2 : ∀ (i : ℕ), i < nums2.val.length → 1 ≤ valAt nums2 i ∧ valAt nums2 i ≤ 1000000000)
      (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000)
      (hshift : ∃ c : ℤ, ∀ (i : ℕ), i < nums.val.length → valAt nums2 i = valAt nums i + c) :
      ∀ r r2 : Std.I64,
        Aegis.LongestSubarray.longest_subarray nums limit = ok r →
          Aegis.LongestSubarray.longest_subarray nums2 limit = ok r2 → r.val = r2.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (limit : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hlen_eq : nums2.val.length = nums.val.length)
        (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
        (helems2 : ∀ (i : ℕ), i < nums2.val.length → 1 ≤ valAt nums2 i ∧ valAt nums2 i ≤ 1000000000)
        (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000)
        (hshift : ∃ c : ℤ, ∀ (i : ℕ), i < nums.val.length → valAt nums2 i = valAt nums i + c), ∀ r r2 : Std.I64,
          Aegis.LongestSubarray.longest_subarray nums limit = ok r →
            Aegis.LongestSubarray.longest_subarray nums2 limit = ok r2 → r.val = r2.val) := by
    sorry

  /-- Whenever the function returns a result r, r is the largest integer L such that L >= 1, there exists an index i with 0 <= i and i+L-1 < len(nums), and nums[i+L-1] - nums[i] <= limit.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= limit <= 1000000000; nums is nondecreasing, i.e. for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
  theorem spec_13
      (nums : Slice Std.I64) (limit : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
      (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000)
      (hmono : Nondecreasing nums) :
      ∀ r : Std.I64,
        Aegis.LongestSubarray.longest_subarray nums limit = ok r →
          (∃ i L : ℕ,
            1 ≤ L ∧ i + L - 1 < nums.val.length ∧
              valAt nums (i + L - 1) - valAt nums i ≤ limit.val ∧ r.val = (L : ℤ)) ∧
          (∀ i L : ℕ,
            1 ≤ L → i + L - 1 < nums.val.length →
              valAt nums (i + L - 1) - valAt nums i ≤ limit.val → (L : ℤ) ≤ r.val) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
        (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000)
        (hmono : Nondecreasing nums), ∀ r : Std.I64,
          Aegis.LongestSubarray.longest_subarray nums limit = ok r →
            (∃ i L : ℕ,
              1 ≤ L ∧ i + L - 1 < nums.val.length ∧
                valAt nums (i + L - 1) - valAt nums i ≤ limit.val ∧ r.val = (L : ℤ)) ∧
            (∀ i L : ℕ,
              1 ≤ L → i + L - 1 < nums.val.length →
                valAt nums (i + L - 1) - valAt nums i ≤ limit.val → (L : ℤ) ≤ r.val)) := by
    sorry

  /-- Whenever the function returns a result r, if |nums[0]-nums[1]| <= limit then r = 2, and otherwise r = 1.
    Preconditions: len(nums) = 2; 1 <= nums[0] <= 1000000000; 1 <= nums[1] <= 1000000000; 0 <= limit <= 1000000000. -/
  theorem spec_14
      (nums : Slice Std.I64) (limit : Std.I64)
      (hlen : nums.val.length = 2)
      (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
      (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.LongestSubarray.longest_subarray nums limit = ok r →
          (|valAt nums 0 - valAt nums 1| ≤ limit.val → r.val = 2) ∧
            (¬ (|valAt nums 0 - valAt nums 1| ≤ limit.val) → r.val = 1) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit : Std.I64)
        (hlen : nums.val.length = 2)
        (helems : ∀ (i : ℕ), i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000000000)
        (hlimit1 : 0 ≤ limit.val) (hlimit2 : limit.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.LongestSubarray.longest_subarray nums limit = ok r →
            (|valAt nums 0 - valAt nums 1| ≤ limit.val → r.val = 2) ∧
              (¬ (|valAt nums 0 - valAt nums 1| ≤ limit.val) → r.val = 1)) := by
    sorry

  end AegisSpec.LongestSubarray
