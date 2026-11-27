import Aegis.MinimumSumSubarray.Code.Funs

/-!
# Specifications of `Aegis.MinimumSumSubarray.minimum_sum_subarray`

LeetCode problem `minimum-positive-sum-subarray`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumSumSubarray

  def windowSum (nums : Slice Std.I64) (a k : ℕ) : ℤ :=
    (((nums.val.drop a).take k).map (fun x => x.val)).sum

  def revSlice (nums : Slice Std.I64) : Slice Std.I64 :=
    Slice.mk nums.val.reverse.length (Data.ListN.ListN.fromList nums.val.reverse) (by
      rw [List.length_reverse]
      simp only [Aeneas.Std.Slice.val]
      rw [Data.ListN.ListN_length]
      exact nums.bound)

  /-- For integers a,k with k >= 1, let sum(a,k) denote nums[a] + nums[a+1] + ... + nums[a+k-1]. The function returns a result ans and: (A) if there exist integers a,k such that 0 <= a, l <= k <= r, a+k <= len(nums), and sum(a,k) > 0, then ans > 0, there exist such a,k with sum(a,k) = ans, and for every such a,k with sum(a,k) > 0 we have ans <= sum(a,k); (B) if no such a,k with sum(a,k) > 0 exists, then ans = -1.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, 1 <= l <= r <= n, and for every i with 0 <= i < n, -1000 <= nums[i] <= 1000. -/
  theorem spec_1 (nums : Slice Std.I64) (l r : Std.I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
      (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ (nums.val.length : ℤ))
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∃ ans : Std.I64,
        Aegis.MinimumSumSubarray.minimum_sum_subarray nums l r = ok ans ∧
        ((∃ (a k : ℕ), l.val ≤ (k : ℤ) ∧ (k : ℤ) ≤ r.val ∧
            a + k ≤ nums.val.length ∧ 0 < windowSum nums a k) →
          (0 < ans.val ∧
            (∃ (a k : ℕ), l.val ≤ (k : ℤ) ∧ (k : ℤ) ≤ r.val ∧
              a + k ≤ nums.val.length ∧ windowSum nums a k = ans.val) ∧
            (∀ (a k : ℕ), l.val ≤ (k : ℤ) → (k : ℤ) ≤ r.val →
              a + k ≤ nums.val.length → 0 < windowSum nums a k →
              ans.val ≤ windowSum nums a k))) ∧
        ((¬ ∃ (a k : ℕ), l.val ≤ (k : ℤ) ∧ (k : ℤ) ≤ r.val ∧
            a + k ≤ nums.val.length ∧ 0 < windowSum nums a k) →
          ans.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (l r : Std.I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
        (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ (nums.val.length : ℤ))
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∃ ans : Std.I64,
          Aegis.MinimumSumSubarray.minimum_sum_subarray nums l r = ok ans ∧
          ((∃ (a k : ℕ), l.val ≤ (k : ℤ) ∧ (k : ℤ) ≤ r.val ∧
              a + k ≤ nums.val.length ∧ 0 < windowSum nums a k) →
            (0 < ans.val ∧
              (∃ (a k : ℕ), l.val ≤ (k : ℤ) ∧ (k : ℤ) ≤ r.val ∧
                a + k ≤ nums.val.length ∧ windowSum nums a k = ans.val) ∧
              (∀ (a k : ℕ), l.val ≤ (k : ℤ) → (k : ℤ) ≤ r.val →
                a + k ≤ nums.val.length → 0 < windowSum nums a k →
                ans.val ≤ windowSum nums a k))) ∧
          ((¬ ∃ (a k : ℕ), l.val ≤ (k : ℤ) ∧ (k : ℤ) ≤ r.val ∧
              a + k ≤ nums.val.length ∧ 0 < windowSum nums a k) →
            ans.val = -1)) := by
    sorry

  /-- The function returns a result ans; it does not fail on any input satisfying the preconditions.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, 1 <= l <= r <= n, and for every i with 0 <= i < n, -1000 <= nums[i] <= 1000. -/
  theorem spec_2 (nums : Slice Std.I64) (l r : Std.I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
      (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ (nums.val.length : ℤ))
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∃ ans : Std.I64, Aegis.MinimumSumSubarray.minimum_sum_subarray nums l r = ok ans := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (l r : Std.I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
        (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ (nums.val.length : ℤ))
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∃ ans : Std.I64, Aegis.MinimumSumSubarray.minimum_sum_subarray nums l r = ok ans) := by
    sorry

  /-- Whenever the function returns a result ans, either ans = -1 or 1 <= ans <= 1000 * r.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, 1 <= l <= r <= n, and for every i with 0 <= i < n, -1000 <= nums[i] <= 1000. -/
  theorem spec_3 (nums : Slice Std.I64) (l r : Std.I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
      (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ (nums.val.length : ℤ))
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∀ ans : Std.I64,
        Aegis.MinimumSumSubarray.minimum_sum_subarray nums l r = ok ans →
          ans.val = -1 ∨ (1 ≤ ans.val ∧ ans.val ≤ 1000 * r.val) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (l r : Std.I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
        (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ (nums.val.length : ℤ))
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∀ ans : Std.I64,
          Aegis.MinimumSumSubarray.minimum_sum_subarray nums l r = ok ans →
            ans.val = -1 ∨ (1 ≤ ans.val ∧ ans.val ≤ 1000 * r.val)) := by
    sorry

  /-- For integers a,k with k >= 1, let sum(a,k) denote nums[a] + nums[a+1] + ... + nums[a+k-1]. Whenever the function returns a result ans, ans = -1 if and only if for every integer a,k with 0 <= a, l <= k <= r, and a+k <= len(nums), we have sum(a,k) <= 0.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, 1 <= l <= r <= n, and for every i with 0 <= i < n, -1000 <= nums[i] <= 1000. -/
  theorem spec_4 (nums : Slice Std.I64) (l r : Std.I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
      (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ (nums.val.length : ℤ))
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∀ ans : Std.I64,
        Aegis.MinimumSumSubarray.minimum_sum_subarray nums l r = ok ans →
          (ans.val = -1 ↔
            ∀ (a k : ℕ), l.val ≤ (k : ℤ) → (k : ℤ) ≤ r.val →
              a + k ≤ nums.val.length → windowSum nums a k ≤ 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (l r : Std.I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
        (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ (nums.val.length : ℤ))
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∀ ans : Std.I64,
          Aegis.MinimumSumSubarray.minimum_sum_subarray nums l r = ok ans →
            (ans.val = -1 ↔
              ∀ (a k : ℕ), l.val ≤ (k : ℤ) → (k : ℤ) ≤ r.val →
                a + k ≤ nums.val.length → windowSum nums a k ≤ 0)) := by
    sorry

  /-- For integers a,k with k >= 1, let sum(a,k) denote nums[a] + nums[a+1] + ... + nums[a+k-1]. Whenever the function returns a result ans with ans > 0, there exist integers a,k such that 0 <= a, l <= k <= r, a+k <= len(nums), and sum(a,k) = ans.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, 1 <= l <= r <= n, and for every i with 0 <= i < n, -1000 <= nums[i] <= 1000. -/
  theorem spec_5 (nums : Slice Std.I64) (l r : Std.I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
      (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ (nums.val.length : ℤ))
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∀ ans : Std.I64,
        Aegis.MinimumSumSubarray.minimum_sum_subarray nums l r = ok ans →
          0 < ans.val →
            ∃ (a k : ℕ), l.val ≤ (k : ℤ) ∧ (k : ℤ) ≤ r.val ∧
              a + k ≤ nums.val.length ∧ windowSum nums a k = ans.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (l r : Std.I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
        (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ (nums.val.length : ℤ))
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∀ ans : Std.I64,
          Aegis.MinimumSumSubarray.minimum_sum_subarray nums l r = ok ans →
            0 < ans.val →
              ∃ (a k : ℕ), l.val ≤ (k : ℤ) ∧ (k : ℤ) ≤ r.val ∧
                a + k ≤ nums.val.length ∧ windowSum nums a k = ans.val) := by
    sorry

  /-- For integers a,k with k >= 1, let sum(a,k) denote nums[a] + nums[a+1] + ... + nums[a+k-1]. Whenever the function returns a result ans with ans > 0, for every integer a,k with 0 <= a, l <= k <= r, a+k <= len(nums), if sum(a,k) > 0 then ans <= sum(a,k).
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, 1 <= l <= r <= n, and for every i with 0 <= i < n, -1000 <= nums[i] <= 1000. -/
  theorem spec_6 (nums : Slice Std.I64) (l r : Std.I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
      (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ (nums.val.length : ℤ))
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∀ ans : Std.I64,
        Aegis.MinimumSumSubarray.minimum_sum_subarray nums l r = ok ans →
          0 < ans.val →
            ∀ (a k : ℕ), l.val ≤ (k : ℤ) → (k : ℤ) ≤ r.val →
              a + k ≤ nums.val.length → 0 < windowSum nums a k →
              ans.val ≤ windowSum nums a k := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (l r : Std.I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
        (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ (nums.val.length : ℤ))
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∀ ans : Std.I64,
          Aegis.MinimumSumSubarray.minimum_sum_subarray nums l r = ok ans →
            0 < ans.val →
              ∀ (a k : ℕ), l.val ≤ (k : ℤ) → (k : ℤ) ≤ r.val →
                a + k ≤ nums.val.length → 0 < windowSum nums a k →
                ans.val ≤ windowSum nums a k) := by
    sorry

  /-- For integers a,k with k >= 1, let sum(a,k) denote nums[a] + nums[a+1] + ... + nums[a+k-1]. Whenever the function returns a result ans, if there exist integers a,k such that 0 <= a, l <= k <= r, a+k <= len(nums), and sum(a,k) = 1, then ans = 1.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, 1 <= l <= r <= n, and for every i with 0 <= i < n, -1000 <= nums[i] <= 1000. -/
  theorem spec_7 (nums : Slice Std.I64) (l r : Std.I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
      (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ (nums.val.length : ℤ))
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∀ ans : Std.I64,
        Aegis.MinimumSumSubarray.minimum_sum_subarray nums l r = ok ans →
          (∃ (a k : ℕ), l.val ≤ (k : ℤ) ∧ (k : ℤ) ≤ r.val ∧
            a + k ≤ nums.val.length ∧ windowSum nums a k = 1) →
          ans.val = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (l r : Std.I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
        (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ (nums.val.length : ℤ))
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∀ ans : Std.I64,
          Aegis.MinimumSumSubarray.minimum_sum_subarray nums l r = ok ans →
            (∃ (a k : ℕ), l.val ≤ (k : ℤ) ∧ (k : ℤ) ≤ r.val ∧
              a + k ≤ nums.val.length ∧ windowSum nums a k = 1) →
            ans.val = 1) := by
    sorry

  /-- Let rev(nums) be the array of length n with rev(nums)[i] = nums[n-1-i] for every i with 0 <= i < n. If the function called on nums returns a result ans, then the function called on rev(nums) with the same l and r returns the same result ans.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, 1 <= l <= r <= n, and for every i with 0 <= i < n, -1000 <= nums[i] <= 1000. -/
  theorem spec_8 (nums : Slice Std.I64) (l r : Std.I64)
      (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
      (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ (nums.val.length : ℤ))
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∀ ans : Std.I64,
        Aegis.MinimumSumSubarray.minimum_sum_subarray nums l r = ok ans →
          Aegis.MinimumSumSubarray.minimum_sum_subarray (revSlice nums) l r = ok ans := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (l r : Std.I64)
        (hpos : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ 100)
        (hl : 1 ≤ l.val) (hlr : l.val ≤ r.val) (hr : r.val ≤ (nums.val.length : ℤ))
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∀ ans : Std.I64,
          Aegis.MinimumSumSubarray.minimum_sum_subarray nums l r = ok ans →
            Aegis.MinimumSumSubarray.minimum_sum_subarray (revSlice nums) l r = ok ans) := by
    sorry

  end AegisSpec.MinimumSumSubarray
