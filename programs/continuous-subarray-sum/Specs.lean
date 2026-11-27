import Aegis.CheckSubarraySum.Code.Funs

/-!
# Specifications of `Aegis.CheckSubarraySum.check_subarray_sum`

LeetCode problem `continuous-subarray-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CheckSubarraySum

  def sliceSum (nums : Slice Std.I64) (a b : ℕ) : ℤ :=
    (((nums.val.drop a).take (b - a)).map (fun x => x.val)).sum

  def pref (nums : Slice Std.I64) (m : ℕ) : ℤ := sliceSum nums 0 m

  /-- The function returns a Bool r and r = true if and only if there exist integers i and j with 0 <= i < j < len(nums) and an integer n such that nums[i] + nums[i+1] + ... + nums[j] = n * k. If no such i, j, n exist, then r = false. This says exactly that nums has a contiguous subarray of length at least two whose sum is a multiple of k.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; sum_{i=0}^{len(nums)-1} nums[i] <= 2^31 - 1; and 1 <= k <= 2^31 - 1. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 100000)
      (hbnd : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
      (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1) :
      ∃ r : Bool,
        Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r ∧
          (r = true ↔
            ∃ (i j : ℕ) (n : ℤ),
              i < j ∧ j < nums.val.length ∧ sliceSum nums i (j + 1) = n * k.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 100000)
        (hbnd : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
        (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1), ∃ r : Bool,
          Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r ∧
            (r = true ↔
              ∃ (i j : ℕ) (n : ℤ),
                i < j ∧ j < nums.val.length ∧ sliceSum nums i (j + 1) = n * k.val)) := by
    sorry

  /-- The function returns a result on every input satisfying the preconditions: there exists a Bool b such that check_subarray_sum nums k = Result.ok b. It does not fail, panic, overflow, or access memory out of bounds.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; sum_{i=0}^{len(nums)-1} nums[i] <= 2^31 - 1; and 1 <= k <= 2^31 - 1. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 100000)
      (hbnd : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
      (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1) :
      ∃ b : Bool, Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok b := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 100000)
        (hbnd : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
        (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1), ∃ b : Bool, Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok b) := by
    sorry

  /-- If there exist integers i and j with 0 <= i < j < len(nums) and an integer n such that sum_{t=i}^{j} nums[t] = n * k, then the function returns true.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; sum_{i=0}^{len(nums)-1} nums[i] <= 2^31 - 1; and 1 <= k <= 2^31 - 1. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 100000)
      (hbnd : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
      (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1)
      (hwit : ∃ (i j : ℕ) (n : ℤ),
        i < j ∧ j < nums.val.length ∧ sliceSum nums i (j + 1) = n * k.val) :
      ∃ r : Bool,
        Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r ∧ r = true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 100000)
        (hbnd : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
        (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1)
        (hwit : ∃ (i j : ℕ) (n : ℤ),
          i < j ∧ j < nums.val.length ∧ sliceSum nums i (j + 1) = n * k.val), ∃ r : Bool,
          Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r ∧ r = true) := by
    sorry

  /-- If the function returns true, then there exist integers i and j with 0 <= i < j < len(nums) and an integer n such that sum_{t=i}^{j} nums[t] = n * k.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; sum_{i=0}^{len(nums)-1} nums[i] <= 2^31 - 1; and 1 <= k <= 2^31 - 1. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 100000)
      (hbnd : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
      (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1) :
      ∀ r : Bool, Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r →
        r = true →
          ∃ (i j : ℕ) (n : ℤ),
            i < j ∧ j < nums.val.length ∧ sliceSum nums i (j + 1) = n * k.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 100000)
        (hbnd : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
        (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1), ∀ r : Bool, Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r →
          r = true →
            ∃ (i j : ℕ) (n : ℤ),
              i < j ∧ j < nums.val.length ∧ sliceSum nums i (j + 1) = n * k.val) := by
    sorry

  /-- If len(nums) = 1, then the function returns false.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; sum_{i=0}^{len(nums)-1} nums[i] <= 2^31 - 1; and 1 <= k <= 2^31 - 1. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 100000)
      (hbnd : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
      (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1)
      (hlen_one : nums.val.length = 1) :
      ∃ r : Bool,
        Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r ∧ r = false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 100000)
        (hbnd : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
        (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1)
        (hlen_one : nums.val.length = 1), ∃ r : Bool,
          Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r ∧ r = false) := by
    sorry

  /-- If len(nums) >= 2, the function returns true; if len(nums) = 1, it returns false. Equivalently, for these inputs the result is true exactly when len(nums) >= 2.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; sum_{i=0}^{len(nums)-1} nums[i] <= 2^31 - 1; and k = 1. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 100000)
      (hbnd : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
      (hk : k.val = 1) :
      ∀ r : Bool, Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r →
        (r = true ↔ 2 ≤ nums.val.length) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 100000)
        (hbnd : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
        (hk : k.val = 1), ∀ r : Bool, Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r →
          (r = true ↔ 2 ≤ nums.val.length)) := by
    sorry

  /-- The function returns true if and only if there is an index i with 0 <= i < len(nums) - 1 such that nums[i] = 0 and nums[i+1] = 0.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; sum_{i=0}^{len(nums)-1} nums[i] <= 2^31 - 1; 1 <= k <= 2^31 - 1; and k > sum_{i=0}^{len(nums)-1} nums[i]. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 100000)
      (hbnd : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
      (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1)
      (hk_gt : sliceSum nums 0 nums.val.length < k.val) :
      ∃ r : Bool,
        Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r ∧
          (r = true ↔
            ∃ (i : ℕ) (hi : i + 1 < nums.val.length),
              (nums.val[i]).val = 0 ∧ (nums.val[i + 1]).val = 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 100000)
        (hbnd : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
        (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1)
        (hk_gt : sliceSum nums 0 nums.val.length < k.val), ∃ r : Bool,
          Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r ∧
            (r = true ↔
              ∃ (i : ℕ) (hi : i + 1 < nums.val.length),
                (nums.val[i]).val = 0 ∧ (nums.val[i + 1]).val = 0)) := by
    sorry

  /-- If nums[i] ≡ nums'[i] (mod k) for every i with 0 <= i < len(nums), meaning k divides nums[i] - nums'[i], then the Bool result returned for nums and k equals the Bool result returned for nums' and k.
    Preconditions: Both nums and nums' are slices with len(nums) >= 1, len(nums') = len(nums), len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000 and 0 <= nums'[i] <= 1000000000; sum_{i=0}^{len(nums)-1} nums[i] <= 2^31 - 1; sum_{i=0}^{len(nums')-1} nums'[i] <= 2^31 - 1; and 1 <= k <= 2^31 - 1. -/
  theorem spec_8 (nums nums' : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 100000)
      (hbnd : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
      (hlen'_pos : 1 ≤ nums'.val.length)
      (hlen'_le : nums'.val.length ≤ 100000)
      (hbnd' : ∀ i (h : i < nums'.val.length),
        0 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 1000000000)
      (hsum' : sliceSum nums' 0 nums'.val.length ≤ 2 ^ 31 - 1)
      (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1)
      (hlen : nums'.val.length = nums.val.length)
      (hcong : ∀ i (h : i < nums.val.length),
        k.val ∣ ((nums.val[i]).val - (nums'.val[i]).val)) :
      ∀ r r' : Bool,
        Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r →
          Aegis.CheckSubarraySum.check_subarray_sum nums' k = Result.ok r' → r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 100000)
        (hbnd : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
        (hlen'_pos : 1 ≤ nums'.val.length)
        (hlen'_le : nums'.val.length ≤ 100000)
        (hbnd' : ∀ i (h : i < nums'.val.length),
          0 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 1000000000)
        (hsum' : sliceSum nums' 0 nums'.val.length ≤ 2 ^ 31 - 1)
        (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1)
        (hlen : nums'.val.length = nums.val.length)
        (hcong : ∀ i (h : i < nums.val.length),
          k.val ∣ ((nums.val[i]).val - (nums'.val[i]).val)), ∀ r r' : Bool,
          Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r →
            Aegis.CheckSubarraySum.check_subarray_sum nums' k = Result.ok r' → r = r') := by
    sorry

  /-- The Bool result returned for nums and k equals the Bool result returned for nums' and k, where nums' is the reversal of nums.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; sum_{i=0}^{len(nums)-1} nums[i] <= 2^31 - 1; 1 <= k <= 2^31 - 1; and nums' is a slice with len(nums') = len(nums) and nums'[i] = nums[len(nums)-1-i] for every 0 <= i < len(nums). -/
  theorem spec_9 (nums nums' : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 100000)
      (hbnd : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
      (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1)
      (hlen : nums'.val.length = nums.val.length)
      (hrev : nums'.val = nums.val.reverse) :
      ∀ r r' : Bool,
        Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r →
          Aegis.CheckSubarraySum.check_subarray_sum nums' k = Result.ok r' → r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 100000)
        (hbnd : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
        (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1)
        (hlen : nums'.val.length = nums.val.length)
        (hrev : nums'.val = nums.val.reverse), ∀ r r' : Bool,
          Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r →
            Aegis.CheckSubarraySum.check_subarray_sum nums' k = Result.ok r' → r = r') := by
    sorry

  /-- If check_subarray_sum nums k returns true, then check_subarray_sum nums' k returns true.
    Preconditions: Both nums and nums' are slices with len(nums) >= 1, len(nums') >= len(nums), len(nums') <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; for every i with 0 <= i < len(nums'), 0 <= nums'[i] <= 1000000000; sum_{i=0}^{len(nums)-1} nums[i] <= 2^31 - 1; sum_{i=0}^{len(nums')-1} nums'[i] <= 2^31 - 1; 1 <= k <= 2^31 - 1; and there exists s with 0 <= s <= len(nums') - len(nums) such that nums'[s+i] = nums[i] for every 0 <= i < len(nums). -/
  theorem spec_10 (nums nums' : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 100000)
      (hbnd : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
      (hlen'_pos : 1 ≤ nums'.val.length)
      (hlen'_ge : nums.val.length ≤ nums'.val.length)
      (hlen'_le : nums'.val.length ≤ 100000)
      (hbnd' : ∀ i (h : i < nums'.val.length),
        0 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 1000000000)
      (hsum' : sliceSum nums' 0 nums'.val.length ≤ 2 ^ 31 - 1)
      (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1)
      (hsub : ∃ s : ℕ, s ≤ nums'.val.length - nums.val.length ∧
        (nums'.val.drop s).take nums.val.length = nums.val) :
      Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok true →
        Aegis.CheckSubarraySum.check_subarray_sum nums' k = Result.ok true := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 100000)
        (hbnd : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
        (hlen'_pos : 1 ≤ nums'.val.length)
        (hlen'_ge : nums.val.length ≤ nums'.val.length)
        (hlen'_le : nums'.val.length ≤ 100000)
        (hbnd' : ∀ i (h : i < nums'.val.length),
          0 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 1000000000)
        (hsum' : sliceSum nums' 0 nums'.val.length ≤ 2 ^ 31 - 1)
        (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1)
        (hsub : ∃ s : ℕ, s ≤ nums'.val.length - nums.val.length ∧
          (nums'.val.drop s).take nums.val.length = nums.val), Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok true →
          Aegis.CheckSubarraySum.check_subarray_sum nums' k = Result.ok true) := by
    sorry

  /-- Define pref(m) = sum_{t=0}^{m-1} nums[t] for 0 <= m <= len(nums), with pref(0) = 0. The function returns true if and only if there exist integers p and q with 0 <= p < q <= len(nums), q - p >= 2, and an integer n such that pref(q) - pref(p) = n * k.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; sum_{i=0}^{len(nums)-1} nums[i] <= 2^31 - 1; and 1 <= k <= 2^31 - 1. -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 100000)
      (hbnd : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
      (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1) :
      ∃ r : Bool,
        Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r ∧
          (r = true ↔
            ∃ (p q : ℕ) (n : ℤ),
              p < q ∧ q ≤ nums.val.length ∧ 2 ≤ q - p ∧
                pref nums q - pref nums p = n * k.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 100000)
        (hbnd : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
        (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1), ∃ r : Bool,
          Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r ∧
            (r = true ↔
              ∃ (p q : ℕ) (n : ℤ),
                p < q ∧ q ≤ nums.val.length ∧ 2 ≤ q - p ∧
                  pref nums q - pref nums p = n * k.val)) := by
    sorry

  /-- The function returns true if and only if nums[0] + nums[1] is a multiple of k, i.e. there exists an integer n such that nums[0] + nums[1] = n * k.
    Preconditions: len(nums) = 2; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; sum_{i=0}^{len(nums)-1} nums[i] <= 2^31 - 1; and 1 <= k <= 2^31 - 1. -/
  theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : nums.val.length = 2)
      (hbnd : ∀ i (h : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
      (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1) :
      ∃ r : Bool,
        Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r ∧
          (r = true ↔ ∃ n : ℤ, (nums.val[0]).val + (nums.val[1]).val = n * k.val) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : nums.val.length = 2)
        (hbnd : ∀ i (h : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hsum : sliceSum nums 0 nums.val.length ≤ 2 ^ 31 - 1)
        (hk_ge : 1 ≤ k.val) (hk_le : k.val ≤ 2 ^ 31 - 1), ∃ r : Bool,
          Aegis.CheckSubarraySum.check_subarray_sum nums k = Result.ok r ∧
            (r = true ↔ ∃ n : ℤ, (nums.val[0]).val + (nums.val[1]).val = n * k.val)) := by
    sorry

  end AegisSpec.CheckSubarraySum
