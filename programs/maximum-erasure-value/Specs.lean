import Aegis.MaximumUniqueSubarray.Code.Funs

/-!
# Specifications of `Aegis.MaximumUniqueSubarray.maximum_unique_subarray`

LeetCode problem `maximum-erasure-value`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumUniqueSubarray

  def vals (nums : Slice Std.I64) : List Int :=
    nums.val.map (fun v => v.val)

  def elem (nums : Slice Std.I64) (i : Nat) : Int :=
    (vals nums).getD i 0

  def sumRange (nums : Slice Std.I64) (l k : Nat) : Int :=
    (((vals nums).drop l).take (k + 1 - l)).sum

  def totalSum (nums : Slice Std.I64) : Int :=
    (vals nums).sum

  def PairwiseDistinct (nums : Slice Std.I64) (l k : Nat) : Prop :=
    ∀ a b : Nat, l ≤ a → a < b → b ≤ k → elem nums a ≠ elem nums b

  def ValidSubarray (nums : Slice Std.I64) (l k : Nat) : Prop :=
    l ≤ k ∧ k < nums.val.length ∧ PairwiseDistinct nums l k

  /-- The function returns a result r and does not fail. Let a subarray nums[l..k] be called valid when 0 <= l <= k < len(nums) and its elements are pairwise distinct, i.e. nums[a] != nums[b] for every l <= a < b <= k. Then r is the maximum, over all valid subarrays, of the sum nums[l] + nums[l+1] + ... + nums[k]. Equivalently: every valid subarray has sum <= r, and some valid subarray has sum exactly r.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. All indices are 0-based. -/
  theorem spec_1 (nums : Slice Std.I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_elems : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10000) :
      ∃ r : Std.I64, Aegis.MaximumUniqueSubarray.maximum_unique_subarray nums = ok r ∧
        (∀ l k : Nat, ValidSubarray nums l k → sumRange nums l k ≤ r.val) ∧
        (∃ l k : Nat, ValidSubarray nums l k ∧ sumRange nums l k = r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_elems : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r : Std.I64, Aegis.MaximumUniqueSubarray.maximum_unique_subarray nums = ok r ∧
          (∀ l k : Nat, ValidSubarray nums l k → sumRange nums l k ≤ r.val) ∧
          (∃ l k : Nat, ValidSubarray nums l k ∧ sumRange nums l k = r.val)) := by
    sorry

  /-- The function returns a result r and there exist indices l,k with 0 <= l <= k < len(nums) such that nums[l],...,nums[k] are pairwise distinct (nums[a] != nums[b] for every l <= a < b <= k) and r = nums[l] + nums[l+1] + ... + nums[k].
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. All indices are 0-based. -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_elems : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10000) :
      ∃ r : Std.I64, Aegis.MaximumUniqueSubarray.maximum_unique_subarray nums = ok r ∧
        ∃ l k : Nat, ValidSubarray nums l k ∧ sumRange nums l k = r.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_elems : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r : Std.I64, Aegis.MaximumUniqueSubarray.maximum_unique_subarray nums = ok r ∧
          ∃ l k : Nat, ValidSubarray nums l k ∧ sumRange nums l k = r.val) := by
    sorry

  /-- The function returns a result r and r <= nums[0] + nums[1] + ... + nums[len(nums)-1].
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. All indices are 0-based. -/
  theorem spec_3 (nums : Slice Std.I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_elems : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10000) :
      ∃ r : Std.I64, Aegis.MaximumUniqueSubarray.maximum_unique_subarray nums = ok r ∧
        r.val ≤ totalSum nums := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_elems : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r : Std.I64, Aegis.MaximumUniqueSubarray.maximum_unique_subarray nums = ok r ∧
          r.val ≤ totalSum nums) := by
    sorry

  /-- The function returns a result r and, for every l,k with 0 <= l <= k < len(nums) such that nums[a] != nums[b] for all l <= a < b <= k, we have nums[l] + nums[l+1] + ... + nums[k] <= r.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. All indices are 0-based. -/
  theorem spec_4 (nums : Slice Std.I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_elems : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10000) :
      ∃ r : Std.I64, Aegis.MaximumUniqueSubarray.maximum_unique_subarray nums = ok r ∧
        ∀ l k : Nat, ValidSubarray nums l k → sumRange nums l k ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_elems : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r : Std.I64, Aegis.MaximumUniqueSubarray.maximum_unique_subarray nums = ok r ∧
          ∀ l k : Nat, ValidSubarray nums l k → sumRange nums l k ≤ r.val) := by
    sorry

  /-- The function returns a result r and, if nums[i] = nums[0] for every i with 0 <= i < len(nums), then r = nums[0].
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. All indices are 0-based. -/
  theorem spec_5 (nums : Slice Std.I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_elems : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10000) :
      ∃ r : Std.I64, Aegis.MaximumUniqueSubarray.maximum_unique_subarray nums = ok r ∧
        ((∀ i : Nat, i < nums.val.length → elem nums i = elem nums 0) → r.val = elem nums 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_elems : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r : Std.I64, Aegis.MaximumUniqueSubarray.maximum_unique_subarray nums = ok r ∧
          ((∀ i : Nat, i < nums.val.length → elem nums i = elem nums 0) → r.val = elem nums 0)) := by
    sorry

  /-- The function returns a result r and, if nums[a] != nums[b] for every 0 <= a < b < len(nums), then r = nums[0] + nums[1] + ... + nums[len(nums)-1].
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. All indices are 0-based. -/
  theorem spec_6 (nums : Slice Std.I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_elems : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10000) :
      ∃ r : Std.I64, Aegis.MaximumUniqueSubarray.maximum_unique_subarray nums = ok r ∧
        ((∀ a b : Nat, a < b → b < nums.val.length → elem nums a ≠ elem nums b) →
          r.val = totalSum nums) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_elems : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r : Std.I64, Aegis.MaximumUniqueSubarray.maximum_unique_subarray nums = ok r ∧
          ((∀ a b : Nat, a < b → b < nums.val.length → elem nums a ≠ elem nums b) →
            r.val = totalSum nums)) := by
    sorry

  /-- The function returns a result r (it does not fail, overflow, or panic) for every input satisfying the preconditions.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. All indices are 0-based. -/
  theorem spec_7 (nums : Slice Std.I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_elems : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10000) :
      ∃ r : Std.I64, Aegis.MaximumUniqueSubarray.maximum_unique_subarray nums = ok r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_elems : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r : Std.I64, Aegis.MaximumUniqueSubarray.maximum_unique_subarray nums = ok r) := by
    sorry

  /-- The function returns a result r and there exist indices l,k with 0 <= l <= k < len(nums) such that nums[l],...,nums[k] are pairwise distinct, r = nums[l] + nums[l+1] + ... + nums[k], and this subarray is maximal with respect to one-step extension: if l > 0 then nums[l-1] = nums[t] for some t with l <= t <= k, and if k < len(nums)-1 then nums[k+1] = nums[t] for some t with l <= t <= k.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. All indices are 0-based. -/
  theorem spec_8 (nums : Slice Std.I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_elems : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10000) :
      ∃ r : Std.I64, Aegis.MaximumUniqueSubarray.maximum_unique_subarray nums = ok r ∧
        ∃ l k : Nat, ValidSubarray nums l k ∧ sumRange nums l k = r.val ∧
          (0 < l → ∃ t : Nat, l ≤ t ∧ t ≤ k ∧ elem nums (l - 1) = elem nums t) ∧
          (k < nums.val.length - 1 → ∃ t : Nat, l ≤ t ∧ t ≤ k ∧ elem nums (k + 1) = elem nums t) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_elems : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r : Std.I64, Aegis.MaximumUniqueSubarray.maximum_unique_subarray nums = ok r ∧
          ∃ l k : Nat, ValidSubarray nums l k ∧ sumRange nums l k = r.val ∧
            (0 < l → ∃ t : Nat, l ≤ t ∧ t ≤ k ∧ elem nums (l - 1) = elem nums t) ∧
            (k < nums.val.length - 1 → ∃ t : Nat, l ≤ t ∧ t ≤ k ∧ elem nums (k + 1) = elem nums t)) := by
    sorry

  end AegisSpec.MaximumUniqueSubarray
