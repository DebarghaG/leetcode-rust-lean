import Aegis.FindSubarrays.Code.Funs

/-!
# Specifications of `Aegis.FindSubarrays.find_subarrays`

LeetCode problem `find-subarrays-with-equal-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindSubarrays

  def elem (nums : Slice Std.I64) (i : ℕ) : ℤ := (nums.val.getD i default).val

  def windowSum (nums : Slice Std.I64) (i : ℕ) : ℤ := elem nums i + elem nums (i + 1)

  def InI64Range (nums : Slice Std.I64) : Prop :=
    ∀ i : ℕ, i < nums.val.length → -1000000000 ≤ elem nums i ∧ elem nums i ≤ 1000000000

  def HasEqualWindowSum (nums : Slice Std.I64) : Prop :=
    ∃ i j : ℕ, i < j ∧ j + 2 ≤ nums.val.length ∧ windowSum nums i = windowSum nums j

  def WindowsSumDistinct (nums : Slice Std.I64) : Prop :=
    ∀ i j : ℕ, i < j → j + 2 ≤ nums.val.length → windowSum nums i ≠ windowSum nums j

  /-- The function returns a result r and r = true if and only if there exist integers i and j such that 0 <= i < j <= len(nums) - 2 and nums[i] + nums[i+1] = nums[j] + nums[j+1].
    Preconditions: len(nums) >= 2, len(nums) <= 1000, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
      (h_bounds : InI64Range nums) :
      ∃ r, Aegis.FindSubarrays.find_subarrays nums = ok r ∧
        (r = true ↔ HasEqualWindowSum nums) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
        (h_bounds : InI64Range nums), ∃ r, Aegis.FindSubarrays.find_subarrays nums = ok r ∧
          (r = true ↔ HasEqualWindowSum nums)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail due to i64 overflow, out-of-bounds indexing, or panic.
    Preconditions: len(nums) >= 2, len(nums) <= 1000, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
      (h_bounds : InI64Range nums) :
      ∃ r, Aegis.FindSubarrays.find_subarrays nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
        (h_bounds : InI64Range nums), ∃ r, Aegis.FindSubarrays.find_subarrays nums = ok r) := by
    sorry

  /-- Whenever the function returns r = true, there exist integers i and j with 0 <= i < j <= len(nums) - 2 and nums[i] + nums[i+1] = nums[j] + nums[j+1].
    Preconditions: len(nums) >= 2, len(nums) <= 1000, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
      (h_bounds : InI64Range nums)
      (h_res : Aegis.FindSubarrays.find_subarrays nums = ok true) :
      ∃ i j : ℕ, i < j ∧ j + 2 ≤ nums.val.length ∧
        windowSum nums i = windowSum nums j := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
        (h_bounds : InI64Range nums)
        (h_res : Aegis.FindSubarrays.find_subarrays nums = ok true), ∃ i j : ℕ, i < j ∧ j + 2 ≤ nums.val.length ∧
          windowSum nums i = windowSum nums j) := by
    sorry

  /-- Whenever the function returns r = false, for every integers i and j with 0 <= i < j <= len(nums) - 2, nums[i] + nums[i+1] != nums[j] + nums[j+1].
    Preconditions: len(nums) >= 2, len(nums) <= 1000, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
      (h_bounds : InI64Range nums)
      (h_res : Aegis.FindSubarrays.find_subarrays nums = ok false) :
      ∀ i j : ℕ, i < j → j + 2 ≤ nums.val.length → windowSum nums i ≠ windowSum nums j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
        (h_bounds : InI64Range nums)
        (h_res : Aegis.FindSubarrays.find_subarrays nums = ok false), ∀ i j : ℕ, i < j → j + 2 ≤ nums.val.length → windowSum nums i ≠ windowSum nums j) := by
    sorry

  /-- If the function returns r = true, then len(nums) >= 3.
    Preconditions: len(nums) >= 2, len(nums) <= 1000, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
      (h_bounds : InI64Range nums)
      (h_res : Aegis.FindSubarrays.find_subarrays nums = ok true) :
      3 ≤ nums.val.length := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
        (h_bounds : InI64Range nums)
        (h_res : Aegis.FindSubarrays.find_subarrays nums = ok true), 3 ≤ nums.val.length) := by
    sorry

  /-- If len(nums) = 2, the function returns r = false.
    Preconditions: len(nums) = 2 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (h_len : nums.val.length = 2)
      (h_bounds : InI64Range nums) :
      ∃ r, Aegis.FindSubarrays.find_subarrays nums = ok r ∧ r = false := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : nums.val.length = 2)
        (h_bounds : InI64Range nums), ∃ r, Aegis.FindSubarrays.find_subarrays nums = ok r ∧ r = false) := by
    sorry

  /-- The function returns a result r and r = true if and only if nums[0] = nums[2].
    Preconditions: len(nums) = 3 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (h_len : nums.val.length = 3)
      (h_bounds : InI64Range nums) :
      ∃ r, Aegis.FindSubarrays.find_subarrays nums = ok r ∧ (r = true ↔ elem nums 0 = elem nums 2) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : nums.val.length = 3)
        (h_bounds : InI64Range nums), ∃ r, Aegis.FindSubarrays.find_subarrays nums = ok r ∧ (r = true ↔ elem nums 0 = elem nums 2)) := by
    sorry

  /-- If find_subarrays nums returns r = true, then find_subarrays nums' returns r' = true.
    Preconditions: nums and nums' are slices of i64; each satisfies len >= 2, len <= 1000, and every entry is in [-1000000000, 1000000000]; moreover len(nums') >= len(nums) and for every i with 0 <= i < len(nums), nums'[i] = nums[i]. -/
  theorem spec_8 (nums nums' : Slice Std.I64)
      (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
      (h_bounds : InI64Range nums)
      (h_len_ge' : 2 ≤ nums'.val.length) (h_len_le' : nums'.val.length ≤ 1000)
      (h_bounds' : InI64Range nums')
      (h_prefix_len : nums.val.length ≤ nums'.val.length)
      (h_prefix : ∀ i : ℕ, i < nums.val.length → elem nums' i = elem nums i)
      (h_res : Aegis.FindSubarrays.find_subarrays nums = ok true) :
      Aegis.FindSubarrays.find_subarrays nums' = ok true := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
        (h_bounds : InI64Range nums)
        (h_len_ge' : 2 ≤ nums'.val.length) (h_len_le' : nums'.val.length ≤ 1000)
        (h_bounds' : InI64Range nums')
        (h_prefix_len : nums.val.length ≤ nums'.val.length)
        (h_prefix : ∀ i : ℕ, i < nums.val.length → elem nums' i = elem nums i)
        (h_res : Aegis.FindSubarrays.find_subarrays nums = ok true), Aegis.FindSubarrays.find_subarrays nums' = ok true) := by
    sorry

  /-- Let revnums be the slice of length len(nums) with revnums[i] = nums[len(nums)-1-i] for every i with 0 <= i < len(nums). Whenever find_subarrays nums returns r and find_subarrays revnums returns r', we have r = r'.
    Preconditions: nums is a slice of i64 with len(nums) >= 2, len(nums) <= 1000, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_9 (nums revnums : Slice Std.I64)
      (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
      (h_bounds : InI64Range nums)
      (h_rev : revnums.val = nums.val.reverse)
      (r r' : Bool)
      (hr : Aegis.FindSubarrays.find_subarrays nums = ok r)
      (hr' : Aegis.FindSubarrays.find_subarrays revnums = ok r') :
      r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums revnums : Slice Std.I64)
        (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
        (h_bounds : InI64Range nums)
        (h_rev : revnums.val = nums.val.reverse)
        (r r' : Bool)
        (hr : Aegis.FindSubarrays.find_subarrays nums = ok r)
        (hr' : Aegis.FindSubarrays.find_subarrays revnums = ok r'), r = r') := by
    sorry

  /-- Whenever find_subarrays nums returns r and find_subarrays nums' returns r', we have r = r'.
    Preconditions: nums and nums' are slices of i64 of equal length; each satisfies len >= 2, len <= 1000, and every entry is in [-1000000000, 1000000000]; there exists an integer c such that for every i with 0 <= i < len(nums), nums'[i] = nums[i] + c as integers. -/
  theorem spec_10 (nums nums' : Slice Std.I64)
      (h_len : nums'.val.length = nums.val.length)
      (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
      (h_bounds : InI64Range nums)
      (h_len_ge' : 2 ≤ nums'.val.length) (h_len_le' : nums'.val.length ≤ 1000)
      (h_bounds' : InI64Range nums')
      (h_shift : ∃ c : ℤ, ∀ i : ℕ, i < nums.val.length → elem nums' i = elem nums i + c)
      (r r' : Bool)
      (hr : Aegis.FindSubarrays.find_subarrays nums = ok r)
      (hr' : Aegis.FindSubarrays.find_subarrays nums' = ok r') :
      r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (h_len : nums'.val.length = nums.val.length)
        (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 1000)
        (h_bounds : InI64Range nums)
        (h_len_ge' : 2 ≤ nums'.val.length) (h_len_le' : nums'.val.length ≤ 1000)
        (h_bounds' : InI64Range nums')
        (h_shift : ∃ c : ℤ, ∀ i : ℕ, i < nums.val.length → elem nums' i = elem nums i + c)
        (r r' : Bool)
        (hr : Aegis.FindSubarrays.find_subarrays nums = ok r)
        (hr' : Aegis.FindSubarrays.find_subarrays nums' = ok r'), r = r') := by
    sorry

  end AegisSpec.FindSubarrays
