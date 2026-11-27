import Aegis.NumSubarrayBoundedMax.Code.Funs

/-!
# Specifications of `Aegis.NumSubarrayBoundedMax.num_subarray_bounded_max`

LeetCode problem `number-of-subarrays-with-bounded-maximum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.NumSubarrayBoundedMax

  namespace AegisSpec.NumSubarrayBoundedMax

  def contents (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def subMax (a : List ℤ) (i j : ℕ) : ℤ :=
    match (a.drop i).take (j + 1 - i) with
    | [] => 0
    | x :: xs => xs.foldl max x

  noncomputable def count (a : List ℤ) (l r : ℤ) : ℕ :=
    (((Finset.range a.length).product (Finset.range a.length)).filter
      (fun p : ℕ × ℕ =>
        p.1 ≤ p.2 ∧ l ≤ subMax a p.1 p.2 ∧ subMax a p.1 p.2 ≤ r)).card

  noncomputable def countLe (a : List ℤ) (t : ℤ) : ℕ :=
    (((Finset.range a.length).product (Finset.range a.length)).filter
      (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ subMax a p.1 p.2 ≤ t)).card

  noncomputable def countInRange (a : List ℤ) (l r : ℤ) : ℕ :=
    (a.filter (fun x => decide (l ≤ x ∧ x ≤ r))).length

  def classify (l r x : ℤ) : ℕ :=
    if x < l then 0 else if x ≤ r then 1 else 2

  def classAt (a : List ℤ) (l r : ℤ) (i : ℕ) : Option ℕ :=
    (a[i]?).map (fun x => classify l r x)

  /-- Whenever the function returns a result r, r equals the number of pairs of integers (i, j) such that 0 <= i <= j < len(nums) and left <= max(nums[i], ..., nums[j]) <= right, where max(nums[i], ..., nums[j]) denotes the maximum of the non-empty contiguous subarray nums[i], nums[i+1], ..., nums[j].
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9; 0 <= left <= right <= 10^9; and the number of qualifying subarrays is at most 2^31 - 1. -/
  theorem spec_1 (nums : Slice Std.I64) (left right : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
        (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
      (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
      (h_right : right.val ≤ 10 ^ 9)
      (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
      (r : Std.I64) (hres : num_subarray_bounded_max nums left right = ok r) :
      r.val = (count (contents nums) left.val right.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (left right : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
          (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
        (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
        (h_right : right.val ≤ 10 ^ 9)
        (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
        (r : Std.I64) (hres : num_subarray_bounded_max nums left right = ok r), r.val = (count (contents nums) left.val right.val : ℤ)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, overflow, or access memory out of bounds) for every input satisfying the preconditions.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9; 0 <= left <= right <= 10^9; and the number of qualifying subarrays is at most 2^31 - 1. -/
  theorem spec_2 (nums : Slice Std.I64) (left right : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
        (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
      (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
      (h_right : right.val ≤ 10 ^ 9)
      (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1) :
      ∃ r : Std.I64, num_subarray_bounded_max nums left right = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (left right : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
          (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
        (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
        (h_right : right.val ≤ 10 ^ 9)
        (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1), ∃ r : Std.I64, num_subarray_bounded_max nums left right = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9; 0 <= left <= right <= 10^9; and the number of qualifying subarrays is at most 2^31 - 1. -/
  theorem spec_3 (nums : Slice Std.I64) (left right : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
        (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
      (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
      (h_right : right.val ≤ 10 ^ 9)
      (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
      (r : Std.I64) (hres : num_subarray_bounded_max nums left right = ok r) :
      (0 : ℤ) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (left right : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
          (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
        (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
        (h_right : right.val ≤ 10 ^ 9)
        (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
        (r : Std.I64) (hres : num_subarray_bounded_max nums left right = ok r), (0 : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= len(nums) * (len(nums) + 1) / 2.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9; 0 <= left <= right <= 10^9; and the number of qualifying subarrays is at most 2^31 - 1. -/
  theorem spec_4 (nums : Slice Std.I64) (left right : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
        (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
      (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
      (h_right : right.val ≤ 10 ^ 9)
      (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
      (r : Std.I64) (hres : num_subarray_bounded_max nums left right = ok r) :
      r.val ≤ ((nums.val.length * (nums.val.length + 1) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (left right : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
          (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
        (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
        (h_right : right.val ≤ 10 ^ 9)
        (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
        (r : Std.I64) (hres : num_subarray_bounded_max nums left right = ok r), r.val ≤ ((nums.val.length * (nums.val.length + 1) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = len(nums) * (len(nums) + 1) / 2.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), left <= nums[i] <= right; 0 <= left <= right <= 10^9; and the number of qualifying subarrays is at most 2^31 - 1. -/
  theorem spec_5 (nums : Slice Std.I64) (left right : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
        left.val ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ right.val)
      (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
      (h_right : right.val ≤ 10 ^ 9)
      (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
      (r : Std.I64) (hres : num_subarray_bounded_max nums left right = ok r) :
      r.val = ((nums.val.length * (nums.val.length + 1) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (left right : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
          left.val ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ right.val)
        (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
        (h_right : right.val ≤ 10 ^ 9)
        (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
        (r : Std.I64) (hres : num_subarray_bounded_max nums left right = ok r), r.val = ((nums.val.length * (nums.val.length + 1) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), nums[i] < left or nums[i] > right; 0 <= left <= right <= 10^9; and the number of qualifying subarrays is at most 2^31 - 1. -/
  theorem spec_6 (nums : Slice Std.I64) (left right : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
        (nums.val[i]'hi).val < left.val ∨ right.val < (nums.val[i]'hi).val)
      (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
      (h_right : right.val ≤ 10 ^ 9)
      (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
      (r : Std.I64) (hres : num_subarray_bounded_max nums left right = ok r) :
      r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (left right : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
          (nums.val[i]'hi).val < left.val ∨ right.val < (nums.val[i]'hi).val)
        (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
        (h_right : right.val ≤ 10 ^ 9)
        (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
        (r : Std.I64) (hres : num_subarray_bounded_max nums left right = ok r), r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r > 0 if and only if there exists an index i with 0 <= i < len(nums) and left <= nums[i] <= right.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9; 0 <= left <= right <= 10^9; and the number of qualifying subarrays is at most 2^31 - 1. -/
  theorem spec_7 (nums : Slice Std.I64) (left right : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
        (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
      (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
      (h_right : right.val ≤ 10 ^ 9)
      (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
      (r : Std.I64) (hres : num_subarray_bounded_max nums left right = ok r) :
      0 < r.val ↔ ∃ (i : ℕ) (hi : i < nums.val.length),
        left.val ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ right.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (left right : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
          (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
        (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
        (h_right : right.val ≤ 10 ^ 9)
        (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
        (r : Std.I64) (hres : num_subarray_bounded_max nums left right = ok r), 0 < r.val ↔ ∃ (i : ℕ) (hi : i < nums.val.length),
          left.val ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ right.val) := by
    sorry

  /-- Whenever the function returns a result r, r is at least the number of indices i with 0 <= i < len(nums) and left <= nums[i] <= right.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9; 0 <= left <= right <= 10^9; and the number of qualifying subarrays is at most 2^31 - 1. -/
  theorem spec_8 (nums : Slice Std.I64) (left right : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
        (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
      (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
      (h_right : right.val ≤ 10 ^ 9)
      (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
      (r : Std.I64) (hres : num_subarray_bounded_max nums left right = ok r) :
      (countInRange (contents nums) left.val right.val : ℤ) ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (left right : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
          (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
        (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
        (h_right : right.val ≤ 10 ^ 9)
        (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
        (r : Std.I64) (hres : num_subarray_bounded_max nums left right = ok r), (countInRange (contents nums) left.val right.val : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if left <= nums[0] <= right, and r = 0 otherwise.
    Preconditions: len(nums) = 1; 0 <= nums[0] <= 10^9; 0 <= left <= right <= 10^9; and the number of qualifying subarrays is at most 2^31 - 1. -/
  theorem spec_9 (nums : Slice Std.I64) (left right x : Std.I64)
      (h_len : nums.val.length = 1) (h_nums : nums.val = [x])
      (h_x : (0 : ℤ) ≤ x.val ∧ x.val ≤ 10 ^ 9)
      (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
      (h_right : right.val ≤ 10 ^ 9)
      (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
      (r : Std.I64) (hres : num_subarray_bounded_max nums left right = ok r) :
      r.val = (if left.val ≤ x.val ∧ x.val ≤ right.val then 1 else 0) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (left right x : Std.I64)
        (h_len : nums.val.length = 1) (h_nums : nums.val = [x])
        (h_x : (0 : ℤ) ≤ x.val ∧ x.val ≤ 10 ^ 9)
        (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
        (h_right : right.val ≤ 10 ^ 9)
        (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
        (r : Std.I64) (hres : num_subarray_bounded_max nums left right = ok r), r.val = (if left.val ≤ x.val ∧ x.val ≤ right.val then 1 else 0)) := by
    sorry

  /-- Define, for any integer t, C(t) as the number of pairs (i, j) with 0 <= i <= j < len(nums) and max(nums[i], ..., nums[j]) <= t, where max(nums[i], ..., nums[j]) is the maximum of the non-empty subarray nums[i], ..., nums[j]. Whenever the function returns a result r, r = C(right) - C(left - 1).
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9; 0 <= left <= right <= 10^9; and the number of qualifying subarrays is at most 2^31 - 1. -/
  theorem spec_10 (nums : Slice Std.I64) (left right : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
        (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
      (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
      (h_right : right.val ≤ 10 ^ 9)
      (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
      (r : Std.I64) (hres : num_subarray_bounded_max nums left right = ok r) :
      r.val = (countLe (contents nums) right.val : ℤ)
        - (countLe (contents nums) (left.val - 1) : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (left right : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
          (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
        (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
        (h_right : right.val ≤ 10 ^ 9)
        (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
        (r : Std.I64) (hres : num_subarray_bounded_max nums left right = ok r), r.val = (countLe (contents nums) right.val : ℤ)
          - (countLe (contents nums) (left.val - 1) : ℤ)) := by
    sorry

  /-- Whenever the function returns r1 on input (nums, left, right1) and r2 on input (nums, left, right2), r1 <= r2.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9; 0 <= left <= right1 <= right2 <= 10^9; and the qualifying counts for (nums,left,right1) and (nums,left,right2) are each at most 2^31 - 1. -/
  theorem spec_11 (nums : Slice Std.I64) (left right1 right2 : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
        (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
      (h_left : (0 : ℤ) ≤ left.val) (h_le1 : left.val ≤ right1.val)
      (h_le12 : right1.val ≤ right2.val) (h_right2 : right2.val ≤ 10 ^ 9)
      (h_count1 : count (contents nums) left.val right1.val ≤ 2 ^ 31 - 1)
      (h_count2 : count (contents nums) left.val right2.val ≤ 2 ^ 31 - 1)
      (r1 r2 : Std.I64)
      (hres1 : num_subarray_bounded_max nums left right1 = ok r1)
      (hres2 : num_subarray_bounded_max nums left right2 = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (left right1 right2 : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
          (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
        (h_left : (0 : ℤ) ≤ left.val) (h_le1 : left.val ≤ right1.val)
        (h_le12 : right1.val ≤ right2.val) (h_right2 : right2.val ≤ 10 ^ 9)
        (h_count1 : count (contents nums) left.val right1.val ≤ 2 ^ 31 - 1)
        (h_count2 : count (contents nums) left.val right2.val ≤ 2 ^ 31 - 1)
        (r1 r2 : Std.I64)
        (hres1 : num_subarray_bounded_max nums left right1 = ok r1)
        (hres2 : num_subarray_bounded_max nums left right2 = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- Whenever the function returns r1 on input (nums, left1, right) and r2 on input (nums, left2, right), r2 <= r1.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9; 0 <= left1 <= left2 <= right <= 10^9; and the qualifying counts for (nums,left1,right) and (nums,left2,right) are each at most 2^31 - 1. -/
  theorem spec_12 (nums : Slice Std.I64) (left1 left2 right : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
        (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
      (h_left1 : (0 : ℤ) ≤ left1.val) (h_le12 : left1.val ≤ left2.val)
      (h_le2 : left2.val ≤ right.val) (h_right : right.val ≤ 10 ^ 9)
      (h_count1 : count (contents nums) left1.val right.val ≤ 2 ^ 31 - 1)
      (h_count2 : count (contents nums) left2.val right.val ≤ 2 ^ 31 - 1)
      (r1 r2 : Std.I64)
      (hres1 : num_subarray_bounded_max nums left1 right = ok r1)
      (hres2 : num_subarray_bounded_max nums left2 right = ok r2) :
      r2.val ≤ r1.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (left1 left2 right : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
          (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
        (h_left1 : (0 : ℤ) ≤ left1.val) (h_le12 : left1.val ≤ left2.val)
        (h_le2 : left2.val ≤ right.val) (h_right : right.val ≤ 10 ^ 9)
        (h_count1 : count (contents nums) left1.val right.val ≤ 2 ^ 31 - 1)
        (h_count2 : count (contents nums) left2.val right.val ≤ 2 ^ 31 - 1)
        (r1 r2 : Std.I64)
        (hres1 : num_subarray_bounded_max nums left1 right = ok r1)
        (hres2 : num_subarray_bounded_max nums left2 right = ok r2), r2.val ≤ r1.val) := by
    sorry

  /-- Whenever the function returns a result r on input (nums, left, right) and a result r' on input (nums', left, right), r = r'.
    Preconditions: len(nums) = len(nums') = n with 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 10^9 and 0 <= nums'[i] <= 10^9; 0 <= left <= right <= 10^9; for every i, nums[i] and nums'[i] have the same three-way relation to [left, right] (both are < left, both are in [left, right], or both are > right); and the qualifying counts for both (nums,left,right) and (nums',left,right) are at most 2^31 - 1. -/
  theorem spec_13 (nums nums' : Slice Std.I64) (left right : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
      (h_len_eq : nums'.val.length = nums.val.length)
      (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
        (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
      (h_nums' : ∀ (i : ℕ) (hi : i < nums'.val.length),
        (0 : ℤ) ≤ (nums'.val[i]'hi).val ∧ (nums'.val[i]'hi).val ≤ 10 ^ 9)
      (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
      (h_right : right.val ≤ 10 ^ 9)
      (h_class : ∀ (i : ℕ), i < nums.val.length →
        classAt (contents nums) left.val right.val i
          = classAt (contents nums') left.val right.val i)
      (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
      (h_count' : count (contents nums') left.val right.val ≤ 2 ^ 31 - 1)
      (r r' : Std.I64)
      (hres : num_subarray_bounded_max nums left right = ok r)
      (hres' : num_subarray_bounded_max nums' left right = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (left right : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
        (h_len_eq : nums'.val.length = nums.val.length)
        (h_nums : ∀ (i : ℕ) (hi : i < nums.val.length),
          (0 : ℤ) ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10 ^ 9)
        (h_nums' : ∀ (i : ℕ) (hi : i < nums'.val.length),
          (0 : ℤ) ≤ (nums'.val[i]'hi).val ∧ (nums'.val[i]'hi).val ≤ 10 ^ 9)
        (h_left : (0 : ℤ) ≤ left.val) (h_le : left.val ≤ right.val)
        (h_right : right.val ≤ 10 ^ 9)
        (h_class : ∀ (i : ℕ), i < nums.val.length →
          classAt (contents nums) left.val right.val i
            = classAt (contents nums') left.val right.val i)
        (h_count : count (contents nums) left.val right.val ≤ 2 ^ 31 - 1)
        (h_count' : count (contents nums') left.val right.val ≤ 2 ^ 31 - 1)
        (r r' : Std.I64)
        (hres : num_subarray_bounded_max nums left right = ok r)
        (hres' : num_subarray_bounded_max nums' left right = ok r'), r.val = r'.val) := by
    sorry

  end AegisSpec.NumSubarrayBoundedMax
