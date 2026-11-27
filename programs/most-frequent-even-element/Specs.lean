import Aegis.MostFrequentEven.Code.Funs

/-!
# Specifications of `Aegis.MostFrequentEven.most_frequent_even`

LeetCode problem `most-frequent-even-element`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MostFrequentEven

def occ (l : List (Std.I64)) (v : ℤ) : ℕ :=
  (l.filter (fun x => x.val = v)).length

def Bounds (l : List (Std.I64)) : Prop :=
  ∀ (i : ℕ) (hi : i < l.length), 0 ≤ (l[i]'hi).val ∧ (l[i]'hi).val ≤ 100000

/-- For an integer v, let occ(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. The function returns a result r and satisfies: if there exists an index i with 0 <= i < len(nums) such that nums[i] is even (divisible by 2), then r is even, occ(r) > 0, and for every index j with 0 <= j < len(nums) such that nums[j] is even, either occ(nums[j]) < occ(r), or occ(nums[j]) = occ(r) and r <= nums[j]; if no index i with 0 <= i < len(nums) has nums[i] even, then r = -1.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 2000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000. -/
theorem spec_1 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val) :
    ∃ r : Std.I64,
      Aegis.MostFrequentEven.most_frequent_even nums = ok r ∧
      ((∃ (i : ℕ) (hi : i < nums.val.length), Even (nums.val[i]'hi).val) →
        Even r.val ∧ 0 < occ nums.val r.val ∧
          (∀ (j : ℕ) (hj : j < nums.val.length), Even (nums.val[j]'hj).val →
            occ nums.val (nums.val[j]'hj).val < occ nums.val r.val ∨
            (occ nums.val (nums.val[j]'hj).val = occ nums.val r.val ∧
              r.val ≤ (nums.val[j]'hj).val))) ∧
      ((¬ ∃ (i : ℕ) (hi : i < nums.val.length), Even (nums.val[i]'hi).val) →
        r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val), ∃ r : Std.I64,
      Aegis.MostFrequentEven.most_frequent_even nums = ok r ∧
      ((∃ (i : ℕ) (hi : i < nums.val.length), Even (nums.val[i]'hi).val) →
        Even r.val ∧ 0 < occ nums.val r.val ∧
          (∀ (j : ℕ) (hj : j < nums.val.length), Even (nums.val[j]'hj).val →
            occ nums.val (nums.val[j]'hj).val < occ nums.val r.val ∨
            (occ nums.val (nums.val[j]'hj).val = occ nums.val r.val ∧
              r.val ≤ (nums.val[j]'hj).val))) ∧
      ((¬ ∃ (i : ℕ) (hi : i < nums.val.length), Even (nums.val[i]'hi).val) →
        r.val = -1)) := by
  sorry

/-- The function returns a result r; in particular, it does not fail, panic, or overflow on any input satisfying the preconditions.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 2000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000. -/
theorem spec_2 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val) :
    ∃ r : Std.I64, Aegis.MostFrequentEven.most_frequent_even nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val), ∃ r : Std.I64, Aegis.MostFrequentEven.most_frequent_even nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 0 <= r <= 100000.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 2000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000. -/
theorem spec_3 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val) :
    ∀ r : Std.I64,
      Aegis.MostFrequentEven.most_frequent_even nums = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ 100000) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val), ∀ r : Std.I64,
      Aegis.MostFrequentEven.most_frequent_even nums = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ 100000)) := by
  sorry

/-- Whenever the function returns a result r and r != -1, r is even (divisible by 2).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 2000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000. -/
theorem spec_4 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val) :
    ∀ r : Std.I64,
      Aegis.MostFrequentEven.most_frequent_even nums = ok r →
      r.val ≠ -1 → Even r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val), ∀ r : Std.I64,
      Aegis.MostFrequentEven.most_frequent_even nums = ok r →
      r.val ≠ -1 → Even r.val) := by
  sorry

/-- Whenever the function returns a result r and r != -1, there exists an index i with 0 <= i < len(nums) such that nums[i] = r.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 2000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000. -/
theorem spec_5 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val) :
    ∀ r : Std.I64,
      Aegis.MostFrequentEven.most_frequent_even nums = ok r →
      r.val ≠ -1 → ∃ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]'hi).val = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val), ∀ r : Std.I64,
      Aegis.MostFrequentEven.most_frequent_even nums = ok r →
      r.val ≠ -1 → ∃ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]'hi).val = r.val) := by
  sorry

/-- For an integer v, let occ(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. Whenever the function returns a result r and r != -1, for every index j with 0 <= j < len(nums) such that nums[j] is even, occ(nums[j]) <= occ(r).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 2000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000. -/
theorem spec_6 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val) :
    ∀ r : Std.I64,
      Aegis.MostFrequentEven.most_frequent_even nums = ok r →
      r.val ≠ -1 →
      ∀ (j : ℕ) (hj : j < nums.val.length), Even (nums.val[j]'hj).val →
        occ nums.val (nums.val[j]'hj).val ≤ occ nums.val r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val), ∀ r : Std.I64,
      Aegis.MostFrequentEven.most_frequent_even nums = ok r →
      r.val ≠ -1 →
      ∀ (j : ℕ) (hj : j < nums.val.length), Even (nums.val[j]'hj).val →
        occ nums.val (nums.val[j]'hj).val ≤ occ nums.val r.val) := by
  sorry

/-- For an integer v, let occ(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. Whenever the function returns a result r and r != -1, for every index j with 0 <= j < len(nums) such that nums[j] is even, if occ(nums[j]) = occ(r) then r <= nums[j].
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 2000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000. -/
theorem spec_7 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val) :
    ∀ r : Std.I64,
      Aegis.MostFrequentEven.most_frequent_even nums = ok r →
      r.val ≠ -1 →
      ∀ (j : ℕ) (hj : j < nums.val.length), Even (nums.val[j]'hj).val →
        occ nums.val (nums.val[j]'hj).val = occ nums.val r.val →
          r.val ≤ (nums.val[j]'hj).val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val), ∀ r : Std.I64,
      Aegis.MostFrequentEven.most_frequent_even nums = ok r →
      r.val ≠ -1 →
      ∀ (j : ℕ) (hj : j < nums.val.length), Even (nums.val[j]'hj).val →
        occ nums.val (nums.val[j]'hj).val = occ nums.val r.val →
          r.val ≤ (nums.val[j]'hj).val) := by
  sorry

/-- Whenever the function returns a result r and r = -1, for every index i with 0 <= i < len(nums), nums[i] is odd (not divisible by 2).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 2000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000. -/
theorem spec_8 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val) :
    ∀ r : Std.I64,
      Aegis.MostFrequentEven.most_frequent_even nums = ok r →
      r.val = -1 → ∀ (i : ℕ) (hi : i < nums.val.length), ¬ Even (nums.val[i]'hi).val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val), ∀ r : Std.I64,
      Aegis.MostFrequentEven.most_frequent_even nums = ok r →
      r.val = -1 → ∀ (i : ℕ) (hi : i < nums.val.length), ¬ Even (nums.val[i]'hi).val) := by
  sorry

/-- For an integer v, let occ(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. Whenever the function returns a result r and r != -1, for every even integer v with v < r, occ(v) < occ(r).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 2000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000. -/
theorem spec_9 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val) :
    ∀ r : Std.I64,
      Aegis.MostFrequentEven.most_frequent_even nums = ok r →
      r.val ≠ -1 →
      ∀ v : ℤ, Even v → v < r.val → occ nums.val v < occ nums.val r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val), ∀ r : Std.I64,
      Aegis.MostFrequentEven.most_frequent_even nums = ok r →
      r.val ≠ -1 →
      ∀ v : ℤ, Even v → v < r.val → occ nums.val v < occ nums.val r.val) := by
  sorry

/-- For an even integer v, let occ(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v, and let occ2(v) be the number of indices i with 0 <= i < len(nums2) and nums2[i] = v. Whenever the function returns r on input nums and r2 on input nums2, if occ(v) = occ2(v) for every even integer v, then r = r2.
  Preconditions: nums and nums2 are slices of 64-bit integers, each with length between 1 and 2000 inclusive, and every element of each slice is between 0 and 100000 inclusive. -/
theorem spec_10 (nums nums2 : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val)
    (h_len_pos2 : 1 ≤ nums2.val.length) (h_len_le2 : nums2.val.length ≤ 2000)
    (h_bounds2 : Bounds nums2.val) :
    ∀ (r r2 : Std.I64),
      Aegis.MostFrequentEven.most_frequent_even nums = ok r →
      Aegis.MostFrequentEven.most_frequent_even nums2 = ok r2 →
      (∀ v : ℤ, Even v → occ nums.val v = occ nums2.val v) → r = r2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 2000)
    (h_bounds : Bounds nums.val)
    (h_len_pos2 : 1 ≤ nums2.val.length) (h_len_le2 : nums2.val.length ≤ 2000)
    (h_bounds2 : Bounds nums2.val), ∀ (r r2 : Std.I64),
      Aegis.MostFrequentEven.most_frequent_even nums = ok r →
      Aegis.MostFrequentEven.most_frequent_even nums2 = ok r2 →
      (∀ v : ℤ, Even v → occ nums.val v = occ nums2.val v) → r = r2) := by
  sorry

end AegisSpec.MostFrequentEven
