import Aegis.ContainsDuplicate.Code.Funs

/-!
# Specifications of `Aegis.ContainsDuplicate.contains_duplicate`

LeetCode problem `contains-duplicate`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ContainsDuplicate

def elem (nums : Slice Std.I64) (t : ℕ) : ℤ := (nums.val[t]!).val

theorem elem_eq (nums : Slice Std.I64) (t : ℕ) (h : t < nums.val.length) :
    elem nums t = (nums.val[t]).val := by
  simp only [elem, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h,
    Option.getD_some]

/-- The function returns a result r (r : Bool) such that r = true if and only if there exist indices i and j with 0 <= i < j < len(nums) and nums[i] = nums[j]. Equivalently, r = false if and only if for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j].
  Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elem nums i ∧ elem nums i ≤ 1000000000) :
    ∃ r, Aegis.ContainsDuplicate.contains_duplicate nums = ok r ∧
      (r = true ↔ ∃ i j, i < j ∧ j < nums.val.length ∧ elem nums i = elem nums j) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elem nums i ∧ elem nums i ≤ 1000000000), ∃ r, Aegis.ContainsDuplicate.contains_duplicate nums = ok r ∧
      (r = true ↔ ∃ i j, i < j ∧ j < nums.val.length ∧ elem nums i = elem nums j)) := by
  sorry

/-- The function returns a result r; in particular it does not fail (no panic, out-of-bounds access, or arithmetic overflow) on any input satisfying the preconditions.
  Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elem nums i ∧ elem nums i ≤ 1000000000) :
    ∃ r, Aegis.ContainsDuplicate.contains_duplicate nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elem nums i ∧ elem nums i ≤ 1000000000), ∃ r, Aegis.ContainsDuplicate.contains_duplicate nums = ok r) := by
  sorry

/-- If contains_duplicate(nums) returns a result r and contains_duplicate(nums') returns a result r', then r = r'.
  Preconditions: nums and nums' are slices of i64, each with length between 1 and 100000 and all entries between -1000000000 and 1000000000; len(nums) = len(nums'); and there exists a bijection pi from {0,...,len(nums)-1} to itself such that nums'[k] = nums[pi(k)] for every k with 0 <= k < len(nums). -/
theorem spec_3 (nums nums' : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (h_len'_ge : 1 ≤ nums'.val.length) (h_len'_le : nums'.val.length ≤ 100000)
    (h_bounds' : ∀ i, i < nums'.val.length →
      -1000000000 ≤ elem nums' i ∧ elem nums' i ≤ 1000000000)
    (h_len_eq : nums.val.length = nums'.val.length)
    (h_perm : ∃ pi : Fin nums.val.length ≃ Fin nums.val.length,
      ∀ k : Fin nums.val.length, elem nums' k.val = elem nums (pi k).val) :
    ∀ r r', Aegis.ContainsDuplicate.contains_duplicate nums = ok r →
      Aegis.ContainsDuplicate.contains_duplicate nums' = ok r' → r = r' := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (h_len'_ge : 1 ≤ nums'.val.length) (h_len'_le : nums'.val.length ≤ 100000)
    (h_bounds' : ∀ i, i < nums'.val.length →
      -1000000000 ≤ elem nums' i ∧ elem nums' i ≤ 1000000000)
    (h_len_eq : nums.val.length = nums'.val.length)
    (h_perm : ∃ pi : Fin nums.val.length ≃ Fin nums.val.length,
      ∀ k : Fin nums.val.length, elem nums' k.val = elem nums (pi k).val), ∀ r r', Aegis.ContainsDuplicate.contains_duplicate nums = ok r →
      Aegis.ContainsDuplicate.contains_duplicate nums' = ok r' → r = r') := by
  sorry

/-- If contains_duplicate(nums) returns a result r with r = true, then contains_duplicate(nums') returns a result r' with r' = true.
  Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 99999 and all entries between -1000000000 and 1000000000; x is an i64 with -1000000000 <= x <= 1000000000; nums' is a slice of length len(nums)+1 such that nums'[i] = nums[i] for every i with 0 <= i < len(nums) and nums'[len(nums)] = x. -/
theorem spec_4 (nums nums' : Slice Std.I64) (x : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 99999)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (h_x_ge : -1000000000 ≤ x.val) (h_x_le : x.val ≤ 1000000000)
    (h_len' : nums'.val.length = nums.val.length + 1)
    (h_prefix : ∀ i, i < nums.val.length → elem nums' i = elem nums i)
    (h_last : elem nums' nums.val.length = x.val) :
    ∀ r, Aegis.ContainsDuplicate.contains_duplicate nums = ok r → r = true →
      ∃ r', Aegis.ContainsDuplicate.contains_duplicate nums' = ok r' ∧ r' = true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (x : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 99999)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (h_x_ge : -1000000000 ≤ x.val) (h_x_le : x.val ≤ 1000000000)
    (h_len' : nums'.val.length = nums.val.length + 1)
    (h_prefix : ∀ i, i < nums.val.length → elem nums' i = elem nums i)
    (h_last : elem nums' nums.val.length = x.val), ∀ r, Aegis.ContainsDuplicate.contains_duplicate nums = ok r → r = true →
      ∃ r', Aegis.ContainsDuplicate.contains_duplicate nums' = ok r' ∧ r' = true) := by
  sorry

/-- If contains_duplicate(sub) returns a result r with r = true, then contains_duplicate(nums) returns a result r' with r' = true.
  Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 100000 and all entries between -1000000000 and 1000000000; sub is a slice of i64 with 1 <= len(sub); and there exist integers k and m with 0 <= k, 0 <= m, k + m <= len(nums), m = len(sub), and for every t with 0 <= t < m, sub[t] = nums[k + t]. -/
theorem spec_5 (nums sub : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (h_sub_len_ge : 1 ≤ sub.val.length)
    (h_seg : ∃ k m : ℕ, k + m ≤ nums.val.length ∧ m = sub.val.length ∧
      ∀ t, t < m → elem sub t = elem nums (k + t)) :
    ∀ r, Aegis.ContainsDuplicate.contains_duplicate sub = ok r → r = true →
      ∃ r', Aegis.ContainsDuplicate.contains_duplicate nums = ok r' ∧ r' = true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums sub : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (h_sub_len_ge : 1 ≤ sub.val.length)
    (h_seg : ∃ k m : ℕ, k + m ≤ nums.val.length ∧ m = sub.val.length ∧
      ∀ t, t < m → elem sub t = elem nums (k + t)), ∀ r, Aegis.ContainsDuplicate.contains_duplicate sub = ok r → r = true →
      ∃ r', Aegis.ContainsDuplicate.contains_duplicate nums = ok r' ∧ r' = true) := by
  sorry

/-- If contains_duplicate(nums) returns a result r with r = false, then contains_duplicate(sub) returns a result r' with r' = false.
  Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 100000 and all entries between -1000000000 and 1000000000; sub is a slice of i64 with 1 <= len(sub); and there exist integers k and m with 0 <= k, 0 <= m, k + m <= len(nums), m = len(sub), and for every t with 0 <= t < m, sub[t] = nums[k + t]. -/
theorem spec_6 (nums sub : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (h_sub_len_ge : 1 ≤ sub.val.length)
    (h_seg : ∃ k m : ℕ, k + m ≤ nums.val.length ∧ m = sub.val.length ∧
      ∀ t, t < m → elem sub t = elem nums (k + t)) :
    ∀ r, Aegis.ContainsDuplicate.contains_duplicate nums = ok r → r = false →
      ∃ r', Aegis.ContainsDuplicate.contains_duplicate sub = ok r' ∧ r' = false := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums sub : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (h_sub_len_ge : 1 ≤ sub.val.length)
    (h_seg : ∃ k m : ℕ, k + m ≤ nums.val.length ∧ m = sub.val.length ∧
      ∀ t, t < m → elem sub t = elem nums (k + t)), ∀ r, Aegis.ContainsDuplicate.contains_duplicate nums = ok r → r = false →
      ∃ r', Aegis.ContainsDuplicate.contains_duplicate sub = ok r' ∧ r' = false) := by
  sorry

/-- If contains_duplicate(nums) returns a result r with r = false, then contains_duplicate(nums') returns a result r' with r' = false.
  Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 99999 and all entries between -1000000000 and 1000000000; x is an i64 with -1000000000 <= x <= 1000000000; nums' is a slice of length len(nums)+1 such that nums'[i] = nums[i] for every i with 0 <= i < len(nums) and nums'[len(nums)] = x; and, for every i with 0 <= i < len(nums), nums[i] != x. -/
theorem spec_7 (nums nums' : Slice Std.I64) (x : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 99999)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (h_x_ge : -1000000000 ≤ x.val) (h_x_le : x.val ≤ 1000000000)
    (h_len' : nums'.val.length = nums.val.length + 1)
    (h_prefix : ∀ i, i < nums.val.length → elem nums' i = elem nums i)
    (h_last : elem nums' nums.val.length = x.val)
    (h_no_mem : ∀ i, i < nums.val.length → elem nums i ≠ x.val) :
    ∀ r, Aegis.ContainsDuplicate.contains_duplicate nums = ok r → r = false →
      ∃ r', Aegis.ContainsDuplicate.contains_duplicate nums' = ok r' ∧ r' = false := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (x : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 99999)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (h_x_ge : -1000000000 ≤ x.val) (h_x_le : x.val ≤ 1000000000)
    (h_len' : nums'.val.length = nums.val.length + 1)
    (h_prefix : ∀ i, i < nums.val.length → elem nums' i = elem nums i)
    (h_last : elem nums' nums.val.length = x.val)
    (h_no_mem : ∀ i, i < nums.val.length → elem nums i ≠ x.val), ∀ r, Aegis.ContainsDuplicate.contains_duplicate nums = ok r → r = false →
      ∃ r', Aegis.ContainsDuplicate.contains_duplicate nums' = ok r' ∧ r' = false) := by
  sorry

end AegisSpec.ContainsDuplicate
