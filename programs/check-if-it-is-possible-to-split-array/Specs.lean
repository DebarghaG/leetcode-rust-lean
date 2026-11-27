import Aegis.CanSplitArray.Code.Funs

/-!
# Specifications of `Aegis.CanSplitArray.can_split_array`

LeetCode problem `check-if-it-is-possible-to-split-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CanSplitArray

namespace AegisSpec.CanSplitArray

def InRange (l : List I64) (lo hi : ℤ) : Prop :=
  ∀ (i : ℕ) (h : i < l.length), lo ≤ (l[i]'h).val ∧ (l[i]'h).val ≤ hi

def AdjacentSumAtLeast (l : List I64) (m : I64) : Prop :=
  ∃ (i : ℕ) (h : i < l.length - 1),
    m.val ≤ (l[i]'(by omega)).val + (l[i+1]'(by omega)).val

def AdjacentSumsBelow (l : List I64) (m : I64) : Prop :=
  ∀ (i : ℕ) (h : i < l.length - 1),
    (l[i]'(by omega)).val + (l[i+1]'(by omega)).val < m.val

/-- Whenever can_split_array nums m returns a result r, r = true if and only if either n <= 2, or there exists an integer i with 0 <= i < n - 1 such that nums[i] + nums[i + 1] >= m.
  Preconditions: Let n = len(nums). 1 <= n <= 100; for every i with 0 <= i < n, 1 <= nums[i] <= 100; and 1 <= m <= 200. -/
theorem spec_1 (nums : Slice I64) (m : I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100)
    (h_nums : InRange nums.val 1 100)
    (h_m_lo : 1 ≤ m.val) (h_m_hi : m.val ≤ 200) :
    ∀ r, can_split_array nums m = ok r →
      (r = true ↔ nums.val.length ≤ 2 ∨ AdjacentSumAtLeast nums.val m) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (m : I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100)
    (h_nums : InRange nums.val 1 100)
    (h_m_lo : 1 ≤ m.val) (h_m_hi : m.val ≤ 200), ∀ r, can_split_array nums m = ok r →
      (r = true ↔ nums.val.length ≤ 2 ∨ AdjacentSumAtLeast nums.val m)) := by
  sorry

/-- The call can_split_array nums m returns a result r; it does not fail by panic, out-of-bounds indexing, or arithmetic overflow.
  Preconditions: Let n = len(nums). 1 <= n <= 100; for every i with 0 <= i < n, 1 <= nums[i] <= 100; and 1 <= m <= 200. -/
theorem spec_2 (nums : Slice I64) (m : I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100)
    (h_nums : InRange nums.val 1 100)
    (h_m_lo : 1 ≤ m.val) (h_m_hi : m.val ≤ 200) :
    ∃ r, can_split_array nums m = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (m : I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100)
    (h_nums : InRange nums.val 1 100)
    (h_m_lo : 1 ≤ m.val) (h_m_hi : m.val ≤ 200), ∃ r, can_split_array nums m = ok r) := by
  sorry

/-- Whenever can_split_array nums m returns a result r, r = true.
  Preconditions: Let n = len(nums). n = 1; 1 <= nums[0] <= 100; and 1 <= m <= 200. -/
theorem spec_3 (nums : Slice I64) (m : I64)
    (h_len : nums.val.length = 1)
    (h_nums0_lo : 1 ≤ (nums.val[0]'(by omega)).val)
    (h_nums0_hi : (nums.val[0]'(by omega)).val ≤ 100)
    (h_m_lo : 1 ≤ m.val) (h_m_hi : m.val ≤ 200) :
    ∀ r, can_split_array nums m = ok r → r = true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (m : I64)
    (h_len : nums.val.length = 1)
    (h_nums0_lo : 1 ≤ (nums.val[0]'(by omega)).val)
    (h_nums0_hi : (nums.val[0]'(by omega)).val ≤ 100)
    (h_m_lo : 1 ≤ m.val) (h_m_hi : m.val ≤ 200), ∀ r, can_split_array nums m = ok r → r = true) := by
  sorry

/-- Whenever can_split_array nums m returns a result r, r = false.
  Preconditions: Let n = len(nums). n >= 3; for every i with 0 <= i < n, 1 <= nums[i] <= 100; and 1 <= m <= 200. For every integer i with 0 <= i < n - 1, nums[i] + nums[i + 1] < m. -/
theorem spec_4 (nums : Slice I64) (m : I64)
    (h_len : 3 ≤ nums.val.length)
    (h_nums : InRange nums.val 1 100)
    (h_m_lo : 1 ≤ m.val) (h_m_hi : m.val ≤ 200)
    (h_adj : AdjacentSumsBelow nums.val m) :
    ∀ r, can_split_array nums m = ok r → r = false := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (m : I64)
    (h_len : 3 ≤ nums.val.length)
    (h_nums : InRange nums.val 1 100)
    (h_m_lo : 1 ≤ m.val) (h_m_hi : m.val ≤ 200)
    (h_adj : AdjacentSumsBelow nums.val m), ∀ r, can_split_array nums m = ok r → r = false) := by
  sorry

/-- Whenever can_split_array nums m1 returns r1 and can_split_array nums m2 returns r2, if r1 = true then r2 = true.
  Preconditions: Let n = len(nums). 1 <= n <= 100; for every i with 0 <= i < n, 1 <= nums[i] <= 100. Let m1 and m2 be integers with 1 <= m2 <= m1 <= 200. -/
theorem spec_5 (nums : Slice I64) (m1 m2 : I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100)
    (h_nums : InRange nums.val 1 100)
    (h_m2_lo : 1 ≤ m2.val) (h_m2_le_m1 : m2.val ≤ m1.val) (h_m1_hi : m1.val ≤ 200) :
    ∀ r1 r2, can_split_array nums m1 = ok r1 → can_split_array nums m2 = ok r2 →
      (r1 = true → r2 = true) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (m1 m2 : I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100)
    (h_nums : InRange nums.val 1 100)
    (h_m2_lo : 1 ≤ m2.val) (h_m2_le_m1 : m2.val ≤ m1.val) (h_m1_hi : m1.val ≤ 200), ∀ r1 r2, can_split_array nums m1 = ok r1 → can_split_array nums m2 = ok r2 →
      (r1 = true → r2 = true)) := by
  sorry

/-- Whenever can_split_array nums m returns r and can_split_array nums' m returns r', if r = true then r' = true.
  Preconditions: Let n = len(nums). 1 <= n <= 100; for every i with 0 <= i < n, 1 <= nums[i] <= 100. Let nums' be another slice of length n such that 1 <= nums'[i] <= 100 and nums[i] <= nums'[i] for every i with 0 <= i < n. Let 1 <= m <= 200. -/
theorem spec_6 (nums nums' : Slice I64) (m : I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100)
    (h_nums : InRange nums.val 1 100)
    (h_len' : nums'.val.length = nums.val.length)
    (h_nums' : InRange nums'.val 1 100)
    (h_le : ∀ (i : ℕ) (h : i < nums.val.length),
      (nums.val[i]'h).val ≤ (nums'.val[i]'(by omega)).val)
    (h_m_lo : 1 ≤ m.val) (h_m_hi : m.val ≤ 200) :
    ∀ r r', can_split_array nums m = ok r → can_split_array nums' m = ok r' →
      (r = true → r' = true) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums nums' : Slice I64) (m : I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100)
    (h_nums : InRange nums.val 1 100)
    (h_len' : nums'.val.length = nums.val.length)
    (h_nums' : InRange nums'.val 1 100)
    (h_le : ∀ (i : ℕ) (h : i < nums.val.length),
      (nums.val[i]'h).val ≤ (nums'.val[i]'(by omega)).val)
    (h_m_lo : 1 ≤ m.val) (h_m_hi : m.val ≤ 200), ∀ r r', can_split_array nums m = ok r → can_split_array nums' m = ok r' →
      (r = true → r' = true)) := by
  sorry

end AegisSpec.CanSplitArray
