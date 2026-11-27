import Aegis.IsArraySpecial.Code.Funs

/-!
# Specifications of `Aegis.IsArraySpecial.is_array_special`

LeetCode problem `special-array-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.IsArraySpecial (is_array_special)

namespace AegisSpec.IsArraySpecial

def SameParity (a b : ℤ) : Prop := a % 2 = b % 2

def OppParity (a b : ℤ) : Prop := ¬ SameParity a b

def AdjacentOppParity (l : List Std.I64) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < l.length), OppParity (l[i]).val (l[i + 1]).val

def AdjacentSameParity (l : List Std.I64) : Prop :=
  ∃ (i : ℕ) (h : i + 1 < l.length), SameParity (l[i]).val (l[i + 1]).val

def prefixSlice (nums : Slice Std.I64) (k : ℕ) : Slice Std.I64 :=
  Slice.from (nums.val.take k) (by
    have h := nums.property
    rw [List.length_take]
    exact le_trans (Nat.min_le_right _ _) h)

def suffixSlice (nums : Slice Std.I64) (k : ℕ) : Slice Std.I64 :=
  Slice.from (nums.val.drop (nums.val.length - k)) (by
    have h := nums.property
    rw [List.length_drop]
    exact le_trans (Nat.sub_le _ _) h)

def revSlice (nums : Slice Std.I64) : Slice Std.I64 :=
  Slice.from nums.val.reverse (by
    rw [List.length_reverse]
    exact nums.property)

/-- The function returns successfully with Boolean b, and b = true if and only if for every i with 0 <= i < len(nums) - 1, nums[i] and nums[i+1] have different parity (one is even and the other is odd). Equivalently, b = false if and only if there exists i with 0 <= i < len(nums) - 1 such that nums[i] and nums[i+1] have the same parity (both even or both odd).
  Preconditions: nums satisfies the problem constraints: 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_1 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ (i : ℕ) (h : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
    ∃ b, is_array_special nums = ok b ∧
      (b = true ↔ AdjacentOppParity nums.val) ∧
      (b = false ↔ AdjacentSameParity nums.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ (i : ℕ) (h : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∃ b, is_array_special nums = ok b ∧
      (b = true ↔ AdjacentOppParity nums.val) ∧
      (b = false ↔ AdjacentSameParity nums.val)) := by
  sorry

/-- The function returns successfully; it does not fail, panic, overflow, or go out of bounds.
  Preconditions: nums satisfies the problem constraints: 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
theorem spec_2 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ (i : ℕ) (h : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
    ∃ b, is_array_special nums = ok b := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ (i : ℕ) (h : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∃ b, is_array_special nums = ok b) := by
  sorry

/-- The function returns successfully with Boolean b on nums if and only if it returns successfully with the same Boolean b on nums'. In particular, replacing any element by another allowed value of the same parity does not change the result.
  Preconditions: nums and nums' each satisfy the problem constraints; len(nums') = len(nums); and for every i with 0 <= i < len(nums), nums[i] and nums'[i] have the same parity (both even or both odd). -/
theorem spec_3 (nums nums' : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ (i : ℕ) (h : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (h_len_pos' : 1 ≤ nums'.val.length) (h_len_le' : nums'.val.length ≤ 100)
    (h_range' : ∀ (i : ℕ) (h : i < nums'.val.length),
      1 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 100)
    (h_len_eq : nums'.val.length = nums.val.length)
    (h_parity : ∀ (i : ℕ) (h : i < nums.val.length),
      SameParity (nums.val[i]).val (nums'.val[i]).val) :
    ∀ b, is_array_special nums = ok b ↔ is_array_special nums' = ok b := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ (i : ℕ) (h : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (h_len_pos' : 1 ≤ nums'.val.length) (h_len_le' : nums'.val.length ≤ 100)
    (h_range' : ∀ (i : ℕ) (h : i < nums'.val.length),
      1 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 100)
    (h_len_eq : nums'.val.length = nums.val.length)
    (h_parity : ∀ (i : ℕ) (h : i < nums.val.length),
      SameParity (nums.val[i]).val (nums'.val[i]).val), ∀ b, is_array_special nums = ok b ↔ is_array_special nums' = ok b) := by
  sorry

/-- The function returns successfully with the same Boolean b on both nums and nums'; that is, flipping the parity of every element does not change whether the array is special.
  Preconditions: nums and nums' each satisfy the problem constraints; len(nums') = len(nums); and for every i with 0 <= i < len(nums), nums[i] and nums'[i] have opposite parity (one even and one odd). -/
theorem spec_4 (nums nums' : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ (i : ℕ) (h : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (h_len_pos' : 1 ≤ nums'.val.length) (h_len_le' : nums'.val.length ≤ 100)
    (h_range' : ∀ (i : ℕ) (h : i < nums'.val.length),
      1 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 100)
    (h_len_eq : nums'.val.length = nums.val.length)
    (h_parity : ∀ (i : ℕ) (h : i < nums.val.length),
      OppParity (nums.val[i]).val (nums'.val[i]).val) :
    ∃ b, is_array_special nums = ok b ∧ is_array_special nums' = ok b := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ (i : ℕ) (h : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (h_len_pos' : 1 ≤ nums'.val.length) (h_len_le' : nums'.val.length ≤ 100)
    (h_range' : ∀ (i : ℕ) (h : i < nums'.val.length),
      1 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 100)
    (h_len_eq : nums'.val.length = nums.val.length)
    (h_parity : ∀ (i : ℕ) (h : i < nums.val.length),
      OppParity (nums.val[i]).val (nums'.val[i]).val), ∃ b, is_array_special nums = ok b ∧ is_array_special nums' = ok b) := by
  sorry

/-- The function returns successfully with Boolean b on nums, and it returns successfully with the same Boolean b on rev.
  Preconditions: nums satisfies the problem constraints. Define rev to be the slice of length len(nums) whose i-th element is nums[len(nums) - 1 - i] for every i with 0 <= i < len(nums). -/
theorem spec_5 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ (i : ℕ) (h : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
    ∃ b, is_array_special nums = ok b ∧ is_array_special (revSlice nums) = ok b := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ (i : ℕ) (h : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∃ b, is_array_special nums = ok b ∧ is_array_special (revSlice nums) = ok b) := by
  sorry

/-- If the function returns successfully with Boolean b on nums and b = true, then for every k with 1 <= k <= len(nums), the function returns successfully with Boolean true on pre.
  Preconditions: nums satisfies the problem constraints. For any k with 1 <= k <= len(nums), let pre be the slice consisting of nums[0], nums[1], ..., nums[k-1]. -/
theorem spec_6 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ (i : ℕ) (h : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
    ∀ b, is_array_special nums = ok b → b = true →
      ∀ (k : ℕ) (hk_pos : 1 ≤ k) (hk_le : k ≤ nums.val.length),
        is_array_special (prefixSlice nums k) = ok true := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ (i : ℕ) (h : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∀ b, is_array_special nums = ok b → b = true →
      ∀ (k : ℕ) (hk_pos : 1 ≤ k) (hk_le : k ≤ nums.val.length),
        is_array_special (prefixSlice nums k) = ok true) := by
  sorry

/-- If the function returns successfully with Boolean b on nums and b = true, then for every k with 1 <= k <= len(nums), the function returns successfully with Boolean true on suf.
  Preconditions: nums satisfies the problem constraints. For any k with 1 <= k <= len(nums), let suf be the slice consisting of the last k elements of nums, namely nums[len(nums)-k], ..., nums[len(nums)-1]. -/
theorem spec_7 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ (i : ℕ) (h : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
    ∀ b, is_array_special nums = ok b → b = true →
      ∀ (k : ℕ) (hk_pos : 1 ≤ k) (hk_le : k ≤ nums.val.length),
        is_array_special (suffixSlice nums k) = ok true := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ (i : ℕ) (h : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∀ b, is_array_special nums = ok b → b = true →
      ∀ (k : ℕ) (hk_pos : 1 ≤ k) (hk_le : k ≤ nums.val.length),
        is_array_special (suffixSlice nums k) = ok true) := by
  sorry

end AegisSpec.IsArraySpecial
