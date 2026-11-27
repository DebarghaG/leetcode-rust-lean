import Aegis.FindMaxK.Code.Funs

/-!
# Specifications of `Aegis.FindMaxK.find_max_k`

LeetCode problem `largest-positive-integer-that-exists-with-its-negative`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindMaxK

def Occurs (nums : Slice Std.I64) (v : ℤ) : Prop :=
  ∃ i : ℕ, ∃ h : i < nums.val.length, (nums.val.get ⟨i, h⟩).val = v

def HasPair (nums : Slice Std.I64) (k : ℤ) : Prop :=
  Occurs nums k ∧ Occurs nums (-k)

def K (nums : Slice Std.I64) : Set ℤ := {k : ℤ | 0 < k ∧ HasPair nums k}

def ValidInput (nums : Slice Std.I64) : Prop :=
  1 ≤ nums.val.length ∧ nums.val.length ≤ 1000 ∧
    ∀ i : ℕ, ∀ h : i < nums.val.length,
      -1000 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 1000 ∧
        (nums.val.get ⟨i, h⟩).val ≠ 0

/-- The function returns a result r, and: let K be the set of positive integers k such that there exists i with 0 <= i < len(nums) and nums[i] = k, and there exists j with 0 <= j < len(nums) and nums[j] = -k. If K is nonempty, then r is an element of K and for every k in K, k <= r. If K is empty, then r = -1.
  Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000 and nums[i] != 0. -/
theorem spec_1 (nums : Slice Std.I64) (h : ValidInput nums) :
    ∃ r : Std.I64,
      Aegis.FindMaxK.find_max_k nums = ok r ∧
        ((K nums).Nonempty → r.val ∈ K nums ∧ ∀ k : ℤ, k ∈ K nums → k ≤ r.val) ∧
          (¬ (K nums).Nonempty → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums), ∃ r : Std.I64,
      Aegis.FindMaxK.find_max_k nums = ok r ∧
        ((K nums).Nonempty → r.val ∈ K nums ∧ ∀ k : ℤ, k ∈ K nums → k ≤ r.val) ∧
          (¬ (K nums).Nonempty → r.val = -1)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000 and nums[i] != 0. -/
theorem spec_2 (nums : Slice Std.I64) (h : ValidInput nums) :
    ∃ r : Std.I64, Aegis.FindMaxK.find_max_k nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums), ∃ r : Std.I64, Aegis.FindMaxK.find_max_k nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or (1 <= r and r <= 1000).
  Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000 and nums[i] != 0. -/
theorem spec_3 (nums : Slice Std.I64) (h : ValidInput nums) :
    ∀ r : Std.I64, Aegis.FindMaxK.find_max_k nums = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ 1000) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums), ∀ r : Std.I64, Aegis.FindMaxK.find_max_k nums = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ 1000)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exists an index i with 0 <= i < len(nums) such that nums[i] = r.
  Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000 and nums[i] != 0. -/
theorem spec_4 (nums : Slice Std.I64) (h : ValidInput nums) :
    ∀ r : Std.I64, Aegis.FindMaxK.find_max_k nums = ok r → r.val ≠ -1 →
      Occurs nums r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums), ∀ r : Std.I64, Aegis.FindMaxK.find_max_k nums = ok r → r.val ≠ -1 →
      Occurs nums r.val) := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exists an index j with 0 <= j < len(nums) such that nums[j] = -r.
  Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000 and nums[i] != 0. -/
theorem spec_5 (nums : Slice Std.I64) (h : ValidInput nums) :
    ∀ r : Std.I64, Aegis.FindMaxK.find_max_k nums = ok r → r.val ≠ -1 →
      Occurs nums (-r.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums), ∀ r : Std.I64, Aegis.FindMaxK.find_max_k nums = ok r → r.val ≠ -1 →
      Occurs nums (-r.val)) := by
  sorry

/-- Whenever the function returns a result r, if there exists an integer k with 0 < k, an index i with 0 <= i < len(nums) and nums[i] = k, and an index j with 0 <= j < len(nums) and nums[j] = -k, then r != -1.
  Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000 and nums[i] != 0. -/
theorem spec_6 (nums : Slice Std.I64) (h : ValidInput nums) :
    ∀ r : Std.I64, Aegis.FindMaxK.find_max_k nums = ok r →
      (∃ k : ℤ, 0 < k ∧ HasPair nums k) → r.val ≠ -1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums), ∀ r : Std.I64, Aegis.FindMaxK.find_max_k nums = ok r →
      (∃ k : ℤ, 0 < k ∧ HasPair nums k) → r.val ≠ -1) := by
  sorry

/-- Whenever the function returns a result r with r != -1, for every integer k with 0 < k, if there exists i with 0 <= i < len(nums) and nums[i] = k, and there exists j with 0 <= j < len(nums) and nums[j] = -k, then k <= r.
  Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000 and nums[i] != 0. -/
theorem spec_7 (nums : Slice Std.I64) (h : ValidInput nums) :
    ∀ r : Std.I64, Aegis.FindMaxK.find_max_k nums = ok r → r.val ≠ -1 →
      ∀ k : ℤ, 0 < k → HasPair nums k → k ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums), ∀ r : Std.I64, Aegis.FindMaxK.find_max_k nums = ok r → r.val ≠ -1 →
      ∀ k : ℤ, 0 < k → HasPair nums k → k ≤ r.val) := by
  sorry

/-- The function returns a result r for nums and a result r' for nums', and r = r'.
  Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000 and nums[i] != 0; nums' is a slice with len(nums') >= 1 and len(nums') <= 1000; for every i with 0 <= i < len(nums'), -1000 <= nums'[i] <= 1000 and nums'[i] != 0; and for every integer v, v occurs in nums if and only if v occurs in nums'. -/
theorem spec_8 (nums nums' : Slice Std.I64) (h : ValidInput nums) (h' : ValidInput nums')
    (hsame : ∀ v : ℤ, Occurs nums v ↔ Occurs nums' v) :
    ∃ r r' : Std.I64,
      Aegis.FindMaxK.find_max_k nums = ok r ∧ Aegis.FindMaxK.find_max_k nums' = ok r' ∧
        r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (h : ValidInput nums) (h' : ValidInput nums')
    (hsame : ∀ v : ℤ, Occurs nums v ↔ Occurs nums' v), ∃ r r' : Std.I64,
      Aegis.FindMaxK.find_max_k nums = ok r ∧ Aegis.FindMaxK.find_max_k nums' = ok r' ∧
        r = r') := by
  sorry

end AegisSpec.FindMaxK
