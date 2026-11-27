import Aegis.CountDifferentSubsequenceGcDs.Code.Funs

/-!
# Specifications of `Aegis.CountDifferentSubsequenceGcDs.count_different_subsequence_gc_ds`

LeetCode problem `number-of-different-subsequences-gcds`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountDifferentSubsequenceGcDs

  open Aegis.CountDifferentSubsequenceGcDs (count_different_subsequence_gc_ds)

  def gcdInt (a b : ℤ) : ℤ := (Int.gcd a b : ℤ)

  def IsGcdOfAll (l : List Std.I64) (g : ℤ) : Prop :=
    0 < g ∧ (∀ x ∈ l, g ∣ x.val) ∧ ∀ d : ℤ, 0 < d → (∀ x ∈ l, d ∣ x.val) → d ≤ g

  def subseqGcds (nums : Slice Std.I64) : Set ℤ :=
    { g : ℤ | ∃ l : List Std.I64, l.Sublist nums.val ∧ l ≠ [] ∧ IsGcdOfAll l g }

  def maxVal (nums : Slice Std.I64) : ℤ :=
    (nums.val.map (fun x => x.val)).foldr max 0

  def valueSet (nums : Slice Std.I64) : Set ℤ :=
    { v : ℤ | ∃ x ∈ nums.val, x.val = v }

  def divisorCover (nums : Slice Std.I64) : Set ℤ :=
    { d : ℤ | 0 < d ∧ ∃ x ∈ nums.val, d ∣ x.val }

  /-- Whenever the function returns a result r, r equals the number of elements of A(nums), where A(nums) is the set of all positive integers g for which there exists a non-empty set I of indices such that I is a subset of {0, ..., len(nums)-1} and g is the greatest positive integer dividing nums[i] for every i in I. The cardinality is interpreted as a mathematical integer and then as the returned 64-bit integer.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 200000) :
      ∀ r : Std.I64, count_different_subsequence_gc_ds nums = ok r →
        r.val = ((subseqGcds nums).ncard : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 200000), ∀ r : Std.I64, count_different_subsequence_gc_ds nums = ok r →
          r.val = ((subseqGcds nums).ncard : ℤ)) := by
    sorry

  /-- The function returns a result r and does not fail (no panic, no out-of-bounds access, and no arithmetic overflow) for every input satisfying the preconditions.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 200000) :
      ∃ r : Std.I64, count_different_subsequence_gc_ds nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 200000), ∃ r : Std.I64, count_different_subsequence_gc_ds nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= max{ nums[i] : 0 <= i < len(nums) }.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 200000) :
      ∀ r : Std.I64, count_different_subsequence_gc_ds nums = ok r →
        1 ≤ r.val ∧ r.val ≤ maxVal nums := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 200000), ∀ r : Std.I64, count_different_subsequence_gc_ds nums = ok r →
          1 ≤ r.val ∧ r.val ≤ maxVal nums) := by
    sorry

  /-- Whenever the function returns a result r, r >= |{ v : v is an integer and there exists i with 0 <= i < len(nums) and nums[i] = v }|.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 200000) :
      ∀ r : Std.I64, count_different_subsequence_gc_ds nums = ok r →
        ((valueSet nums).ncard : ℤ) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 200000), ∀ r : Std.I64, count_different_subsequence_gc_ds nums = ok r →
          ((valueSet nums).ncard : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= |{ d : d is a positive integer and there exists i with 0 <= i < len(nums) such that d divides nums[i] }|.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 200000) :
      ∀ r : Std.I64, count_different_subsequence_gc_ds nums = ok r →
        r.val ≤ ((divisorCover nums).ncard : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 200000), ∀ r : Std.I64, count_different_subsequence_gc_ds nums = ok r →
          r.val ≤ ((divisorCover nums).ncard : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if there exists an integer v such that nums[i] = v for every i with 0 <= i < len(nums).
    Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 200000) :
      ∀ r : Std.I64, count_different_subsequence_gc_ds nums = ok r →
        (r.val = 1 ↔ ∃ v : ℤ, ∀ x ∈ nums.val, x.val = v) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 200000), ∀ r : Std.I64, count_different_subsequence_gc_ds nums = ok r →
          (r.val = 1 ↔ ∃ v : ℤ, ∀ x ∈ nums.val, x.val = v)) := by
    sorry

  /-- If the function returns r on nums and returns r' on nums', then r = r'.
    Preconditions: len(nums) and len(nums') are each between 1 and 100000; every value of either slice is between 1 and 200000; and for every integer v, v occurs in nums if and only if v occurs in nums'. -/
  theorem spec_7 (nums nums' : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hlen_ge' : 1 ≤ nums'.val.length) (hlen_le' : nums'.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 200000)
      (hval' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 200000)
      (hsame : ∀ v : ℤ, (∃ x ∈ nums.val, x.val = v) ↔ (∃ x ∈ nums'.val, x.val = v)) :
      ∀ r r' : Std.I64, count_different_subsequence_gc_ds nums = ok r →
        count_different_subsequence_gc_ds nums' = ok r' → r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hlen_ge' : 1 ≤ nums'.val.length) (hlen_le' : nums'.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 200000)
        (hval' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 200000)
        (hsame : ∀ v : ℤ, (∃ x ∈ nums.val, x.val = v) ↔ (∃ x ∈ nums'.val, x.val = v)), ∀ r r' : Std.I64, count_different_subsequence_gc_ds nums = ok r →
          count_different_subsequence_gc_ds nums' = ok r' → r = r') := by
    sorry

  /-- Whenever the function returns a result r, the following hold: if nums[0] = nums[1] then r = 1; if nums[0] != nums[1] and either nums[0] divides nums[1] or nums[1] divides nums[0], then r = 2; and if nums[0] != nums[1] and neither divides the other, then r = 3.
    Preconditions: len(nums) = 2; 1 <= nums[0] <= 200000 and 1 <= nums[1] <= 200000. -/
  theorem spec_8 (nums : Slice Std.I64) (a b : Std.I64)
      (hvals : nums.val = [a, b])
      (ha_low : 1 ≤ a.val) (ha_high : a.val ≤ 200000)
      (hb_low : 1 ≤ b.val) (hb_high : b.val ≤ 200000) :
      ∀ r : Std.I64, count_different_subsequence_gc_ds nums = ok r →
        (a.val = b.val → r.val = 1) ∧
        (a.val ≠ b.val → (a.val ∣ b.val ∨ b.val ∣ a.val) → r.val = 2) ∧
        (a.val ≠ b.val → ¬ a.val ∣ b.val → ¬ b.val ∣ a.val → r.val = 3) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (a b : Std.I64)
        (hvals : nums.val = [a, b])
        (ha_low : 1 ≤ a.val) (ha_high : a.val ≤ 200000)
        (hb_low : 1 ≤ b.val) (hb_high : b.val ≤ 200000), ∀ r : Std.I64, count_different_subsequence_gc_ds nums = ok r →
          (a.val = b.val → r.val = 1) ∧
          (a.val ≠ b.val → (a.val ∣ b.val ∨ b.val ∣ a.val) → r.val = 2) ∧
          (a.val ≠ b.val → ¬ a.val ∣ b.val → ¬ b.val ∣ a.val → r.val = 3)) := by
    sorry

  end AegisSpec.CountDifferentSubsequenceGcDs
