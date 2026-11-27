import Aegis.AverageValue.Code.Funs

/-!
# Specifications of `Aegis.AverageValue.average_value`

LeetCode problem `average-value-of-even-numbers-that-are-divisible-by-three`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.AverageValue

def Qualifies (x : Std.I64) : Prop := x.val % 2 = 0 ∧ x.val % 3 = 0

instance instDecidableQualifies (x : Std.I64) : Decidable (Qualifies x) := by
  unfold Qualifies
  infer_instance

def qualifyingList (nums : Slice Std.I64) : List Std.I64 :=
  nums.val.filter (fun x => decide (Qualifies x))

def qualifyingCount (nums : Slice Std.I64) : Nat :=
  (qualifyingList nums).length

def qualifyingSum (nums : Slice Std.I64) : Int :=
  ((qualifyingList nums).map (fun x => x.val)).sum

def totalSum (nums : Slice Std.I64) : Int :=
  (nums.val.map (fun x => x.val)).sum

/-- The function returns a result r and does not fail. Let C be the number of indices i with 0 <= i < len(nums) such that nums[i] is even and divisible by 3, and let S be the sum of nums[i] over exactly those indices. If C = 0 then r = 0. If C > 0 then r = floor(S / C), i.e. the greatest integer not exceeding the exact average of those C values.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 1000, and for every integer i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      (qualifyingCount nums = 0 → r.val = 0) ∧
      (0 < qualifyingCount nums →
        r.val = qualifyingSum nums / (qualifyingCount nums : Int)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000), ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      (qualifyingCount nums = 0 → r.val = 0) ∧
      (0 < qualifyingCount nums →
        r.val = qualifyingSum nums / (qualifyingCount nums : Int))) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r and does not fail (no panic, out-of-bounds access, or arithmetic overflow).
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 1000, and for every integer i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000) :
    ∃ r : Std.I64, Aegis.AverageValue.average_value nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000), ∃ r : Std.I64, Aegis.AverageValue.average_value nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= 1000.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 1000, and for every integer i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000) :
    ∀ r : Std.I64, Aegis.AverageValue.average_value nums = ok r →
      0 ≤ r.val ∧ r.val ≤ 1000 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000), ∀ r : Std.I64, Aegis.AverageValue.average_value nums = ok r →
      0 ≤ r.val ∧ r.val ≤ 1000) := by
  sorry

/-- The function returns a result r and r = 0 if and only if there is no index i with 0 <= i < len(nums) such that nums[i] is even and divisible by 3.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 1000, and for every integer i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      (r.val = 0 ↔ qualifyingCount nums = 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000), ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      (r.val = 0 ↔ qualifyingCount nums = 0)) := by
  sorry

/-- Whenever the function returns a result r, either r = 0 or r >= 6; equivalently, r is never an integer from 1 through 5.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 1000, and for every integer i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000) :
    ∀ r : Std.I64, Aegis.AverageValue.average_value nums = ok r →
      r.val = 0 ∨ 6 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000), ∀ r : Std.I64, Aegis.AverageValue.average_value nums = ok r →
      r.val = 0 ∨ 6 ≤ r.val) := by
  sorry

/-- Let C be the number of indices i with 0 <= i < len(nums) such that nums[i] is even and divisible by 3. If C > 0, let m be the minimum and M the maximum of the set { nums[i] | 0 <= i < len(nums), nums[i] is even and divisible by 3 }. Then the function returns a result r and m <= r <= M.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 1000, and for every integer i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000)
    (hC : 0 < qualifyingCount nums) (m M : Int)
    (hm_lb : ∀ x ∈ qualifyingList nums, m ≤ x.val)
    (hm_attained : ∃ x ∈ qualifyingList nums, x.val = m)
    (hM_ub : ∀ x ∈ qualifyingList nums, x.val ≤ M)
    (hM_attained : ∃ x ∈ qualifyingList nums, x.val = M) :
    ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧ m ≤ r.val ∧ r.val ≤ M := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000)
    (hC : 0 < qualifyingCount nums) (m M : Int)
    (hm_lb : ∀ x ∈ qualifyingList nums, m ≤ x.val)
    (hm_attained : ∃ x ∈ qualifyingList nums, x.val = m)
    (hM_ub : ∀ x ∈ qualifyingList nums, x.val ≤ M)
    (hM_attained : ∃ x ∈ qualifyingList nums, x.val = M), ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧ m ≤ r.val ∧ r.val ≤ M) := by
  sorry

/-- Let C be the number of indices i with 0 <= i < len(nums) such that nums[i] is even and divisible by 3, and let S be the sum of nums[i] over exactly those indices. If C > 0, the function returns a result r and there exists an integer t with 0 <= t < C such that S = r*C + t.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 1000, and for every integer i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000)
    (hC : 0 < qualifyingCount nums) :
    ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      ∃ t : Int,
        0 ≤ t ∧ t < (qualifyingCount nums : Int) ∧
          qualifyingSum nums = r.val * (qualifyingCount nums : Int) + t := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000)
    (hC : 0 < qualifyingCount nums), ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      ∃ t : Int,
        0 ≤ t ∧ t < (qualifyingCount nums : Int) ∧
          qualifyingSum nums = r.val * (qualifyingCount nums : Int) + t) := by
  sorry

/-- Let r be the result of the function on nums. For every slice nums' that is a permutation (reordering) of nums, the function returns a result r' on nums' and r' = r.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 1000, and for every integer i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      ∀ (nums' : Slice Std.I64), nums'.val.Perm nums.val →
        ∃ r' : Std.I64, Aegis.AverageValue.average_value nums' = ok r' ∧ r' = r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000), ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      ∀ (nums' : Slice Std.I64), nums'.val.Perm nums.val →
        ∃ r' : Std.I64, Aegis.AverageValue.average_value nums' = ok r' ∧ r' = r) := by
  sorry

/-- For every index j with 0 <= j < len(nums) such that nums[j] is not even or not divisible by 3, let nums' be the slice obtained from nums by deleting the entry at index j. Then the function returns results r on nums and r' on nums', and r' = r.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 1000, for every integer i with 0 <= i < len(nums), 1 <= nums[i] <= 1000, and len(nums) >= 2. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000)
    (hlen_two : 2 ≤ nums.val.length) :
    ∀ (j : Fin nums.val.length), ¬ Qualifies (nums.val.get j) →
      ∀ (nums' : Slice Std.I64), nums'.val = nums.val.eraseIdx j.1 →
        ∃ r : Std.I64, ∃ r' : Std.I64,
          Aegis.AverageValue.average_value nums = ok r ∧
          Aegis.AverageValue.average_value nums' = ok r' ∧ r'.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000)
    (hlen_two : 2 ≤ nums.val.length), ∀ (j : Fin nums.val.length), ¬ Qualifies (nums.val.get j) →
      ∀ (nums' : Slice Std.I64), nums'.val = nums.val.eraseIdx j.1 →
        ∃ r : Std.I64, ∃ r' : Std.I64,
          Aegis.AverageValue.average_value nums = ok r ∧
          Aegis.AverageValue.average_value nums' = ok r' ∧ r'.val = r.val) := by
  sorry

/-- The function returns a result r and r = floor((sum of all nums[i] for 0 <= i < len(nums)) / len(nums)).
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 1000, for every integer i with 0 <= i < len(nums), 1 <= nums[i] <= 1000, and for every integer i with 0 <= i < len(nums), nums[i] is even and divisible by 3. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000)
    (hall : ∀ (i : Fin nums.val.length), Qualifies (nums.val.get i)) :
    ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      r.val = totalSum nums / (nums.val.length : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000)
    (hall : ∀ (i : Fin nums.val.length), Qualifies (nums.val.get i)), ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      r.val = totalSum nums / (nums.val.length : Int)) := by
  sorry

/-- The function returns a result r and r = nums[j], where j is that unique qualifying index.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 1000, for every integer i with 0 <= i < len(nums), 1 <= nums[i] <= 1000, and there is exactly one index j with 0 <= j < len(nums) such that nums[j] is even and divisible by 3. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000)
    (huniq : ∃ (j : Fin nums.val.length),
      Qualifies (nums.val.get j) ∧
        ∀ (k : Fin nums.val.length), Qualifies (nums.val.get k) → k = j) :
    ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      ∀ (j : Fin nums.val.length), Qualifies (nums.val.get j) →
        r.val = (nums.val.get j).val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000)
    (huniq : ∃ (j : Fin nums.val.length),
      Qualifies (nums.val.get j) ∧
        ∀ (k : Fin nums.val.length), Qualifies (nums.val.get k) → k = j), ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      ∀ (j : Fin nums.val.length), Qualifies (nums.val.get j) →
        r.val = (nums.val.get j).val) := by
  sorry

/-- The function returns a result r and there exists an index i with 0 <= i < len(nums) such that nums[i] is even and divisible by 3 and nums[i] >= r.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 1000, for every integer i with 0 <= i < len(nums), 1 <= nums[i] <= 1000, and there exists an index i with 0 <= i < len(nums) such that nums[i] is even and divisible by 3. -/
theorem spec_12 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000)
    (hex : ∃ (i : Fin nums.val.length), Qualifies (nums.val.get i)) :
    ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      ∃ (i : Fin nums.val.length), Qualifies (nums.val.get i) ∧ r.val ≤ (nums.val.get i).val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000)
    (hex : ∃ (i : Fin nums.val.length), Qualifies (nums.val.get i)), ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      ∃ (i : Fin nums.val.length), Qualifies (nums.val.get i) ∧ r.val ≤ (nums.val.get i).val) := by
  sorry

/-- The function returns a result r and there exists an index j with 0 <= j < len(nums) such that nums[j] is even and divisible by 3 and nums[j] <= r.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 1000, for every integer i with 0 <= i < len(nums), 1 <= nums[i] <= 1000, and there exists an index i with 0 <= i < len(nums) such that nums[i] is even and divisible by 3. -/
theorem spec_13 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000)
    (hex : ∃ (i : Fin nums.val.length), Qualifies (nums.val.get i)) :
    ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      ∃ (j : Fin nums.val.length), Qualifies (nums.val.get j) ∧ (nums.val.get j).val ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000)
    (hex : ∃ (i : Fin nums.val.length), Qualifies (nums.val.get i)), ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      ∃ (j : Fin nums.val.length), Qualifies (nums.val.get j) ∧ (nums.val.get j).val ≤ r.val) := by
  sorry

/-- The function returns a result r and: if nums[0] is even and divisible by 3 then r = nums[0]; otherwise r = 0.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 1000, for every integer i with 0 <= i < len(nums), 1 <= nums[i] <= 1000, and len(nums) = 1. -/
theorem spec_14 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000)
    (hlen_one : nums.val.length = 1) :
    ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      (Qualifies (nums.val.get ⟨0, by omega⟩) →
        r.val = (nums.val.get ⟨0, by omega⟩).val) ∧
      (¬ Qualifies (nums.val.get ⟨0, by omega⟩) → r.val = 0) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000)
    (hlen_one : nums.val.length = 1), ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      (Qualifies (nums.val.get ⟨0, by omega⟩) →
        r.val = (nums.val.get ⟨0, by omega⟩).val) ∧
      (¬ Qualifies (nums.val.get ⟨0, by omega⟩) → r.val = 0)) := by
  sorry

/-- The function returns a result r and r = v.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 1000, for every integer i with 0 <= i < len(nums), 1 <= nums[i] <= 1000, there exists at least one index i with 0 <= i < len(nums) such that nums[i] is even and divisible by 3, and there exists an integer v such that for every index i with 0 <= i < len(nums) satisfying that nums[i] is even and divisible by 3, nums[i] = v. -/
theorem spec_15 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000)
    (hex : ∃ (i : Fin nums.val.length), Qualifies (nums.val.get i))
    (hv : ∃ v : Int,
      ∀ (i : Fin nums.val.length), Qualifies (nums.val.get i) → (nums.val.get i).val = v) :
    ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      ∀ v : Int,
        (∀ (i : Fin nums.val.length), Qualifies (nums.val.get i) → (nums.val.get i).val = v) →
          r.val = v := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hrange : ∀ (i : Fin nums.val.length),
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000)
    (hex : ∃ (i : Fin nums.val.length), Qualifies (nums.val.get i))
    (hv : ∃ v : Int,
      ∀ (i : Fin nums.val.length), Qualifies (nums.val.get i) → (nums.val.get i).val = v), ∃ r : Std.I64,
      Aegis.AverageValue.average_value nums = ok r ∧
      ∀ v : Int,
        (∀ (i : Fin nums.val.length), Qualifies (nums.val.get i) → (nums.val.get i).val = v) →
          r.val = v) := by
  sorry

end AegisSpec.AverageValue
