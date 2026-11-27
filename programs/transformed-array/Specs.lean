import Aegis.ConstructTransformedArray.Code.Funs

/-!
# Specifications of `Aegis.ConstructTransformedArray.construct_transformed_array`

LeetCode problem `transformed-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ConstructTransformedArray

def getI (l : List Std.I64) (i : Nat) : Int :=
  ((l[i]?).map (fun x => x.val)).getD 0

theorem getI_of_lt {l : List Std.I64} {i : Nat} (h : i < l.length) :
    getI l i = (l[i]).val := by
  simp [getI, List.getElem?_eq_getElem h]

/-- The function returns a result r such that r.len = len(nums), and for every i with 0 <= i < len(nums), if j is the unique integer satisfying 0 <= j < len(nums) and j ≡ i + nums[i] (mod len(nums)), then r[i] = nums[j]. This is the circular move: positive nums[i] moves right, negative nums[i] moves left, and nums[i] = 0 stays at i.
  Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_1 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
    ∃ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r ∧
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length →
        ∃ j, j < nums.val.length ∧
          ((j : Int) ≡ (i : Int) + getI nums.val i [ZMOD (nums.val.length : Int)]) ∧
          getI r.val i = getI nums.val j := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∃ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r ∧
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length →
        ∃ j, j < nums.val.length ∧
          ((j : Int) ≡ (i : Int) + getI nums.val i [ZMOD (nums.val.length : Int)]) ∧
          getI r.val i = getI nums.val j) := by
  sorry

/-- The function returns a result r; it does not fail for any input satisfying the preconditions.
  Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_2 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
    ∃ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∃ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, r.len = len(nums).
  Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_3 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
    ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      r.val.length = nums.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      r.val.length = nums.val.length) := by
  sorry

/-- Whenever the function returns a result r, r.len = len(nums) and for every i with 0 <= i < len(nums), -100 <= r[i] <= 100.
  Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_4 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
    ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length → -100 ≤ getI r.val i ∧ getI r.val i ≤ 100 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length → -100 ≤ getI r.val i ∧ getI r.val i ≤ 100) := by
  sorry

/-- Whenever the function returns a result r, r.len = len(nums) and for every i with 0 <= i < len(nums), there exists k with 0 <= k < len(nums) such that r[i] = nums[k].
  Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_5 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
    ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length → ∃ k, k < nums.val.length ∧ getI r.val i = getI nums.val k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length → ∃ k, k < nums.val.length ∧ getI r.val i = getI nums.val k) := by
  sorry

/-- Whenever the function returns a result r, r.len = len(nums) and for every i with 0 <= i < len(nums), if nums[i] = 0 then r[i] = 0.
  Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_6 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
    ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length → getI nums.val i = 0 → getI r.val i = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length → getI nums.val i = 0 → getI r.val i = 0) := by
  sorry

/-- Whenever the function returns a result r, r.len = len(nums) and for every i with 0 <= i < len(nums), if len(nums) divides nums[i], then r[i] = nums[i].
  Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_7 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
    ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length → (nums.val.length : Int) ∣ getI nums.val i →
        getI r.val i = getI nums.val i := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length → (nums.val.length : Int) ∣ getI nums.val i →
        getI r.val i = getI nums.val i) := by
  sorry

/-- Whenever the function returns a result r and there exists an integer c such that nums[i] = c for every i with 0 <= i < len(nums), then r.len = len(nums) and r[i] = c for every i with 0 <= i < len(nums).
  Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_8 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
    ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      ∀ c : Int, (∀ i, i < nums.val.length → getI nums.val i = c) →
        r.val.length = nums.val.length ∧
        ∀ i, i < nums.val.length → getI r.val i = c := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      ∀ c : Int, (∀ i, i < nums.val.length → getI nums.val i = c) →
        r.val.length = nums.val.length ∧
        ∀ i, i < nums.val.length → getI r.val i = c) := by
  sorry

/-- Whenever the function returns a result r, r.len = len(nums) and for every i with 0 <= i < len(nums), if nums[i] >= 0 and i + nums[i] < len(nums), then r[i] = nums[i + nums[i]].
  Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_9 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
    ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length → 0 ≤ getI nums.val i →
        i + (getI nums.val i).toNat < nums.val.length →
        getI r.val i = getI nums.val (i + (getI nums.val i).toNat) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length → 0 ≤ getI nums.val i →
        i + (getI nums.val i).toNat < nums.val.length →
        getI r.val i = getI nums.val (i + (getI nums.val i).toNat)) := by
  sorry

/-- Whenever the function returns a result r, r.len = len(nums) and for every i with 0 <= i < len(nums), if nums[i] <= 0 and i + nums[i] >= 0, then r[i] = nums[i + nums[i]].
  Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_10 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
    ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length → getI nums.val i ≤ 0 →
        0 ≤ (i : Int) + getI nums.val i →
        getI r.val i = getI nums.val ((i : Int) + getI nums.val i).toNat := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length → getI nums.val i ≤ 0 →
        0 ≤ (i : Int) + getI nums.val i →
        getI r.val i = getI nums.val ((i : Int) + getI nums.val i).toNat) := by
  sorry

/-- Whenever the function returns a result r, r.len = len(nums) and for every i with 0 <= i < len(nums), if nums[i] > 0 and len(nums) <= i + nums[i] < 2 * len(nums), then r[i] = nums[i + nums[i] - len(nums)].
  Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_11 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
    ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length → 0 < getI nums.val i →
        (nums.val.length : Int) ≤ (i : Int) + getI nums.val i →
        (i : Int) + getI nums.val i < 2 * (nums.val.length : Int) →
        getI r.val i =
          getI nums.val (((i : Int) + getI nums.val i) - (nums.val.length : Int)).toNat := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length → 0 < getI nums.val i →
        (nums.val.length : Int) ≤ (i : Int) + getI nums.val i →
        (i : Int) + getI nums.val i < 2 * (nums.val.length : Int) →
        getI r.val i =
          getI nums.val (((i : Int) + getI nums.val i) - (nums.val.length : Int)).toNat) := by
  sorry

/-- Whenever the function returns a result r, r.len = len(nums) and for every i with 0 <= i < len(nums), if nums[i] < 0 and -len(nums) <= i + nums[i] < 0, then r[i] = nums[i + nums[i] + len(nums)].
  Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
theorem spec_12 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100) :
    ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length → getI nums.val i < 0 →
        -((nums.val.length : Int)) ≤ (i : Int) + getI nums.val i →
        (i : Int) + getI nums.val i < 0 →
        getI r.val i =
          getI nums.val (((i : Int) + getI nums.val i) + (nums.val.length : Int)).toNat := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100)
    (h_range : ∀ i, i < nums.val.length →
      -100 ≤ getI nums.val i ∧ getI nums.val i ≤ 100), ∀ r, Aegis.ConstructTransformedArray.construct_transformed_array nums = Result.ok r →
      r.val.length = nums.val.length ∧
      ∀ i, i < nums.val.length → getI nums.val i < 0 →
        -((nums.val.length : Int)) ≤ (i : Int) + getI nums.val i →
        (i : Int) + getI nums.val i < 0 →
        getI r.val i =
          getI nums.val (((i : Int) + getI nums.val i) + (nums.val.length : Int)).toNat) := by
  sorry

end AegisSpec.ConstructTransformedArray
