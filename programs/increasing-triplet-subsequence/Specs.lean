import Aegis.IncreasingTriplet.Code.Funs

/-!
# Specifications of `Aegis.IncreasingTriplet.increasing_triplet`

LeetCode problem `increasing-triplet-subsequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IncreasingTriplet

  def LengthWithinBounds (nums : Slice Std.I64) : Prop :=
    1 ≤ nums.val.length ∧ nums.val.length ≤ 500000

  def ValuesWithinBounds (nums : Slice Std.I64) : Prop :=
    ∀ (i : Fin nums.val.length),
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647

  def HasIncreasingTriplet (nums : Slice Std.I64) : Prop :=
    ∃ (i j k : Fin nums.val.length),
      i < j ∧ j < k ∧
        (nums.val.get i).val < (nums.val.get j).val ∧
          (nums.val.get j).val < (nums.val.get k).val

  def SameComparisonPattern (nums other : Slice Std.I64)
      (h : other.val.length = nums.val.length) : Prop :=
    ∀ (i j : Fin nums.val.length),
      (nums.val.get i).val < (nums.val.get j).val ↔
        (other.val.get ⟨i.val, i.isLt.trans_eq h.symm⟩).val <
          (other.val.get ⟨j.val, j.isLt.trans_eq h.symm⟩).val

  /-- The function returns a result r, and r = true if and only if there exist indices i, j, k with 0 <= i < j < k < len(nums) such that nums[i] < nums[j] < nums[k]. Equivalently, r = false if and only if no such indices i, j, k exist.
    Preconditions: 1 <= len(nums) <= 500000 and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
  theorem spec_1 (nums : Slice Std.I64)
      (h_len : LengthWithinBounds nums) (h_range : ValuesWithinBounds nums) :
      ∃ r : Bool, Aegis.IncreasingTriplet.increasing_triplet nums = ok r ∧
        (r = true ↔ HasIncreasingTriplet nums) ∧
          (r = false ↔ ¬ HasIncreasingTriplet nums) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : LengthWithinBounds nums) (h_range : ValuesWithinBounds nums), ∃ r : Bool, Aegis.IncreasingTriplet.increasing_triplet nums = ok r ∧
          (r = true ↔ HasIncreasingTriplet nums) ∧
            (r = false ↔ ¬ HasIncreasingTriplet nums)) := by
    sorry

  /-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
    Preconditions: 1 <= len(nums) <= 500000 and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_len : LengthWithinBounds nums) (h_range : ValuesWithinBounds nums) :
      ∃ r : Bool, Aegis.IncreasingTriplet.increasing_triplet nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : LengthWithinBounds nums) (h_range : ValuesWithinBounds nums), ∃ r : Bool, Aegis.IncreasingTriplet.increasing_triplet nums = ok r) := by
    sorry

  /-- For every slice other with len(other) = len(nums), every element of other in the range -2147483648..2147483647, and with nums[i] < nums[j] if and only if other[i] < other[j] for all 0 <= i < len(nums) and 0 <= j < len(nums), the function returns a result r when applied to nums and a result s when applied to other, and r = s.
    Preconditions: 1 <= len(nums) <= 500000 and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
  theorem spec_3 (nums other : Slice Std.I64)
      (h_len : LengthWithinBounds nums) (h_range : ValuesWithinBounds nums)
      (h_len_other : other.val.length = nums.val.length)
      (h_range_other : ValuesWithinBounds other)
      (h_cmp : SameComparisonPattern nums other h_len_other) :
      ∃ r s : Bool,
        Aegis.IncreasingTriplet.increasing_triplet nums = ok r ∧
          Aegis.IncreasingTriplet.increasing_triplet other = ok s ∧ r = s := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums other : Slice Std.I64)
        (h_len : LengthWithinBounds nums) (h_range : ValuesWithinBounds nums)
        (h_len_other : other.val.length = nums.val.length)
        (h_range_other : ValuesWithinBounds other)
        (h_cmp : SameComparisonPattern nums other h_len_other), ∃ r s : Bool,
          Aegis.IncreasingTriplet.increasing_triplet nums = ok r ∧
            Aegis.IncreasingTriplet.increasing_triplet other = ok s ∧ r = s) := by
    sorry

  end AegisSpec.IncreasingTriplet
