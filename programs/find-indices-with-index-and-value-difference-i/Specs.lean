import Aegis.FindIndices.Code.Funs

/-!
# Specifications of `Aegis.FindIndices.find_indices`

LeetCode problem `find-indices-with-index-and-value-difference-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindIndices

def elem (nums : Slice Std.I64) (i : Int) : Int := (nums.val[i.toNat]!).val

def ValidPair (nums : Slice Std.I64) (indexDifference valueDifference : Int)
    (i j : Int) : Prop :=
  0 ≤ i ∧ i < (nums.val.length : Int) ∧ 0 ≤ j ∧ j < (nums.val.length : Int) ∧
    indexDifference.toNat ≤ Int.natAbs (i - j) ∧
    valueDifference.toNat ≤ Int.natAbs (elem nums i - elem nums j)

/-- Let n = len(nums). Call a pair (i,j) of integers valid when 0 <= i < n, 0 <= j < n, |i-j| >= indexDifference, and |nums[i]-nums[j]| >= valueDifference. Whenever the function returns a result r, len(r) = 2 and: (1) if at least one valid pair exists, then 0 <= r[0] < n, 0 <= r[1] < n, |r[0]-r[1]| >= indexDifference, and |nums[r[0]]-nums[r[1]]| >= valueDifference; (2) if no valid pair exists, then r[0] = -1 and r[1] = -1. Any valid ordered pair is acceptable; the specification does not require a unique answer.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100; for every k with 0 <= k < n, 0 <= nums[k] <= 50; 0 <= indexDifference <= 100; and 0 <= valueDifference <= 50. All I64 values are interpreted as mathematical integers; these bounds keep the mentioned differences and absolute values in range. -/
theorem spec_1 (nums : Slice Std.I64) (indexDifference valueDifference : Std.I64)
    (h_len_lower : 1 ≤ nums.val.length)
    (h_len_upper : nums.val.length ≤ 100)
    (h_nums : ∀ k, k < nums.val.length → 0 ≤ (nums.val[k]!).val ∧ (nums.val[k]!).val ≤ 50)
    (h_index_lower : 0 ≤ indexDifference.val) (h_index_upper : indexDifference.val ≤ 100)
    (h_value_lower : 0 ≤ valueDifference.val) (h_value_upper : valueDifference.val ≤ 50) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindIndices.find_indices nums indexDifference valueDifference = ok r →
        r.val.length = 2 ∧
          ((∃ i j : Int, ValidPair nums indexDifference.val valueDifference.val i j) →
            0 ≤ (r.val[0]!).val ∧ (r.val[0]!).val < (nums.val.length : Int) ∧
              0 ≤ (r.val[1]!).val ∧ (r.val[1]!).val < (nums.val.length : Int) ∧
              indexDifference.val.toNat ≤ Int.natAbs ((r.val[0]!).val - (r.val[1]!).val) ∧
              valueDifference.val.toNat ≤
                Int.natAbs (elem nums (r.val[0]!).val - elem nums (r.val[1]!).val)) ∧
          ((¬∃ i j : Int, ValidPair nums indexDifference.val valueDifference.val i j) →
            (r.val[0]!).val = -1 ∧ (r.val[1]!).val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (indexDifference valueDifference : Std.I64)
    (h_len_lower : 1 ≤ nums.val.length)
    (h_len_upper : nums.val.length ≤ 100)
    (h_nums : ∀ k, k < nums.val.length → 0 ≤ (nums.val[k]!).val ∧ (nums.val[k]!).val ≤ 50)
    (h_index_lower : 0 ≤ indexDifference.val) (h_index_upper : indexDifference.val ≤ 100)
    (h_value_lower : 0 ≤ valueDifference.val) (h_value_upper : valueDifference.val ≤ 50), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindIndices.find_indices nums indexDifference valueDifference = ok r →
        r.val.length = 2 ∧
          ((∃ i j : Int, ValidPair nums indexDifference.val valueDifference.val i j) →
            0 ≤ (r.val[0]!).val ∧ (r.val[0]!).val < (nums.val.length : Int) ∧
              0 ≤ (r.val[1]!).val ∧ (r.val[1]!).val < (nums.val.length : Int) ∧
              indexDifference.val.toNat ≤ Int.natAbs ((r.val[0]!).val - (r.val[1]!).val) ∧
              valueDifference.val.toNat ≤
                Int.natAbs (elem nums (r.val[0]!).val - elem nums (r.val[1]!).val)) ∧
          ((¬∃ i j : Int, ValidPair nums indexDifference.val valueDifference.val i j) →
            (r.val[0]!).val = -1 ∧ (r.val[1]!).val = -1)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100; for every k with 0 <= k < n, 0 <= nums[k] <= 50; 0 <= indexDifference <= 100; and 0 <= valueDifference <= 50. All I64 values are interpreted as mathematical integers; these bounds keep the mentioned differences and absolute values in range. -/
theorem spec_2 (nums : Slice Std.I64) (indexDifference valueDifference : Std.I64)
    (h_len_lower : 1 ≤ nums.val.length)
    (h_len_upper : nums.val.length ≤ 100)
    (h_nums : ∀ k, k < nums.val.length → 0 ≤ (nums.val[k]!).val ∧ (nums.val[k]!).val ≤ 50)
    (h_index_lower : 0 ≤ indexDifference.val) (h_index_upper : indexDifference.val ≤ 100)
    (h_value_lower : 0 ≤ valueDifference.val) (h_value_upper : valueDifference.val ≤ 50) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindIndices.find_indices nums indexDifference valueDifference = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (indexDifference valueDifference : Std.I64)
    (h_len_lower : 1 ≤ nums.val.length)
    (h_len_upper : nums.val.length ≤ 100)
    (h_nums : ∀ k, k < nums.val.length → 0 ≤ (nums.val[k]!).val ∧ (nums.val[k]!).val ≤ 50)
    (h_index_lower : 0 ≤ indexDifference.val) (h_index_upper : indexDifference.val ≤ 100)
    (h_value_lower : 0 ≤ valueDifference.val) (h_value_upper : valueDifference.val ≤ 50), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindIndices.find_indices nums indexDifference valueDifference = ok r) := by
  sorry

end AegisSpec.FindIndices
