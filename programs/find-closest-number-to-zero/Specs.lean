import Aegis.FindClosestNumber.Code.Funs

/-!
# Specifications of `Aegis.FindClosestNumber.find_closest_number`

LeetCode problem `find-closest-number-to-zero`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindClosestNumber

  def countValue (nums : Slice Std.I64) (v : Int) : Nat :=
    (nums.val.filter fun x => decide (x.val = v)).length

  def IsPermutationOf (nums nums' : Slice Std.I64) : Prop :=
    ∀ v : Int, countValue nums v = countValue nums' v

  /-- Whenever find_closest_number(nums) returns a result r, the following three conditions hold: (1) there is an index i with 0 <= i < len(nums) such that nums[i] = r; (2) for every index j with 0 <= j < len(nums), |r| <= |nums[j]|; (3) for every index j with 0 <= j < len(nums), if |nums[j]| = |r| then nums[j] <= r. In words, r is an element of nums with minimum absolute value, and among all elements of nums with that minimum absolute value it is the largest.
    Preconditions: The input slice nums satisfies: 1 <= len(nums) <= 1000, and for every index i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. Machine integers are interpreted by their mathematical values; these bounds make the absolute values used below safe from i64 overflow. -/
  theorem spec_1 (nums : Slice Std.I64) (r : Std.I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 1000)
      (h_bounds : ∀ i : Nat, ∀ h : i < nums.val.length,
        -100000 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 100000)
      (h_res : Aegis.FindClosestNumber.find_closest_number nums = ok r) :
      (∃ i : Nat, ∃ h : i < nums.val.length, (nums.val.get ⟨i, h⟩).val = r.val) ∧
      (∀ j : Nat, ∀ h : j < nums.val.length, |r.val| ≤ |(nums.val.get ⟨j, h⟩).val|) ∧
      (∀ j : Nat, ∀ h : j < nums.val.length,
        |(nums.val.get ⟨j, h⟩).val| = |r.val| → (nums.val.get ⟨j, h⟩).val ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 1000)
        (h_bounds : ∀ i : Nat, ∀ h : i < nums.val.length,
          -100000 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 100000)
        (h_res : Aegis.FindClosestNumber.find_closest_number nums = ok r), (∃ i : Nat, ∃ h : i < nums.val.length, (nums.val.get ⟨i, h⟩).val = r.val) ∧
        (∀ j : Nat, ∀ h : j < nums.val.length, |r.val| ≤ |(nums.val.get ⟨j, h⟩).val|) ∧
        (∀ j : Nat, ∀ h : j < nums.val.length,
          |(nums.val.get ⟨j, h⟩).val| = |r.val| → (nums.val.get ⟨j, h⟩).val ≤ r.val)) := by
    sorry

  /-- For every input nums satisfying the preconditions, find_closest_number(nums) returns a result r; it does not fail, panic, or overflow.
    Preconditions: The input slice nums satisfies: 1 <= len(nums) <= 1000, and for every index i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 1000)
      (h_bounds : ∀ i : Nat, ∀ h : i < nums.val.length,
        -100000 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 100000) :
      ∃ r : Std.I64, Aegis.FindClosestNumber.find_closest_number nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 1000)
        (h_bounds : ∀ i : Nat, ∀ h : i < nums.val.length,
          -100000 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 100000), ∃ r : Std.I64, Aegis.FindClosestNumber.find_closest_number nums = ok r) := by
    sorry

  /-- Whenever find_closest_number(nums) returns a result r, there exists an index i with 0 <= i < len(nums) such that nums[i] = r.
    Preconditions: The input slice nums satisfies: 1 <= len(nums) <= 1000, and for every index i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_3 (nums : Slice Std.I64) (r : Std.I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 1000)
      (h_bounds : ∀ i : Nat, ∀ h : i < nums.val.length,
        -100000 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 100000)
      (h_res : Aegis.FindClosestNumber.find_closest_number nums = ok r) :
      ∃ i : Nat, ∃ h : i < nums.val.length, (nums.val.get ⟨i, h⟩).val = r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 1000)
        (h_bounds : ∀ i : Nat, ∀ h : i < nums.val.length,
          -100000 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 100000)
        (h_res : Aegis.FindClosestNumber.find_closest_number nums = ok r), ∃ i : Nat, ∃ h : i < nums.val.length, (nums.val.get ⟨i, h⟩).val = r.val) := by
    sorry

  /-- Whenever find_closest_number(nums) returns a result r, for every index j with 0 <= j < len(nums), |r| <= |nums[j]|.
    Preconditions: The input slice nums satisfies: 1 <= len(nums) <= 1000, and for every index i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_4 (nums : Slice Std.I64) (r : Std.I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 1000)
      (h_bounds : ∀ i : Nat, ∀ h : i < nums.val.length,
        -100000 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 100000)
      (h_res : Aegis.FindClosestNumber.find_closest_number nums = ok r) :
      ∀ j : Nat, ∀ h : j < nums.val.length, |r.val| ≤ |(nums.val.get ⟨j, h⟩).val| := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 1000)
        (h_bounds : ∀ i : Nat, ∀ h : i < nums.val.length,
          -100000 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 100000)
        (h_res : Aegis.FindClosestNumber.find_closest_number nums = ok r), ∀ j : Nat, ∀ h : j < nums.val.length, |r.val| ≤ |(nums.val.get ⟨j, h⟩).val|) := by
    sorry

  /-- Whenever find_closest_number(nums) returns a result r, for every index j with 0 <= j < len(nums), if |nums[j]| = |r| then nums[j] <= r.
    Preconditions: The input slice nums satisfies: 1 <= len(nums) <= 1000, and for every index i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_5 (nums : Slice Std.I64) (r : Std.I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 1000)
      (h_bounds : ∀ i : Nat, ∀ h : i < nums.val.length,
        -100000 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 100000)
      (h_res : Aegis.FindClosestNumber.find_closest_number nums = ok r) :
      ∀ j : Nat, ∀ h : j < nums.val.length,
        |(nums.val.get ⟨j, h⟩).val| = |r.val| → (nums.val.get ⟨j, h⟩).val ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 1000)
        (h_bounds : ∀ i : Nat, ∀ h : i < nums.val.length,
          -100000 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 100000)
        (h_res : Aegis.FindClosestNumber.find_closest_number nums = ok r), ∀ j : Nat, ∀ h : j < nums.val.length,
          |(nums.val.get ⟨j, h⟩).val| = |r.val| → (nums.val.get ⟨j, h⟩).val ≤ r.val) := by
    sorry

  /-- Whenever find_closest_number(nums) returns a result r, -100000 <= r <= 100000.
    Preconditions: The input slice nums satisfies: 1 <= len(nums) <= 1000, and for every index i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_6 (nums : Slice Std.I64) (r : Std.I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 1000)
      (h_bounds : ∀ i : Nat, ∀ h : i < nums.val.length,
        -100000 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 100000)
      (h_res : Aegis.FindClosestNumber.find_closest_number nums = ok r) :
      -100000 ≤ r.val ∧ r.val ≤ 100000 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 1000)
        (h_bounds : ∀ i : Nat, ∀ h : i < nums.val.length,
          -100000 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 100000)
        (h_res : Aegis.FindClosestNumber.find_closest_number nums = ok r), -100000 ≤ r.val ∧ r.val ≤ 100000) := by
    sorry

  /-- Whenever find_closest_number(nums) returns a result r and find_closest_number(nums') returns a result r', we have r = r'.
    Preconditions: The slices nums and nums' both satisfy the original input constraints: 1 <= len(nums) <= 1000, 1 <= len(nums') <= 1000, and all values lie in [-100000, 100000]. Moreover, nums' is a permutation of nums, meaning that for every integer v, the number of indices i with nums[i] = v equals the number of indices i with nums'[i] = v. -/
  theorem spec_7 (nums nums' : Slice Std.I64) (r r' : Std.I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 1000)
      (h_bounds : ∀ i : Nat, ∀ h : i < nums.val.length,
        -100000 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 100000)
      (h_len' : 1 ≤ nums'.val.length)
      (h_len_le' : nums'.val.length ≤ 1000)
      (h_bounds' : ∀ i : Nat, ∀ h : i < nums'.val.length,
        -100000 ≤ (nums'.val.get ⟨i, h⟩).val ∧ (nums'.val.get ⟨i, h⟩).val ≤ 100000)
      (h_perm : IsPermutationOf nums nums')
      (h_res : Aegis.FindClosestNumber.find_closest_number nums = ok r)
      (h_res' : Aegis.FindClosestNumber.find_closest_number nums' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (r r' : Std.I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 1000)
        (h_bounds : ∀ i : Nat, ∀ h : i < nums.val.length,
          -100000 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 100000)
        (h_len' : 1 ≤ nums'.val.length)
        (h_len_le' : nums'.val.length ≤ 1000)
        (h_bounds' : ∀ i : Nat, ∀ h : i < nums'.val.length,
          -100000 ≤ (nums'.val.get ⟨i, h⟩).val ∧ (nums'.val.get ⟨i, h⟩).val ≤ 100000)
        (h_perm : IsPermutationOf nums nums')
        (h_res : Aegis.FindClosestNumber.find_closest_number nums = ok r)
        (h_res' : Aegis.FindClosestNumber.find_closest_number nums' = ok r'), r.val = r'.val) := by
    sorry

  end AegisSpec.FindClosestNumber
