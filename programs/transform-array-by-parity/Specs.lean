import Aegis.TransformArray.Code.Funs

/-!
# Specifications of `Aegis.TransformArray.transform_array`

LeetCode problem `transform-array-by-parity`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.TransformArray

  def IsEven (x : Std.I64) : Prop := 2 ∣ x.val

  def IsOdd (x : Std.I64) : Prop := 2 ∣ x.val - 1

  instance (x : Std.I64) : Decidable (IsEven x) :=
    inferInstanceAs (Decidable (2 ∣ x.val))

  instance (x : Std.I64) : Decidable (IsOdd x) :=
    inferInstanceAs (Decidable (2 ∣ x.val - 1))

  def countWhere (p : Std.I64 → Prop) [DecidablePred p] (l : List Std.I64) : ℕ :=
    (l.filter p).length

  /-- Whenever transform_array(nums) returns a result r, the following all hold: (1) len(r) = len(nums); (2) for every j with 0 <= j < len(r), r[j] is either 0 or 1; (3) r is non-decreasing, i.e. r[j] <= r[j+1] for every j with 0 <= j < len(r)-1; and (4) the number of indices j with 0 <= j < len(r) and r[j] = 0 equals the number of indices i with 0 <= i < len(nums) such that nums[i] is even, while the number of indices j with 0 <= j < len(r) and r[j] = 1 equals the number of indices i with 0 <= i < len(nums) such that nums[i] is odd. Here nums[i] is even if nums[i] = 2k for some integer k, and odd if nums[i] = 2k+1 for some integer k.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100)
      (h_range : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 1000) :
      ∀ (r : alloc.vec.Vec Std.I64),
        Aegis.TransformArray.transform_array nums = ok r →
          r.val.length = nums.val.length ∧
          (∀ (j : ℕ) (hj : j < r.val.length),
            (r.val.get ⟨j, hj⟩).val = 0 ∨ (r.val.get ⟨j, hj⟩).val = 1) ∧
          (∀ (j : ℕ) (hj : j + 1 < r.val.length),
            (r.val.get ⟨j, Nat.lt_of_succ_lt hj⟩).val ≤ (r.val.get ⟨j + 1, hj⟩).val) ∧
          countWhere (fun x => x.val = 0) r.val = countWhere IsEven nums.val ∧
          countWhere (fun x => x.val = 1) r.val = countWhere IsOdd nums.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100)
        (h_range : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 1000), ∀ (r : alloc.vec.Vec Std.I64),
          Aegis.TransformArray.transform_array nums = ok r →
            r.val.length = nums.val.length ∧
            (∀ (j : ℕ) (hj : j < r.val.length),
              (r.val.get ⟨j, hj⟩).val = 0 ∨ (r.val.get ⟨j, hj⟩).val = 1) ∧
            (∀ (j : ℕ) (hj : j + 1 < r.val.length),
              (r.val.get ⟨j, Nat.lt_of_succ_lt hj⟩).val ≤ (r.val.get ⟨j + 1, hj⟩).val) ∧
            countWhere (fun x => x.val = 0) r.val = countWhere IsEven nums.val ∧
            countWhere (fun x => x.val = 1) r.val = countWhere IsOdd nums.val) := by
    sorry

  /-- transform_array(nums) returns a result r; in particular, it does not fail, panic, or overflow for any input satisfying the preconditions.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100)
      (h_range : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 1000) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.TransformArray.transform_array nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100)
        (h_range : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 1000), ∃ r : alloc.vec.Vec Std.I64, Aegis.TransformArray.transform_array nums = ok r) := by
    sorry

  end AegisSpec.TransformArray
