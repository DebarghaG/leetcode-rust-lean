import Aegis.BuildArray.Code.Funs

/-!
# Specifications of `Aegis.BuildArray.build_array`

LeetCode problem `build-array-from-permutation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.BuildArray

  def countOcc (l : List I64) (v : Int) : Nat :=
    l.countP (fun x => decide (x.val = v))

  /-- The function returns a result r, len(r) = len(nums), and for every i with 0 <= i < len(nums), r[i] = nums[nums[i]].
    Preconditions: nums is a zero-based permutation: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); and for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_1 (nums : Slice I64)
      (hnums_pos : 1 ≤ nums.val.length)
      (hnums_le : nums.val.length ≤ 1000)
      (hnums_bounds : ∀ i : Nat, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
      (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
        (nums.val[i]!).val ≠ (nums.val[j]!).val) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.BuildArray.build_array nums = ok r ∧
        r.val.length = nums.val.length ∧
        ∀ i : Nat, i < nums.val.length →
          (r.val[i]!).val = (nums.val[(nums.val[i]!).val.toNat]!).val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (hnums_pos : 1 ≤ nums.val.length)
        (hnums_le : nums.val.length ≤ 1000)
        (hnums_bounds : ∀ i : Nat, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
        (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
          (nums.val[i]!).val ≠ (nums.val[j]!).val), ∃ r : alloc.vec.Vec I64,
          Aegis.BuildArray.build_array nums = ok r ∧
          r.val.length = nums.val.length ∧
          ∀ i : Nat, i < nums.val.length →
            (r.val[i]!).val = (nums.val[(nums.val[i]!).val.toNat]!).val) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, return an error, or leave the result undefined) for every input satisfying the preconditions.
    Preconditions: nums is a zero-based permutation: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); and for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_2 (nums : Slice I64)
      (hnums_pos : 1 ≤ nums.val.length)
      (hnums_le : nums.val.length ≤ 1000)
      (hnums_bounds : ∀ i : Nat, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
      (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
        (nums.val[i]!).val ≠ (nums.val[j]!).val) :
      ∃ r : alloc.vec.Vec I64, Aegis.BuildArray.build_array nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (hnums_pos : 1 ≤ nums.val.length)
        (hnums_le : nums.val.length ≤ 1000)
        (hnums_bounds : ∀ i : Nat, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
        (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
          (nums.val[i]!).val ≠ (nums.val[j]!).val), ∃ r : alloc.vec.Vec I64, Aegis.BuildArray.build_array nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(nums).
    Preconditions: nums is a zero-based permutation: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); and for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_3 (nums : Slice I64)
      (hnums_pos : 1 ≤ nums.val.length)
      (hnums_le : nums.val.length ≤ 1000)
      (hnums_bounds : ∀ i : Nat, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
      (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
        (nums.val[i]!).val ≠ (nums.val[j]!).val) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.BuildArray.build_array nums = ok r → r.val.length = nums.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (hnums_pos : 1 ≤ nums.val.length)
        (hnums_le : nums.val.length ≤ 1000)
        (hnums_bounds : ∀ i : Nat, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
        (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
          (nums.val[i]!).val ≠ (nums.val[j]!).val), ∀ r : alloc.vec.Vec I64,
          Aegis.BuildArray.build_array nums = ok r → r.val.length = nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), 0 <= r[i] < len(nums).
    Preconditions: nums is a zero-based permutation: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); and for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_4 (nums : Slice I64)
      (hnums_pos : 1 ≤ nums.val.length)
      (hnums_le : nums.val.length ≤ 1000)
      (hnums_bounds : ∀ i : Nat, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
      (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
        (nums.val[i]!).val ≠ (nums.val[j]!).val) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.BuildArray.build_array nums = ok r →
          ∀ i : Nat, i < r.val.length →
            0 ≤ (r.val[i]!).val ∧ (r.val[i]!).val < (nums.val.length : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (hnums_pos : 1 ≤ nums.val.length)
        (hnums_le : nums.val.length ≤ 1000)
        (hnums_bounds : ∀ i : Nat, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
        (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
          (nums.val[i]!).val ≠ (nums.val[j]!).val), ∀ r : alloc.vec.Vec I64,
          Aegis.BuildArray.build_array nums = ok r →
            ∀ i : Nat, i < r.val.length →
              0 ≤ (r.val[i]!).val ∧ (r.val[i]!).val < (nums.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < j < len(r), r[i] != r[j].
    Preconditions: nums is a zero-based permutation: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); and for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_5 (nums : Slice I64)
      (hnums_pos : 1 ≤ nums.val.length)
      (hnums_le : nums.val.length ≤ 1000)
      (hnums_bounds : ∀ i : Nat, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
      (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
        (nums.val[i]!).val ≠ (nums.val[j]!).val) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.BuildArray.build_array nums = ok r →
          ∀ i j : Nat, i < r.val.length → j < r.val.length → i < j →
            (r.val[i]!).val ≠ (r.val[j]!).val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (hnums_pos : 1 ≤ nums.val.length)
        (hnums_le : nums.val.length ≤ 1000)
        (hnums_bounds : ∀ i : Nat, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
        (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
          (nums.val[i]!).val ≠ (nums.val[j]!).val), ∀ r : alloc.vec.Vec I64,
          Aegis.BuildArray.build_array nums = ok r →
            ∀ i j : Nat, i < r.val.length → j < r.val.length → i < j →
              (r.val[i]!).val ≠ (r.val[j]!).val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v with 0 <= v < len(nums), there exists an index i with 0 <= i < len(r) such that r[i] = v.
    Preconditions: nums is a zero-based permutation: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); and for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_6 (nums : Slice I64)
      (hnums_pos : 1 ≤ nums.val.length)
      (hnums_le : nums.val.length ≤ 1000)
      (hnums_bounds : ∀ i : Nat, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
      (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
        (nums.val[i]!).val ≠ (nums.val[j]!).val) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.BuildArray.build_array nums = ok r →
          ∀ v : Int, 0 ≤ v → v < (nums.val.length : Int) →
            ∃ i : Nat, i < r.val.length ∧ (r.val[i]!).val = v := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (hnums_pos : 1 ≤ nums.val.length)
        (hnums_le : nums.val.length ≤ 1000)
        (hnums_bounds : ∀ i : Nat, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
        (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
          (nums.val[i]!).val ≠ (nums.val[j]!).val), ∀ r : alloc.vec.Vec I64,
          Aegis.BuildArray.build_array nums = ok r →
            ∀ v : Int, 0 ≤ v → v < (nums.val.length : Int) →
              ∃ i : Nat, i < r.val.length ∧ (r.val[i]!).val = v) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), if nums[i] = i then r[i] = i.
    Preconditions: nums is a zero-based permutation: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); and for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_7 (nums : Slice I64)
      (hnums_pos : 1 ≤ nums.val.length)
      (hnums_le : nums.val.length ≤ 1000)
      (hnums_bounds : ∀ i : Nat, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
      (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
        (nums.val[i]!).val ≠ (nums.val[j]!).val) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.BuildArray.build_array nums = ok r →
          ∀ i : Nat, i < nums.val.length →
            (nums.val[i]!).val = (i : Int) → (r.val[i]!).val = (i : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64)
        (hnums_pos : 1 ≤ nums.val.length)
        (hnums_le : nums.val.length ≤ 1000)
        (hnums_bounds : ∀ i : Nat, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
        (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
          (nums.val[i]!).val ≠ (nums.val[j]!).val), ∀ r : alloc.vec.Vec I64,
          Aegis.BuildArray.build_array nums = ok r →
            ∀ i : Nat, i < nums.val.length →
              (nums.val[i]!).val = (i : Int) → (r.val[i]!).val = (i : Int)) := by
    sorry

  /-- Whenever the function returns a result r, if for every i with 0 <= i < len(nums) we have nums[nums[i]] = i, then for every i with 0 <= i < len(nums), r[i] = i.
    Preconditions: nums is a zero-based permutation: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); and for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_8 (nums : Slice I64)
      (hnums_pos : 1 ≤ nums.val.length)
      (hnums_le : nums.val.length ≤ 1000)
      (hnums_bounds : ∀ i : Nat, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
      (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
        (nums.val[i]!).val ≠ (nums.val[j]!).val) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.BuildArray.build_array nums = ok r →
          (∀ i : Nat, i < nums.val.length →
            (nums.val[(nums.val[i]!).val.toNat]!).val = (i : Int)) →
            ∀ i : Nat, i < nums.val.length → (r.val[i]!).val = (i : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64)
        (hnums_pos : 1 ≤ nums.val.length)
        (hnums_le : nums.val.length ≤ 1000)
        (hnums_bounds : ∀ i : Nat, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
        (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
          (nums.val[i]!).val ≠ (nums.val[j]!).val), ∀ r : alloc.vec.Vec I64,
          Aegis.BuildArray.build_array nums = ok r →
            (∀ i : Nat, i < nums.val.length →
              (nums.val[(nums.val[i]!).val.toNat]!).val = (i : Int)) →
              ∀ i : Nat, i < nums.val.length → (r.val[i]!).val = (i : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v equals the number of indices i with 0 <= i < len(nums) and nums[i] = v.
    Preconditions: nums is a zero-based permutation: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); and for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_9 (nums : Slice I64)
      (hnums_pos : 1 ≤ nums.val.length)
      (hnums_le : nums.val.length ≤ 1000)
      (hnums_bounds : ∀ i : Nat, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
      (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
        (nums.val[i]!).val ≠ (nums.val[j]!).val) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.BuildArray.build_array nums = ok r →
          ∀ v : Int, countOcc r.val v = countOcc nums.val v := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64)
        (hnums_pos : 1 ≤ nums.val.length)
        (hnums_le : nums.val.length ≤ 1000)
        (hnums_bounds : ∀ i : Nat, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
        (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
          (nums.val[i]!).val ≠ (nums.val[j]!).val), ∀ r : alloc.vec.Vec I64,
          Aegis.BuildArray.build_array nums = ok r →
            ∀ v : Int, countOcc r.val v = countOcc nums.val v) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < len(nums), 0 <= j < len(nums), if nums[i] = j and nums[j] = i, then r[i] = i and r[j] = j.
    Preconditions: nums is a zero-based permutation: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] < len(nums); and for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_10 (nums : Slice I64)
      (hnums_pos : 1 ≤ nums.val.length)
      (hnums_le : nums.val.length ≤ 1000)
      (hnums_bounds : ∀ i : Nat, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
      (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
        (nums.val[i]!).val ≠ (nums.val[j]!).val) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.BuildArray.build_array nums = ok r →
          ∀ i j : Nat, i < nums.val.length → j < nums.val.length →
            (nums.val[i]!).val = (j : Int) → (nums.val[j]!).val = (i : Int) →
              (r.val[i]!).val = (i : Int) ∧ (r.val[j]!).val = (j : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64)
        (hnums_pos : 1 ≤ nums.val.length)
        (hnums_le : nums.val.length ≤ 1000)
        (hnums_bounds : ∀ i : Nat, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val < (nums.val.length : Int))
        (hnums_inj : ∀ i j : Nat, i < nums.val.length → j < nums.val.length → i < j →
          (nums.val[i]!).val ≠ (nums.val[j]!).val), ∀ r : alloc.vec.Vec I64,
          Aegis.BuildArray.build_array nums = ok r →
            ∀ i j : Nat, i < nums.val.length → j < nums.val.length →
              (nums.val[i]!).val = (j : Int) → (nums.val[j]!).val = (i : Int) →
                (r.val[i]!).val = (i : Int) ∧ (r.val[j]!).val = (j : Int)) := by
    sorry

  end AegisSpec.BuildArray
