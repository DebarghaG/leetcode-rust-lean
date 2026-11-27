import Aegis.SmallerNumbersThanCurrent.Code.Funs

/-!
# Specifications of `Aegis.SmallerNumbersThanCurrent.smaller_numbers_than_current`

LeetCode problem `how-many-numbers-are-smaller-than-the-current-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.SmallerNumbersThanCurrent (smaller_numbers_than_current)

  namespace AegisSpec.SmallerNumbersThanCurrent

  def elem (nums : Slice Std.I64) (i : Nat) : Int := (nums.val.getD i 0#i64).val

  def outElem (r : alloc.vec.Vec Std.I64) (i : Nat) : Int := (r.val.getD i 0#i64).val

  def countSmaller (nums : Slice Std.I64) (i : Nat) : Nat :=
    (List.range nums.val.length).countP
      (fun j => decide (j ≠ i ∧ elem nums j < elem nums i))

  def sumOut (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64) : Int :=
    ((List.range nums.val.length).map (fun i => outElem r i)).sum

  def pairCount (nums : Slice Std.I64) : Nat :=
    ((List.range nums.val.length).map
      (fun i => (List.range nums.val.length).countP
        (fun j => decide (elem nums j < elem nums i)))).sum

  def firstOcc (nums : Slice Std.I64) (i : Nat) : Nat :=
    ((List.range nums.val.length).find? (fun k => decide (elem nums k = elem nums i))).getD 0

  /-- The function returns a result r and, for every i with 0 <= i < len(nums), r[i] is exactly the number of indices j such that 0 <= j < len(nums), j != i, and nums[j] < nums[i].
    Preconditions: 2 <= len(nums) <= 500 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
      (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∃ r, smaller_numbers_than_current nums = ok r ∧
        ∀ i, i < nums.val.length →
          outElem r i = (countSmaller nums i : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
        (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∃ r, smaller_numbers_than_current nums = ok r ∧
          ∀ i, i < nums.val.length →
            outElem r i = (countSmaller nums i : Int)) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(nums).
    Preconditions: 2 <= len(nums) <= 500 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
      (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∀ r, smaller_numbers_than_current nums = ok r → r.val.length = nums.val.length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
        (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∀ r, smaller_numbers_than_current nums = ok r → r.val.length = nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), 0 <= r[i] <= len(nums) - 1.
    Preconditions: 2 <= len(nums) <= 500 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
      (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∀ r, smaller_numbers_than_current nums = ok r →
        ∀ i, i < nums.val.length →
          0 ≤ outElem r i ∧ outElem r i ≤ ((nums.val.length - 1 : Nat) : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
        (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∀ r, smaller_numbers_than_current nums = ok r →
          ∀ i, i < nums.val.length →
            0 ≤ outElem r i ∧ outElem r i ≤ ((nums.val.length - 1 : Nat) : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail because of arithmetic overflow, out-of-bounds indexing, or panic.
    Preconditions: 2 <= len(nums) <= 500 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
      (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∃ r, smaller_numbers_than_current nums = ok r := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
        (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∃ r, smaller_numbers_than_current nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r[i] = 0.
    Preconditions: 2 <= len(nums) <= 500, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100, and for all i and j with 0 <= i < len(nums) and 0 <= j < len(nums), nums[i] = nums[j]. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
      (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100)
      (hall : ∀ i j, i < nums.val.length → j < nums.val.length → elem nums i = elem nums j) :
      ∀ r, smaller_numbers_than_current nums = ok r →
        ∀ i, i < nums.val.length → outElem r i = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
        (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100)
        (hall : ∀ i j, i < nums.val.length → j < nums.val.length → elem nums i = elem nums j), ∀ r, smaller_numbers_than_current nums = ok r →
          ∀ i, i < nums.val.length → outElem r i = 0) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 2, r[0] = (if nums[1] < nums[0] then 1 else 0), and r[1] = (if nums[0] < nums[1] then 1 else 0).
    Preconditions: 2 <= len(nums) <= 500, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100, and len(nums) = 2. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
      (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100)
      (hlen : nums.val.length = 2) :
      ∀ r, smaller_numbers_than_current nums = ok r →
        r.val.length = 2 ∧
        outElem r 0 = (if elem nums 1 < elem nums 0 then 1 else 0) ∧
        outElem r 1 = (if elem nums 0 < elem nums 1 then 1 else 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
        (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100)
        (hlen : nums.val.length = 2), ∀ r, smaller_numbers_than_current nums = ok r →
          r.val.length = 2 ∧
          outElem r 0 = (if elem nums 1 < elem nums 0 then 1 else 0) ∧
          outElem r 1 = (if elem nums 0 < elem nums 1 then 1 else 0)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r[i] = 0 if and only if there is no j with 0 <= j < len(nums), j != i, and nums[j] < nums[i].
    Preconditions: 2 <= len(nums) <= 500 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
      (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∀ r, smaller_numbers_than_current nums = ok r →
        ∀ i, i < nums.val.length →
          (outElem r i = 0 ↔
            ¬ ∃ j, j < nums.val.length ∧ j ≠ i ∧ elem nums j < elem nums i) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
        (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∀ r, smaller_numbers_than_current nums = ok r →
          ∀ i, i < nums.val.length →
            (outElem r i = 0 ↔
              ¬ ∃ j, j < nums.val.length ∧ j ≠ i ∧ elem nums j < elem nums i)) := by
    sorry

  /-- Whenever the function returns a result r, for all i and j with 0 <= i < len(nums) and 0 <= j < len(nums), if nums[i] <= nums[j] then r[i] <= r[j].
    Preconditions: 2 <= len(nums) <= 500 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
      (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∀ r, smaller_numbers_than_current nums = ok r →
        ∀ i j, i < nums.val.length → j < nums.val.length →
          elem nums i ≤ elem nums j → outElem r i ≤ outElem r j := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
        (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∀ r, smaller_numbers_than_current nums = ok r →
          ∀ i j, i < nums.val.length → j < nums.val.length →
            elem nums i ≤ elem nums j → outElem r i ≤ outElem r j) := by
    sorry

  /-- Whenever the function returns a result r, for all i and j with 0 <= i < len(nums) and 0 <= j < len(nums), if nums[i] < nums[j] then r[i] < r[j].
    Preconditions: 2 <= len(nums) <= 500 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
      (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∀ r, smaller_numbers_than_current nums = ok r →
        ∀ i j, i < nums.val.length → j < nums.val.length →
          elem nums i < elem nums j → outElem r i < outElem r j := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
        (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∀ r, smaller_numbers_than_current nums = ok r →
          ∀ i j, i < nums.val.length → j < nums.val.length →
            elem nums i < elem nums j → outElem r i < outElem r j) := by
    sorry

  /-- Whenever the function returns a result r, for all i and j with 0 <= i < len(nums) and 0 <= j < len(nums), if nums[i] = nums[j] then r[i] = r[j].
    Preconditions: 2 <= len(nums) <= 500 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
      (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∀ r, smaller_numbers_than_current nums = ok r →
        ∀ i j, i < nums.val.length → j < nums.val.length →
          elem nums i = elem nums j → outElem r i = outElem r j := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
        (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∀ r, smaller_numbers_than_current nums = ok r →
          ∀ i j, i < nums.val.length → j < nums.val.length →
            elem nums i = elem nums j → outElem r i = outElem r j) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), if nums[i] > nums[j] for every j with 0 <= j < len(nums) and j != i, then r[i] = len(nums) - 1.
    Preconditions: 2 <= len(nums) <= 500 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
      (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∀ r, smaller_numbers_than_current nums = ok r →
        ∀ i, i < nums.val.length →
          (∀ j, j < nums.val.length → j ≠ i → elem nums j < elem nums i) →
            outElem r i = ((nums.val.length - 1 : Nat) : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
        (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∀ r, smaller_numbers_than_current nums = ok r →
          ∀ i, i < nums.val.length →
            (∀ j, j < nums.val.length → j ≠ i → elem nums j < elem nums i) →
              outElem r i = ((nums.val.length - 1 : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), if r[i] = len(nums) - 1, then nums[i] > nums[j] for every j with 0 <= j < len(nums) and j != i.
    Preconditions: 2 <= len(nums) <= 500 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
      (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∀ r, smaller_numbers_than_current nums = ok r →
        ∀ i, i < nums.val.length →
          outElem r i = ((nums.val.length - 1 : Nat) : Int) →
            ∀ j, j < nums.val.length → j ≠ i → elem nums j < elem nums i := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
        (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∀ r, smaller_numbers_than_current nums = ok r →
          ∀ i, i < nums.val.length →
            outElem r i = ((nums.val.length - 1 : Nat) : Int) →
              ∀ j, j < nums.val.length → j ≠ i → elem nums j < elem nums i) := by
    sorry

  /-- Whenever the function returns a result r, the sum of r[i] over all i with 0 <= i < len(nums) equals the number of ordered pairs (i,j) such that 0 <= i < len(nums), 0 <= j < len(nums), and nums[j] < nums[i].
    Preconditions: 2 <= len(nums) <= 500 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
  theorem spec_13 (nums : Slice Std.I64)
      (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
      (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∀ r, smaller_numbers_than_current nums = ok r →
        sumOut nums r = (pairCount nums : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
        (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100), ∀ r, smaller_numbers_than_current nums = ok r →
          sumOut nums r = (pairCount nums : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(nums), there is exactly one i with 0 <= i < len(nums) such that r[i] = k.
    Preconditions: 2 <= len(nums) <= 500, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100, and for all i and j with 0 <= i < len(nums) and 0 <= j < len(nums), if i != j then nums[i] != nums[j]. -/
  theorem spec_14 (nums : Slice Std.I64)
      (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
      (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100)
      (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length →
        i ≠ j → elem nums i ≠ elem nums j) :
      ∀ r, smaller_numbers_than_current nums = ok r →
        ∀ k, k < nums.val.length →
          ∃! i, i < nums.val.length ∧ outElem r i = (k : Int) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
        (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100)
        (hdistinct : ∀ i j, i < nums.val.length → j < nums.val.length →
          i ≠ j → elem nums i ≠ elem nums j), ∀ r, smaller_numbers_than_current nums = ok r →
          ∀ k, k < nums.val.length →
            ∃! i, i < nums.val.length ∧ outElem r i = (k : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r[i] equals the smallest index k with 0 <= k < len(nums) and nums[k] = nums[i].
    Preconditions: 2 <= len(nums) <= 500, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100, and for all i and j with 0 <= i <= j < len(nums), nums[i] <= nums[j]. -/
  theorem spec_15 (nums : Slice Std.I64)
      (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
      (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100)
      (hsorted : ∀ i j, i ≤ j → j < nums.val.length → elem nums i ≤ elem nums j) :
      ∀ r, smaller_numbers_than_current nums = ok r →
        ∀ i, i < nums.val.length → outElem r i = (firstOcc nums i : Int) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen2 : 2 ≤ nums.val.length) (hlen500 : nums.val.length ≤ 500)
        (hbound : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 100)
        (hsorted : ∀ i j, i ≤ j → j < nums.val.length → elem nums i ≤ elem nums j), ∀ r, smaller_numbers_than_current nums = ok r →
          ∀ i, i < nums.val.length → outElem r i = (firstOcc nums i : Int)) := by
    sorry

  end AegisSpec.SmallerNumbersThanCurrent
