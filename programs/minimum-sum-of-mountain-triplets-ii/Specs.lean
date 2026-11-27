import Aegis.MinimumSum.Code.Funs

/-!
# Specifications of `Aegis.MinimumSum.minimum_sum`

LeetCode problem `minimum-sum-of-mountain-triplets-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumSum

  abbrev I64Slice : Type := Slice Std.I64

  def numLen (nums : I64Slice) : Nat := nums.val.length

  def numAt (nums : I64Slice) (i : Nat) : Int := (nums.val[i]!).val

  def IsMountainTriplet (nums : I64Slice) (i j k : Nat) : Prop :=
    i < j ∧ j < k ∧ k < numLen nums ∧ numAt nums i < numAt nums j ∧
      numAt nums k < numAt nums j

  def HasMountainTriplet (nums : I64Slice) : Prop :=
    ∃ i j k, IsMountainTriplet nums i j k

  def IsMinMountainSum (nums : I64Slice) (r : Int) : Prop :=
    (∃ i j k,
        IsMountainTriplet nums i j k ∧ r = numAt nums i + numAt nums j + numAt nums k) ∧
      ∀ i j k,
        IsMountainTriplet nums i j k → r ≤ numAt nums i + numAt nums j + numAt nums k

  def IsReverse (revs nums : I64Slice) : Prop :=
    numLen revs = numLen nums ∧
      ∀ t, t < numLen nums → numAt revs t = numAt nums (numLen nums - 1 - t)

  def StrictlyIncreasing (nums : I64Slice) : Prop :=
    ∀ i, i + 1 < numLen nums → numAt nums i < numAt nums (i + 1)

  def StrictlyDecreasing (nums : I64Slice) : Prop :=
    ∀ i, i + 1 < numLen nums → numAt nums (i + 1) < numAt nums i

  def AllEqual (nums : I64Slice) : Prop :=
    ∀ i, i < numLen nums → numAt nums i = numAt nums 0

  /-- Whenever the function returns a result r, define a mountain triplet of nums to be any triple of indices (i, j, k) such that 0 <= i < j < k < len(nums), nums[i] < nums[j], and nums[k] < nums[j]. If there exists at least one mountain triplet, then r equals the minimum of nums[i] + nums[j] + nums[k] over all mountain triplets; if there exists no mountain triplet, then r = -1.
    Preconditions: 3 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100000000. -/
  theorem spec_1 (nums : I64Slice)
      (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
      (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
      {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r) :
      (HasMountainTriplet nums → IsMinMountainSum nums r.val) ∧
        (¬ HasMountainTriplet nums → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : I64Slice)
        (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
        (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
        {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r), (HasMountainTriplet nums → IsMinMountainSum nums r.val) ∧
          (¬ HasMountainTriplet nums → r.val = -1)) := by
    sorry

  /-- The function returns a result r (it does not fail, overflow, panic, or go out of bounds) for every input satisfying the preconditions.
    Preconditions: 3 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100000000. -/
  theorem spec_2 (nums : I64Slice)
      (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
      (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000) :
      ∃ r : Std.I64, Aegis.MinimumSum.minimum_sum nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : I64Slice)
        (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
        (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000), ∃ r : Std.I64, Aegis.MinimumSum.minimum_sum nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 3 <= r <= 300000000.
    Preconditions: 3 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100000000. -/
  theorem spec_3 (nums : I64Slice)
      (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
      (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
      {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r) :
      r.val = -1 ∨ (3 ≤ r.val ∧ r.val ≤ 300000000) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : I64Slice)
        (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
        (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
        {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r), r.val = -1 ∨ (3 ≤ r.val ∧ r.val ≤ 300000000)) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or there exist indices i, j, k such that 0 <= i < j < k < len(nums), nums[i] < nums[j], nums[k] < nums[j], and r = nums[i] + nums[j] + nums[k].
    Preconditions: 3 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100000000. -/
  theorem spec_4 (nums : I64Slice)
      (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
      (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
      {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r) :
      r.val = -1 ∨
        ∃ i j k, IsMountainTriplet nums i j k ∧
          r.val = numAt nums i + numAt nums j + numAt nums k := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : I64Slice)
        (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
        (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
        {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r), r.val = -1 ∨
          ∃ i j k, IsMountainTriplet nums i j k ∧
            r.val = numAt nums i + numAt nums j + numAt nums k) := by
    sorry

  /-- Whenever the function returns a result r, if r = -1 then there do not exist indices i, j, k with 0 <= i < j < k < len(nums), nums[i] < nums[j], and nums[k] < nums[j].
    Preconditions: 3 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100000000. -/
  theorem spec_5 (nums : I64Slice)
      (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
      (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
      {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r) :
      r.val = -1 → ¬ HasMountainTriplet nums := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : I64Slice)
        (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
        (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
        {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r), r.val = -1 → ¬ HasMountainTriplet nums) := by
    sorry

  /-- Whenever the function returns a result r, if there do not exist indices i, j, k with 0 <= i < j < k < len(nums), nums[i] < nums[j], and nums[k] < nums[j], then r = -1.
    Preconditions: 3 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100000000. -/
  theorem spec_6 (nums : I64Slice)
      (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
      (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
      {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r) :
      ¬ HasMountainTriplet nums → r.val = -1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : I64Slice)
        (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
        (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
        {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r), ¬ HasMountainTriplet nums → r.val = -1) := by
    sorry

  /-- Whenever the function returns a result r, if r != -1 then for every triple of indices (i, j, k) with 0 <= i < j < k < len(nums), nums[i] < nums[j], and nums[k] < nums[j], we have r <= nums[i] + nums[j] + nums[k].
    Preconditions: 3 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100000000. -/
  theorem spec_7 (nums : I64Slice)
      (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
      (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
      {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r) :
      r.val ≠ -1 →
        ∀ i j k, IsMountainTriplet nums i j k →
          r.val ≤ numAt nums i + numAt nums j + numAt nums k := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : I64Slice)
        (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
        (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
        {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r), r.val ≠ -1 →
          ∀ i j k, IsMountainTriplet nums i j k →
            r.val ≤ numAt nums i + numAt nums j + numAt nums k) := by
    sorry

  /-- Whenever the function returns a result r, if len(nums) = 3, then: if nums[0] < nums[1] and nums[2] < nums[1], then r = nums[0] + nums[1] + nums[2]; otherwise r = -1.
    Preconditions: 3 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100000000. -/
  theorem spec_8 (nums : I64Slice)
      (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
      (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
      {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r) :
      numLen nums = 3 →
        (numAt nums 0 < numAt nums 1 ∧ numAt nums 2 < numAt nums 1 →
            r.val = numAt nums 0 + numAt nums 1 + numAt nums 2) ∧
          (¬ (numAt nums 0 < numAt nums 1 ∧ numAt nums 2 < numAt nums 1) → r.val = -1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : I64Slice)
        (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
        (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
        {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r), numLen nums = 3 →
          (numAt nums 0 < numAt nums 1 ∧ numAt nums 2 < numAt nums 1 →
              r.val = numAt nums 0 + numAt nums 1 + numAt nums 2) ∧
            (¬ (numAt nums 0 < numAt nums 1 ∧ numAt nums 2 < numAt nums 1) → r.val = -1)) := by
    sorry

  /-- Whenever the function returns a result r, if nums is strictly increasing (that is, nums[i] < nums[i+1] for every 0 <= i < len(nums)-1), then r = -1.
    Preconditions: 3 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100000000. -/
  theorem spec_9 (nums : I64Slice)
      (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
      (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
      {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r)
      (hincr : StrictlyIncreasing nums) :
      r.val = -1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : I64Slice)
        (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
        (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
        {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r)
        (hincr : StrictlyIncreasing nums), r.val = -1) := by
    sorry

  /-- Whenever the function returns a result r, if nums is strictly decreasing (that is, nums[i] > nums[i+1] for every 0 <= i < len(nums)-1), then r = -1.
    Preconditions: 3 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100000000. -/
  theorem spec_10 (nums : I64Slice)
      (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
      (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
      {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r)
      (hdecr : StrictlyDecreasing nums) :
      r.val = -1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : I64Slice)
        (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
        (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
        {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r)
        (hdecr : StrictlyDecreasing nums), r.val = -1) := by
    sorry

  /-- Whenever the function returns a result r, if all entries of nums are equal (that is, nums[i] = nums[0] for every 0 <= i < len(nums)), then r = -1.
    Preconditions: 3 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100000000. -/
  theorem spec_11 (nums : I64Slice)
      (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
      (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
      {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r)
      (heq : AllEqual nums) :
      r.val = -1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : I64Slice)
        (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
        (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
        {r : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r)
        (heq : AllEqual nums), r.val = -1) := by
    sorry

  /-- Let rev(nums) be the array of length len(nums) defined by rev(nums)[t] = nums[len(nums)-1-t] for every 0 <= t < len(nums). Whenever the function returns a result r on input nums and a result s on input rev(nums), r = s.
    Preconditions: 3 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100000000. -/
  theorem spec_12 (nums : I64Slice)
      (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
      (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
      (revs : I64Slice) (hrev : IsReverse revs nums)
      {r s : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r)
      (hres' : Aegis.MinimumSum.minimum_sum revs = ok s) :
      r = s := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : I64Slice)
        (hlen : 3 ≤ numLen nums) (hlen_bound : numLen nums ≤ 100000)
        (hvals : ∀ i, i < numLen nums → 1 ≤ numAt nums i ∧ numAt nums i ≤ 100000000)
        (revs : I64Slice) (hrev : IsReverse revs nums)
        {r s : Std.I64} (hres : Aegis.MinimumSum.minimum_sum nums = ok r)
        (hres' : Aegis.MinimumSum.minimum_sum revs = ok s), r = s) := by
    sorry

  end AegisSpec.MinimumSum
