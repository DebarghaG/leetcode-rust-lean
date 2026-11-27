import Aegis.SumOfUnique.Code.Funs

/-!
# Specifications of `Aegis.SumOfUnique.sum_of_unique`

LeetCode problem `sum-of-unique-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SumOfUnique

  def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def occ (nums : Slice Std.I64) (v : Int) : Nat :=
    (vals nums).countP (fun x => decide (x = v))

  def occurring (nums : Slice Std.I64) : Finset Int := (vals nums).toFinset

  def sumOccGe (nums : Slice Std.I64) (k : Nat) : Int :=
    ((occurring nums).filter (fun v => k ≤ occ nums v)).sum id

  def uniqSum (nums : Slice Std.I64) : Int :=
    ((occurring nums).filter (fun v => occ nums v = 1)).sum id

  def uniqCount (nums : Slice Std.I64) : Nat :=
    ((occurring nums).filter (fun v => occ nums v = 1)).card

  def total (nums : Slice Std.I64) : Int := (vals nums).sum

  /-- The function returns a result r. For each integer v, let occ(nums,v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. Then r is the sum of all integers v such that occ(nums,v) = 1.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100) :
      ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r ∧ r.val = uniqSum nums := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100), ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r ∧ r.val = uniqSum nums) := by
    sorry

  /-- The function returns a result r; in particular, it does not panic, fail, access out of bounds, or overflow.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100) :
      ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100), ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r) := by
    sorry

  /-- The function returns a result r and r >= 0.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100) :
      ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r ∧ 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100), ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r ∧ 0 ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= sum_{i=0}^{len(nums)-1} nums[i], the sum of all entries of nums.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100) :
      ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r ∧ r.val ≤ total nums := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100), ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r ∧ r.val ≤ total nums) := by
    sorry

  /-- The function returns a result r. For each integer v, let occ(nums,v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. Then r = 0 if and only if occ(nums,v) != 1 for every integer v.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100) :
      ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r ∧
        (r.val = 0 ↔ ∀ v : Int, occ nums v ≠ 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100), ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r ∧
          (r.val = 0 ↔ ∀ v : Int, occ nums v ≠ 1)) := by
    sorry

  /-- The function returns a result r. For each integer v, let occ(nums,v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. Then r = (sum of all integers v with occ(nums,v) >= 1 of v) - (sum of all integers v with occ(nums,v) >= 2 of v).
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100) :
      ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r ∧
        r.val = sumOccGe nums 1 - sumOccGe nums 2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100), ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r ∧
          r.val = sumOccGe nums 1 - sumOccGe nums 2) := by
    sorry

  /-- The function returns a result r. For each integer v, let occ(nums,v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. For every slice nums2 with 1 <= len(nums2) <= 100 and 1 <= nums2[j] <= 100 for all 0 <= j < len(nums2), if occ(nums2,v) = occ(nums,v) for every integer v, then the call sum_of_unique(nums2) returns a result r2 with r2 = r.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100) :
      ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r ∧
        ∀ nums2 : Slice Std.I64,
          1 ≤ nums2.val.length →
          nums2.val.length ≤ 100 →
          (∀ x ∈ nums2.val, 1 ≤ x.val ∧ x.val ≤ 100) →
          (∀ v : Int, occ nums2 v = occ nums v) →
          ∃ r2, Aegis.SumOfUnique.sum_of_unique nums2 = ok r2 ∧ r2.val = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100), ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r ∧
          ∀ nums2 : Slice Std.I64,
            1 ≤ nums2.val.length →
            nums2.val.length ≤ 100 →
            (∀ x ∈ nums2.val, 1 ≤ x.val ∧ x.val ≤ 100) →
            (∀ v : Int, occ nums2 v = occ nums v) →
            ∃ r2, Aegis.SumOfUnique.sum_of_unique nums2 = ok r2 ∧ r2.val = r.val) := by
    sorry

  /-- The function returns a result r. For each integer v, let occ(nums,v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. For every integer v with occ(nums,v) = 1, we have v <= r.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100) :
      ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r ∧
        ∀ v : Int, occ nums v = 1 → v ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100), ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r ∧
          ∀ v : Int, occ nums v = 1 → v ≤ r.val) := by
    sorry

  /-- The function returns a result r. For each integer v, let occ(nums,v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. Let U be the number of integers v with occ(nums,v) = 1. Then r <= 100 * U.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100) :
      ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r ∧
        r.val ≤ 100 * (uniqCount nums : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100), ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r ∧
          r.val ≤ 100 * (uniqCount nums : Int)) := by
    sorry

  /-- The function returns a result r. For each integer v, let occ(nums,v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v. For every integer v with 1 <= v <= 100 and every slice nums2 with len(nums2) = len(nums) + 1, len(nums2) <= 100, nums2[i] = nums[i] for every 0 <= i < len(nums), and nums2[len(nums)] = v, the call sum_of_unique(nums2) returns a result r2, and r2 = r + v if occ(nums,v) = 0, r2 = r - v if occ(nums,v) = 1, and r2 = r if occ(nums,v) >= 2.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100) :
      ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r ∧
        ∀ (v : Int) (nums2 : Slice Std.I64),
          1 ≤ v → v ≤ 100 →
          nums2.val.length = nums.val.length + 1 →
          nums2.val.length ≤ 100 →
          (vals nums2).take nums.val.length = vals nums →
          (vals nums2)[nums.val.length]? = some v →
          ∃ r2, Aegis.SumOfUnique.sum_of_unique nums2 = ok r2 ∧
            (occ nums v = 0 → r2.val = r.val + v) ∧
            (occ nums v = 1 → r2.val = r.val - v) ∧
            (2 ≤ occ nums v → r2.val = r.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (helem : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100), ∃ r, Aegis.SumOfUnique.sum_of_unique nums = ok r ∧
          ∀ (v : Int) (nums2 : Slice Std.I64),
            1 ≤ v → v ≤ 100 →
            nums2.val.length = nums.val.length + 1 →
            nums2.val.length ≤ 100 →
            (vals nums2).take nums.val.length = vals nums →
            (vals nums2)[nums.val.length]? = some v →
            ∃ r2, Aegis.SumOfUnique.sum_of_unique nums2 = ok r2 ∧
              (occ nums v = 0 → r2.val = r.val + v) ∧
              (occ nums v = 1 → r2.val = r.val - v) ∧
              (2 ≤ occ nums v → r2.val = r.val)) := by
    sorry

  end AegisSpec.SumOfUnique
