import Aegis.UnequalTriplets.Code.Funs

/-!
# Specifications of `Aegis.UnequalTriplets.unequal_triplets`

LeetCode problem `number-of-unequal-triplets-in-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.UnequalTriplets

  namespace AegisSpec.UnequalTriplets

  def cnt (l : List Std.I64) (v : ℤ) : ℕ := (l.filter (fun x => x.val = v)).length

  def valSet (l : List Std.I64) : Finset ℤ := (l.map fun x => x.val).toFinset

  def numUnequalTriples (l : List Std.I64) : ℕ :=
    ((Finset.univ : Finset (Fin l.length × Fin l.length × Fin l.length)).filter
      (fun t =>
        t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
        (l.get t.1).val ≠ (l.get t.2.1).val ∧
        (l.get t.1).val ≠ (l.get t.2.2).val ∧
        (l.get t.2.1).val ≠ (l.get t.2.2).val)).card

  def numPairsAvoiding (l : List Std.I64) (x : ℤ) : ℕ :=
    ((Finset.univ : Finset (Fin l.length × Fin l.length)).filter
      (fun t =>
        t.1 < t.2 ∧
        (l.get t.1).val ≠ (l.get t.2).val ∧
        (l.get t.1).val ≠ x ∧
        (l.get t.2).val ≠ x)).card

  def numIndexTriples (n : ℕ) : ℤ := ((n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2)) / 6

  /-- The call returns a result r and r is exactly the number of triples (i,j,k) of indices such that 0 <= i < j < k < len(nums), nums[i] != nums[j], nums[i] != nums[k], and nums[j] != nums[k].
    Preconditions: 3 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hb : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∃ r : Std.I64, unequal_triplets nums = ok r ∧
        r.val = (numUnequalTriples nums.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hb : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∃ r : Std.I64, unequal_triplets nums = ok r ∧
          r.val = (numUnequalTriples nums.val : ℤ)) := by
    sorry

  /-- The call returns a result r and does not fail: there is no arithmetic overflow, out-of-bounds access, or panic for any input satisfying the preconditions.
    Preconditions: 3 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hb : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∃ r : Std.I64, unequal_triplets nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hb : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∃ r : Std.I64, unequal_triplets nums = ok r) := by
    sorry

  /-- The call returns a result r and 0 <= r <= (len(nums)*(len(nums)-1)*(len(nums)-2))/6.
    Preconditions: 3 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hb : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∃ r : Std.I64, unequal_triplets nums = ok r ∧
        0 ≤ r.val ∧ r.val ≤ numIndexTriples nums.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hb : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∃ r : Std.I64, unequal_triplets nums = ok r ∧
          0 ≤ r.val ∧ r.val ≤ numIndexTriples nums.val.length) := by
    sorry

  /-- If there is a value c such that nums[i] = c for every i with 0 <= i < len(nums), then the call returns r = 0.
    Preconditions: 3 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hb : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      (∃ c : ℤ, ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]).val = c) →
        ∃ r : Std.I64, unequal_triplets nums = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hb : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), (∃ c : ℤ, ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]).val = c) →
          ∃ r : Std.I64, unequal_triplets nums = ok r ∧ r.val = 0) := by
    sorry

  /-- If nums[i] != nums[j] for every pair of indices with 0 <= i < j < len(nums), then the call returns r = (len(nums)*(len(nums)-1)*(len(nums)-2))/6.
    Preconditions: 3 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hb : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      (∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
          i < j → (nums.val[i]).val ≠ (nums.val[j]).val) →
        ∃ r : Std.I64, unequal_triplets nums = ok r ∧
          r.val = numIndexTriples nums.val.length := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hb : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), (∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
            i < j → (nums.val[i]).val ≠ (nums.val[j]).val) →
          ∃ r : Std.I64, unequal_triplets nums = ok r ∧
            r.val = numIndexTriples nums.val.length) := by
    sorry

  /-- If len(nums) = 3, then the call returns r = 1 when nums[0], nums[1], nums[2] are pairwise distinct (nums[0] != nums[1], nums[0] != nums[2], and nums[1] != nums[2]), and returns r = 0 otherwise.
    Preconditions: 3 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hb : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (h3 : nums.val.length = 3) :
      (((nums.val[0]).val ≠ (nums.val[1]).val ∧
        (nums.val[0]).val ≠ (nums.val[2]).val ∧
        (nums.val[1]).val ≠ (nums.val[2]).val) →
        ∃ r : Std.I64, unequal_triplets nums = ok r ∧ r.val = 1) ∧
      (¬ ((nums.val[0]).val ≠ (nums.val[1]).val ∧
        (nums.val[0]).val ≠ (nums.val[2]).val ∧
        (nums.val[1]).val ≠ (nums.val[2]).val) →
        ∃ r : Std.I64, unequal_triplets nums = ok r ∧ r.val = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hb : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (h3 : nums.val.length = 3), (((nums.val[0]).val ≠ (nums.val[1]).val ∧
          (nums.val[0]).val ≠ (nums.val[2]).val ∧
          (nums.val[1]).val ≠ (nums.val[2]).val) →
          ∃ r : Std.I64, unequal_triplets nums = ok r ∧ r.val = 1) ∧
        (¬ ((nums.val[0]).val ≠ (nums.val[1]).val ∧
          (nums.val[0]).val ≠ (nums.val[2]).val ∧
          (nums.val[1]).val ≠ (nums.val[2]).val) →
          ∃ r : Std.I64, unequal_triplets nums = ok r ∧ r.val = 0)) := by
    sorry

  /-- The call returns r and, if the set {nums[i] | 0 <= i < len(nums)} has at least three elements, then r > 0.
    Preconditions: 3 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hb : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∃ r : Std.I64, unequal_triplets nums = ok r ∧
        (3 ≤ (valSet nums.val).card → 0 < r.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hb : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∃ r : Std.I64, unequal_triplets nums = ok r ∧
          (3 ≤ (valSet nums.val).card → 0 < r.val)) := by
    sorry

  /-- The call returns r and, defining cnt(v) to be the number of indices i with 0 <= i < len(nums) and nums[i] = v, r = sum over all 1 <= a < b < c <= 1000 of cnt(a)*cnt(b)*cnt(c).
    Preconditions: 3 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hb : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∃ r : Std.I64, unequal_triplets nums = ok r ∧
        r.val = ∑ a ∈ (Finset.Icc 1 1000 : Finset ℕ), ∑ b ∈ Finset.Icc (a + 1) 1000,
          ∑ c ∈ Finset.Icc (b + 1) 1000,
            (((cnt nums.val (a : ℤ) * cnt nums.val (b : ℤ) * cnt nums.val (c : ℤ) : ℕ)) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hb : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∃ r : Std.I64, unequal_triplets nums = ok r ∧
          r.val = ∑ a ∈ (Finset.Icc 1 1000 : Finset ℕ), ∑ b ∈ Finset.Icc (a + 1) 1000,
            ∑ c ∈ Finset.Icc (b + 1) 1000,
              (((cnt nums.val (a : ℤ) * cnt nums.val (b : ℤ) * cnt nums.val (c : ℤ) : ℕ)) : ℤ)) := by
    sorry

  /-- If r is the result of the call on nums and r2 is the result of the call on nums2, then r2 = r.
    Preconditions: 3 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; nums2 is a slice with 3 <= len(nums2) <= 100; for every i with 0 <= i < len(nums2), 1 <= nums2[i] <= 1000; len(nums2) = len(nums); and for every v with 1 <= v <= 1000, the number of indices i with nums[i] = v equals the number of indices i with nums2[i] = v. -/
  theorem spec_9 (nums nums2 : Slice Std.I64) (hlo : 3 ≤ nums.val.length)
      (hhi : nums.val.length ≤ 100)
      (hb : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hlo2 : 3 ≤ nums2.val.length) (hhi2 : nums2.val.length ≤ 100)
      (hb2 : ∀ (i : Nat) (hi : i < nums2.val.length),
        1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 1000)
      (hlen : nums2.val.length = nums.val.length)
      (hcnt : ∀ v : ℤ, 1 ≤ v → v ≤ 1000 → cnt nums.val v = cnt nums2.val v) :
      ∀ (r r2 : Std.I64), unequal_triplets nums = ok r →
        unequal_triplets nums2 = ok r2 → r2 = r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (hlo : 3 ≤ nums.val.length)
        (hhi : nums.val.length ≤ 100)
        (hb : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hlo2 : 3 ≤ nums2.val.length) (hhi2 : nums2.val.length ≤ 100)
        (hb2 : ∀ (i : Nat) (hi : i < nums2.val.length),
          1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 1000)
        (hlen : nums2.val.length = nums.val.length)
        (hcnt : ∀ v : ℤ, 1 ≤ v → v ≤ 1000 → cnt nums.val v = cnt nums2.val v), ∀ (r r2 : Std.I64), unequal_triplets nums = ok r →
          unequal_triplets nums2 = ok r2 → r2 = r) := by
    sorry

  /-- Let nums2 be the slice of length len(nums)+1 with nums2[i] = nums[i] for 0 <= i < len(nums) and nums2[len(nums)] = x. Let r be the result of the call on nums and r2 the result of the call on nums2. Let P be the number of pairs (i,j) with 0 <= i < j < len(nums) such that nums[i] != nums[j], nums[i] != x, and nums[j] != x. Then r2 = r + P.
    Preconditions: 3 <= len(nums) <= 99; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; and 1 <= x <= 1000. -/
  theorem spec_10 (nums nums2 : Slice Std.I64) (x : ℤ) (y : Std.I64)
      (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 99)
      (hb : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hx1 : 1 ≤ x) (hx2 : x ≤ 1000)
      (hy : y.val = x) (hnums2 : nums2.val = nums.val ++ [y]) :
      ∀ (r r2 : Std.I64), unequal_triplets nums = ok r →
        unequal_triplets nums2 = ok r2 →
          r2.val = r.val + (numPairsAvoiding nums.val x : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (x : ℤ) (y : Std.I64)
        (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 99)
        (hb : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hx1 : 1 ≤ x) (hx2 : x ≤ 1000)
        (hy : y.val = x) (hnums2 : nums2.val = nums.val ++ [y]), ∀ (r r2 : Std.I64), unequal_triplets nums = ok r →
          unequal_triplets nums2 = ok r2 →
            r2.val = r.val + (numPairsAvoiding nums.val x : ℤ)) := by
    sorry

  /-- The call returns r and r = 0 if and only if the set {nums[i] | 0 <= i < len(nums)} has at most two elements.
    Preconditions: 3 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hb : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∃ r : Std.I64, unequal_triplets nums = ok r ∧
        (r.val = 0 ↔ (valSet nums.val).card ≤ 2) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hb : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∃ r : Std.I64, unequal_triplets nums = ok r ∧
          (r.val = 0 ↔ (valSet nums.val).card ≤ 2)) := by
    sorry

  /-- The call returns r and r = (len(nums)*(len(nums)-1)*(len(nums)-2))/6 if and only if nums[i] != nums[j] for every pair of indices with 0 <= i < j < len(nums).
    Preconditions: 3 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hb : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000) :
      ∃ r : Std.I64, unequal_triplets nums = ok r ∧
        (r.val = numIndexTriples nums.val.length ↔
          ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
            i < j → (nums.val[i]).val ≠ (nums.val[j]).val) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hb : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000), ∃ r : Std.I64, unequal_triplets nums = ok r ∧
          (r.val = numIndexTriples nums.val.length ↔
            ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
              i < j → (nums.val[i]).val ≠ (nums.val[j]).val)) := by
    sorry

  end AegisSpec.UnequalTriplets
