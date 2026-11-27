import Aegis.SubarrayLcm.Code.Funs

/-!
# Specifications of `Aegis.SubarrayLcm.subarray_lcm`

LeetCode problem `number-of-subarrays-with-lcm-equal-to-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SubarrayLcm

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def segv (xs : List Int) (l h : Nat) : List Int := (xs.drop l).take (h - l + 1)

def IsLcmOf (l : List Int) (m : Int) : Prop :=
  0 < m ∧ (∀ x ∈ l, x ∣ m) ∧ ∀ m' : Int, 0 < m' → (∀ x ∈ l, x ∣ m') → m ≤ m'

def IsPrimeInt (p : Int) : Prop :=
  2 ≤ p ∧ ∀ d : Int, 0 < d → d ∣ p → d = 1 ∨ d = p

noncomputable def numPairs (n : Nat) (p : Nat → Nat → Prop) : Nat :=
  (((List.range n).product (List.range n)).filter
      (fun q : Nat × Nat =>
        @decide (q.1 ≤ q.2 ∧ p q.1 q.2) (Classical.propDecidable _))).length

noncomputable def numPairsIn (lo hi : Nat) (p : Nat → Nat → Prop) : Nat :=
  (((List.range (hi + 1)).product (List.range (hi + 1))).filter
      (fun q : Nat × Nat =>
        @decide (lo ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ hi ∧ p q.1 q.2)
          (Classical.propDecidable _))).length

def blocksFrom (xs : List Int) (k : Int) (start : Nat) : List (Nat × Nat) :=
  match xs with
  | [] => []
  | x :: xs =>
    if x ∣ k then
      match blocksFrom xs k (start + 1) with
      | (a, b) :: rest =>
        if a = start + 1 then (start, b) :: rest else (start, start) :: (a, b) :: rest
      | [] => [(start, start)]
    else blocksFrom xs k (start + 1)

def blocks (nums : List Int) (k : Int) : List (Nat × Nat) := blocksFrom nums k 0

def DiffersAtNondividing (nums nums' : Slice Std.I64) (k : Std.I64) (i0 : Nat) : Prop :=
  i0 < nums.val.length ∧
    (∀ j : Nat, j < nums.val.length → j ≠ i0 → (vals nums')[j]? = (vals nums)[j]?) ∧
    (∀ x : Int, (vals nums)[i0]? = some x → ¬ x ∣ k.val) ∧
    (∀ x : Int, (vals nums')[i0]? = some x → ¬ x ∣ k.val)

/-- The call subarray_lcm(nums,k) returns a result r, and r equals the number of pairs (l,h) of integers with 0 <= l <= h < len(nums) such that the least common multiple of the non-empty sequence nums[l], nums[l+1], ..., nums[h] is exactly k. Here the LCM of a non-empty sequence is the least positive integer divisible by every element of the sequence.
  Preconditions: len(nums) >= 1, len(nums) <= 1000, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 1000, and 1 <= k <= 1000. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r ∧
        r.val =
          (numPairs nums.val.length
              (fun l h => IsLcmOf (segv (vals nums) l h) k.val) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000), ∃ r : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r ∧
        r.val =
          (numPairs nums.val.length
              (fun l h => IsLcmOf (segv (vals nums) l h) k.val) : Int)) := by
  sorry

/-- For every nums and k satisfying the preconditions, subarray_lcm(nums,k) returns a result; it does not fail (no overflow, out-of-bounds, or panic).
  Preconditions: len(nums) >= 1, len(nums) <= 1000, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 1000, and 1 <= k <= 1000. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000) :
    ∃ r : Std.I64, Aegis.SubarrayLcm.subarray_lcm nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000), ∃ r : Std.I64, Aegis.SubarrayLcm.subarray_lcm nums k = ok r) := by
  sorry

/-- Whenever subarray_lcm(nums,k) returns a result r, 0 <= r.
  Preconditions: len(nums) >= 1, len(nums) <= 1000, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 1000, and 1 <= k <= 1000. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000) :
    ∀ r : Std.I64, Aegis.SubarrayLcm.subarray_lcm nums k = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000), ∀ r : Std.I64, Aegis.SubarrayLcm.subarray_lcm nums k = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever subarray_lcm(nums,k) returns a result r, r <= n*(n+1)/2, where n = len(nums).
  Preconditions: len(nums) >= 1, len(nums) <= 1000, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 1000, and 1 <= k <= 1000. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000) :
    ∀ r : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        r.val ≤ (↑(nums.val.length * (nums.val.length + 1) / 2) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000), ∀ r : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        r.val ≤ (↑(nums.val.length * (nums.val.length + 1) / 2) : Int)) := by
  sorry

/-- Whenever subarray_lcm(nums,k) returns a result r, r <= D, where D is the number of pairs (l,h) with 0 <= l <= h < len(nums) such that nums[i] divides k for every i with l <= i <= h.
  Preconditions: len(nums) >= 1, len(nums) <= 1000, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 1000, and 1 <= k <= 1000. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000) :
    ∀ r : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        r.val ≤
          (numPairs nums.val.length
              (fun l h => ∀ x ∈ segv (vals nums) l h, x ∣ k.val) : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000), ∀ r : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        r.val ≤
          (numPairs nums.val.length
              (fun l h => ∀ x ∈ segv (vals nums) l h, x ∣ k.val) : Int)) := by
  sorry

/-- Whenever subarray_lcm(nums,k) returns a result r, r = 0.
  Preconditions: len(nums) >= 1, len(nums) <= 1000, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 1000, 1 <= k <= 1000, and for every i with 0 <= i < len(nums), nums[i] does not divide k. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
    (hnd : ∀ x ∈ vals nums, ¬ x ∣ k.val) :
    ∀ r : Std.I64, Aegis.SubarrayLcm.subarray_lcm nums k = ok r → r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
    (hnd : ∀ x ∈ vals nums, ¬ x ∣ k.val), ∀ r : Std.I64, Aegis.SubarrayLcm.subarray_lcm nums k = ok r → r.val = 0) := by
  sorry

/-- Whenever subarray_lcm(nums,k) returns a result r, r = 1 if nums[0] = k, and r = 0 if nums[0] != k.
  Preconditions: len(nums) >= 1, len(nums) <= 1000, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 1000, 1 <= k <= 1000, and len(nums) = 1. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
    (hlen : nums.val.length = 1) :
    ∀ r : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        r.val = if vals nums = [k.val] then 1 else 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
    (hlen : nums.val.length = 1), ∀ r : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        r.val = if vals nums = [k.val] then 1 else 0) := by
  sorry

/-- Whenever subarray_lcm(nums,k) returns a result r, r = n*(n+1)/2, where n = len(nums).
  Preconditions: len(nums) >= 1, len(nums) <= 1000, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 1000, 1 <= k <= 1000, and for every i with 0 <= i < len(nums), nums[i] = k. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
    (hall : ∀ x ∈ vals nums, x = k.val) :
    ∀ r : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        r.val = (↑(nums.val.length * (nums.val.length + 1) / 2) : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
    (hall : ∀ x ∈ vals nums, x = k.val), ∀ r : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        r.val = (↑(nums.val.length * (nums.val.length + 1) / 2) : Int)) := by
  sorry

/-- Whenever subarray_lcm(nums,k) returns a result r, r equals the number of pairs (l,h) with 0 <= l <= h < len(nums) such that nums[i] = 1 for every i with l <= i <= h. Equivalently, if the maximal contiguous runs of indices i with nums[i] = 1 have lengths a_1, ..., a_m (and m = 0 if there are none), then r = sum_{j=1..m} a_j*(a_j+1)/2.
  Preconditions: len(nums) >= 1, len(nums) <= 1000, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 1000, and k = 1. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk : k.val = 1) :
    ∀ r : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        r.val =
          (numPairs nums.val.length
              (fun l h => ∀ x ∈ segv (vals nums) l h, x = 1) : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk : k.val = 1), ∀ r : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        r.val =
          (numPairs nums.val.length
              (fun l h => ∀ x ∈ segv (vals nums) l h, x = 1) : Int)) := by
  sorry

/-- Whenever subarray_lcm(nums,k) returns a result r, r equals the number of pairs (l,h) with 0 <= l <= h < len(nums) such that for every i with l <= i <= h, nums[i] is either 1 or k, and there exists i with l <= i <= h and nums[i] = k.
  Preconditions: len(nums) >= 1, len(nums) <= 1000, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 1000, and k is prime with 1 <= k <= 1000. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
    (hkp : IsPrimeInt k.val) :
    ∀ r : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        r.val =
          (numPairs nums.val.length
              (fun l h =>
                (∀ x ∈ segv (vals nums) l h, x = 1 ∨ x = k.val) ∧
                  ∃ i : Nat, l ≤ i ∧ i ≤ h ∧ (vals nums)[i]? = some k.val) : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
    (hkp : IsPrimeInt k.val), ∀ r : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        r.val =
          (numPairs nums.val.length
              (fun l h =>
                (∀ x ∈ segv (vals nums) l h, x = 1 ∨ x = k.val) ∧
                  ∃ i : Nat, l ≤ i ∧ i ≤ h ∧ (vals nums)[i]? = some k.val) : Int)) := by
  sorry

/-- Whenever subarray_lcm(nums,k) returns a result r, let [a_1,b_1], ..., [a_m,b_m] be the maximal intervals of indices such that 0 <= a_j <= b_j < len(nums) and nums[i] divides k for every i with a_j <= i <= b_j. Then r = sum_{j=1..m} c_j, where c_j is the number of pairs (l,h) with a_j <= l <= h <= b_j such that the LCM of nums[l], ..., nums[h] is k. If m = 0, the sum is 0.
  Preconditions: len(nums) >= 1, len(nums) <= 1000, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 1000, and 1 <= k <= 1000. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000) :
    ∀ r : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        r.val =
          (↑(((blocks (vals nums) k.val).map
                (fun p : Nat × Nat =>
                  numPairsIn p.1 p.2
                    (fun l h => IsLcmOf (segv (vals nums) l h) k.val))).sum) : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000), ∀ r : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        r.val =
          (↑(((blocks (vals nums) k.val).map
                (fun p : Nat × Nat =>
                  numPairsIn p.1 p.2
                    (fun l h => IsLcmOf (segv (vals nums) l h) k.val))).sum) : Int)) := by
  sorry

/-- For every nums and k satisfying the preconditions, whenever subarray_lcm(nums,k) returns r and subarray_lcm(reverse(nums),k) returns r', where reverse(nums) is the slice with entries nums[n-1], ..., nums[0] and n = len(nums), we have r = r'.
  Preconditions: len(nums) >= 1, len(nums) <= 1000, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 1000, and 1 <= k <= 1000. -/
theorem spec_12 (nums rev : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
    (hrev : rev.val = nums.val.reverse) :
    ∀ r r' : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        Aegis.SubarrayLcm.subarray_lcm rev k = ok r' → r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums rev : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
    (hrev : rev.val = nums.val.reverse), ∀ r r' : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        Aegis.SubarrayLcm.subarray_lcm rev k = ok r' → r = r') := by
  sorry

/-- Whenever subarray_lcm(nums,k) returns r and subarray_lcm(nums',k) returns r', we have r = r'.
  Preconditions: len(nums) >= 1, len(nums) <= 1000, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 1000, and 1 <= k <= 1000. Also nums' is a slice with len(nums') = len(nums), for every i with 0 <= i < len(nums') we have 1 <= nums'[i] <= 1000, and there exists an index i0 with 0 <= i0 < len(nums) such that nums'[j] = nums[j] for every j != i0, while nums[i0] does not divide k and nums'[i0] does not divide k. -/
theorem spec_13 (nums nums' : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
    (hnd : nums'.val.length = nums.val.length)
    (hnum' : ∀ x ∈ vals nums', 1 ≤ x ∧ x ≤ 1000)
    (hdiff : ∃ i0 : Nat, DiffersAtNondividing nums nums' k i0) :
    ∀ r r' : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        Aegis.SubarrayLcm.subarray_lcm nums' k = ok r' → r = r' := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
    (hnd : nums'.val.length = nums.val.length)
    (hnum' : ∀ x ∈ vals nums', 1 ≤ x ∧ x ≤ 1000)
    (hdiff : ∃ i0 : Nat, DiffersAtNondividing nums nums' k i0), ∀ r r' : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        Aegis.SubarrayLcm.subarray_lcm nums' k = ok r' → r = r') := by
  sorry

/-- Whenever subarray_lcm(nums,k) returns a result r, r > 0 if and only if there exist integers l,h with 0 <= l <= h < len(nums) such that the LCM of nums[l], ..., nums[h] is exactly k, where the LCM of a non-empty sequence is the least positive integer divisible by every element of that sequence.
  Preconditions: len(nums) >= 1, len(nums) <= 1000, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 1000, and 1 <= k <= 1000. -/
theorem spec_14 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000) :
    ∀ r : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        (0 < r.val ↔
          ∃ l h : Nat, l ≤ h ∧ h < nums.val.length ∧
            IsLcmOf (segv (vals nums) l h) k.val) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
    (hnum : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000), ∀ r : Std.I64,
      Aegis.SubarrayLcm.subarray_lcm nums k = ok r →
        (0 < r.val ↔
          ∃ l h : Nat, l ≤ h ∧ h < nums.val.length ∧
            IsLcmOf (segv (vals nums) l h) k.val)) := by
  sorry

end AegisSpec.SubarrayLcm
