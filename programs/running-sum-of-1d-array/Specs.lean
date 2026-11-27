import Aegis.RunningSum.Code.Funs

/-!
# Specifications of `Aegis.RunningSum.running_sum`

LeetCode problem `running-sum-of-1d-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.RunningSum

def sliceVals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def vecVals (v : alloc.vec.Vec Std.I64) : List ℤ := v.slice.val.map (fun x => x.val)

def vecLen (v : alloc.vec.Vec Std.I64) : ℕ := v.slice.val.length

def nthD (xs : List ℤ) (j : ℕ) : ℤ := (xs[j]?).getD 0

theorem nthD_of_lt {xs : List ℤ} {j : ℕ} (h : j < xs.length) : nthD xs j = xs[j]'h := by
  simp [nthD, List.getElem?_eq_getElem h]

def prefixSum (nums : Slice Std.I64) (j : ℕ) : ℤ := ((sliceVals nums).take j).sum

def segSum (nums : Slice Std.I64) (a b : ℕ) : ℤ := (((sliceVals nums).drop a).take (b - a)).sum

def sliceMin (nums : Slice Std.I64) : ℤ := ((sliceVals nums).min?).getD 0

def sliceMax (nums : Slice Std.I64) : ℤ := ((sliceVals nums).max?).getD 0

/-- Whenever the function returns a result r, then for every j with 0 ≤ j < len(nums) it holds that j < len(r) and r[j] equals the sum of nums[k] for k = 0, 1, ..., j.
  Preconditions: 1 ≤ len(nums) ≤ 1000, and for every i with 0 ≤ i < len(nums), -10^6 ≤ nums[i] ≤ 10^6. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
    (hbounds : ∀ i (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000) :
    ∀ r, Aegis.RunningSum.running_sum nums = ok r →
      ∀ j, j < nums.val.length →
        j < vecLen r ∧ nthD (vecVals r) j = prefixSum nums (j + 1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
    (hbounds : ∀ i (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000), ∀ r, Aegis.RunningSum.running_sum nums = ok r →
      ∀ j, j < nums.val.length →
        j < vecLen r ∧ nthD (vecVals r) j = prefixSum nums (j + 1)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail (no integer overflow, no out-of-bounds access, no panic).
  Preconditions: 1 ≤ len(nums) ≤ 1000, and for every i with 0 ≤ i < len(nums), -10^6 ≤ nums[i] ≤ 10^6. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
    (hbounds : ∀ i (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000) :
    ∃ r, Aegis.RunningSum.running_sum nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
    (hbounds : ∀ i (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000), ∃ r, Aegis.RunningSum.running_sum nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(nums).
  Preconditions: 1 ≤ len(nums) ≤ 1000, and for every i with 0 ≤ i < len(nums), -10^6 ≤ nums[i] ≤ 10^6. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
    (hbounds : ∀ i (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000) :
    ∀ r, Aegis.RunningSum.running_sum nums = ok r → vecLen r = nums.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
    (hbounds : ∀ i (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000), ∀ r, Aegis.RunningSum.running_sum nums = ok r → vecLen r = nums.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every pair of indices i, j with 0 ≤ i ≤ j < len(nums) and j < len(r), r[j] - r[i] = the sum of nums[k] for k = i+1, ..., j (this sum is 0 when i = j).
  Preconditions: 1 ≤ len(nums) ≤ 1000, and for every i with 0 ≤ i < len(nums), -10^6 ≤ nums[i] ≤ 10^6. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
    (hbounds : ∀ i (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000) :
    ∀ r, Aegis.RunningSum.running_sum nums = ok r →
      ∀ i j, i ≤ j → j < nums.val.length → j < vecLen r →
        nthD (vecVals r) j - nthD (vecVals r) i = segSum nums (i + 1) (j + 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
    (hbounds : ∀ i (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000), ∀ r, Aegis.RunningSum.running_sum nums = ok r →
      ∀ i j, i ≤ j → j < nums.val.length → j < vecLen r →
        nthD (vecVals r) j - nthD (vecVals r) i = segSum nums (i + 1) (j + 1)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(nums) = n, the sum of r[j] over j = 0, ..., n-1 equals the sum of (n - i) · nums[i] over i = 0, ..., n-1.
  Preconditions: 1 ≤ len(nums) ≤ 1000, and for every i with 0 ≤ i < len(nums), -10^6 ≤ nums[i] ≤ 10^6. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
    (hbounds : ∀ i (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000) :
    ∀ r, Aegis.RunningSum.running_sum nums = ok r → ∀ n, vecLen r = n → nums.val.length = n →
      ((List.range n).map (fun (j : ℕ) => nthD (vecVals r) j)).sum
        = ((List.range n).map (fun (i : ℕ) => ((n : ℤ) - (i : ℤ)) *
            nthD (sliceVals nums) i)).sum := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
    (hbounds : ∀ i (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000), ∀ r, Aegis.RunningSum.running_sum nums = ok r → ∀ n, vecLen r = n → nums.val.length = n →
      ((List.range n).map (fun (j : ℕ) => nthD (vecVals r) j)).sum
        = ((List.range n).map (fun (i : ℕ) => ((n : ℤ) - (i : ℤ)) *
            nthD (sliceVals nums) i)).sum) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(nums), if nums[i] ≥ 0 for every i with 0 ≤ i < len(nums), then r[j] ≤ r[j+1] for every j with 0 ≤ j < len(r) - 1.
  Preconditions: 1 ≤ len(nums) ≤ 1000, and for every i with 0 ≤ i < len(nums), -10^6 ≤ nums[i] ≤ 10^6. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
    (hbounds : ∀ i (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000) :
    ∀ r, Aegis.RunningSum.running_sum nums = ok r → vecLen r = nums.val.length →
      (∀ i (hi : i < nums.val.length), 0 ≤ (nums.val[i]'hi).val) →
        ∀ j, j < vecLen r - 1 → nthD (vecVals r) j ≤ nthD (vecVals r) (j + 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
    (hbounds : ∀ i (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000), ∀ r, Aegis.RunningSum.running_sum nums = ok r → vecLen r = nums.val.length →
      (∀ i (hi : i < nums.val.length), 0 ≤ (nums.val[i]'hi).val) →
        ∀ j, j < vecLen r - 1 → nthD (vecVals r) j ≤ nthD (vecVals r) (j + 1)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(nums), if nums[i] ≤ 0 for every i with 0 ≤ i < len(nums), then r[j] ≥ r[j+1] for every j with 0 ≤ j < len(r) - 1.
  Preconditions: 1 ≤ len(nums) ≤ 1000, and for every i with 0 ≤ i < len(nums), -10^6 ≤ nums[i] ≤ 10^6. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
    (hbounds : ∀ i (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000) :
    ∀ r, Aegis.RunningSum.running_sum nums = ok r → vecLen r = nums.val.length →
      (∀ i (hi : i < nums.val.length), (nums.val[i]'hi).val ≤ 0) →
        ∀ j, j < vecLen r - 1 → nthD (vecVals r) j ≥ nthD (vecVals r) (j + 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
    (hbounds : ∀ i (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000), ∀ r, Aegis.RunningSum.running_sum nums = ok r → vecLen r = nums.val.length →
      (∀ i (hi : i < nums.val.length), (nums.val[i]'hi).val ≤ 0) →
        ∀ j, j < vecLen r - 1 → nthD (vecVals r) j ≥ nthD (vecVals r) (j + 1)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = len(nums), letting mn = min over 0 ≤ i < len(nums) of nums[i] and mx = max over 0 ≤ i < len(nums) of nums[i], for every j with 0 ≤ j < len(nums), (j + 1) · mn ≤ r[j] ≤ (j + 1) · mx.
  Preconditions: 1 ≤ len(nums) ≤ 1000, and for every i with 0 ≤ i < len(nums), -10^6 ≤ nums[i] ≤ 10^6. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
    (hbounds : ∀ i (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000) :
    ∀ r, Aegis.RunningSum.running_sum nums = ok r → vecLen r = nums.val.length →
      ∀ j, j < nums.val.length →
        ((j : ℤ) + 1) * sliceMin nums ≤ nthD (vecVals r) j ∧
          nthD (vecVals r) j ≤ ((j : ℤ) + 1) * sliceMax nums := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
    (hbounds : ∀ i (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000), ∀ r, Aegis.RunningSum.running_sum nums = ok r → vecLen r = nums.val.length →
      ∀ j, j < nums.val.length →
        ((j : ℤ) + 1) * sliceMin nums ≤ nthD (vecVals r) j ∧
          nthD (vecVals r) j ≤ ((j : ℤ) + 1) * sliceMax nums) := by
  sorry

end AegisSpec.RunningSum
