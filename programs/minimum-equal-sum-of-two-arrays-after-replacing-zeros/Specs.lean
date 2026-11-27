import Aegis.MinSum.Code.Funs

/-!
# Specifications of `Aegis.MinSum.min_sum`

LeetCode problem `minimum-equal-sum-of-two-arrays-after-replacing-zeros`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AegisSpec.MinSum

def vals (s : Slice I64) : List ℤ := s.list.toList.map (fun x => (x : ℤ))

def zeros (s : Slice I64) : ℤ := (((vals s).filter (fun x => x = 0)).length : ℤ)

def total (s : Slice I64) : ℤ := (vals s).sum

def Fills (u : List ℤ) (s : Slice I64) : Prop :=
  u.length = s.leng ∧
    List.Forall₂ (fun a b => (b ≠ 0 → a = b) ∧ (b = 0 → 0 < a)) u (vals s)

/-- Let z1 be the number of indices i with 0 <= i < len(nums1) and nums1[i] = 0, and let b1 = sum_{0 <= i < len(nums1)} nums1[i]. Let z2 be the number of indices j with 0 <= j < len(nums2) and nums2[j] = 0, and let b2 = sum_{0 <= j < len(nums2)} nums2[j]. The function returns a result r and: (1) if z1 = 0 and z2 = 0, then r = b1 when b1 = b2, and r = -1 when b1 != b2; (2) if z1 = 0 and z2 > 0, then r = b1 when b1 >= b2 + z2, and r = -1 when b1 < b2 + z2; (3) if z1 > 0 and z2 = 0, then r = b2 when b2 >= b1 + z1, and r = -1 when b2 < b1 + z1; (4) if z1 > 0 and z2 > 0, then r = max(b1 + z1, b2 + z2).
  Preconditions: nums1 and nums2 are slices of 64-bit integers with 1 <= len(nums1) <= 100000 and 1 <= len(nums2) <= 100000; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000. -/
theorem spec_1 (nums1 nums2 : Slice I64)
    (h1len : 1 ≤ nums1.leng) (h1len' : nums1.leng ≤ 100000)
    (h2len : 1 ≤ nums2.leng) (h2len' : nums2.leng ≤ 100000)
    (h1val : ∀ x ∈ vals nums1, 0 ≤ x ∧ x ≤ 1000000)
    (h2val : ∀ x ∈ vals nums2, 0 ≤ x ∧ x ≤ 1000000) :
    ∃ r : I64, Aegis.MinSum.min_sum nums1 nums2 = Result.ok r ∧

      (zeros nums1 = 0 ∧ zeros nums2 = 0 →
        (total nums1 = total nums2 → (r : ℤ) = total nums1) ∧
        (total nums1 ≠ total nums2 → (r : ℤ) = -1)) ∧

      (zeros nums1 = 0 ∧ zeros nums2 > 0 →
        (total nums1 ≥ total nums2 + zeros nums2 → (r : ℤ) = total nums1) ∧
        (total nums1 < total nums2 + zeros nums2 → (r : ℤ) = -1)) ∧

      (zeros nums1 > 0 ∧ zeros nums2 = 0 →
        (total nums2 ≥ total nums1 + zeros nums1 → (r : ℤ) = total nums2) ∧
        (total nums2 < total nums1 + zeros nums1 → (r : ℤ) = -1)) ∧

      (zeros nums1 > 0 ∧ zeros nums2 > 0 →
        (r : ℤ) = max (total nums1 + zeros nums1) (total nums2 + zeros nums2)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1len : 1 ≤ nums1.leng) (h1len' : nums1.leng ≤ 100000)
    (h2len : 1 ≤ nums2.leng) (h2len' : nums2.leng ≤ 100000)
    (h1val : ∀ x ∈ vals nums1, 0 ≤ x ∧ x ≤ 1000000)
    (h2val : ∀ x ∈ vals nums2, 0 ≤ x ∧ x ≤ 1000000), ∃ r : I64, Aegis.MinSum.min_sum nums1 nums2 = Result.ok r ∧

      (zeros nums1 = 0 ∧ zeros nums2 = 0 →
        (total nums1 = total nums2 → (r : ℤ) = total nums1) ∧
        (total nums1 ≠ total nums2 → (r : ℤ) = -1)) ∧

      (zeros nums1 = 0 ∧ zeros nums2 > 0 →
        (total nums1 ≥ total nums2 + zeros nums2 → (r : ℤ) = total nums1) ∧
        (total nums1 < total nums2 + zeros nums2 → (r : ℤ) = -1)) ∧

      (zeros nums1 > 0 ∧ zeros nums2 = 0 →
        (total nums2 ≥ total nums1 + zeros nums1 → (r : ℤ) = total nums2) ∧
        (total nums2 < total nums1 + zeros nums1 → (r : ℤ) = -1)) ∧

      (zeros nums1 > 0 ∧ zeros nums2 > 0 →
        (r : ℤ) = max (total nums1 + zeros nums1) (total nums2 + zeros nums2))) := by
  sorry

/-- The function returns a result r; it does not fail by overflow, panic, out-of-bounds access, or any other failure for any inputs satisfying the preconditions.
  Preconditions: nums1 and nums2 are slices of 64-bit integers with 1 <= len(nums1) <= 100000 and 1 <= len(nums2) <= 100000; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000. -/
theorem spec_2 (nums1 nums2 : Slice I64)
    (h1len : 1 ≤ nums1.leng) (h1len' : nums1.leng ≤ 100000)
    (h2len : 1 ≤ nums2.leng) (h2len' : nums2.leng ≤ 100000)
    (h1val : ∀ x ∈ vals nums1, 0 ≤ x ∧ x ≤ 1000000)
    (h2val : ∀ x ∈ vals nums2, 0 ≤ x ∧ x ≤ 1000000) :
    ∃ r : I64, Aegis.MinSum.min_sum nums1 nums2 = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1len : 1 ≤ nums1.leng) (h1len' : nums1.leng ≤ 100000)
    (h2len : 1 ≤ nums2.leng) (h2len' : nums2.leng ≤ 100000)
    (h1val : ∀ x ∈ vals nums1, 0 ≤ x ∧ x ≤ 1000000)
    (h2val : ∀ x ∈ vals nums2, 0 ≤ x ∧ x ≤ 1000000), ∃ r : I64, Aegis.MinSum.min_sum nums1 nums2 = Result.ok r) := by
  sorry

/-- Let z1 be the number of zero entries of nums1 and b1 be the sum of all entries of nums1; let z2 be the number of zero entries of nums2 and b2 be the sum of all entries of nums2. Whenever the function returns a result r with r != -1, it holds that r >= b1 + z1 and r >= b2 + z2.
  Preconditions: nums1 and nums2 are slices of 64-bit integers with 1 <= len(nums1) <= 100000 and 1 <= len(nums2) <= 100000; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000. -/
theorem spec_3 (nums1 nums2 : Slice I64)
    (h1len : 1 ≤ nums1.leng) (h1len' : nums1.leng ≤ 100000)
    (h2len : 1 ≤ nums2.leng) (h2len' : nums2.leng ≤ 100000)
    (h1val : ∀ x ∈ vals nums1, 0 ≤ x ∧ x ≤ 1000000)
    (h2val : ∀ x ∈ vals nums2, 0 ≤ x ∧ x ≤ 1000000) :
    ∀ r : I64, Aegis.MinSum.min_sum nums1 nums2 = Result.ok r → (r : ℤ) ≠ -1 →
      (r : ℤ) ≥ total nums1 + zeros nums1 ∧ (r : ℤ) ≥ total nums2 + zeros nums2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1len : 1 ≤ nums1.leng) (h1len' : nums1.leng ≤ 100000)
    (h2len : 1 ≤ nums2.leng) (h2len' : nums2.leng ≤ 100000)
    (h1val : ∀ x ∈ vals nums1, 0 ≤ x ∧ x ≤ 1000000)
    (h2val : ∀ x ∈ vals nums2, 0 ≤ x ∧ x ≤ 1000000), ∀ r : I64, Aegis.MinSum.min_sum nums1 nums2 = Result.ok r → (r : ℤ) ≠ -1 →
      (r : ℤ) ≥ total nums1 + zeros nums1 ∧ (r : ℤ) ≥ total nums2 + zeros nums2) := by
  sorry

/-- Let z1 be the number of zero entries of nums1 and b1 be the sum of all entries of nums1; let z2 be the number of zero entries of nums2 and b2 be the sum of all entries of nums2. Whenever the function returns a result r with r != -1, it holds that r = max(b1 + z1, b2 + z2).
  Preconditions: nums1 and nums2 are slices of 64-bit integers with 1 <= len(nums1) <= 100000 and 1 <= len(nums2) <= 100000; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000. -/
theorem spec_4 (nums1 nums2 : Slice I64)
    (h1len : 1 ≤ nums1.leng) (h1len' : nums1.leng ≤ 100000)
    (h2len : 1 ≤ nums2.leng) (h2len' : nums2.leng ≤ 100000)
    (h1val : ∀ x ∈ vals nums1, 0 ≤ x ∧ x ≤ 1000000)
    (h2val : ∀ x ∈ vals nums2, 0 ≤ x ∧ x ≤ 1000000) :
    ∀ r : I64, Aegis.MinSum.min_sum nums1 nums2 = Result.ok r → (r : ℤ) ≠ -1 →
      (r : ℤ) = max (total nums1 + zeros nums1) (total nums2 + zeros nums2) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1len : 1 ≤ nums1.leng) (h1len' : nums1.leng ≤ 100000)
    (h2len : 1 ≤ nums2.leng) (h2len' : nums2.leng ≤ 100000)
    (h1val : ∀ x ∈ vals nums1, 0 ≤ x ∧ x ≤ 1000000)
    (h2val : ∀ x ∈ vals nums2, 0 ≤ x ∧ x ≤ 1000000), ∀ r : I64, Aegis.MinSum.min_sum nums1 nums2 = Result.ok r → (r : ℤ) ≠ -1 →
      (r : ℤ) = max (total nums1 + zeros nums1) (total nums2 + zeros nums2)) := by
  sorry

/-- Let z1 be the number of zero entries of nums1 and b1 be the sum of all entries of nums1; let z2 be the number of zero entries of nums2 and b2 be the sum of all entries of nums2. The function returns a result r, and r = -1 if and only if at least one of these three conditions holds: (i) z1 = 0 and z2 = 0 and b1 != b2; (ii) z1 = 0 and z2 > 0 and b1 < b2 + z2; (iii) z1 > 0 and z2 = 0 and b2 < b1 + z1. In all other cases r != -1.
  Preconditions: nums1 and nums2 are slices of 64-bit integers with 1 <= len(nums1) <= 100000 and 1 <= len(nums2) <= 100000; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000. -/
theorem spec_5 (nums1 nums2 : Slice I64)
    (h1len : 1 ≤ nums1.leng) (h1len' : nums1.leng ≤ 100000)
    (h2len : 1 ≤ nums2.leng) (h2len' : nums2.leng ≤ 100000)
    (h1val : ∀ x ∈ vals nums1, 0 ≤ x ∧ x ≤ 1000000)
    (h2val : ∀ x ∈ vals nums2, 0 ≤ x ∧ x ≤ 1000000) :
    ∃ r : I64, Aegis.MinSum.min_sum nums1 nums2 = Result.ok r ∧
      ((r : ℤ) = -1 ↔
        (zeros nums1 = 0 ∧ zeros nums2 = 0 ∧ total nums1 ≠ total nums2) ∨
        (zeros nums1 = 0 ∧ zeros nums2 > 0 ∧ total nums1 < total nums2 + zeros nums2) ∨
        (zeros nums1 > 0 ∧ zeros nums2 = 0 ∧ total nums2 < total nums1 + zeros nums1)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1len : 1 ≤ nums1.leng) (h1len' : nums1.leng ≤ 100000)
    (h2len : 1 ≤ nums2.leng) (h2len' : nums2.leng ≤ 100000)
    (h1val : ∀ x ∈ vals nums1, 0 ≤ x ∧ x ≤ 1000000)
    (h2val : ∀ x ∈ vals nums2, 0 ≤ x ∧ x ≤ 1000000), ∃ r : I64, Aegis.MinSum.min_sum nums1 nums2 = Result.ok r ∧
      ((r : ℤ) = -1 ↔
        (zeros nums1 = 0 ∧ zeros nums2 = 0 ∧ total nums1 ≠ total nums2) ∨
        (zeros nums1 = 0 ∧ zeros nums2 > 0 ∧ total nums1 < total nums2 + zeros nums2) ∨
        (zeros nums1 > 0 ∧ zeros nums2 = 0 ∧ total nums2 < total nums1 + zeros nums1))) := by
  sorry

/-- Let r be the result returned for the argument pair (nums1, nums2), and let r' be the result returned for the argument pair (nums2, nums1). Both calls return results and r = r'.
  Preconditions: nums1 and nums2 are slices of 64-bit integers with 1 <= len(nums1) <= 100000 and 1 <= len(nums2) <= 100000; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000. -/
theorem spec_6 (nums1 nums2 : Slice I64)
    (h1len : 1 ≤ nums1.leng) (h1len' : nums1.leng ≤ 100000)
    (h2len : 1 ≤ nums2.leng) (h2len' : nums2.leng ≤ 100000)
    (h1val : ∀ x ∈ vals nums1, 0 ≤ x ∧ x ≤ 1000000)
    (h2val : ∀ x ∈ vals nums2, 0 ≤ x ∧ x ≤ 1000000) :
    ∃ r r' : I64, Aegis.MinSum.min_sum nums1 nums2 = Result.ok r ∧
      Aegis.MinSum.min_sum nums2 nums1 = Result.ok r' ∧ r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1len : 1 ≤ nums1.leng) (h1len' : nums1.leng ≤ 100000)
    (h2len : 1 ≤ nums2.leng) (h2len' : nums2.leng ≤ 100000)
    (h1val : ∀ x ∈ vals nums1, 0 ≤ x ∧ x ≤ 1000000)
    (h2val : ∀ x ∈ vals nums2, 0 ≤ x ∧ x ≤ 1000000), ∃ r r' : I64, Aegis.MinSum.min_sum nums1 nums2 = Result.ok r ∧
      Aegis.MinSum.min_sum nums2 nums1 = Result.ok r' ∧ r = r') := by
  sorry

/-- Let z1 be the number of zero entries of nums1 and b1 be the sum of all entries of nums1; let z1' be the number of zero entries of nums1' and b1' be the sum of all entries of nums1'. If z1' = z1 and b1' = b1, then the result returned for (nums1', nums2) equals the result returned for (nums1, nums2).
  Preconditions: nums1 and nums2 are slices of 64-bit integers with 1 <= len(nums1) <= 100000 and 1 <= len(nums2) <= 100000; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000. Also nums1' is any slice of 64-bit integers with len(nums1') = len(nums1), 1 <= len(nums1') <= 100000, and for every i with 0 <= i < len(nums1'), 0 <= nums1'[i] <= 1000000. -/
theorem spec_7 (nums1 nums2 nums1' : Slice I64)
    (h1len : 1 ≤ nums1.leng) (h1len' : nums1.leng ≤ 100000)
    (h2len : 1 ≤ nums2.leng) (h2len' : nums2.leng ≤ 100000)
    (h1val : ∀ x ∈ vals nums1, 0 ≤ x ∧ x ≤ 1000000)
    (h2val : ∀ x ∈ vals nums2, 0 ≤ x ∧ x ≤ 1000000)
    (h1'len : nums1'.leng = nums1.leng)
    (h1'len1 : 1 ≤ nums1'.leng) (h1'len2 : nums1'.leng ≤ 100000)
    (h1'val : ∀ x ∈ vals nums1', 0 ≤ x ∧ x ≤ 1000000) :
    zeros nums1' = zeros nums1 → total nums1' = total nums1 →
      ∃ r r' : I64, Aegis.MinSum.min_sum nums1' nums2 = Result.ok r ∧
        Aegis.MinSum.min_sum nums1 nums2 = Result.ok r' ∧ r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums1 nums2 nums1' : Slice I64)
    (h1len : 1 ≤ nums1.leng) (h1len' : nums1.leng ≤ 100000)
    (h2len : 1 ≤ nums2.leng) (h2len' : nums2.leng ≤ 100000)
    (h1val : ∀ x ∈ vals nums1, 0 ≤ x ∧ x ≤ 1000000)
    (h2val : ∀ x ∈ vals nums2, 0 ≤ x ∧ x ≤ 1000000)
    (h1'len : nums1'.leng = nums1.leng)
    (h1'len1 : 1 ≤ nums1'.leng) (h1'len2 : nums1'.leng ≤ 100000)
    (h1'val : ∀ x ∈ vals nums1', 0 ≤ x ∧ x ≤ 1000000), zeros nums1' = zeros nums1 → total nums1' = total nums1 →
      ∃ r r' : I64, Aegis.MinSum.min_sum nums1' nums2 = Result.ok r ∧
        Aegis.MinSum.min_sum nums1 nums2 = Result.ok r' ∧ r = r') := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exist integer arrays u of length len(nums1) and v of length len(nums2) such that: for every i with 0 <= i < len(nums1), if nums1[i] != 0 then u[i] = nums1[i], and if nums1[i] = 0 then u[i] > 0; for every j with 0 <= j < len(nums2), if nums2[j] != 0 then v[j] = nums2[j], and if nums2[j] = 0 then v[j] > 0; and sum_{0 <= i < len(nums1)} u[i] = sum_{0 <= j < len(nums2)} v[j] = r.
  Preconditions: nums1 and nums2 are slices of 64-bit integers with 1 <= len(nums1) <= 100000 and 1 <= len(nums2) <= 100000; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000. -/
theorem spec_8 (nums1 nums2 : Slice I64)
    (h1len : 1 ≤ nums1.leng) (h1len' : nums1.leng ≤ 100000)
    (h2len : 1 ≤ nums2.leng) (h2len' : nums2.leng ≤ 100000)
    (h1val : ∀ x ∈ vals nums1, 0 ≤ x ∧ x ≤ 1000000)
    (h2val : ∀ x ∈ vals nums2, 0 ≤ x ∧ x ≤ 1000000) :
    ∀ r : I64, Aegis.MinSum.min_sum nums1 nums2 = Result.ok r → (r : ℤ) ≠ -1 →
      ∃ u v : List ℤ, Fills u nums1 ∧ Fills v nums2 ∧
        u.sum = (r : ℤ) ∧ v.sum = (r : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1len : 1 ≤ nums1.leng) (h1len' : nums1.leng ≤ 100000)
    (h2len : 1 ≤ nums2.leng) (h2len' : nums2.leng ≤ 100000)
    (h1val : ∀ x ∈ vals nums1, 0 ≤ x ∧ x ≤ 1000000)
    (h2val : ∀ x ∈ vals nums2, 0 ≤ x ∧ x ≤ 1000000), ∀ r : I64, Aegis.MinSum.min_sum nums1 nums2 = Result.ok r → (r : ℤ) ≠ -1 →
      ∃ u v : List ℤ, Fills u nums1 ∧ Fills v nums2 ∧
        u.sum = (r : ℤ) ∧ v.sum = (r : ℤ)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, for every integer S with S < r there do not exist integer arrays u of length len(nums1) and v of length len(nums2) such that: for every i with 0 <= i < len(nums1), if nums1[i] != 0 then u[i] = nums1[i], and if nums1[i] = 0 then u[i] > 0; for every j with 0 <= j < len(nums2), if nums2[j] != 0 then v[j] = nums2[j], and if nums2[j] = 0 then v[j] > 0; and sum_{0 <= i < len(nums1)} u[i] = sum_{0 <= j < len(nums2)} v[j] = S.
  Preconditions: nums1 and nums2 are slices of 64-bit integers with 1 <= len(nums1) <= 100000 and 1 <= len(nums2) <= 100000; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000. -/
theorem spec_9 (nums1 nums2 : Slice I64)
    (h1len : 1 ≤ nums1.leng) (h1len' : nums1.leng ≤ 100000)
    (h2len : 1 ≤ nums2.leng) (h2len' : nums2.leng ≤ 100000)
    (h1val : ∀ x ∈ vals nums1, 0 ≤ x ∧ x ≤ 1000000)
    (h2val : ∀ x ∈ vals nums2, 0 ≤ x ∧ x ≤ 1000000) :
    ∀ r : I64, Aegis.MinSum.min_sum nums1 nums2 = Result.ok r → (r : ℤ) ≠ -1 →
      ∀ S : ℤ, S < (r : ℤ) →
        ¬ ∃ u v : List ℤ, Fills u nums1 ∧ Fills v nums2 ∧ u.sum = S ∧ v.sum = S := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 : Slice I64)
    (h1len : 1 ≤ nums1.leng) (h1len' : nums1.leng ≤ 100000)
    (h2len : 1 ≤ nums2.leng) (h2len' : nums2.leng ≤ 100000)
    (h1val : ∀ x ∈ vals nums1, 0 ≤ x ∧ x ≤ 1000000)
    (h2val : ∀ x ∈ vals nums2, 0 ≤ x ∧ x ≤ 1000000), ∀ r : I64, Aegis.MinSum.min_sum nums1 nums2 = Result.ok r → (r : ℤ) ≠ -1 →
      ∀ S : ℤ, S < (r : ℤ) →
        ¬ ∃ u v : List ℤ, Fills u nums1 ∧ Fills v nums2 ∧ u.sum = S ∧ v.sum = S) := by
  sorry

end AegisSpec.MinSum
