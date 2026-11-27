import Aegis.MaximumCount.Code.Funs

/-!
# Specifications of `Aegis.MaximumCount.maximum_count`

LeetCode problem `maximum-count-of-positive-integer-and-negative-integer`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumCount

  def posCount (nums : Slice I64) : ℕ :=
    nums.val.countP fun x => decide (0 < x.val)

  def negCount (nums : Slice I64) : ℕ :=
    nums.val.countP fun x => decide (x.val < 0)

  def zeroCount (nums : Slice I64) : ℕ :=
    nums.val.countP fun x => decide (x.val = 0)

  def sameSignCount (nums : Slice I64) (x : I64) : ℕ :=
    nums.val.countP fun y =>
      decide ((0 < x.val ∧ 0 < y.val) ∨ (x.val < 0 ∧ y.val < 0))

  def i64Neg (x : I64) : I64 := ⟨-x.bv⟩

  def negRevContents (nums : Slice I64) : List I64 :=
    (nums.val.map i64Neg).reverse

  /-- Let pos(nums) be the number of indices i with 0 <= i < len(nums) and nums[i] > 0, and let neg(nums) be the number of indices i with 0 <= i < len(nums) and nums[i] < 0. The call maximum_count nums returns Result.ok r for some i64 r, and r = max(pos(nums), neg(nums)).
    Preconditions: len(nums) >= 1 and len(nums) <= 2000; for every i with 0 <= i < len(nums), -2000 <= nums[i] <= 2000; for every i, j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
  theorem spec_1 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
      (hbound : ∀ (i : ℕ) (hi : i < nums.length),
        -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
      (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
        i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val) :
      ∃ r : I64,
        Aegis.MaximumCount.maximum_count nums = ok r ∧
        r.val = max (posCount nums : ℤ) (negCount nums : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
        (hbound : ∀ (i : ℕ) (hi : i < nums.length),
          -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
        (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
          i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val), ∃ r : I64,
          Aegis.MaximumCount.maximum_count nums = ok r ∧
          r.val = max (posCount nums : ℤ) (negCount nums : ℤ)) := by
    sorry

  /-- The call maximum_count nums does not fail: there exists an i64 value r such that maximum_count nums returns Result.ok r.
    Preconditions: len(nums) >= 1 and len(nums) <= 2000; for every i with 0 <= i < len(nums), -2000 <= nums[i] <= 2000; for every i, j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
  theorem spec_2 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
      (hbound : ∀ (i : ℕ) (hi : i < nums.length),
        -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
      (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
        i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val) :
      ∃ r : I64, Aegis.MaximumCount.maximum_count nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
        (hbound : ∀ (i : ℕ) (hi : i < nums.length),
          -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
        (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
          i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val), ∃ r : I64, Aegis.MaximumCount.maximum_count nums = ok r) := by
    sorry

  /-- Whenever the call maximum_count nums returns Result.ok r, we have 0 <= r <= len(nums).
    Preconditions: len(nums) >= 1 and len(nums) <= 2000; for every i with 0 <= i < len(nums), -2000 <= nums[i] <= 2000; for every i, j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
  theorem spec_3 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
      (hbound : ∀ (i : ℕ) (hi : i < nums.length),
        -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
      (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
        i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val) :
      ∀ r : I64, Aegis.MaximumCount.maximum_count nums = ok r →
        0 ≤ r.val ∧ r.val ≤ (nums.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
        (hbound : ∀ (i : ℕ) (hi : i < nums.length),
          -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
        (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
          i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val), ∀ r : I64, Aegis.MaximumCount.maximum_count nums = ok r →
          0 ≤ r.val ∧ r.val ≤ (nums.length : ℤ)) := by
    sorry

  /-- Let pos(nums) be the number of indices i with 0 <= i < len(nums) and nums[i] > 0, and let neg(nums) be the number of indices i with 0 <= i < len(nums) and nums[i] < 0. Whenever the call maximum_count nums returns Result.ok r, either r = pos(nums) or r = neg(nums).
    Preconditions: len(nums) >= 1 and len(nums) <= 2000; for every i with 0 <= i < len(nums), -2000 <= nums[i] <= 2000; for every i, j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
  theorem spec_4 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
      (hbound : ∀ (i : ℕ) (hi : i < nums.length),
        -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
      (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
        i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val) :
      ∀ r : I64, Aegis.MaximumCount.maximum_count nums = ok r →
        r.val = (posCount nums : ℤ) ∨ r.val = (negCount nums : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
        (hbound : ∀ (i : ℕ) (hi : i < nums.length),
          -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
        (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
          i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val), ∀ r : I64, Aegis.MaximumCount.maximum_count nums = ok r →
          r.val = (posCount nums : ℤ) ∨ r.val = (negCount nums : ℤ)) := by
    sorry

  /-- Whenever the call maximum_count nums returns Result.ok r with r > 0, there exists an index i with 0 <= i < len(nums) and nums[i] != 0 such that r equals the number of indices j with 0 <= j < len(nums) for which nums[j] has the same sign as nums[i], meaning both are positive or both are negative.
    Preconditions: len(nums) >= 1 and len(nums) <= 2000; for every i with 0 <= i < len(nums), -2000 <= nums[i] <= 2000; for every i, j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
  theorem spec_5 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
      (hbound : ∀ (i : ℕ) (hi : i < nums.length),
        -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
      (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
        i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val) :
      ∀ r : I64, Aegis.MaximumCount.maximum_count nums = ok r → 0 < r.val →
        ∃ (i : ℕ) (hi : i < nums.length),
          (nums.val[i]'hi).val ≠ 0 ∧
          r.val = (sameSignCount nums (nums.val[i]'hi) : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
        (hbound : ∀ (i : ℕ) (hi : i < nums.length),
          -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
        (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
          i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val), ∀ r : I64, Aegis.MaximumCount.maximum_count nums = ok r → 0 < r.val →
          ∃ (i : ℕ) (hi : i < nums.length),
            (nums.val[i]'hi).val ≠ 0 ∧
            r.val = (sameSignCount nums (nums.val[i]'hi) : ℤ)) := by
    sorry

  /-- The call maximum_count nums returns Result.ok r, and r = 0 if and only if for every i with 0 <= i < len(nums), nums[i] = 0.
    Preconditions: len(nums) >= 1 and len(nums) <= 2000; for every i with 0 <= i < len(nums), -2000 <= nums[i] <= 2000; for every i, j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
  theorem spec_6 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
      (hbound : ∀ (i : ℕ) (hi : i < nums.length),
        -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
      (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
        i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val) :
      ∃ r : I64,
        Aegis.MaximumCount.maximum_count nums = ok r ∧
        (r.val = 0 ↔
          ∀ (i : ℕ) (hi : i < nums.length), (nums.val[i]'hi).val = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
        (hbound : ∀ (i : ℕ) (hi : i < nums.length),
          -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
        (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
          i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val), ∃ r : I64,
          Aegis.MaximumCount.maximum_count nums = ok r ∧
          (r.val = 0 ↔
            ∀ (i : ℕ) (hi : i < nums.length), (nums.val[i]'hi).val = 0)) := by
    sorry

  /-- The call maximum_count nums returns Result.ok r, and if nums[0] = 0 then r = 0, while if nums[0] != 0 then r = 1.
    Preconditions: len(nums) = 1; for every i with 0 <= i < len(nums), -2000 <= nums[i] <= 2000; and the sortedness condition holds vacuously. -/
  theorem spec_7 (nums : Slice I64)
      (hlen : nums.length = 1)
      (hbound : ∀ (i : ℕ) (hi : i < nums.length),
        -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
      (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
        i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val) :
      ∃ r : I64,
        Aegis.MaximumCount.maximum_count nums = ok r ∧
        ((nums.val[0]'(by have h : nums.val.length = 1 := hlen; omega)).val = 0 →
          r.val = 0) ∧
        ((nums.val[0]'(by have h : nums.val.length = 1 := hlen; omega)).val ≠ 0 →
          r.val = 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : nums.length = 1)
        (hbound : ∀ (i : ℕ) (hi : i < nums.length),
          -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
        (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
          i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val), ∃ r : I64,
          Aegis.MaximumCount.maximum_count nums = ok r ∧
          ((nums.val[0]'(by have h : nums.val.length = 1 := hlen; omega)).val = 0 →
            r.val = 0) ∧
          ((nums.val[0]'(by have h : nums.val.length = 1 := hlen; omega)).val ≠ 0 →
            r.val = 1)) := by
    sorry

  /-- The call maximum_count nums returns Result.ok r, and r = len(nums) if and only if either (for every i with 0 <= i < len(nums), nums[i] > 0) or (for every i with 0 <= i < len(nums), nums[i] < 0).
    Preconditions: len(nums) >= 1 and len(nums) <= 2000; for every i with 0 <= i < len(nums), -2000 <= nums[i] <= 2000; for every i, j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
  theorem spec_8 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
      (hbound : ∀ (i : ℕ) (hi : i < nums.length),
        -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
      (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
        i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val) :
      ∃ r : I64,
        Aegis.MaximumCount.maximum_count nums = ok r ∧
        (r.val = (nums.length : ℤ) ↔
          (∀ (i : ℕ) (hi : i < nums.length), 0 < (nums.val[i]'hi).val) ∨
          (∀ (i : ℕ) (hi : i < nums.length), (nums.val[i]'hi).val < 0)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
        (hbound : ∀ (i : ℕ) (hi : i < nums.length),
          -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
        (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
          i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val), ∃ r : I64,
          Aegis.MaximumCount.maximum_count nums = ok r ∧
          (r.val = (nums.length : ℤ) ↔
            (∀ (i : ℕ) (hi : i < nums.length), 0 < (nums.val[i]'hi).val) ∨
            (∀ (i : ℕ) (hi : i < nums.length), (nums.val[i]'hi).val < 0))) := by
    sorry

  /-- The call maximum_count nums returns Result.ok r, and r < len(nums).
    Preconditions: len(nums) >= 1 and len(nums) <= 2000; for every i with 0 <= i < len(nums), -2000 <= nums[i] <= 2000; for every i, j with 0 <= i < j < len(nums), nums[i] <= nums[j]; and there exists i with 0 <= i < len(nums) and nums[i] > 0, and there exists j with 0 <= j < len(nums) and nums[j] < 0. -/
  theorem spec_9 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
      (hbound : ∀ (i : ℕ) (hi : i < nums.length),
        -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
      (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
        i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val)
      (hpos : ∃ (i : ℕ) (hi : i < nums.length), 0 < (nums.val[i]'hi).val)
      (hneg : ∃ (j : ℕ) (hj : j < nums.length), (nums.val[j]'hj).val < 0) :
      ∃ r : I64,
        Aegis.MaximumCount.maximum_count nums = ok r ∧ r.val < (nums.length : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
        (hbound : ∀ (i : ℕ) (hi : i < nums.length),
          -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
        (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
          i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val)
        (hpos : ∃ (i : ℕ) (hi : i < nums.length), 0 < (nums.val[i]'hi).val)
        (hneg : ∃ (j : ℕ) (hj : j < nums.length), (nums.val[j]'hj).val < 0), ∃ r : I64,
          Aegis.MaximumCount.maximum_count nums = ok r ∧ r.val < (nums.length : ℤ)) := by
    sorry

  /-- Let pos(nums) be the number of indices i with 0 <= i < len(nums) and nums[i] > 0, and let neg(nums) be the number of indices i with 0 <= i < len(nums) and nums[i] < 0. Whenever the call maximum_count nums returns Result.ok r, r >= pos(nums) and r >= neg(nums).
    Preconditions: len(nums) >= 1 and len(nums) <= 2000; for every i with 0 <= i < len(nums), -2000 <= nums[i] <= 2000; for every i, j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
  theorem spec_10 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
      (hbound : ∀ (i : ℕ) (hi : i < nums.length),
        -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
      (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
        i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val) :
      ∀ r : I64, Aegis.MaximumCount.maximum_count nums = ok r →
        (posCount nums : ℤ) ≤ r.val ∧ (negCount nums : ℤ) ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
        (hbound : ∀ (i : ℕ) (hi : i < nums.length),
          -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
        (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
          i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val), ∀ r : I64, Aegis.MaximumCount.maximum_count nums = ok r →
          (posCount nums : ℤ) ≤ r.val ∧ (negCount nums : ℤ) ≤ r.val) := by
    sorry

  /-- The call maximum_count nums returns Result.ok r1, the call maximum_count nums2 returns Result.ok r2, and r1 = r2.
    Preconditions: len(nums) >= 1 and len(nums) <= 2000; for every i with 0 <= i < len(nums), -2000 <= nums[i] <= 2000; for every i, j with 0 <= i < j < len(nums), nums[i] <= nums[j]. For every slice nums2: len(nums2) >= 1 and len(nums2) <= 2000; for every i with 0 <= i < len(nums2), -2000 <= nums2[i] <= 2000; for every i, j with 0 <= i < j < len(nums2), nums2[i] <= nums2[j]; the number of positive entries of nums equals the number of positive entries of nums2; and the number of negative entries of nums equals the number of negative entries of nums2. -/
  theorem spec_11 (nums nums2 : Slice I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
      (hbound : ∀ (i : ℕ) (hi : i < nums.length),
        -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
      (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
        i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val)
      (hlen2_lo : 1 ≤ nums2.length) (hlen2_hi : nums2.length ≤ 2000)
      (hbound2 : ∀ (i : ℕ) (hi : i < nums2.length),
        -2000 ≤ (nums2.val[i]'hi).val ∧ (nums2.val[i]'hi).val ≤ 2000)
      (hsorted2 : ∀ (i j : ℕ) (hi : i < nums2.length) (hj : j < nums2.length),
        i < j → (nums2.val[i]'hi).val ≤ (nums2.val[j]'hj).val)
      (hpos : posCount nums = posCount nums2)
      (hneg : negCount nums = negCount nums2) :
      ∃ r1 r2 : I64,
        Aegis.MaximumCount.maximum_count nums = ok r1 ∧
        Aegis.MaximumCount.maximum_count nums2 = ok r2 ∧
        r1.val = r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums2 : Slice I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
        (hbound : ∀ (i : ℕ) (hi : i < nums.length),
          -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
        (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
          i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val)
        (hlen2_lo : 1 ≤ nums2.length) (hlen2_hi : nums2.length ≤ 2000)
        (hbound2 : ∀ (i : ℕ) (hi : i < nums2.length),
          -2000 ≤ (nums2.val[i]'hi).val ∧ (nums2.val[i]'hi).val ≤ 2000)
        (hsorted2 : ∀ (i j : ℕ) (hi : i < nums2.length) (hj : j < nums2.length),
          i < j → (nums2.val[i]'hi).val ≤ (nums2.val[j]'hj).val)
        (hpos : posCount nums = posCount nums2)
        (hneg : negCount nums = negCount nums2), ∃ r1 r2 : I64,
          Aegis.MaximumCount.maximum_count nums = ok r1 ∧
          Aegis.MaximumCount.maximum_count nums2 = ok r2 ∧
          r1.val = r2.val) := by
    sorry

  /-- Let n = len(nums) and let rev be the slice of length n with rev[i] = -nums[n-1-i] for every i with 0 <= i < n. The call maximum_count nums returns Result.ok r, the call maximum_count rev returns Result.ok r2, and r = r2.
    Preconditions: len(nums) >= 1 and len(nums) <= 2000; for every i with 0 <= i < len(nums), -2000 <= nums[i] <= 2000; for every i, j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
  theorem spec_12 (nums rev : Slice I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
      (hbound : ∀ (i : ℕ) (hi : i < nums.length),
        -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
      (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
        i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val)
      (hrev_len : rev.length = nums.length)
      (hrev_val : rev.val = negRevContents nums) :
      ∃ r r2 : I64,
        Aegis.MaximumCount.maximum_count nums = ok r ∧
        Aegis.MaximumCount.maximum_count rev = ok r2 ∧
        r.val = r2.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums rev : Slice I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
        (hbound : ∀ (i : ℕ) (hi : i < nums.length),
          -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
        (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
          i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val)
        (hrev_len : rev.length = nums.length)
        (hrev_val : rev.val = negRevContents nums), ∃ r r2 : I64,
          Aegis.MaximumCount.maximum_count nums = ok r ∧
          Aegis.MaximumCount.maximum_count rev = ok r2 ∧
          r.val = r2.val) := by
    sorry

  /-- Whenever the call maximum_count nums returns Result.ok r, let pos be the number of positive entries of nums, neg the number of negative entries of nums, and z the number of entries equal to 0. Then r + min(pos, neg) + z = len(nums).
    Preconditions: len(nums) >= 1 and len(nums) <= 2000; for every i with 0 <= i < len(nums), -2000 <= nums[i] <= 2000; for every i, j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
  theorem spec_13 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
      (hbound : ∀ (i : ℕ) (hi : i < nums.length),
        -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
      (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
        i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val) :
      ∀ r : I64, Aegis.MaximumCount.maximum_count nums = ok r →
        r.val + min (posCount nums : ℤ) (negCount nums : ℤ) + (zeroCount nums : ℤ)
          = (nums.length : ℤ) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
        (hbound : ∀ (i : ℕ) (hi : i < nums.length),
          -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
        (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
          i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val), ∀ r : I64, Aegis.MaximumCount.maximum_count nums = ok r →
          r.val + min (posCount nums : ℤ) (negCount nums : ℤ) + (zeroCount nums : ℤ)
            = (nums.length : ℤ)) := by
    sorry

  /-- Let pos(nums) be the number of indices i with 0 <= i < len(nums) and nums[i] > 0, and let neg(nums) be the number of indices i with 0 <= i < len(nums) and nums[i] < 0. The call maximum_count nums returns Result.ok r, and if every entry of nums is nonnegative then r = pos(nums), while if every entry of nums is nonpositive then r = neg(nums).
    Preconditions: len(nums) >= 1 and len(nums) <= 2000; for every i with 0 <= i < len(nums), -2000 <= nums[i] <= 2000; for every i, j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
  theorem spec_14 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
      (hbound : ∀ (i : ℕ) (hi : i < nums.length),
        -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
      (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
        i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val) :
      ∃ r : I64,
        Aegis.MaximumCount.maximum_count nums = ok r ∧
        ((∀ (i : ℕ) (hi : i < nums.length), 0 ≤ (nums.val[i]'hi).val) →
          r.val = (posCount nums : ℤ)) ∧
        ((∀ (i : ℕ) (hi : i < nums.length), (nums.val[i]'hi).val ≤ 0) →
          r.val = (negCount nums : ℤ)) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 2000)
        (hbound : ∀ (i : ℕ) (hi : i < nums.length),
          -2000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 2000)
        (hsorted : ∀ (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length),
          i < j → (nums.val[i]'hi).val ≤ (nums.val[j]'hj).val), ∃ r : I64,
          Aegis.MaximumCount.maximum_count nums = ok r ∧
          ((∀ (i : ℕ) (hi : i < nums.length), 0 ≤ (nums.val[i]'hi).val) →
            r.val = (posCount nums : ℤ)) ∧
          ((∀ (i : ℕ) (hi : i < nums.length), (nums.val[i]'hi).val ≤ 0) →
            r.val = (negCount nums : ℤ))) := by
    sorry

  end AegisSpec.MaximumCount
