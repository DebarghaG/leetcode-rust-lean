import Aegis.MinimumAverageDifference.Code.Funs

/-!
# Specifications of `Aegis.MinimumAverageDifference.minimum_average_difference`

LeetCode problem `minimum-average-difference`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinimumAverageDifference

  namespace AegisSpec.MinimumAverageDifference

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def prefixSum (nums : Slice Std.I64) (i : ℕ) : ℤ := ((vals nums).take (i + 1)).sum

  def suffixSum (nums : Slice Std.I64) (i : ℕ) : ℤ := ((vals nums).drop (i + 1)).sum

  def leftAvg (nums : Slice Std.I64) (i : ℕ) : ℤ := prefixSum nums i / ((i : ℤ) + 1)

  def rightAvg (nums : Slice Std.I64) (i : ℕ) : ℤ :=
    if i + 1 < (vals nums).length then
      suffixSum nums i / (((vals nums).length : ℤ) - ((i : ℤ) + 1))
    else 0

  def diff (nums : Slice Std.I64) (i : ℕ) : ℕ := Int.natAbs (leftAvg nums i - rightAvg nums i)

  /-- Let n = len(nums). For each integer i with 0 <= i < n define: P(i) = sum_{j=0}^{i} nums[j]; Q(i) = sum_{j=i+1}^{n-1} nums[j] (the empty sum is 0); A(i) = P(i) div (i+1); B(i) = if i < n-1 then Q(i) div (n-1-i) else 0; D(i) = |A(i) - B(i)|. The function returns a result r such that 0 <= r < n, and for every i with 0 <= i < n, D(r) <= D(i), and for every i with 0 <= i < r, D(i) > D(r).
    Preconditions: 1 <= len(nums) <= 100000 and for every j with 0 <= j < len(nums), 0 <= nums[j] <= 100000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (vals nums).length)
      (hn_high : (vals nums).length ≤ 100000)
      (hvals : ∀ j : ℕ, j < (vals nums).length →
        0 ≤ (vals nums)[j]! ∧ (vals nums)[j]! ≤ 100000) :
      ∃ r : Std.I64,
        minimum_average_difference nums = ok r ∧
        0 ≤ r.val ∧
        r.val < ((vals nums).length : ℤ) ∧
        (∀ i : ℕ, i < (vals nums).length → diff nums r.val.toNat ≤ diff nums i) ∧
        (∀ i : ℕ, i < r.val.toNat → diff nums r.val.toNat < diff nums i) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (vals nums).length)
        (hn_high : (vals nums).length ≤ 100000)
        (hvals : ∀ j : ℕ, j < (vals nums).length →
          0 ≤ (vals nums)[j]! ∧ (vals nums)[j]! ≤ 100000), ∃ r : Std.I64,
          minimum_average_difference nums = ok r ∧
          0 ≤ r.val ∧
          r.val < ((vals nums).length : ℤ) ∧
          (∀ i : ℕ, i < (vals nums).length → diff nums r.val.toNat ≤ diff nums i) ∧
          (∀ i : ℕ, i < r.val.toNat → diff nums r.val.toNat < diff nums i)) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < len(nums).
    Preconditions: 1 <= len(nums) <= 100000 and for every j with 0 <= j < len(nums), 0 <= nums[j] <= 100000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (vals nums).length)
      (hn_high : (vals nums).length ≤ 100000)
      (hvals : ∀ j : ℕ, j < (vals nums).length →
        0 ≤ (vals nums)[j]! ∧ (vals nums)[j]! ≤ 100000) :
      ∀ r : Std.I64, minimum_average_difference nums = ok r →
        0 ≤ r.val ∧ r.val < ((vals nums).length : ℤ) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (vals nums).length)
        (hn_high : (vals nums).length ≤ 100000)
        (hvals : ∀ j : ℕ, j < (vals nums).length →
          0 ≤ (vals nums)[j]! ∧ (vals nums)[j]! ≤ 100000), ∀ r : Std.I64, minimum_average_difference nums = ok r →
          0 ≤ r.val ∧ r.val < ((vals nums).length : ℤ)) := by
    sorry

  /-- The function returns a result r (it does not fail: no overflow, division by zero, panic, or out-of-bounds access occurs).
    Preconditions: 1 <= len(nums) <= 100000 and for every j with 0 <= j < len(nums), 0 <= nums[j] <= 100000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (vals nums).length)
      (hn_high : (vals nums).length ≤ 100000)
      (hvals : ∀ j : ℕ, j < (vals nums).length →
        0 ≤ (vals nums)[j]! ∧ (vals nums)[j]! ≤ 100000) :
      ∃ r : Std.I64, minimum_average_difference nums = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (vals nums).length)
        (hn_high : (vals nums).length ≤ 100000)
        (hvals : ∀ j : ℕ, j < (vals nums).length →
          0 ≤ (vals nums)[j]! ∧ (vals nums)[j]! ≤ 100000), ∃ r : Std.I64, minimum_average_difference nums = ok r) := by
    sorry

  /-- Let n = len(nums). Define D(i) for 0 <= i < n as in spec_1: P(i) = sum_{j=0}^{i} nums[j]; Q(i) = sum_{j=i+1}^{n-1} nums[j]; A(i) = P(i) div (i+1); B(i) = if i < n-1 then Q(i) div (n-1-i) else 0; D(i) = |A(i) - B(i)|. Whenever the function returns a result r, for every i with 0 <= i < n, D(r) <= D(i).
    Preconditions: 1 <= len(nums) <= 100000 and for every j with 0 <= j < len(nums), 0 <= nums[j] <= 100000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (vals nums).length)
      (hn_high : (vals nums).length ≤ 100000)
      (hvals : ∀ j : ℕ, j < (vals nums).length →
        0 ≤ (vals nums)[j]! ∧ (vals nums)[j]! ≤ 100000) :
      ∀ r : Std.I64, minimum_average_difference nums = ok r →
        ∀ i : ℕ, i < (vals nums).length → diff nums r.val.toNat ≤ diff nums i := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (vals nums).length)
        (hn_high : (vals nums).length ≤ 100000)
        (hvals : ∀ j : ℕ, j < (vals nums).length →
          0 ≤ (vals nums)[j]! ∧ (vals nums)[j]! ≤ 100000), ∀ r : Std.I64, minimum_average_difference nums = ok r →
          ∀ i : ℕ, i < (vals nums).length → diff nums r.val.toNat ≤ diff nums i) := by
    sorry

  /-- Let n = len(nums). Define D(i) for 0 <= i < n as in spec_1: P(i) = sum_{j=0}^{i} nums[j]; Q(i) = sum_{j=i+1}^{n-1} nums[j]; A(i) = P(i) div (i+1); B(i) = if i < n-1 then Q(i) div (n-1-i) else 0; D(i) = |A(i) - B(i)|. Whenever the function returns a result r, for every i with 0 <= i < r, D(i) > D(r).
    Preconditions: 1 <= len(nums) <= 100000 and for every j with 0 <= j < len(nums), 0 <= nums[j] <= 100000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (vals nums).length)
      (hn_high : (vals nums).length ≤ 100000)
      (hvals : ∀ j : ℕ, j < (vals nums).length →
        0 ≤ (vals nums)[j]! ∧ (vals nums)[j]! ≤ 100000) :
      ∀ r : Std.I64, minimum_average_difference nums = ok r →
        ∀ i : ℕ, i < r.val.toNat → diff nums r.val.toNat < diff nums i := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (vals nums).length)
        (hn_high : (vals nums).length ≤ 100000)
        (hvals : ∀ j : ℕ, j < (vals nums).length →
          0 ≤ (vals nums)[j]! ∧ (vals nums)[j]! ≤ 100000), ∀ r : Std.I64, minimum_average_difference nums = ok r →
          ∀ i : ℕ, i < r.val.toNat → diff nums r.val.toNat < diff nums i) := by
    sorry

  /-- Let n = len(nums). Define D(i) for 0 <= i < n as in spec_1: P(i) = sum_{j=0}^{i} nums[j]; Q(i) = sum_{j=i+1}^{n-1} nums[j]; A(i) = P(i) div (i+1); B(i) = if i < n-1 then Q(i) div (n-1-i) else 0; D(i) = |A(i) - B(i)|. Whenever the function returns a result r, if there exists an i with 0 <= i < n and D(i) = 0, then D(r) = 0 and for every i with 0 <= i < r, D(i) > 0.
    Preconditions: 1 <= len(nums) <= 100000 and for every j with 0 <= j < len(nums), 0 <= nums[j] <= 100000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (vals nums).length)
      (hn_high : (vals nums).length ≤ 100000)
      (hvals : ∀ j : ℕ, j < (vals nums).length →
        0 ≤ (vals nums)[j]! ∧ (vals nums)[j]! ≤ 100000) :
      ∀ r : Std.I64, minimum_average_difference nums = ok r →
        (∃ i : ℕ, i < (vals nums).length ∧ diff nums i = 0) →
          diff nums r.val.toNat = 0 ∧ (∀ i : ℕ, i < r.val.toNat → 0 < diff nums i) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (vals nums).length)
        (hn_high : (vals nums).length ≤ 100000)
        (hvals : ∀ j : ℕ, j < (vals nums).length →
          0 ≤ (vals nums)[j]! ∧ (vals nums)[j]! ≤ 100000), ∀ r : Std.I64, minimum_average_difference nums = ok r →
          (∃ i : ℕ, i < (vals nums).length ∧ diff nums i = 0) →
            diff nums r.val.toNat = 0 ∧ (∀ i : ℕ, i < r.val.toNat → 0 < diff nums i)) := by
    sorry

  end AegisSpec.MinimumAverageDifference
