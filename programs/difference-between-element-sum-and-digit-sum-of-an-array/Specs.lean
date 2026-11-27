import Aegis.DifferenceOfSum.Code.Funs

/-!
# Specifications of `Aegis.DifferenceOfSum.difference_of_sum`

LeetCode problem `difference-between-element-sum-and-digit-sum-of-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.DifferenceOfSum

  def dsNat (n : ℕ) : ℕ :=
    if h : n = 0 then 0 else n % 10 + dsNat (n / 10)
  termination_by n
  decreasing_by
    exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)

  def ds (n : ℤ) : ℤ := (dsNat n.natAbs : ℤ)

  def sumElems (nums : Slice Std.I64) : ℤ := (nums.val.map (fun x => x.val)).sum

  def sumDigits (nums : Slice Std.I64) : ℤ :=
    (nums.val.map (fun x => ds x.val)).sum

  /-- Let E = sum over i with 0 <= i < len(nums) of nums[i], and let D = sum over i with 0 <= i < len(nums) of ds(nums[i]), where ds(n) is the sum of the decimal digits of the positive integer n. Whenever the function returns a result r, the integer value of r is |E - D|.
    Preconditions: 1 <= len(nums) <= 2000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 2000. -/
  theorem spec_1 (nums : Slice Std.I64) (r : Std.I64)
      (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 2000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000)
      (hr : Aegis.DifferenceOfSum.difference_of_sum nums = ok r) :
      r.val = |sumElems nums - sumDigits nums| := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 2000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000)
        (hr : Aegis.DifferenceOfSum.difference_of_sum nums = ok r), r.val = |sumElems nums - sumDigits nums|) := by
    sorry

  /-- The function returns a result r; it does not fail.
    Preconditions: 1 <= len(nums) <= 2000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 2000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 2000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000) :
      ∃ r : Std.I64, Aegis.DifferenceOfSum.difference_of_sum nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 2000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000), ∃ r : Std.I64, Aegis.DifferenceOfSum.difference_of_sum nums = ok r) := by
    sorry

  /-- Let E = sum over i with 0 <= i < len(nums) of nums[i] and let D = sum over i with 0 <= i < len(nums) of ds(nums[i]), where ds(n) is the sum of the decimal digits of the positive integer n. Whenever the function returns a result r, r <= E - len(nums).
    Preconditions: 1 <= len(nums) <= 2000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 2000. -/
  theorem spec_3 (nums : Slice Std.I64) (r : Std.I64)
      (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 2000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000)
      (hr : Aegis.DifferenceOfSum.difference_of_sum nums = ok r) :
      r.val ≤ sumElems nums - (nums.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 2000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000)
        (hr : Aegis.DifferenceOfSum.difference_of_sum nums = ok r), r.val ≤ sumElems nums - (nums.length : ℤ)) := by
    sorry

  /-- Let E = sum over i with 0 <= i < len(nums) of nums[i] and let D = sum over i with 0 <= i < len(nums) of ds(nums[i]), where ds(n) is the sum of the decimal digits of the positive integer n. For every positive integer n, ds(n) <= n, hence D <= E. Whenever the function returns a result r, r = E - D.
    Preconditions: 1 <= len(nums) <= 2000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 2000. -/
  theorem spec_4 (nums : Slice Std.I64) (r : Std.I64)
      (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 2000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000)
      (hr : Aegis.DifferenceOfSum.difference_of_sum nums = ok r) :
      r.val = sumElems nums - sumDigits nums := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 2000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000)
        (hr : Aegis.DifferenceOfSum.difference_of_sum nums = ok r), r.val = sumElems nums - sumDigits nums) := by
    sorry

  /-- Let E = sum over i with 0 <= i < len(nums) of nums[i] and let D = sum over i with 0 <= i < len(nums) of ds(nums[i]), where ds(n) is the sum of the decimal digits of the positive integer n. Whenever the function returns a result r, there exists an integer k such that r = 9 * k.
    Preconditions: 1 <= len(nums) <= 2000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 2000. -/
  theorem spec_5 (nums : Slice Std.I64) (r : Std.I64)
      (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 2000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000)
      (hr : Aegis.DifferenceOfSum.difference_of_sum nums = ok r) :
      ∃ k : ℤ, r.val = 9 * k := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 2000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000)
        (hr : Aegis.DifferenceOfSum.difference_of_sum nums = ok r), ∃ k : ℤ, r.val = 9 * k) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < len(nums), nums[i] <= 9.
    Preconditions: 1 <= len(nums) <= 2000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 2000. -/
  theorem spec_6 (nums : Slice Std.I64) (r : Std.I64)
      (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 2000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000)
      (hr : Aegis.DifferenceOfSum.difference_of_sum nums = ok r) :
      r.val = 0 ↔ ∀ x ∈ nums.val, x.val ≤ 9 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 2000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000)
        (hr : Aegis.DifferenceOfSum.difference_of_sum nums = ok r), r.val = 0 ↔ ∀ x ∈ nums.val, x.val ≤ 9) := by
    sorry

  /-- For every valid slice nums and every integer d with 1 <= d <= 9, if the function returns r on nums and returns r' on the concatenation nums ++ [d], then r' = r.
    Preconditions: 1 <= len(nums) <= 1999, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 2000, and 1 <= d <= 9. -/
  theorem spec_7 (nums nums' : Slice Std.I64) (d r r' : Std.I64)
      (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 1999)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000)
      (hd1 : 1 ≤ d.val) (hd2 : d.val ≤ 9)
      (hcat : nums'.val = nums.val ++ [d])
      (hr : Aegis.DifferenceOfSum.difference_of_sum nums = ok r)
      (hr' : Aegis.DifferenceOfSum.difference_of_sum nums' = ok r') :
      r'.val = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (d r r' : Std.I64)
        (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 1999)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000)
        (hd1 : 1 ≤ d.val) (hd2 : d.val ≤ 9)
        (hcat : nums'.val = nums.val ++ [d])
        (hr : Aegis.DifferenceOfSum.difference_of_sum nums = ok r)
        (hr' : Aegis.DifferenceOfSum.difference_of_sum nums' = ok r'), r'.val = r.val) := by
    sorry

  /-- For every valid slice nums and every permutation nums' of nums, if the function returns r on nums and returns r' on nums', then r = r'.
    Preconditions: 1 <= len(nums) <= 2000, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 2000, and nums' is a slice that is a permutation of nums. -/
  theorem spec_8 (nums nums' : Slice Std.I64) (r r' : Std.I64)
      (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 2000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000)
      (hperm : nums'.val.Perm nums.val)
      (hr : Aegis.DifferenceOfSum.difference_of_sum nums = ok r)
      (hr' : Aegis.DifferenceOfSum.difference_of_sum nums' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (r r' : Std.I64)
        (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 2000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000)
        (hperm : nums'.val.Perm nums.val)
        (hr : Aegis.DifferenceOfSum.difference_of_sum nums = ok r)
        (hr' : Aegis.DifferenceOfSum.difference_of_sum nums' = ok r'), r.val = r'.val) := by
    sorry

  /-- Let m be the slice with len(m) = len(nums) and m[i] = nums[i] / 10 for every i. Let E_m = sum over i with 0 <= i < len(m) of m[i]. Whenever the function returns r on nums and returns r_m on m, r = 9 * E_m + r_m.
    Preconditions: 1 <= len(nums) <= 2000, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 2000, and for every i with 0 <= i < len(nums), nums[i] is divisible by 10. -/
  theorem spec_9 (nums m : Slice Std.I64) (r r_m : Std.I64)
      (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 2000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000)
      (hdiv : ∀ x ∈ nums.val, ∃ k : ℤ, x.val = 10 * k)
      (hm : List.Forall₂ (fun x y => y.val = x.val / 10) nums.val m.val)
      (hr : Aegis.DifferenceOfSum.difference_of_sum nums = ok r)
      (hr_m : Aegis.DifferenceOfSum.difference_of_sum m = ok r_m) :
      r.val = 9 * sumElems m + r_m.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums m : Slice Std.I64) (r r_m : Std.I64)
        (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 2000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000)
        (hdiv : ∀ x ∈ nums.val, ∃ k : ℤ, x.val = 10 * k)
        (hm : List.Forall₂ (fun x y => y.val = x.val / 10) nums.val m.val)
        (hr : Aegis.DifferenceOfSum.difference_of_sum nums = ok r)
        (hr_m : Aegis.DifferenceOfSum.difference_of_sum m = ok r_m), r.val = 9 * sumElems m + r_m.val) := by
    sorry

  /-- Let E = sum over i with 0 <= i < len(nums) of nums[i] and let D = sum over i with 0 <= i < len(nums) of ds(nums[i]), where ds(n) is the sum of the decimal digits of the positive integer n. Whenever the function returns a result r, r >= E - 28 * len(nums).
    Preconditions: 1 <= len(nums) <= 2000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 2000. -/
  theorem spec_10 (nums : Slice Std.I64) (r : Std.I64)
      (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 2000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000)
      (hr : Aegis.DifferenceOfSum.difference_of_sum nums = ok r) :
      r.val ≥ sumElems nums - 28 * (nums.length : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen : 1 ≤ nums.length) (hlen' : nums.length ≤ 2000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 2000)
        (hr : Aegis.DifferenceOfSum.difference_of_sum nums = ok r), r.val ≥ sumElems nums - 28 * (nums.length : ℤ)) := by
    sorry

  end AegisSpec.DifferenceOfSum
