import Aegis.CountEven.Code.Funs

/-!
# Specifications of `Aegis.CountEven.count_even`

LeetCode problem `count-integers-with-even-digit-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountEven

  def digitSum (n : ℕ) : ℕ :=
    if h : n = 0 then 0 else n % 10 + digitSum (n / 10)
  termination_by n
  decreasing_by omega

  def hasEvenDigitSum (i : ℤ) : Bool := digitSum i.toNat % 2 == 0

  def evenDigitSumInts (n : ℤ) : List ℤ :=
    ((List.range n.toNat).map (fun k => (k : ℤ) + 1)).filter hasEvenDigitSum

  def countEvenDigitSum (n : ℤ) : ℤ := ((evenDigitSumInts n).length : ℤ)

  /-- The function returns a result r and r = the number of integers i such that 1 <= i <= num and ds(i) is even.
    Preconditions: num is an I64 whose mathematical value satisfies 1 <= num <= 1000. Let ds(i) denote the sum of the decimal digits of the positive integer i written in base 10 without leading zeros. -/
  theorem spec_1 (num : Std.I64) (hpos : 1 ≤ num.val) (hle : num.val ≤ 1000) :
      ∃ r : Std.I64, Aegis.CountEven.count_even num = ok r ∧
        r.val = countEvenDigitSum num.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (num : Std.I64) (hpos : 1 ≤ num.val) (hle : num.val ≤ 1000), ∃ r : Std.I64, Aegis.CountEven.count_even num = ok r ∧
          r.val = countEvenDigitSum num.val) := by
    sorry

  /-- The function returns a result r; it does not fail (no overflow, panic, or out-of-bounds) for any input satisfying the preconditions.
    Preconditions: num is an I64 whose mathematical value satisfies 1 <= num <= 1000. -/
  theorem spec_2 (num : Std.I64) (hpos : 1 ≤ num.val) (hle : num.val ≤ 1000) :
      ∃ r : Std.I64, Aegis.CountEven.count_even num = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (num : Std.I64) (hpos : 1 ≤ num.val) (hle : num.val ≤ 1000), ∃ r : Std.I64, Aegis.CountEven.count_even num = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= num.
    Preconditions: num is an I64 whose mathematical value satisfies 1 <= num <= 1000. -/
  theorem spec_3 (num : Std.I64) (hpos : 1 ≤ num.val) (hle : num.val ≤ 1000) (r : Std.I64)
      (hr : Aegis.CountEven.count_even num = ok r) :
      0 ≤ r.val ∧ r.val ≤ num.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (num : Std.I64) (hpos : 1 ≤ num.val) (hle : num.val ≤ 1000) (r : Std.I64)
        (hr : Aegis.CountEven.count_even num = ok r), 0 ≤ r.val ∧ r.val ≤ num.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= 499.
    Preconditions: num is an I64 whose mathematical value satisfies 1 <= num <= 1000. -/
  theorem spec_4 (num : Std.I64) (hpos : 1 ≤ num.val) (hle : num.val ≤ 1000) (r : Std.I64)
      (hr : Aegis.CountEven.count_even num = ok r) :
      r.val ≤ 499 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (num : Std.I64) (hpos : 1 ≤ num.val) (hle : num.val ≤ 1000) (r : Std.I64)
        (hr : Aegis.CountEven.count_even num = ok r), r.val ≤ 499) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if num = 1.
    Preconditions: num is an I64 whose mathematical value satisfies 1 <= num <= 1000. -/
  theorem spec_5 (num : Std.I64) (hpos : 1 ≤ num.val) (hle : num.val ≤ 1000) (r : Std.I64)
      (hr : Aegis.CountEven.count_even num = ok r) :
      r.val = 0 ↔ num.val = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (num : Std.I64) (hpos : 1 ≤ num.val) (hle : num.val ≤ 1000) (r : Std.I64)
        (hr : Aegis.CountEven.count_even num = ok r), r.val = 0 ↔ num.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, r = floor(num / 2), the number of even positive integers not exceeding num.
    Preconditions: num is an I64 whose mathematical value satisfies 1 <= num <= 9. -/
  theorem spec_6 (num : Std.I64) (hpos : 1 ≤ num.val) (hle : num.val ≤ 9) (r : Std.I64)
      (hr : Aegis.CountEven.count_even num = ok r) :
      r.val = num.val / 2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (num : Std.I64) (hpos : 1 ≤ num.val) (hle : num.val ≤ 9) (r : Std.I64)
        (hr : Aegis.CountEven.count_even num = ok r), r.val = num.val / 2) := by
    sorry

  /-- Whenever the function returns a result r, r = 4.
    Preconditions: num is an I64 and num = 10. -/
  theorem spec_7 (num : Std.I64) (hnum : num.val = 10) (r : Std.I64)
      (hr : Aegis.CountEven.count_even num = ok r) :
      r.val = 4 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (num : Std.I64) (hnum : num.val = 10) (r : Std.I64)
        (hr : Aegis.CountEven.count_even num = ok r), r.val = 4) := by
    sorry

  /-- Whenever the function returns a result r, r = 14.
    Preconditions: num is an I64 and num = 30. -/
  theorem spec_8 (num : Std.I64) (hnum : num.val = 30) (r : Std.I64)
      (hr : Aegis.CountEven.count_even num = ok r) :
      r.val = 14 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (num : Std.I64) (hnum : num.val = 30) (r : Std.I64)
        (hr : Aegis.CountEven.count_even num = ok r), r.val = 14) := by
    sorry

  /-- Whenever the function returns a result r, r = 249.
    Preconditions: num is an I64 and num = 500. -/
  theorem spec_9 (num : Std.I64) (hnum : num.val = 500) (r : Std.I64)
      (hr : Aegis.CountEven.count_even num = ok r) :
      r.val = 249 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (num : Std.I64) (hnum : num.val = 500) (r : Std.I64)
        (hr : Aegis.CountEven.count_even num = ok r), r.val = 249) := by
    sorry

  /-- Whenever the function returns a result r, r = 499.
    Preconditions: num is an I64 and num = 999. -/
  theorem spec_10 (num : Std.I64) (hnum : num.val = 999) (r : Std.I64)
      (hr : Aegis.CountEven.count_even num = ok r) :
      r.val = 499 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (num : Std.I64) (hnum : num.val = 999) (r : Std.I64)
        (hr : Aegis.CountEven.count_even num = ok r), r.val = 499) := by
    sorry

  /-- Whenever the function returns a result r, r = (the number of integers i with 1 <= i < num and ds(i) even) + (1 if ds(num) is even, otherwise 0).
    Preconditions: num is an I64 whose mathematical value satisfies 1 <= num <= 1000. Let ds(i) denote the sum of the decimal digits of the positive integer i. -/
  theorem spec_11 (num : Std.I64) (hpos : 1 ≤ num.val) (hle : num.val ≤ 1000) (r : Std.I64)
      (hr : Aegis.CountEven.count_even num = ok r) :
      r.val = countEvenDigitSum (num.val - 1) + (if hasEvenDigitSum num.val then 1 else 0) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (num : Std.I64) (hpos : 1 ≤ num.val) (hle : num.val ≤ 1000) (r : Std.I64)
        (hr : Aegis.CountEven.count_even num = ok r), r.val = countEvenDigitSum (num.val - 1) + (if hasEvenDigitSum num.val then 1 else 0)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k with 1 <= k < num, the number of integers i with 1 <= i <= k and ds(i) even is at most r.
    Preconditions: num is an I64 whose mathematical value satisfies 1 <= num <= 1000. Let ds(i) denote the sum of the decimal digits of the positive integer i. -/
  theorem spec_12 (num : Std.I64) (hpos : 1 ≤ num.val) (hle : num.val ≤ 1000) (r : Std.I64)
      (hr : Aegis.CountEven.count_even num = ok r) :
      ∀ k : ℤ, 1 ≤ k → k < num.val → countEvenDigitSum k ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (num : Std.I64) (hpos : 1 ≤ num.val) (hle : num.val ≤ 1000) (r : Std.I64)
        (hr : Aegis.CountEven.count_even num = ok r), ∀ k : ℤ, 1 ≤ k → k < num.val → countEvenDigitSum k ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r >= 1 and the integer 2, whose digit sum is 2 and hence even, is one of the integers counted in the main specification.
    Preconditions: num is an I64 whose mathematical value satisfies 2 <= num <= 1000. -/
  theorem spec_13 (num : Std.I64) (hpos : 2 ≤ num.val) (hle : num.val ≤ 1000) (r : Std.I64)
      (hr : Aegis.CountEven.count_even num = ok r) :
      1 ≤ r.val ∧ digitSum 2 = 2 ∧ (2 : ℤ) ∈ evenDigitSumInts num.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (num : Std.I64) (hpos : 2 ≤ num.val) (hle : num.val ≤ 1000) (r : Std.I64)
        (hr : Aegis.CountEven.count_even num = ok r), 1 ≤ r.val ∧ digitSum 2 = 2 ∧ (2 : ℤ) ∈ evenDigitSumInts num.val) := by
    sorry

  end AegisSpec.CountEven
