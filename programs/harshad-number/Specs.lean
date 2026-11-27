import Aegis.SumOfTheDigitsOfHarshadNumber.Code.Funs

/-!
# Specifications of `Aegis.SumOfTheDigitsOfHarshadNumber.sum_of_the_digits_of_harshad_number`

LeetCode problem `harshad-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SumOfTheDigitsOfHarshadNumber

  def digit_sum (x : ℤ) : ℤ := x / 100 + (x / 10) % 10 + x % 10

  /-- Let s = x / 100 + (x / 10) mod 10 + x mod 10, the sum of the decimal digits of x. The function returns a result r and: if x mod s = 0 then r = s; if x mod s != 0 then r = -1.
    Preconditions: 1 <= x <= 100 -/
  theorem spec_1 (x : Std.I64) (hx_low : 1 ≤ x.val) (hx_high : x.val ≤ 100) :
      ∃ r : Std.I64,
        Aegis.SumOfTheDigitsOfHarshadNumber.sum_of_the_digits_of_harshad_number x = ok r ∧
          (if x.val % digit_sum x.val = 0 then r.val = digit_sum x.val else r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (x : Std.I64) (hx_low : 1 ≤ x.val) (hx_high : x.val ≤ 100), ∃ r : Std.I64,
          Aegis.SumOfTheDigitsOfHarshadNumber.sum_of_the_digits_of_harshad_number x = ok r ∧
            (if x.val % digit_sum x.val = 0 then r.val = digit_sum x.val else r.val = -1)) := by
    sorry

  /-- For every x with 1 <= x <= 100, the function returns a result r (it does not fail, overflow, or panic).
    Preconditions: 1 <= x <= 100 -/
  theorem spec_2 (x : Std.I64) (hx_low : 1 ≤ x.val) (hx_high : x.val ≤ 100) :
      ∃ r : Std.I64,
        Aegis.SumOfTheDigitsOfHarshadNumber.sum_of_the_digits_of_harshad_number x = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (x : Std.I64) (hx_low : 1 ≤ x.val) (hx_high : x.val ≤ 100), ∃ r : Std.I64,
          Aegis.SumOfTheDigitsOfHarshadNumber.sum_of_the_digits_of_harshad_number x = ok r) := by
    sorry

  /-- Whenever the function returns a result r, -1 <= r <= 18.
    Preconditions: 1 <= x <= 100 -/
  theorem spec_3 (x : Std.I64) (hx_low : 1 ≤ x.val) (hx_high : x.val ≤ 100)
      (r : Std.I64)
      (hr : Aegis.SumOfTheDigitsOfHarshadNumber.sum_of_the_digits_of_harshad_number x = ok r) :
      -1 ≤ r.val ∧ r.val ≤ 18 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (x : Std.I64) (hx_low : 1 ≤ x.val) (hx_high : x.val ≤ 100)
        (r : Std.I64)
        (hr : Aegis.SumOfTheDigitsOfHarshadNumber.sum_of_the_digits_of_harshad_number x = ok r), -1 ≤ r.val ∧ r.val ≤ 18) := by
    sorry

  /-- Whenever the function returns a result r, letting s = x / 100 + (x / 10) mod 10 + x mod 10 (the sum of the decimal digits of x), either r = -1 or r = s.
    Preconditions: 1 <= x <= 100 -/
  theorem spec_4 (x : Std.I64) (hx_low : 1 ≤ x.val) (hx_high : x.val ≤ 100)
      (r : Std.I64)
      (hr : Aegis.SumOfTheDigitsOfHarshadNumber.sum_of_the_digits_of_harshad_number x = ok r) :
      r.val = -1 ∨ r.val = digit_sum x.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (x : Std.I64) (hx_low : 1 ≤ x.val) (hx_high : x.val ≤ 100)
        (r : Std.I64)
        (hr : Aegis.SumOfTheDigitsOfHarshadNumber.sum_of_the_digits_of_harshad_number x = ok r), r.val = -1 ∨ r.val = digit_sum x.val) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, letting s = x / 100 + (x / 10) mod 10 + x mod 10 (the sum of the decimal digits of x), we have r = s and r > 0 and x mod r = 0.
    Preconditions: 1 <= x <= 100 -/
  theorem spec_5 (x : Std.I64) (hx_low : 1 ≤ x.val) (hx_high : x.val ≤ 100)
      (r : Std.I64)
      (hr : Aegis.SumOfTheDigitsOfHarshadNumber.sum_of_the_digits_of_harshad_number x = ok r)
      (hr_ne : r.val ≠ -1) :
      r.val = digit_sum x.val ∧ 0 < r.val ∧ x.val % r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (x : Std.I64) (hx_low : 1 ≤ x.val) (hx_high : x.val ≤ 100)
        (r : Std.I64)
        (hr : Aegis.SumOfTheDigitsOfHarshadNumber.sum_of_the_digits_of_harshad_number x = ok r)
        (hr_ne : r.val ≠ -1), r.val = digit_sum x.val ∧ 0 < r.val ∧ x.val % r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r with r = -1, letting s = x / 100 + (x / 10) mod 10 + x mod 10 (the sum of the decimal digits of x), we have x mod s != 0.
    Preconditions: 1 <= x <= 100 -/
  theorem spec_6 (x : Std.I64) (hx_low : 1 ≤ x.val) (hx_high : x.val ≤ 100)
      (r : Std.I64)
      (hr : Aegis.SumOfTheDigitsOfHarshadNumber.sum_of_the_digits_of_harshad_number x = ok r)
      (hr_eq : r.val = -1) :
      x.val % digit_sum x.val ≠ 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (x : Std.I64) (hx_low : 1 ≤ x.val) (hx_high : x.val ≤ 100)
        (r : Std.I64)
        (hr : Aegis.SumOfTheDigitsOfHarshadNumber.sum_of_the_digits_of_harshad_number x = ok r)
        (hr_eq : r.val = -1), x.val % digit_sum x.val ≠ 0) := by
    sorry

  /-- The function returns a result r equal to x.
    Preconditions: 1 <= x <= 9 -/
  theorem spec_7 (x : Std.I64) (hx_low : 1 ≤ x.val) (hx_high : x.val ≤ 9) :
      ∃ r : Std.I64,
        Aegis.SumOfTheDigitsOfHarshadNumber.sum_of_the_digits_of_harshad_number x = ok r ∧
          r.val = x.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (x : Std.I64) (hx_low : 1 ≤ x.val) (hx_high : x.val ≤ 9), ∃ r : Std.I64,
          Aegis.SumOfTheDigitsOfHarshadNumber.sum_of_the_digits_of_harshad_number x = ok r ∧
            r.val = x.val) := by
    sorry

  end AegisSpec.SumOfTheDigitsOfHarshadNumber
