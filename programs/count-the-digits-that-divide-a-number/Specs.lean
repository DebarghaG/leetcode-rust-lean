import Aegis.CountDigits.Code.Funs

/-!
# Specifications of `Aegis.CountDigits.count_digits`

LeetCode problem `count-the-digits-that-divide-a-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.CountDigits

namespace AegisSpec.CountDigits

def numDigits (n : Nat) : Nat := if n = 0 then 0 else Nat.log 10 n + 1

def digitFromLeft (n i : Nat) : Nat := (n / 10 ^ (numDigits n - 1 - i)) % 10

def decDigits (n : Nat) : List Nat := (List.range (numDigits n)).map (fun i => digitFromLeft n i)

def noZeroDigit (n : Nat) : Prop := ∀ d ∈ decDigits n, d ≠ 0

def countDigitOcc (n d : Nat) : Nat := (decDigits n).count d

def lastDigit (n : Nat) : Nat := n % 10

/-- Let k be the number of decimal digits of num and, for each i with 0 <= i < k, let d_i = (num / 10^(k-1-i)) mod 10 be the i-th digit from the left. Whenever count_digits returns a result r, r is equal to the number of indices i with 0 <= i < k such that num % d_i = 0.
  Preconditions: 1 <= num <= 1000000000 and the usual decimal representation of num contains no digit 0. -/
theorem spec_1 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r) :
    r.val = (((List.range (numDigits num.val.natAbs)).filter
      (fun i => num.val % (digitFromLeft num.val.natAbs i : Int) = 0)).length : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r), r.val = (((List.range (numDigits num.val.natAbs)).filter
      (fun i => num.val % (digitFromLeft num.val.natAbs i : Int) = 0)).length : Int)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow.
  Preconditions: 1 <= num <= 1000000000 and the usual decimal representation of num contains no digit 0. -/
theorem spec_2 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs) :
    ∃ r, count_digits num = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs), ∃ r, count_digits num = ok r) := by
  sorry

/-- Whenever count_digits returns a result r, 0 <= r <= 9.
  Preconditions: 1 <= num <= 1000000000 and the usual decimal representation of num contains no digit 0. -/
theorem spec_3 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r) :
    0 ≤ r.val ∧ r.val ≤ 9 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r), 0 ≤ r.val ∧ r.val ≤ 9) := by
  sorry

/-- Whenever count_digits returns a result r, r <= k, where k is the number of decimal digits of num.
  Preconditions: 1 <= num <= 1000000000 and the usual decimal representation of num contains no digit 0. -/
theorem spec_4 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r) :
    r.val ≤ (numDigits num.val.natAbs : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r), r.val ≤ (numDigits num.val.natAbs : Int)) := by
  sorry

/-- Whenever count_digits returns a result r, r = 1.
  Preconditions: 1 <= num <= 9 and the usual decimal representation of num contains no digit 0. -/
theorem spec_5 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 9)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r) :
    r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 9)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r), r.val = 1) := by
  sorry

/-- Let k be the number of decimal digits of num and, for each i with 0 <= i < k, let d_i be the i-th digit from the left. Whenever count_digits returns a result r, if num % d_i = 0 for every i with 0 <= i < k, then r = k.
  Preconditions: 1 <= num <= 1000000000 and the usual decimal representation of num contains no digit 0. -/
theorem spec_6 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r)
    (hdiv : ∀ i, i < numDigits num.val.natAbs →
      num.val % (digitFromLeft num.val.natAbs i : Int) = 0) :
    r.val = (numDigits num.val.natAbs : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r)
    (hdiv : ∀ i, i < numDigits num.val.natAbs →
      num.val % (digitFromLeft num.val.natAbs i : Int) = 0), r.val = (numDigits num.val.natAbs : Int)) := by
  sorry

/-- Let k be the number of decimal digits of num and, for each i with 0 <= i < k, let d_i be the i-th digit from the left. Whenever count_digits returns a result r, if num % d_i != 0 for every i with 0 <= i < k, then r = 0.
  Preconditions: 1 <= num <= 1000000000 and the usual decimal representation of num contains no digit 0. -/
theorem spec_7 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r)
    (hndiv : ∀ i, i < numDigits num.val.natAbs →
      num.val % (digitFromLeft num.val.natAbs i : Int) ≠ 0) :
    r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r)
    (hndiv : ∀ i, i < numDigits num.val.natAbs →
      num.val % (digitFromLeft num.val.natAbs i : Int) ≠ 0), r.val = 0) := by
  sorry

/-- Let m_1 be the number of occurrences of the digit 1 in the decimal representation of num. Whenever count_digits returns a result r, r >= m_1.
  Preconditions: 1 <= num <= 1000000000 and the usual decimal representation of num contains no digit 0. -/
theorem spec_8 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r) :
    (countDigitOcc num.val.natAbs 1 : Int) ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r), (countDigitOcc num.val.natAbs 1 : Int) ≤ r.val) := by
  sorry

/-- Let m_2 be the number of occurrences of the digit 2 in the decimal representation of num. Whenever count_digits returns a result r, if the last decimal digit of num is even, then r >= m_2.
  Preconditions: 1 <= num <= 1000000000 and the usual decimal representation of num contains no digit 0. -/
theorem spec_9 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r)
    (heven : lastDigit num.val.natAbs % 2 = 0) :
    (countDigitOcc num.val.natAbs 2 : Int) ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r)
    (heven : lastDigit num.val.natAbs % 2 = 0), (countDigitOcc num.val.natAbs 2 : Int) ≤ r.val) := by
  sorry

/-- Let m_5 be the number of occurrences of the digit 5 in the decimal representation of num. Whenever count_digits returns a result r, if the last decimal digit of num is 5, then r >= m_5.
  Preconditions: 1 <= num <= 1000000000 and the usual decimal representation of num contains no digit 0. -/
theorem spec_10 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r)
    (hlast : lastDigit num.val.natAbs = 5) :
    (countDigitOcc num.val.natAbs 5 : Int) ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r)
    (hlast : lastDigit num.val.natAbs = 5), (countDigitOcc num.val.natAbs 5 : Int) ≤ r.val) := by
  sorry

/-- Let k be the number of decimal digits of num. Whenever count_digits returns a result r, if all decimal digits of num are equal to the same nonzero digit d, then r = k.
  Preconditions: 1 <= num <= 1000000000 and the usual decimal representation of num contains no digit 0. -/
theorem spec_11 (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r)
    (hall : ∃ d, d ≠ 0 ∧ ∀ i, i < numDigits num.val.natAbs →
      digitFromLeft num.val.natAbs i = d) :
    r.val = (numDigits num.val.natAbs : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (num : Std.I64) (h1 : 1 ≤ num.val) (h2 : num.val ≤ 1000000000)
    (hz : noZeroDigit num.val.natAbs) (r : Std.I64) (hr : count_digits num = ok r)
    (hall : ∃ d, d ≠ 0 ∧ ∀ i, i < numDigits num.val.natAbs →
      digitFromLeft num.val.natAbs i = d), r.val = (numDigits num.val.natAbs : Int)) := by
  sorry

end AegisSpec.CountDigits
