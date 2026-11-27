import Aegis.IsSameAfterReversals.Code.Funs

/-!
# Specifications of `Aegis.IsSameAfterReversals.is_same_after_reversals`

LeetCode problem `a-number-after-a-double-reversal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace AegisSpec.IsSameAfterReversals

def revAux : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | fuel + 1, n, acc => if n = 0 then acc else revAux fuel (n / 10) (acc * 10 + n % 10)

def revNat (n : Nat) : Nat := revAux (n + 1) n 0

def rev (n : Int) : Int := (revNat n.toNat : Int)

def digitsAux : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | fuel + 1, n, acc => if n = 0 then acc else digitsAux fuel (n / 10) (acc + 1)

def digitsNat (n : Nat) : Nat := if n = 0 then 1 else digitsAux (n + 1) n 0

def numDigits (n : Int) : Nat := digitsNat n.toNat

/-- The function returns a result r (it does not fail) and r = true if and only if rev(rev(num)) = num, where for a non-negative integer n, rev(n) is the integer obtained by writing n in decimal, reversing the order of the digits, and dropping any leading zeros (so rev(0) = 0).
  Preconditions: num is an I64 and 0 <= num <= 10^6. -/
theorem spec_1 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 10 ^ 6) :
    ∃ r, Aegis.IsSameAfterReversals.is_same_after_reversals num = ok r ∧
      (r = true ↔ rev (rev num.val) = num.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 10 ^ 6), ∃ r, Aegis.IsSameAfterReversals.is_same_after_reversals num = ok r ∧
      (r = true ↔ rev (rev num.val) = num.val)) := by
  sorry

/-- The function returns a result r for every such num; in particular, it does not overflow, panic, or otherwise fail.
  Preconditions: num is an I64 and 0 <= num <= 10^6. -/
theorem spec_2 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 10 ^ 6) :
    ∃ r, Aegis.IsSameAfterReversals.is_same_after_reversals num = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 10 ^ 6), ∃ r, Aegis.IsSameAfterReversals.is_same_after_reversals num = ok r) := by
  sorry

/-- The function returns a result r and r = true if and only if num = 0 or the last decimal digit of num is nonzero (equivalently, num mod 10 != 0).
  Preconditions: num is an I64 and 0 <= num <= 10^6. -/
theorem spec_3 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 10 ^ 6) :
    ∃ r, Aegis.IsSameAfterReversals.is_same_after_reversals num = ok r ∧
      (r = true ↔ (num.val = 0 ∨ num.val % 10 ≠ 0)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 10 ^ 6), ∃ r, Aegis.IsSameAfterReversals.is_same_after_reversals num = ok r ∧
      (r = true ↔ (num.val = 0 ∨ num.val % 10 ≠ 0))) := by
  sorry

/-- The function returns a result r and r = true if and only if d(rev(num)) = d(num), where rev reverses decimal digits and drops leading zeros as in spec_1, and d(n) is the number of decimal digits of n with d(0) = 1.
  Preconditions: num is an I64 and 0 <= num <= 10^6. -/
theorem spec_4 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 10 ^ 6) :
    ∃ r, Aegis.IsSameAfterReversals.is_same_after_reversals num = ok r ∧
      (r = true ↔ numDigits (rev num.val) = numDigits num.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 10 ^ 6), ∃ r, Aegis.IsSameAfterReversals.is_same_after_reversals num = ok r ∧
      (r = true ↔ numDigits (rev num.val) = numDigits num.val)) := by
  sorry

/-- Let x = 10 * num. The function returns a result r on input x, and r = true if and only if num = 0.
  Preconditions: num is an I64 and 0 <= num <= 100000. -/
theorem spec_5 (num x : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 100000)
    (hx : x.val = 10 * num.val) :
    ∃ r, Aegis.IsSameAfterReversals.is_same_after_reversals x = ok r ∧
      (r = true ↔ num.val = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (num x : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 100000)
    (hx : x.val = 10 * num.val), ∃ r, Aegis.IsSameAfterReversals.is_same_after_reversals x = ok r ∧
      (r = true ↔ num.val = 0)) := by
  sorry

/-- Let x = 10 * num + digit. The function returns a result r on input x, and r = true.
  Preconditions: num is an I64, 0 <= num <= 99999, and digit is an integer with 1 <= digit <= 9. -/
theorem spec_6 (num x : Std.I64) (digit : Int) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 99999)
    (hdlo : 1 ≤ digit) (hdhi : digit ≤ 9) (hx : x.val = 10 * num.val + digit) :
    ∃ r, Aegis.IsSameAfterReversals.is_same_after_reversals x = ok r ∧ r = true := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (num x : Std.I64) (digit : Int) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 99999)
    (hdlo : 1 ≤ digit) (hdhi : digit ≤ 9) (hx : x.val = 10 * num.val + digit), ∃ r, Aegis.IsSameAfterReversals.is_same_after_reversals x = ok r ∧ r = true) := by
  sorry

/-- Let x = rev(num), where rev reverses decimal digits and drops leading zeros as in spec_1. The function returns a result r on input x, and r = true.
  Preconditions: num is an I64 and 0 <= num <= 10^6. -/
theorem spec_7 (num x : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 10 ^ 6)
    (hx : x.val = rev num.val) :
    ∃ r, Aegis.IsSameAfterReversals.is_same_after_reversals x = ok r ∧ r = true := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (num x : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 10 ^ 6)
    (hx : x.val = rev num.val), ∃ r, Aegis.IsSameAfterReversals.is_same_after_reversals x = ok r ∧ r = true) := by
  sorry

/-- If (num1 = 0 if and only if num2 = 0) and the last decimal digit of num1 equals the last decimal digit of num2, then the function returns the same Boolean value on num1 and num2 (if it returns r1 on num1 and r2 on num2, then r1 = r2).
  Preconditions: num1 and num2 are I64 values with 0 <= num1 <= 10^6 and 0 <= num2 <= 10^6. -/
theorem spec_8 (num1 num2 : Std.I64) (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 10 ^ 6)
    (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 10 ^ 6)
    (hzero : (num1.val = 0 ↔ num2.val = 0)) (hdigit : num1.val % 10 = num2.val % 10) :
    ∀ r1 r2, Aegis.IsSameAfterReversals.is_same_after_reversals num1 = ok r1 →
      Aegis.IsSameAfterReversals.is_same_after_reversals num2 = ok r2 → r1 = r2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (num1 num2 : Std.I64) (h1lo : 0 ≤ num1.val) (h1hi : num1.val ≤ 10 ^ 6)
    (h2lo : 0 ≤ num2.val) (h2hi : num2.val ≤ 10 ^ 6)
    (hzero : (num1.val = 0 ↔ num2.val = 0)) (hdigit : num1.val % 10 = num2.val % 10), ∀ r1 r2, Aegis.IsSameAfterReversals.is_same_after_reversals num1 = ok r1 →
      Aegis.IsSameAfterReversals.is_same_after_reversals num2 = ok r2 → r1 = r2) := by
  sorry

end AegisSpec.IsSameAfterReversals
