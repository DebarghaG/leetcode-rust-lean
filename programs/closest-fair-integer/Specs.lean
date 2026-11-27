import Aegis.ClosestFair.Code.Funs
import Mathlib.Data.Nat.Digits.Defs

/-!
# Specifications of `Aegis.ClosestFair.closest_fair`

LeetCode problem `closest-fair-integer`. Each `spec_<n>` theorem states one property of the function.
-/

namespace AegisSpec.ClosestFair

open Aeneas Aeneas.Std Result

def digitsOf (n : Nat) : List Nat := Nat.digits 10 n

def evenDigitCount (n : Nat) : Nat := (digitsOf n).countP fun d => d % 2 == 0

def oddDigitCount (n : Nat) : Nat := (digitsOf n).countP fun d => d % 2 == 1

def fairNat (n : Nat) : Prop := evenDigitCount n = oddDigitCount n

def IsFair (z : Int) : Prop := 0 < z ∧ fairNat z.natAbs

def numDigits (z : Int) : Nat := (digitsOf z.natAbs).length

/-- Whenever closest_fair(n) returns a result r, r is the smallest fair integer greater than or equal to n: (1) r >= n; (2) r is fair, meaning its decimal representation with no leading zeros has exactly as many even digits (0,2,4,6,8) as odd digits (1,3,5,7,9); and (3) for every integer m with n <= m < r, m is not fair.
  Preconditions: n is an integer with 1 <= n <= 10^9. -/
theorem spec_1 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ (10 : Int) ^ 9) :
    ∀ r : Std.I64, Aegis.ClosestFair.closest_fair n = ok r →
      n.val ≤ r.val ∧ IsFair r.val ∧ (∀ m : Int, n.val ≤ m → m < r.val → ¬ IsFair m) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ (10 : Int) ^ 9), ∀ r : Std.I64, Aegis.ClosestFair.closest_fair n = ok r →
      n.val ≤ r.val ∧ IsFair r.val ∧ (∀ m : Int, n.val ≤ m → m < r.val → ¬ IsFair m)) := by
  sorry

/-- closest_fair(n) returns a result (it does not fail).
  Preconditions: n is an integer with 1 <= n <= 10^9. -/
theorem spec_2 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ (10 : Int) ^ 9) :
    ∃ r : Std.I64, Aegis.ClosestFair.closest_fair n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ (10 : Int) ^ 9), ∃ r : Std.I64, Aegis.ClosestFair.closest_fair n = ok r) := by
  sorry

/-- Whenever closest_fair(n) returns a result r, r = n if and only if n is fair, where fair means its decimal representation with no leading zeros has equally many even digits (0,2,4,6,8) and odd digits (1,3,5,7,9).
  Preconditions: n is an integer with 1 <= n <= 10^9. -/
theorem spec_3 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ (10 : Int) ^ 9) :
    ∀ r : Std.I64, Aegis.ClosestFair.closest_fair n = ok r → (r.val = n.val ↔ IsFair n.val) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ (10 : Int) ^ 9), ∀ r : Std.I64, Aegis.ClosestFair.closest_fair n = ok r → (r.val = n.val ↔ IsFair n.val)) := by
  sorry

/-- Whenever closest_fair(n) returns a result r, if n is not fair, where fair means its decimal representation with no leading zeros has equally many even digits (0,2,4,6,8) and odd digits (1,3,5,7,9), then r > n.
  Preconditions: n is an integer with 1 <= n <= 10^9. -/
theorem spec_4 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ (10 : Int) ^ 9) :
    ∀ r : Std.I64, Aegis.ClosestFair.closest_fair n = ok r → ¬ IsFair n.val → n.val < r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ (10 : Int) ^ 9), ∀ r : Std.I64, Aegis.ClosestFair.closest_fair n = ok r → ¬ IsFair n.val → n.val < r.val) := by
  sorry

/-- Whenever closest_fair(n) returns a result r, the decimal representation of r without leading zeros has a positive even number of digits.
  Preconditions: n is an integer with 1 <= n <= 10^9. -/
theorem spec_5 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ (10 : Int) ^ 9) :
    ∀ r : Std.I64, Aegis.ClosestFair.closest_fair n = ok r →
      0 < numDigits r.val ∧ numDigits r.val % 2 = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ (10 : Int) ^ 9), ∀ r : Std.I64, Aegis.ClosestFair.closest_fair n = ok r →
      0 < numDigits r.val ∧ numDigits r.val % 2 = 0) := by
  sorry

/-- Whenever closest_fair(n) returns a result r, r <= 1000001111.
  Preconditions: n is an integer with 1 <= n <= 10^9. -/
theorem spec_6 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ (10 : Int) ^ 9) :
    ∀ r : Std.I64, Aegis.ClosestFair.closest_fair n = ok r → r.val ≤ 1000001111 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ (10 : Int) ^ 9), ∀ r : Std.I64, Aegis.ClosestFair.closest_fair n = ok r → r.val ≤ 1000001111) := by
  sorry

/-- If closest_fair(n1) returns r1 and closest_fair(n2) returns r2, then r1 <= r2.
  Preconditions: n1 and n2 are integers with 1 <= n1 <= n2 <= 10^9. -/
theorem spec_7 (n1 n2 : Std.I64)
    (h1 : 1 ≤ n1.val ∧ n1.val ≤ (10 : Int) ^ 9)
    (h2 : 1 ≤ n2.val ∧ n2.val ≤ (10 : Int) ^ 9)
    (h12 : n1.val ≤ n2.val) :
    ∀ r1 r2 : Std.I64, Aegis.ClosestFair.closest_fair n1 = ok r1 →
      Aegis.ClosestFair.closest_fair n2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n1 n2 : Std.I64)
    (h1 : 1 ≤ n1.val ∧ n1.val ≤ (10 : Int) ^ 9)
    (h2 : 1 ≤ n2.val ∧ n2.val ≤ (10 : Int) ^ 9)
    (h12 : n1.val ≤ n2.val), ∀ r1 r2 : Std.I64, Aegis.ClosestFair.closest_fair n1 = ok r1 →
      Aegis.ClosestFair.closest_fair n2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- Whenever closest_fair(n) returns a result r, if the decimal representation of n without leading zeros has an odd number d of digits, then the decimal representation of r without leading zeros has exactly d + 1 digits.
  Preconditions: n is an integer with 1 <= n <= 10^9. -/
theorem spec_8 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ (10 : Int) ^ 9) :
    ∀ r : Std.I64, Aegis.ClosestFair.closest_fair n = ok r →
      numDigits n.val % 2 = 1 → numDigits r.val = numDigits n.val + 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ (10 : Int) ^ 9), ∀ r : Std.I64, Aegis.ClosestFair.closest_fair n = ok r →
      numDigits n.val % 2 = 1 → numDigits r.val = numDigits n.val + 1) := by
  sorry

/-- Whenever closest_fair(n) returns a result r, r = 10.
  Preconditions: n is an integer with 1 <= n <= 10. -/
theorem spec_9 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10) :
    ∀ r : Std.I64, Aegis.ClosestFair.closest_fair n = ok r → r.val = 10 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10), ∀ r : Std.I64, Aegis.ClosestFair.closest_fair n = ok r → r.val = 10) := by
  sorry

/-- Whenever closest_fair(n) returns a result r, if the decimal representation of n without leading zeros has an even number d of digits, then the decimal representation of r without leading zeros has either d or d + 2 digits.
  Preconditions: n is an integer with 1 <= n <= 10^9. -/
theorem spec_10 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ (10 : Int) ^ 9) :
    ∀ r : Std.I64, Aegis.ClosestFair.closest_fair n = ok r →
      numDigits n.val % 2 = 0 →
      numDigits r.val = numDigits n.val ∨ numDigits r.val = numDigits n.val + 2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ (10 : Int) ^ 9), ∀ r : Std.I64, Aegis.ClosestFair.closest_fair n = ok r →
      numDigits n.val % 2 = 0 →
      numDigits r.val = numDigits n.val ∨ numDigits r.val = numDigits n.val + 2) := by
  sorry

end AegisSpec.ClosestFair
