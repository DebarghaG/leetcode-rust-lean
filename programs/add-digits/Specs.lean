import Aegis.AddDigits.Code.Funs

/-!
# Specifications of `Aegis.AddDigits.add_digits`

LeetCode problem `add-digits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.AddDigits

def i64OfInt (n : ℤ) : Aeneas.Std.I64 :=
  Aeneas.Std.IScalar.mk (BitVec.ofNat 64 n.toNat)

def digitSum : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) % 10 + digitSum ((n + 1) / 10)
termination_by n => n
decreasing_by omega

/-- Whenever add_digits(num) returns a result r, r is the digital root of num: r = 0 if num = 0, and r = 1 + ((num - 1) mod 9) if num > 0. Equivalently, for num > 0, r is the unique integer with 1 <= r <= 9 and r ≡ num (mod 9).
  Preconditions: num is a 64-bit integer with 0 <= num <= 2147483647. -/
theorem spec_1 (num : Aeneas.Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 2147483647)
    (r : Aeneas.Std.I64) (hr : Aegis.AddDigits.add_digits num = ok r) :
    (num.val = 0 → r.val = 0) ∧ (0 < num.val → r.val = 1 + (num.val - 1) % 9) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (num : Aeneas.Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 2147483647)
    (r : Aeneas.Std.I64) (hr : Aegis.AddDigits.add_digits num = ok r), (num.val = 0 → r.val = 0) ∧ (0 < num.val → r.val = 1 + (num.val - 1) % 9)) := by
  sorry

/-- For every num with 0 <= num <= 2147483647, add_digits(num) returns a result r; it does not fail, overflow, panic, or go out of bounds.
  Preconditions: num is a 64-bit integer with 0 <= num <= 2147483647. -/
theorem spec_2 (num : Aeneas.Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 2147483647) :
    ∃ r : Aeneas.Std.I64, Aegis.AddDigits.add_digits num = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (num : Aeneas.Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 2147483647), ∃ r : Aeneas.Std.I64, Aegis.AddDigits.add_digits num = ok r) := by
  sorry

/-- Whenever add_digits(num) returns a result r, 0 <= r <= 9.
  Preconditions: num is a 64-bit integer with 0 <= num <= 2147483647. -/
theorem spec_3 (num : Aeneas.Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 2147483647)
    (r : Aeneas.Std.I64) (hr : Aegis.AddDigits.add_digits num = ok r) :
    0 ≤ r.val ∧ r.val ≤ 9 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (num : Aeneas.Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 2147483647)
    (r : Aeneas.Std.I64) (hr : Aegis.AddDigits.add_digits num = ok r), 0 ≤ r.val ∧ r.val ≤ 9) := by
  sorry

/-- Whenever add_digits(num) returns a result r, r = num.
  Preconditions: 0 <= num <= 9. -/
theorem spec_4 (num : Aeneas.Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 9)
    (r : Aeneas.Std.I64) (hr : Aegis.AddDigits.add_digits num = ok r) :
    r.val = num.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (num : Aeneas.Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 9)
    (r : Aeneas.Std.I64) (hr : Aegis.AddDigits.add_digits num = ok r), r.val = num.val) := by
  sorry

/-- Whenever add_digits(num) returns a result r, r = 9.
  Preconditions: 0 < num <= 2147483647 and num mod 9 = 0. -/
theorem spec_5 (num : Aeneas.Std.I64) (hlo : 0 < num.val) (hhi : num.val ≤ 2147483647)
    (hmod : num.val % 9 = 0) (r : Aeneas.Std.I64)
    (hr : Aegis.AddDigits.add_digits num = ok r) :
    r.val = 9 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (num : Aeneas.Std.I64) (hlo : 0 < num.val) (hhi : num.val ≤ 2147483647)
    (hmod : num.val % 9 = 0) (r : Aeneas.Std.I64)
    (hr : Aegis.AddDigits.add_digits num = ok r), r.val = 9) := by
  sorry

/-- Whenever add_digits(num) returns a result r, r ≡ num (mod 9); equivalently, num - r is divisible by 9.
  Preconditions: num is a 64-bit integer with 0 <= num <= 2147483647. -/
theorem spec_6 (num : Aeneas.Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 2147483647)
    (r : Aeneas.Std.I64) (hr : Aegis.AddDigits.add_digits num = ok r) :
    (9 : ℤ) ∣ num.val - r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (num : Aeneas.Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 2147483647)
    (r : Aeneas.Std.I64) (hr : Aegis.AddDigits.add_digits num = ok r), (9 : ℤ) ∣ num.val - r.val) := by
  sorry

/-- Whenever add_digits(num) returns a result r, r = 0 if and only if num = 0.
  Preconditions: num is a 64-bit integer with 0 <= num <= 2147483647. -/
theorem spec_7 (num : Aeneas.Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 2147483647)
    (r : Aeneas.Std.I64) (hr : Aegis.AddDigits.add_digits num = ok r) :
    r.val = 0 ↔ num.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (num : Aeneas.Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 2147483647)
    (r : Aeneas.Std.I64) (hr : Aegis.AddDigits.add_digits num = ok r), r.val = 0 ↔ num.val = 0) := by
  sorry

/-- Let S(n) be the sum of the decimal digits of n. Whenever both add_digits(n) and add_digits(S(n)) return results r and r', we have r = r'.
  Preconditions: n is an integer with 0 <= n <= 2147483647 and n >= 10. -/
theorem spec_8 (n : Aeneas.Std.I64) (hlo : 0 ≤ n.val) (hhi : n.val ≤ 2147483647)
    (hge : 10 ≤ n.val) (r r' : Aeneas.Std.I64)
    (hr : Aegis.AddDigits.add_digits n = ok r)
    (hr' : Aegis.AddDigits.add_digits (i64OfInt (digitSum n.val.toNat)) = ok r') :
    r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hlo : 0 ≤ n.val) (hhi : n.val ≤ 2147483647)
    (hge : 10 ≤ n.val) (r r' : Aeneas.Std.I64)
    (hr : Aegis.AddDigits.add_digits n = ok r)
    (hr' : Aegis.AddDigits.add_digits (i64OfInt (digitSum n.val.toNat)) = ok r'), r = r') := by
  sorry

/-- Whenever both add_digits(num) and add_digits(num + 9) return results r and r', we have r = r'.
  Preconditions: 1 <= num <= 2147483638. -/
theorem spec_9 (num : Aeneas.Std.I64) (hlo : 1 ≤ num.val) (hhi : num.val ≤ 2147483638)
    (r r' : Aeneas.Std.I64)
    (hr : Aegis.AddDigits.add_digits num = ok r)
    (hr' : Aegis.AddDigits.add_digits (i64OfInt (num.val + 9)) = ok r') :
    r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (num : Aeneas.Std.I64) (hlo : 1 ≤ num.val) (hhi : num.val ≤ 2147483638)
    (r r' : Aeneas.Std.I64)
    (hr : Aegis.AddDigits.add_digits num = ok r)
    (hr' : Aegis.AddDigits.add_digits (i64OfInt (num.val + 9)) = ok r'), r = r') := by
  sorry

/-- Whenever add_digits(num) returns a result r, add_digits(r) returns the result r.
  Preconditions: 0 <= num <= 2147483647. -/
theorem spec_10 (num : Aeneas.Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 2147483647)
    (r : Aeneas.Std.I64) (hr : Aegis.AddDigits.add_digits num = ok r) :
    Aegis.AddDigits.add_digits r = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (num : Aeneas.Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 2147483647)
    (r : Aeneas.Std.I64) (hr : Aegis.AddDigits.add_digits num = ok r), Aegis.AddDigits.add_digits r = ok r) := by
  sorry

/-- Whenever add_digits(num) returns a result r, r = 1.
  Preconditions: num = 2147483647. -/
theorem spec_11 (num : Aeneas.Std.I64) (hnum : num.val = 2147483647)
    (r : Aeneas.Std.I64) (hr : Aegis.AddDigits.add_digits num = ok r) :
    r.val = 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (num : Aeneas.Std.I64) (hnum : num.val = 2147483647)
    (r : Aeneas.Std.I64) (hr : Aegis.AddDigits.add_digits num = ok r), r.val = 1) := by
  sorry

/-- Whenever add_digits(num) returns a result r, r is the smallest positive integer d such that num - d is divisible by 9.
  Preconditions: 0 < num <= 2147483647. -/
theorem spec_12 (num : Aeneas.Std.I64) (hlo : 0 < num.val) (hhi : num.val ≤ 2147483647)
    (r : Aeneas.Std.I64) (hr : Aegis.AddDigits.add_digits num = ok r) :
    0 < r.val ∧ (9 : ℤ) ∣ num.val - r.val ∧
      ∀ d : ℤ, 0 < d → (9 : ℤ) ∣ num.val - d → r.val ≤ d := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (num : Aeneas.Std.I64) (hlo : 0 < num.val) (hhi : num.val ≤ 2147483647)
    (r : Aeneas.Std.I64) (hr : Aegis.AddDigits.add_digits num = ok r), 0 < r.val ∧ (9 : ℤ) ∣ num.val - r.val ∧
      ∀ d : ℤ, 0 < d → (9 : ℤ) ∣ num.val - d → r.val ≤ d) := by
  sorry

end AegisSpec.AddDigits
