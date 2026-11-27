import Aegis.CountSpecialNumbers.Code.Funs

/-!
# Specifications of `Aegis.CountSpecialNumbers.count_special_numbers`

LeetCode problem `count-special-integers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountSpecialNumbers

open Aegis.CountSpecialNumbers (count_special_numbers)

def digitsOf (x : Nat) : List Nat :=
  match x with
  | 0 => []
  | k + 1 => digitsOf ((k + 1) / 10) ++ [(k + 1) % 10]
termination_by x
decreasing_by omega

@[reducible] def DigitsDistinct (x : Nat) : Prop := (digitsOf x).Nodup

def specialNumbers (n : Nat) : Finset Nat :=
  (Finset.Icc 1 n).filter (fun x => (digitsOf x).Nodup)

def specialNumbersOfLength (n d : Nat) : Finset Nat :=
  (Finset.Icc 1 n).filter (fun x => (digitsOf x).length = d ∧ (digitsOf x).Nodup)

/-- Whenever count_special_numbers(n) returns a result r, r is the cardinality of the set of integers x such that 1 <= x <= n and the decimal representation of x (written without leading zeros) has pairwise distinct digits; that is, for every two distinct digit positions i and j of x, the digit at i is different from the digit at j.
  Preconditions: 1 <= n <= 2000000000. -/
theorem spec_1 (n : Std.I64) (hn : 1 <= n.val ∧ n.val <= 2000000000) :
    ∀ r : Std.I64, count_special_numbers n = ok r →
      r.val = ((specialNumbers n.val.toNat).card : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 <= n.val ∧ n.val <= 2000000000), ∀ r : Std.I64, count_special_numbers n = ok r →
      r.val = ((specialNumbers n.val.toNat).card : Int)) := by
  sorry

/-- The call count_special_numbers(n) returns a result; it does not fail by overflow, panic, or out-of-bounds access.
  Preconditions: 1 <= n <= 2000000000. -/
theorem spec_2 (n : Std.I64) (hn : 1 <= n.val ∧ n.val <= 2000000000) :
    ∃ r : Std.I64, count_special_numbers n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 <= n.val ∧ n.val <= 2000000000), ∃ r : Std.I64, count_special_numbers n = ok r) := by
  sorry

/-- Whenever count_special_numbers(n) returns a result r, 1 <= r.
  Preconditions: 1 <= n <= 2000000000. -/
theorem spec_3 (n : Std.I64) (hn : 1 <= n.val ∧ n.val <= 2000000000) :
    ∀ r : Std.I64, count_special_numbers n = ok r → 1 <= r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 <= n.val ∧ n.val <= 2000000000), ∀ r : Std.I64, count_special_numbers n = ok r → 1 <= r.val) := by
  sorry

/-- Whenever count_special_numbers(n) returns a result r, r <= n.
  Preconditions: 1 <= n <= 2000000000. -/
theorem spec_4 (n : Std.I64) (hn : 1 <= n.val ∧ n.val <= 2000000000) :
    ∀ r : Std.I64, count_special_numbers n = ok r → r.val <= n.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 <= n.val ∧ n.val <= 2000000000), ∀ r : Std.I64, count_special_numbers n = ok r → r.val <= n.val) := by
  sorry

/-- Whenever count_special_numbers(n) returns a result r, r <= 8877690.
  Preconditions: 1 <= n <= 2000000000. -/
theorem spec_5 (n : Std.I64) (hn : 1 <= n.val ∧ n.val <= 2000000000) :
    ∀ r : Std.I64, count_special_numbers n = ok r → r.val <= 8877690 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 <= n.val ∧ n.val <= 2000000000), ∀ r : Std.I64, count_special_numbers n = ok r → r.val <= 8877690) := by
  sorry

/-- Whenever count_special_numbers(n) returns a result r, r = n.
  Preconditions: 1 <= n <= 9. -/
theorem spec_6 (n : Std.I64) (hn : 1 <= n.val ∧ n.val <= 9) :
    ∀ r : Std.I64, count_special_numbers n = ok r → r.val = n.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 <= n.val ∧ n.val <= 9), ∀ r : Std.I64, count_special_numbers n = ok r → r.val = n.val) := by
  sorry

/-- Whenever count_special_numbers(n) returns a result r, r = 10.
  Preconditions: n = 10. -/
theorem spec_7 (n : Std.I64) (hn : n.val = 10) :
    ∀ r : Std.I64, count_special_numbers n = ok r → r.val = 10 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 10), ∀ r : Std.I64, count_special_numbers n = ok r → r.val = 10) := by
  sorry

/-- Whenever count_special_numbers(n) returns a result r, r = 738.
  Preconditions: n = 999. -/
theorem spec_8 (n : Std.I64) (hn : n.val = 999) :
    ∀ r : Std.I64, count_special_numbers n = ok r → r.val = 738 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 999), ∀ r : Std.I64, count_special_numbers n = ok r → r.val = 738) := by
  sorry

/-- Whenever count_special_numbers(n) returns a result r, r = 5274.
  Preconditions: n = 10000. -/
theorem spec_9 (n : Std.I64) (hn : n.val = 10000) :
    ∀ r : Std.I64, count_special_numbers n = ok r → r.val = 5274 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 10000), ∀ r : Std.I64, count_special_numbers n = ok r → r.val = 5274) := by
  sorry

/-- Whenever count_special_numbers(n) returns a result r, r = 5611770.
  Preconditions: n = 1000000000. -/
theorem spec_10 (n : Std.I64) (hn : n.val = 1000000000) :
    ∀ r : Std.I64, count_special_numbers n = ok r → r.val = 5611770 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 1000000000), ∀ r : Std.I64, count_special_numbers n = ok r → r.val = 5611770) := by
  sorry

/-- Whenever count_special_numbers(n) returns a result r, r = 5974650.
  Preconditions: n = 2000000000. -/
theorem spec_11 (n : Std.I64) (hn : n.val = 2000000000) :
    ∀ r : Std.I64, count_special_numbers n = ok r → r.val = 5974650 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 2000000000), ∀ r : Std.I64, count_special_numbers n = ok r → r.val = 5974650) := by
  sorry

/-- If count_special_numbers(a) returns r_a and count_special_numbers(b) returns r_b, then r_a <= r_b.
  Preconditions: 1 <= a <= b <= 2000000000. -/
theorem spec_12 (a b : Std.I64) (ha : 1 <= a.val ∧ a.val <= b.val)
    (hb : b.val <= 2000000000) :
    ∀ r_a r_b : Std.I64,
      count_special_numbers a = ok r_a → count_special_numbers b = ok r_b →
        r_a.val <= r_b.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (a b : Std.I64) (ha : 1 <= a.val ∧ a.val <= b.val)
    (hb : b.val <= 2000000000), ∀ r_a r_b : Std.I64,
      count_special_numbers a = ok r_a → count_special_numbers b = ok r_b →
        r_a.val <= r_b.val) := by
  sorry

/-- If count_special_numbers(n) returns r and count_special_numbers(n+1) returns s, then s = r + 1 when the decimal representation of n+1 has pairwise distinct digits, and s = r otherwise.
  Preconditions: 1 <= n < 2000000000. -/
theorem spec_13 (n n1 : Std.I64) (hn : 1 <= n.val ∧ n.val < 2000000000)
    (hn1 : n1.val = n.val + 1) :
    ∀ r s : Std.I64,
      count_special_numbers n = ok r → count_special_numbers n1 = ok s →
        (DigitsDistinct (n.val.toNat + 1) → s.val = r.val + 1) ∧
        (¬ DigitsDistinct (n.val.toNat + 1) → s.val = r.val) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n n1 : Std.I64) (hn : 1 <= n.val ∧ n.val < 2000000000)
    (hn1 : n1.val = n.val + 1), ∀ r s : Std.I64,
      count_special_numbers n = ok r → count_special_numbers n1 = ok s →
        (DigitsDistinct (n.val.toNat + 1) → s.val = r.val + 1) ∧
        (¬ DigitsDistinct (n.val.toNat + 1) → s.val = r.val)) := by
  sorry

/-- Whenever count_special_numbers(n) returns a result r, let c_d be the number of d-digit positive integers x such that x <= n and the decimal digits of x are pairwise distinct, for d = 1,2,...,10. Then r = c_1 + c_2 + ... + c_10.
  Preconditions: 1 <= n <= 2000000000. -/
theorem spec_14 (n : Std.I64) (hn : 1 <= n.val ∧ n.val <= 2000000000) :
    ∀ r : Std.I64, count_special_numbers n = ok r →
      r.val = ((Finset.Icc 1 10).sum (fun d => (specialNumbersOfLength n.val.toNat d).card) :
        Int) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 <= n.val ∧ n.val <= 2000000000), ∀ r : Std.I64, count_special_numbers n = ok r →
      r.val = ((Finset.Icc 1 10).sum (fun d => (specialNumbersOfLength n.val.toNat d).card) :
        Int)) := by
  sorry

end AegisSpec.CountSpecialNumbers
