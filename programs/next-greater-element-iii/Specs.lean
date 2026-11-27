import Aegis.NextGreaterElement.Code.Funs

/-!
# Specifications of `Aegis.NextGreaterElement.next_greater_element`

LeetCode problem `next-greater-element-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aeneas.Std.Result

namespace AegisSpec.NextGreaterElement

def M : ℤ := 2147483647

def digitsAux : Nat → Nat → List Nat
  | 0, _ => []
  | _, 0 => []
  | f + 1, k + 1 => (k + 1) % 10 :: digitsAux f ((k + 1) / 10)

def digitsNat (n : Nat) : List Nat := digitsAux (n + 1) n

def digitsMSD (x : ℤ) : List Nat := (digitsNat x.natAbs).reverse

def digitMultiset (x : ℤ) : Multiset Nat := (digitsNat x.natAbs : Multiset Nat)

def numDigits (x : ℤ) : Nat := (digitsNat x.natAbs).length

def digitsNonIncreasing (x : ℤ) : Prop := (digitsMSD x).Pairwise (· ≥ ·)

def candidates (n : ℤ) : Set ℤ := {x | n < x ∧ x ≤ M ∧ digitMultiset x = digitMultiset n}

def largerCandidates (n : ℤ) : Set ℤ := {y | n < y ∧ digitMultiset y = digitMultiset n}

/-- Let M = 2147483647 and, for every positive integer x, let D(x) be the multiset of decimal digits in the standard decimal representation of x (multiplicities counted). Whenever next_greater_element(n) returns a result r, the following holds: if the set S = {x : n < x <= M and D(x) = D(n)} is nonempty, then r = min(S); if S is empty, then r = -1.
  Preconditions: 1 <= n <= 2147483647. -/
theorem spec_1 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M) :
    ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      ((∃ x : ℤ, x ∈ candidates n.val) → IsLeast (candidates n.val) r.val) ∧
      (¬ (∃ x : ℤ, x ∈ candidates n.val) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M), ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      ((∃ x : ℤ, x ∈ candidates n.val) → IsLeast (candidates n.val) r.val) ∧
      (¬ (∃ x : ℤ, x ∈ candidates n.val) → r.val = -1)) := by
  sorry

/-- next_greater_element(n) returns a result r; it does not fail, panic, or overflow for any n in this range.
  Preconditions: 1 <= n <= 2147483647. -/
theorem spec_2 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M) :
    ∃ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M), ∃ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r) := by
  sorry

/-- Whenever next_greater_element(n) returns a result r, either r = -1 or (1 <= r <= 2147483647).
  Preconditions: 1 <= n <= 2147483647. -/
theorem spec_3 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M) :
    ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ M) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M), ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ M)) := by
  sorry

/-- Whenever next_greater_element(n) returns a result r with r != -1, we have r > n.
  Preconditions: 1 <= n <= 2147483647. -/
theorem spec_4 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M) :
    ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      r.val ≠ -1 → n.val < r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M), ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      r.val ≠ -1 → n.val < r.val) := by
  sorry

/-- Let D(x) be the multiset of decimal digits in the standard decimal representation of the positive integer x, with multiplicities counted. Whenever next_greater_element(n) returns a result r with r != -1, we have D(r) = D(n).
  Preconditions: 1 <= n <= 2147483647. -/
theorem spec_5 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M) :
    ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      r.val ≠ -1 → digitMultiset r.val = digitMultiset n.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M), ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      r.val ≠ -1 → digitMultiset r.val = digitMultiset n.val) := by
  sorry

/-- Whenever next_greater_element(n) returns a result r with r != -1, the number of decimal digits of r equals the number of decimal digits of n.
  Preconditions: 1 <= n <= 2147483647. -/
theorem spec_6 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M) :
    ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      r.val ≠ -1 → numDigits r.val = numDigits n.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M), ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      r.val ≠ -1 → numDigits r.val = numDigits n.val) := by
  sorry

/-- Let D(x) be the multiset of decimal digits in the standard decimal representation of the positive integer x, with multiplicities counted. Whenever next_greater_element(n) returns a result r with r != -1, for every integer x such that n < x and D(x) = D(n), we have r <= x.
  Preconditions: 1 <= n <= 2147483647. -/
theorem spec_7 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M) :
    ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      r.val ≠ -1 →
        ∀ x : ℤ, n.val < x → digitMultiset x = digitMultiset n.val → r.val ≤ x := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M), ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      r.val ≠ -1 →
        ∀ x : ℤ, n.val < x → digitMultiset x = digitMultiset n.val → r.val ≤ x) := by
  sorry

/-- Let D(x) be the multiset of decimal digits in the standard decimal representation of the positive integer x, with multiplicities counted. Whenever next_greater_element(n) returns a result r, r = -1 if and only if there is no integer x with n < x <= 2147483647 and D(x) = D(n).
  Preconditions: 1 <= n <= 2147483647. -/
theorem spec_8 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M) :
    ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      (r.val = -1 ↔ ¬ (∃ x : ℤ, x ∈ candidates n.val)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M), ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      (r.val = -1 ↔ ¬ (∃ x : ℤ, x ∈ candidates n.val))) := by
  sorry

/-- Whenever next_greater_element(n) returns a result r, r = -1.
  Preconditions: 1 <= n <= 2147483647. The decimal digits of n, read from most significant to least significant, are non-increasing (each digit is greater than or equal to the next digit). -/
theorem spec_9 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M)
    (hd : digitsNonIncreasing n.val) :
    ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      r.val = -1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M)
    (hd : digitsNonIncreasing n.val), ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      r.val = -1) := by
  sorry

/-- Let D(x) be the multiset of decimal digits in the standard decimal representation of the positive integer x, with multiplicities counted. Whenever next_greater_element(n) returns a result r, r = -1 if and only if the decimal digits of n, read from most significant to least significant, are non-increasing (each digit is >= the next digit).
  Preconditions: 1 <= n <= 999999999. -/
theorem spec_10 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 999999999) :
    ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      (r.val = -1 ↔ digitsNonIncreasing n.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 999999999), ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      (r.val = -1 ↔ digitsNonIncreasing n.val)) := by
  sorry

/-- Write n = 10*a + b with 1 <= a <= 9 and 0 <= b <= 9. Whenever next_greater_element(n) returns a result r, if b > a then r = 10*b + a, and if b <= a then r = -1.
  Preconditions: 10 <= n <= 99. -/
theorem spec_11 (n : Std.I64) (hn1 : 10 ≤ n.val) (hn2 : n.val ≤ 99)
    (a b : ℤ) (ha1 : 1 ≤ a) (ha9 : a ≤ 9) (hb0 : 0 ≤ b) (hb9 : b ≤ 9)
    (hn : n.val = 10 * a + b) :
    ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      (b > a → r.val = 10 * b + a) ∧ (b ≤ a → r.val = -1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 10 ≤ n.val) (hn2 : n.val ≤ 99)
    (a b : ℤ) (ha1 : 1 ≤ a) (ha9 : a ≤ 9) (hb0 : 0 ≤ b) (hb9 : b ≤ 9)
    (hn : n.val = 10 * a + b), ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      (b > a → r.val = 10 * b + a) ∧ (b ≤ a → r.val = -1)) := by
  sorry

/-- Let D(x) be the multiset of decimal digits in the standard decimal representation of the positive integer x, with multiplicities counted. Whenever next_greater_element(n) returns a result r, if there exists at least one integer y with y > n and D(y) = D(n), and the least such y is greater than 2147483647, then r = -1.
  Preconditions: 1 <= n <= 2147483647. -/
theorem spec_12 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M) :
    ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      (∃ y : ℤ, y ∈ largerCandidates n.val) →
      (∃ y : ℤ, IsLeast (largerCandidates n.val) y ∧ M < y) →
      r.val = -1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M), ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      (∃ y : ℤ, y ∈ largerCandidates n.val) →
      (∃ y : ℤ, IsLeast (largerCandidates n.val) y ∧ M < y) →
      r.val = -1) := by
  sorry

/-- Let D(x) be the multiset of decimal digits in the standard decimal representation of the positive integer x, with multiplicities counted. Whenever next_greater_element(n) returns a result r, if there exists an integer x with n < x <= 2147483647 and D(x) = D(n), then n < r <= 2147483647 and D(r) = D(n).
  Preconditions: 1 <= n <= 2147483647. -/
theorem spec_13 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M) :
    ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      (∃ x : ℤ, x ∈ candidates n.val) →
      n.val < r.val ∧ r.val ≤ M ∧ digitMultiset r.val = digitMultiset n.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ M), ∀ r : Std.I64, Aegis.NextGreaterElement.next_greater_element n = ok r →
      (∃ x : ℤ, x ∈ candidates n.val) →
      n.val < r.val ∧ r.val ≤ M ∧ digitMultiset r.val = digitMultiset n.val) := by
  sorry

end AegisSpec.NextGreaterElement
