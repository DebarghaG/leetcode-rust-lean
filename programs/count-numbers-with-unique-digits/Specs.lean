import Aegis.CountNumbersWithUniqueDigits.Code.Funs

/-!
# Specifications of `Aegis.CountNumbersWithUniqueDigits.count_numbers_with_unique_digits`

LeetCode problem `count-numbers-with-unique-digits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountNumbersWithUniqueDigits (count_numbers_with_unique_digits)

  namespace AegisSpec.CountNumbersWithUniqueDigits

  def digitsOf (x : Nat) : List Nat :=
    if h : x = 0 then [] else x % 10 :: digitsOf (x / 10)
  termination_by x
  decreasing_by
    exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide : 1 < 10)

  def decimalDigits (x : Nat) : List Nat :=
    if x = 0 then [0] else (digitsOf x).reverse

  abbrev hasUniqueDigits (x : Nat) : Prop := (decimalDigits x).Nodup

  def countUniqueInRange (lo hi : Nat) : Nat :=
    ((Finset.Ico lo hi).filter hasUniqueDigits).card

  def countUniqueBelowPow (m : Nat) : Nat := countUniqueInRange 0 (10 ^ m)

  def fallingFactorial (a : Nat) : Nat → Nat
    | 0 => 1
    | (b + 1) => fallingFactorial a b * (a - b)

  /-- The function returns a result r and r is exactly the number of integers x with 0 <= x < 10^n for which the usual decimal representation of x contains no digit more than once. The usual decimal representation has no leading zeros, except that the integer 0 is represented by the single digit 0.
    Preconditions: n is a 64-bit signed integer with 0 <= n <= 8. -/
  theorem spec_1 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn8 : n.val ≤ 8) :
      ∃ r, count_numbers_with_unique_digits n = ok r ∧
        r.val = (countUniqueBelowPow n.val.toNat : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn8 : n.val ≤ 8), ∃ r, count_numbers_with_unique_digits n = ok r ∧
          r.val = (countUniqueBelowPow n.val.toNat : Int)) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or overflow.
    Preconditions: n is a 64-bit signed integer with 0 <= n <= 8. -/
  theorem spec_2 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn8 : n.val ≤ 8) :
      ∃ r, count_numbers_with_unique_digits n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn8 : n.val ≤ 8), ∃ r, count_numbers_with_unique_digits n = ok r) := by
    sorry

  /-- The function returns a result r and r >= 1.
    Preconditions: n is a 64-bit signed integer with 0 <= n <= 8. -/
  theorem spec_3 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn8 : n.val ≤ 8) :
      ∃ r, count_numbers_with_unique_digits n = ok r ∧ 1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn8 : n.val ≤ 8), ∃ r, count_numbers_with_unique_digits n = ok r ∧ 1 ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= 10^n.
    Preconditions: n is a 64-bit signed integer with 0 <= n <= 8. -/
  theorem spec_4 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn8 : n.val ≤ 8) :
      ∃ r, count_numbers_with_unique_digits n = ok r ∧
        r.val ≤ ((10 ^ n.val.toNat : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn8 : n.val ≤ 8), ∃ r, count_numbers_with_unique_digits n = ok r ∧
          r.val ≤ ((10 ^ n.val.toNat : Nat) : Int)) := by
    sorry

  /-- The function returns a result r and r < 10^n.
    Preconditions: n is a 64-bit signed integer with 2 <= n <= 8. -/
  theorem spec_5 (n : Std.I64) (hn2 : 2 ≤ n.val) (hn8 : n.val ≤ 8) :
      ∃ r, count_numbers_with_unique_digits n = ok r ∧
        r.val < ((10 ^ n.val.toNat : Nat) : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn2 : 2 ≤ n.val) (hn8 : n.val ≤ 8), ∃ r, count_numbers_with_unique_digits n = ok r ∧
          r.val < ((10 ^ n.val.toNat : Nat) : Int)) := by
    sorry

  /-- The function returns a result r and r >= 10.
    Preconditions: n is a 64-bit signed integer with 1 <= n <= 8. -/
  theorem spec_6 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn8 : n.val ≤ 8) :
      ∃ r, count_numbers_with_unique_digits n = ok r ∧ 10 ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn8 : n.val ≤ 8), ∃ r, count_numbers_with_unique_digits n = ok r ∧ 10 ≤ r.val) := by
    sorry

  /-- The function returns a result r and r = 1 + sum_{k=1}^{n} (9 * (9)_{k-1}), where (a)_b = a*(a-1)*...*(a-b+1) for b >= 0, with (a)_0 = 1, and the sum is empty when n = 0.
    Preconditions: n is a 64-bit signed integer with 0 <= n <= 8. -/
  theorem spec_7 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn8 : n.val ≤ 8) :
      ∃ r, count_numbers_with_unique_digits n = ok r ∧
        r.val = ((1 + ∑ k ∈ Finset.Icc 1 n.val.toNat,
          9 * fallingFactorial 9 (k - 1) : Nat) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn8 : n.val ≤ 8), ∃ r, count_numbers_with_unique_digits n = ok r ∧
          r.val = ((1 + ∑ k ∈ Finset.Icc 1 n.val.toNat,
            9 * fallingFactorial 9 (k - 1) : Nat) : Int)) := by
    sorry

  /-- The function returns a result r and, if for each k with 1 <= k <= n we let C_k be the number of integers x such that 10^{k-1} <= x < 10^k and the usual decimal representation of x contains no digit more than once, then r = 1 + sum_{k=1}^{n} C_k.
    Preconditions: n is a 64-bit signed integer with 0 <= n <= 8. -/
  theorem spec_8 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn8 : n.val ≤ 8) :
      ∃ r, count_numbers_with_unique_digits n = ok r ∧
        r.val = ((1 + ∑ k ∈ Finset.Icc 1 n.val.toNat,
          countUniqueInRange (10 ^ (k - 1)) (10 ^ k) : Nat) : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn8 : n.val ≤ 8), ∃ r, count_numbers_with_unique_digits n = ok r ∧
          r.val = ((1 + ∑ k ∈ Finset.Icc 1 n.val.toNat,
            countUniqueInRange (10 ^ (k - 1)) (10 ^ k) : Nat) : Int)) := by
    sorry

  /-- The function returns a result r and r mod 9 = 1.
    Preconditions: n is a 64-bit signed integer with 0 <= n <= 8. -/
  theorem spec_9 (n : Std.I64) (hn0 : 0 ≤ n.val) (hn8 : n.val ≤ 8) :
      ∃ r, count_numbers_with_unique_digits n = ok r ∧ r.val % 9 = 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hn0 : 0 ≤ n.val) (hn8 : n.val ≤ 8), ∃ r, count_numbers_with_unique_digits n = ok r ∧ r.val % 9 = 1) := by
    sorry

  /-- The function returns a result r and r mod 8 = 3.
    Preconditions: n is a 64-bit signed integer with 2 <= n <= 8. -/
  theorem spec_10 (n : Std.I64) (hn2 : 2 ≤ n.val) (hn8 : n.val ≤ 8) :
      ∃ r, count_numbers_with_unique_digits n = ok r ∧ r.val % 8 = 3 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hn2 : 2 ≤ n.val) (hn8 : n.val ≤ 8), ∃ r, count_numbers_with_unique_digits n = ok r ∧ r.val % 8 = 3) := by
    sorry

  end AegisSpec.CountNumbersWithUniqueDigits
