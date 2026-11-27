import Aegis.SmallestNumber.Code.Funs

/-!
# Specifications of `Aegis.SmallestNumber.smallest_number`

LeetCode problem `smallest-value-of-the-rearranged-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SmallestNumber

  def bound : Int := 10 ^ 15

  def natDigits (n : Nat) : List Nat :=
    if n < 10 then [n] else natDigits (n / 10) ++ [n % 10]
  termination_by n
  decreasing_by omega

  def digitString (z : Int) : List Nat := natDigits z.natAbs

  def mostSigDigit (z : Int) : Option Nat := (digitString z).head?

  def SameSign (a b : Int) : Prop :=
    (a > 0 ∧ b > 0) ∨ (a < 0 ∧ b < 0) ∨ (a = 0 ∧ b = 0)

  def IsMinNonzeroDigit (d : Nat) (z : Int) : Prop :=
    d ∈ digitString z ∧ d ≠ 0 ∧ ∀ e, e ∈ digitString z → e ≠ 0 → d ≤ e

  def IsMaxDigit (d : Nat) (z : Int) : Prop :=
    d ∈ digitString z ∧ ∀ e, e ∈ digitString z → e ≤ d

  def AllDigitsEqual (z : Int) : Prop :=
    ∀ a, a ∈ digitString z → ∀ b, b ∈ digitString z → a = b

  def Nondecreasing (l : List Nat) : Prop := l.Pairwise (· ≤ ·)

  def Nonincreasing (l : List Nat) : Prop := l.Pairwise (· ≥ ·)

  def SameDigits (m z : Int) : Prop := List.Perm (digitString m) (digitString z)

  /-- Whenever the function returns a result r, r is the minimum, under the usual integer order, among all integers m satisfying: (1) m has the same sign as num, namely m > 0 if num > 0, m < 0 if num < 0, and m = 0 if num = 0; and (2) the decimal representation of |m| without leading zeros, with |0| represented by the single digit '0', has the same multiset of digits as the decimal representation of |num| without leading zeros. Equivalently, r belongs to this set and r <= m for every m in this set.
    Preconditions: num is a Std.I64 whose mathematical value satisfies -10^15 <= num <= 10^15. -/
  theorem spec_1 (num : Std.I64)
      (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound)
      (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r) :
      SameSign r.val num.val ∧ SameDigits r.val num.val ∧
        ∀ m : Int, SameSign m num.val → SameDigits m num.val → r.val ≤ m := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound)
        (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r), SameSign r.val num.val ∧ SameDigits r.val num.val ∧
          ∀ m : Int, SameSign m num.val → SameDigits m num.val → r.val ≤ m) := by
    sorry

  /-- The function returns a result r for every num satisfying the precondition; it does not fail, panic, or overflow.
    Preconditions: num is a Std.I64 whose mathematical value satisfies -10^15 <= num <= 10^15. -/
  theorem spec_2 (num : Std.I64)
      (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound) :
      ∃ r, Aegis.SmallestNumber.smallest_number num = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound), ∃ r, Aegis.SmallestNumber.smallest_number num = ok r) := by
    sorry

  /-- Whenever the function returns a result r: if num > 0 then r > 0, and if num < 0 then r < 0.
    Preconditions: num is a Std.I64 whose mathematical value satisfies -10^15 <= num <= 10^15 and num != 0. -/
  theorem spec_3 (num : Std.I64)
      (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound) (hne : num.val ≠ 0)
      (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r) :
      (num.val > 0 → r.val > 0) ∧ (num.val < 0 → r.val < 0) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound) (hne : num.val ≠ 0)
        (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r), (num.val > 0 → r.val > 0) ∧ (num.val < 0 → r.val < 0)) := by
    sorry

  /-- Whenever the function returns a result r, let digit_string(x) be the decimal representation of |x| without leading zeros, with digit_string(0) = '0'. Then the multiset of characters in digit_string(r) equals the multiset of characters in digit_string(num).
    Preconditions: num is a Std.I64 whose mathematical value satisfies -10^15 <= num <= 10^15. -/
  theorem spec_4 (num : Std.I64)
      (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound)
      (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r) :
      SameDigits r.val num.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound)
        (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r), SameDigits r.val num.val) := by
    sorry

  /-- Whenever the function returns a result r, let n be the number of decimal digits in |num|. Then |r| has exactly n decimal digits; equivalently, 10^(n-1) <= |r| <= 10^n - 1. In particular, the most significant decimal digit of |r| is nonzero.
    Preconditions: num is a Std.I64 whose mathematical value satisfies -10^15 <= num <= 10^15 and num != 0. -/
  theorem spec_5 (num : Std.I64)
      (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound) (hne : num.val ≠ 0)
      (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r) :
      let n := (digitString num.val).length
      (digitString r.val).length = n ∧
        (10 : Int) ^ (n - 1) ≤ |r.val| ∧ |r.val| ≤ (10 : Int) ^ n - 1 ∧
        mostSigDigit r.val ≠ some 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound) (hne : num.val ≠ 0)
        (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r), let n := (digitString num.val).length
        (digitString r.val).length = n ∧
          (10 : Int) ^ (n - 1) ≤ |r.val| ∧ |r.val| ≤ (10 : Int) ^ n - 1 ∧
          mostSigDigit r.val ≠ some 0) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: num is a Std.I64 whose mathematical value satisfies -10^15 <= num <= 10^15 and num = 0. -/
  theorem spec_6 (num : Std.I64)
      (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound) (hzero : num.val = 0)
      (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r) :
      r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound) (hzero : num.val = 0)
        (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r), r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r = num.
    Preconditions: num is a Std.I64 whose mathematical value satisfies -10^15 <= num <= 10^15, num != 0, and all decimal digits of |num| are equal (single-digit nonzero inputs are included). -/
  theorem spec_7 (num : Std.I64)
      (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound) (hne : num.val ≠ 0)
      (heq : AllDigitsEqual num.val)
      (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r) :
      r.val = num.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound) (hne : num.val ≠ 0)
        (heq : AllDigitsEqual num.val)
        (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r), r.val = num.val) := by
    sorry

  /-- Whenever the function returns a result r, let d be the smallest nonzero digit occurring in the decimal representation of num. Then the most significant decimal digit of |r| is d.
    Preconditions: num is a Std.I64 whose mathematical value satisfies -10^15 <= num <= 10^15 and num > 0. -/
  theorem spec_8 (num : Std.I64)
      (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound) (hpos : num.val > 0)
      (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r) :
      ∃ d, IsMinNonzeroDigit d num.val ∧ mostSigDigit r.val = some d := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound) (hpos : num.val > 0)
        (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r), ∃ d, IsMinNonzeroDigit d num.val ∧ mostSigDigit r.val = some d) := by
    sorry

  /-- Whenever the function returns a result r, after deleting the most significant digit from the decimal representation of |r|, the remaining digits, if any, form a nondecreasing sequence from left to right.
    Preconditions: num is a Std.I64 whose mathematical value satisfies -10^15 <= num <= 10^15 and num > 0. -/
  theorem spec_9 (num : Std.I64)
      (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound) (hpos : num.val > 0)
      (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r) :
      Nondecreasing (digitString r.val).tail := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound) (hpos : num.val > 0)
        (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r), Nondecreasing (digitString r.val).tail) := by
    sorry

  /-- Whenever the function returns a result r, let d be the largest decimal digit occurring in the decimal representation of |num|. Then the most significant decimal digit of |r| is d.
    Preconditions: num is a Std.I64 whose mathematical value satisfies -10^15 <= num <= 10^15 and num < 0. -/
  theorem spec_10 (num : Std.I64)
      (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound) (hneg : num.val < 0)
      (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r) :
      ∃ d, IsMaxDigit d num.val ∧ mostSigDigit r.val = some d := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound) (hneg : num.val < 0)
        (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r), ∃ d, IsMaxDigit d num.val ∧ mostSigDigit r.val = some d) := by
    sorry

  /-- Whenever the function returns a result r, after deleting the most significant digit from the decimal representation of |r|, the remaining digits, if any, form a nonincreasing sequence from left to right.
    Preconditions: num is a Std.I64 whose mathematical value satisfies -10^15 <= num <= 10^15 and num < 0. -/
  theorem spec_11 (num : Std.I64)
      (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound) (hneg : num.val < 0)
      (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r) :
      Nonincreasing (digitString r.val).tail := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound) (hneg : num.val < 0)
        (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r), Nonincreasing (digitString r.val).tail) := by
    sorry

  /-- If the function returns r1 on input num1 and r2 on input num2, then r1 = r2.
    Preconditions: num1 and num2 are Std.I64 values whose mathematical values each satisfy -10^15 <= num_i <= 10^15, and they have the same sign (both positive, both negative, or both zero) and the same multiset of decimal digits in their absolute values, with 0 represented as '0'. -/
  theorem spec_12 (num1 num2 : Std.I64)
      (h1lo : -bound ≤ num1.val) (h1hi : num1.val ≤ bound)
      (h2lo : -bound ≤ num2.val) (h2hi : num2.val ≤ bound)
      (hsgn : SameSign num1.val num2.val) (hdg : SameDigits num1 num2)
      (r1 : Std.I64) (hr1 : Aegis.SmallestNumber.smallest_number num1 = ok r1)
      (r2 : Std.I64) (hr2 : Aegis.SmallestNumber.smallest_number num2 = ok r2) :
      r1 = r2 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (num1 num2 : Std.I64)
        (h1lo : -bound ≤ num1.val) (h1hi : num1.val ≤ bound)
        (h2lo : -bound ≤ num2.val) (h2hi : num2.val ≤ bound)
        (hsgn : SameSign num1.val num2.val) (hdg : SameDigits num1 num2)
        (r1 : Std.I64) (hr1 : Aegis.SmallestNumber.smallest_number num1 = ok r1)
        (r2 : Std.I64) (hr2 : Aegis.SmallestNumber.smallest_number num2 = ok r2), r1 = r2) := by
    sorry

  /-- If the function returns r on input num, and then the function returns r2 on input r, then r2 = r.
    Preconditions: num is a Std.I64 whose mathematical value satisfies -10^15 <= num <= 10^15. -/
  theorem spec_13 (num : Std.I64)
      (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound)
      (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r)
      (r2 : Std.I64) (hr2 : Aegis.SmallestNumber.smallest_number r = ok r2) :
      r2 = r := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound)
        (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r)
        (r2 : Std.I64) (hr2 : Aegis.SmallestNumber.smallest_number r = ok r2), r2 = r) := by
    sorry

  /-- Whenever the function returns a result r, |r| <= 10^15.
    Preconditions: num is a Std.I64 whose mathematical value satisfies -10^15 <= num <= 10^15. -/
  theorem spec_14 (num : Std.I64)
      (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound)
      (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r) :
      |r.val| ≤ bound := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound)
        (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r), |r.val| ≤ bound) := by
    sorry

  /-- Whenever the function returns a result r, r <= num.
    Preconditions: num is a Std.I64 whose mathematical value satisfies -10^15 <= num <= 10^15. -/
  theorem spec_15 (num : Std.I64)
      (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound)
      (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r) :
      r.val ≤ num.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (num : Std.I64)
        (hlo : -bound ≤ num.val) (hhi : num.val ≤ bound)
        (r : Std.I64) (hr : Aegis.SmallestNumber.smallest_number num = ok r), r.val ≤ num.val) := by
    sorry

  end AegisSpec.SmallestNumber
