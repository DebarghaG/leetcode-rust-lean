import Aegis.SumOfNumberAndReverse.Code.Funs

/-!
# Specifications of `Aegis.SumOfNumberAndReverse.sum_of_number_and_reverse`

LeetCode problem `sum-of-number-and-its-reverse`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SumOfNumberAndReverse

  def decimalDigitsRev (x : Nat) : List Nat :=
    if h : x = 0 then [] else x % 10 :: decimalDigitsRev (x / 10)
  termination_by x
  decreasing_by
    exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

  def reverseDigits (x : Nat) : Nat :=
    (decimalDigitsRev x).foldl (fun acc d => acc * 10 + d) 0

  def digitCount (x : Nat) : Nat :=
    if x = 0 then 1 else (decimalDigitsRev x).length

  /-- Whenever the function returns a result r, r is true if and only if there exists a non-negative integer x with 0 <= x <= num such that x + reverse(x) = num. Here reverse(0)=0; for x>0, if x has decimal digits d_0,...,d_{k-1} with d_0 the units digit, d_{k-1} != 0, and each d_i in {0,...,9}, then reverse(x) = sum_{i=0}^{k-1} d_i * 10^(k-1-i), so leading zeros in the reversed decimal form are discarded.
    Preconditions: num is an i64 with 0 <= num <= 100000 (the problem's bound 0 <= num <= 10^5). -/
  theorem spec_1 (num : Std.I64) (h0 : 0 ≤ num.val) (hle : num.val ≤ 100000) :
      ∀ r : Bool,
        Aegis.SumOfNumberAndReverse.sum_of_number_and_reverse num = ok r →
          (r = true ↔
            ∃ x : Nat,
              (x : Int) ≤ num.val ∧ (x : Int) + (reverseDigits x : Int) = num.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (num : Std.I64) (h0 : 0 ≤ num.val) (hle : num.val ≤ 100000), ∀ r : Bool,
          Aegis.SumOfNumberAndReverse.sum_of_number_and_reverse num = ok r →
            (r = true ↔
              ∃ x : Nat,
                (x : Int) ≤ num.val ∧ (x : Int) + (reverseDigits x : Int) = num.val)) := by
    sorry

  /-- For every num satisfying the precondition, the function returns a Bool result r; it does not fail, panic, or overflow on these inputs.
    Preconditions: num is an i64 with 0 <= num <= 100000. -/
  theorem spec_2 (num : Std.I64) (h0 : 0 ≤ num.val) (hle : num.val ≤ 100000) :
      ∃ r : Bool, Aegis.SumOfNumberAndReverse.sum_of_number_and_reverse num = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (num : Std.I64) (h0 : 0 ≤ num.val) (hle : num.val ≤ 100000), ∃ r : Bool, Aegis.SumOfNumberAndReverse.sum_of_number_and_reverse num = ok r) := by
    sorry

  /-- Whenever the function returns false for num, there is no non-negative integer x such that x + reverse(x) = num; equivalently, there is no x with 0 <= x <= num satisfying this equation.
    Preconditions: num is an i64 with 0 <= num <= 100000. -/
  theorem spec_3 (num : Std.I64) (h0 : 0 ≤ num.val) (hle : num.val ≤ 100000)
      (hres : Aegis.SumOfNumberAndReverse.sum_of_number_and_reverse num = ok false) :
      ¬ ∃ x : Nat, (x : Int) + (reverseDigits x : Int) = num.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (num : Std.I64) (h0 : 0 ≤ num.val) (hle : num.val ≤ 100000)
        (hres : Aegis.SumOfNumberAndReverse.sum_of_number_and_reverse num = ok false), ¬ ∃ x : Nat, (x : Int) + (reverseDigits x : Int) = num.val) := by
    sorry

  /-- Whenever the function returns true for num, there exists an integer x with 0 <= x <= num such that x + reverse(x) = num. Thus a witness never needs to be larger than num.
    Preconditions: num is an i64 with 0 <= num <= 100000. -/
  theorem spec_4 (num : Std.I64) (h0 : 0 ≤ num.val) (hle : num.val ≤ 100000)
      (hres : Aegis.SumOfNumberAndReverse.sum_of_number_and_reverse num = ok true) :
      ∃ x : Nat,
        (x : Int) ≤ num.val ∧ (x : Int) + (reverseDigits x : Int) = num.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (num : Std.I64) (h0 : 0 ≤ num.val) (hle : num.val ≤ 100000)
        (hres : Aegis.SumOfNumberAndReverse.sum_of_number_and_reverse num = ok true), ∃ x : Nat,
          (x : Int) ≤ num.val ∧ (x : Int) + (reverseDigits x : Int) = num.val) := by
    sorry

  /-- Whenever the function returns true for num and num is not divisible by 11 (num mod 11 != 0), there exists a witness x with 0 <= x <= num and x+reverse(x)=num whose decimal representation, written without leading zeros and with 0 represented by the single digit 0, has an odd number of digits.
    Preconditions: num is an i64 with 0 <= num <= 100000. -/
  theorem spec_5 (num : Std.I64) (h0 : 0 ≤ num.val) (hle : num.val ≤ 100000)
      (hres : Aegis.SumOfNumberAndReverse.sum_of_number_and_reverse num = ok true)
      (h11 : num.val % 11 ≠ 0) :
      ∃ x : Nat,
        (x : Int) ≤ num.val ∧
          ((x : Int) + (reverseDigits x : Int) = num.val ∧ digitCount x % 2 = 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (num : Std.I64) (h0 : 0 ≤ num.val) (hle : num.val ≤ 100000)
        (hres : Aegis.SumOfNumberAndReverse.sum_of_number_and_reverse num = ok true)
        (h11 : num.val % 11 ≠ 0), ∃ x : Nat,
          (x : Int) ≤ num.val ∧
            ((x : Int) + (reverseDigits x : Int) = num.val ∧ digitCount x % 2 = 1)) := by
    sorry

  /-- The function returns true; a valid witness is x=140, because reverse(140)=41 (the reversed digits 041 are read as 41) and 140+41=181.
    Preconditions: num = 181. -/
  theorem spec_6 (num : Std.I64) (hnum : num.val = 181) :
      Aegis.SumOfNumberAndReverse.sum_of_number_and_reverse num = ok true ∧
        (140 : Int) ≤ num.val ∧
          ((140 : Int) + (reverseDigits 140 : Int) = num.val ∧ reverseDigits 140 = 41) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (num : Std.I64) (hnum : num.val = 181), Aegis.SumOfNumberAndReverse.sum_of_number_and_reverse num = ok true ∧
          (140 : Int) ≤ num.val ∧
            ((140 : Int) + (reverseDigits 140 : Int) = num.val ∧ reverseDigits 140 = 41)) := by
    sorry

  /-- The function returns false; no non-negative integer x satisfies x+reverse(x)=100000.
    Preconditions: num = 100000. -/
  theorem spec_7 (num : Std.I64) (hnum : num.val = 100000) :
      Aegis.SumOfNumberAndReverse.sum_of_number_and_reverse num = ok false ∧
        ¬ ∃ x : Nat, (x : Int) + (reverseDigits x : Int) = num.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (num : Std.I64) (hnum : num.val = 100000), Aegis.SumOfNumberAndReverse.sum_of_number_and_reverse num = ok false ∧
          ¬ ∃ x : Nat, (x : Int) + (reverseDigits x : Int) = num.val) := by
    sorry

  end AegisSpec.SumOfNumberAndReverse
