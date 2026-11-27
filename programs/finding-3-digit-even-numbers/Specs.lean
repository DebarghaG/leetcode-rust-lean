import Aegis.FindEvenNumbers.Code.Funs

/-!
# Specifications of `Aegis.FindEvenNumbers.find_even_numbers`

LeetCode problem `finding-3-digit-even-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindEvenNumbers

  def HasValueAt (l : List Std.I64) (i : Nat) (x : Int) : Prop :=
    ∃ (h : i < l.length), (l.get ⟨i, h⟩).val = x

  def OccursIn (l : List Std.I64) (x : Int) : Prop :=
    ∃ p : Nat, HasValueAt l p x

  def StrictlyIncreasingList (l : List Std.I64) : Prop :=
    ∀ p (h : p + 1 < l.length),
      (l.get ⟨p, Nat.lt_trans (Nat.lt_succ_self p) h⟩).val < (l.get ⟨p + 1, h⟩).val

  def CanForm (digits : Slice Std.I64) (x : Int) : Prop :=
    ∃ i j k : Nat,
      i < digits.val.length ∧ j < digits.val.length ∧ k < digits.val.length ∧
        i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
          HasValueAt digits.val i (x / 100) ∧
            HasValueAt digits.val j ((x / 10) % 10) ∧
              HasValueAt digits.val k (x % 10)

  /-- Whenever the function returns a result r, r is strictly increasing (for every p with 0 <= p and p + 1 < len(r), r[p] < r[p + 1]), and for every integer x, x occurs in r (there exists p with 0 <= p < len(r) and r[p] = x) if and only if 100 <= x <= 999, x mod 2 = 0, and there exist pairwise distinct indices i, j, k with 0 <= i < len(digits), 0 <= j < len(digits), 0 <= k < len(digits) such that digits[i] = x / 100, digits[j] = (x / 10) mod 10, and digits[k] = x mod 10.
    Preconditions: len(digits) >= 3 and len(digits) <= 100, and for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9. -/
  theorem spec_1 (digits : Slice Std.I64)
      (hlen_lo : 3 ≤ digits.val.length)
      (hlen_hi : digits.val.length ≤ 100)
      (hdigits : ∀ i (h : i < digits.val.length),
        0 ≤ (digits.val.get ⟨i, h⟩).val ∧ (digits.val.get ⟨i, h⟩).val ≤ 9) :
      ∀ r, Aegis.FindEvenNumbers.find_even_numbers digits = ok r →
        StrictlyIncreasingList r.val ∧
          ∀ x : Int,
            OccursIn r.val x ↔
              (100 ≤ x ∧ x ≤ 999 ∧ x % 2 = 0 ∧ CanForm digits x) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (digits : Slice Std.I64)
        (hlen_lo : 3 ≤ digits.val.length)
        (hlen_hi : digits.val.length ≤ 100)
        (hdigits : ∀ i (h : i < digits.val.length),
          0 ≤ (digits.val.get ⟨i, h⟩).val ∧ (digits.val.get ⟨i, h⟩).val ≤ 9), ∀ r, Aegis.FindEvenNumbers.find_even_numbers digits = ok r →
          StrictlyIncreasingList r.val ∧
            ∀ x : Int,
              OccursIn r.val x ↔
                (100 ≤ x ∧ x ≤ 999 ∧ x % 2 = 0 ∧ CanForm digits x)) := by
    sorry

  /-- Whenever the input satisfies the preconditions, the function returns a result r; in particular it does not fail because of arithmetic overflow, out-of-bounds indexing, or a panic.
    Preconditions: len(digits) >= 3 and len(digits) <= 100, and for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9. -/
  theorem spec_2 (digits : Slice Std.I64)
      (hlen_lo : 3 ≤ digits.val.length)
      (hlen_hi : digits.val.length ≤ 100)
      (hdigits : ∀ i (h : i < digits.val.length),
        0 ≤ (digits.val.get ⟨i, h⟩).val ∧ (digits.val.get ⟨i, h⟩).val ≤ 9) :
      ∃ r, Aegis.FindEvenNumbers.find_even_numbers digits = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (digits : Slice Std.I64)
        (hlen_lo : 3 ≤ digits.val.length)
        (hlen_hi : digits.val.length ≤ 100)
        (hdigits : ∀ i (h : i < digits.val.length),
          0 ≤ (digits.val.get ⟨i, h⟩).val ∧ (digits.val.get ⟨i, h⟩).val ≤ 9), ∃ r, Aegis.FindEvenNumbers.find_even_numbers digits = ok r) := by
    sorry

  end AegisSpec.FindEvenNumbers
