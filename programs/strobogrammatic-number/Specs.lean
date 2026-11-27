import Aegis.IsStrobogrammatic.Code.Funs

/-!
# Specifications of `Aegis.IsStrobogrammatic.is_strobogrammatic`

LeetCode problem `strobogrammatic-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsStrobogrammatic

def IsDigitCode (b : U8) : Prop :=
  b.val = 48 ∨ b.val = 49 ∨ b.val = 50 ∨ b.val = 51 ∨ b.val = 52 ∨
    b.val = 53 ∨ b.val = 54 ∨ b.val = 55 ∨ b.val = 56 ∨ b.val = 57

def IsDecimalString (num : Slice U8) : Prop :=
  1 ≤ num.val.length ∧ num.val.length ≤ 50 ∧
    (∀ i (hi : i < num.val.length), IsDigitCode (num.val[i])) ∧
    ((hlen : 1 < num.val.length) → (num.val[0]'(by omega)).val ≠ 48)

def IsStrobPair (a b : U8) : Prop :=
  (a.val, b.val) ∈ [(48, 48), (49, 49), (54, 57), (56, 56), (57, 54)]

def IsUprightDigit (b : U8) : Prop :=
  b.val = 48 ∨ b.val = 49 ∨ b.val = 56

def IsNonStrobDigit (b : U8) : Prop :=
  b.val = 50 ∨ b.val = 51 ∨ b.val = 52 ∨ b.val = 53 ∨ b.val = 55

def IsTiltedDigit (b : U8) : Prop :=
  b.val = 54 ∨ b.val = 57

/-- The function returns a result r and r = true if and only if for every i with 0 <= i < len(num), the ordered pair (num[i], num[len(num)-1-i]) is one of (48,48), (49,49), (54,57), (56,56), (57,54).
  Preconditions: num is a byte slice representing a decimal string; 1 <= len(num) <= 50; for every i with 0 <= i < len(num), num[i] is one of the ASCII codes 48 ('0'), 49 ('1'), 50 ('2'), 51 ('3'), 52 ('4'), 53 ('5'), 54 ('6'), 55 ('7'), 56 ('8'), 57 ('9'); and if len(num) > 1 then num[0] != 48. -/
theorem spec_1 (num : Slice U8) (hinput : IsDecimalString num) :
    ∃ r, Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r ∧
      (r = true ↔ ∀ i (hi : i < num.val.length),
        IsStrobPair (num.val[i]) (num.val[num.val.length - 1 - i]'(by omega))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (num : Slice U8) (hinput : IsDecimalString num), ∃ r, Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r ∧
      (r = true ↔ ∀ i (hi : i < num.val.length),
        IsStrobPair (num.val[i]) (num.val[num.val.length - 1 - i]'(by omega)))) := by
  sorry

/-- For every input satisfying the preconditions, the function returns an ok result r; it does not fail due to overflow, out-of-bounds access, or panic.
  Preconditions: num is a byte slice representing a decimal string; 1 <= len(num) <= 50; for every i with 0 <= i < len(num), num[i] is one of the ASCII codes 48 ('0'), 49 ('1'), 50 ('2'), 51 ('3'), 52 ('4'), 53 ('5'), 54 ('6'), 55 ('7'), 56 ('8'), 57 ('9'); and if len(num) > 1 then num[0] != 48. -/
theorem spec_2 (num : Slice U8) (hinput : IsDecimalString num) :
    ∃ r, Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (num : Slice U8) (hinput : IsDecimalString num), ∃ r, Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r) := by
  sorry

/-- For every i with 0 <= i < len(num), if num[i] is one of 50 ('2'), 51 ('3'), 52 ('4'), 53 ('5'), 55 ('7'), then whenever the function returns a result r, r = false.
  Preconditions: num is a byte slice representing a decimal string; 1 <= len(num) <= 50; for every i with 0 <= i < len(num), num[i] is one of the ASCII codes 48 ('0'), 49 ('1'), 50 ('2'), 51 ('3'), 52 ('4'), 53 ('5'), 54 ('6'), 55 ('7'), 56 ('8'), 57 ('9'); and if len(num) > 1 then num[0] != 48. -/
theorem spec_3 (num : Slice U8) (hinput : IsDecimalString num)
    (i : Nat) (hi : i < num.val.length) (hbad : IsNonStrobDigit (num.val[i]))
    (r : Bool) (hr : Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r) :
    r = false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (num : Slice U8) (hinput : IsDecimalString num)
    (i : Nat) (hi : i < num.val.length) (hbad : IsNonStrobDigit (num.val[i]))
    (r : Bool) (hr : Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r), r = false) := by
  sorry

/-- Whenever the function returns a result r with r = true and len(num) > 1, num[0] != 48 ('0') and num[len(num)-1] != 48 ('0').
  Preconditions: num is a byte slice representing a decimal string; 1 <= len(num) <= 50; for every i with 0 <= i < len(num), num[i] is one of the ASCII codes 48 ('0'), 49 ('1'), 50 ('2'), 51 ('3'), 52 ('4'), 53 ('5'), 54 ('6'), 55 ('7'), 56 ('8'), 57 ('9'); and if len(num) > 1 then num[0] != 48. -/
theorem spec_4 (num : Slice U8) (hinput : IsDecimalString num)
    (r : Bool) (hr : Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r)
    (hr_true : r = true) (hlen : 1 < num.val.length) :
    (num.val[0]'(by omega)).val ≠ 48 ∧
      (num.val[num.val.length - 1]'(by omega)).val ≠ 48 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (num : Slice U8) (hinput : IsDecimalString num)
    (r : Bool) (hr : Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r)
    (hr_true : r = true) (hlen : 1 < num.val.length), (num.val[0]'(by omega)).val ≠ 48 ∧
      (num.val[num.val.length - 1]'(by omega)).val ≠ 48) := by
  sorry

/-- Whenever the function returns a result r with r = true and len(num) is odd, num[(len(num)-1)/2] is 48 ('0'), 49 ('1'), or 56 ('8').
  Preconditions: num is a byte slice representing a decimal string; 1 <= len(num) <= 50; for every i with 0 <= i < len(num), num[i] is one of the ASCII codes 48 ('0'), 49 ('1'), 50 ('2'), 51 ('3'), 52 ('4'), 53 ('5'), 54 ('6'), 55 ('7'), 56 ('8'), 57 ('9'); and if len(num) > 1 then num[0] != 48. -/
theorem spec_5 (num : Slice U8) (hinput : IsDecimalString num)
    (r : Bool) (hr : Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r)
    (hr_true : r = true) (hodd : num.val.length % 2 = 1) :
    IsUprightDigit (num.val[(num.val.length - 1) / 2]'(by omega)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (num : Slice U8) (hinput : IsDecimalString num)
    (r : Bool) (hr : Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r)
    (hr_true : r = true) (hodd : num.val.length % 2 = 1), IsUprightDigit (num.val[(num.val.length - 1) / 2]'(by omega))) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if for every i with 0 <= i < len(num), num[i] = num[len(num)-1-i].
  Preconditions: num is a byte slice representing a decimal string; 1 <= len(num) <= 50; for every i with 0 <= i < len(num), num[i] is one of the ASCII codes 48 ('0'), 49 ('1'), 50 ('2'), 51 ('3'), 52 ('4'), 53 ('5'), 54 ('6'), 55 ('7'), 56 ('8'), 57 ('9'); if len(num) > 1 then num[0] != 48; and for every i with 0 <= i < len(num), num[i] is 48 ('0'), 49 ('1'), or 56 ('8'). -/
theorem spec_6 (num : Slice U8) (hinput : IsDecimalString num)
    (hupright : ∀ i (hi : i < num.val.length), IsUprightDigit (num.val[i]))
    (r : Bool) (hr : Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r) :
    (r = true ↔ ∀ i (hi : i < num.val.length),
      (num.val[i]).val = (num.val[num.val.length - 1 - i]'(by omega)).val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (num : Slice U8) (hinput : IsDecimalString num)
    (hupright : ∀ i (hi : i < num.val.length), IsUprightDigit (num.val[i]))
    (r : Bool) (hr : Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r), (r = true ↔ ∀ i (hi : i < num.val.length),
      (num.val[i]).val = (num.val[num.val.length - 1 - i]'(by omega)).val)) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if len(num) is even and for every i with 0 <= i < len(num), num[i] != num[len(num)-1-i].
  Preconditions: num is a byte slice representing a decimal string; 1 <= len(num) <= 50; for every i with 0 <= i < len(num), num[i] is one of the ASCII codes 48 ('0'), 49 ('1'), 50 ('2'), 51 ('3'), 52 ('4'), 53 ('5'), 54 ('6'), 55 ('7'), 56 ('8'), 57 ('9'); if len(num) > 1 then num[0] != 48; and for every i with 0 <= i < len(num), num[i] is 54 ('6') or 57 ('9'). -/
theorem spec_7 (num : Slice U8) (hinput : IsDecimalString num)
    (htilted : ∀ i (hi : i < num.val.length), IsTiltedDigit (num.val[i]))
    (r : Bool) (hr : Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r) :
    (r = true ↔ num.val.length % 2 = 0 ∧ ∀ i (hi : i < num.val.length),
      (num.val[i]).val ≠ (num.val[num.val.length - 1 - i]'(by omega)).val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (num : Slice U8) (hinput : IsDecimalString num)
    (htilted : ∀ i (hi : i < num.val.length), IsTiltedDigit (num.val[i]))
    (r : Bool) (hr : Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r), (r = true ↔ num.val.length % 2 = 0 ∧ ∀ i (hi : i < num.val.length),
      (num.val[i]).val ≠ (num.val[num.val.length - 1 - i]'(by omega)).val)) := by
  sorry

/-- Whenever the function returns a result r on num and a result r_rev on rev, r = r_rev.
  Preconditions: num is a byte slice representing a decimal string with 1 <= len(num) <= 50, every byte num[i] is an ASCII digit code 48 through 57, and if len(num) > 1 then num[0] != 48. Let rev be the byte slice of length len(num) defined by rev[i] = num[len(num)-1-i] for every i with 0 <= i < len(num). Assume also that rev satisfies the same input constraints: 1 <= len(rev) <= 50, every byte rev[i] is an ASCII digit code 48 through 57, and if len(rev) > 1 then rev[0] != 48. -/
theorem spec_8 (num rev : Slice U8) (hinput : IsDecimalString num)
    (hrev_def : rev.val = num.val.reverse) (hrev_input : IsDecimalString rev)
    (r r_rev : Bool) (hr : Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r)
    (hr_rev : Aegis.IsStrobogrammatic.is_strobogrammatic rev = ok r_rev) :
    r = r_rev := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (num rev : Slice U8) (hinput : IsDecimalString num)
    (hrev_def : rev.val = num.val.reverse) (hrev_input : IsDecimalString rev)
    (r r_rev : Bool) (hr : Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r)
    (hr_rev : Aegis.IsStrobogrammatic.is_strobogrammatic rev = ok r_rev), r = r_rev) := by
  sorry

/-- Whenever the function returns a result r with r = true, for every i with 0 <= i < len(num): if num[i] = 54 ('6') then num[len(num)-1-i] = 57 ('9'), and if num[i] = 57 ('9') then num[len(num)-1-i] = 54 ('6').
  Preconditions: num is a byte slice representing a decimal string; 1 <= len(num) <= 50; for every i with 0 <= i < len(num), num[i] is one of the ASCII codes 48 ('0'), 49 ('1'), 50 ('2'), 51 ('3'), 52 ('4'), 53 ('5'), 54 ('6'), 55 ('7'), 56 ('8'), 57 ('9'); and if len(num) > 1 then num[0] != 48. -/
theorem spec_9 (num : Slice U8) (hinput : IsDecimalString num)
    (r : Bool) (hr : Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r)
    (hr_true : r = true) :
    (∀ i (hi : i < num.val.length),
        (num.val[i]).val = 54 → (num.val[num.val.length - 1 - i]'(by omega)).val = 57) ∧
      (∀ i (hi : i < num.val.length),
        (num.val[i]).val = 57 → (num.val[num.val.length - 1 - i]'(by omega)).val = 54) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (num : Slice U8) (hinput : IsDecimalString num)
    (r : Bool) (hr : Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r)
    (hr_true : r = true), (∀ i (hi : i < num.val.length),
        (num.val[i]).val = 54 → (num.val[num.val.length - 1 - i]'(by omega)).val = 57) ∧
      (∀ i (hi : i < num.val.length),
        (num.val[i]).val = 57 → (num.val[num.val.length - 1 - i]'(by omega)).val = 54)) := by
  sorry

/-- For every i with 1 <= i < len(num)/2 (integer division), define num' to be the byte slice of length len(num) that equals num except that num'[i] = num[len(num)-1-i] and num'[len(num)-1-i] = num[i]. Then num' satisfies the input constraints, and whenever the function returns a result r on num and a result r' on num', r = r'.
  Preconditions: num is a byte slice representing a decimal string; 1 <= len(num) <= 50; for every i with 0 <= i < len(num), num[i] is one of the ASCII codes 48 ('0'), 49 ('1'), 50 ('2'), 51 ('3'), 52 ('4'), 53 ('5'), 54 ('6'), 55 ('7'), 56 ('8'), 57 ('9'); and if len(num) > 1 then num[0] != 48. -/
theorem spec_10 (num num' : Slice U8) (hinput : IsDecimalString num)
    (i : Nat) (hi1 : 1 ≤ i) (hi2 : i < num.val.length / 2)
    (hlen' : num'.val.length = num.val.length)
    (hnum' : ∀ j (hj : j < num.val.length),
      (num'.val[j]'(by omega)).val =
        (if j = i then (num.val[num.val.length - 1 - i]'(by omega)).val
          else if j = num.val.length - 1 - i then (num.val[i]'(by omega)).val
          else (num.val[j]'(by omega)).val))
    (r r' : Bool) (hr : Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r)
    (hr' : Aegis.IsStrobogrammatic.is_strobogrammatic num' = ok r') :
    IsDecimalString num' ∧ r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (num num' : Slice U8) (hinput : IsDecimalString num)
    (i : Nat) (hi1 : 1 ≤ i) (hi2 : i < num.val.length / 2)
    (hlen' : num'.val.length = num.val.length)
    (hnum' : ∀ j (hj : j < num.val.length),
      (num'.val[j]'(by omega)).val =
        (if j = i then (num.val[num.val.length - 1 - i]'(by omega)).val
          else if j = num.val.length - 1 - i then (num.val[i]'(by omega)).val
          else (num.val[j]'(by omega)).val))
    (r r' : Bool) (hr : Aegis.IsStrobogrammatic.is_strobogrammatic num = ok r)
    (hr' : Aegis.IsStrobogrammatic.is_strobogrammatic num' = ok r'), IsDecimalString num' ∧ r = r') := by
  sorry

end AegisSpec.IsStrobogrammatic
