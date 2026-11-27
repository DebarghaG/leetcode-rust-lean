import Aegis.MaximumValue.Code.Funs

/-!
# Specifications of `Aegis.MaximumValue.maximum_value`

LeetCode problem `maximum-value-of-a-string-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaximumValue (maximum_value)
open Classical

namespace AegisSpec.MaximumValue

def isDigitByte (b : U8) : Prop := 48 ≤ b.val ∧ b.val ≤ 57

def isLetterOrDigitByte (b : U8) : Prop :=
  (97 ≤ b.val ∧ b.val ≤ 122) ∨ (48 ≤ b.val ∧ b.val ≤ 57)

def digits (s : List U8) : Prop := ∀ k : Fin s.length, isDigitByte (s.get k)

def num (s : List U8) : ℤ :=
  ∑ k : Fin s.length, (((s.get k).val : ℤ) - 48) * 10 ^ (s.length - 1 - (k : ℕ))

noncomputable def val (s : List U8) : ℤ :=
  if digits s then num s else (s.length : ℤ)

def entryOK (s : alloc.vec.Vec U8) : Prop :=
  1 ≤ s.val.length ∧ s.val.length ≤ 9 ∧ ∀ k : Fin s.val.length, isLetterOrDigitByte (s.val.get k)

def inputOK (strs : Slice (alloc.vec.Vec U8)) : Prop :=
  1 ≤ strs.val.length ∧ strs.val.length ≤ 100 ∧ ∀ i : Fin strs.val.length, entryOK (strs.val.get i)

/-- For a byte string s, define digits(s) to mean that for every k with 0 <= k < len(s), 48 <= s[k] <= 57. If digits(s), define num(s) = sum over k from 0 to len(s)-1 of (s[k]-48) * 10^(len(s)-1-k). Define val(s) = num(s) if digits(s), and val(s) = len(s) otherwise. The function returns a result r and r = max{ val(strs[i]) | 0 <= i < len(strs) }, the ordinary integer maximum over this nonempty finite set.
  Preconditions: 1 <= len(strs) <= 100; for every i with 0 <= i < len(strs), 1 <= len(strs[i]) <= 9 and every byte of strs[i] is either a lowercase English letter (byte value 97..122) or a digit (byte value 48..57). -/
theorem spec_1 (strs : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs) :
    ∃ r : I64,
      maximum_value strs = ok r ∧
        (∀ i : Fin strs.val.length, val (strs.val.get i).val ≤ r.val) ∧
        ∃ j : Fin strs.val.length, val (strs.val.get j).val = r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs), ∃ r : I64,
      maximum_value strs = ok r ∧
        (∀ i : Fin strs.val.length, val (strs.val.get i).val ≤ r.val) ∧
        ∃ j : Fin strs.val.length, val (strs.val.get j).val = r.val) := by
  sorry

/-- The function returns a result r (it does not fail, overflow, read out of bounds, or panic).
  Preconditions: 1 <= len(strs) <= 100; for every i with 0 <= i < len(strs), 1 <= len(strs[i]) <= 9 and every byte of strs[i] is either a lowercase English letter (byte value 97..122) or a digit (byte value 48..57). -/
theorem spec_2 (strs : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs) :
    ∃ r : I64, maximum_value strs = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs), ∃ r : I64, maximum_value strs = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: 1 <= len(strs) <= 100; for every i with 0 <= i < len(strs), 1 <= len(strs[i]) <= 9 and every byte of strs[i] is either a lowercase English letter (byte value 97..122) or a digit (byte value 48..57). -/
theorem spec_3 (strs : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs) :
    ∀ r : I64, maximum_value strs = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs), ∀ r : I64, maximum_value strs = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= 999999999.
  Preconditions: 1 <= len(strs) <= 100; for every i with 0 <= i < len(strs), 1 <= len(strs[i]) <= 9 and every byte of strs[i] is either a lowercase English letter (byte value 97..122) or a digit (byte value 48..57). -/
theorem spec_4 (strs : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs) :
    ∀ r : I64, maximum_value strs = ok r → r.val ≤ 999999999 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs), ∀ r : I64, maximum_value strs = ok r → r.val ≤ 999999999) := by
  sorry

/-- Define val(s) as in spec_1. Whenever the function returns a result r, there exists an index j with 0 <= j < len(strs) such that r = val(strs[j]).
  Preconditions: 1 <= len(strs) <= 100; for every i with 0 <= i < len(strs), 1 <= len(strs[i]) <= 9 and every byte of strs[i] is either a lowercase English letter (byte value 97..122) or a digit (byte value 48..57). -/
theorem spec_5 (strs : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs) :
    ∀ r : I64,
      maximum_value strs = ok r → ∃ j : Fin strs.val.length, r.val = val (strs.val.get j).val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs), ∀ r : I64,
      maximum_value strs = ok r → ∃ j : Fin strs.val.length, r.val = val (strs.val.get j).val) := by
  sorry

/-- Define val(s) as in spec_1. Whenever the function returns a result r, for every i with 0 <= i < len(strs), val(strs[i]) <= r.
  Preconditions: 1 <= len(strs) <= 100; for every i with 0 <= i < len(strs), 1 <= len(strs[i]) <= 9 and every byte of strs[i] is either a lowercase English letter (byte value 97..122) or a digit (byte value 48..57). -/
theorem spec_6 (strs : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs) :
    ∀ r : I64,
      maximum_value strs = ok r → ∀ i : Fin strs.val.length, val (strs.val.get i).val ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs), ∀ r : I64,
      maximum_value strs = ok r → ∀ i : Fin strs.val.length, val (strs.val.get i).val ≤ r.val) := by
  sorry

/-- Define digits(s) and num(s) as in spec_1. Whenever the function returns a result r and r > 9, there exists an index j with 0 <= j < len(strs) such that digits(strs[j]) and num(strs[j]) = r.
  Preconditions: 1 <= len(strs) <= 100; for every i with 0 <= i < len(strs), 1 <= len(strs[i]) <= 9 and every byte of strs[i] is either a lowercase English letter (byte value 97..122) or a digit (byte value 48..57). -/
theorem spec_7 (strs : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs) :
    ∀ r : I64,
      maximum_value strs = ok r →
        9 < r.val →
          ∃ j : Fin strs.val.length,
            digits (strs.val.get j).val ∧ num (strs.val.get j).val = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs), ∀ r : I64,
      maximum_value strs = ok r →
        9 < r.val →
          ∃ j : Fin strs.val.length,
            digits (strs.val.get j).val ∧ num (strs.val.get j).val = r.val) := by
  sorry

/-- Whenever the function returns a result r and r > 9, for every i with 0 <= i < len(strs), len(strs[i]) < r.
  Preconditions: 1 <= len(strs) <= 100; for every i with 0 <= i < len(strs), 1 <= len(strs[i]) <= 9 and every byte of strs[i] is either a lowercase English letter (byte value 97..122) or a digit (byte value 48..57). -/
theorem spec_8 (strs : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs) :
    ∀ r : I64,
      maximum_value strs = ok r →
        9 < r.val → ∀ i : Fin strs.val.length, ((strs.val.get i).val.length : ℤ) < r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs), ∀ r : I64,
      maximum_value strs = ok r →
        9 < r.val → ∀ i : Fin strs.val.length, ((strs.val.get i).val.length : ℤ) < r.val) := by
  sorry

/-- If maximum_value(strs) returns r and maximum_value(strs_prime) returns r_prime, then r = r_prime.
  Preconditions: strs and strs_prime both satisfy the base constraints: their lengths are between 1 and 100, every inner string has length between 1 and 9, and every byte is a lowercase English letter (97..122) or a digit (48..57). Also strs_prime is a permutation of strs. -/
theorem spec_9 (strs strs' : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs)
    (hstrs' : inputOK strs') (hperm : strs'.val.Perm strs.val) :
    ∀ r r' : I64,
      maximum_value strs = ok r → maximum_value strs' = ok r' → r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (strs strs' : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs)
    (hstrs' : inputOK strs') (hperm : strs'.val.Perm strs.val), ∀ r r' : I64,
      maximum_value strs = ok r → maximum_value strs' = ok r' → r = r') := by
  sorry

/-- Define num(s) as in spec_1. If num(s) = num(t), maximum_value(strs) returns r, and maximum_value(strs_prime) returns r_prime, then r = r_prime.
  Preconditions: 1 <= len(strs) <= 100; for every i with 0 <= i < len(strs), 1 <= len(strs[i]) <= 9 and every byte of strs[i] is either a lowercase English letter (byte value 97..122) or a digit (byte value 48..57); j is an index with 0 <= j < len(strs); s = strs[j] is digits-only; t is a byte string satisfying 1 <= len(t) <= 9, consists only of digits (48..57), and has the same numeric value as s; strs_prime is obtained from strs by replacing entry j with t. -/
theorem spec_10 (strs strs' : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs)
    (j : ℕ) (hj : j < strs.val.length) (s t : alloc.vec.Vec U8)
    (hs : strs.val.get ⟨j, hj⟩ = s) (hdigits : digits s.val)
    (htlen : 1 ≤ t.val.length) (htlen9 : t.val.length ≤ 9) (hdigits' : digits t.val)
    (hnum : num s.val = num t.val) (hreplace : strs'.val = strs.val.set j t) :
    ∀ r r' : I64,
      maximum_value strs = ok r → maximum_value strs' = ok r' → r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (strs strs' : Slice (alloc.vec.Vec U8)) (hstrs : inputOK strs)
    (j : ℕ) (hj : j < strs.val.length) (s t : alloc.vec.Vec U8)
    (hs : strs.val.get ⟨j, hj⟩ = s) (hdigits : digits s.val)
    (htlen : 1 ≤ t.val.length) (htlen9 : t.val.length ≤ 9) (hdigits' : digits t.val)
    (hnum : num s.val = num t.val) (hreplace : strs'.val = strs.val.set j t), ∀ r r' : I64,
      maximum_value strs = ok r → maximum_value strs' = ok r' → r = r') := by
  sorry

end AegisSpec.MaximumValue
