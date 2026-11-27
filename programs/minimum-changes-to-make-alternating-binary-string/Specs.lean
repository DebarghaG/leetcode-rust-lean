import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-changes-to-make-alternating-binary-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinOperations

def byteAt (l : List U8) (i : Nat) : Option Nat := l[i]?.map (fun b => b.val)

def IsBinary (l : List U8) : Prop :=
  ∀ i : Nat, i < l.length → byteAt l i = some 48 ∨ byteAt l i = some 49

def Alternating (l : List U8) : Prop :=
  ∀ i : Nat, i + 1 < l.length → byteAt l i ≠ byteAt l (i + 1)

def mismatchCount (s t : List U8) : Nat :=
  (List.range s.length).countP (fun i => decide (byteAt s i ≠ byteAt t i))

def Valid (s : Slice U8) : Prop :=
  1 ≤ s.val.length ∧ s.val.length ≤ 10000 ∧ IsBinary s.val

def IsCandidate (s : Slice U8) (t : List U8) : Prop :=
  t.length = s.val.length ∧ IsBinary t ∧ Alternating t

def countEvenZeroOddOne (l : List U8) : Nat :=
  (List.range l.length).countP
    (fun i => decide ((i % 2 = 0 ∧ byteAt l i = some 48) ∨
      (i % 2 = 1 ∧ byteAt l i = some 49)))

def flipByte (b : U8) : U8 := if b.val = 48 then 49#u8 else 48#u8

def flip (l : List U8) : List U8 := l.map flipByte

def AllBytes (l : List U8) (v : Nat) : Prop :=
  ∀ i : Nat, i < l.length → byteAt l i = some v

/-- Whenever the function returns a result r, letting n = len(s), r equals the minimum, over all byte strings t of length n such that t[i] is either 48 ('0') or 49 ('1') for every 0 <= i < n and t[i] != t[i+1] for every 0 <= i < n-1, of the number of indices i with 0 <= i < n and s[i] != t[i].
  Preconditions: len(s) is between 1 and 10000 inclusive, and for every i with 0 <= i < len(s), s[i] is either 48 ('0') or 49 ('1'). -/
theorem spec_1 (s : Slice U8) (h : Valid s) (r : I64)
    (hr : Aegis.MinOperations.min_operations s = ok r) :
    (∃ t : List U8, IsCandidate s t ∧ (mismatchCount s.val t : Int) = r.val) ∧
    (∀ t : List U8, IsCandidate s t → r.val ≤ (mismatchCount s.val t : Int)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (h : Valid s) (r : I64)
    (hr : Aegis.MinOperations.min_operations s = ok r), (∃ t : List U8, IsCandidate s t ∧ (mismatchCount s.val t : Int) = r.val) ∧
    (∀ t : List U8, IsCandidate s t → r.val ≤ (mismatchCount s.val t : Int))) := by
  sorry

/-- For every s satisfying the preconditions, the function returns a result r; it does not fail (no overflow, out-of-bounds access, or panic occurs).
  Preconditions: len(s) is between 1 and 10000 inclusive, and for every i with 0 <= i < len(s), s[i] is either 48 ('0') or 49 ('1'). -/
theorem spec_2 (s : Slice U8) (h : Valid s) :
    ∃ r : I64, Aegis.MinOperations.min_operations s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (h : Valid s), ∃ r : I64, Aegis.MinOperations.min_operations s = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= floor(len(s)/2), where floor(len(s)/2) is integer division of the nonnegative length by 2.
  Preconditions: len(s) is between 1 and 10000 inclusive, and for every i with 0 <= i < len(s), s[i] is either 48 ('0') or 49 ('1'). -/
theorem spec_3 (s : Slice U8) (h : Valid s) (r : I64)
    (hr : Aegis.MinOperations.min_operations s = ok r) :
    0 ≤ r.val ∧ r.val ≤ ((s.val.length / 2 : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (h : Valid s) (r : I64)
    (hr : Aegis.MinOperations.min_operations s = ok r), 0 ≤ r.val ∧ r.val ≤ ((s.val.length / 2 : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if s is alternating, i.e. if and only if for every i with 0 <= i < len(s)-1, s[i] != s[i+1].
  Preconditions: len(s) is between 1 and 10000 inclusive, and for every i with 0 <= i < len(s), s[i] is either 48 ('0') or 49 ('1'). -/
theorem spec_4 (s : Slice U8) (h : Valid s) (r : I64)
    (hr : Aegis.MinOperations.min_operations s = ok r) :
    r.val = 0 ↔ Alternating s.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (h : Valid s) (r : I64)
    (hr : Aegis.MinOperations.min_operations s = ok r), r.val = 0 ↔ Alternating s.val) := by
  sorry

/-- Whenever the function returns a result r, if all bytes of s are equal (s[i] = 48 for every i, or s[i] = 49 for every i), then r = floor(len(s)/2), with integer division by 2.
  Preconditions: len(s) is between 1 and 10000 inclusive, and for every i with 0 <= i < len(s), s[i] is either 48 ('0') or 49 ('1'). -/
theorem spec_5 (s : Slice U8) (h : Valid s) (r : I64)
    (hr : Aegis.MinOperations.min_operations s = ok r)
    (hconst : AllBytes s.val 48 ∨ AllBytes s.val 49) :
    r.val = ((s.val.length / 2 : Nat) : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (h : Valid s) (r : I64)
    (hr : Aegis.MinOperations.min_operations s = ok r)
    (hconst : AllBytes s.val 48 ∨ AllBytes s.val 49), r.val = ((s.val.length / 2 : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, there exists a byte string t of length len(s) such that every t[i] is 48 ('0') or 49 ('1'), t is alternating (t[i] != t[i+1] for every 0 <= i < len(t)-1), and the number of indices i with s[i] != t[i] equals r.
  Preconditions: len(s) is between 1 and 10000 inclusive, and for every i with 0 <= i < len(s), s[i] is either 48 ('0') or 49 ('1'). -/
theorem spec_6 (s : Slice U8) (h : Valid s) (r : I64)
    (hr : Aegis.MinOperations.min_operations s = ok r) :
    ∃ t : List U8, IsCandidate s t ∧ (mismatchCount s.val t : Int) = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (h : Valid s) (r : I64)
    (hr : Aegis.MinOperations.min_operations s = ok r), ∃ t : List U8, IsCandidate s t ∧ (mismatchCount s.val t : Int) = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every byte string t of length len(s) such that every t[i] is 48 ('0') or 49 ('1') and t is alternating (t[i] != t[i+1] for every 0 <= i < len(t)-1), the number of indices i with s[i] != t[i] is at least r.
  Preconditions: len(s) is between 1 and 10000 inclusive, and for every i with 0 <= i < len(s), s[i] is either 48 ('0') or 49 ('1'). -/
theorem spec_7 (s : Slice U8) (h : Valid s) (r : I64)
    (hr : Aegis.MinOperations.min_operations s = ok r) :
    ∀ t : List U8, IsCandidate s t → r.val ≤ (mismatchCount s.val t : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (h : Valid s) (r : I64)
    (hr : Aegis.MinOperations.min_operations s = ok r), ∀ t : List U8, IsCandidate s t → r.val ≤ (mismatchCount s.val t : Int)) := by
  sorry

/-- Whenever the function returns a result r, let n = len(s) and let c be the number of indices i with 0 <= i < n for which either (i is even and s[i] = 48) or (i is odd and s[i] = 49). Then r = min(c, n - c).
  Preconditions: len(s) is between 1 and 10000 inclusive, and for every i with 0 <= i < len(s), s[i] is either 48 ('0') or 49 ('1'). -/
theorem spec_8 (s : Slice U8) (h : Valid s) (r : I64)
    (hr : Aegis.MinOperations.min_operations s = ok r) :
    r.val = (((min (countEvenZeroOddOne s.val)
      (s.val.length - countEvenZeroOddOne s.val)) : Nat) : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8) (h : Valid s) (r : I64)
    (hr : Aegis.MinOperations.min_operations s = ok r), r.val = (((min (countEvenZeroOddOne s.val)
      (s.val.length - countEvenZeroOddOne s.val)) : Nat) : Int)) := by
  sorry

/-- Whenever the call on s returns r_s and the call on t returns r_t, we have r_s = r_t.
  Preconditions: s is a valid input: len(s) is between 1 and 10000 inclusive, and every s[i] is 48 ('0') or 49 ('1'). Define t of length len(s) by t[i] = 49 if s[i] = 48, and t[i] = 48 if s[i] = 49; then t is also valid. -/
theorem spec_9 (s t : Slice U8) (h : Valid s) (ht : t.val = flip s.val)
    (r_s r_t : I64)
    (h_s : Aegis.MinOperations.min_operations s = ok r_s)
    (h_t : Aegis.MinOperations.min_operations t = ok r_t) :
    r_s = r_t := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s t : Slice U8) (h : Valid s) (ht : t.val = flip s.val)
    (r_s r_t : I64)
    (h_s : Aegis.MinOperations.min_operations s = ok r_s)
    (h_t : Aegis.MinOperations.min_operations t = ok r_t), r_s = r_t) := by
  sorry

/-- Whenever the call on s returns r_s and the call on u returns r_u, |r_s - r_u| <= D, where D is the number of indices i with 0 <= i < len(s) and s[i] != u[i].
  Preconditions: s and u are valid byte strings with the same length: len(s) = len(u), lengths are between 1 and 10000 inclusive, and every byte of s and u is 48 ('0') or 49 ('1'). -/
theorem spec_10 (s u : Slice U8) (h : Valid s) (hu : Valid u)
    (hlen : s.val.length = u.val.length) (r_s r_u : I64)
    (h_s : Aegis.MinOperations.min_operations s = ok r_s)
    (h_u : Aegis.MinOperations.min_operations u = ok r_u) :
    |r_s.val - r_u.val| ≤ (mismatchCount s.val u.val : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s u : Slice U8) (h : Valid s) (hu : Valid u)
    (hlen : s.val.length = u.val.length) (r_s r_u : I64)
    (h_s : Aegis.MinOperations.min_operations s = ok r_s)
    (h_u : Aegis.MinOperations.min_operations u = ok r_u), |r_s.val - r_u.val| ≤ (mismatchCount s.val u.val : Int)) := by
  sorry

end AegisSpec.MinOperations
