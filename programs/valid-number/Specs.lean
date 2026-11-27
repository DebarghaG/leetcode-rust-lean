import Aegis.IsNumber.Code.Funs

/-!
# Specifications of `Aegis.IsNumber.is_number`

LeetCode problem `valid-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsNumber

def contents (s : Slice U8) : List U8 := s.list.toList

def byteAt (l : List U8) (i : Nat) : Option Nat := (l[i]?).map (fun b => b.val)

def isDigitByte (c : Nat) : Prop := 48 ≤ c ∧ c ≤ 57

def isLetterByte (c : Nat) : Prop := (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122)

def isAllowedByte (c : Nat) : Prop :=
  isLetterByte c ∨ isDigitByte c ∨ c = 43 ∨ c = 45 ∨ c = 46

def AllAllowed (l : List U8) : Prop := ∀ i c, byteAt l i = some c → isAllowedByte c

def countExpMarkers (l : List U8) : Nat :=
  l.countP (fun b => b.val = 101 || b.val = 69)

def countDots (l : List U8) : Nat := l.countP (fun b => b.val = 46)

def NonEmptyDigits (l : List U8) : Prop :=
  1 ≤ l.length ∧ ∀ i c, byteAt l i = some c → isDigitByte c

def ValidInt (l : List U8) : Prop :=
  NonEmptyDigits l ∨
    (2 ≤ l.length ∧ (byteAt l 0 = some 43 ∨ byteAt l 0 = some 45) ∧
      NonEmptyDigits (l.drop 1))

def decOffset (l : List U8) : Nat :=
  if byteAt l 0 = some 43 ∨ byteAt l 0 = some 45 then 1 else 0

def ValidDecimal (l : List U8) : Prop :=
  ∃ k, decOffset l ≤ k ∧ k < l.length ∧ byteAt l k = some 46 ∧
    (∀ i c, decOffset l ≤ i → i < k → byteAt l i = some c → isDigitByte c) ∧
    (∀ i c, k < i → i < l.length → byteAt l i = some c → isDigitByte c) ∧
    (decOffset l < k ∨ k + 1 < l.length)

def ValidNumber (l : List U8) : Prop :=
  ∃ m, m ≤ l.length ∧
    (ValidInt (l.take m) ∨ ValidDecimal (l.take m)) ∧
    (m = l.length ∨
      (m < l.length ∧ (byteAt l m = some 101 ∨ byteAt l m = some 69) ∧
        ValidInt (l.drop (m + 1))))

/-- Whenever the function returns a result r, r = true if and only if s is a valid number, where a byte string u is a valid number exactly when there exists an index m with 0 ≤ m ≤ len(u) such that (a) the prefix u[0..m] (the bytes u[0], ..., u[m-1]) is a valid integer or a valid decimal, and (b) either m = len(u), or (m < len(u) and u[m] is 'e' (101) or 'E' (69) and the suffix u[m+1..len(u)] is a valid integer. Here, for a byte string v: a byte is a digit iff its code is between 48 and 57 inclusive; v is a nonempty digit string iff len(v) ≥ 1 and every byte of v is a digit; v is a valid integer iff either v is a nonempty digit string, or (len(v) ≥ 2 and v[0] is '+' (43) or '-' (45) and v[1..len(v)] is a nonempty digit string); v is a valid decimal iff, letting a = 1 when len(v) ≥ 1 and v[0] is '+' or '-' and a = 0 otherwise, there is an index k with a ≤ k < len(v) such that v[k] is '.' (46), every byte of v[a..k] is a digit, every byte of v[k+1..len(v)] is a digit, and at least one of the segments v[a..k] and v[k+1..len(v)] is nonempty (a segment of zero bytes vacuously satisfies 'every byte is a digit').
  Preconditions: 1 ≤ len(s) ≤ 20; every byte s[i] with 0 ≤ i < len(s) is an English letter 'A'-'Z' (65-90) or 'a'-'z' (97-122), a digit '0'-'9' (48-57), '+' (43), '-' (45), or '.' (46). -/
theorem spec_1 (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) :
    (r = true ↔ ValidNumber (contents s)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r), (r = true ↔ ValidNumber (contents s))) := by
  sorry

/-- The function returns a result r (i.e. it does not fail: no panic, no out-of-bounds indexing, no arithmetic overflow); nothing further is claimed about r.
  Preconditions: 1 ≤ len(s) ≤ 20; every byte of s is an English letter, a digit, '+', '-', or '.'. -/
theorem spec_2 (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s)) :
    ∃ r, Aegis.IsNumber.is_number s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s)), ∃ r, Aegis.IsNumber.is_number s = ok r) := by
  sorry

/-- Whenever the function returns a result r, if r = true then there exists an index i with 0 ≤ i < len(s) such that s[i] is a digit (48 ≤ s[i] ≤ 57).
  Preconditions: 1 ≤ len(s) ≤ 20; every byte of s is an English letter, a digit, '+', '-', or '.'. -/
theorem spec_3 (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) (htrue : r = true) :
    ∃ i c, i < s.length ∧ byteAt (contents s) i = some c ∧ isDigitByte c := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) (htrue : r = true), ∃ i c, i < s.length ∧ byteAt (contents s) i = some c ∧ isDigitByte c) := by
  sorry

/-- Whenever the function returns a result r, if r = true then the number of indices i with 0 ≤ i < len(s) and s[i] in {'e' (101), 'E' (69)} is at most 1.
  Preconditions: 1 ≤ len(s) ≤ 20; every byte of s is an English letter, a digit, '+', '-', or '.'. -/
theorem spec_4 (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) (htrue : r = true) :
    countExpMarkers (contents s) ≤ 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) (htrue : r = true), countExpMarkers (contents s) ≤ 1) := by
  sorry

/-- Whenever the function returns a result r, if r = true then the number of indices i with 0 ≤ i < len(s) and s[i] = '.' (46) is at most 1.
  Preconditions: 1 ≤ len(s) ≤ 20; every byte of s is an English letter, a digit, '+', '-', or '.'. -/
theorem spec_5 (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) (htrue : r = true) :
    countDots (contents s) ≤ 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) (htrue : r = true), countDots (contents s) ≤ 1) := by
  sorry

/-- Whenever the function returns a result r, if r = true then for every i with 0 ≤ i < len(s), s[i] is a digit (48-57) or s[i] is one of '+' (43), '-' (45), '.' (46), 'E' (69), 'e' (101); in other words, no letter other than 'e' or 'E' occurs in s.
  Preconditions: 1 ≤ len(s) ≤ 20; every byte of s is an English letter, a digit, '+', '-', or '.'. -/
theorem spec_6 (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) (htrue : r = true) :
    ∀ i c, byteAt (contents s) i = some c →
      isDigitByte c ∨ c = 43 ∨ c = 45 ∨ c = 46 ∨ c = 69 ∨ c = 101 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) (htrue : r = true), ∀ i c, byteAt (contents s) i = some c →
      isDigitByte c ∨ c = 43 ∨ c = 45 ∨ c = 46 ∨ c = 69 ∨ c = 101) := by
  sorry

/-- Whenever the function returns a result r, if r = true then for every i with 0 ≤ i < len(s), if s[i] is '+' (43) or '-' (45) then i = 0 or s[i-1] is 'e' (101) or 'E' (69).
  Preconditions: 1 ≤ len(s) ≤ 20; every byte of s is an English letter, a digit, '+', '-', or '.'. -/
theorem spec_7 (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) (htrue : r = true) :
    ∀ i c, i < s.length → byteAt (contents s) i = some c → (c = 43 ∨ c = 45) →
      i = 0 ∨ byteAt (contents s) (i - 1) = some 101 ∨
        byteAt (contents s) (i - 1) = some 69 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) (htrue : r = true), ∀ i c, i < s.length → byteAt (contents s) i = some c → (c = 43 ∨ c = 45) →
      i = 0 ∨ byteAt (contents s) (i - 1) = some 101 ∨
        byteAt (contents s) (i - 1) = some 69) := by
  sorry

/-- Whenever the function returns a result r, if r = true then for every i with 0 ≤ i < len(s) and s[i] in {'e' (101), 'E' (69)}, one has 0 < i and i < len(s) - 1.
  Preconditions: 1 ≤ len(s) ≤ 20; every byte of s is an English letter, a digit, '+', '-', or '.'. -/
theorem spec_8 (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) (htrue : r = true) :
    ∀ i, i < s.length →
      (byteAt (contents s) i = some 101 ∨ byteAt (contents s) i = some 69) →
      0 < i ∧ i < s.length - 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) (htrue : r = true), ∀ i, i < s.length →
      (byteAt (contents s) i = some 101 ∨ byteAt (contents s) i = some 69) →
      0 < i ∧ i < s.length - 1) := by
  sorry

/-- Whenever the function returns a result r, if r = true then s[0] is a digit (48-57), '+' (43), '-' (45), or '.' (46), and s[len(s)-1] is a digit (48-57) or '.' (46).
  Preconditions: 1 ≤ len(s) ≤ 20; every byte of s is an English letter, a digit, '+', '-', or '.'. -/
theorem spec_9 (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) (htrue : r = true) :
    (∃ c, byteAt (contents s) 0 = some c ∧
      (isDigitByte c ∨ c = 43 ∨ c = 45 ∨ c = 46)) ∧
    (∃ c, byteAt (contents s) (s.length - 1) = some c ∧ (isDigitByte c ∨ c = 46)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) (htrue : r = true), (∃ c, byteAt (contents s) 0 = some c ∧
      (isDigitByte c ∨ c = 43 ∨ c = 45 ∨ c = 46)) ∧
    (∃ c, byteAt (contents s) (s.length - 1) = some c ∧ (isDigitByte c ∨ c = 46))) := by
  sorry

/-- Whenever the function returns a result r, if s contains no digit at all (for every i with 0 ≤ i < len(s), s[i] < 48 or s[i] > 57) then r = false.
  Preconditions: 1 ≤ len(s) ≤ 20; every byte of s is an English letter, a digit, '+', '-', or '.'. -/
theorem spec_10 (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (nodigit : ∀ i c, byteAt (contents s) i = some c → c < 48 ∨ 57 < c)
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) :
    r = false := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (nodigit : ∀ i c, byteAt (contents s) i = some c → c < 48 ∨ 57 < c)
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r), r = false) := by
  sorry

/-- Whenever the function returns a result r on s, and returns a result r' on the byte string u = s[1..len(s)] (so len(u) = len(s) - 1 and u[j] = s[j+1] for 0 ≤ j < len(s)-1), then r = true if and only if (r' = true and len(u) ≥ 1 and u[0] is neither '+' (43) nor '-' (45)).
  Preconditions: 1 ≤ len(s) ≤ 20; every byte of s is an English letter, a digit, '+', '-', or '.'; 2 ≤ len(s) and s[0] is '+' (43) or '-' (45). -/
theorem spec_11 (s u : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (hlen_two : 2 ≤ s.length)
    (hsign : byteAt (contents s) 0 = some 43 ∨ byteAt (contents s) 0 = some 45)
    (hu : contents u = (contents s).drop 1)
    (r r' : Bool) (hret : Aegis.IsNumber.is_number s = ok r)
    (hret' : Aegis.IsNumber.is_number u = ok r') :
    (r = true ↔
      (r' = true ∧ 1 ≤ (contents u).length ∧
        byteAt (contents u) 0 ≠ some 43 ∧ byteAt (contents u) 0 ≠ some 45)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s u : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (hlen_two : 2 ≤ s.length)
    (hsign : byteAt (contents s) 0 = some 43 ∨ byteAt (contents s) 0 = some 45)
    (hu : contents u = (contents s).drop 1)
    (r r' : Bool) (hret : Aegis.IsNumber.is_number s = ok r)
    (hret' : Aegis.IsNumber.is_number u = ok r'), (r = true ↔
      (r' = true ∧ 1 ≤ (contents u).length ∧
        byteAt (contents u) 0 ≠ some 43 ∧ byteAt (contents u) 0 ≠ some 45))) := by
  sorry

/-- Suppose that for every i with 0 ≤ i < len(s), either both s[i] and t[i] are digits (48-57), or s[i] = t[i] and s[i] is not a digit. Then whenever the function returns a result r on s and a result r' on t, r = r'.
  Preconditions: 1 ≤ len(s) ≤ 20; every byte of s is an English letter, a digit, '+', '-', or '.'; t is a byte string with len(t) = len(s). -/
theorem spec_12 (s t : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (hlen_t : t.length = s.length)
    (hsim : ∀ i c c', byteAt (contents s) i = some c → byteAt (contents t) i = some c' →
      (isDigitByte c ∧ isDigitByte c') ∨ (c' = c ∧ ¬ isDigitByte c))
    (r r' : Bool) (hret : Aegis.IsNumber.is_number s = ok r)
    (hret' : Aegis.IsNumber.is_number t = ok r') :
    r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s t : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (hlen_t : t.length = s.length)
    (hsim : ∀ i c c', byteAt (contents s) i = some c → byteAt (contents t) i = some c' →
      (isDigitByte c ∧ isDigitByte c') ∨ (c' = c ∧ ¬ isDigitByte c))
    (r r' : Bool) (hret : Aegis.IsNumber.is_number s = ok r)
    (hret' : Aegis.IsNumber.is_number t = ok r'), r = r') := by
  sorry

/-- Suppose that for every i with 0 ≤ i < len(s), either t[i] = s[i], or (s[i] is '+' (43) or '-' (45)) and (t[i] is '+' (43) or '-' (45)). Then whenever the function returns a result r on s and a result r' on t, r = r'.
  Preconditions: 1 ≤ len(s) ≤ 20; every byte of s is an English letter, a digit, '+', '-', or '.'; t is a byte string with len(t) = len(s). -/
theorem spec_13 (s t : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (hlen_t : t.length = s.length)
    (hsim : ∀ i c c', byteAt (contents s) i = some c → byteAt (contents t) i = some c' →
      c' = c ∨ ((c = 43 ∨ c = 45) ∧ (c' = 43 ∨ c' = 45)))
    (r r' : Bool) (hret : Aegis.IsNumber.is_number s = ok r)
    (hret' : Aegis.IsNumber.is_number t = ok r') :
    r = r' := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s t : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (hlen_t : t.length = s.length)
    (hsim : ∀ i c c', byteAt (contents s) i = some c → byteAt (contents t) i = some c' →
      c' = c ∨ ((c = 43 ∨ c = 45) ∧ (c' = 43 ∨ c' = 45)))
    (r r' : Bool) (hret : Aegis.IsNumber.is_number s = ok r)
    (hret' : Aegis.IsNumber.is_number t = ok r'), r = r') := by
  sorry

/-- Whenever the function returns a result r, if r = true then for every k and p with 0 ≤ k < len(s), 0 ≤ p < len(s), s[k] = '.' (46) and s[p] in {'e' (101), 'E' (69)}, one has k < p.
  Preconditions: 1 ≤ len(s) ≤ 20; every byte of s is an English letter, a digit, '+', '-', or '.'. -/
theorem spec_14 (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) (htrue : r = true) :
    ∀ k p, k < s.length → p < s.length → byteAt (contents s) k = some 46 →
      (byteAt (contents s) p = some 101 ∨ byteAt (contents s) p = some 69) → k < p := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) (htrue : r = true), ∀ k p, k < s.length → p < s.length → byteAt (contents s) k = some 46 →
      (byteAt (contents s) p = some 101 ∨ byteAt (contents s) p = some 69) → k < p) := by
  sorry

/-- Whenever the function returns a result r, if r = true and s[len(s)-1] = '.' (46) then len(s) ≥ 2, s[len(s)-2] is a digit (48-57), and no byte of s equals 'e' (101) or 'E' (69).
  Preconditions: 1 ≤ len(s) ≤ 20; every byte of s is an English letter, a digit, '+', '-', or '.'. -/
theorem spec_15 (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) (htrue : r = true)
    (hlast : byteAt (contents s) (s.length - 1) = some 46) :
    2 ≤ s.length ∧
      (∃ c, byteAt (contents s) (s.length - 2) = some c ∧ isDigitByte c) ∧
      (∀ i c, byteAt (contents s) i = some c → c ≠ 101 ∧ c ≠ 69) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (r : Bool) (hret : Aegis.IsNumber.is_number s = ok r) (htrue : r = true)
    (hlast : byteAt (contents s) (s.length - 1) = some 46), 2 ≤ s.length ∧
      (∃ c, byteAt (contents s) (s.length - 2) = some c ∧ isDigitByte c) ∧
      (∀ i c, byteAt (contents s) i = some c → c ≠ 101 ∧ c ≠ 69)) := by
  sorry

/-- Suppose that for every i with 0 ≤ i < len(s), either t[i] = s[i], or (s[i] is 'e' (101) or 'E' (69)) and (t[i] is 'e' (101) or 'E' (69)). Then whenever the function returns a result r on s and a result r' on t, r = r'.
  Preconditions: 1 ≤ len(s) ≤ 20; every byte of s is an English letter, a digit, '+', '-', or '.'; t is a byte string with len(t) = len(s). -/
theorem spec_16 (s t : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (hlen_t : t.length = s.length)
    (hsim : ∀ i c c', byteAt (contents s) i = some c → byteAt (contents t) i = some c' →
      c' = c ∨ ((c = 101 ∨ c = 69) ∧ (c' = 101 ∨ c' = 69)))
    (r r' : Bool) (hret : Aegis.IsNumber.is_number s = ok r)
    (hret' : Aegis.IsNumber.is_number t = ok r') :
    r = r' := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (s t : Slice U8)
    (hlen_low : 1 ≤ s.length) (hlen_high : s.length ≤ 20)
    (hbytes : AllAllowed (contents s))
    (hlen_t : t.length = s.length)
    (hsim : ∀ i c c', byteAt (contents s) i = some c → byteAt (contents t) i = some c' →
      c' = c ∨ ((c = 101 ∨ c = 69) ∧ (c' = 101 ∨ c' = 69)))
    (r r' : Bool) (hret : Aegis.IsNumber.is_number s = ok r)
    (hret' : Aegis.IsNumber.is_number t = ok r'), r = r') := by
  sorry

end AegisSpec.IsNumber
