import Aegis.CountSegments.Code.Funs

/-!
# Specifications of `Aegis.CountSegments.count_segments`

LeetCode problem `number-of-segments-in-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountSegments

namespace AegisSpec.CountSegments

def isWhitespace (c : U8) : Prop := c.val = 32 ∨ c.val = 9 ∨ c.val = 10 ∨ c.val = 13

instance (c : U8) : Decidable (isWhitespace c) := by
  unfold isWhitespace
  infer_instance

def isWsB (c : U8) : Bool := decide (isWhitespace c)

def isLetter (c : U8) : Prop := (65 ≤ c.val ∧ c.val ≤ 90) ∨ (97 ≤ c.val ∧ c.val ≤ 122)

def isDigit (c : U8) : Prop := 48 ≤ c.val ∧ c.val ≤ 57

def punctBytes : List ℕ :=
  [33, 64, 35, 36, 37, 94, 38, 42, 40, 41, 95, 43, 45, 61, 39, 44, 46, 58]

def isPunct (c : U8) : Prop := c.val ∈ punctBytes

def isAllowed (c : U8) : Prop := isLetter c ∨ isDigit c ∨ isPunct c ∨ isWhitespace c

def AllowedBytes (l : List U8) : Prop :=
  ∀ (i : ℕ) (h : i < l.length), isAllowed (l.get ⟨i, h⟩)

def byteAt (l : List U8) (i : ℕ) : U8 := l.getD i 0#u8

def spaceByte : U8 := 32#u8

def segmentStarts (l : List U8) : List ℕ :=
  (List.range l.length).filter fun i =>
    decide (¬ isWhitespace (byteAt l i) ∧ (i = 0 ∨ isWhitespace (byteAt l (i - 1))))

def segmentStartCount (l : List U8) : ℕ := (segmentStarts l).length

def segmentEnds (l : List U8) : List ℕ :=
  (List.range l.length).filter fun i =>
    decide (¬ isWhitespace (byteAt l i) ∧ (i = l.length - 1 ∨ isWhitespace (byteAt l (i + 1))))

def segmentEndCount (l : List U8) : ℕ := (segmentEnds l).length

def noWsIn (l : List U8) (i j : ℕ) : Bool :=
  (List.range (j - i)).all fun k => !isWsB (byteAt l (i + k))

def segmentPairs (l : List U8) : List (ℕ × ℕ) :=
  ((List.range (l.length + 1)).product (List.range (l.length + 1))).filter fun p =>
    decide (p.1 < p.2 ∧ (p.1 = 0 ∨ isWhitespace (byteAt l (p.1 - 1))) ∧
      (p.2 = l.length ∨ isWhitespace (byteAt l p.2))) && noWsIn l p.1 p.2

def segmentPairCount (l : List U8) : ℕ := (segmentPairs l).length

def dropLeadingWs : List U8 → List U8
  | [] => []
  | c :: cs => if isWsB c then dropLeadingWs cs else c :: cs

def dropTrailingWs (l : List U8) : List U8 := (dropLeadingWs l.reverse).reverse

def trimWs (l : List U8) : List U8 := dropTrailingWs (dropLeadingWs l)

def collapseWsGo : List U8 → Bool → List U8
  | [], _ => []
  | c :: cs, prev =>
    if isWsB c then (if prev then [] else [spaceByte]) ++ collapseWsGo cs true
    else c :: collapseWsGo cs false

def collapseWs (l : List U8) : List U8 := collapseWsGo l false

/-- The function returns a result r such that r equals the number of indices i with 0 <= i < len(s) for which s[i] is not a whitespace character and (i = 0 or s[i-1] is a whitespace character).
  Preconditions: s is a byte slice. For every i with 0 <= i < len(s), s[i] is either an English letter, a digit, one of the characters "!@#$%^&*()_+-=',.:", or a whitespace character (32, 9, 10, or 13). -/
theorem spec_1 (s : Slice U8) (hAll : AllowedBytes s.val) :
    ∃ r : I64, count_segments s = ok r ∧ r.val = (segmentStartCount s.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (hAll : AllowedBytes s.val), ∃ r : I64, count_segments s = ok r ∧ r.val = (segmentStartCount s.val : ℤ)) := by
  sorry

/-- The function returns a result r such that 0 <= r <= len(s).
  Preconditions: s is a byte slice. For every i with 0 <= i < len(s), s[i] is either an English letter, a digit, one of the characters "!@#$%^&*()_+-=',.:", or a whitespace character (32, 9, 10, or 13). -/
theorem spec_2 (s : Slice U8) (hAll : AllowedBytes s.val) :
    ∃ r : I64, count_segments s = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (hAll : AllowedBytes s.val), ∃ r : I64, count_segments s = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ)) := by
  sorry

/-- If len(s) = 0, then the function returns r = 0.
  Preconditions: s is a byte slice. For every i with 0 <= i < len(s), s[i] is either an English letter, a digit, one of the characters "!@#$%^&*()_+-=',.:", or a whitespace character (32, 9, 10, or 13). -/
theorem spec_3 (s : Slice U8) (hAll : AllowedBytes s.val) (hlen : s.val.length = 0) :
    ∃ r : I64, count_segments s = ok r ∧ r.val = 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (hAll : AllowedBytes s.val) (hlen : s.val.length = 0), ∃ r : I64, count_segments s = ok r ∧ r.val = 0) := by
  sorry

/-- If len(s) > 0 and for every i with 0 <= i < len(s), s[i] is not a whitespace character (i.e., s[i] is not 32, 9, 10, or 13), then the function returns r = 1.
  Preconditions: s is a byte slice. For every i with 0 <= i < len(s), s[i] is either an English letter, a digit, one of the characters "!@#$%^&*()_+-=',.:", or a whitespace character (32, 9, 10, or 13). -/
theorem spec_4 (s : Slice U8) (hAll : AllowedBytes s.val) (hlen : 0 < s.val.length)
    (hnoWs : ∀ (i : ℕ) (h : i < s.val.length), ¬ isWhitespace (s.val.get ⟨i, h⟩)) :
    ∃ r : I64, count_segments s = ok r ∧ r.val = 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (hAll : AllowedBytes s.val) (hlen : 0 < s.val.length)
    (hnoWs : ∀ (i : ℕ) (h : i < s.val.length), ¬ isWhitespace (s.val.get ⟨i, h⟩)), ∃ r : I64, count_segments s = ok r ∧ r.val = 1) := by
  sorry

/-- If for every i with 0 <= i < len(s), s[i] is a whitespace character (32, 9, 10, or 13), then the function returns r = 0.
  Preconditions: s is a byte slice. For every i with 0 <= i < len(s), s[i] is either an English letter, a digit, one of the characters "!@#$%^&*()_+-=',.:", or a whitespace character (32, 9, 10, or 13). -/
theorem spec_5 (s : Slice U8) (hAll : AllowedBytes s.val)
    (hws : ∀ (i : ℕ) (h : i < s.val.length), isWhitespace (s.val.get ⟨i, h⟩)) :
    ∃ r : I64, count_segments s = ok r ∧ r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (hAll : AllowedBytes s.val)
    (hws : ∀ (i : ℕ) (h : i < s.val.length), isWhitespace (s.val.get ⟨i, h⟩)), ∃ r : I64, count_segments s = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r such that r equals the number of indices i with 0 <= i < len(s) for which s[i] is not a whitespace character (32, 9, 10, or 13) and (i = len(s)-1 or s[i+1] is a whitespace character).
  Preconditions: s is a byte slice. For every i with 0 <= i < len(s), s[i] is either an English letter, a digit, one of the characters "!@#$%^&*()_+-=',.:", or a whitespace character (32, 9, 10, or 13). -/
theorem spec_6 (s : Slice U8) (hAll : AllowedBytes s.val) :
    ∃ r : I64, count_segments s = ok r ∧ r.val = (segmentEndCount s.val : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (hAll : AllowedBytes s.val), ∃ r : I64, count_segments s = ok r ∧ r.val = (segmentEndCount s.val : ℤ)) := by
  sorry

/-- For any byte slice s' of the same length as s that also satisfies the same allowed-character condition (i.e., for every i with 0 <= i < len(s), s'[i] is either an English letter, a digit, one of the characters "!@#$%^&*()_+-=',.:", or a whitespace character (32, 9, 10, or 13)) and such that for every i with 0 <= i < len(s), s[i] is a whitespace character (32, 9, 10, or 13) if and only if s'[i] is a whitespace character (32, 9, 10, or 13), if count_segments(s) returns r and count_segments(s') returns r', then r = r'.
  Preconditions: s is a byte slice. For every i with 0 <= i < len(s), s[i] is either an English letter, a digit, one of the characters "!@#$%^&*()_+-=',.:", or a whitespace character (32, 9, 10, or 13). -/
theorem spec_7 (s s' : Slice U8) (hAll : AllowedBytes s.val) (hAll' : AllowedBytes s'.val)
    (hlen : s'.val.length = s.val.length)
    (hws : ∀ (i : ℕ), i < s.val.length →
      (isWhitespace (byteAt s.val i) ↔ isWhitespace (byteAt s'.val i))) :
    ∀ (r r' : I64), count_segments s = ok r → count_segments s' = ok r' → r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s s' : Slice U8) (hAll : AllowedBytes s.val) (hAll' : AllowedBytes s'.val)
    (hlen : s'.val.length = s.val.length)
    (hws : ∀ (i : ℕ), i < s.val.length →
      (isWhitespace (byteAt s.val i) ↔ isWhitespace (byteAt s'.val i))), ∀ (r r' : I64), count_segments s = ok r → count_segments s' = ok r' → r = r') := by
  sorry

/-- Let s' be the byte slice obtained by prepending a space character (32) to s (so len(s') = len(s) + 1, s'[0] = 32, and s'[i+1] = s[i] for 0 <= i < len(s)). Then if count_segments(s) returns r and count_segments(s') returns r', we have r = r'. The analogous statement holds for appending a space character (32) to s.
  Preconditions: s is a byte slice. For every i with 0 <= i < len(s), s[i] is either an English letter, a digit, one of the characters "!@#$%^&*()_+-=',.:", or a whitespace character (32, 9, 10, or 13). -/
theorem spec_8 (s : Slice U8) (hAll : AllowedBytes s.val) :
    (∀ (s' : Slice U8), s'.val = spaceByte :: s.val →
        ∀ (r r' : I64), count_segments s = ok r → count_segments s' = ok r' → r = r') ∧
      (∀ (s' : Slice U8), s'.val = s.val ++ [spaceByte] →
        ∀ (r r' : I64), count_segments s = ok r → count_segments s' = ok r' → r = r') := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8) (hAll : AllowedBytes s.val), (∀ (s' : Slice U8), s'.val = spaceByte :: s.val →
        ∀ (r r' : I64), count_segments s = ok r → count_segments s' = ok r' → r = r') ∧
      (∀ (s' : Slice U8), s'.val = s.val ++ [spaceByte] →
        ∀ (r r' : I64), count_segments s = ok r → count_segments s' = ok r' → r = r')) := by
  sorry

/-- Let s' be the byte slice obtained from s by replacing every maximal contiguous run of whitespace characters (32, 9, 10, or 13) in s with a single space character (32). Then if count_segments(s) returns r and count_segments(s') returns r', we have r = r'.
  Preconditions: s is a byte slice. For every i with 0 <= i < len(s), s[i] is either an English letter, a digit, one of the characters "!@#$%^&*()_+-=',.:", or a whitespace character (32, 9, 10, or 13). -/
theorem spec_9 (s s' : Slice U8) (hAll : AllowedBytes s.val)
    (hcollapse : s'.val = collapseWs s.val) :
    ∀ (r r' : I64), count_segments s = ok r → count_segments s' = ok r' → r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s s' : Slice U8) (hAll : AllowedBytes s.val)
    (hcollapse : s'.val = collapseWs s.val), ∀ (r r' : I64), count_segments s = ok r → count_segments s' = ok r' → r = r') := by
  sorry

/-- The function returns a result r such that r <= (len(s) + 1) / 2, where division is integer division.
  Preconditions: s is a byte slice. For every i with 0 <= i < len(s), s[i] is either an English letter, a digit, one of the characters "!@#$%^&*()_+-=',.:", or a whitespace character (32, 9, 10, or 13). -/
theorem spec_10 (s : Slice U8) (hAll : AllowedBytes s.val) :
    ∃ r : I64, count_segments s = ok r ∧ r.val ≤ ((s.val.length : ℤ) + 1) / 2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8) (hAll : AllowedBytes s.val), ∃ r : I64, count_segments s = ok r ∧ r.val ≤ ((s.val.length : ℤ) + 1) / 2) := by
  sorry

/-- The function returns a result r such that r = 0 if and only if there is no index i with 0 <= i < len(s) for which s[i] is not a whitespace character (32, 9, 10, or 13).
  Preconditions: s is a byte slice. For every i with 0 <= i < len(s), s[i] is either an English letter, a digit, one of the characters "!@#$%^&*()_+-=',.:", or a whitespace character (32, 9, 10, or 13). -/
theorem spec_11 (s : Slice U8) (hAll : AllowedBytes s.val) :
    ∃ r : I64, count_segments s = ok r ∧
      (r.val = 0 ↔ ¬ ∃ (i : ℕ) (h : i < s.val.length), ¬ isWhitespace (s.val.get ⟨i, h⟩)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice U8) (hAll : AllowedBytes s.val), ∃ r : I64, count_segments s = ok r ∧
      (r.val = 0 ↔ ¬ ∃ (i : ℕ) (h : i < s.val.length), ¬ isWhitespace (s.val.get ⟨i, h⟩))) := by
  sorry

/-- The function returns a result r such that r >= 1 if and only if there exists an index i with 0 <= i < len(s) for which s[i] is not a whitespace character (32, 9, 10, or 13).
  Preconditions: s is a byte slice. For every i with 0 <= i < len(s), s[i] is either an English letter, a digit, one of the characters "!@#$%^&*()_+-=',.:", or a whitespace character (32, 9, 10, or 13). -/
theorem spec_12 (s : Slice U8) (hAll : AllowedBytes s.val) :
    ∃ r : I64, count_segments s = ok r ∧
      (1 ≤ r.val ↔ ∃ (i : ℕ) (h : i < s.val.length), ¬ isWhitespace (s.val.get ⟨i, h⟩)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice U8) (hAll : AllowedBytes s.val), ∃ r : I64, count_segments s = ok r ∧
      (1 ≤ r.val ↔ ∃ (i : ℕ) (h : i < s.val.length), ¬ isWhitespace (s.val.get ⟨i, h⟩))) := by
  sorry

/-- The function returns a result r (i.e., it does not fail).
  Preconditions: s is a byte slice. For every i with 0 <= i < len(s), s[i] is either an English letter, a digit, one of the characters "!@#$%^&*()_+-=',.:", or a whitespace character (32, 9, 10, or 13). -/
theorem spec_13 (s : Slice U8) (hAll : AllowedBytes s.val) :
    ∃ r : I64, count_segments s = ok r := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice U8) (hAll : AllowedBytes s.val), ∃ r : I64, count_segments s = ok r) := by
  sorry

/-- Let s' be the byte slice obtained by removing all leading and trailing whitespace characters (32, 9, 10, or 13) from s. Then if count_segments(s) returns r and count_segments(s') returns r', we have r = r'.
  Preconditions: s is a byte slice. For every i with 0 <= i < len(s), s[i] is either an English letter, a digit, one of the characters "!@#$%^&*()_+-=',.:", or a whitespace character (32, 9, 10, or 13). -/
theorem spec_14 (s s' : Slice U8) (hAll : AllowedBytes s.val) (htrim : s'.val = trimWs s.val) :
    ∀ (r r' : I64), count_segments s = ok r → count_segments s' = ok r' → r = r' := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s s' : Slice U8) (hAll : AllowedBytes s.val) (htrim : s'.val = trimWs s.val), ∀ (r r' : I64), count_segments s = ok r → count_segments s' = ok r' → r = r') := by
  sorry

/-- Let s' be the byte slice obtained by appending c to s (so len(s') = len(s) + 1, s'[i] = s[i] for 0 <= i < len(s), and s'[len(s)] = c). If count_segments(s) returns r and count_segments(s') returns r', then: if len(s) = 0 or s[len(s)-1] is a whitespace character (32, 9, 10, or 13), then r' = r + 1; otherwise r' = r. The analogous statement holds for prepending c to s: if len(s) = 0 or s[0] is a whitespace character (32, 9, 10, or 13), then r' = r + 1; otherwise r' = r.
  Preconditions: s is a byte slice. For every i with 0 <= i < len(s), s[i] is either an English letter, a digit, one of the characters "!@#$%^&*()_+-=',.:", or a whitespace character (32, 9, 10, or 13). Let c be a byte that is an English letter, a digit, or one of the characters "!@#$%^&*()_+-=',.:" (i.e., a non-whitespace allowed character). -/
theorem spec_15 (s : Slice U8) (hAll : AllowedBytes s.val) (c : U8) (hcAllowed : isAllowed c)
    (hcNonWs : ¬ isWhitespace c) :
    (∀ (s' : Slice U8), s'.val = s.val ++ [c] →
        ∀ (r r' : I64), count_segments s = ok r → count_segments s' = ok r' →
          ((s.val.length = 0 ∨ isWhitespace (byteAt s.val (s.val.length - 1))) →
              r'.val = r.val + 1) ∧
            (¬ (s.val.length = 0 ∨ isWhitespace (byteAt s.val (s.val.length - 1))) →
              r'.val = r.val)) ∧
      (∀ (s' : Slice U8), s'.val = c :: s.val →
        ∀ (r r' : I64), count_segments s = ok r → count_segments s' = ok r' →
          ((s.val.length = 0 ∨ isWhitespace (byteAt s.val 0)) → r'.val = r.val + 1) ∧
            (¬ (s.val.length = 0 ∨ isWhitespace (byteAt s.val 0)) → r'.val = r.val)) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (s : Slice U8) (hAll : AllowedBytes s.val) (c : U8) (hcAllowed : isAllowed c)
    (hcNonWs : ¬ isWhitespace c), (∀ (s' : Slice U8), s'.val = s.val ++ [c] →
        ∀ (r r' : I64), count_segments s = ok r → count_segments s' = ok r' →
          ((s.val.length = 0 ∨ isWhitespace (byteAt s.val (s.val.length - 1))) →
              r'.val = r.val + 1) ∧
            (¬ (s.val.length = 0 ∨ isWhitespace (byteAt s.val (s.val.length - 1))) →
              r'.val = r.val)) ∧
      (∀ (s' : Slice U8), s'.val = c :: s.val →
        ∀ (r r' : I64), count_segments s = ok r → count_segments s' = ok r' →
          ((s.val.length = 0 ∨ isWhitespace (byteAt s.val 0)) → r'.val = r.val + 1) ∧
            (¬ (s.val.length = 0 ∨ isWhitespace (byteAt s.val 0)) → r'.val = r.val))) := by
  sorry

/-- The function returns a result r such that r equals the number of pairs (i, j) with 0 <= i <= j <= len(s) such that: (a) for every k with i <= k < j, s[k] is not a whitespace character (32, 9, 10, or 13); (b) either i = 0 or s[i-1] is a whitespace character (32, 9, 10, or 13); (c) either j = len(s) or s[j] is a whitespace character (32, 9, 10, or 13); and (d) i < j.
  Preconditions: s is a byte slice. For every i with 0 <= i < len(s), s[i] is either an English letter, a digit, one of the characters "!@#$%^&*()_+-=',.:", or a whitespace character (32, 9, 10, or 13). -/
theorem spec_16 (s : Slice U8) (hAll : AllowedBytes s.val) :
    ∃ r : I64, count_segments s = ok r ∧ r.val = (segmentPairCount s.val : ℤ) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (s : Slice U8) (hAll : AllowedBytes s.val), ∃ r : I64, count_segments s = ok r ∧ r.val = (segmentPairCount s.val : ℤ)) := by
  sorry

end AegisSpec.CountSegments
