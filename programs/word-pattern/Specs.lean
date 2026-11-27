import Aegis.WordPattern.Code.Funs

/-!
# Specifications of `Aegis.WordPattern.word_pattern`

LeetCode problem `word-pattern`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.WordPattern

namespace AegisSpec.WordPattern

def bytes (sl : Slice Std.U8) : List Nat := sl.val.map (fun b => b.val)

def byteAt (sl : Slice Std.U8) (i : Nat) : Option Nat := (bytes sl)[i]?

def words (s : Slice Std.U8) : List (List Nat) :=
  ((bytes s).splitOn 32).filter (fun w => w ≠ [])

def wordAt (s : Slice Std.U8) (i : Nat) : Option (List Nat) := (words s)[i]?

def isLower (b : Nat) : Prop := 97 ≤ b ∧ b ≤ 122

def isLetterOrSpace (b : Nat) : Prop := isLower b ∨ b = 32

def firstByte (l : List Nat) : Option Nat := l[0]?

def lastByte (l : List Nat) : Option Nat := l[l.length - 1]?

def NoDoubleSpace : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => (a ≠ 32 ∨ b ≠ 32) ∧ NoDoubleSpace (b :: rest)

def joinWords (W : List (List Nat)) : List Nat := List.intercalate [32] W

def distinctBytes (l : List Nat) : List Nat := l.dedup

def distinctWords (W : List (List Nat)) : List (List Nat) := W.dedup

/-- Let W be the list of words of s, i.e. the maximal contiguous byte segments of s that do not contain a space byte, in left-to-right order; under the preconditions W is non-empty and every W[t] is non-empty. Whenever word_pattern pattern s returns a result r, r is true if and only if len(W) = len(pattern) and, for every i and j with 0 <= i < len(pattern) and 0 <= j < len(pattern), pattern[i] = pattern[j] if and only if W[i] = W[j] (word equality is equality of byte sequences).
  Preconditions: pattern and s are byte slices. 1 <= len(pattern) <= 300. Every byte of pattern is a lowercase English letter (byte value 97 through 122). 1 <= len(s) <= 3000. Every byte of s is a lowercase English letter or a space (byte value 32). s[0] is not a space and s[len(s)-1] is not a space. No two consecutive bytes of s are spaces; thus the words of s are separated by single spaces. -/
theorem spec_1 (pattern s : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s)) :
    ∀ r, word_pattern pattern s = ok r →
      (r = true ↔
        (words s).length = (bytes pattern).length ∧
        ∀ i j : Nat, i < (bytes pattern).length → j < (bytes pattern).length →
          (byteAt pattern i = byteAt pattern j ↔ wordAt s i = wordAt s j)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (pattern s : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s)), ∀ r, word_pattern pattern s = ok r →
      (r = true ↔
        (words s).length = (bytes pattern).length ∧
        ∀ i j : Nat, i < (bytes pattern).length → j < (bytes pattern).length →
          (byteAt pattern i = byteAt pattern j ↔ wordAt s i = wordAt s j))) := by
  sorry

/-- For every pattern and s satisfying the preconditions, word_pattern pattern s returns a result r (it does not fail: no overflow, out-of-bounds access, or panic).
  Preconditions: pattern and s are byte slices. 1 <= len(pattern) <= 300. Every byte of pattern is a lowercase English letter (byte value 97 through 122). 1 <= len(s) <= 3000. Every byte of s is a lowercase English letter or a space (byte value 32). s[0] is not a space and s[len(s)-1] is not a space. No two consecutive bytes of s are spaces; thus the words of s are separated by single spaces. -/
theorem spec_2 (pattern s : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s)) :
    ∃ r, word_pattern pattern s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (pattern s : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s)), ∃ r, word_pattern pattern s = ok r) := by
  sorry

/-- Let W be the list of words of s. Whenever word_pattern pattern s returns a result r and len(W) != len(pattern), r is false. Equivalently, if word_pattern pattern s returns true, then len(W) = len(pattern).
  Preconditions: pattern and s are byte slices. 1 <= len(pattern) <= 300. Every byte of pattern is a lowercase English letter (byte value 97 through 122). 1 <= len(s) <= 3000. Every byte of s is a lowercase English letter or a space (byte value 32). s[0] is not a space and s[len(s)-1] is not a space. No two consecutive bytes of s are spaces; thus the words of s are separated by single spaces. -/
theorem spec_3 (pattern s : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s)) :
    ∀ r, word_pattern pattern s = ok r →
      ((words s).length ≠ (bytes pattern).length → r = false) ∧
      (r = true → (words s).length = (bytes pattern).length) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (pattern s : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s)), ∀ r, word_pattern pattern s = ok r →
      ((words s).length ≠ (bytes pattern).length → r = false) ∧
      (r = true → (words s).length = (bytes pattern).length)) := by
  sorry

/-- Let W be the list of words of s. Whenever word_pattern pattern s returns true, for every i and j with 0 <= i < len(pattern) and 0 <= j < len(pattern), the words W[i] and W[j] are defined and pattern[i] = pattern[j] implies W[i] = W[j].
  Preconditions: pattern and s are byte slices. 1 <= len(pattern) <= 300. Every byte of pattern is a lowercase English letter (byte value 97 through 122). 1 <= len(s) <= 3000. Every byte of s is a lowercase English letter or a space (byte value 32). s[0] is not a space and s[len(s)-1] is not a space. No two consecutive bytes of s are spaces; thus the words of s are separated by single spaces. -/
theorem spec_4 (pattern s : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s)) :
    ∀ r, word_pattern pattern s = ok r → r = true →
      ∀ i j : Nat, i < (bytes pattern).length → j < (bytes pattern).length →
        ∃ wi wj : List Nat,
          wordAt s i = some wi ∧ wordAt s j = some wj ∧
          (byteAt pattern i = byteAt pattern j → wi = wj) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (pattern s : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s)), ∀ r, word_pattern pattern s = ok r → r = true →
      ∀ i j : Nat, i < (bytes pattern).length → j < (bytes pattern).length →
        ∃ wi wj : List Nat,
          wordAt s i = some wi ∧ wordAt s j = some wj ∧
          (byteAt pattern i = byteAt pattern j → wi = wj)) := by
  sorry

/-- Let W be the list of words of s. Whenever word_pattern pattern s returns true, for every i and j with 0 <= i < len(pattern) and 0 <= j < len(pattern), the words W[i] and W[j] are defined and W[i] = W[j] implies pattern[i] = pattern[j].
  Preconditions: pattern and s are byte slices. 1 <= len(pattern) <= 300. Every byte of pattern is a lowercase English letter (byte value 97 through 122). 1 <= len(s) <= 3000. Every byte of s is a lowercase English letter or a space (byte value 32). s[0] is not a space and s[len(s)-1] is not a space. No two consecutive bytes of s are spaces; thus the words of s are separated by single spaces. -/
theorem spec_5 (pattern s : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s)) :
    ∀ r, word_pattern pattern s = ok r → r = true →
      ∀ i j : Nat, i < (bytes pattern).length → j < (bytes pattern).length →
        ∃ wi wj : List Nat,
          wordAt s i = some wi ∧ wordAt s j = some wj ∧
          (wi = wj → byteAt pattern i = byteAt pattern j) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (pattern s : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s)), ∀ r, word_pattern pattern s = ok r → r = true →
      ∀ i j : Nat, i < (bytes pattern).length → j < (bytes pattern).length →
        ∃ wi wj : List Nat,
          wordAt s i = some wi ∧ wordAt s j = some wj ∧
          (wi = wj → byteAt pattern i = byteAt pattern j)) := by
  sorry

/-- Let W be the list of words of s. Let rev_pattern be the byte slice of length len(pattern) with rev_pattern[i] = pattern[len(pattern)-1-i] for 0 <= i < len(pattern). Let rev_s be the byte string obtained by writing W[len(W)-1], W[len(W)-2], ..., W[0] in that order, separated by single space bytes, with no leading or trailing space. Whenever word_pattern pattern s and word_pattern rev_pattern rev_s both return results r1 and r2, r1 = r2.
  Preconditions: pattern and s are byte slices. 1 <= len(pattern) <= 300. Every byte of pattern is a lowercase English letter (byte value 97 through 122). 1 <= len(s) <= 3000. Every byte of s is a lowercase English letter or a space (byte value 32). s[0] is not a space and s[len(s)-1] is not a space. No two consecutive bytes of s are spaces; thus the words of s are separated by single spaces. -/
theorem spec_6 (pattern s rev_pattern rev_s : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s))
    (hrev_pattern : bytes rev_pattern = (bytes pattern).reverse)
    (hrev_s : bytes rev_s = joinWords (words s).reverse) :
    ∀ r1 r2, word_pattern pattern s = ok r1 →
      word_pattern rev_pattern rev_s = ok r2 → r1 = r2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (pattern s rev_pattern rev_s : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s))
    (hrev_pattern : bytes rev_pattern = (bytes pattern).reverse)
    (hrev_s : bytes rev_s = joinWords (words s).reverse), ∀ r1 r2, word_pattern pattern s = ok r1 →
      word_pattern rev_pattern rev_s = ok r2 → r1 = r2) := by
  sorry

/-- For every byte slice p' such that len(p') = len(pattern), every byte of p' is a lowercase English letter, and for all i and j with 0 <= i < len(pattern) and 0 <= j < len(pattern), p'[i] = p'[j] if and only if pattern[i] = pattern[j], whenever word_pattern pattern s and word_pattern p' s both return results r and r', we have r = r'.
  Preconditions: pattern and s are byte slices. 1 <= len(pattern) <= 300. Every byte of pattern is a lowercase English letter (byte value 97 through 122). 1 <= len(s) <= 3000. Every byte of s is a lowercase English letter or a space (byte value 32). s[0] is not a space and s[len(s)-1] is not a space. No two consecutive bytes of s are spaces; thus the words of s are separated by single spaces. -/
theorem spec_7 (pattern p' s : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s))
    (hp'_len : (bytes p').length = (bytes pattern).length)
    (hp'_lower : ∀ b ∈ bytes p', isLower b)
    (hp'_eq : ∀ i j : Nat, i < (bytes pattern).length → j < (bytes pattern).length →
      (byteAt p' i = byteAt p' j ↔ byteAt pattern i = byteAt pattern j)) :
    ∀ r r', word_pattern pattern s = ok r → word_pattern p' s = ok r' → r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (pattern p' s : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s))
    (hp'_len : (bytes p').length = (bytes pattern).length)
    (hp'_lower : ∀ b ∈ bytes p', isLower b)
    (hp'_eq : ∀ i j : Nat, i < (bytes pattern).length → j < (bytes pattern).length →
      (byteAt p' i = byteAt p' j ↔ byteAt pattern i = byteAt pattern j)), ∀ r r', word_pattern pattern s = ok r → word_pattern p' s = ok r' → r = r') := by
  sorry

/-- Let W be the list of words of s. For every byte string s' satisfying the same syntactic conditions as s (1 <= len(s') <= 3000, every byte is a lowercase English letter or a space, no leading or trailing space, no two consecutive spaces), if W' is the list of words of s', len(W') = len(W), and for all i and j with 0 <= i < len(W) and 0 <= j < len(W), W'[i] = W'[j] if and only if W[i] = W[j], then whenever word_pattern pattern s and word_pattern pattern s' both return results r and r', we have r = r'.
  Preconditions: pattern and s are byte slices. 1 <= len(pattern) <= 300. Every byte of pattern is a lowercase English letter (byte value 97 through 122). 1 <= len(s) <= 3000. Every byte of s is a lowercase English letter or a space (byte value 32). s[0] is not a space and s[len(s)-1] is not a space. No two consecutive bytes of s are spaces; thus the words of s are separated by single spaces. -/
theorem spec_8 (pattern s s' : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s))
    (hs'_len_lo : 1 ≤ (bytes s').length)
    (hs'_len_hi : (bytes s').length ≤ 3000)
    (hs'_letter : ∀ b ∈ bytes s', isLetterOrSpace b)
    (hs'_first : firstByte (bytes s') ≠ some 32)
    (hs'_last : lastByte (bytes s') ≠ some 32)
    (hs'_noDouble : NoDoubleSpace (bytes s'))
    (hW'_len : (words s').length = (words s).length)
    (hW'_eq : ∀ i j : Nat, i < (words s).length → j < (words s).length →
      (wordAt s' i = wordAt s' j ↔ wordAt s i = wordAt s j)) :
    ∀ r r', word_pattern pattern s = ok r → word_pattern pattern s' = ok r' → r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (pattern s s' : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s))
    (hs'_len_lo : 1 ≤ (bytes s').length)
    (hs'_len_hi : (bytes s').length ≤ 3000)
    (hs'_letter : ∀ b ∈ bytes s', isLetterOrSpace b)
    (hs'_first : firstByte (bytes s') ≠ some 32)
    (hs'_last : lastByte (bytes s') ≠ some 32)
    (hs'_noDouble : NoDoubleSpace (bytes s'))
    (hW'_len : (words s').length = (words s).length)
    (hW'_eq : ∀ i j : Nat, i < (words s).length → j < (words s).length →
      (wordAt s' i = wordAt s' j ↔ wordAt s i = wordAt s j)), ∀ r r', word_pattern pattern s = ok r → word_pattern pattern s' = ok r' → r = r') := by
  sorry

/-- Let W be the list of words of s. Let D be the set of distinct byte values occurring in pattern, and let E be the set of distinct words occurring among the words W. Whenever word_pattern pattern s returns true, len(W) = len(pattern) and there exists a bijection f from D to E such that for every i with 0 <= i < len(pattern), f(pattern[i]) = W[i].
  Preconditions: pattern and s are byte slices. 1 <= len(pattern) <= 300. Every byte of pattern is a lowercase English letter (byte value 97 through 122). 1 <= len(s) <= 3000. Every byte of s is a lowercase English letter or a space (byte value 32). s[0] is not a space and s[len(s)-1] is not a space. No two consecutive bytes of s are spaces; thus the words of s are separated by single spaces. -/
theorem spec_9 (pattern s : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s)) :
    ∀ r, word_pattern pattern s = ok r → r = true →
      (words s).length = (bytes pattern).length ∧
      ∃ f : Nat → List Nat,
        (∀ b, b ∈ distinctBytes (bytes pattern) → f b ∈ distinctWords (words s)) ∧
        (∀ a, a ∈ distinctBytes (bytes pattern) →
          ∀ b, b ∈ distinctBytes (bytes pattern) → f a = f b → a = b) ∧
        (∀ w, w ∈ distinctWords (words s) →
          ∃ b, b ∈ distinctBytes (bytes pattern) ∧ f b = w) ∧
        (∀ i, i < (bytes pattern).length →
          ∃ b w, byteAt pattern i = some b ∧ wordAt s i = some w ∧ f b = w) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (pattern s : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s)), ∀ r, word_pattern pattern s = ok r → r = true →
      (words s).length = (bytes pattern).length ∧
      ∃ f : Nat → List Nat,
        (∀ b, b ∈ distinctBytes (bytes pattern) → f b ∈ distinctWords (words s)) ∧
        (∀ a, a ∈ distinctBytes (bytes pattern) →
          ∀ b, b ∈ distinctBytes (bytes pattern) → f a = f b → a = b) ∧
        (∀ w, w ∈ distinctWords (words s) →
          ∃ b, b ∈ distinctBytes (bytes pattern) ∧ f b = w) ∧
        (∀ i, i < (bytes pattern).length →
          ∃ b w, byteAt pattern i = some b ∧ wordAt s i = some w ∧ f b = w)) := by
  sorry

/-- Let W be the list of words of s. Whenever word_pattern pattern s returns false, exactly one of the following holds: (a) len(W) != len(pattern); or (b) len(W) = len(pattern) and there exist indices i and j with 0 <= i < len(pattern) and 0 <= j < len(pattern) such that either (pattern[i] = pattern[j] and W[i] != W[j]) or (pattern[i] != pattern[j] and W[i] = W[j]).
  Preconditions: pattern and s are byte slices. 1 <= len(pattern) <= 300. Every byte of pattern is a lowercase English letter (byte value 97 through 122). 1 <= len(s) <= 3000. Every byte of s is a lowercase English letter or a space (byte value 32). s[0] is not a space and s[len(s)-1] is not a space. No two consecutive bytes of s are spaces; thus the words of s are separated by single spaces. -/
theorem spec_10 (pattern s : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s)) :
    ∀ r, word_pattern pattern s = ok r → r = false →
      (words s).length ≠ (bytes pattern).length ∨
      ((words s).length = (bytes pattern).length ∧
        ∃ i j : Nat, i < (bytes pattern).length ∧ j < (bytes pattern).length ∧
          ∃ wi wj : List Nat,
            wordAt s i = some wi ∧ wordAt s j = some wj ∧
            ((byteAt pattern i = byteAt pattern j ∧ wi ≠ wj) ∨
             (byteAt pattern i ≠ byteAt pattern j ∧ wi = wj))) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (pattern s : Slice Std.U8)
    (hpat_len_lo : 1 ≤ (bytes pattern).length)
    (hpat_len_hi : (bytes pattern).length ≤ 300)
    (hpat_lower : ∀ b ∈ bytes pattern, isLower b)
    (hs_len_lo : 1 ≤ (bytes s).length)
    (hs_len_hi : (bytes s).length ≤ 3000)
    (hs_letter : ∀ b ∈ bytes s, isLetterOrSpace b)
    (hs_first : firstByte (bytes s) ≠ some 32)
    (hs_last : lastByte (bytes s) ≠ some 32)
    (hs_noDouble : NoDoubleSpace (bytes s)), ∀ r, word_pattern pattern s = ok r → r = false →
      (words s).length ≠ (bytes pattern).length ∨
      ((words s).length = (bytes pattern).length ∧
        ∃ i j : Nat, i < (bytes pattern).length ∧ j < (bytes pattern).length ∧
          ∃ wi wj : List Nat,
            wordAt s i = some wi ∧ wordAt s j = some wj ∧
            ((byteAt pattern i = byteAt pattern j ∧ wi ≠ wj) ∨
             (byteAt pattern i ≠ byteAt pattern j ∧ wi = wj)))) := by
  sorry

end AegisSpec.WordPattern
