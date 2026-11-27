import Aegis.MaxLengthBetweenEqualCharacters.Code.Funs

/-!
# Specifications of `Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters`

LeetCode problem `largest-substring-between-two-equal-characters`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxLengthBetweenEqualCharacters

  open Aeneas Aeneas.Std Result

  def byteAt (s : Slice Std.U8) (i : Nat) : Nat := (s.val.getD i default).val

  def allLower (s : Slice Std.U8) : Prop :=
    ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122

  def validInput (s : Slice Std.U8) : Prop :=
    1 ≤ s.val.length ∧ s.val.length ≤ 300 ∧ allLower s

  def hasEqualPair (s : Slice Std.U8) : Prop :=
    ∃ i j : Nat, i < j ∧ j < s.val.length ∧ byteAt s i = byteAt s j

  def betweenLengths (s : Slice Std.U8) : Set Int :=
    {k | ∃ i j : Nat,
      i < j ∧ j < s.val.length ∧ byteAt s i = byteAt s j ∧ k = (j : Int) - (i : Int) - 1}

  /-- Whenever the function returns a result r, the following holds. Let n = len(s). If there exist indices i, j with 0 <= i < j < n and s[i] = s[j], then r is the maximum of the set { j - i - 1 | 0 <= i < j < n and s[i] = s[j] }; otherwise r = -1. The substring between the two equal characters excludes the two endpoint characters, so adjacent equal characters give length 0.
    Preconditions: 1 <= len(s) <= 300 and, for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_1 (s : Slice Std.U8) (hpre : validInput s) (r : Std.I64)
      (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r) :
      (hasEqualPair s → IsGreatest (betweenLengths s) r.val) ∧
        (¬ hasEqualPair s → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : validInput s) (r : Std.I64)
        (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r), (hasEqualPair s → IsGreatest (betweenLengths s) r.val) ∧
          (¬ hasEqualPair s → r.val = -1)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: 1 <= len(s) <= 300 and, for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_2 (s : Slice Std.U8) (hpre : validInput s) :
      ∃ r : Std.I64,
        Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : validInput s), ∃ r : Std.I64,
          Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, -1 <= r <= len(s) - 2.
    Preconditions: 1 <= len(s) <= 300 and, for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_3 (s : Slice Std.U8) (hpre : validInput s) (r : Std.I64)
      (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r) :
      -1 ≤ r.val ∧ r.val ≤ (s.val.length : Int) - 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : validInput s) (r : Std.I64)
        (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r), -1 ≤ r.val ∧ r.val ≤ (s.val.length : Int) - 2) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, there exist indices i and j such that 0 <= i < j < len(s), s[i] = s[j], and r = j - i - 1.
    Preconditions: 1 <= len(s) <= 300 and, for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_4 (s : Slice Std.U8) (hpre : validInput s) (r : Std.I64)
      (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r)
      (h0 : 0 ≤ r.val) :
      ∃ i j : Nat,
        i < j ∧ j < s.val.length ∧ byteAt s i = byteAt s j ∧
          r.val = (j : Int) - (i : Int) - 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : validInput s) (r : Std.I64)
        (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r)
        (h0 : 0 ≤ r.val), ∃ i j : Nat,
          i < j ∧ j < s.val.length ∧ byteAt s i = byteAt s j ∧
            r.val = (j : Int) - (i : Int) - 1) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, for every pair of indices i and j with 0 <= i < j < len(s) and s[i] = s[j], we have j - i - 1 <= r.
    Preconditions: 1 <= len(s) <= 300 and, for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_5 (s : Slice Std.U8) (hpre : validInput s) (r : Std.I64)
      (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r)
      (h0 : 0 ≤ r.val) :
      ∀ i j : Nat,
        i < j → j < s.val.length → byteAt s i = byteAt s j →
          (j : Int) - (i : Int) - 1 ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : validInput s) (r : Std.I64)
        (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r)
        (h0 : 0 ≤ r.val), ∀ i j : Nat,
          i < j → j < s.val.length → byteAt s i = byteAt s j →
            (j : Int) - (i : Int) - 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = -1 if and only if there do not exist indices i and j with 0 <= i < j < len(s) and s[i] = s[j].
    Preconditions: 1 <= len(s) <= 300 and, for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_6 (s : Slice Std.U8) (hpre : validInput s) (r : Std.I64)
      (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r) :
      (r.val = -1 ↔ ¬ hasEqualPair s) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : validInput s) (r : Std.I64)
        (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r), (r.val = -1 ↔ ¬ hasEqualPair s)) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: 1 <= len(s) <= 300, all bytes are lowercase letters, and there exists an index i with 0 <= i < len(s)-1 and s[i] = s[i+1]. -/
  theorem spec_7 (s : Slice Std.U8) (hpre : validInput s)
      (hadj : ∃ i : Nat, i + 1 < s.val.length ∧ byteAt s i = byteAt s (i + 1))
      (r : Std.I64)
      (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r) :
      0 ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : validInput s)
        (hadj : ∃ i : Nat, i + 1 < s.val.length ∧ byteAt s i = byteAt s (i + 1))
        (r : Std.I64)
        (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r), 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = len(s) - 2.
    Preconditions: 1 <= len(s) <= 300, all bytes are lowercase letters, len(s) >= 2, and s[0] = s[len(s)-1]. -/
  theorem spec_8 (s : Slice Std.U8) (hpre : validInput s)
      (hlen : 2 ≤ s.val.length)
      (hend : byteAt s 0 = byteAt s (s.val.length - 1))
      (r : Std.I64)
      (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r) :
      r.val = (s.val.length : Int) - 2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : validInput s)
        (hlen : 2 ≤ s.val.length)
        (hend : byteAt s 0 = byteAt s (s.val.length - 1))
        (r : Std.I64)
        (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r), r.val = (s.val.length : Int) - 2) := by
    sorry

  /-- Whenever the function returns r on input s and returns r' on input rev(s), r = r'.
    Preconditions: 1 <= len(s) <= 300 and all bytes of s are lowercase letters. Let n = len(s) and let rev(s) be the slice of length n with rev(s)[i] = s[n-1-i] for every 0 <= i < n. -/
  theorem spec_9 (s : Slice Std.U8) (hpre : validInput s) (t : Slice Std.U8)
      (ht : t.val = s.val.reverse) (r r' : Std.I64)
      (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r)
      (hr' : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters t = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : validInput s) (t : Slice Std.U8)
        (ht : t.val = s.val.reverse) (r r' : Std.I64)
        (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r)
        (hr' : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters t = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever the function returns r on input s and returns r' on input s', r = r'.
    Preconditions: 1 <= len(s) <= 300 and all bytes of s are lowercase letters. Let c be a byte with 97 <= c <= 122 such that c != s[i] for every 0 <= i < len(s), and len(s)+1 <= 300. Let s' be the slice of length len(s)+1 with s'[i] = s[i] for 0 <= i < len(s) and s'[len(s)] = c. -/
  theorem spec_10 (s : Slice Std.U8) (hpre : validInput s)
      (hlen : s.val.length + 1 ≤ 300)
      (c : Std.U8) (hc_lo : 97 ≤ c.val) (hc_hi : c.val ≤ 122)
      (hfresh : ∀ i : Nat, i < s.val.length → byteAt s i ≠ c.val)
      (s' : Slice Std.U8) (hs' : s'.val = s.val ++ [c])
      (r r' : Std.I64)
      (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r)
      (hr' : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : validInput s)
        (hlen : s.val.length + 1 ≤ 300)
        (c : Std.U8) (hc_lo : 97 ≤ c.val) (hc_hi : c.val ≤ 122)
        (hfresh : ∀ i : Nat, i < s.val.length → byteAt s i ≠ c.val)
        (s' : Slice Std.U8) (hs' : s'.val = s.val ++ [c])
        (r r' : Std.I64)
        (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r)
        (hr' : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s' = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever the function returns r on input s and returns r' on input t, r = r'.
    Preconditions: s and t are slices satisfying 1 <= len(s) = len(t) <= 300 and all their bytes are lowercase letters, and for all i and j with 0 <= i < len(s) and 0 <= j < len(s), s[i] = s[j] if and only if t[i] = t[j]. -/
  theorem spec_11 (s t : Slice Std.U8)
      (hlen : s.val.length = t.val.length)
      (hpos : 1 ≤ s.val.length) (hlen300 : s.val.length ≤ 300)
      (hs_lower : allLower s) (ht_lower : allLower t)
      (hpat : ∀ i j : Nat, i < s.val.length → j < s.val.length →
        (byteAt s i = byteAt s j ↔ byteAt t i = byteAt t j))
      (r r' : Std.I64)
      (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r)
      (hr' : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters t = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hlen : s.val.length = t.val.length)
        (hpos : 1 ≤ s.val.length) (hlen300 : s.val.length ≤ 300)
        (hs_lower : allLower s) (ht_lower : allLower t)
        (hpat : ∀ i j : Nat, i < s.val.length → j < s.val.length →
          (byteAt s i = byteAt s j ↔ byteAt t i = byteAt t j))
        (r r' : Std.I64)
        (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r)
        (hr' : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters t = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever the function returns a result r and r = -1, we have len(s) <= 26.
    Preconditions: 1 <= len(s) <= 300 and, for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_12 (s : Slice Std.U8) (hpre : validInput s) (r : Std.I64)
      (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r)
      (hneg : r.val = -1) :
      s.val.length ≤ 26 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8) (hpre : validInput s) (r : Std.I64)
        (hr : Aegis.MaxLengthBetweenEqualCharacters.max_length_between_equal_characters s = ok r)
        (hneg : r.val = -1), s.val.length ≤ 26) := by
    sorry

  end AegisSpec.MaxLengthBetweenEqualCharacters
