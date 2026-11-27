import Aegis.LengthOfLongestSubstringTwoDistinct.Code.Funs

/-!
# Specifications of `Aegis.LengthOfLongestSubstringTwoDistinct.length_of_longest_substring_two_distinct`

LeetCode problem `longest-substring-with-at-most-two-distinct-characters`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LengthOfLongestSubstringTwoDistinct

  open Aegis.LengthOfLongestSubstringTwoDistinct

  def bytes (s : Slice Std.U8) : List ℕ := s.val.map (fun b => b.val)

  def isLetter (b : ℕ) : Prop := (65 ≤ b ∧ b ≤ 90) ∨ (97 ≤ b ∧ b ≤ 122)

  def allLetters (s : Slice Std.U8) : Prop := ∀ b ∈ s.val, isLetter b.val

  def byteAt (s : Slice Std.U8) (k : ℕ) : ℕ := (bytes s).getD k 0

  def win (s : Slice Std.U8) (i j : ℕ) : List ℕ := ((bytes s).drop i).take (j + 1 - i)

  def winVals (s : Slice Std.U8) (i j : ℕ) : Finset ℕ := (win s i j).toFinset

  def winCard (s : Slice Std.U8) (i j : ℕ) : ℕ := (winVals s i j).card

  def winLen (i j : ℕ) : ℤ := (j : ℤ) - (i : ℤ) + 1

  def valSet (s : Slice Std.U8) : Finset ℕ := (bytes s).toFinset

  def IsSubstrAt (s t : Slice Std.U8) (a : ℕ) : Prop :=
    a + t.val.length ≤ s.val.length ∧ ∀ k, k < t.val.length → byteAt t k = byteAt s (a + k)

  def SamePattern (s t : Slice Std.U8) : Prop :=
    s.val.length = t.val.length ∧
      ∀ i j, i < s.val.length → j < s.val.length →
        (byteAt s i = byteAt s j ↔ byteAt t i = byteAt t j)

  /-- The function returns an integer r equal to the maximum length of a contiguous substring of s that contains at most two distinct byte values. More explicitly, for indices 0 <= i <= j < len(s), let the substring s[i..j] be s[i], s[i+1], ..., s[j] and let its length be j-i+1. Then r = max { j-i+1 | 0 <= i <= j < len(s) and the set { s[k] | i <= k <= j } has cardinality at most 2 }.
    Preconditions: 1 <= len(s) <= 100000; every byte of s is an English ASCII letter (in 65..90 or 97..122). -/
  theorem spec_1 (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s) :
      ∃ r : Std.I64,
        length_of_longest_substring_two_distinct s = ok r ∧
          (∃ i j : ℕ, i ≤ j ∧ j < s.val.length ∧ winLen i j = r.val ∧ winCard s i j ≤ 2) ∧
          (∀ i j : ℕ, i ≤ j → j < s.val.length → winCard s i j ≤ 2 → winLen i j ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s), ∃ r : Std.I64,
          length_of_longest_substring_two_distinct s = ok r ∧
            (∃ i j : ℕ, i ≤ j ∧ j < s.val.length ∧ winLen i j = r.val ∧ winCard s i j ≤ 2) ∧
            (∀ i j : ℕ, i ≤ j → j < s.val.length → winCard s i j ≤ 2 → winLen i j ≤ r.val)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r. In particular, it does not fail, panic, access memory out of bounds, or overflow.
    Preconditions: 1 <= len(s) <= 100000; every byte of s is an English ASCII letter (in 65..90 or 97..122). -/
  theorem spec_2 (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s) :
      ∃ r : Std.I64, length_of_longest_substring_two_distinct s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s), ∃ r : Std.I64, length_of_longest_substring_two_distinct s = ok r) := by
    sorry

  /-- The function returns a result r and r <= len(s).
    Preconditions: 1 <= len(s) <= 100000; every byte of s is an English ASCII letter (in 65..90 or 97..122). -/
  theorem spec_3 (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s) :
      ∃ r : Std.I64,
        length_of_longest_substring_two_distinct s = ok r ∧ r.val ≤ (s.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s), ∃ r : Std.I64,
          length_of_longest_substring_two_distinct s = ok r ∧ r.val ≤ (s.val.length : ℤ)) := by
    sorry

  /-- The function returns a result r with r >= 1, and if len(s) >= 2 then r >= 2.
    Preconditions: 1 <= len(s) <= 100000; every byte of s is an English ASCII letter (in 65..90 or 97..122). -/
  theorem spec_4 (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s) :
      ∃ r : Std.I64,
        length_of_longest_substring_two_distinct s = ok r ∧ 1 ≤ r.val ∧
          (2 ≤ s.val.length → 2 ≤ r.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s), ∃ r : Std.I64,
          length_of_longest_substring_two_distinct s = ok r ∧ 1 ≤ r.val ∧
            (2 ≤ s.val.length → 2 ≤ r.val)) := by
    sorry

  /-- If the set of byte values occurring in s has cardinality at most 2, then the function returns r = len(s).
    Preconditions: 1 <= len(s) <= 100000; every byte of s is an English ASCII letter (in 65..90 or 97..122). -/
  theorem spec_5 (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s)
      (hvals : (valSet s).card ≤ 2) :
      ∃ r : Std.I64,
        length_of_longest_substring_two_distinct s = ok r ∧ r.val = (s.val.length : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s)
        (hvals : (valSet s).card ≤ 2), ∃ r : Std.I64,
          length_of_longest_substring_two_distinct s = ok r ∧ r.val = (s.val.length : ℤ)) := by
    sorry

  /-- If the set of byte values occurring in s has cardinality greater than 2, then the function returns a result r with r < len(s), equivalently r <= len(s)-1.
    Preconditions: 1 <= len(s) <= 100000; every byte of s is an English ASCII letter (in 65..90 or 97..122). -/
  theorem spec_6 (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s)
      (hvals : 2 < (valSet s).card) :
      ∃ r : Std.I64,
        length_of_longest_substring_two_distinct s = ok r ∧ r.val < (s.val.length : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s)
        (hvals : 2 < (valSet s).card), ∃ r : Std.I64,
          length_of_longest_substring_two_distinct s = ok r ∧ r.val < (s.val.length : ℤ)) := by
    sorry

  /-- If len(s) >= 3 and all byte values occurring in s are pairwise distinct, that is s[i] != s[j] for every 0 <= i < j < len(s), then the function returns r = 2.
    Preconditions: 1 <= len(s) <= 100000; every byte of s is an English ASCII letter (in 65..90 or 97..122). -/
  theorem spec_7 (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s)
      (hlen3 : 3 ≤ s.val.length)
      (hnd : ∀ i j : ℕ, i < j → j < s.val.length → byteAt s i ≠ byteAt s j) :
      ∃ r : Std.I64,
        length_of_longest_substring_two_distinct s = ok r ∧ r.val = 2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s)
        (hlen3 : 3 ≤ s.val.length)
        (hnd : ∀ i j : ℕ, i < j → j < s.val.length → byteAt s i ≠ byteAt s j), ∃ r : Std.I64,
          length_of_longest_substring_two_distinct s = ok r ∧ r.val = 2) := by
    sorry

  /-- The function returns a result r and there exist indices i and j with 0 <= i <= j < len(s) such that j-i+1 = r and the set { s[k] | i <= k <= j } has cardinality at most 2.
    Preconditions: 1 <= len(s) <= 100000; every byte of s is an English ASCII letter (in 65..90 or 97..122). -/
  theorem spec_8 (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s) :
      ∃ r : Std.I64,
        length_of_longest_substring_two_distinct s = ok r ∧
          ∃ i j : ℕ, i ≤ j ∧ j < s.val.length ∧ winLen i j = r.val ∧ winCard s i j ≤ 2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s), ∃ r : Std.I64,
          length_of_longest_substring_two_distinct s = ok r ∧
            ∃ i j : ℕ, i ≤ j ∧ j < s.val.length ∧ winLen i j = r.val ∧ winCard s i j ≤ 2) := by
    sorry

  /-- The function returns a result r and for every pair of indices i and j with 0 <= i <= j < len(s), if the set { s[k] | i <= k <= j } has cardinality at most 2, then j-i+1 <= r.
    Preconditions: 1 <= len(s) <= 100000; every byte of s is an English ASCII letter (in 65..90 or 97..122). -/
  theorem spec_9 (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s) :
      ∃ r : Std.I64,
        length_of_longest_substring_two_distinct s = ok r ∧
          ∀ i j : ℕ, i ≤ j → j < s.val.length → winCard s i j ≤ 2 → winLen i j ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s), ∃ r : Std.I64,
          length_of_longest_substring_two_distinct s = ok r ∧
            ∀ i j : ℕ, i ≤ j → j < s.val.length → winCard s i j ≤ 2 → winLen i j ≤ r.val) := by
    sorry

  /-- If the set of byte values occurring in s has cardinality greater than 2, then the function returns a result r and there exist indices i and j with 0 <= i <= j < len(s) such that j-i+1 = r and the set { s[k] | i <= k <= j } has cardinality exactly 2.
    Preconditions: 1 <= len(s) <= 100000; every byte of s is an English ASCII letter (in 65..90 or 97..122). -/
  theorem spec_10 (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s)
      (hvals : 2 < (valSet s).card) :
      ∃ r : Std.I64,
        length_of_longest_substring_two_distinct s = ok r ∧
          ∃ i j : ℕ, i ≤ j ∧ j < s.val.length ∧ winLen i j = r.val ∧ winCard s i j = 2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s)
        (hvals : 2 < (valSet s).card), ∃ r : Std.I64,
          length_of_longest_substring_two_distinct s = ok r ∧
            ∃ i j : ℕ, i ≤ j ∧ j < s.val.length ∧ winLen i j = r.val ∧ winCard s i j = 2) := by
    sorry

  /-- The function returns a result r for s. For every nonempty contiguous substring t of s, meaning t[k] = s[a+k] for some a with 0 <= a and 1 <= len(t) and a+len(t) <= len(s), if the same function returns r_t on input t, then r_t <= r.
    Preconditions: 1 <= len(s) <= 100000; every byte of s is an English ASCII letter (in 65..90 or 97..122). -/
  theorem spec_11 (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s) :
      ∃ r : Std.I64,
        length_of_longest_substring_two_distinct s = ok r ∧
          ∀ t : Slice Std.U8, 1 ≤ t.val.length → (∃ a : ℕ, IsSubstrAt s t a) →
            ∀ r_t : Std.I64, length_of_longest_substring_two_distinct t = ok r_t → r_t.val ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s), ∃ r : Std.I64,
          length_of_longest_substring_two_distinct s = ok r ∧
            ∀ t : Slice Std.U8, 1 ≤ t.val.length → (∃ a : ℕ, IsSubstrAt s t a) →
              ∀ r_t : Std.I64, length_of_longest_substring_two_distinct t = ok r_t → r_t.val ≤ r.val) := by
    sorry

  /-- The function returns a result r for s. For every byte c such that len(s) < 100000 and c is an English ASCII letter, let s' be the sequence obtained by appending c to s, and let r' be the result returned by the same function on s'. Then r' = r or r' = r+1.
    Preconditions: 1 <= len(s) <= 100000; every byte of s is an English ASCII letter (in 65..90 or 97..122). -/
  theorem spec_12 (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s)
      (hsmall : s.val.length < 100000) :
      ∃ r : Std.I64,
        length_of_longest_substring_two_distinct s = ok r ∧
          ∀ c : Std.U8, isLetter c.val →
            ∀ s' : Slice Std.U8, s'.val = s.val ++ [c] →
              ∀ r' : Std.I64,
                length_of_longest_substring_two_distinct s' = ok r' →
                  r'.val = r.val ∨ r'.val = r.val + 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s)
        (hsmall : s.val.length < 100000), ∃ r : Std.I64,
          length_of_longest_substring_two_distinct s = ok r ∧
            ∀ c : Std.U8, isLetter c.val →
              ∀ s' : Slice Std.U8, s'.val = s.val ++ [c] →
                ∀ r' : Std.I64,
                  length_of_longest_substring_two_distinct s' = ok r' →
                    r'.val = r.val ∨ r'.val = r.val + 1) := by
    sorry

  /-- Let rev(s) be the sequence of length len(s) defined by rev(s)[i] = s[len(s)-1-i] for all 0 <= i < len(s). If the function returns r on s and r_rev on rev(s), then r_rev = r.
    Preconditions: 1 <= len(s) <= 100000; every byte of s is an English ASCII letter (in 65..90 or 97..122). -/
  theorem spec_13 (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s) :
      ∀ r : Std.I64, length_of_longest_substring_two_distinct s = ok r →
        ∀ s' : Slice Std.U8, s'.val = s.val.reverse →
          ∀ r_rev : Std.I64,
            length_of_longest_substring_two_distinct s' = ok r_rev → r_rev.val = r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s), ∀ r : Std.I64, length_of_longest_substring_two_distinct s = ok r →
          ∀ s' : Slice Std.U8, s'.val = s.val.reverse →
            ∀ r_rev : Std.I64,
              length_of_longest_substring_two_distinct s' = ok r_rev → r_rev.val = r.val) := by
    sorry

  /-- Let t be any nonempty byte sequence with len(t) = len(s), len(t) <= 100000, all bytes of t English ASCII letters, and for all 0 <= i,j < len(s), s[i] = s[j] if and only if t[i] = t[j]. If the function returns r on s and r_t on t, then r_t = r.
    Preconditions: 1 <= len(s) <= 100000; every byte of s is an English ASCII letter (in 65..90 or 97..122). -/
  theorem spec_14 (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s) :
      ∀ t : Slice Std.U8, 1 ≤ t.val.length → t.val.length ≤ 100000 → allLetters t →
        SamePattern s t →
          ∀ r r_t : Std.I64,
            length_of_longest_substring_two_distinct s = ok r →
              length_of_longest_substring_two_distinct t = ok r_t → r_t.val = r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 100000) (hletters : allLetters s), ∀ t : Slice Std.U8, 1 ≤ t.val.length → t.val.length ≤ 100000 → allLetters t →
          SamePattern s t →
            ∀ r r_t : Std.I64,
              length_of_longest_substring_two_distinct s = ok r →
                length_of_longest_substring_two_distinct t = ok r_t → r_t.val = r.val) := by
    sorry

  end AegisSpec.LengthOfLongestSubstringTwoDistinct
