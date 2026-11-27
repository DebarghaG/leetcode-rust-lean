import Aegis.IsCircularSentence.Code.Funs

/-!
# Specifications of `Aegis.IsCircularSentence.is_circular_sentence`

LeetCode problem `circular-sentence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsCircularSentence

  open Aegis.IsCircularSentence (is_circular_sentence)

  def byteAt (l : List Std.U8) (i : Nat) : Std.U8 := l.getD i 0#u8

  def isSpace (b : Std.U8) : Prop := b.val = 32

  def isLetter (b : Std.U8) : Prop :=
    (65 ≤ b.val ∧ b.val ≤ 90) ∨ (97 ≤ b.val ∧ b.val ≤ 122)

  def blocksFrom (i : Nat) (cur : Option Nat) : List Std.U8 → List (Nat × Nat)
    | [] =>
      match cur with
      | some s => [(s, i - 1)]
      | none => []
    | b :: rest =>
      if b.val = 32 then
        (match cur with
          | some s => [(s, i - 1)]
          | none => []) ++ blocksFrom (i + 1) none rest
      else
        blocksFrom (i + 1) (some (cur.getD i)) rest

  def wordBounds (l : List Std.U8) : List (Nat × Nat) := blocksFrom 0 none l

  def numWords (l : List Std.U8) : Nat := (wordBounds l).length

  def firstIdx (l : List Std.U8) (j : Nat) : Nat := ((wordBounds l).getD j (0, 0)).1

  def lastIdx (l : List Std.U8) (j : Nat) : Nat := ((wordBounds l).getD j (0, 0)).2

  /-- Let n be the number of maximal contiguous non-space blocks (words) in sentence, ordered left to right, and for 0 <= j < n let f(j) be the index of the first byte and l(j) the index of the last byte of the j-th block. The function returns a result r (not failure) and r = true if and only if for every j with 0 <= j < n, sentence[l(j)] = sentence[f((j+1) mod n)]. In particular, the last byte of each word equals the first byte of the next word, with the last word wrapping to the first; for n = 1 this is the condition sentence[l(0)] = sentence[f(0)].
    Preconditions: len(sentence) is between 1 and 500 inclusive; every byte of sentence is either the space byte 32, an uppercase ASCII letter (65..90), or a lowercase ASCII letter (97..122); sentence[0] != 32 and sentence[len(sentence)-1] != 32; there are no two consecutive space bytes (for every i with 0 <= i < len(sentence)-1, not (sentence[i] = 32 and sentence[i+1] = 32)). -/
  theorem spec_1 (sentence : Slice Std.U8)
      (hlen_lo : 1 ≤ sentence.val.length) (hlen_hi : sentence.val.length ≤ 500)
      (hbytes : ∀ b ∈ sentence.val, isSpace b ∨ isLetter b)
      (hfirst : ¬ isSpace (byteAt sentence.val 0))
      (hlast : ¬ isSpace (byteAt sentence.val (sentence.val.length - 1)))
      (hnospaces : ∀ i, i + 1 < sentence.val.length →
        ¬ (isSpace (byteAt sentence.val i) ∧ isSpace (byteAt sentence.val (i + 1)))) :
      ∃ r, is_circular_sentence sentence = ok r ∧
        (r = true ↔ ∀ j, j < numWords sentence.val →
          byteAt sentence.val (lastIdx sentence.val j) =
            byteAt sentence.val (firstIdx sentence.val ((j + 1) % numWords sentence.val))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (sentence : Slice Std.U8)
        (hlen_lo : 1 ≤ sentence.val.length) (hlen_hi : sentence.val.length ≤ 500)
        (hbytes : ∀ b ∈ sentence.val, isSpace b ∨ isLetter b)
        (hfirst : ¬ isSpace (byteAt sentence.val 0))
        (hlast : ¬ isSpace (byteAt sentence.val (sentence.val.length - 1)))
        (hnospaces : ∀ i, i + 1 < sentence.val.length →
          ¬ (isSpace (byteAt sentence.val i) ∧ isSpace (byteAt sentence.val (i + 1)))), ∃ r, is_circular_sentence sentence = ok r ∧
          (r = true ↔ ∀ j, j < numWords sentence.val →
            byteAt sentence.val (lastIdx sentence.val j) =
              byteAt sentence.val (firstIdx sentence.val ((j + 1) % numWords sentence.val)))) := by
    sorry

  /-- The function returns a result r (not failure).
    Preconditions: len(sentence) is between 1 and 500 inclusive; every byte of sentence is either the space byte 32, an uppercase ASCII letter (65..90), or a lowercase ASCII letter (97..122); sentence[0] != 32 and sentence[len(sentence)-1] != 32; there are no two consecutive space bytes (for every i with 0 <= i < len(sentence)-1, not (sentence[i] = 32 and sentence[i+1] = 32)). -/
  theorem spec_2 (sentence : Slice Std.U8)
      (hlen_lo : 1 ≤ sentence.val.length) (hlen_hi : sentence.val.length ≤ 500)
      (hbytes : ∀ b ∈ sentence.val, isSpace b ∨ isLetter b)
      (hfirst : ¬ isSpace (byteAt sentence.val 0))
      (hlast : ¬ isSpace (byteAt sentence.val (sentence.val.length - 1)))
      (hnospaces : ∀ i, i + 1 < sentence.val.length →
        ¬ (isSpace (byteAt sentence.val i) ∧ isSpace (byteAt sentence.val (i + 1)))) :
      ∃ r, is_circular_sentence sentence = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (sentence : Slice Std.U8)
        (hlen_lo : 1 ≤ sentence.val.length) (hlen_hi : sentence.val.length ≤ 500)
        (hbytes : ∀ b ∈ sentence.val, isSpace b ∨ isLetter b)
        (hfirst : ¬ isSpace (byteAt sentence.val 0))
        (hlast : ¬ isSpace (byteAt sentence.val (sentence.val.length - 1)))
        (hnospaces : ∀ i, i + 1 < sentence.val.length →
          ¬ (isSpace (byteAt sentence.val i) ∧ isSpace (byteAt sentence.val (i + 1)))), ∃ r, is_circular_sentence sentence = ok r) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then sentence[0] = sentence[len(sentence)-1].
    Preconditions: len(sentence) is between 1 and 500 inclusive; every byte of sentence is either the space byte 32, an uppercase ASCII letter (65..90), or a lowercase ASCII letter (97..122); sentence[0] != 32 and sentence[len(sentence)-1] != 32; there are no two consecutive space bytes (for every i with 0 <= i < len(sentence)-1, not (sentence[i] = 32 and sentence[i+1] = 32)). -/
  theorem spec_3 (sentence : Slice Std.U8)
      (hlen_lo : 1 ≤ sentence.val.length) (hlen_hi : sentence.val.length ≤ 500)
      (hbytes : ∀ b ∈ sentence.val, isSpace b ∨ isLetter b)
      (hfirst : ¬ isSpace (byteAt sentence.val 0))
      (hlast : ¬ isSpace (byteAt sentence.val (sentence.val.length - 1)))
      (hnospaces : ∀ i, i + 1 < sentence.val.length →
        ¬ (isSpace (byteAt sentence.val i) ∧ isSpace (byteAt sentence.val (i + 1)))) :
      ∀ r, is_circular_sentence sentence = ok r → r = true →
        byteAt sentence.val 0 = byteAt sentence.val (sentence.val.length - 1) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (sentence : Slice Std.U8)
        (hlen_lo : 1 ≤ sentence.val.length) (hlen_hi : sentence.val.length ≤ 500)
        (hbytes : ∀ b ∈ sentence.val, isSpace b ∨ isLetter b)
        (hfirst : ¬ isSpace (byteAt sentence.val 0))
        (hlast : ¬ isSpace (byteAt sentence.val (sentence.val.length - 1)))
        (hnospaces : ∀ i, i + 1 < sentence.val.length →
          ¬ (isSpace (byteAt sentence.val i) ∧ isSpace (byteAt sentence.val (i + 1)))), ∀ r, is_circular_sentence sentence = ok r → r = true →
          byteAt sentence.val 0 = byteAt sentence.val (sentence.val.length - 1)) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then for every index i with 0 < i < len(sentence)-1 and sentence[i] = 32, sentence[i-1] = sentence[i+1].
    Preconditions: len(sentence) is between 1 and 500 inclusive; every byte of sentence is either the space byte 32, an uppercase ASCII letter (65..90), or a lowercase ASCII letter (97..122); sentence[0] != 32 and sentence[len(sentence)-1] != 32; there are no two consecutive space bytes (for every i with 0 <= i < len(sentence)-1, not (sentence[i] = 32 and sentence[i+1] = 32)). -/
  theorem spec_4 (sentence : Slice Std.U8)
      (hlen_lo : 1 ≤ sentence.val.length) (hlen_hi : sentence.val.length ≤ 500)
      (hbytes : ∀ b ∈ sentence.val, isSpace b ∨ isLetter b)
      (hfirst : ¬ isSpace (byteAt sentence.val 0))
      (hlast : ¬ isSpace (byteAt sentence.val (sentence.val.length - 1)))
      (hnospaces : ∀ i, i + 1 < sentence.val.length →
        ¬ (isSpace (byteAt sentence.val i) ∧ isSpace (byteAt sentence.val (i + 1)))) :
      ∀ r, is_circular_sentence sentence = ok r → r = true →
        ∀ i, 0 < i → i < sentence.val.length - 1 → isSpace (byteAt sentence.val i) →
          byteAt sentence.val (i - 1) = byteAt sentence.val (i + 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (sentence : Slice Std.U8)
        (hlen_lo : 1 ≤ sentence.val.length) (hlen_hi : sentence.val.length ≤ 500)
        (hbytes : ∀ b ∈ sentence.val, isSpace b ∨ isLetter b)
        (hfirst : ¬ isSpace (byteAt sentence.val 0))
        (hlast : ¬ isSpace (byteAt sentence.val (sentence.val.length - 1)))
        (hnospaces : ∀ i, i + 1 < sentence.val.length →
          ¬ (isSpace (byteAt sentence.val i) ∧ isSpace (byteAt sentence.val (i + 1)))), ∀ r, is_circular_sentence sentence = ok r → r = true →
          ∀ i, 0 < i → i < sentence.val.length - 1 → isSpace (byteAt sentence.val i) →
            byteAt sentence.val (i - 1) = byteAt sentence.val (i + 1)) := by
    sorry

  /-- Whenever the function returns a result r, if sentence[0] = sentence[len(sentence)-1] and for every index i with 0 < i < len(sentence)-1 and sentence[i] = 32 we have sentence[i-1] = sentence[i+1], then r = true.
    Preconditions: len(sentence) is between 1 and 500 inclusive; every byte of sentence is either the space byte 32, an uppercase ASCII letter (65..90), or a lowercase ASCII letter (97..122); sentence[0] != 32 and sentence[len(sentence)-1] != 32; there are no two consecutive space bytes (for every i with 0 <= i < len(sentence)-1, not (sentence[i] = 32 and sentence[i+1] = 32)). -/
  theorem spec_5 (sentence : Slice Std.U8)
      (hlen_lo : 1 ≤ sentence.val.length) (hlen_hi : sentence.val.length ≤ 500)
      (hbytes : ∀ b ∈ sentence.val, isSpace b ∨ isLetter b)
      (hfirst : ¬ isSpace (byteAt sentence.val 0))
      (hlast : ¬ isSpace (byteAt sentence.val (sentence.val.length - 1)))
      (hnospaces : ∀ i, i + 1 < sentence.val.length →
        ¬ (isSpace (byteAt sentence.val i) ∧ isSpace (byteAt sentence.val (i + 1)))) :
      ∀ r, is_circular_sentence sentence = ok r →
        byteAt sentence.val 0 = byteAt sentence.val (sentence.val.length - 1) →
        (∀ i, 0 < i → i < sentence.val.length - 1 → isSpace (byteAt sentence.val i) →
          byteAt sentence.val (i - 1) = byteAt sentence.val (i + 1)) →
        r = true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (sentence : Slice Std.U8)
        (hlen_lo : 1 ≤ sentence.val.length) (hlen_hi : sentence.val.length ≤ 500)
        (hbytes : ∀ b ∈ sentence.val, isSpace b ∨ isLetter b)
        (hfirst : ¬ isSpace (byteAt sentence.val 0))
        (hlast : ¬ isSpace (byteAt sentence.val (sentence.val.length - 1)))
        (hnospaces : ∀ i, i + 1 < sentence.val.length →
          ¬ (isSpace (byteAt sentence.val i) ∧ isSpace (byteAt sentence.val (i + 1)))), ∀ r, is_circular_sentence sentence = ok r →
          byteAt sentence.val 0 = byteAt sentence.val (sentence.val.length - 1) →
          (∀ i, 0 < i → i < sentence.val.length - 1 → isSpace (byteAt sentence.val i) →
            byteAt sentence.val (i - 1) = byteAt sentence.val (i + 1)) →
          r = true) := by
    sorry

  /-- Whenever the function returns a result r, if r = false then either sentence[0] != sentence[len(sentence)-1] or there exists an index i with 0 < i < len(sentence)-1 and sentence[i] = 32 and sentence[i-1] != sentence[i+1].
    Preconditions: len(sentence) is between 1 and 500 inclusive; every byte of sentence is either the space byte 32, an uppercase ASCII letter (65..90), or a lowercase ASCII letter (97..122); sentence[0] != 32 and sentence[len(sentence)-1] != 32; there are no two consecutive space bytes (for every i with 0 <= i < len(sentence)-1, not (sentence[i] = 32 and sentence[i+1] = 32)). -/
  theorem spec_6 (sentence : Slice Std.U8)
      (hlen_lo : 1 ≤ sentence.val.length) (hlen_hi : sentence.val.length ≤ 500)
      (hbytes : ∀ b ∈ sentence.val, isSpace b ∨ isLetter b)
      (hfirst : ¬ isSpace (byteAt sentence.val 0))
      (hlast : ¬ isSpace (byteAt sentence.val (sentence.val.length - 1)))
      (hnospaces : ∀ i, i + 1 < sentence.val.length →
        ¬ (isSpace (byteAt sentence.val i) ∧ isSpace (byteAt sentence.val (i + 1)))) :
      ∀ r, is_circular_sentence sentence = ok r → r = false →
        byteAt sentence.val 0 ≠ byteAt sentence.val (sentence.val.length - 1) ∨
          ∃ i, 0 < i ∧ i < sentence.val.length - 1 ∧ isSpace (byteAt sentence.val i) ∧
            byteAt sentence.val (i - 1) ≠ byteAt sentence.val (i + 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (sentence : Slice Std.U8)
        (hlen_lo : 1 ≤ sentence.val.length) (hlen_hi : sentence.val.length ≤ 500)
        (hbytes : ∀ b ∈ sentence.val, isSpace b ∨ isLetter b)
        (hfirst : ¬ isSpace (byteAt sentence.val 0))
        (hlast : ¬ isSpace (byteAt sentence.val (sentence.val.length - 1)))
        (hnospaces : ∀ i, i + 1 < sentence.val.length →
          ¬ (isSpace (byteAt sentence.val i) ∧ isSpace (byteAt sentence.val (i + 1)))), ∀ r, is_circular_sentence sentence = ok r → r = false →
          byteAt sentence.val 0 ≠ byteAt sentence.val (sentence.val.length - 1) ∨
            ∃ i, 0 < i ∧ i < sentence.val.length - 1 ∧ isSpace (byteAt sentence.val i) ∧
              byteAt sentence.val (i - 1) ≠ byteAt sentence.val (i + 1)) := by
    sorry

  /-- Whenever the function returns a result r, if there exists a byte c such that for every maximal contiguous non-space block (word) in sentence, its first byte and its last byte are both equal to c, then r = true.
    Preconditions: len(sentence) is between 1 and 500 inclusive; every byte of sentence is either the space byte 32, an uppercase ASCII letter (65..90), or a lowercase ASCII letter (97..122); sentence[0] != 32 and sentence[len(sentence)-1] != 32; there are no two consecutive space bytes (for every i with 0 <= i < len(sentence)-1, not (sentence[i] = 32 and sentence[i+1] = 32)). -/
  theorem spec_7 (sentence : Slice Std.U8)
      (hlen_lo : 1 ≤ sentence.val.length) (hlen_hi : sentence.val.length ≤ 500)
      (hbytes : ∀ b ∈ sentence.val, isSpace b ∨ isLetter b)
      (hfirst : ¬ isSpace (byteAt sentence.val 0))
      (hlast : ¬ isSpace (byteAt sentence.val (sentence.val.length - 1)))
      (hnospaces : ∀ i, i + 1 < sentence.val.length →
        ¬ (isSpace (byteAt sentence.val i) ∧ isSpace (byteAt sentence.val (i + 1)))) :
      ∀ r, is_circular_sentence sentence = ok r →
        (∃ c, ∀ j, j < numWords sentence.val →
          byteAt sentence.val (firstIdx sentence.val j) = c ∧
            byteAt sentence.val (lastIdx sentence.val j) = c) →
        r = true := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (sentence : Slice Std.U8)
        (hlen_lo : 1 ≤ sentence.val.length) (hlen_hi : sentence.val.length ≤ 500)
        (hbytes : ∀ b ∈ sentence.val, isSpace b ∨ isLetter b)
        (hfirst : ¬ isSpace (byteAt sentence.val 0))
        (hlast : ¬ isSpace (byteAt sentence.val (sentence.val.length - 1)))
        (hnospaces : ∀ i, i + 1 < sentence.val.length →
          ¬ (isSpace (byteAt sentence.val i) ∧ isSpace (byteAt sentence.val (i + 1)))), ∀ r, is_circular_sentence sentence = ok r →
          (∃ c, ∀ j, j < numWords sentence.val →
            byteAt sentence.val (firstIdx sentence.val j) = c ∧
              byteAt sentence.val (lastIdx sentence.val j) = c) →
          r = true) := by
    sorry

  /-- For any byte slices s and t satisfying the preconditions, let n_s and n_t be their numbers of maximal contiguous non-space blocks (words). If n_s = n_t = n and for every j with 0 <= j < n the first byte of the j-th word of s equals the first byte of the j-th word of t and the last byte of the j-th word of s equals the last byte of the j-th word of t, then whenever is_circular_sentence(s) returns r_s and is_circular_sentence(t) returns r_t, r_s = r_t.
    Preconditions: Both s and t are byte slices satisfying the valid-sentence preconditions: 1 <= len(s) <= 500 and 1 <= len(t) <= 500; every byte of s and t is either the space byte 32, an uppercase ASCII letter (65..90), or a lowercase ASCII letter (97..122); s[0] != 32, s[len(s)-1] != 32, t[0] != 32, t[len(t)-1] != 32; there are no two consecutive space bytes in s or in t. -/
  theorem spec_8 (s t : Slice Std.U8)
      (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 500)
      (ht_len_lo : 1 ≤ t.val.length) (ht_len_hi : t.val.length ≤ 500)
      (hs_bytes : ∀ b ∈ s.val, isSpace b ∨ isLetter b)
      (ht_bytes : ∀ b ∈ t.val, isSpace b ∨ isLetter b)
      (hs_first : ¬ isSpace (byteAt s.val 0))
      (hs_last : ¬ isSpace (byteAt s.val (s.val.length - 1)))
      (ht_first : ¬ isSpace (byteAt t.val 0))
      (ht_last : ¬ isSpace (byteAt t.val (t.val.length - 1)))
      (hs_nospaces : ∀ i, i + 1 < s.val.length →
        ¬ (isSpace (byteAt s.val i) ∧ isSpace (byteAt s.val (i + 1))))
      (ht_nospaces : ∀ i, i + 1 < t.val.length →
        ¬ (isSpace (byteAt t.val i) ∧ isSpace (byteAt t.val (i + 1))))
      (hn : numWords s.val = numWords t.val)
      (hwords_first : ∀ j, j < numWords s.val →
        byteAt s.val (firstIdx s.val j) = byteAt t.val (firstIdx t.val j))
      (hwords_last : ∀ j, j < numWords s.val →
        byteAt s.val (lastIdx s.val j) = byteAt t.val (lastIdx t.val j)) :
      ∀ r_s r_t, is_circular_sentence s = ok r_s → is_circular_sentence t = ok r_t →
        r_s = r_t := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hs_len_lo : 1 ≤ s.val.length) (hs_len_hi : s.val.length ≤ 500)
        (ht_len_lo : 1 ≤ t.val.length) (ht_len_hi : t.val.length ≤ 500)
        (hs_bytes : ∀ b ∈ s.val, isSpace b ∨ isLetter b)
        (ht_bytes : ∀ b ∈ t.val, isSpace b ∨ isLetter b)
        (hs_first : ¬ isSpace (byteAt s.val 0))
        (hs_last : ¬ isSpace (byteAt s.val (s.val.length - 1)))
        (ht_first : ¬ isSpace (byteAt t.val 0))
        (ht_last : ¬ isSpace (byteAt t.val (t.val.length - 1)))
        (hs_nospaces : ∀ i, i + 1 < s.val.length →
          ¬ (isSpace (byteAt s.val i) ∧ isSpace (byteAt s.val (i + 1))))
        (ht_nospaces : ∀ i, i + 1 < t.val.length →
          ¬ (isSpace (byteAt t.val i) ∧ isSpace (byteAt t.val (i + 1))))
        (hn : numWords s.val = numWords t.val)
        (hwords_first : ∀ j, j < numWords s.val →
          byteAt s.val (firstIdx s.val j) = byteAt t.val (firstIdx t.val j))
        (hwords_last : ∀ j, j < numWords s.val →
          byteAt s.val (lastIdx s.val j) = byteAt t.val (lastIdx t.val j)), ∀ r_s r_t, is_circular_sentence s = ok r_s → is_circular_sentence t = ok r_t →
          r_s = r_t) := by
    sorry

  end AegisSpec.IsCircularSentence
