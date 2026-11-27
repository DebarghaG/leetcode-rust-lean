import Aegis.MaximumLengthSubstring.Code.Funs

/-!
# Specifications of `Aegis.MaximumLengthSubstring.maximum_length_substring`

LeetCode problem `maximum-length-substring-with-two-occurrences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumLengthSubstring

  open Aegis.MaximumLengthSubstring (maximum_length_substring)

  def slen (s : Slice Std.U8) : Nat := s.val.length

  def byteAt (s : Slice Std.U8) (k : Nat) : Nat := (s.val.getD k 0#u8).val

  def countByte (s : Slice Std.U8) (i j c : Nat) : Nat :=
    ((s.val.drop i).take (j - i)).countP (fun x => decide (x.val = c))

  def allowed (s : Slice Std.U8) (i j : Nat) : Prop := ∀ c : Nat, countByte s i j c ≤ 2

  def asciiLower (s : Slice Std.U8) : Prop :=
    ∀ k : Nat, k < slen s → 97 ≤ byteAt s k ∧ byteAt s k ≤ 122

  def allEqual (s : Slice Std.U8) : Prop := ∃ b : Nat, ∀ k : Nat, k < slen s → byteAt s k = b

  def distinctCount (s : Slice Std.U8) : Nat := (s.val.map (fun x => x.val)).dedup.length

  def windowLen (i j : Nat) : Int := (j : Int) - (i : Int)

  lemma byteAt_eq_getElem (s : Slice Std.U8) (k : Nat) (h : k < slen s) :
      byteAt s k = (s.val.get ⟨k, by simpa [slen] using h⟩).val := by
    simp [byteAt, slen] at h ⊢
    rw [List.getElem?_eq_getElem h]
    rfl

  lemma allowed_self (s : Slice Std.U8) (i : Nat) : allowed s i i := by
    intro c
    simp [countByte]

  /-- The function returns a result r and r is the maximum length of a contiguous substring of s in which every byte occurs at most twice. Equivalently: (a) for every i and j with 0 <= i <= j <= len(s), if for every byte value c the number of indices k with i <= k < j and s[k] = c is at most 2, then j - i <= r; and (b) there exist i and j with 0 <= i <= j <= len(s) such that j - i = r and for every byte value c the number of indices k with i <= k < j and s[k] = c is at most 2.
    Preconditions: len(s) is an integer with 2 <= len(s) <= 100, and for every k with 0 <= k < len(s), s[k] is an ASCII code of a lowercase English letter (97 <= s[k] <= 122). -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s) :
      ∃ r : Std.I64, maximum_length_substring s = ok r ∧
        (∀ i j : Nat, i ≤ j → j ≤ slen s → allowed s i j → windowLen i j ≤ r.val) ∧
        (∃ i j : Nat, i ≤ j ∧ j ≤ slen s ∧ windowLen i j = r.val ∧ allowed s i j) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s), ∃ r : Std.I64, maximum_length_substring s = ok r ∧
          (∀ i j : Nat, i ≤ j → j ≤ slen s → allowed s i j → windowLen i j ≤ r.val) ∧
          (∃ i j : Nat, i ≤ j ∧ j ≤ slen s ∧ windowLen i j = r.val ∧ allowed s i j)) := by
    sorry

  /-- The function returns a result r; it does not panic, overflow, or access out of bounds.
    Preconditions: len(s) is an integer with 2 <= len(s) <= 100, and for every k with 0 <= k < len(s), s[k] is an ASCII code of a lowercase English letter (97 <= s[k] <= 122). -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s) :
      ∃ r : Std.I64, maximum_length_substring s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s), ∃ r : Std.I64, maximum_length_substring s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 2 <= r <= len(s).
    Preconditions: len(s) is an integer with 2 <= len(s) <= 100, and for every k with 0 <= k < len(s), s[k] is an ASCII code of a lowercase English letter (97 <= s[k] <= 122). -/
  theorem spec_3 (s : Slice Std.U8)
      (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
      (r : Std.I64) (hr : maximum_length_substring s = ok r) :
      2 ≤ r.val ∧ r.val ≤ (slen s : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
        (r : Std.I64) (hr : maximum_length_substring s = ok r), 2 ≤ r.val ∧ r.val ≤ (slen s : Int)) := by
    sorry

  /-- Whenever the function returns a result r, there exist integers i and j such that 0 <= i <= j <= len(s), j - i = r, and for every byte value c the number of indices k with i <= k < j and s[k] = c is at most 2.
    Preconditions: len(s) is an integer with 2 <= len(s) <= 100, and for every k with 0 <= k < len(s), s[k] is an ASCII code of a lowercase English letter (97 <= s[k] <= 122). -/
  theorem spec_4 (s : Slice Std.U8)
      (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
      (r : Std.I64) (hr : maximum_length_substring s = ok r) :
      ∃ i j : Nat, i ≤ j ∧ j ≤ slen s ∧ windowLen i j = r.val ∧ allowed s i j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
        (r : Std.I64) (hr : maximum_length_substring s = ok r), ∃ i j : Nat, i ≤ j ∧ j ≤ slen s ∧ windowLen i j = r.val ∧ allowed s i j) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i <= j <= len(s), if for every byte value c the number of indices k with i <= k < j and s[k] = c is at most 2, then j - i <= r.
    Preconditions: len(s) is an integer with 2 <= len(s) <= 100, and for every k with 0 <= k < len(s), s[k] is an ASCII code of a lowercase English letter (97 <= s[k] <= 122). -/
  theorem spec_5 (s : Slice Std.U8)
      (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
      (r : Std.I64) (hr : maximum_length_substring s = ok r) :
      ∀ i j : Nat, i ≤ j → j ≤ slen s → allowed s i j → windowLen i j ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
        (r : Std.I64) (hr : maximum_length_substring s = ok r), ∀ i j : Nat, i ≤ j → j ≤ slen s → allowed s i j → windowLen i j ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = len(s) if and only if for every byte value c the number of indices k with 0 <= k < len(s) and s[k] = c is at most 2.
    Preconditions: len(s) is an integer with 2 <= len(s) <= 100, and for every k with 0 <= k < len(s), s[k] is an ASCII code of a lowercase English letter (97 <= s[k] <= 122). -/
  theorem spec_6 (s : Slice Std.U8)
      (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
      (r : Std.I64) (hr : maximum_length_substring s = ok r) :
      r.val = (slen s : Int) ↔ allowed s 0 (slen s) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
        (r : Std.I64) (hr : maximum_length_substring s = ok r), r.val = (slen s : Int) ↔ allowed s 0 (slen s)) := by
    sorry

  /-- Whenever the function returns a result r, if all entries of s are equal, that is, there exists a byte b such that s[k] = b for every k with 0 <= k < len(s), then r = 2.
    Preconditions: len(s) is an integer with 2 <= len(s) <= 100, and for every k with 0 <= k < len(s), s[k] is an ASCII code of a lowercase English letter (97 <= s[k] <= 122). -/
  theorem spec_7 (s : Slice Std.U8)
      (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
      (r : Std.I64) (hr : maximum_length_substring s = ok r) :
      allEqual s → r.val = 2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
        (r : Std.I64) (hr : maximum_length_substring s = ok r), allEqual s → r.val = 2) := by
    sorry

  /-- Whenever the function returns a result r, if there exists a byte value c such that the number of indices k with 0 <= k < len(s) and s[k] = c is at least 3, then r < len(s).
    Preconditions: len(s) is an integer with 2 <= len(s) <= 100, and for every k with 0 <= k < len(s), s[k] is an ASCII code of a lowercase English letter (97 <= s[k] <= 122). -/
  theorem spec_8 (s : Slice Std.U8)
      (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
      (r : Std.I64) (hr : maximum_length_substring s = ok r) :
      (∃ c : Nat, 3 ≤ countByte s 0 (slen s) c) → r.val < (slen s : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
        (r : Std.I64) (hr : maximum_length_substring s = ok r), (∃ c : Nat, 3 ≤ countByte s 0 (slen s) c) → r.val < (slen s : Int)) := by
    sorry

  /-- Let t be the byte slice of length len(s) defined by t[k] = s[len(s) - 1 - k] for every 0 <= k < len(s). If the function called on s returns r and the function called on t returns r_t, then r = r_t.
    Preconditions: len(s) is an integer with 2 <= len(s) <= 100, and for every k with 0 <= k < len(s), s[k] is an ASCII code of a lowercase English letter (97 <= s[k] <= 122). -/
  theorem spec_9 (s t : Slice Std.U8)
      (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
      (htlen : slen t = slen s)
      (htrev : ∀ k : Nat, k < slen s → byteAt t k = byteAt s (slen s - 1 - k))
      (r r_t : Std.I64)
      (hr : maximum_length_substring s = ok r) (hr_t : maximum_length_substring t = ok r_t) :
      r = r_t := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
        (htlen : slen t = slen s)
        (htrev : ∀ k : Nat, k < slen s → byteAt t k = byteAt s (slen s - 1 - k))
        (r r_t : Std.I64)
        (hr : maximum_length_substring s = ok r) (hr_t : maximum_length_substring t = ok r_t), r = r_t) := by
    sorry

  /-- Whenever the function returns a result r, if len(s) > 2 and r = 2, then all entries of s are equal.
    Preconditions: len(s) is an integer with 2 <= len(s) <= 100, and for every k with 0 <= k < len(s), s[k] is an ASCII code of a lowercase English letter (97 <= s[k] <= 122). -/
  theorem spec_10 (s : Slice Std.U8)
      (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
      (r : Std.I64) (hr : maximum_length_substring s = ok r) :
      2 < slen s → r.val = 2 → allEqual s := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
        (r : Std.I64) (hr : maximum_length_substring s = ok r), 2 < slen s → r.val = 2 → allEqual s) := by
    sorry

  /-- Let t be any byte slice of length len(s) such that t also has length between 2 and 100, all entries of t are ASCII lowercase letters, and s and t have the same equality pattern: for all i and j with 0 <= i,j < len(s), s[i] = s[j] if and only if t[i] = t[j]. If the function called on s returns r_s and the function called on t returns r_t, then r_s = r_t.
    Preconditions: len(s) is an integer with 2 <= len(s) <= 100, and for every k with 0 <= k < len(s), s[k] is an ASCII code of a lowercase English letter (97 <= s[k] <= 122). -/
  theorem spec_11 (s t : Slice Std.U8)
      (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
      (htlen : slen t = slen s) (htbytes : asciiLower t)
      (hpat : ∀ i j : Nat, i < slen s → j < slen s →
        (byteAt s i = byteAt s j ↔ byteAt t i = byteAt t j))
      (r_s r_t : Std.I64)
      (hr_s : maximum_length_substring s = ok r_s) (hr_t : maximum_length_substring t = ok r_t) :
      r_s = r_t := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
        (htlen : slen t = slen s) (htbytes : asciiLower t)
        (hpat : ∀ i j : Nat, i < slen s → j < slen s →
          (byteAt s i = byteAt s j ↔ byteAt t i = byteAt t j))
        (r_s r_t : Std.I64)
        (hr_s : maximum_length_substring s = ok r_s) (hr_t : maximum_length_substring t = ok r_t), r_s = r_t) := by
    sorry

  /-- Let D be the number of distinct byte values that occur among the entries of s. Whenever the function returns a result r, r <= 2 * D. In particular, since there are at most 26 distinct lowercase letters, r <= 52.
    Preconditions: len(s) is an integer with 2 <= len(s) <= 100, and for every k with 0 <= k < len(s), s[k] is an ASCII code of a lowercase English letter (97 <= s[k] <= 122). -/
  theorem spec_12 (s : Slice Std.U8)
      (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
      (r : Std.I64) (hr : maximum_length_substring s = ok r) :
      r.val ≤ 2 * (distinctCount s : Int) ∧ r.val ≤ 52 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
        (r : Std.I64) (hr : maximum_length_substring s = ok r), r.val ≤ 2 * (distinctCount s : Int) ∧ r.val ≤ 52) := by
    sorry

  /-- If the function called on s returns r_s and the function called on t returns r_t, then r_t <= r_s. Equivalently, taking a contiguous substring cannot increase the maximum admissible length.
    Preconditions: Let s satisfy: len(s) is an integer with 2 <= len(s) <= 100, and for every k with 0 <= k < len(s), s[k] is an ASCII code of a lowercase English letter (97 <= s[k] <= 122). Let i and j be integers with 0 <= i <= j <= len(s) and j - i >= 2, and let t be the slice defined by t[k] = s[i+k] for 0 <= k < j-i. -/
  theorem spec_13 (s t : Slice Std.U8) (i j : Nat)
      (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
      (hi : i ≤ j) (hj : j ≤ slen s) (hlenij : 2 ≤ j - i)
      (htlen : slen t = j - i)
      (ht : ∀ k : Nat, k < j - i → byteAt t k = byteAt s (i + k))
      (r_s r_t : Std.I64)
      (hr_s : maximum_length_substring s = ok r_s) (hr_t : maximum_length_substring t = ok r_t) :
      r_t.val ≤ r_s.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s t : Slice Std.U8) (i j : Nat)
        (hlen : 2 ≤ slen s ∧ slen s ≤ 100) (hbytes : asciiLower s)
        (hi : i ≤ j) (hj : j ≤ slen s) (hlenij : 2 ≤ j - i)
        (htlen : slen t = j - i)
        (ht : ∀ k : Nat, k < j - i → byteAt t k = byteAt s (i + k))
        (r_s r_t : Std.I64)
        (hr_s : maximum_length_substring s = ok r_s) (hr_t : maximum_length_substring t = ok r_t), r_t.val ≤ r_s.val) := by
    sorry

  end AegisSpec.MaximumLengthSubstring
