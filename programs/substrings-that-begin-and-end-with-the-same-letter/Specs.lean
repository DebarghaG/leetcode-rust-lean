import Aegis.NumberOfSubstrings.Code.Funs

/-!
# Specifications of `Aegis.NumberOfSubstrings.number_of_substrings`

LeetCode problem `substrings-that-begin-and-end-with-the-same-letter`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumberOfSubstrings

  def slen (s : Slice U8) : Nat := (Slice.len s).val

  def allLower (s : Slice U8) : Prop := ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122

  def precond (s : Slice U8) : Prop := 1 ≤ slen s ∧ slen s ≤ 100000 ∧ allLower s

  def byteAt (s : Slice U8) (i : Nat) : Option Nat := (s.val[i]?).map (fun b => b.val)

  def occ (s : Slice U8) (c : Nat) : Nat :=
    ((Finset.range (slen s)).filter (fun i => byteAt s i = some c)).card

  def letters (s : Slice U8) : Finset Nat :=
    (Finset.Icc 97 122).filter (fun c => 0 < occ s c)

  def distinctLetters (s : Slice U8) : Nat := (letters s).card

  def triangle (n : Nat) : Nat := n * (n + 1) / 2

  def pairCount (s : Slice U8) : Nat :=
    (((Finset.range (slen s)).product (Finset.range (slen s))).filter
        (fun p : Nat × Nat => p.1 ≤ p.2 ∧ byteAt s p.1 = byteAt s p.2)).card

  def strictPairCount (s : Slice U8) : Nat :=
    (((Finset.range (slen s)).product (Finset.range (slen s))).filter
        (fun p : Nat × Nat => p.1 < p.2 ∧ byteAt s p.1 = byteAt s p.2)).card

  /-- Whenever the function returns a result r, r equals the number of integer pairs (i, j) such that 0 <= i <= j < len(s) and s[i] = s[j]. Each such pair represents the non-empty contiguous substring of s from index i through index j, inclusive; conversely every non-empty contiguous substring has exactly one such pair of endpoints.
    Preconditions: s is a non-empty byte slice with 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122. -/
  theorem spec_1 (s : Slice U8) (hs : precond s) :
      ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
        r.val = (pairCount s : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8) (hs : precond s), ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
          r.val = (pairCount s : Int)) := by
    sorry

  /-- For every input s satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow the i64 result.
    Preconditions: s is a non-empty byte slice with 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122. -/
  theorem spec_2 (s : Slice U8) (hs : precond s) :
      ∃ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8) (hs : precond s), ∃ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r <= len(s) * (len(s) + 1) / 2.
    Preconditions: s is a non-empty byte slice with 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122. -/
  theorem spec_3 (s : Slice U8) (hs : precond s) :
      ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
        r.val ≤ (triangle (slen s) : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8) (hs : precond s), ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
          r.val ≤ (triangle (slen s) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, len(s) <= r.
    Preconditions: s is a non-empty byte slice with 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122. -/
  theorem spec_4 (s : Slice U8) (hs : precond s) :
      ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
        (slen s : Int) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8) (hs : precond s), ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
          (slen s : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, let occ(c) be the number of indices i with 0 <= i < len(s) and s[i] = c. Then r = sum over c from 97 to 122 of occ(c) * (occ(c) + 1) / 2.
    Preconditions: s is a non-empty byte slice with 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122. -/
  theorem spec_5 (s : Slice U8) (hs : precond s) :
      ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
        r.val = ((((Finset.Icc 97 122).sum (fun c => triangle (occ s c)) : Nat)) : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8) (hs : precond s), ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
          r.val = ((((Finset.Icc 97 122).sum (fun c => triangle (occ s c)) : Nat)) : Int)) := by
    sorry

  /-- If len(s) = 1, then whenever the function returns a result r, r = 1.
    Preconditions: s is a non-empty byte slice with 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122. -/
  theorem spec_6 (s : Slice U8) (hs : precond s) (h1 : slen s = 1) :
      ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r → r.val = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice U8) (hs : precond s) (h1 : slen s = 1), ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r → r.val = 1) := by
    sorry

  /-- If there is a byte c with 97 <= c <= 122 such that s[i] = c for every i with 0 <= i < len(s), then whenever the function returns a result r, r = len(s) * (len(s) + 1) / 2.
    Preconditions: s is a non-empty byte slice with 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122. -/
  theorem spec_7 (s : Slice U8) (hs : precond s)
      (hc : ∃ c : U8, 97 ≤ c.val ∧ c.val ≤ 122 ∧ ∀ i, i < slen s → byteAt s i = some c.val) :
      ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
        r.val = (triangle (slen s) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice U8) (hs : precond s)
        (hc : ∃ c : U8, 97 ≤ c.val ∧ c.val ≤ 122 ∧ ∀ i, i < slen s → byteAt s i = some c.val), ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
          r.val = (triangle (slen s) : Int)) := by
    sorry

  /-- If s[i] != s[j] for every pair i, j with 0 <= i < j < len(s), then whenever the function returns a result r, r = len(s).
    Preconditions: s is a non-empty byte slice with 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122. -/
  theorem spec_8 (s : Slice U8) (hs : precond s)
      (hne : ∀ i j, i < j → j < slen s → byteAt s i ≠ byteAt s j) :
      ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
        r.val = (slen s : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice U8) (hs : precond s)
        (hne : ∀ i j, i < j → j < slen s → byteAt s i ≠ byteAt s j), ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
          r.val = (slen s : Int)) := by
    sorry

  /-- Whenever the function returns a result r on input s and a result r' on input t, r' = r + occ_s(c) + 1, where occ_s(c) is the number of indices i with 0 <= i < len(s) and s[i] = c.
    Preconditions: s is a non-empty byte slice with 1 <= len(s) < 100000, every s[i] with 0 <= i < len(s) is an ASCII lowercase letter, and c is a byte with 97 <= c <= 122. Let t be the byte slice of length len(s)+1 with t[i]=s[i] for 0 <= i < len(s) and t[len(s)]=c. -/
  theorem spec_9 (s t : Slice U8) (c : U8)
      (hs : 1 ≤ slen s ∧ slen s < 100000 ∧ allLower s)
      (hc : 97 ≤ c.val ∧ c.val ≤ 122)
      (htlen : slen t = slen s + 1)
      (ht : ∀ k, k < slen s → byteAt t k = byteAt s k)
      (htlast : byteAt t (slen s) = some c.val) :
      ∀ r r', Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
        Aegis.NumberOfSubstrings.number_of_substrings t = ok r' →
        r'.val = r.val + (occ s c.val : Int) + 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s t : Slice U8) (c : U8)
        (hs : 1 ≤ slen s ∧ slen s < 100000 ∧ allLower s)
        (hc : 97 ≤ c.val ∧ c.val ≤ 122)
        (htlen : slen t = slen s + 1)
        (ht : ∀ k, k < slen s → byteAt t k = byteAt s k)
        (htlast : byteAt t (slen s) = some c.val), ∀ r r', Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
          Aegis.NumberOfSubstrings.number_of_substrings t = ok r' →
          r'.val = r.val + (occ s c.val : Int) + 1) := by
    sorry

  /-- Whenever the function returns a result r_s on input s and a result r_t on input t, r_s = r_t.
    Preconditions: s and t are non-empty byte slices with lengths between 1 and 100000, all their bytes are ASCII lowercase letters, and for every c with 97 <= c <= 122, the number of indices i with s[i]=c equals the number of indices j with t[j]=c. -/
  theorem spec_10 (s t : Slice U8) (hs : precond s) (ht : precond t)
      (hocc : ∀ c, 97 ≤ c → c ≤ 122 → occ s c = occ t c) :
      ∀ rs rt, Aegis.NumberOfSubstrings.number_of_substrings s = ok rs →
        Aegis.NumberOfSubstrings.number_of_substrings t = ok rt → rs.val = rt.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s t : Slice U8) (hs : precond s) (ht : precond t)
        (hocc : ∀ c, 97 ≤ c → c ≤ 122 → occ s c = occ t c), ∀ rs rt, Aegis.NumberOfSubstrings.number_of_substrings s = ok rs →
          Aegis.NumberOfSubstrings.number_of_substrings t = ok rt → rs.val = rt.val) := by
    sorry

  /-- If there exist indices i and j with 0 <= i < j < len(s) and s[i] = s[j], then whenever the function returns a result r, len(s) + 1 <= r.
    Preconditions: s is a non-empty byte slice with 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122. -/
  theorem spec_11 (s : Slice U8) (hs : precond s)
      (h : ∃ i j, i < j ∧ j < slen s ∧ byteAt s i = byteAt s j) :
      ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
        (slen s : Int) + 1 ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice U8) (hs : precond s)
        (h : ∃ i j, i < j ∧ j < slen s ∧ byteAt s i = byteAt s j), ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
          (slen s : Int) + 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r on input s and a result r' on input t, r = r'.
    Preconditions: s is a non-empty byte slice with 1 <= len(s) <= 100000, and every byte of s is an ASCII lowercase letter. Let t be the reversal of s, i.e. len(t)=len(s) and t[k]=s[len(s)-1-k] for every 0 <= k < len(s). -/
  theorem spec_12 (s t : Slice U8) (hs : precond s)
      (htlen : slen t = slen s)
      (ht : ∀ k, k < slen s → byteAt t k = byteAt s (slen s - 1 - k)) :
      ∀ r r', Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
        Aegis.NumberOfSubstrings.number_of_substrings t = ok r' → r.val = r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s t : Slice U8) (hs : precond s)
        (htlen : slen t = slen s)
        (ht : ∀ k, k < slen s → byteAt t k = byteAt s (slen s - 1 - k)), ∀ r r', Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
          Aegis.NumberOfSubstrings.number_of_substrings t = ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever the function returns a result r on input s and a result r_u on input u, r_u <= r.
    Preconditions: s and u are non-empty byte slices with lengths between 1 and 100000, all their bytes are ASCII lowercase letters, and there exist 0 <= a <= b < len(s) such that len(u) = b - a + 1 and u[k] = s[a + k] for every 0 <= k < len(u). -/
  theorem spec_13 (s u : Slice U8) (hs : precond s) (hu : precond u)
      (hab : ∃ a b, a ≤ b ∧ b < slen s ∧ slen u = b - a + 1 ∧
        ∀ k, k < slen u → byteAt u k = byteAt s (a + k)) :
      ∀ r ru, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
        Aegis.NumberOfSubstrings.number_of_substrings u = ok ru → ru.val ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s u : Slice U8) (hs : precond s) (hu : precond u)
        (hab : ∃ a b, a ≤ b ∧ b < slen s ∧ slen u = b - a + 1 ∧
          ∀ k, k < slen u → byteAt u k = byteAt s (a + k)), ∀ r ru, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
          Aegis.NumberOfSubstrings.number_of_substrings u = ok ru → ru.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r - len(s) equals the number of pairs (i, j) with 0 <= i < j < len(s) and s[i] = s[j]; i.e. the excess over len(s) counts exactly the qualifying substrings of length at least 2.
    Preconditions: s is a non-empty byte slice with 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122. -/
  theorem spec_14 (s : Slice U8) (hs : precond s) :
      ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
        r.val - (slen s : Int) = (strictPairCount s : Int) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s : Slice U8) (hs : precond s), ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
          r.val - (slen s : Int) = (strictPairCount s : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r >= 2 * len(s) - d, where d is the number of distinct bytes c with 97 <= c <= 122 for which s[i] = c for some i with 0 <= i < len(s).
    Preconditions: s is a non-empty byte slice with 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122. -/
  theorem spec_15 (s : Slice U8) (hs : precond s) :
      ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
        ((2 * slen s - distinctLetters s : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (s : Slice U8) (hs : precond s), ∀ r, Aegis.NumberOfSubstrings.number_of_substrings s = ok r →
          ((2 * slen s - distinctLetters s : Nat) : Int) ≤ r.val) := by
    sorry

  end AegisSpec.NumberOfSubstrings
