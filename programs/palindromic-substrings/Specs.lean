import Aegis.CountSubstrings.Code.Funs

/-!
# Specifications of `Aegis.CountSubstrings.count_substrings`

LeetCode problem `palindromic-substrings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountSubstrings

def bytes (s : Slice U8) : List ℕ := s.list.toList.map (fun b => b.val)

def byteAt (s : Slice U8) (i : ℕ) : ℕ := (bytes s).getD i 0

theorem bytes_length (s : Slice U8) : (bytes s).length = s.leng := by
  simp [bytes, Aeneas.Data.ListN.ListN_length]

@[reducible] def IsPal (L : List ℕ) (i j : ℕ) : Prop :=
  ∀ k ∈ Finset.range (j - i), L.getD (i + k) 0 = L.getD (j - 1 - k) 0

def PalCount (L : List ℕ) (m : ℕ) : ℕ :=
  (((Finset.range (m + 1)) ×ˢ (Finset.range (m + 1))).filter
      (fun p => p.1 < p.2 ∧ IsPal L p.1 p.2)).card

def eqOffsetCount (L : List ℕ) (m d : ℕ) : ℕ :=
  ((Finset.range (m - d)).filter (fun i => L.getD i 0 = L.getD (i + d) 0)).card

def ind (p : Prop) [Decidable p] : ℤ := if p then 1 else 0

/-- count_substrings returns a result r and r is the number of pairs (i, j) of integers such that 0 <= i < j <= n and the substring s[i..j) is a palindrome. Here s[i..j) denotes the contiguous substring of length j - i consisting of s[i], s[i+1], ..., s[j-1], and it is a palindrome iff for every k with 0 <= k < j - i we have s[i + k] = s[j - 1 - k]. Different position intervals are counted separately even if their byte contents are equal.
  Preconditions: Let n = len(s). 1 <= n <= 1000 and for every i with 0 <= i < n, 97 <= s[i] <= 122 (s consists of lowercase English letters). -/
theorem spec_1 (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∃ r, Aegis.CountSubstrings.count_substrings s = ok r ∧
      r.val = (PalCount (bytes s) s.leng : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∃ r, Aegis.CountSubstrings.count_substrings s = ok r ∧
      r.val = (PalCount (bytes s) s.leng : ℤ)) := by
  sorry

/-- For every s satisfying the preconditions, count_substrings s returns a result (it does not fail, panic, overflow, or access out of bounds).
  Preconditions: Let n = len(s). 1 <= n <= 1000 and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_2 (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∃ r, Aegis.CountSubstrings.count_substrings s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∃ r, Aegis.CountSubstrings.count_substrings s = ok r) := by
  sorry

/-- Whenever count_substrings returns a result r, r <= n * (n + 1) / 2, where n = len(s); this is the total number of non-empty contiguous substrings of s.
  Preconditions: Let n = len(s). 1 <= n <= 1000 and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_3 (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r, Aegis.CountSubstrings.count_substrings s = ok r →
      r.val ≤ ((s.leng * (s.leng + 1) / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r, Aegis.CountSubstrings.count_substrings s = ok r →
      r.val ≤ ((s.leng * (s.leng + 1) / 2 : ℕ) : ℤ)) := by
  sorry

/-- Whenever count_substrings returns a result r, r >= n + e1 + e2, where n = len(s), e1 is the number of indices i with 0 <= i < n - 1 and s[i] = s[i + 1], and e2 is the number of indices i with 0 <= i < n - 2 and s[i] = s[i + 2].
  Preconditions: Let n = len(s). 1 <= n <= 1000 and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_4 (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r, Aegis.CountSubstrings.count_substrings s = ok r →
      ((s.leng + eqOffsetCount (bytes s) s.leng 1 + eqOffsetCount (bytes s) s.leng 2 : ℕ) : ℤ)
        ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r, Aegis.CountSubstrings.count_substrings s = ok r →
      ((s.leng + eqOffsetCount (bytes s) s.leng 1 + eqOffsetCount (bytes s) s.leng 2 : ℕ) : ℤ)
        ≤ r.val) := by
  sorry

/-- Whenever count_substrings returns a result r, r = 1 if and only if n = 1.
  Preconditions: Let n = len(s). 1 <= n <= 1000 and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_5 (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r, Aegis.CountSubstrings.count_substrings s = ok r → (r.val = 1 ↔ s.leng = 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r, Aegis.CountSubstrings.count_substrings s = ok r → (r.val = 1 ↔ s.leng = 1)) := by
  sorry

/-- Whenever count_substrings returns a result r, r = 2 + (if s[0] = s[1] then 1 else 0). Equivalently, r = 3 when the two bytes are equal and r = 2 otherwise.
  Preconditions: Let n = len(s). n = 2 and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_6 (s : Slice U8) (hlen : s.leng = 2)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r, Aegis.CountSubstrings.count_substrings s = ok r →
      r.val = 2 + ind (byteAt s 0 = byteAt s 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (hlen : s.leng = 2)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r, Aegis.CountSubstrings.count_substrings s = ok r →
      r.val = 2 + ind (byteAt s 0 = byteAt s 1)) := by
  sorry

/-- Whenever count_substrings returns a result r, r = 3 + I(s[0] = s[1]) + I(s[1] = s[2]) + I(s[0] = s[2]), where I(condition) is 1 if the condition holds and 0 otherwise.
  Preconditions: Let n = len(s). n = 3 and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_7 (s : Slice U8) (hlen : s.leng = 3)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r, Aegis.CountSubstrings.count_substrings s = ok r →
      r.val = 3 + ind (byteAt s 0 = byteAt s 1) + ind (byteAt s 1 = byteAt s 2) +
        ind (byteAt s 0 = byteAt s 2) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (hlen : s.leng = 3)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r, Aegis.CountSubstrings.count_substrings s = ok r →
      r.val = 3 + ind (byteAt s 0 = byteAt s 1) + ind (byteAt s 1 = byteAt s 2) +
        ind (byteAt s 0 = byteAt s 2)) := by
  sorry

/-- Whenever count_substrings returns a result r, r = n * (n + 1) / 2 if and only if for every i with 0 <= i < n, s[i] = s[0] (all characters of s are equal).
  Preconditions: Let n = len(s). 1 <= n <= 1000 and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_8 (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r, Aegis.CountSubstrings.count_substrings s = ok r →
      (r.val = ((s.leng * (s.leng + 1) / 2 : ℕ) : ℤ) ↔
        ∀ i, i < s.leng → byteAt s i = byteAt s 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r, Aegis.CountSubstrings.count_substrings s = ok r →
      (r.val = ((s.leng * (s.leng + 1) / 2 : ℕ) : ℤ) ↔
        ∀ i, i < s.leng → byteAt s i = byteAt s 0)) := by
  sorry

/-- Whenever count_substrings returns a result r, r = n if and only if both of the following hold: (a) for every i with 0 <= i < n - 1, s[i] != s[i + 1]; and (b) for every i with 0 <= i < n - 2, s[i] != s[i + 2].
  Preconditions: Let n = len(s). 1 <= n <= 1000 and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_9 (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r, Aegis.CountSubstrings.count_substrings s = ok r →
      (r.val = (s.leng : ℤ) ↔
        ((∀ i, i + 1 < s.leng → byteAt s i ≠ byteAt s (i + 1)) ∧
          (∀ i, i + 2 < s.leng → byteAt s i ≠ byteAt s (i + 2)))) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r, Aegis.CountSubstrings.count_substrings s = ok r →
      (r.val = (s.leng : ℤ) ↔
        ((∀ i, i + 1 < s.leng → byteAt s i ≠ byteAt s (i + 1)) ∧
          (∀ i, i + 2 < s.leng → byteAt s i ≠ byteAt s (i + 2))))) := by
  sorry

/-- Whenever count_substrings returns a result r, if the whole string s[0..n) is a palindrome (that is, for every k with 0 <= k < n, s[k] = s[n - 1 - k]), then r >= n + floor(n / 2).
  Preconditions: Let n = len(s). 1 <= n <= 1000 and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_10 (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hpal : IsPal (bytes s) 0 s.leng) :
    ∀ r, Aegis.CountSubstrings.count_substrings s = ok r →
      ((s.leng + s.leng / 2 : ℕ) : ℤ) ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hpal : IsPal (bytes s) 0 s.leng), ∀ r, Aegis.CountSubstrings.count_substrings s = ok r →
      ((s.leng + s.leng / 2 : ℕ) : ℤ) ≤ r.val) := by
  sorry

/-- Whenever count_substrings returns a result r, r equals the number of pairs (i, j) with 0 <= i < j <= n such that the substring of the reversed byte sequence rev(s) on [i, j) is a palindrome, where rev(s)[k] = s[n - 1 - k] for 0 <= k < n.
  Preconditions: Let n = len(s). 1 <= n <= 1000 and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_11 (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r, Aegis.CountSubstrings.count_substrings s = ok r →
      r.val = (PalCount (bytes s).reverse s.leng : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r, Aegis.CountSubstrings.count_substrings s = ok r →
      r.val = (PalCount (bytes s).reverse s.leng : ℤ)) := by
  sorry

/-- Whenever count_substrings returns a result r, for every m with 0 <= m <= n we have r >= P_m, where P_m is the number of pairs (i, j) with 0 <= i < j <= m and s[i..j) palindrome.
  Preconditions: Let n = len(s). 1 <= n <= 1000 and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_12 (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r, Aegis.CountSubstrings.count_substrings s = ok r →
      ∀ m, m ≤ s.leng → ((PalCount (bytes s) m : ℕ) : ℤ) ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice U8) (hn : 1 ≤ s.leng) (hmax : s.leng ≤ 1000)
    (halpha : ∀ i, i < s.leng → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r, Aegis.CountSubstrings.count_substrings s = ok r →
      ∀ m, m ≤ s.leng → ((PalCount (bytes s) m : ℕ) : ℤ) ≤ r.val) := by
  sorry

end AegisSpec.CountSubstrings
