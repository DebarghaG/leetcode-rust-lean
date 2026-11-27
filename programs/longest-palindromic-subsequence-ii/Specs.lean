import Aegis.LongestPalindromeSubseq.Code.Funs

/-!
# Specifications of `Aegis.LongestPalindromeSubseq.longest_palindrome_subseq`

LeetCode problem `longest-palindromic-subsequence-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LongestPalindromeSubseq

def StrictInc (ix : List ℕ) : Prop := ix.Pairwise (· < ·)

def AllLower (s : Slice U8) : Prop := ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122

def pick (s : Slice U8) (ix : List ℕ) : List U8 := ix.map (fun i => s.val.getD i 0#u8)

def GoodPalSubseq (s : Slice U8) (ix : List ℕ) : Prop :=
  StrictInc ix ∧
  (∀ i ∈ ix, i < s.val.length) ∧
  Even ix.length ∧
  (∀ j : ℕ, j < ix.length / 2 → (pick s ix)[j]? = (pick s ix)[ix.length - 1 - j]?) ∧
  (∀ j : ℕ, j < ix.length - 1 → j ≠ ix.length / 2 - 1 →
    (pick s ix)[j]? ≠ (pick s ix)[j + 1]?)

def revSlice (s : Slice U8) : Slice U8 :=
  Slice.from s.val.reverse (by
    rw [List.length_reverse]
    exact Slice.length_ineq s)

/-- Let a good palindromic subsequence of s of length L be an increasing list of indices i_0 < ... < i_{L-1} with 0 <= i_j < len(s) (the empty list when L=0) such that, writing c_j = s[i_j], L is even, c_j = c_{L-1-j} for every j with 0 <= j < L/2, and c_j != c_{j+1} for every j with 0 <= j < L-1 and j != L/2 - 1. The function returns a result r such that r is the maximum length L for which such a good palindromic subsequence of s exists. In particular, r is even, 0 <= r <= len(s), a good palindromic subsequence of s of length r exists, and every good palindromic subsequence of s has length at most r.
  Preconditions: s is a byte slice with 1 <= len(s) <= 250, and for every i with 0 <= i < len(s), s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_1 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s) :
    ∃ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r ∧
      Even r.val ∧
      0 ≤ r.val ∧
      r.val ≤ (s.val.length : ℤ) ∧
      (∃ ix : List ℕ, GoodPalSubseq s ix ∧ (ix.length : ℤ) = r.val) ∧
      (∀ ix : List ℕ, GoodPalSubseq s ix → (ix.length : ℤ) ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s), ∃ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r ∧
      Even r.val ∧
      0 ≤ r.val ∧
      r.val ≤ (s.val.length : ℤ) ∧
      (∃ ix : List ℕ, GoodPalSubseq s ix ∧ (ix.length : ℤ) = r.val) ∧
      (∀ ix : List ℕ, GoodPalSubseq s ix → (ix.length : ℤ) ≤ r.val)) := by
  sorry

/-- The function returns a result r on every valid input s; it does not fail by panic, out-of-bounds access, or arithmetic overflow.
  Preconditions: s is a byte slice with 1 <= len(s) <= 250, and every byte s[i] is a lowercase English letter. -/
theorem spec_2 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s) :
    ∃ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s), ∃ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(s).
  Preconditions: s is a byte slice with 1 <= len(s) <= 250, and every byte s[i] is a lowercase English letter. -/
theorem spec_3 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s) :
    ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      0 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s), ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      0 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r is even; that is, r = 2*k for some integer k >= 0.
  Preconditions: s is a byte slice with 1 <= len(s) <= 250, and every byte s[i] is a lowercase English letter. -/
theorem spec_4 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s) :
    ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      ∃ k : ℤ, r.val = 2 * k ∧ 0 ≤ k := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s), ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      ∃ k : ℤ, r.val = 2 * k ∧ 0 ≤ k) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every i,j with 0 <= i < j < len(s), s[i] != s[j].
  Preconditions: s is a byte slice with 1 <= len(s) <= 250, and every byte s[i] is a lowercase English letter. -/
theorem spec_5 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s) :
    ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      (r.val = 0 ↔ ∀ i j : ℕ, i < j → j < s.val.length → s.val[i]? ≠ s.val[j]?) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s), ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      (r.val = 0 ↔ ∀ i j : ℕ, i < j → j < s.val.length → s.val[i]? ≠ s.val[j]?)) := by
  sorry

/-- Whenever the function returns a result r, there exists an increasing list of indices i_0 < ... < i_{r-1} in [0, len(s)) (empty if r=0) such that, with c_j = s[i_j], r is even, c_j = c_{r-1-j} for every j with 0 <= j < r/2, and c_j != c_{j+1} for every j with 0 <= j < r-1 and j != r/2 - 1.
  Preconditions: s is a byte slice with 1 <= len(s) <= 250, and every byte s[i] is a lowercase English letter. -/
theorem spec_6 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s) :
    ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      ∃ ix : List ℕ, GoodPalSubseq s ix ∧ (ix.length : ℤ) = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s), ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      ∃ ix : List ℕ, GoodPalSubseq s ix ∧ (ix.length : ℤ) = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every even L >= 0 and every increasing list of indices i_0 < ... < i_{L-1} in [0, len(s)) whose characters c_j = s[i_j] satisfy c_j = c_{L-1-j} for all 0 <= j < L/2 and c_j != c_{j+1} for all 0 <= j < L-1 with j != L/2 - 1, we have L <= r.
  Preconditions: s is a byte slice with 1 <= len(s) <= 250, and every byte s[i] is a lowercase English letter. -/
theorem spec_7 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s) :
    ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      ∀ ix : List ℕ, GoodPalSubseq s ix → (ix.length : ℤ) ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s), ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      ∀ ix : List ℕ, GoodPalSubseq s ix → (ix.length : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns r on input s and r_t on input t, we have r_t <= r.
  Preconditions: s is a byte slice with 1 <= len(s) <= 250, every byte s[i] is a lowercase English letter, t is a nonempty byte slice with 1 <= len(t) <= 250, every byte t[k] is a lowercase English letter, and t is a subsequence of s (there exist indices j_0 < ... < j_{len(t)-1} with s[j_k] = t[k] for every k). -/
theorem spec_8 (s t : Slice U8)
    (hs1 : 1 ≤ s.val.length) (hs250 : s.val.length ≤ 250) (hslower : AllLower s)
    (ht1 : 1 ≤ t.val.length) (ht250 : t.val.length ≤ 250) (htlower : AllLower t)
    (hsub : ∃ jx : List ℕ, StrictInc jx ∧ jx.length = t.val.length ∧
      (∀ i ∈ jx, i < s.val.length) ∧ pick s jx = t.val) :
    ∀ r rt : I64,
      Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      Aegis.LongestPalindromeSubseq.longest_palindrome_subseq t = ok rt →
      rt.val ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s t : Slice U8)
    (hs1 : 1 ≤ s.val.length) (hs250 : s.val.length ≤ 250) (hslower : AllLower s)
    (ht1 : 1 ≤ t.val.length) (ht250 : t.val.length ≤ 250) (htlower : AllLower t)
    (hsub : ∃ jx : List ℕ, StrictInc jx ∧ jx.length = t.val.length ∧
      (∀ i ∈ jx, i < s.val.length) ∧ pick s jx = t.val), ∀ r rt : I64,
      Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      Aegis.LongestPalindromeSubseq.longest_palindrome_subseq t = ok rt →
      rt.val ≤ r.val) := by
  sorry

/-- Whenever the function returns r on input s and r_rev on input rev(s), r_rev = r.
  Preconditions: s is a byte slice with 1 <= len(s) <= 250, and every byte s[i] is a lowercase English letter. Let rev(s) be the slice of the same length with rev(s)[i] = s[len(s)-1-i]. -/
theorem spec_9 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s) :
    ∀ r rrev : I64,
      Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      Aegis.LongestPalindromeSubseq.longest_palindrome_subseq (revSlice s) = ok rrev →
      rrev.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s), ∀ r rrev : I64,
      Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      Aegis.LongestPalindromeSubseq.longest_palindrome_subseq (revSlice s) = ok rrev →
      rrev.val = r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: s is a byte slice with len(s) = 1, and s[0] is a lowercase English letter. -/
theorem spec_10 (s : Slice U8)
    (hlen : s.val.length = 1) (hlower : AllLower s) :
    ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      r.val = 0 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : s.val.length = 1) (hlower : AllLower s), ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = 2.
  Preconditions: s is a byte slice with 2 <= len(s) <= 250, every byte s[i] is a lowercase English letter, and all bytes of s are equal: s[i] = s[0] for every 0 <= i < len(s). -/
theorem spec_11 (s : Slice U8)
    (hlen2 : 2 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s)
    (hconst : ∀ i : ℕ, i < s.val.length → s.val[i]? = s.val[0]?) :
    ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      r.val = 2 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice U8)
    (hlen2 : 2 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s)
    (hconst : ∀ i : ℕ, i < s.val.length → s.val[i]? = s.val[0]?), ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      r.val = 2) := by
  sorry

/-- Whenever the function returns a result r, r = 2 if s[0] = s[1], and r = 0 otherwise.
  Preconditions: s is a byte slice with len(s) = 2, and both bytes are lowercase English letters. -/
theorem spec_12 (s : Slice U8)
    (hlen : s.val.length = 2) (hlower : AllLower s) :
    ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      (s.val[0]? = s.val[1]? → r.val = 2) ∧ (s.val[0]? ≠ s.val[1]? → r.val = 0) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : s.val.length = 2) (hlower : AllLower s), ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      (s.val[0]? = s.val[1]? → r.val = 2) ∧ (s.val[0]? ≠ s.val[1]? → r.val = 0)) := by
  sorry

/-- Whenever the function returns a result r, r = len(s).
  Preconditions: s is a byte slice with 1 <= len(s) <= 250, every byte s[i] is a lowercase English letter, len(s) is even, s[i] = s[len(s)-1-i] for every 0 <= i < len(s)/2, and s[j] != s[j+1] for every 0 <= j < len(s)-1 with j != len(s)/2 - 1. -/
theorem spec_13 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s)
    (heven : Even s.val.length)
    (hpal : ∀ i : ℕ, i < s.val.length / 2 → s.val[i]? = s.val[s.val.length - 1 - i]?)
    (hadj : ∀ j : ℕ, j < s.val.length - 1 → j ≠ s.val.length / 2 - 1 →
      s.val[j]? ≠ s.val[j + 1]?) :
    ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      r.val = (s.val.length : ℤ) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s)
    (heven : Even s.val.length)
    (hpal : ∀ i : ℕ, i < s.val.length / 2 → s.val[i]? = s.val[s.val.length - 1 - i]?)
    (hadj : ∀ j : ℕ, j < s.val.length - 1 → j ≠ s.val.length / 2 - 1 →
      s.val[j]? ≠ s.val[j + 1]?), ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      r.val = (s.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r with r = len(s), then len(s) is even, s[i] = s[len(s)-1-i] for every 0 <= i < len(s)/2, and s[j] != s[j+1] for every 0 <= j < len(s)-1 with j != len(s)/2 - 1.
  Preconditions: s is a byte slice with 1 <= len(s) <= 250, and every byte s[i] is a lowercase English letter. -/
theorem spec_14 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s) :
    ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      r.val = (s.val.length : ℤ) →
      Even s.val.length ∧
      (∀ i : ℕ, i < s.val.length / 2 → s.val[i]? = s.val[s.val.length - 1 - i]?) ∧
      (∀ j : ℕ, j < s.val.length - 1 → j ≠ s.val.length / 2 - 1 →
        s.val[j]? ≠ s.val[j + 1]?) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen250 : s.val.length ≤ 250) (hlower : AllLower s), ∀ r : I64, Aegis.LongestPalindromeSubseq.longest_palindrome_subseq s = ok r →
      r.val = (s.val.length : ℤ) →
      Even s.val.length ∧
      (∀ i : ℕ, i < s.val.length / 2 → s.val[i]? = s.val[s.val.length - 1 - i]?) ∧
      (∀ j : ℕ, j < s.val.length - 1 → j ≠ s.val.length / 2 - 1 →
        s.val[j]? ≠ s.val[j + 1]?)) := by
  sorry

end AegisSpec.LongestPalindromeSubseq
