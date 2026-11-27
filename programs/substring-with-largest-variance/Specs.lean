import Aegis.LargestVariance.Code.Funs

/-!
# Specifications of `Aegis.LargestVariance.largest_variance`

LeetCode problem `substring-with-largest-variance`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LargestVariance

open Aegis.LargestVariance (largest_variance)

def LowerByte (b : U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def AllLower (s : Slice U8) : Prop := ∀ b ∈ s.val, LowerByte b

def LenInRange (s : Slice U8) : Prop := 1 ≤ s.val.length ∧ s.val.length ≤ 10000

def bytes (s : Slice U8) : List Nat := s.val.map (fun b => b.val)

def cnt (s : Slice U8) (c l h : Nat) : Nat :=
  ((bytes s).drop l).take (h - l) |>.count c

def letterDiffs (s : Slice U8) (l h : Nat) : List Int :=
  ((List.range 26).product (List.range 26)).filterMap (fun p =>
    if cnt s (97 + p.1) l h > 0 ∧ cnt s (97 + p.2) l h > 0 then
      some ((cnt s (97 + p.1) l h : Int) - (cnt s (97 + p.2) l h : Int))
    else
      none)

def variance (s : Slice U8) (l h : Nat) : Int := (letterDiffs s l h).foldr max 0

def intervals (s : Slice U8) : List (Nat × Nat) :=
  (((List.range (s.val.length + 1)).product (List.range (s.val.length + 1))).filterMap
    (fun p => if p.1 < p.2 then some p else none))

def maxVariance (s : Slice U8) : Int :=
  ((intervals s).map (fun p => variance s p.1 p.2)).foldr max 0

def pairDiffMax (s : Slice U8) (c d : Nat) : Int :=
  ((intervals s).filterMap (fun p =>
    if cnt s c p.1 p.2 > 0 ∧ cnt s d p.1 p.2 > 0 then
      some ((cnt s c p.1 p.2 : Int) - (cnt s d p.1 p.2 : Int))
    else
      none)).foldr max 0

def pairAbsDiffMax (s : Slice U8) (a b : Nat) : Int :=
  ((intervals s).filterMap (fun p =>
    if cnt s a p.1 p.2 > 0 ∧ cnt s b p.1 p.2 > 0 then
      some (((cnt s a p.1 p.2 : Int) - (cnt s b p.1 p.2 : Int)).natAbs : Int)
    else
      none)).foldr max 0

def maxLetterCount (s : Slice U8) : Nat :=
  ((List.range 26).map (fun i => cnt s (97 + i) 0 s.val.length)).foldr max 0

def distinctPairMax (s : Slice U8) : Int :=
  (((List.range 26).product (List.range 26)).filterMap (fun p =>
    if p.1 ≠ p.2 ∧ cnt s (97 + p.1) 0 s.val.length > 0 ∧
        cnt s (97 + p.2) 0 s.val.length > 0 then
      some (pairDiffMax s (97 + p.1) (97 + p.2))
    else
      none)).foldr max 0

def balanced (s : Slice U8) (l h : Nat) : Prop :=
  ∀ c d : Nat, 97 ≤ c → c ≤ 122 → 97 ≤ d → d ≤ 122 →
    cnt s c l h > 0 → cnt s d l h > 0 → cnt s c l h = cnt s d l h

def allBalanced (s : Slice U8) : Prop :=
  ∀ l h : Nat, l < h → h ≤ s.val.length → balanced s l h

def isReverse (s t : Slice U8) : Prop :=
  t.val.length = s.val.length ∧ bytes t = (bytes s).reverse

def isSubstring (s t : Slice U8) : Prop :=
  ∃ k : Nat, k + s.val.length ≤ t.val.length ∧
    ((bytes t).drop k).take s.val.length = bytes s

def atLeastTwoLetters (s : Slice U8) : Prop :=
  ∃ c d : Nat, 97 ≤ c ∧ c ≤ 122 ∧ 97 ≤ d ∧ d ≤ 122 ∧ c ≠ d ∧
    cnt s c 0 s.val.length > 0 ∧ cnt s d 0 s.val.length > 0

def atMostOneLetter (s : Slice U8) : Prop :=
  ∀ c d : Nat, 97 ≤ c → c ≤ 122 → 97 ≤ d → d ≤ 122 →
    cnt s c 0 s.val.length > 0 → cnt s d 0 s.val.length > 0 → c = d

/-- Whenever the function returns a result r, r is the maximum, over all integers l and h with 0 <= l < h <= len(s), of the variance of the non-empty substring s[l..h). For such a substring and a byte c, let cnt(c,l,h) be the number of indices i with l <= i < h and s[i] = c. The variance of s[l..h) is the maximum of cnt(c,l,h) - cnt(d,l,h) over all bytes c and d with 97 <= c,d <= 122, cnt(c,l,h) > 0, and cnt(d,l,h) > 0. Thus c and d must both occur in the substring, and they may be equal; if they are equal the difference is 0. The result r is exactly this largest possible difference over all non-empty contiguous substrings of s.
  Preconditions: s is a slice of bytes with 1 <= len(s) <= 10000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (so every byte is a lowercase ASCII letter). -/
theorem spec_1 (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s) :
    ∀ r, largest_variance s = ok r → r.val = maxVariance s := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s), ∀ r, largest_variance s = ok r → r.val = maxVariance s) := by
  sorry

/-- The function returns a result r (it does not fail, overflow, go out of bounds, or panic) for every s satisfying the preconditions.
  Preconditions: s is a slice of bytes with 1 <= len(s) <= 10000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_2 (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s) :
    ∃ r, largest_variance s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s), ∃ r, largest_variance s = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: s is a slice of bytes with 1 <= len(s) <= 10000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_3 (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s) :
    ∀ r, largest_variance s = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s), ∀ r, largest_variance s = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r and len(s) >= 2, r <= len(s) - 2.
  Preconditions: s is a slice of bytes with 1 <= len(s) <= 10000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_4 (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s) :
    ∀ r, largest_variance s = ok r → 2 ≤ s.val.length → r.val ≤ (s.val.length : Int) - 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s), ∀ r, largest_variance s = ok r → 2 ≤ s.val.length → r.val ≤ (s.val.length : Int) - 2) := by
  sorry

/-- Whenever the function returns a result r and len(s) = 1, r = 0.
  Preconditions: s is a slice of bytes with 1 <= len(s) <= 10000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_5 (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s) :
    ∀ r, largest_variance s = ok r → s.val.length = 1 → r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s), ∀ r, largest_variance s = ok r → s.val.length = 1 → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r and all bytes of s are equal (s[i] = s[j] for every 0 <= i < len(s) and 0 <= j < len(s)), r = 0.
  Preconditions: s is a slice of bytes with 1 <= len(s) <= 10000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_6 (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s) :
    (∀ b₁ : U8, b₁ ∈ s.val → ∀ b₂ : U8, b₂ ∈ s.val → b₁ = b₂) →
      ∀ r, largest_variance s = ok r → r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s), (∀ b₁ : U8, b₁ ∈ s.val → ∀ b₂ : U8, b₂ ∈ s.val → b₁ = b₂) →
      ∀ r, largest_variance s = ok r → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r and no byte value occurs twice in s (s[i] != s[j] for every 0 <= i < j < len(s)), r = 0.
  Preconditions: s is a slice of bytes with 1 <= len(s) <= 10000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_7 (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s) :
    (∀ (i j : Nat) (hi : i < s.val.length) (hj : j < s.val.length),
        i < j → s.val.get ⟨i, hi⟩ ≠ s.val.get ⟨j, hj⟩) →
      ∀ r, largest_variance s = ok r → r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s), (∀ (i j : Nat) (hi : i < s.val.length) (hj : j < s.val.length),
        i < j → s.val.get ⟨i, hi⟩ ≠ s.val.get ⟨j, hj⟩) →
      ∀ r, largest_variance s = ok r → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every non-empty substring s[l..h) with 0 <= l < h <= len(s), all lowercase letters that occur in s[l..h) have the same occurrence count in that substring.
  Preconditions: s is a slice of bytes with 1 <= len(s) <= 10000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_8 (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s) :
    ∀ r, largest_variance s = ok r → (r.val = 0 ↔ allBalanced s) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s), ∀ r, largest_variance s = ok r → (r.val = 0 ↔ allBalanced s)) := by
  sorry

/-- Whenever the function returns a result r, there exist integers l and h with 0 <= l < h <= len(s) such that the variance of the non-empty substring s[l..h), defined as the maximum over present lowercase bytes c and d in s[l..h) of (count of c in s[l..h) minus count of d in s[l..h)), is exactly r. Here the count of x in s[l..h) is the number of i with l <= i < h and s[i] = x.
  Preconditions: s is a slice of bytes with 1 <= len(s) <= 10000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_9 (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s) :
    ∀ r, largest_variance s = ok r →
      ∃ l h : Nat, l < h ∧ h ≤ s.val.length ∧ variance s l h = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s), ∀ r, largest_variance s = ok r →
      ∃ l h : Nat, l < h ∧ h ≤ s.val.length ∧ variance s l h = r.val) := by
  sorry

/-- Whenever the function returns a result r and r > 0, there exist integers l and h with 0 <= l < h <= len(s) and distinct lowercase bytes c and d (97 <= c,d <= 122, c != d) such that c and d both occur in s[l..h) and (the number of i with l <= i < h and s[i] = c) - (the number of i with l <= i < h and s[i] = d) = r.
  Preconditions: s is a slice of bytes with 1 <= len(s) <= 10000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_10 (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s) :
    ∀ r, largest_variance s = ok r → r.val > 0 →
      ∃ l h c d : Nat, l < h ∧ h ≤ s.val.length ∧
        97 ≤ c ∧ c ≤ 122 ∧ 97 ≤ d ∧ d ≤ 122 ∧ c ≠ d ∧
        cnt s c l h > 0 ∧ cnt s d l h > 0 ∧
        (cnt s c l h : Int) - (cnt s d l h : Int) = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s), ∀ r, largest_variance s = ok r → r.val > 0 →
      ∃ l h c d : Nat, l < h ∧ h ≤ s.val.length ∧
        97 ≤ c ∧ c ≤ 122 ∧ 97 ≤ d ∧ d ≤ 122 ∧ c ≠ d ∧
        cnt s c l h > 0 ∧ cnt s d l h > 0 ∧
        (cnt s c l h : Int) - (cnt s d l h : Int) = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every non-empty substring s[l..h) with 0 <= l < h <= len(s) and every two lowercase bytes c and d with 97 <= c,d <= 122 that both occur in s[l..h), (the number of i with l <= i < h and s[i] = c) - (the number of i with l <= i < h and s[i] = d) <= r.
  Preconditions: s is a slice of bytes with 1 <= len(s) <= 10000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_11 (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s) :
    ∀ r, largest_variance s = ok r →
      ∀ (l h : Nat), l < h → h ≤ s.val.length →
        ∀ c d : Nat, 97 ≤ c → c ≤ 122 → 97 ≤ d → d ≤ 122 →
          cnt s c l h > 0 → cnt s d l h > 0 →
          (cnt s c l h : Int) - (cnt s d l h : Int) ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s), ∀ r, largest_variance s = ok r →
      ∀ (l h : Nat), l < h → h ≤ s.val.length →
        ∀ c d : Nat, 97 ≤ c → c ≤ 122 → 97 ≤ d → d ≤ 122 →
          cnt s c l h > 0 → cnt s d l h > 0 →
          (cnt s c l h : Int) - (cnt s d l h : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r on input s and a result r' on input t, r = r'.
  Preconditions: s is a slice of bytes with 1 <= len(s) <= 10000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. Let t be the slice of bytes with len(t) = len(s) and t[i] = s[len(s)-1-i] for every 0 <= i < len(s). -/
theorem spec_12 (s t : Slice U8) (hlen : LenInRange s) (hlow : AllLower s)
    (hrev : isReverse s t) :
    ∀ r r', largest_variance s = ok r → largest_variance t = ok r' → r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s t : Slice U8) (hlen : LenInRange s) (hlow : AllLower s)
    (hrev : isReverse s t), ∀ r r', largest_variance s = ok r → largest_variance t = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r_s on input s and a result r_t on input t, r_s <= r_t.
  Preconditions: s and t are slices of bytes, each satisfying 1 <= len <= 10000 and all bytes in the range 97 to 122. Moreover, s occurs as a contiguous substring of t: there exists an integer k with 0 <= k and k + len(s) <= len(t) such that t[k+i] = s[i] for every 0 <= i < len(s). -/
theorem spec_13 (s t : Slice U8) (hs : LenInRange s) (hlows : AllLower s)
    (ht : LenInRange t) (hlowt : AllLower t) (hsub : isSubstring s t) :
    ∀ r_s r_t, largest_variance s = ok r_s → largest_variance t = ok r_t →
      r_s.val ≤ r_t.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s t : Slice U8) (hs : LenInRange s) (hlows : AllLower s)
    (ht : LenInRange t) (hlowt : AllLower t) (hsub : isSubstring s t), ∀ r_s r_t, largest_variance s = ok r_s → largest_variance t = ok r_t →
      r_s.val ≤ r_t.val) := by
  sorry

/-- Whenever the function returns a result r, r is the maximum, over all integers l and h with 0 <= l < h <= len(s) such that both a and b occur in s[l..h), of the absolute difference |cnt(a,l,h) - cnt(b,l,h)|, where cnt(x,l,h) is the number of i with l <= i < h and s[i] = x. Since a and b both occur in s, the full interval l=0, h=len(s) is among the intervals considered.
  Preconditions: s is a slice of bytes with 1 <= len(s) <= 10000, every byte is in 97..122, and exactly two distinct byte values occur in s. Let a and b be these two distinct values, with 97 <= a < b <= 122. -/
theorem spec_14 (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s)
    (a b : Nat) (ha : 97 ≤ a ∧ a ≤ 122) (hb : 97 ≤ b ∧ b ≤ 122) (hab : a < b)
    (hoccA : cnt s a 0 s.val.length > 0) (hoccB : cnt s b 0 s.val.length > 0)
    (htwo : ∀ c : Nat, 97 ≤ c → c ≤ 122 → cnt s c 0 s.val.length > 0 → c = a ∨ c = b) :
    ∀ r, largest_variance s = ok r → r.val = pairAbsDiffMax s a b := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s)
    (a b : Nat) (ha : 97 ≤ a ∧ a ≤ 122) (hb : 97 ≤ b ∧ b ≤ 122) (hab : a < b)
    (hoccA : cnt s a 0 s.val.length > 0) (hoccB : cnt s b 0 s.val.length > 0)
    (htwo : ∀ c : Nat, 97 ≤ c → c ≤ 122 → cnt s c 0 s.val.length > 0 → c = a ∨ c = b), ∀ r, largest_variance s = ok r → r.val = pairAbsDiffMax s a b) := by
  sorry

/-- Whenever the function returns a result r, r <= M - 1, where M is the maximum over 97 <= c <= 122 of the number of indices i with 0 <= i < len(s) and s[i] = c.
  Preconditions: s is a slice of bytes with 1 <= len(s) <= 10000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_15 (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s) :
    ∀ r, largest_variance s = ok r → r.val ≤ (maxLetterCount s : Int) - 1 := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s), ∀ r, largest_variance s = ok r → r.val ≤ (maxLetterCount s : Int) - 1) := by
  sorry

/-- Whenever the function returns a result r, if at least two distinct byte values occur in s, then r is the maximum over all distinct lowercase bytes c and d (97 <= c,d <= 122, c != d) that both occur in s, of the maximum over all integers l and h with 0 <= l < h <= len(s) such that both c and d occur in s[l..h), of (cnt(c,l,h) - cnt(d,l,h)), where cnt(x,l,h) is the number of i with l <= i < h and s[i] = x. If only one distinct byte value occurs in s, then r = 0.
  Preconditions: s is a slice of bytes with 1 <= len(s) <= 10000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_16 (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s) :
    ∀ r, largest_variance s = ok r →
      (atLeastTwoLetters s → r.val = distinctPairMax s) ∧
      (atMostOneLetter s → r.val = 0) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (s : Slice U8) (hlen : LenInRange s) (hlow : AllLower s), ∀ r, largest_variance s = ok r →
      (atLeastTwoLetters s → r.val = distinctPairMax s) ∧
      (atMostOneLetter s → r.val = 0)) := by
  sorry

end AegisSpec.LargestVariance
