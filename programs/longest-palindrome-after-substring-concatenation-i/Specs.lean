import Aegis.LongestPalindrome.Code.Funs

/-!
# Specifications of `Aegis.LongestPalindrome.longest_palindrome`

LeetCode problem `longest-palindrome-after-substring-concatenation-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestPalindrome

  abbrev IsPal {α : Type} (l : List α) : Prop := l = l.reverse

  def IsLowerAscii (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def window (s t : Slice Std.U8) (i j k l : ℕ) : List Std.U8 :=
    (s.val.drop i).take (j - i) ++ (t.val.drop k).take (l - k)

  def windowLength (i j k l : ℕ) : ℕ := (j - i) + (l - k)

  def maxCombinedPalLen (s t : Slice Std.U8) : ℕ :=
    ((Finset.range (s.val.length + 1)).product (Finset.range (s.val.length + 1))).sup
      (fun p : ℕ × ℕ =>
        ((Finset.range (t.val.length + 1)).product
            (Finset.range (t.val.length + 1))).sup
          (fun q : ℕ × ℕ =>
            if p.1 ≤ p.2 ∧ q.1 ≤ q.2 ∧ IsPal (window s t p.1 p.2 q.1 q.2)
            then windowLength p.1 p.2 q.1 q.2 else 0))

  def maxPalSubstringLen (l : List Std.U8) : ℕ :=
    ((Finset.range (l.length + 1)).product (Finset.range (l.length + 1))).sup
      (fun p : ℕ × ℕ =>
        if p.1 ≤ p.2 ∧ IsPal ((l.drop p.1).take (p.2 - p.1))
        then p.2 - p.1 else 0)

  def IsFactor (x y : List Std.U8) : Prop := ∃ p : ℕ, (y.drop p).take x.length = x

  def reverseSlice (s : Slice Std.U8) : Slice Std.U8 :=
    ⟨s.val.reverse.length, Aeneas.Data.ListN.ListN.fromList s.val.reverse, by
      simpa [Aeneas.Std.Slice.val, Aeneas.Data.ListN.ListN_length, List.length_reverse]
        using s.bound⟩

  theorem reverseSlice_val (s : Slice Std.U8) : (reverseSlice s).val = s.val.reverse := by
    simp [reverseSlice, Aeneas.Std.Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

  def HasAdjacentEq (l : List Std.U8) : Prop :=
    ∃ i : ℕ, i + 1 < l.length ∧ l[i]? = l[i + 1]?

  def HasGapTwoEq (l : List Std.U8) : Prop :=
    ∃ i : ℕ, i + 2 < l.length ∧ l[i]? = l[i + 2]?

  def SharesByte (s t : Slice Std.U8) : Prop :=
    ∃ i k : ℕ, i < s.val.length ∧ k < t.val.length ∧ s.val[i]? = t.val[k]?

  def ValidInput (s t : Slice Std.U8) : Prop :=
    (1 ≤ s.val.length ∧ s.val.length ≤ 30) ∧
    (1 ≤ t.val.length ∧ t.val.length ≤ 30) ∧
    (∀ b, b ∈ s.val → IsLowerAscii b) ∧
    (∀ b, b ∈ t.val → IsLowerAscii b)

  /-- the function returns a result r and r equals the maximum, over all choices of indices 0 <= i <= j <= len(s) and 0 <= k <= l <= len(t) such that the byte sequence s[i..j) concatenated with t[k..l) is a palindrome, of (j - i) + (l - k). Empty substrings (i = j or k = l) are allowed; a sequence is a palindrome if it equals its reverse; the maximum is taken over a nonempty finite set.
    Preconditions: s and t are byte slices (Slice Std.U8) with 1 <= len(s) <= 30, 1 <= len(t) <= 30, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
  theorem spec_1 (s t : Slice Std.U8) (h : ValidInput s t) :
      ∃ r : Std.I64,
        Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r ∧
        r.val = ((maxCombinedPalLen s t : ℕ) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s t : Slice Std.U8) (h : ValidInput s t), ∃ r : Std.I64,
          Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r ∧
          r.val = ((maxCombinedPalLen s t : ℕ) : ℤ)) := by
    sorry

  /-- the function returns a result r (it does not fail, panic, or report overflow) for every pair s,t satisfying the preconditions.
    Preconditions: s and t are byte slices (Slice Std.U8) with 1 <= len(s) <= 30, 1 <= len(t) <= 30, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
  theorem spec_2 (s t : Slice Std.U8) (h : ValidInput s t) :
      ∃ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s t : Slice Std.U8) (h : ValidInput s t), ∃ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r) := by
    sorry

  /-- whenever the function returns a result r, r <= len(s) + len(t).
    Preconditions: s and t are byte slices (Slice Std.U8) with 1 <= len(s) <= 30, 1 <= len(t) <= 30, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
  theorem spec_3 (s t : Slice Std.U8) (h : ValidInput s t) :
      ∀ r : Std.I64,
        Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
        r.val ≤ ((s.val.length + t.val.length : ℕ) : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s t : Slice Std.U8) (h : ValidInput s t), ∀ r : Std.I64,
          Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
          r.val ≤ ((s.val.length + t.val.length : ℕ) : ℤ)) := by
    sorry

  /-- whenever the function returns a result r, there exist indices 0 <= i <= j <= len(s) and 0 <= k <= l <= len(t) such that (j - i) + (l - k) = r and the concatenation s[i..j) followed by t[k..l) is a palindrome.
    Preconditions: s and t are byte slices (Slice Std.U8) with 1 <= len(s) <= 30, 1 <= len(t) <= 30, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
  theorem spec_4 (s t : Slice Std.U8) (h : ValidInput s t) :
      ∀ r : Std.I64,
        Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
        ∃ i j k l : ℕ,
          i ≤ j ∧ j ≤ s.val.length ∧ k ≤ l ∧ l ≤ t.val.length ∧
          (windowLength i j k l : ℤ) = r.val ∧ IsPal (window s t i j k l) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s t : Slice Std.U8) (h : ValidInput s t), ∀ r : Std.I64,
          Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
          ∃ i j k l : ℕ,
            i ≤ j ∧ j ≤ s.val.length ∧ k ≤ l ∧ l ≤ t.val.length ∧
            (windowLength i j k l : ℤ) = r.val ∧ IsPal (window s t i j k l)) := by
    sorry

  /-- whenever the function returns a result r, for every choice of indices 0 <= i <= j <= len(s) and 0 <= k <= l <= len(t), if s[i..j) followed by t[k..l) is a palindrome, then (j - i) + (l - k) <= r.
    Preconditions: s and t are byte slices (Slice Std.U8) with 1 <= len(s) <= 30, 1 <= len(t) <= 30, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
  theorem spec_5 (s t : Slice Std.U8) (h : ValidInput s t) :
      ∀ r : Std.I64,
        Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
        ∀ i j k l : ℕ, i ≤ j → j ≤ s.val.length → k ≤ l → l ≤ t.val.length →
          IsPal (window s t i j k l) → (windowLength i j k l : ℤ) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s t : Slice Std.U8) (h : ValidInput s t), ∀ r : Std.I64,
          Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
          ∀ i j k l : ℕ, i ≤ j → j ≤ s.val.length → k ≤ l → l ≤ t.val.length →
            IsPal (window s t i j k l) → (windowLength i j k l : ℤ) ≤ r.val) := by
    sorry

  /-- let L(x) be the maximum length of a contiguous substring of x that is a palindrome. Whenever the function returns a result r, r >= L(s).
    Preconditions: s and t are byte slices (Slice Std.U8) with 1 <= len(s) <= 30, 1 <= len(t) <= 30, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
  theorem spec_6 (s t : Slice Std.U8) (h : ValidInput s t) :
      ∀ r : Std.I64,
        Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
        ((maxPalSubstringLen s.val : ℕ) : ℤ) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s t : Slice Std.U8) (h : ValidInput s t), ∀ r : Std.I64,
          Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
          ((maxPalSubstringLen s.val : ℕ) : ℤ) ≤ r.val) := by
    sorry

  /-- let L(x) be the maximum length of a contiguous substring of x that is a palindrome. Whenever the function returns a result r, r >= L(t).
    Preconditions: s and t are byte slices (Slice Std.U8) with 1 <= len(s) <= 30, 1 <= len(t) <= 30, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
  theorem spec_7 (s t : Slice Std.U8) (h : ValidInput s t) :
      ∀ r : Std.I64,
        Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
        ((maxPalSubstringLen t.val : ℕ) : ℤ) ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s t : Slice Std.U8) (h : ValidInput s t), ∀ r : Std.I64,
          Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
          ((maxPalSubstringLen t.val : ℕ) : ℤ) ≤ r.val) := by
    sorry

  /-- whenever the function returns a result r, for every nonempty contiguous substring x of s, if the reverse of x occurs as a contiguous substring of t, then r >= 2 * len(x).
    Preconditions: s and t are byte slices (Slice Std.U8) with 1 <= len(s) <= 30, 1 <= len(t) <= 30, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
  theorem spec_8 (s t : Slice Std.U8) (h : ValidInput s t) :
      ∀ r : Std.I64,
        Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
        ∀ x : List Std.U8,
          IsFactor x s.val → x ≠ [] → IsFactor x.reverse t.val →
          2 * ((x.length : ℕ) : ℤ) ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s t : Slice Std.U8) (h : ValidInput s t), ∀ r : Std.I64,
          Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
          ∀ x : List Std.U8,
            IsFactor x s.val → x ≠ [] → IsFactor x.reverse t.val →
            2 * ((x.length : ℕ) : ℤ) ≤ r.val) := by
    sorry

  /-- if no byte value occurs in both s and t (that is, for every i,k with 0 <= i < len(s) and 0 <= k < len(t), s[i] != t[k]), then whenever the function returns a result r, r = max(L(s), L(t)), where L(x) is the maximum length of a contiguous palindromic substring of x.
    Preconditions: s and t are byte slices (Slice Std.U8) with 1 <= len(s) <= 30, 1 <= len(t) <= 30, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
  theorem spec_9 (s t : Slice Std.U8) (h : ValidInput s t)
      (hdisjoint : ∀ i k : ℕ, i < s.val.length → k < t.val.length →
        s.val[i]? ≠ t.val[k]?) :
      ∀ r : Std.I64,
        Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
        r.val = ((max (maxPalSubstringLen s.val) (maxPalSubstringLen t.val) : ℕ) : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s t : Slice Std.U8) (h : ValidInput s t)
        (hdisjoint : ∀ i k : ℕ, i < s.val.length → k < t.val.length →
          s.val[i]? ≠ t.val[k]?), ∀ r : Std.I64,
          Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
          r.val = ((max (maxPalSubstringLen s.val) (maxPalSubstringLen t.val) : ℕ) : ℤ)) := by
    sorry

  /-- if the concatenation of all of s followed by all of t is a palindrome, then whenever the function returns a result r, r = len(s) + len(t).
    Preconditions: s and t are byte slices (Slice Std.U8) with 1 <= len(s) <= 30, 1 <= len(t) <= 30, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
  theorem spec_10 (s t : Slice Std.U8) (h : ValidInput s t)
      (hpal : IsPal (s.val ++ t.val)) :
      ∀ r : Std.I64,
        Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
        r.val = ((s.val.length + t.val.length : ℕ) : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s t : Slice Std.U8) (h : ValidInput s t)
        (hpal : IsPal (s.val ++ t.val)), ∀ r : Std.I64,
          Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
          r.val = ((s.val.length + t.val.length : ℕ) : ℤ)) := by
    sorry

  /-- whenever the function returns a result r, if r = len(s) + len(t), then the concatenation of all of s followed by all of t is a palindrome.
    Preconditions: s and t are byte slices (Slice Std.U8) with 1 <= len(s) <= 30, 1 <= len(t) <= 30, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
  theorem spec_11 (s t : Slice Std.U8) (h : ValidInput s t) :
      ∀ r : Std.I64,
        Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
        r.val = ((s.val.length + t.val.length : ℕ) : ℤ) → IsPal (s.val ++ t.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s t : Slice Std.U8) (h : ValidInput s t), ∀ r : Std.I64,
          Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
          r.val = ((s.val.length + t.val.length : ℕ) : ℤ) → IsPal (s.val ++ t.val)) := by
    sorry

  /-- let reverse(x) be the byte sequence x read in reverse order. Whenever the function returns r on (s,t) and returns r' on (reverse(t), reverse(s)), we have r = r'.
    Preconditions: s and t are byte slices (Slice Std.U8) with 1 <= len(s) <= 30, 1 <= len(t) <= 30, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
  theorem spec_12 (s t : Slice Std.U8) (h : ValidInput s t) :
      ∀ r r' : Std.I64,
        Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
        Aegis.LongestPalindrome.longest_palindrome (reverseSlice t) (reverseSlice s)
          = Result.ok r' →
        r = r' := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s t : Slice Std.U8) (h : ValidInput s t), ∀ r r' : Std.I64,
          Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
          Aegis.LongestPalindrome.longest_palindrome (reverseSlice t) (reverseSlice s)
            = Result.ok r' →
          r = r') := by
    sorry

  /-- whenever the function returns a result r: r >= 2 if and only if at least one of the following holds: (a) there is an index i with 0 <= i and i+1 < len(s) and s[i] = s[i+1]; (b) there is an index i with 0 <= i and i+2 < len(s) and s[i] = s[i+2]; (c) there is an index i with 0 <= i and i+1 < len(t) and t[i] = t[i+1], or there is an index i with 0 <= i and i+2 < len(t) and t[i] = t[i+2]; (d) there are indices i,k with 0 <= i < len(s), 0 <= k < len(t), and s[i] = t[k].
    Preconditions: s and t are byte slices (Slice Std.U8) with 1 <= len(s) <= 30, 1 <= len(t) <= 30, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
  theorem spec_13 (s t : Slice Std.U8) (h : ValidInput s t) :
      ∀ r : Std.I64,
        Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
        (2 ≤ r.val ↔
          (HasAdjacentEq s.val ∨ HasGapTwoEq s.val ∨ HasAdjacentEq t.val ∨
            HasGapTwoEq t.val ∨ SharesByte s t)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s t : Slice Std.U8) (h : ValidInput s t), ∀ r : Std.I64,
          Aegis.LongestPalindrome.longest_palindrome s t = Result.ok r →
          (2 ≤ r.val ↔
            (HasAdjacentEq s.val ∨ HasGapTwoEq s.val ∨ HasAdjacentEq t.val ∨
              HasGapTwoEq t.val ∨ SharesByte s t))) := by
    sorry

  end AegisSpec.LongestPalindrome
