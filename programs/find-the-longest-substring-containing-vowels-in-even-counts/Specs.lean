import Aegis.FindTheLongestSubstring.Code.Funs

/-!
# Specifications of `Aegis.FindTheLongestSubstring.find_the_longest_substring`

LeetCode problem `find-the-longest-substring-containing-vowels-in-even-counts`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindTheLongestSubstring

  def vowelCodes : List Nat := [97, 101, 105, 111, 117]

  def IsVowelByte (c : Aeneas.Std.U8) : Prop := c.val ∈ vowelCodes

  def AllLowercase (l : List Aeneas.Std.U8) : Prop :=
    ∀ c, c ∈ l → 97 ≤ c.val ∧ c.val ≤ 122

  def NoVowelByte (l : List Aeneas.Std.U8) : Prop := ∀ c, c ∈ l → ¬ IsVowelByte c

  def byteAt (l : List Aeneas.Std.U8) (i : Nat) (h : i < l.length) : Aeneas.Std.U8 :=
    l.get ⟨i, h⟩

  def IsVowelAt (l : List Aeneas.Std.U8) (i : Nat) (h : i < l.length) : Prop :=
    IsVowelByte (byteAt l i h)

  def vowelCount (l : List Aeneas.Std.U8) (v : Nat) (lo hi : Nat) : Nat :=
    ((l.drop lo).take (hi - lo)).countP (fun c => c.val = v)

  def VowelsEvenIn (l : List Aeneas.Std.U8) (lo hi : Nat) : Prop :=
    ∀ v, v ∈ vowelCodes → vowelCount l v lo hi % 2 = 0

  def IsLongestEvenVowelSubstring (l : List Aeneas.Std.U8) (r : Int) : Prop :=
    (∃ lo hi : Nat,
        lo ≤ hi ∧ hi ≤ l.length ∧ VowelsEvenIn l lo hi ∧ r = (hi : Int) - (lo : Int)) ∧
      ∀ lo hi : Nat,
        lo ≤ hi → hi ≤ l.length → VowelsEvenIn l lo hi → (hi : Int) - (lo : Int) ≤ r

  def SameVowelPattern (l₁ l₂ : List Aeneas.Std.U8) : Prop :=
    l₁.length = l₂.length ∧
      List.Forall₂
        (fun c d => (IsVowelByte c → d = c) ∧ (¬ IsVowelByte c → ¬ IsVowelByte d)) l₁ l₂

  /-- Let V = {97, 101, 105, 111, 117} (the ASCII codes of 'a', 'e', 'i', 'o', 'u'). Whenever the function returns a result r, r is the maximum of r0 - l over all pairs (l, r0) such that 0 <= l <= r0 <= len(s) and, for every v in V, the number of indices k with l <= k < r0 and s[k] = v is even. Equivalently, r is the length of a longest contiguous substring of s in which each of the five vowels occurs an even number of times. The empty substring (l = r0, length 0) is allowed.
    Preconditions: len(s) >= 1, len(s) <= 500000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (so s is a nonempty string of lowercase ASCII letters). -/
  theorem spec_1 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val) {r : Aeneas.Std.I64}
      (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r) :
      IsLongestEvenVowelSubstring s.val r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val) {r : Aeneas.Std.I64}
        (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r), IsLongestEvenVowelSubstring s.val r.val) := by
    sorry

  /-- For every s satisfying the preconditions, the function returns a result r; it does not overflow, panic, or access out of bounds.
    Preconditions: len(s) >= 1, len(s) <= 500000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_2 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val) :
      ∃ r : Aeneas.Std.I64,
        Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val), ∃ r : Aeneas.Std.I64,
          Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= len(s).
    Preconditions: len(s) >= 1, len(s) <= 500000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_3 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val) {r : Aeneas.Std.I64}
      (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r) :
      0 ≤ r.val ∧ r.val ≤ (s.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val) {r : Aeneas.Std.I64}
        (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r), 0 ≤ r.val ∧ r.val ≤ (s.val.length : Int)) := by
    sorry

  /-- Let V = {97, 101, 105, 111, 117}. Whenever the function returns a result r, there exist indices l and r0 with 0 <= l <= r0 <= len(s), r0 - l = r, and for every v in V the number of indices k with l <= k < r0 and s[k] = v is even.
    Preconditions: len(s) >= 1, len(s) <= 500000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_4 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val) {r : Aeneas.Std.I64}
      (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r) :
      ∃ lo hi : Nat,
        lo ≤ hi ∧ hi ≤ s.val.length ∧ VowelsEvenIn s.val lo hi ∧
          r.val = (hi : Int) - (lo : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val) {r : Aeneas.Std.I64}
        (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r), ∃ lo hi : Nat,
          lo ≤ hi ∧ hi ≤ s.val.length ∧ VowelsEvenIn s.val lo hi ∧
            r.val = (hi : Int) - (lo : Int)) := by
    sorry

  /-- Let V = {97, 101, 105, 111, 117}. Whenever the function returns a result r, for every pair (l, r0) with 0 <= l <= r0 <= len(s) and for every v in V the number of indices k with l <= k < r0 and s[k] = v is even, we have r0 - l <= r.
    Preconditions: len(s) >= 1, len(s) <= 500000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_5 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val) {r : Aeneas.Std.I64}
      (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r) :
      ∀ lo hi : Nat,
        lo ≤ hi → hi ≤ s.val.length → VowelsEvenIn s.val lo hi →
          (hi : Int) - (lo : Int) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val) {r : Aeneas.Std.I64}
        (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r), ∀ lo hi : Nat,
          lo ≤ hi → hi ≤ s.val.length → VowelsEvenIn s.val lo hi →
            (hi : Int) - (lo : Int) ≤ r.val) := by
    sorry

  /-- Let V = {97, 101, 105, 111, 117}. Whenever the function returns a result r, if no byte of s belongs to V (that is, for every i with 0 <= i < len(s), s[i] not in V), then r = len(s).
    Preconditions: len(s) >= 1, len(s) <= 500000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_6 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val) {r : Aeneas.Std.I64}
      (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r)
      (hnv : NoVowelByte s.val) :
      r.val = (s.val.length : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val) {r : Aeneas.Std.I64}
        (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r)
        (hnv : NoVowelByte s.val), r.val = (s.val.length : Int)) := by
    sorry

  /-- Let V = {97, 101, 105, 111, 117}. Whenever the function returns a result r, if there are exactly two indices p and q with 0 <= p < q < len(s), s[p] in V, s[q] in V, s[p] != s[q], and s[i] not in V for every i with 0 <= i < len(s) such that i != p and i != q, then r = max(p, q - p - 1, len(s) - 1 - q).
    Preconditions: len(s) >= 1, len(s) <= 500000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_7 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val) {r : Aeneas.Std.I64}
      (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r)
      (p q : Nat) (hp : p < s.val.length) (hq : q < s.val.length) (hpq : p < q)
      (hvp : IsVowelAt s.val p hp) (hvq : IsVowelAt s.val q hq)
      (hne : byteAt s.val p hp ≠ byteAt s.val q hq)
      (hrest : ∀ (j : Nat) (hj : j < s.val.length),
        j ≠ p → j ≠ q → ¬ IsVowelAt s.val j hj) :
      r.val = max (max (p : Int) ((q : Int) - (p : Int) - 1))
        ((s.val.length : Int) - 1 - (q : Int)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val) {r : Aeneas.Std.I64}
        (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r)
        (p q : Nat) (hp : p < s.val.length) (hq : q < s.val.length) (hpq : p < q)
        (hvp : IsVowelAt s.val p hp) (hvq : IsVowelAt s.val q hq)
        (hne : byteAt s.val p hp ≠ byteAt s.val q hq)
        (hrest : ∀ (j : Nat) (hj : j < s.val.length),
          j ≠ p → j ≠ q → ¬ IsVowelAt s.val j hj), r.val = max (max (p : Int) ((q : Int) - (p : Int) - 1))
          ((s.val.length : Int) - 1 - (q : Int))) := by
    sorry

  /-- Let V = {97, 101, 105, 111, 117}. Whenever the function returns a result r, if at least one byte of s belongs to V and, for every v in V, the number of indices i with 0 <= i < len(s) and s[i] = v is even, then r = len(s).
    Preconditions: len(s) >= 1, len(s) <= 500000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_8 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val) {r : Aeneas.Std.I64}
      (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r)
      (hex : ∃ c, c ∈ s.val ∧ IsVowelByte c)
      (heven : VowelsEvenIn s.val 0 s.val.length) :
      r.val = (s.val.length : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val) {r : Aeneas.Std.I64}
        (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r)
        (hex : ∃ c, c ∈ s.val ∧ IsVowelByte c)
        (heven : VowelsEvenIn s.val 0 s.val.length), r.val = (s.val.length : Int)) := by
    sorry

  /-- Let V = {97, 101, 105, 111, 117}. Whenever the function returns a result r, if there is exactly one index p with 0 <= p < len(s) and s[p] in V (so s[i] not in V for every i != p), then r = max(p, len(s) - 1 - p).
    Preconditions: len(s) >= 1, len(s) <= 500000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_9 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val) {r : Aeneas.Std.I64}
      (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r)
      (p : Nat) (hp : p < s.val.length) (hvp : IsVowelAt s.val p hp)
      (hrest : ∀ (j : Nat) (hj : j < s.val.length), j ≠ p → ¬ IsVowelAt s.val j hj) :
      r.val = max (p : Int) ((s.val.length : Int) - 1 - (p : Int)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val) {r : Aeneas.Std.I64}
        (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r)
        (p : Nat) (hp : p < s.val.length) (hvp : IsVowelAt s.val p hp)
        (hrest : ∀ (j : Nat) (hj : j < s.val.length), j ≠ p → ¬ IsVowelAt s.val j hj), r.val = max (p : Int) ((s.val.length : Int) - 1 - (p : Int))) := by
    sorry

  /-- Let V = {97, 101, 105, 111, 117}. For every byte slice t with len(t) = len(s), 97 <= t[i] <= 122 for all i with 0 <= i < len(s), and such that for every i with 0 <= i < len(s): if s[i] in V then t[i] = s[i], and if s[i] not in V then t[i] not in V, whenever the function returns r on s and r_t on t, we have r = r_t.
    Preconditions: len(s) >= 1, len(s) <= 500000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_10 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val)
      (t : Aeneas.Std.Slice Aeneas.Std.U8) (hlen : t.val.length = s.val.length)
      (hlower_t : AllLowercase t.val) (hsame : SameVowelPattern s.val t.val)
      {r rₜ : Aeneas.Std.I64}
      (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r)
      (hrₜ : Aegis.FindTheLongestSubstring.find_the_longest_substring t = ok rₜ) :
      r.val = rₜ.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val)
        (t : Aeneas.Std.Slice Aeneas.Std.U8) (hlen : t.val.length = s.val.length)
        (hlower_t : AllLowercase t.val) (hsame : SameVowelPattern s.val t.val)
        {r rₜ : Aeneas.Std.I64}
        (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r)
        (hrₜ : Aegis.FindTheLongestSubstring.find_the_longest_substring t = ok rₜ), r.val = rₜ.val) := by
    sorry

  /-- Let rev(s) be the byte slice t of length len(s) defined by t[i] = s[len(s) - 1 - i] for every i with 0 <= i < len(s). Whenever the function returns r on s and r_rev on rev(s), we have r = r_rev.
    Preconditions: len(s) >= 1, len(s) <= 500000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_11 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
      (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val)
      (t : Aeneas.Std.Slice Aeneas.Std.U8) (hrev : t.val = s.val.reverse)
      {r rᵣₑᵥ : Aeneas.Std.I64}
      (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r)
      (hrᵣₑᵥ : Aegis.FindTheLongestSubstring.find_the_longest_substring t = ok rᵣₑᵥ) :
      r.val = rᵣₑᵥ.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hlen1 : 1 ≤ s.val.length)
        (hlen2 : s.val.length ≤ 500000) (hlower : AllLowercase s.val)
        (t : Aeneas.Std.Slice Aeneas.Std.U8) (hrev : t.val = s.val.reverse)
        {r rᵣₑᵥ : Aeneas.Std.I64}
        (hr : Aegis.FindTheLongestSubstring.find_the_longest_substring s = ok r)
        (hrᵣₑᵥ : Aegis.FindTheLongestSubstring.find_the_longest_substring t = ok rᵣₑᵥ), r.val = rᵣₑᵥ.val) := by
    sorry

  end AegisSpec.FindTheLongestSubstring
