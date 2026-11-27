import Aegis.LongestContinuousSubstring.Code.Funs

/-!
# Specifications of `Aegis.LongestContinuousSubstring.longest_continuous_substring`

LeetCode problem `length-of-the-longest-alphabetical-continuous-substring`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestContinuousSubstring

  def byteAt (s : Slice Std.U8) (i : Nat) : Nat :=
    (s.val.map (fun b => b.val)).getD i 0

  def IsAlphaCont (s : Slice Std.U8) (l m : Nat) : Prop :=
    1 ≤ m ∧ l + m ≤ s.val.length ∧
      ∀ k, l ≤ k → k < l + m - 1 → byteAt s (k + 1) = byteAt s k + 1

  /-- The function returns a result r and r is exactly the maximum length of an alphabetical continuous substring of s. Formally, call a substring s[l..l+m-1] alphabetical continuous if 0 <= l, m >= 1, l+m <= len(s), and for every k with l <= k < l+m-1, s[k+1] = s[k] + 1. Then there exists l with 0 <= l, r >= 1, and l+r <= len(s) such that s[l..l+r-1] is alphabetical continuous, and for every l and m such that s[l..l+m-1] is alphabetical continuous, m <= r. Thus r is exactly the largest length of such a substring.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is an ASCII lowercase letter, with a=97, ..., z=122). -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
      (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      ∃ r : Std.I64,
        Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r ∧
          (∃ (l m : Nat), IsAlphaCont s l m ∧ (m : Int) = r.val) ∧
          (∀ (l m : Nat), IsAlphaCont s l m → (m : Int) ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
        (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∃ r : Std.I64,
          Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r ∧
            (∃ (l m : Nat), IsAlphaCont s l m ∧ (m : Int) = r.val) ∧
            (∀ (l m : Nat), IsAlphaCont s l m → (m : Int) ≤ r.val)) := by
    sorry

  /-- The function returns a result r and does not fail: for every input satisfying the preconditions, the computation completes without overflow, out-of-bounds access, or panic.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is an ASCII lowercase letter, with a=97, ..., z=122). -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
      (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      ∃ r : Std.I64,
        Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
        (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∃ r : Std.I64,
          Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= len(s).
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is an ASCII lowercase letter, with a=97, ..., z=122). -/
  theorem spec_3 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
      (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (r : Std.I64)
      (hr : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r) :
      1 ≤ r.val ∧ r.val ≤ (s.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
        (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (r : Std.I64)
        (hr : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r), 1 ≤ r.val ∧ r.val ≤ (s.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r <= 26.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is an ASCII lowercase letter, with a=97, ..., z=122). -/
  theorem spec_4 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
      (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (r : Std.I64)
      (hr : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r) :
      r.val ≤ 26 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
        (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (r : Std.I64)
        (hr : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r), r.val ≤ 26) := by
    sorry

  /-- Whenever the function returns a result r, there exists an integer l with 0 <= l, r >= 1, and l+r <= len(s) such that for every k with l <= k < l+r-1, s[k+1] = s[k] + 1. In other words, some contiguous substring of length exactly r is alphabetical continuous.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is an ASCII lowercase letter, with a=97, ..., z=122). -/
  theorem spec_5 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
      (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (r : Std.I64)
      (hr : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r) :
      ∃ (l m : Nat), IsAlphaCont s l m ∧ (m : Int) = r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
        (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (r : Std.I64)
        (hr : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r), ∃ (l m : Nat), IsAlphaCont s l m ∧ (m : Int) = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer l and positive integer m with 0 <= l and l+m <= len(s), if for every k with l <= k < l+m-1, s[k+1] = s[k] + 1, then m <= r. In other words, no alphabetical continuous substring is longer than r.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is an ASCII lowercase letter, with a=97, ..., z=122). -/
  theorem spec_6 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
      (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (r : Std.I64)
      (hr : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r) :
      ∀ (l m : Nat), IsAlphaCont s l m → (m : Int) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
        (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (r : Std.I64)
        (hr : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r), ∀ (l m : Nat), IsAlphaCont s l m → (m : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, if len(s) = 1 then r = 1.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is an ASCII lowercase letter, with a=97, ..., z=122). -/
  theorem spec_7 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
      (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (r : Std.I64)
      (hr : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r) :
      s.val.length = 1 → r.val = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
        (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (r : Std.I64)
        (hr : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r), s.val.length = 1 → r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, if there exists a byte c such that s[i] = c for every i with 0 <= i < len(s), then r = 1.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is an ASCII lowercase letter, with a=97, ..., z=122). -/
  theorem spec_8 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
      (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (r : Std.I64)
      (hr : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r) :
      (∃ c : Nat, ∀ (i : Nat), i < s.val.length → byteAt s i = c) → r.val = 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
        (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (r : Std.I64)
        (hr : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r), (∃ c : Nat, ∀ (i : Nat), i < s.val.length → byteAt s i = c) → r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, if for every i with 0 <= i < len(s)-1 we have s[i+1] = s[i] + 1, then r = len(s).
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is an ASCII lowercase letter, with a=97, ..., z=122). -/
  theorem spec_9 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
      (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (r : Std.I64)
      (hr : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r) :
      (∀ (i : Nat), i + 1 < s.val.length → byteAt s (i + 1) = byteAt s i + 1) →
        r.val = (s.val.length : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
        (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (r : Std.I64)
        (hr : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r), (∀ (i : Nat), i + 1 < s.val.length → byteAt s (i + 1) = byteAt s i + 1) →
          r.val = (s.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if for every i with 0 <= i < len(s)-1, s[i+1] != s[i] + 1.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is an ASCII lowercase letter, with a=97, ..., z=122). -/
  theorem spec_10 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
      (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (r : Std.I64)
      (hr : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r) :
      (r.val = 1 ↔ ∀ (i : Nat), i + 1 < s.val.length → byteAt s (i + 1) ≠ byteAt s i + 1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
        (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (r : Std.I64)
        (hr : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r), (r.val = 1 ↔ ∀ (i : Nat), i + 1 < s.val.length → byteAt s (i + 1) ≠ byteAt s i + 1)) := by
    sorry

  /-- Whenever the function returns a result r_s on input s and a result r_t on input t, we have r_s = r_t. In other words, adding the same constant to every letter of a lowercase string does not change the length of the longest alphabetical continuous substring.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. Also, for the comparison string t, len(t) = len(s), 97 <= t[i] <= 122 for every i with 0 <= i < len(s), and there exists an integer d such that t[i] = s[i] + d for every i with 0 <= i < len(s). -/
  theorem spec_11 (s t : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
      (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (htlen : t.val.length = s.val.length)
      (htlow : ∀ (i : Nat), i < t.val.length → 97 ≤ byteAt t i ∧ byteAt t i ≤ 122)
      (hshift : ∃ d : Int, ∀ (i : Nat), i < s.val.length → (byteAt t i : Int) = (byteAt s i : Int) + d)
      (rs rt : Std.I64)
      (hrs : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok rs)
      (hrt : Aegis.LongestContinuousSubstring.longest_continuous_substring t = ok rt) :
      rs.val = rt.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
        (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (htlen : t.val.length = s.val.length)
        (htlow : ∀ (i : Nat), i < t.val.length → 97 ≤ byteAt t i ∧ byteAt t i ≤ 122)
        (hshift : ∃ d : Int, ∀ (i : Nat), i < s.val.length → (byteAt t i : Int) = (byteAt s i : Int) + d)
        (rs rt : Std.I64)
        (hrs : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok rs)
        (hrt : Aegis.LongestContinuousSubstring.longest_continuous_substring t = ok rt), rs.val = rt.val) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices a and b with 0 <= a <= b < len(s), b - a + 1 = r, such that: (i) for every k with a <= k < b, s[k+1] = s[k] + 1; (ii) either a = 0 or s[a] != s[a-1] + 1; and (iii) either b = len(s)-1 or s[b+1] != s[b] + 1. In other words, r is the length of some maximal contiguous run of letters that increase by exactly 1 and cannot be extended left or right.
    Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is an ASCII lowercase letter, with a=97, ..., z=122). -/
  theorem spec_12 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
      (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (r : Std.I64)
      (hr : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r) :
      ∃ (a b : Nat),
        a ≤ b ∧ b < s.val.length ∧ ((b - a + 1 : Nat) : Int) = r.val ∧
          (∀ k, a ≤ k → k < b → byteAt s (k + 1) = byteAt s k + 1) ∧
          (a = 0 ∨ byteAt s a ≠ byteAt s (a - 1) + 1) ∧
          (b + 1 = s.val.length ∨ byteAt s (b + 1) ≠ byteAt s b + 1) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hmax : s.val.length ≤ 100000)
        (hlow : ∀ (i : Nat), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (r : Std.I64)
        (hr : Aegis.LongestContinuousSubstring.longest_continuous_substring s = ok r), ∃ (a b : Nat),
          a ≤ b ∧ b < s.val.length ∧ ((b - a + 1 : Nat) : Int) = r.val ∧
            (∀ k, a ≤ k → k < b → byteAt s (k + 1) = byteAt s k + 1) ∧
            (a = 0 ∨ byteAt s a ≠ byteAt s (a - 1) + 1) ∧
            (b + 1 = s.val.length ∨ byteAt s (b + 1) ≠ byteAt s b + 1)) := by
    sorry

  end AegisSpec.LongestContinuousSubstring
