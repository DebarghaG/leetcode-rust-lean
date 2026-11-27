import Aegis.LengthOfLongestSubstring.Code.Funs

/-!
# Specifications of `Aegis.LengthOfLongestSubstring.length_of_longest_substring`

LeetCode problem `longest-substring-without-repeating-characters`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LengthOfLongestSubstring

def byteAt (s : Slice Std.U8) (i : Nat) : Nat :=
  match s.val[i]? with
  | some b => b.val
  | none => 0

def RepeatFree (s : Slice Std.U8) (l u : Nat) : Prop :=
  ∀ i j : Nat, l ≤ i → i < j → j < u → byteAt s i ≠ byteAt s j

def IsLongestRepeatFree (s : Slice Std.U8) (r : Nat) : Prop :=
  (∃ l u : Nat, l ≤ u ∧ u ≤ s.val.length ∧ RepeatFree s l u ∧ u - l = r) ∧
    ∀ l u : Nat, l ≤ u → u ≤ s.val.length → RepeatFree s l u → u - l ≤ r

def numDistinctBytes (s : Slice Std.U8) : Nat :=
  (s.val.map (fun b => b.val)).eraseDups.length

/-- Whenever the function returns Ok r, interpreting r as an integer, r equals the greatest length u - l of a contiguous segment s[l..u) such that 0 <= l <= u <= len(s) and the bytes in that segment are pairwise distinct: for every i, j with l <= i < j < u, s[i] != s[j]. Equivalently, r is the length of a repeat-free contiguous substring of s, and no repeat-free contiguous substring of s is longer. The empty segment is allowed, so len(s) = 0 forces r = 0.
  Preconditions: 0 <= len(s) <= 50000. -/
theorem spec_1 (s : Slice Std.U8) (hlen : s.val.length ≤ 50000) (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r) :
    IsLongestRepeatFree s r.val.toNat := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (hlen : s.val.length ≤ 50000) (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r), IsLongestRepeatFree s r.val.toNat) := by
  sorry

/-- The function returns a result of the form Ok r for some i64 r; in particular, it does not fail, panic, or overflow on any input satisfying the precondition.
  Preconditions: 0 <= len(s) <= 50000. -/
theorem spec_2 (s : Slice Std.U8) (hlen : s.val.length ≤ 50000) :
    ∃ r : Std.I64, Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (hlen : s.val.length ≤ 50000), ∃ r : Std.I64, Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r) := by
  sorry

/-- Whenever the function returns Ok r, interpreting r as an integer, 0 <= r <= len(s).
  Preconditions: 0 <= len(s) <= 50000. -/
theorem spec_3 (s : Slice Std.U8) (hlen : s.val.length ≤ 50000) (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r) :
    0 ≤ r.val ∧ r.val ≤ (s.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (hlen : s.val.length ≤ 50000) (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r), 0 ≤ r.val ∧ r.val ≤ (s.val.length : Int)) := by
  sorry

/-- Whenever the function returns Ok r, interpreting r as an integer, r = 0.
  Preconditions: len(s) = 0. -/
theorem spec_4 (s : Slice Std.U8) (hlen : s.val.length = 0) (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r) :
    r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (hlen : s.val.length = 0) (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r), r.val = 0) := by
  sorry

/-- Whenever the function returns Ok r, interpreting r as an integer, r = 1.
  Preconditions: len(s) = 1. -/
theorem spec_5 (s : Slice Std.U8) (hlen : s.val.length = 1) (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r) :
    r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (hlen : s.val.length = 1) (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r), r.val = 1) := by
  sorry

/-- Whenever the function returns Ok r, interpreting r as an integer, r >= 1.
  Preconditions: 1 <= len(s) <= 50000. -/
theorem spec_6 (s : Slice Std.U8) (hlen : 1 ≤ s.val.length) (hle : s.val.length ≤ 50000)
    (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r) :
    1 ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (hlen : 1 ≤ s.val.length) (hle : s.val.length ≤ 50000)
    (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r), 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns Ok r, interpreting r as an integer, r = len(s).
  Preconditions: 0 <= len(s) <= 50000 and for every i, j with 0 <= i < j < len(s), s[i] != s[j]. -/
theorem spec_7 (s : Slice Std.U8) (hlen : s.val.length ≤ 50000)
    (hdist : ∀ i j : Nat, i < j → j < s.val.length → byteAt s i ≠ byteAt s j)
    (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r) :
    r.val = (s.val.length : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (hlen : s.val.length ≤ 50000)
    (hdist : ∀ i j : Nat, i < j → j < s.val.length → byteAt s i ≠ byteAt s j)
    (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r), r.val = (s.val.length : Int)) := by
  sorry

/-- Whenever the function returns Ok r, interpreting r as an integer, there exists an index l such that 0 <= l <= len(s), l + r <= len(s), and the segment s[l..l+r) is repeat-free, i.e. for every i, j with l <= i < j < l+r, s[i] != s[j].
  Preconditions: 0 <= len(s) <= 50000. -/
theorem spec_8 (s : Slice Std.U8) (hlen : s.val.length ≤ 50000) (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r) :
    ∃ l : Nat, l ≤ s.val.length ∧ l + r.val.toNat ≤ s.val.length ∧
      RepeatFree s l (l + r.val.toNat) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (hlen : s.val.length ≤ 50000) (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r), ∃ l : Nat, l ≤ s.val.length ∧ l + r.val.toNat ≤ s.val.length ∧
      RepeatFree s l (l + r.val.toNat)) := by
  sorry

/-- Whenever the function returns Ok r, interpreting r as an integer, for every l, u with 0 <= l <= u <= len(s), if the segment s[l..u) is repeat-free (for every i, j with l <= i < j < u, s[i] != s[j]), then u - l <= r.
  Preconditions: 0 <= len(s) <= 50000. -/
theorem spec_9 (s : Slice Std.U8) (hlen : s.val.length ≤ 50000) (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r) :
    ∀ l u : Nat, l ≤ u → u ≤ s.val.length → RepeatFree s l u → (u - l : Int) ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (hlen : s.val.length ≤ 50000) (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r), ∀ l u : Nat, l ≤ u → u ≤ s.val.length → RepeatFree s l u → (u - l : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns Ok r, interpreting r as an integer, r is at most the number of distinct byte values occurring in s: r <= |{ s[i] | 0 <= i < len(s) }|.
  Preconditions: 0 <= len(s) <= 50000. -/
theorem spec_10 (s : Slice Std.U8) (hlen : s.val.length ≤ 50000) (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r) :
    r.val ≤ (numDistinctBytes s : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (hlen : s.val.length ≤ 50000) (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r), r.val ≤ (numDistinctBytes s : Int)) := by
  sorry

/-- Whenever the function returns Ok r, interpreting r as an integer, r = 0 if and only if len(s) = 0.
  Preconditions: 0 <= len(s) <= 50000. -/
theorem spec_11 (s : Slice Std.U8) (hlen : s.val.length ≤ 50000) (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r) :
    r.val = 0 ↔ s.val.length = 0 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (hlen : s.val.length ≤ 50000) (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r), r.val = 0 ↔ s.val.length = 0) := by
  sorry

/-- If the function returns Ok r on input s and returns Ok r' on input t, then interpreting r and r' as integers, r = r'.
  Preconditions: 0 <= len(s) <= 50000 and 0 <= len(t) <= 50000 and len(t) = len(s) and for every i, j with 0 <= i < len(s) and 0 <= j < len(s), s[i] = s[j] if and only if t[i] = t[j]. -/
theorem spec_12 (s t : Slice Std.U8) (hs : s.val.length ≤ 50000)
    (ht : t.val.length ≤ 50000) (hlen : t.val.length = s.val.length)
    (hpat : ∀ i j : Nat, i < s.val.length → j < s.val.length →
      (byteAt s i = byteAt s j ↔ byteAt t i = byteAt t j))
    (r r' : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r)
    (hr' : Aegis.LengthOfLongestSubstring.length_of_longest_substring t = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s t : Slice Std.U8) (hs : s.val.length ≤ 50000)
    (ht : t.val.length ≤ 50000) (hlen : t.val.length = s.val.length)
    (hpat : ∀ i j : Nat, i < s.val.length → j < s.val.length →
      (byteAt s i = byteAt s j ↔ byteAt t i = byteAt t j))
    (r r' : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r)
    (hr' : Aegis.LengthOfLongestSubstring.length_of_longest_substring t = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns Ok r, interpreting r as an integer, r < len(s).
  Preconditions: 0 <= len(s) <= 50000 and there exist i, j with 0 <= i < j < len(s) and s[i] = s[j]. -/
theorem spec_13 (s : Slice Std.U8) (hlen : s.val.length ≤ 50000)
    (hrep : ∃ i j : Nat, i < j ∧ j < s.val.length ∧ byteAt s i = byteAt s j)
    (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r) :
    r.val < (s.val.length : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.U8) (hlen : s.val.length ≤ 50000)
    (hrep : ∃ i j : Nat, i < j ∧ j < s.val.length ∧ byteAt s i = byteAt s j)
    (r : Std.I64)
    (hr : Aegis.LengthOfLongestSubstring.length_of_longest_substring s = ok r), r.val < (s.val.length : Int)) := by
  sorry

end AegisSpec.LengthOfLongestSubstring
