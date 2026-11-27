import Aegis.RepeatedSubstringPattern.Code.Funs

/-!
# Specifications of `Aegis.RepeatedSubstringPattern.repeated_substring_pattern`

LeetCode problem `repeated-substring-pattern`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.RepeatedSubstringPattern (repeated_substring_pattern)

namespace AegisSpec.RepeatedSubstringPattern

def byteAt (s : Slice Std.U8) (i : ℕ) : ℕ :=
  match s.val[i]? with
  | some b => b.val
  | none => 0

def IsLowerAscii (s : Slice Std.U8) : Prop :=
  ∀ (i : ℕ), i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122

def HasPeriod (s : Slice Std.U8) (d : ℕ) : Prop :=
  1 ≤ d ∧ d < s.val.length ∧ s.val.length % d = 0 ∧
    ∀ (i : ℕ), i < s.val.length → byteAt s i = byteAt s (i % d)

def IsRepetition (s : Slice Std.U8) : Prop :=
  ∃ d, HasPeriod s d

/-- Let n = len(s). The function returns a result r (it does not fail) and r = true exactly when there exists an integer d such that 1 <= d < n, n mod d = 0, and for every i with 0 <= i < n, s[i] = s[i mod d]. Equivalently, the non-empty prefix of s of length d occurs n/d >= 2 times consecutively.
  Preconditions: len(s) is an integer with 1 <= len(s) <= 10000, and every byte of s is an ASCII lowercase English letter (code 97..122). -/
theorem spec_1 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
    (hbytes : IsLowerAscii s) :
    ∃ (r : Bool), repeated_substring_pattern s = ok r ∧
      (r = true ↔ IsRepetition s) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
    (hbytes : IsLowerAscii s), ∃ (r : Bool), repeated_substring_pattern s = ok r ∧
      (r = true ↔ IsRepetition s)) := by
  sorry

/-- Let n = len(s). The function does not fail: evaluation returns Result.ok r for some Bool r. In particular, no arithmetic overflow, out-of-bounds access, or panic occurs.
  Preconditions: len(s) is an integer with 1 <= len(s) <= 10000, and every byte of s is an ASCII lowercase English letter (code 97..122). -/
theorem spec_2 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
    (hbytes : IsLowerAscii s) :
    ∃ (r : Bool), repeated_substring_pattern s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
    (hbytes : IsLowerAscii s), ∃ (r : Bool), repeated_substring_pattern s = ok r) := by
  sorry

/-- Suppose s and t have the same equality pattern: for all i,j with 0 <= i < n and 0 <= j < n, s[i] = s[j] if and only if t[i] = t[j]. Whenever the function returns Result.ok r_s on s and Result.ok r_t on t, we have r_s = r_t.
  Preconditions: s and t are byte slices, each with length between 1 and 10000 inclusive and every byte an ASCII lowercase English letter, and len(s)=len(t)=n. -/
theorem spec_3 (s t : Slice Std.U8)
    (hlen_s_lo : 1 ≤ s.val.length) (hlen_s_hi : s.val.length ≤ 10000)
    (hlen_t_lo : 1 ≤ t.val.length) (hlen_t_hi : t.val.length ≤ 10000)
    (hlen_eq : s.val.length = t.val.length)
    (hbytes_s : IsLowerAscii s) (hbytes_t : IsLowerAscii t)
    (hpattern : ∀ (i j : ℕ), i < s.val.length → j < s.val.length →
      (byteAt s i = byteAt s j ↔ byteAt t i = byteAt t j)) :
    ∀ (rs rt : Bool),
      repeated_substring_pattern s = ok rs →
      repeated_substring_pattern t = ok rt → rs = rt := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hlen_s_lo : 1 ≤ s.val.length) (hlen_s_hi : s.val.length ≤ 10000)
    (hlen_t_lo : 1 ≤ t.val.length) (hlen_t_hi : t.val.length ≤ 10000)
    (hlen_eq : s.val.length = t.val.length)
    (hbytes_s : IsLowerAscii s) (hbytes_t : IsLowerAscii t)
    (hpattern : ∀ (i j : ℕ), i < s.val.length → j < s.val.length →
      (byteAt s i = byteAt s j ↔ byteAt t i = byteAt t j)), ∀ (rs rt : Bool),
      repeated_substring_pattern s = ok rs →
      repeated_substring_pattern t = ok rt → rs = rt) := by
  sorry

end AegisSpec.RepeatedSubstringPattern
