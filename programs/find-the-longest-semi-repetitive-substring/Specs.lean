import Aegis.LongestSemiRepetitiveSubstring.Code.Funs

/-!
# Specifications of `Aegis.LongestSemiRepetitiveSubstring.longest_semi_repetitive_substring`

LeetCode problem `find-the-longest-semi-repetitive-substring`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LongestSemiRepetitiveSubstring

abbrev f (s : Slice Std.U8) : Result Std.I64 :=
  Aegis.LongestSemiRepetitiveSubstring.longest_semi_repetitive_substring s

def IsDigitBytes (l : List Std.U8) : Prop :=
  ∀ b ∈ l, 48 ≤ b.val ∧ b.val ≤ 57

def eqPairs (s : Slice Std.U8) (a b : Nat) : Nat :=
  ((List.range b).filter fun i => decide (a ≤ i ∧ i + 1 < b ∧ s.val[i]? = s.val[i + 1]?)).length

def IsValidWindow (s : Slice Std.U8) (a b : Nat) : Prop :=
  a < b ∧ b ≤ s.val.length ∧ eqPairs s a b ≤ 1

def IsLongestValidLength (s : Slice Std.U8) (res : Int) : Prop :=
  (∃ a b : Nat, IsValidWindow s a b ∧ res = ((b - a : Nat) : Int)) ∧
    ∀ a b : Nat, IsValidWindow s a b → ((b - a : Nat) : Int) ≤ res

/-- Whenever the function returns a result res, res is the maximum of the set { hi - l | 0 <= l < hi <= len(s) and Eq(l, hi) <= 1 }, where for any 0 <= l < hi <= len(s), Eq(l, hi) is the number of indices i with l <= i < hi - 1 and s[i] = s[i+1]. In words, res is the length of a longest non-empty contiguous substring of s that has at most one adjacent pair of equal bytes.
  Preconditions: Let n = len(s). The slice s is non-empty (1 <= n <= 50) and every byte s[i] for 0 <= i < n is an ASCII digit code, i.e. 48 <= s[i] <= 57. -/
theorem spec_1 (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) :
    ∀ res : Std.I64, f s = ok res → IsLongestValidLength s res.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val), ∀ res : Std.I64, f s = ok res → IsLongestValidLength s res.val) := by
  sorry

/-- The function returns a result res; equivalently, for every s satisfying the preconditions the call does not fail (no panic, out-of-bounds access, or arithmetic overflow).
  Preconditions: Let n = len(s). The slice s is non-empty (1 <= n <= 50) and every byte s[i] for 0 <= i < n is an ASCII digit code, i.e. 48 <= s[i] <= 57. -/
theorem spec_2 (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) :
    ∃ res : Std.I64, f s = ok res := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val), ∃ res : Std.I64, f s = ok res) := by
  sorry

/-- Whenever the function returns a result res, 1 <= res <= len(s).
  Preconditions: Let n = len(s). The slice s is non-empty (1 <= n <= 50) and every byte s[i] for 0 <= i < n is an ASCII digit code, i.e. 48 <= s[i] <= 57. -/
theorem spec_3 (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) :
    ∀ res : Std.I64, f s = ok res → 1 ≤ res.val ∧ res.val ≤ ((s.val.length : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val), ∀ res : Std.I64, f s = ok res → 1 ≤ res.val ∧ res.val ≤ ((s.val.length : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result res, there exist integers l and hi such that 0 <= l < hi <= len(s), hi - l = res, and the number of indices i with l <= i < hi - 1 and s[i] = s[i+1] is at most 1.
  Preconditions: Let n = len(s). The slice s is non-empty (1 <= n <= 50) and every byte s[i] for 0 <= i < n is an ASCII digit code, i.e. 48 <= s[i] <= 57. -/
theorem spec_4 (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) :
    ∀ res : Std.I64, f s = ok res →
      ∃ l hi : Nat, l < hi ∧ hi ≤ s.val.length ∧ ((hi - l : Nat) : Int) = res.val ∧
        eqPairs s l hi ≤ 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val), ∀ res : Std.I64, f s = ok res →
      ∃ l hi : Nat, l < hi ∧ hi ≤ s.val.length ∧ ((hi - l : Nat) : Int) = res.val ∧
        eqPairs s l hi ≤ 1) := by
  sorry

/-- Whenever the function returns a result res, for every pair of integers l and hi with 0 <= l < hi <= len(s) and hi - l > res, the number of indices i with l <= i < hi - 1 and s[i] = s[i+1] is at least 2.
  Preconditions: Let n = len(s). The slice s is non-empty (1 <= n <= 50) and every byte s[i] for 0 <= i < n is an ASCII digit code, i.e. 48 <= s[i] <= 57. -/
theorem spec_5 (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) :
    ∀ res : Std.I64, f s = ok res → ∀ l hi : Nat, l < hi → hi ≤ s.val.length →
      res.val < ((hi - l : Nat) : Int) → 2 ≤ eqPairs s l hi := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val), ∀ res : Std.I64, f s = ok res → ∀ l hi : Nat, l < hi → hi ≤ s.val.length →
      res.val < ((hi - l : Nat) : Int) → 2 ≤ eqPairs s l hi) := by
  sorry

/-- If the number of indices i with 0 <= i < len(s) - 1 and s[i] = s[i+1] is at most 1, then whenever the function returns a result res, res = len(s).
  Preconditions: Let n = len(s). The slice s is non-empty (1 <= n <= 50) and every byte s[i] for 0 <= i < n is an ASCII digit code, i.e. 48 <= s[i] <= 57. -/
theorem spec_6 (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) (hcount : eqPairs s 0 s.val.length ≤ 1) :
    ∀ res : Std.I64, f s = ok res → res.val = ((s.val.length : Nat) : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) (hcount : eqPairs s 0 s.val.length ≤ 1), ∀ res : Std.I64, f s = ok res → res.val = ((s.val.length : Nat) : Int)) := by
  sorry

/-- If the number of indices i with 0 <= i < len(s) - 1 and s[i] = s[i+1] is at least 2, then whenever the function returns a result res, res < len(s).
  Preconditions: Let n = len(s). The slice s is non-empty (1 <= n <= 50) and every byte s[i] for 0 <= i < n is an ASCII digit code, i.e. 48 <= s[i] <= 57. -/
theorem spec_7 (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) (hcount : 2 ≤ eqPairs s 0 s.val.length) :
    ∀ res : Std.I64, f s = ok res → res.val < ((s.val.length : Nat) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) (hcount : 2 ≤ eqPairs s 0 s.val.length), ∀ res : Std.I64, f s = ok res → res.val < ((s.val.length : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result res, if res = len(s), then the number of indices i with 0 <= i < len(s) - 1 and s[i] = s[i+1] is at most 1.
  Preconditions: Let n = len(s). The slice s is non-empty (1 <= n <= 50) and every byte s[i] for 0 <= i < n is an ASCII digit code, i.e. 48 <= s[i] <= 57. -/
theorem spec_8 (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) :
    ∀ res : Std.I64, f s = ok res → res.val = ((s.val.length : Nat) : Int) →
      eqPairs s 0 s.val.length ≤ 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val), ∀ res : Std.I64, f s = ok res → res.val = ((s.val.length : Nat) : Int) →
      eqPairs s 0 s.val.length ≤ 1) := by
  sorry

/-- If s[i] = s[0] for every i with 0 <= i < len(s), then whenever the function returns a result res, res = min(len(s), 2).
  Preconditions: Let n = len(s). The slice s is non-empty (1 <= n <= 50) and every byte s[i] for 0 <= i < n is an ASCII digit code, i.e. 48 <= s[i] <= 57. -/
theorem spec_9 (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) (hconst : ∀ i : Nat, i < s.val.length → s.val[i]? = s.val[0]?) :
    ∀ res : Std.I64, f s = ok res → res.val = ((min s.val.length 2 : Nat) : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) (hconst : ∀ i : Nat, i < s.val.length → s.val[i]? = s.val[0]?), ∀ res : Std.I64, f s = ok res → res.val = ((min s.val.length 2 : Nat) : Int)) := by
  sorry

/-- If len(s) >= 2, then whenever the function returns a result res, res >= 2.
  Preconditions: Let n = len(s). The slice s is non-empty (1 <= n <= 50) and every byte s[i] for 0 <= i < n is an ASCII digit code, i.e. 48 <= s[i] <= 57. -/
theorem spec_10 (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) (hlen : 2 ≤ s.val.length) :
    ∀ res : Std.I64, f s = ok res → 2 ≤ res.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) (hlen : 2 ≤ s.val.length), ∀ res : Std.I64, f s = ok res → 2 ≤ res.val) := by
  sorry

/-- For every s satisfying the preconditions, let t be the slice of length len(s) defined by t[i] = s[len(s)-1-i] for 0 <= i < len(s). Whenever the function returns res on input s and res' on input t, res = res'.
  Preconditions: Let n = len(s). The slice s is non-empty (1 <= n <= 50) and every byte s[i] for 0 <= i < n is an ASCII digit code, i.e. 48 <= s[i] <= 57. -/
theorem spec_11 (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) (t : Slice Std.U8) (ht : t.val = s.val.reverse) :
    ∀ res res' : Std.I64, f s = ok res → f t = ok res' → res.val = res'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) (t : Slice Std.U8) (ht : t.val = s.val.reverse), ∀ res res' : Std.I64, f s = ok res → f t = ok res' → res.val = res'.val) := by
  sorry

/-- For every pair of integers l and hi with 0 <= l < hi <= len(s), let t be the substring slice t[j] = s[l+j] for 0 <= j < hi-l. Whenever the function returns res on input s and res' on input t, res' <= res.
  Preconditions: Let n = len(s). The slice s is non-empty (1 <= n <= 50) and every byte s[i] for 0 <= i < n is an ASCII digit code, i.e. 48 <= s[i] <= 57. -/
theorem spec_12 (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) (l hi : Nat) (hl : l < hi) (hhi : hi ≤ s.val.length)
    (t : Slice Std.U8) (ht : t.val = (s.val.drop l).take (hi - l)) :
    ∀ res res' : Std.I64, f s = ok res → f t = ok res' → res'.val ≤ res.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) (l hi : Nat) (hl : l < hi) (hhi : hi ≤ s.val.length)
    (t : Slice Std.U8) (ht : t.val = (s.val.drop l).take (hi - l)), ∀ res res' : Std.I64, f s = ok res → f t = ok res' → res'.val ≤ res.val) := by
  sorry

/-- If len(s) <= 49 and c is any ASCII digit code (48 <= c <= 57), let t be the slice obtained by appending c to s, so len(t)=len(s)+1, t[i]=s[i] for 0 <= i < len(s), and t[len(s)]=c. Whenever the function returns res on input s and res' on input t, res' >= res.
  Preconditions: Let n = len(s). The slice s is non-empty (1 <= n <= 50) and every byte s[i] for 0 <= i < n is an ASCII digit code, i.e. 48 <= s[i] <= 57. -/
theorem spec_13 (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) (hle49 : s.val.length ≤ 49) (c : Std.U8)
    (hc1 : 48 ≤ c.val) (hc2 : c.val ≤ 57) (t : Slice Std.U8) (ht : t.val = s.val ++ [c]) :
    ∀ res res' : Std.I64, f s = ok res → f t = ok res' → res.val ≤ res'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) (hle49 : s.val.length ≤ 49) (c : Std.U8)
    (hc1 : 48 ≤ c.val) (hc2 : c.val ≤ 57) (t : Slice Std.U8) (ht : t.val = s.val ++ [c]), ∀ res res' : Std.I64, f s = ok res → f t = ok res' → res.val ≤ res'.val) := by
  sorry

/-- Whenever the function returns a result res, res = 1 if and only if len(s) = 1.
  Preconditions: Let n = len(s). The slice s is non-empty (1 <= n <= 50) and every byte s[i] for 0 <= i < n is an ASCII digit code, i.e. 48 <= s[i] <= 57. -/
theorem spec_14 (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val) :
    ∀ res : Std.I64, f s = ok res → (res.val = 1 ↔ s.val.length = 1) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice Std.U8) (hne : 1 ≤ s.val.length) (hle : s.val.length ≤ 50)
    (hdig : IsDigitBytes s.val), ∀ res : Std.I64, f s = ok res → (res.val = 1 ↔ s.val.length = 1)) := by
  sorry

end AegisSpec.LongestSemiRepetitiveSubstring
