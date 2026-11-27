import Aegis.IsSubstringPresent.Code.Funs

/-!
# Specifications of `Aegis.IsSubstringPresent.is_substring_present`

LeetCode problem `existence-of-a-substring-in-a-string-and-its-reverse`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.IsSubstringPresent (is_substring_present)

set_option autoImplicit false

namespace AegisSpec.IsSubstringPresent

def revPairOccurs (l : List Std.U8) : Prop :=
  ∃ (i j : Nat) (hi : i + 1 < l.length) (hj : j + 1 < l.length),
    l[i] = l[j + 1] ∧ l[i + 1] = l[j]

def occursIn (a b : List Std.U8) : Prop :=
  ∃ (k : Nat) (hk : k + a.length ≤ b.length),
    ∀ (i : Nat) (h : i < a.length), b[k + i]'(by omega) = a[i]

/-- Whenever the function returns a result r, r = true if and only if there exist indices i and j such that 0 <= i < len(s)-1, 0 <= j < len(s)-1, s[i] = s[j+1], and s[i+1] = s[j]. Equivalently, r = true if and only if some contiguous length-2 substring of s equals the reverse of some contiguous length-2 substring of s, i.e. occurs in the reverse of s; r = false otherwise.
  Preconditions: len(s) is an integer with 1 <= len(s) <= 100, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (so s is a nonempty lowercase ASCII string of at most 100 bytes). -/
theorem spec_1 (s : Slice Std.U8) (r : Bool)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122) :
    is_substring_present s = ok r → (r = true ↔ revPairOccurs s.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (r : Bool)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122), is_substring_present s = ok r → (r = true ↔ revPairOccurs s.val)) := by
  sorry

/-- For every s satisfying the preconditions, the function returns a result r and does not fail (no overflow, out-of-bounds access, or panic).
  Preconditions: len(s) is an integer with 1 <= len(s) <= 100, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_2 (s : Slice Std.U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122) :
    ∃ r : Bool, is_substring_present s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122), ∃ r : Bool, is_substring_present s = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = false.
  Preconditions: len(s) = 1, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_3 (s : Slice Std.U8) (r : Bool)
    (hlen : s.val.length = 1)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122) :
    is_substring_present s = ok r → r = false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (r : Bool)
    (hlen : s.val.length = 1)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122), is_substring_present s = ok r → r = false) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if s[0] = s[1].
  Preconditions: len(s) = 2, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_4 (s : Slice Std.U8) (r : Bool)
    (hlen : s.val.length = 2)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122) :
    is_substring_present s = ok r →
      (r = true ↔ s.val[0]'(by omega) = s.val[1]'(by omega)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (r : Bool)
    (hlen : s.val.length = 2)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122), is_substring_present s = ok r →
      (r = true ↔ s.val[0]'(by omega) = s.val[1]'(by omega))) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if s[0] = s[1] or s[1] = s[2] or s[0] = s[2]. Equivalently, for length 3 the answer is true exactly when the three bytes are not pairwise distinct.
  Preconditions: len(s) = 3, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_5 (s : Slice Std.U8) (r : Bool)
    (hlen : s.val.length = 3)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122) :
    is_substring_present s = ok r →
      (r = true ↔
        (s.val[0]'(by omega) = s.val[1]'(by omega) ∨
         s.val[1]'(by omega) = s.val[2]'(by omega) ∨
         s.val[0]'(by omega) = s.val[2]'(by omega))) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (r : Bool)
    (hlen : s.val.length = 3)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122), is_substring_present s = ok r →
      (r = true ↔
        (s.val[0]'(by omega) = s.val[1]'(by omega) ∨
         s.val[1]'(by omega) = s.val[2]'(by omega) ∨
         s.val[0]'(by omega) = s.val[2]'(by omega)))) := by
  sorry

/-- Whenever the function returns a result r and there exists an index i with 0 <= i < len(s)-1 and s[i] = s[i+1], we have r = true.
  Preconditions: len(s) is an integer with 1 <= len(s) <= 100, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_6 (s : Slice Std.U8) (r : Bool)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122)
    (hadj : ∃ (i : Nat) (hi : i + 1 < s.val.length), s.val[i] = s.val[i + 1]) :
    is_substring_present s = ok r → r = true := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (r : Bool)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122)
    (hadj : ∃ (i : Nat) (hi : i + 1 < s.val.length), s.val[i] = s.val[i + 1]), is_substring_present s = ok r → r = true) := by
  sorry

/-- Whenever the function returns a result r, r = true.
  Preconditions: len(s) >= 2, len(s) <= 100, for every i with 0 <= i < len(s), 97 <= s[i] <= 122, and for every k with 0 <= k < len(s), s[k] = s[len(s)-1-k] (s is equal to its reverse). -/
theorem spec_7 (s : Slice Std.U8) (r : Bool)
    (hlen : 2 ≤ s.val.length) (hlen' : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122)
    (hpal : ∀ (k : Nat) (hk : k < s.val.length),
      s.val[k] = s.val[s.val.length - 1 - k]) :
    is_substring_present s = ok r → r = true := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (r : Bool)
    (hlen : 2 ≤ s.val.length) (hlen' : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122)
    (hpal : ∀ (k : Nat) (hk : k < s.val.length),
      s.val[k] = s.val[s.val.length - 1 - k]), is_substring_present s = ok r → r = true) := by
  sorry

/-- Let rev(s) be the byte slice of length len(s) with rev(s)[k] = s[len(s)-1-k] for every k with 0 <= k < len(s). Whenever the function returns r on input s and returns r' on input rev(s), we have r = r'.
  Preconditions: len(s) is an integer with 1 <= len(s) <= 100, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_8 (s t : Slice Std.U8) (r r' : Bool)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122)
    (hrev : t.val = s.val.reverse) :
    is_substring_present s = ok r → is_substring_present t = ok r' → r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s t : Slice Std.U8) (r r' : Bool)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122)
    (hrev : t.val = s.val.reverse), is_substring_present s = ok r → is_substring_present t = ok r' → r = r') := by
  sorry

/-- Whenever the function returns a result r = true, there exist indices p and q with 0 <= p < q < len(s) and s[p] = s[q]; that is, at least one byte value occurs at least twice in s.
  Preconditions: len(s) is an integer with 1 <= len(s) <= 100, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_9 (s : Slice Std.U8) (r : Bool)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122) :
    is_substring_present s = ok r → r = true →
      ∃ (p q : Nat) (hpq : p < q) (hq : q < s.val.length), s.val[p] = s.val[q] := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (r : Bool)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122), is_substring_present s = ok r → r = true →
      ∃ (p q : Nat) (hpq : p < q) (hq : q < s.val.length), s.val[p] = s.val[q]) := by
  sorry

/-- Whenever the function returns a result r = true, there exist indices i and j with 0 <= i < len(s)-1 and 0 <= j < len(s)-1 such that s[i] = s[j+1] and s[i+1] = s[j]. Thus the contiguous length-2 substring s[i], s[i+1] occurs in the reverse of s as the reversed pair s[j], s[j+1].
  Preconditions: len(s) is an integer with 1 <= len(s) <= 100, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_10 (s : Slice Std.U8) (r : Bool)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122) :
    is_substring_present s = ok r → r = true → revPairOccurs s.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (r : Bool)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122), is_substring_present s = ok r → r = true → revPairOccurs s.val) := by
  sorry

/-- Whenever the function returns a result r and there exists an index i with 0 <= i < len(s)-2 and s[i] = s[i+2], we have r = true.
  Preconditions: len(s) is an integer with 1 <= len(s) <= 100, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_11 (s : Slice Std.U8) (r : Bool)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122)
    (hwin : ∃ (i : Nat) (hi : i + 2 < s.val.length), s.val[i] = s.val[i + 2]) :
    is_substring_present s = ok r → r = true := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (r : Bool)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122)
    (hwin : ∃ (i : Nat) (hi : i + 2 < s.val.length), s.val[i] = s.val[i + 2]), is_substring_present s = ok r → r = true) := by
  sorry

/-- Whenever the function returns a result r = true, len(s) >= 2.
  Preconditions: len(s) is an integer with 1 <= len(s) <= 100, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_12 (s : Slice Std.U8) (r : Bool)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122) :
    is_substring_present s = ok r → r = true → 2 ≤ s.val.length := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8) (r : Bool)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 100)
    (hbytes : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122), is_substring_present s = ok r → r = true → 2 ≤ s.val.length) := by
  sorry

/-- Whenever the function returns r = true on input s and returns r' on input t, we have r' = true.
  Preconditions: s and t are byte slices, each with length between 1 and 100 inclusive and each consisting only of bytes in the range 97 through 122. Moreover s occurs contiguously in t: there exists an offset k with 0 <= k, k + len(s) <= len(t), and for every i with 0 <= i < len(s), t[k+i] = s[i]. -/
theorem spec_13 (s t : Slice Std.U8) (r r' : Bool)
    (hlen_s : 1 ≤ s.val.length) (hlen_s' : s.val.length ≤ 100)
    (hbytes_s : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122)
    (hlen_t : 1 ≤ t.val.length) (hlen_t' : t.val.length ≤ 100)
    (hbytes_t : ∀ (i : Nat) (h : i < t.val.length), 97 ≤ t.val[i].val ∧ t.val[i].val ≤ 122)
    (hocc : occursIn s.val t.val) :
    is_substring_present s = ok r → is_substring_present t = ok r' → r = true → r' = true := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s t : Slice Std.U8) (r r' : Bool)
    (hlen_s : 1 ≤ s.val.length) (hlen_s' : s.val.length ≤ 100)
    (hbytes_s : ∀ (i : Nat) (h : i < s.val.length), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122)
    (hlen_t : 1 ≤ t.val.length) (hlen_t' : t.val.length ≤ 100)
    (hbytes_t : ∀ (i : Nat) (h : i < t.val.length), 97 ≤ t.val[i].val ∧ t.val[i].val ≤ 122)
    (hocc : occursIn s.val t.val), is_substring_present s = ok r → is_substring_present t = ok r' → r = true → r' = true) := by
  sorry

end AegisSpec.IsSubstringPresent
