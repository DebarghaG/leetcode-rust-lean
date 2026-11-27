import Aegis.HasMatch.Code.Funs

/-!
# Specifications of `Aegis.HasMatch.has_match`

LeetCode problem `substring-matching-pattern`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.HasMatch

def isLower (x : Std.U8) : Prop := 97 ≤ x.val ∧ x.val ≤ 122

def isStar (x : Std.U8) : Prop := x.val = 42

def byteAt (l : List Std.U8) (i : Nat) : Option Nat := (l[i]?).map (fun x => x.val)

def starAt (p : List Std.U8) (k : Nat) : Prop :=
  byteAt p k = some 42 ∧ ∀ j, byteAt p j = some 42 → j = k

def hasUniqueStar (p : List Std.U8) : Prop :=
  ∃ k, starAt p k

def matchAt (s t : List Std.U8) (i : Nat) : Prop :=
  ∀ j, j < t.length → s[i + j]? = t[j]?

def occurs (s t : List Std.U8) : Prop :=
  ∃ i, i + t.length ≤ s.length ∧ matchAt s t i

/-- Whenever has_match s p returns a Boolean value r, r is true exactly when there exist integers L and i such that: (1) a + b <= L <= len(s); (2) 0 <= i <= len(s) - L; (3) for every j with 0 <= j < a, s[i + j] = p[j]; and (4) for every j with 0 <= j < b, s[i + L - b + j] = p[k + 1 + j]. Here L is the length of a contiguous substring of s that matches p, and the star is replaced by the L - a - b bytes between the prefix and suffix.
  Preconditions: s and p are byte arrays of ASCII codes with 1 <= len(s) <= 50 and 1 <= len(p) <= 50. s contains only lowercase English letters. p contains only lowercase English letters and exactly one '*' (byte 42). Let k be the unique index with p[k] = '*'; let a = k and b = len(p) - k - 1. -/
theorem spec_1 (s p : Slice Std.U8) (k : Nat)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hstar : starAt p.val k) :
    ∀ r, Aegis.HasMatch.has_match s p = ok r →
      (r = true ↔
        ∃ L i : Nat,
          k + (p.val.length - k - 1) ≤ L ∧
          L ≤ s.val.length ∧
          i ≤ s.val.length - L ∧
          matchAt s.val (p.val.take k) i ∧
          matchAt s.val (p.val.drop (k + 1)) (i + L - (p.val.length - k - 1))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s p : Slice Std.U8) (k : Nat)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hstar : starAt p.val k), ∀ r, Aegis.HasMatch.has_match s p = ok r →
      (r = true ↔
        ∃ L i : Nat,
          k + (p.val.length - k - 1) ≤ L ∧
          L ≤ s.val.length ∧
          i ≤ s.val.length - L ∧
          matchAt s.val (p.val.take k) i ∧
          matchAt s.val (p.val.drop (k + 1)) (i + L - (p.val.length - k - 1)))) := by
  sorry

/-- For every s and p satisfying the preconditions, the call has_match s p does not fail: it returns some Boolean value (Result.ok true or Result.ok false).
  Preconditions: s and p are byte arrays of ASCII codes with 1 <= len(s) <= 50 and 1 <= len(p) <= 50. s contains only lowercase English letters. p contains only lowercase English letters and exactly one '*' (byte 42). -/
theorem spec_2 (s p : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hstar : hasUniqueStar p.val) :
    ∃ r : Bool, Aegis.HasMatch.has_match s p = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s p : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hstar : hasUniqueStar p.val), ∃ r : Bool, Aegis.HasMatch.has_match s p = ok r) := by
  sorry

/-- Whenever has_match s p returns a Boolean value r, r is true.
  Preconditions: s and p are byte arrays of ASCII codes with 1 <= len(s) <= 50 and 1 <= len(p) <= 50. s contains only lowercase English letters. p contains only lowercase English letters and exactly one '*' (byte 42). Moreover, len(p) = 1 and p[0] = '*'. -/
theorem spec_3 (s p : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hp_len_one : p.val.length = 1)
    (hp_star : starAt p.val 0) :
    ∀ r, Aegis.HasMatch.has_match s p = ok r → r = true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s p : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hp_len_one : p.val.length = 1)
    (hp_star : starAt p.val 0), ∀ r, Aegis.HasMatch.has_match s p = ok r → r = true) := by
  sorry

/-- Whenever has_match s p returns a Boolean value r, r is true exactly when the suffix B = p[1..len(p)) occurs as a contiguous substring of s: there exists an integer q with 0 <= q, q + b <= len(s), and for every j with 0 <= j < b, s[q + j] = p[1 + j].
  Preconditions: s and p are byte arrays of ASCII codes with 1 <= len(s) <= 50 and 1 <= len(p) <= 50. s contains only lowercase English letters. p contains only lowercase English letters and exactly one '*' (byte 42). Moreover, p[0] = '*' and len(p) > 1. Let b = len(p) - 1; the unique star is at index 0. -/
theorem spec_4 (s p : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hp_gt_one : 1 < p.val.length)
    (hp_star : starAt p.val 0) :
    ∀ r, Aegis.HasMatch.has_match s p = ok r →
      (r = true ↔ occurs s.val (p.val.drop 1)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s p : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hp_gt_one : 1 < p.val.length)
    (hp_star : starAt p.val 0), ∀ r, Aegis.HasMatch.has_match s p = ok r →
      (r = true ↔ occurs s.val (p.val.drop 1))) := by
  sorry

/-- Whenever has_match s p returns a Boolean value r, r is true exactly when the prefix A = p[0..len(p) - 1) occurs as a contiguous substring of s: there exists an integer i with 0 <= i, i + a <= len(s), and for every j with 0 <= j < a, s[i + j] = p[j].
  Preconditions: s and p are byte arrays of ASCII codes with 1 <= len(s) <= 50 and 1 <= len(p) <= 50. s contains only lowercase English letters. p contains only lowercase English letters and exactly one '*' (byte 42). Moreover, p[len(p) - 1] = '*' and len(p) > 1. Let a = len(p) - 1; the unique star is at the last index. -/
theorem spec_5 (s p : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hp_gt_one : 1 < p.val.length)
    (hp_star : starAt p.val (p.val.length - 1)) :
    ∀ r, Aegis.HasMatch.has_match s p = ok r →
      (r = true ↔ occurs s.val (p.val.take (p.val.length - 1))) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s p : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hp_gt_one : 1 < p.val.length)
    (hp_star : starAt p.val (p.val.length - 1)), ∀ r, Aegis.HasMatch.has_match s p = ok r →
      (r = true ↔ occurs s.val (p.val.take (p.val.length - 1)))) := by
  sorry

/-- Whenever has_match s p returns a Boolean value r, r is true exactly when s is the concatenation of the pattern parts around the star: for every j with 0 <= j < a, s[j] = p[j], and for every j with 0 <= j < b, s[a + j] = p[k + 1 + j].
  Preconditions: s and p are byte arrays of ASCII codes with 1 <= len(s) <= 50 and 1 <= len(p) <= 50. s contains only lowercase English letters. p contains only lowercase English letters and exactly one '*' (byte 42). Let k be the unique index with p[k] = '*'; let a = k and b = len(p) - k - 1; assume len(s) = a + b. -/
theorem spec_6 (s p : Slice Std.U8) (k : Nat)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hstar : starAt p.val k)
    (hlen : s.val.length = k + (p.val.length - k - 1)) :
    ∀ r, Aegis.HasMatch.has_match s p = ok r →
      (r = true ↔
        matchAt s.val (p.val.take k) 0 ∧
        matchAt s.val (p.val.drop (k + 1)) k) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s p : Slice Std.U8) (k : Nat)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hstar : starAt p.val k)
    (hlen : s.val.length = k + (p.val.length - k - 1)), ∀ r, Aegis.HasMatch.has_match s p = ok r →
      (r = true ↔
        matchAt s.val (p.val.take k) 0 ∧
        matchAt s.val (p.val.drop (k + 1)) k)) := by
  sorry

/-- Whenever has_match s p returns a Boolean value r, r is false.
  Preconditions: s and p are byte arrays of ASCII codes with 1 <= len(s) <= 50 and 1 <= len(p) <= 50. s contains only lowercase English letters. p contains only lowercase English letters and exactly one '*' (byte 42). Let k be the unique index with p[k] = '*'; let a = k and b = len(p) - k - 1; assume a + b > len(s). -/
theorem spec_7 (s p : Slice Std.U8) (k : Nat)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hstar : starAt p.val k)
    (hlen : k + (p.val.length - k - 1) > s.val.length) :
    ∀ r, Aegis.HasMatch.has_match s p = ok r → r = false := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s p : Slice Std.U8) (k : Nat)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hstar : starAt p.val k)
    (hlen : k + (p.val.length - k - 1) > s.val.length), ∀ r, Aegis.HasMatch.has_match s p = ok r → r = false) := by
  sorry

/-- Whenever has_match s p returns a Boolean value r, if there exist integers i and q such that 0 <= i, i + a <= q, q + b <= len(s), for every j with 0 <= j < a, s[i + j] = p[j], and for every j with 0 <= j < b, s[q + j] = p[k + 1 + j], then r is true.
  Preconditions: s and p are byte arrays of ASCII codes with 1 <= len(s) <= 50 and 1 <= len(p) <= 50. s contains only lowercase English letters. p contains only lowercase English letters and exactly one '*' (byte 42). Let k be the unique index with p[k] = '*'; let a = k and b = len(p) - k - 1. -/
theorem spec_8 (s p : Slice Std.U8) (k : Nat)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hstar : starAt p.val k) :
    ∀ r, Aegis.HasMatch.has_match s p = ok r →
      (∃ i q : Nat,
          i + k ≤ q ∧
          q + (p.val.length - k - 1) ≤ s.val.length ∧
          matchAt s.val (p.val.take k) i ∧
          matchAt s.val (p.val.drop (k + 1)) q) →
      r = true := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s p : Slice Std.U8) (k : Nat)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hstar : starAt p.val k), ∀ r, Aegis.HasMatch.has_match s p = ok r →
      (∃ i q : Nat,
          i + k ≤ q ∧
          q + (p.val.length - k - 1) ≤ s.val.length ∧
          matchAt s.val (p.val.take k) i ∧
          matchAt s.val (p.val.drop (k + 1)) q) →
      r = true) := by
  sorry

/-- Whenever has_match s p returns a Boolean value r and r is true, the prefix A = p[0..k) occurs as a contiguous substring of s: there exists an integer i with 0 <= i, i + a <= len(s), and for every j with 0 <= j < a, s[i + j] = p[j].
  Preconditions: s and p are byte arrays of ASCII codes with 1 <= len(s) <= 50 and 1 <= len(p) <= 50. s contains only lowercase English letters. p contains only lowercase English letters and exactly one '*' (byte 42). Let k be the unique index with p[k] = '*'; let a = k and b = len(p) - k - 1; assume a > 0. -/
theorem spec_9 (s p : Slice Std.U8) (k : Nat)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hstar : starAt p.val k)
    (ha : 0 < k) :
    ∀ r, Aegis.HasMatch.has_match s p = ok r → r = true →
      occurs s.val (p.val.take k) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s p : Slice Std.U8) (k : Nat)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hstar : starAt p.val k)
    (ha : 0 < k), ∀ r, Aegis.HasMatch.has_match s p = ok r → r = true →
      occurs s.val (p.val.take k)) := by
  sorry

/-- Whenever has_match s p returns a Boolean value r and r is true, the suffix B = p[k+1..len(p)) occurs as a contiguous substring of s: there exists an integer q with 0 <= q, q + b <= len(s), and for every j with 0 <= j < b, s[q + j] = p[k + 1 + j].
  Preconditions: s and p are byte arrays of ASCII codes with 1 <= len(s) <= 50 and 1 <= len(p) <= 50. s contains only lowercase English letters. p contains only lowercase English letters and exactly one '*' (byte 42). Let k be the unique index with p[k] = '*'; let a = k and b = len(p) - k - 1; assume b > 0. -/
theorem spec_10 (s p : Slice Std.U8) (k : Nat)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hstar : starAt p.val k)
    (hb : 0 < p.val.length - k - 1) :
    ∀ r, Aegis.HasMatch.has_match s p = ok r → r = true →
      occurs s.val (p.val.drop (k + 1)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s p : Slice Std.U8) (k : Nat)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hstar : starAt p.val k)
    (hb : 0 < p.val.length - k - 1), ∀ r, Aegis.HasMatch.has_match s p = ok r → r = true →
      occurs s.val (p.val.drop (k + 1))) := by
  sorry

/-- If has_match s p returns true, then whenever has_match s' p returns a Boolean value r, r is true.
  Preconditions: s and p are byte arrays of ASCII codes with 1 <= len(s) <= 50 and 1 <= len(p) <= 50. s contains only lowercase English letters. p contains only lowercase English letters and exactly one '*' (byte 42). Also u and v are byte arrays consisting only of lowercase English letters, with 1 <= len(u) + len(s) + len(v) <= 50. Let s' = u ++ s ++ v (concatenation). -/
theorem spec_11 (s p u v s' : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hstar : hasUniqueStar p.val)
    (hu_chars : ∀ x ∈ u.val, isLower x)
    (hv_chars : ∀ x ∈ v.val, isLower x)
    (huv_len : 1 ≤ u.val.length + s.val.length + v.val.length ∧
      u.val.length + s.val.length + v.val.length ≤ 50)
    (hs' : s'.val = u.val ++ s.val ++ v.val) :
    Aegis.HasMatch.has_match s p = ok true →
      ∀ r, Aegis.HasMatch.has_match s' p = ok r → r = true := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s p u v s' : Slice Std.U8)
    (hs_len : 1 ≤ s.val.length ∧ s.val.length ≤ 50)
    (hp_len : 1 ≤ p.val.length ∧ p.val.length ≤ 50)
    (hs_chars : ∀ x ∈ s.val, isLower x)
    (hp_chars : ∀ x ∈ p.val, isLower x ∨ isStar x)
    (hstar : hasUniqueStar p.val)
    (hu_chars : ∀ x ∈ u.val, isLower x)
    (hv_chars : ∀ x ∈ v.val, isLower x)
    (huv_len : 1 ≤ u.val.length + s.val.length + v.val.length ∧
      u.val.length + s.val.length + v.val.length ≤ 50)
    (hs' : s'.val = u.val ++ s.val ++ v.val), Aegis.HasMatch.has_match s p = ok true →
      ∀ r, Aegis.HasMatch.has_match s' p = ok r → r = true) := by
  sorry

end AegisSpec.HasMatch
