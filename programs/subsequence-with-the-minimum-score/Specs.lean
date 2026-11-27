import Aegis.MinimumScore.Code.Funs

/-!
# Specifications of `Aegis.MinimumScore.minimum_score`

LeetCode problem `subsequence-with-the-minimum-score`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumScore (minimum_score)

namespace AegisSpec.MinimumScore

def isLowerAscii (c : Std.U8) : Prop := 97 ≤ c.val ∧ c.val ≤ 122

def eraseRange (t : List Std.U8) (p q : ℕ) : List Std.U8 := t.take p ++ t.drop q

def IsSubseqList (u v : List Std.U8) : Prop := u.Sublist v

def IsSubseq (u : List Std.U8) (s : Slice Std.U8) : Prop := IsSubseqList u s.val

def scores (s : Slice Std.U8) (t : Slice Std.U8) : Set ℤ :=
  { d | ∃ p q : ℕ, p ≤ q ∧ q ≤ t.length ∧ d = (q : ℤ) - (p : ℤ) ∧
      IsSubseq (eraseRange t.val p q) s }

/-- Whenever the function returns a result r, r equals the minimum value of q - p over all integer pairs (p, q) with 0 <= p <= q <= len(t) for which the concatenation of t[0..p) and t[q..len(t)) is a subsequence of s. Here t[0..p) is the byte sequence t[0],...,t[p-1] (empty if p=0), t[q..len(t)) is t[q],...,t[len(t)-1] (empty if q=len(t)), and a byte sequence u is a subsequence of s if there exist indices 0 <= j_0 < j_1 < ... < j_{len(u)-1} < len(s) with s[j_k] = u[k] for every k (the empty sequence is a subsequence of s). The set being minimized over is nonempty because p=0, q=len(t) gives the empty concatenation.
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
theorem spec_1 (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hres : minimum_score s t = ok r) :
    IsLeast (scores s t) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hres : minimum_score s t = ok r), IsLeast (scores s t) r.val) := by
  sorry

/-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
theorem spec_2 (s t : Slice Std.U8)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c) :
    ∃ r : Std.I64, minimum_score s t = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c), ∃ r : Std.I64, minimum_score s t = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(t).
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
theorem spec_3 (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hres : minimum_score s t = ok r) :
    0 ≤ r.val ∧ r.val ≤ (t.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hres : minimum_score s t = ok r), 0 ≤ r.val ∧ r.val ≤ (t.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if t is a subsequence of s, where a byte sequence u is a subsequence of s if there exist indices 0 <= j_0 < ... < j_{len(u)-1} < len(s) with s[j_k] = u[k] for every k; in particular t is a subsequence of s if there exist indices 0 <= j_0 < ... < j_{len(t)-1} < len(s) with s[j_k] = t[k] for every k.
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
theorem spec_4 (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hres : minimum_score s t = ok r) :
    r.val = 0 ↔ IsSubseq t.val s := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hres : minimum_score s t = ok r), r.val = 0 ↔ IsSubseq t.val s) := by
  sorry

/-- Whenever the function returns a result r and r > 0, there exist integers p and q with 0 <= p < q <= len(t) such that q - p = r and the concatenation of t[0..p) and t[q..len(t)) is a subsequence of s (where subsequence means there are strictly increasing indices in s matching the concatenated bytes in order).
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
theorem spec_5 (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hres : minimum_score s t = ok r) :
    0 < r.val → ∃ p q : ℕ, p < q ∧ q ≤ t.length ∧ (q : ℤ) - (p : ℤ) = r.val ∧
      IsSubseq (eraseRange t.val p q) s := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hres : minimum_score s t = ok r), 0 < r.val → ∃ p q : ℕ, p < q ∧ q ≤ t.length ∧ (q : ℤ) - (p : ℤ) = r.val ∧
      IsSubseq (eraseRange t.val p q) s) := by
  sorry

/-- Whenever the function returns a result r, for every pair of integers (p, q) with 0 <= p <= q <= len(t) such that the concatenation of t[0..p) and t[q..len(t)) is a subsequence of s (with the standard order-preserving meaning), we have r <= q - p.
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
theorem spec_6 (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hres : minimum_score s t = ok r) :
    ∀ p q : ℕ, p ≤ q → q ≤ t.length → IsSubseq (eraseRange t.val p q) s →
      r.val ≤ (q : ℤ) - (p : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hres : minimum_score s t = ok r), ∀ p q : ℕ, p ≤ q → q ≤ t.length → IsSubseq (eraseRange t.val p q) s →
      r.val ≤ (q : ℤ) - (p : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r >= len(t) - len(s).
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122), and len(t) > len(s). -/
theorem spec_7 (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hlen : s.length < t.length)
    (hres : minimum_score s t = ok r) :
    (t.length : ℤ) - (s.length : ℤ) ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hlen : s.length < t.length)
    (hres : minimum_score s t = ok r), (t.length : ℤ) - (s.length : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if there exists an index i with 0 <= i < len(s) and s[i] = t[0], and r = 1 otherwise.
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122), and len(t) = 1. -/
theorem spec_8 (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (ht_len : t.length = 1)
    (hres : minimum_score s t = ok r) :
    (r.val = 0 ↔ ∃ i : ℕ, i < s.length ∧ s.val[i]? = t.val.head?) ∧
      (r.val = 1 ↔ ¬ ∃ i : ℕ, i < s.length ∧ s.val[i]? = t.val.head?) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (ht_len : t.length = 1)
    (hres : minimum_score s t = ok r), (r.val = 0 ↔ ∃ i : ℕ, i < s.length ∧ s.val[i]? = t.val.head?) ∧
      (r.val = 1 ↔ ¬ ∃ i : ℕ, i < s.length ∧ s.val[i]? = t.val.head?)) := by
  sorry

/-- Whenever the function returns a result r, r = len(t).
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122), and for every i with 0 <= i < len(s) and every j with 0 <= j < len(t), s[i] != t[j]. -/
theorem spec_9 (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hdisj : ∀ i j : ℕ, i < s.length → j < t.length → s.val[i]? ≠ t.val[j]?)
    (hres : minimum_score s t = ok r) :
    r.val = (t.length : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hdisj : ∀ i j : ℕ, i < s.length → j < t.length → s.val[i]? ≠ t.val[j]?)
    (hres : minimum_score s t = ok r), r.val = (t.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = len(t) if and only if for every pair of integers (p, q) with 0 <= p <= q <= len(t) and q - p < len(t), the concatenation of t[0..p) and t[q..len(t)) is not a subsequence of s (with the standard order-preserving meaning).
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
theorem spec_10 (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hres : minimum_score s t = ok r) :
    (r.val = (t.length : ℤ) ↔ ∀ p q : ℕ, p ≤ q → q ≤ t.length →
      (q : ℤ) - (p : ℤ) < (t.length : ℤ) → ¬ IsSubseq (eraseRange t.val p q) s) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hres : minimum_score s t = ok r), (r.val = (t.length : ℤ) ↔ ∀ p q : ℕ, p ≤ q → q ≤ t.length →
      (q : ℤ) - (p : ℤ) < (t.length : ℤ) → ¬ IsSubseq (eraseRange t.val p q) s)) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if (a) t is not a subsequence of s, and (b) there exists an index i with 0 <= i < len(t) such that the concatenation of t[0..i) and t[i+1..len(t)) (that is, t with the single character at index i deleted) is a subsequence of s.
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
theorem spec_11 (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hres : minimum_score s t = ok r) :
    (r.val = 1 ↔ ¬ IsSubseq t.val s ∧
      ∃ i : ℕ, i < t.length ∧ IsSubseq (eraseRange t.val i (i + 1)) s) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s t : Slice Std.U8) (r : Std.I64)
    (hs_pos : 1 ≤ s.length) (ht_pos : 1 ≤ t.length)
    (hs_bound : s.length ≤ 100000) (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hres : minimum_score s t = ok r), (r.val = 1 ↔ ¬ IsSubseq t.val s ∧
      ∃ i : ℕ, i < t.length ∧ IsSubseq (eraseRange t.val i (i + 1)) s)) := by
  sorry

/-- Let c = s[0]. Whenever the function returns a result r: (1) if len(t) = 1 and t[0] = c, then r = 0; (2) if len(t) = 1 and t[0] != c, then r = 1; (3) if len(t) >= 2 and (t[0] = c or t[len(t)-1] = c), then r = len(t) - 1; (4) if len(t) >= 2 and t[0] != c and t[len(t)-1] != c, then r = len(t).
  Preconditions: len(s) = 1, len(t) >= 1, len(t) <= 100000, and every byte of s and t is an ASCII lowercase English letter (97 <= byte <= 122). -/
theorem spec_12 (s t : Slice Std.U8) (r : Std.I64)
    (hs_len : s.length = 1) (ht_pos : 1 ≤ t.length)
    (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hres : minimum_score s t = ok r) :
    (t.length = 1 → t.val.head? = s.val.head? → r.val = 0) ∧
    (t.length = 1 → t.val.head? ≠ s.val.head? → r.val = 1) ∧
    (2 ≤ t.length →
      (t.val.head? = s.val.head? ∨ t.val.getLast? = s.val.head?) →
        r.val = (t.length : ℤ) - 1) ∧
    (2 ≤ t.length → t.val.head? ≠ s.val.head? → t.val.getLast? ≠ s.val.head? →
      r.val = (t.length : ℤ)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s t : Slice Std.U8) (r : Std.I64)
    (hs_len : s.length = 1) (ht_pos : 1 ≤ t.length)
    (ht_bound : t.length ≤ 100000)
    (hs_ascii : ∀ c ∈ s.val, isLowerAscii c)
    (ht_ascii : ∀ c ∈ t.val, isLowerAscii c)
    (hres : minimum_score s t = ok r), (t.length = 1 → t.val.head? = s.val.head? → r.val = 0) ∧
    (t.length = 1 → t.val.head? ≠ s.val.head? → r.val = 1) ∧
    (2 ≤ t.length →
      (t.val.head? = s.val.head? ∨ t.val.getLast? = s.val.head?) →
        r.val = (t.length : ℤ) - 1) ∧
    (2 ≤ t.length → t.val.head? ≠ s.val.head? → t.val.getLast? ≠ s.val.head? →
      r.val = (t.length : ℤ))) := by
  sorry

end AegisSpec.MinimumScore
