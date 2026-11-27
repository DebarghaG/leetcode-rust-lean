import Aegis.ReverseDegree.Code.Funs

/-!
# Specifications of `Aegis.ReverseDegree.reverse_degree`

LeetCode problem `reverse-degree-of-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AegisSpec.ReverseDegree

def contribution (i : ℕ) (c : Std.U8) : ℤ := ((i : ℤ) + 1) * (123 - (c.val : ℤ))

def weightedSumFrom : List Std.U8 → ℕ → ℤ
  | [], _ => 0
  | c :: cs, start => contribution start c + weightedSumFrom cs (start + 1)

def weightedSum (l : List Std.U8) : ℤ := weightedSumFrom l 0

def reversedWeightedSum : List Std.U8 → ℤ
  | [] => 0
  | c :: cs => ((cs.length : ℤ) + 1) * (123 - (c.val : ℤ)) + reversedWeightedSum cs

def PointwiseRel (R : ℕ → ℕ → Prop) (l m : List Std.U8) : Prop :=
  ∀ p ∈ l.zip m, R p.1.val p.2.val

def ExistsPointwiseRel (R : ℕ → ℕ → Prop) (l m : List Std.U8) : Prop :=
  ∃ p ∈ l.zip m, R p.1.val p.2.val

/-- The function returns a result r (it does not fail), and r = sum_{i=0}^{len(s)-1} ((i+1) * (123 - s[i])). Here s[i] is the byte value at 0-based index i, and 123 - s[i] is its 1-based position in the reversed alphabet ('a' -> 26, ..., 'z' -> 1).
  Preconditions: len(s) is between 1 and 1000 inclusive, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (so every byte is a lowercase English letter). -/
theorem spec_1 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122) :
    ∃ r : Std.I64,
      Aegis.ReverseDegree.reverse_degree s = ok r ∧ r.val = weightedSum s.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122), ∃ r : Std.I64,
      Aegis.ReverseDegree.reverse_degree s = ok r ∧ r.val = weightedSum s.val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; in particular, it does not panic, overflow, read out of bounds, or otherwise fail.
  Preconditions: len(s) is between 1 and 1000 inclusive, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_2 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122) :
    ∃ r : Std.I64, Aegis.ReverseDegree.reverse_degree s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122), ∃ r : Std.I64, Aegis.ReverseDegree.reverse_degree s = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= len(s) * (len(s) + 1) / 2.
  Preconditions: len(s) is between 1 and 1000 inclusive, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_3 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (r : Std.I64) (hr : Aegis.ReverseDegree.reverse_degree s = ok r) :
    r.val ≥ ((s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (r : Std.I64) (hr : Aegis.ReverseDegree.reverse_degree s = ok r), r.val ≥ ((s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r <= 26 * len(s) * (len(s) + 1) / 2.
  Preconditions: len(s) is between 1 and 1000 inclusive, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_4 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (r : Std.I64) (hr : Aegis.ReverseDegree.reverse_degree s = ok r) :
    r.val ≤ ((26 * s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (r : Std.I64) (hr : Aegis.ReverseDegree.reverse_degree s = ok r), r.val ≤ ((26 * s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = len(s) * (len(s) + 1) / 2.
  Preconditions: len(s) is between 1 and 1000 inclusive, and for every i with 0 <= i < len(s), s[i] = 122 ('z'). -/
theorem spec_5 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, c.val = 122)
    (r : Std.I64) (hr : Aegis.ReverseDegree.reverse_degree s = ok r) :
    r.val = ((s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, c.val = 122)
    (r : Std.I64) (hr : Aegis.ReverseDegree.reverse_degree s = ok r), r.val = ((s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = 26 * len(s) * (len(s) + 1) / 2.
  Preconditions: len(s) is between 1 and 1000 inclusive, and for every i with 0 <= i < len(s), s[i] = 97 ('a'). -/
theorem spec_6 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, c.val = 97)
    (r : Std.I64) (hr : Aegis.ReverseDegree.reverse_degree s = ok r) :
    r.val = ((26 * s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, c.val = 97)
    (r : Std.I64) (hr : Aegis.ReverseDegree.reverse_degree s = ok r), r.val = ((26 * s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = 123 - s[0].
  Preconditions: len(s) is between 1 and 1000 inclusive, every byte is in 97..122, and len(s) = 1. -/
theorem spec_7 (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hlen_eq : s.val.length = 1)
    (r : Std.I64) (hr : Aegis.ReverseDegree.reverse_degree s = ok r) :
    r.val = 123 - ((s.val[0]'(by omega)).val : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hlen_eq : s.val.length = 1)
    (r : Std.I64) (hr : Aegis.ReverseDegree.reverse_degree s = ok r), r.val = 123 - ((s.val[0]'(by omega)).val : ℤ)) := by
  sorry

/-- Whenever reverse_degree(s) returns r_s and reverse_degree(t) returns r_t, r_t = r_s + (len(s) + 1) * (123 - c).
  Preconditions: s is a byte slice with 1 <= len(s) <= 999 and every s[i] for 0 <= i < len(s) satisfies 97 <= s[i] <= 122; c is a byte with 97 <= c <= 122; t is the byte slice of length len(s)+1 such that t[i] = s[i] for 0 <= i < len(s) and t[len(s)] = c. -/
theorem spec_8 (s t : Slice Std.U8) (c : Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 999)
    (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hc1 : 97 ≤ c.val) (hc2 : c.val ≤ 122)
    (ht : t.val = s.val ++ [c])
    (r_s r_t : Std.I64)
    (hrs : Aegis.ReverseDegree.reverse_degree s = ok r_s)
    (hrt : Aegis.ReverseDegree.reverse_degree t = ok r_t) :
    r_t.val = r_s.val + (((s.val.length : ℤ) + 1) * (123 - (c.val : ℤ))) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s t : Slice Std.U8) (c : Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 999)
    (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (hc1 : 97 ≤ c.val) (hc2 : c.val ≤ 122)
    (ht : t.val = s.val ++ [c])
    (r_s r_t : Std.I64)
    (hrs : Aegis.ReverseDegree.reverse_degree s = ok r_s)
    (hrt : Aegis.ReverseDegree.reverse_degree t = ok r_t), r_t.val = r_s.val + (((s.val.length : ℤ) + 1) * (123 - (c.val : ℤ)))) := by
  sorry

/-- Whenever reverse_degree(s) returns r_s and reverse_degree(t) returns r_t, r_t - r_s = sum_{j=len(s)}^{len(t)-1} ((j+1) * (123 - t[j])). The sum is 0 when len(s) = len(t).
  Preconditions: s and t are byte slices with 1 <= len(s) <= len(t) <= 1000, every byte of both is in 97..122, and s[i] = t[i] for every i with 0 <= i < len(s). -/
theorem spec_9 (s t : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ t.val.length)
    (hlen3 : t.val.length ≤ 1000)
    (hbytes_s : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hbytes_t : ∀ c ∈ t.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpre : s.val <+: t.val)
    (r_s r_t : Std.I64)
    (hrs : Aegis.ReverseDegree.reverse_degree s = ok r_s)
    (hrt : Aegis.ReverseDegree.reverse_degree t = ok r_t) :
    r_t.val - r_s.val = weightedSumFrom (t.val.drop s.val.length) s.val.length := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ t.val.length)
    (hlen3 : t.val.length ≤ 1000)
    (hbytes_s : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hbytes_t : ∀ c ∈ t.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hpre : s.val <+: t.val)
    (r_s r_t : Std.I64)
    (hrs : Aegis.ReverseDegree.reverse_degree s = ok r_s)
    (hrt : Aegis.ReverseDegree.reverse_degree t = ok r_t), r_t.val - r_s.val = weightedSumFrom (t.val.drop s.val.length) s.val.length) := by
  sorry

/-- Whenever reverse_degree(s) returns r_s and reverse_degree(t) returns r_t, r_s + r_t = 27 * (len(s) * (len(s) + 1) / 2).
  Preconditions: s is a byte slice with 1 <= len(s) <= 1000 and every s[i] is in 97..122; t is the byte slice of the same length defined by t[i] = 219 - s[i] for every i with 0 <= i < len(s), which maps 'a'<->'z', 'b'<->'y', etc., so t is also lowercase. -/
theorem spec_10 (s t : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (htlen : t.val.length = s.val.length)
    (ht : PointwiseRel (fun a b => b = 219 - a) s.val t.val)
    (r_s r_t : Std.I64)
    (hrs : Aegis.ReverseDegree.reverse_degree s = ok r_s)
    (hrt : Aegis.ReverseDegree.reverse_degree t = ok r_t) :
    r_s.val + r_t.val = 27 * ((s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (htlen : t.val.length = s.val.length)
    (ht : PointwiseRel (fun a b => b = 219 - a) s.val t.val)
    (r_s r_t : Std.I64)
    (hrs : Aegis.ReverseDegree.reverse_degree s = ok r_s)
    (hrt : Aegis.ReverseDegree.reverse_degree t = ok r_t), r_s.val + r_t.val = 27 * ((s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ)) := by
  sorry

/-- Whenever reverse_degree(s) returns r_s and reverse_degree(t) returns r_t, r_s >= r_t; moreover, if s[i] < t[i] for at least one i, then r_s > r_t.
  Preconditions: s and t are byte slices with 1 <= len(s) = len(t) <= 1000, every byte of both is in 97..122, and s[i] <= t[i] for every i with 0 <= i < len(s). -/
theorem spec_11 (s t : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 1000)
    (htlen : t.val.length = s.val.length)
    (hbytes_s : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hbytes_t : ∀ c ∈ t.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hle : PointwiseRel (fun a b => a ≤ b) s.val t.val)
    (r_s r_t : Std.I64)
    (hrs : Aegis.ReverseDegree.reverse_degree s = ok r_s)
    (hrt : Aegis.ReverseDegree.reverse_degree t = ok r_t) :
    r_s.val ≥ r_t.val ∧
      (ExistsPointwiseRel (fun a b => a < b) s.val t.val → r_s.val > r_t.val) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hlen1 : 1 ≤ s.val.length) (hlen : s.val.length ≤ 1000)
    (htlen : t.val.length = s.val.length)
    (hbytes_s : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hbytes_t : ∀ c ∈ t.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hle : PointwiseRel (fun a b => a ≤ b) s.val t.val)
    (r_s r_t : Std.I64)
    (hrs : Aegis.ReverseDegree.reverse_degree s = ok r_s)
    (hrt : Aegis.ReverseDegree.reverse_degree t = ok r_t), r_s.val ≥ r_t.val ∧
      (ExistsPointwiseRel (fun a b => a < b) s.val t.val → r_s.val > r_t.val)) := by
  sorry

end AegisSpec.ReverseDegree
