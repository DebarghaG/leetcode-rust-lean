import Aegis.CountGoodSubstrings.Code.Funs

/-!
# Specifications of `Aegis.CountGoodSubstrings.count_good_substrings`

LeetCode problem `substrings-of-size-three-with-distinct-characters`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountGoodSubstrings

def byteAt (s : Slice Std.U8) (j : ℕ) : Option ℕ := (s.val[j]?).map (fun b => b.val)

def PairwiseDistinctWindow (s : Slice Std.U8) (i : ℕ) : Prop :=
  ∃ a b c : ℕ,
    byteAt s i = some a ∧ byteAt s (i + 1) = some b ∧ byteAt s (i + 2) = some c ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c

def GoodWindow (s : Slice Std.U8) (i : ℕ) : Prop :=
  i + 2 < s.val.length ∧ PairwiseDistinctWindow s i

noncomputable def goodCount (s : Slice Std.U8) : ℕ := by
  classical
  exact ((Finset.range (s.val.length - 2)).filter (fun i => GoodWindow s i)).card

def ValidInput (s : Slice Std.U8) : Prop :=
  1 ≤ s.val.length ∧ s.val.length ≤ 100 ∧
    ∀ (j a : ℕ), byteAt s j = some a → 97 ≤ a ∧ a ≤ 122

def SameEqualityPattern (s t : Slice Std.U8) : Prop :=
  s.val.length = t.val.length ∧
    ∀ p q : ℕ,
      p < s.val.length → q < s.val.length →
        (byteAt s p = byteAt s q ↔ byteAt t p = byteAt t q)

/-- Whenever count_good_substrings(s) returns a result r, r is the number of indices i such that 0 <= i and i+2 < len(s) and the three bytes s[i], s[i+1], s[i+2] are pairwise distinct, i.e. s[i] != s[i+1] and s[i] != s[i+2] and s[i+1] != s[i+2]. Each index i is counted separately, so equal textual length-3 substrings occurring at different positions contribute separately.
  Preconditions: 1 <= len(s) <= 100, and for every j with 0 <= j < len(s), 97 <= s[j] <= 122 (so s is a nonempty string of lowercase ASCII letters). -/
theorem spec_1 (s : Slice Std.U8) (hs : ValidInput s) (r : Std.I64)
    (h : Aegis.CountGoodSubstrings.count_good_substrings s = ok r) :
    r.val = (goodCount s : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : ValidInput s) (r : Std.I64)
    (h : Aegis.CountGoodSubstrings.count_good_substrings s = ok r), r.val = (goodCount s : ℤ)) := by
  sorry

/-- For every s satisfying the preconditions, count_good_substrings(s) returns a result (it does not fail: no panic, no out-of-bounds access, and no arithmetic overflow).
  Preconditions: 1 <= len(s) <= 100, and for every j with 0 <= j < len(s), 97 <= s[j] <= 122. -/
theorem spec_2 (s : Slice Std.U8) (hs : ValidInput s) :
    ∃ r : Std.I64, Aegis.CountGoodSubstrings.count_good_substrings s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : ValidInput s), ∃ r : Std.I64, Aegis.CountGoodSubstrings.count_good_substrings s = ok r) := by
  sorry

/-- Whenever count_good_substrings(s) returns a result r, 0 <= r <= max(0, len(s)-2). Equivalently, r is at most the number of length-3 contiguous substrings of s, which is max(0, len(s)-2).
  Preconditions: 1 <= len(s) <= 100, and for every j with 0 <= j < len(s), 97 <= s[j] <= 122. -/
theorem spec_3 (s : Slice Std.U8) (hs : ValidInput s) (r : Std.I64)
    (h : Aegis.CountGoodSubstrings.count_good_substrings s = ok r) :
    0 ≤ r.val ∧ r.val ≤ max 0 ((s.val.length : ℤ) - 2) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : ValidInput s) (r : Std.I64)
    (h : Aegis.CountGoodSubstrings.count_good_substrings s = ok r), 0 ≤ r.val ∧ r.val ≤ max 0 ((s.val.length : ℤ) - 2)) := by
  sorry

/-- If len(s) < 3 (so len(s) is 1 or 2 under the preconditions), then whenever count_good_substrings(s) returns a result r, r = 0.
  Preconditions: 1 <= len(s) <= 100, and for every j with 0 <= j < len(s), 97 <= s[j] <= 122. -/
theorem spec_4 (s : Slice Std.U8) (hs : ValidInput s) (hsmall : s.val.length < 3)
    (r : Std.I64) (h : Aegis.CountGoodSubstrings.count_good_substrings s = ok r) :
    r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : ValidInput s) (hsmall : s.val.length < 3)
    (r : Std.I64) (h : Aegis.CountGoodSubstrings.count_good_substrings s = ok r), r.val = 0) := by
  sorry

/-- Whenever count_good_substrings(s) returns a result r, r > 0 if and only if there exists an index i with 0 <= i and i+2 < len(s) such that s[i], s[i+1], s[i+2] are pairwise distinct. Equivalently, r = 0 if and only if no such index i exists.
  Preconditions: 1 <= len(s) <= 100, and for every j with 0 <= j < len(s), 97 <= s[j] <= 122. -/
theorem spec_5 (s : Slice Std.U8) (hs : ValidInput s) (r : Std.I64)
    (h : Aegis.CountGoodSubstrings.count_good_substrings s = ok r) :
    0 < r.val ↔ ∃ i : ℕ, GoodWindow s i := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : ValidInput s) (r : Std.I64)
    (h : Aegis.CountGoodSubstrings.count_good_substrings s = ok r), 0 < r.val ↔ ∃ i : ℕ, GoodWindow s i) := by
  sorry

/-- Let t be the slice with len(t) = len(s) and t[j] = s[len(s)-1-j] for every j with 0 <= j < len(s) (the reversal of s). Whenever count_good_substrings(s) returns r and count_good_substrings(t) returns r', we have r = r'.
  Preconditions: 1 <= len(s) <= 100, and for every j with 0 <= j < len(s), 97 <= s[j] <= 122. -/
theorem spec_6 (s t : Slice Std.U8) (hs : ValidInput s) (hrev : t.val = s.val.reverse)
    (r r' : Std.I64)
    (h : Aegis.CountGoodSubstrings.count_good_substrings s = ok r)
    (h' : Aegis.CountGoodSubstrings.count_good_substrings t = ok r') :
    r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s t : Slice Std.U8) (hs : ValidInput s) (hrev : t.val = s.val.reverse)
    (r r' : Std.I64)
    (h : Aegis.CountGoodSubstrings.count_good_substrings s = ok r)
    (h' : Aegis.CountGoodSubstrings.count_good_substrings t = ok r'), r = r') := by
  sorry

/-- For every pair of valid slices s and t with len(s) = len(t) and with the same equality pattern, i.e. for all p,q with 0 <= p < len(s) and 0 <= q < len(s), s[p] = s[q] if and only if t[p] = t[q], whenever count_good_substrings(s) returns r and count_good_substrings(t) returns r', we have r = r'.
  Preconditions: s and t each satisfy: 1 <= len <= 100, and for every index j in that slice, 97 <= value <= 122 (both are nonempty lowercase ASCII strings). -/
theorem spec_7 (s t : Slice Std.U8) (hs : ValidInput s) (ht : ValidInput t)
    (hpat : SameEqualityPattern s t) (r r' : Std.I64)
    (h : Aegis.CountGoodSubstrings.count_good_substrings s = ok r)
    (h' : Aegis.CountGoodSubstrings.count_good_substrings t = ok r') :
    r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s t : Slice Std.U8) (hs : ValidInput s) (ht : ValidInput t)
    (hpat : SameEqualityPattern s t) (r r' : Std.I64)
    (h : Aegis.CountGoodSubstrings.count_good_substrings s = ok r)
    (h' : Aegis.CountGoodSubstrings.count_good_substrings t = ok r'), r = r') := by
  sorry

/-- If for all p,q with 0 <= p < q < len(s), s[p] != s[q] (all bytes in s are pairwise distinct), then whenever count_good_substrings(s) returns a result r, r = max(0, len(s)-2).
  Preconditions: 1 <= len(s) <= 100, and for every j with 0 <= j < len(s), 97 <= s[j] <= 122. -/
theorem spec_8 (s : Slice Std.U8) (hs : ValidInput s)
    (hdistinct : ∀ (p q ap aq : ℕ),
      p < q → q < s.val.length → byteAt s p = some ap → byteAt s q = some aq → ap ≠ aq)
    (r : Std.I64) (h : Aegis.CountGoodSubstrings.count_good_substrings s = ok r) :
    r.val = max 0 ((s.val.length : ℤ) - 2) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : ValidInput s)
    (hdistinct : ∀ (p q ap aq : ℕ),
      p < q → q < s.val.length → byteAt s p = some ap → byteAt s q = some aq → ap ≠ aq)
    (r : Std.I64) (h : Aegis.CountGoodSubstrings.count_good_substrings s = ok r), r.val = max 0 ((s.val.length : ℤ) - 2)) := by
  sorry

/-- If there exists a byte c such that s[j] = c for every j with 0 <= j < len(s) (s is constant), then whenever count_good_substrings(s) returns a result r, r = 0.
  Preconditions: 1 <= len(s) <= 100, and for every j with 0 <= j < len(s), 97 <= s[j] <= 122. -/
theorem spec_9 (s : Slice Std.U8) (hs : ValidInput s)
    (hconst : ∃ c : ℕ, ∀ (j a : ℕ), byteAt s j = some a → a = c)
    (r : Std.I64) (h : Aegis.CountGoodSubstrings.count_good_substrings s = ok r) :
    r.val = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : ValidInput s)
    (hconst : ∃ c : ℕ, ∀ (j a : ℕ), byteAt s j = some a → a = c)
    (r : Std.I64) (h : Aegis.CountGoodSubstrings.count_good_substrings s = ok r), r.val = 0) := by
  sorry

/-- Whenever count_good_substrings(s) returns a result r, r = max(0, len(s)-2) if and only if for every index i with 0 <= i and i+2 < len(s), the bytes s[i], s[i+1], s[i+2] are pairwise distinct.
  Preconditions: 1 <= len(s) <= 100, and for every j with 0 <= j < len(s), 97 <= s[j] <= 122. -/
theorem spec_10 (s : Slice Std.U8) (hs : ValidInput s) (r : Std.I64)
    (h : Aegis.CountGoodSubstrings.count_good_substrings s = ok r) :
    r.val = max 0 ((s.val.length : ℤ) - 2) ↔
      ∀ i : ℕ, i + 2 < s.val.length → PairwiseDistinctWindow s i := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (hs : ValidInput s) (r : Std.I64)
    (h : Aegis.CountGoodSubstrings.count_good_substrings s = ok r), r.val = max 0 ((s.val.length : ℤ) - 2) ↔
      ∀ i : ℕ, i + 2 < s.val.length → PairwiseDistinctWindow s i) := by
  sorry

end AegisSpec.CountGoodSubstrings
