import Aegis.SumScores.Code.Funs

/-!
# Specifications of `Aegis.SumScores.sum_scores`

LeetCode problem `sum-of-scores-of-built-strings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open scoped BigOperators

namespace AegisSpec.SumScores

def byteAt (s : Slice Std.U8) (i : Nat) : Nat := ((s.val[i]?).map (fun b => b.val)).getD 0

def LowercaseLetters (s : Slice Std.U8) : Prop :=
  ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122

def IsCommonPrefixLen (s : Slice Std.U8) (j L : Nat) : Prop :=
  L ≤ s.val.length - j ∧ ∀ t, t < L → byteAt s (j + t) = byteAt s t

noncomputable def lcpLen (s : Slice Std.U8) (j : Nat) : Nat :=
  @Nat.findGreatest (fun L => IsCommonPrefixLen s j L) (Classical.decPred _)
    (s.val.length - j)

noncomputable def suffixScore (s : Slice Std.U8) (k : Nat) : Nat :=
  @Nat.findGreatest
    (fun L => L ≤ k ∧ ∀ t, t < L → byteAt s (s.val.length - k + t) = byteAt s t)
    (Classical.decPred _) k

def firstByteCount (s : Slice Std.U8) : Nat :=
  ((Finset.range s.val.length).filter (fun i => 1 ≤ i ∧ byteAt s i = byteAt s 0)).card

def IsLetterPermutation (f : Nat → Nat) : Prop :=
  (∀ x, 97 ≤ x → x ≤ 122 → 97 ≤ f x ∧ f x ≤ 122) ∧
    ∃ g : Nat → Nat,
      (∀ y, 97 ≤ y → y ≤ 122 → 97 ≤ g y ∧ g y ≤ 122) ∧
        (∀ x, 97 ≤ x → x ≤ 122 → g (f x) = x) ∧ ∀ y, 97 ≤ y → y ≤ 122 → f (g y) = y

/-- Let n = len(s). For each k with 1 <= k <= n, let u_k be the suffix of s of length k, defined by u_k[t] = s[n-k+t] for every t with 0 <= t < k. Let score(k) be the largest integer L with 0 <= L <= k such that for every t with 0 <= t < L, u_k[t] = s[t]. Whenever the function returns a result r, r = sum_{k=1}^{n} score(k).
  Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (so s is a nonempty list of lowercase English ASCII letters). -/
theorem spec_1 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hlower : LowercaseLetters s) (r : Std.I64)
    (hres : Aegis.SumScores.sum_scores s = ok r) :
    r.val = (((∑ k ∈ Finset.Icc 1 s.val.length, suffixScore s k) : Nat) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hlower : LowercaseLetters s) (r : Std.I64)
    (hres : Aegis.SumScores.sum_scores s = ok r), r.val = (((∑ k ∈ Finset.Icc 1 s.val.length, suffixScore s k) : Nat) : Int)) := by
  sorry

/-- For every s satisfying the preconditions, the function returns a result r (it does not fail; in particular, no arithmetic overflow, out-of-bounds access, or panic occurs).
  Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (so s is a nonempty list of lowercase English ASCII letters). -/
theorem spec_2 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hlower : LowercaseLetters s) :
    ∃ r : Std.I64, Aegis.SumScores.sum_scores s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hlower : LowercaseLetters s), ∃ r : Std.I64, Aegis.SumScores.sum_scores s = ok r) := by
  sorry

/-- Let n = len(s). Whenever the function returns a result r, n <= r <= n*(n+1)/2.
  Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (so s is a nonempty list of lowercase English ASCII letters). -/
theorem spec_3 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hlower : LowercaseLetters s) (r : Std.I64)
    (hres : Aegis.SumScores.sum_scores s = ok r) :
    (s.val.length : Int) ≤ r.val ∧
      r.val ≤ ((s.val.length * (s.val.length + 1) / 2 : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hlower : LowercaseLetters s) (r : Std.I64)
    (hres : Aegis.SumScores.sum_scores s = ok r), (s.val.length : Int) ≤ r.val ∧
      r.val ≤ ((s.val.length * (s.val.length + 1) / 2 : Nat) : Int)) := by
  sorry

/-- Let n = len(s). Whenever the function returns a result r, r = n*(n+1)/2 if and only if every byte of s is equal to s[0] (that is, for every i with 0 <= i < n, s[i] = s[0]).
  Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (so s is a nonempty list of lowercase English ASCII letters). -/
theorem spec_4 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hlower : LowercaseLetters s) (r : Std.I64)
    (hres : Aegis.SumScores.sum_scores s = ok r) :
    (r.val = ((s.val.length * (s.val.length + 1) / 2 : Nat) : Int) ↔
      ∀ i, i < s.val.length → byteAt s i = byteAt s 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hlower : LowercaseLetters s) (r : Std.I64)
    (hres : Aegis.SumScores.sum_scores s = ok r), (r.val = ((s.val.length * (s.val.length + 1) / 2 : Nat) : Int) ↔
      ∀ i, i < s.val.length → byteAt s i = byteAt s 0)) := by
  sorry

/-- Let n = len(s). Whenever the function returns a result r, r = n if and only if for every i with 1 <= i < n, s[i] != s[0].
  Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (so s is a nonempty list of lowercase English ASCII letters). -/
theorem spec_5 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hlower : LowercaseLetters s) (r : Std.I64)
    (hres : Aegis.SumScores.sum_scores s = ok r) :
    (r.val = (s.val.length : Int) ↔
      ∀ i, 1 ≤ i → i < s.val.length → byteAt s i ≠ byteAt s 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hlower : LowercaseLetters s) (r : Std.I64)
    (hres : Aegis.SumScores.sum_scores s = ok r), (r.val = (s.val.length : Int) ↔
      ∀ i, 1 ≤ i → i < s.val.length → byteAt s i ≠ byteAt s 0)) := by
  sorry

/-- Let n = len(s) and let C be the number of indices i with 1 <= i < n and s[i] = s[0]. Whenever the function returns a result r, r >= n + C.
  Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (so s is a nonempty list of lowercase English ASCII letters). -/
theorem spec_6 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hlower : LowercaseLetters s) (r : Std.I64)
    (hres : Aegis.SumScores.sum_scores s = ok r) :
    (s.val.length : Int) + (firstByteCount s : Int) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hlower : LowercaseLetters s) (r : Std.I64)
    (hres : Aegis.SumScores.sum_scores s = ok r), (s.val.length : Int) + (firstByteCount s : Int) ≤ r.val) := by
  sorry

/-- Let n = len(s). Whenever the function returns a result r, r <= n + sum_{j=1}^{n-1} (if s[j] = s[0] then n-j else 0).
  Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (so s is a nonempty list of lowercase English ASCII letters). -/
theorem spec_7 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hlower : LowercaseLetters s) (r : Std.I64)
    (hres : Aegis.SumScores.sum_scores s = ok r) :
    r.val ≤ (s.val.length : Int) +
      (((∑ j ∈ Finset.Icc 1 (s.val.length - 1),
          (if byteAt s j = byteAt s 0 then s.val.length - j else 0)) : Nat) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hlower : LowercaseLetters s) (r : Std.I64)
    (hres : Aegis.SumScores.sum_scores s = ok r), r.val ≤ (s.val.length : Int) +
      (((∑ j ∈ Finset.Icc 1 (s.val.length - 1),
          (if byteAt s j = byteAt s 0 then s.val.length - j else 0)) : Nat) : Int)) := by
  sorry

/-- Let n = len(s). For each j with 0 <= j < n, let L_j be the largest integer L with 0 <= L <= n-j such that for every t with 0 <= t < L, s[j+t] = s[t]. Whenever the function returns a result r, r = n + sum_{j=1}^{n-1} L_j. Moreover, for every j with 1 <= j < n, L_j = 0 if and only if s[j] != s[0], and if s[j] = s[0] then 1 <= L_j <= n-j.
  Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (so s is a nonempty list of lowercase English ASCII letters). -/
theorem spec_8 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hlower : LowercaseLetters s) (r : Std.I64)
    (hres : Aegis.SumScores.sum_scores s = ok r) :
    r.val = (s.val.length : Int) +
        (((∑ j ∈ Finset.Icc 1 (s.val.length - 1), lcpLen s j) : Nat) : Int) ∧
      (∀ j, 1 ≤ j → j < s.val.length →
        (lcpLen s j = 0 ↔ byteAt s j ≠ byteAt s 0) ∧
          (byteAt s j = byteAt s 0 → 1 ≤ lcpLen s j ∧ lcpLen s j ≤ s.val.length - j)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hlower : LowercaseLetters s) (r : Std.I64)
    (hres : Aegis.SumScores.sum_scores s = ok r), r.val = (s.val.length : Int) +
        (((∑ j ∈ Finset.Icc 1 (s.val.length - 1), lcpLen s j) : Nat) : Int) ∧
      (∀ j, 1 ≤ j → j < s.val.length →
        (lcpLen s j = 0 ↔ byteAt s j ≠ byteAt s 0) ∧
          (byteAt s j = byteAt s 0 → 1 ≤ lcpLen s j ∧ lcpLen s j ≤ s.val.length - j))) := by
  sorry

/-- Let n = len(s). Whenever the function returns a result r, there exist integers L_j for 0 <= j < n such that r = sum_{j=0}^{n-1} L_j and for each j: (1) 0 <= L_j <= n-j; (2) for every t with 0 <= t < L_j, s[j+t] = s[t]; (3) if L_j < n-j then s[j+L_j] != s[L_j]. Each L_j is the LCP length of s[j..n] with s.
  Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (so s is a nonempty list of lowercase English ASCII letters). -/
theorem spec_9 (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hlower : LowercaseLetters s) (r : Std.I64)
    (hres : Aegis.SumScores.sum_scores s = ok r) :
    ∃ L : Nat → Nat,
      r.val = (((∑ j ∈ Finset.range s.val.length, L j) : Nat) : Int) ∧
        ∀ j, j < s.val.length →
          0 ≤ L j ∧ L j ≤ s.val.length - j ∧
            (∀ t, t < L j → byteAt s (j + t) = byteAt s t) ∧
              (L j < s.val.length - j → byteAt s (j + L j) ≠ byteAt s (L j)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
    (hlower : LowercaseLetters s) (r : Std.I64)
    (hres : Aegis.SumScores.sum_scores s = ok r), ∃ L : Nat → Nat,
      r.val = (((∑ j ∈ Finset.range s.val.length, L j) : Nat) : Int) ∧
        ∀ j, j < s.val.length →
          0 ≤ L j ∧ L j ≤ s.val.length - j ∧
            (∀ t, t < L j → byteAt s (j + t) = byteAt s t) ∧
              (L j < s.val.length - j → byteAt s (j + L j) ≠ byteAt s (L j))) := by
  sorry

/-- For every s and every t satisfying the same length and lowercase-letter constraints, if len(t) = len(s) and there exists a bijection f from the set {97,...,122} to itself such that t[i] = f(s[i]) for every i with 0 <= i < len(s), then whenever the function returns r_s on s and r_t on t, r_s = r_t.
  Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (so s is a nonempty list of lowercase English ASCII letters). -/
theorem spec_10 (s t : Slice Std.U8)
    (hs_pos : 1 ≤ s.val.length) (hs_le : s.val.length ≤ 100000)
    (hs_lower : LowercaseLetters s)
    (ht_pos : 1 ≤ t.val.length) (ht_le : t.val.length ≤ 100000)
    (ht_lower : LowercaseLetters t) (hlen : t.val.length = s.val.length)
    (hperm : ∃ f : Nat → Nat,
      IsLetterPermutation f ∧ ∀ i, i < s.val.length → byteAt t i = f (byteAt s i))
    (rs rt : Std.I64)
    (hres_s : Aegis.SumScores.sum_scores s = ok rs)
    (hres_t : Aegis.SumScores.sum_scores t = ok rt) :
    rs = rt := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hs_pos : 1 ≤ s.val.length) (hs_le : s.val.length ≤ 100000)
    (hs_lower : LowercaseLetters s)
    (ht_pos : 1 ≤ t.val.length) (ht_le : t.val.length ≤ 100000)
    (ht_lower : LowercaseLetters t) (hlen : t.val.length = s.val.length)
    (hperm : ∃ f : Nat → Nat,
      IsLetterPermutation f ∧ ∀ i, i < s.val.length → byteAt t i = f (byteAt s i))
    (rs rt : Std.I64)
    (hres_s : Aegis.SumScores.sum_scores s = ok rs)
    (hres_t : Aegis.SumScores.sum_scores t = ok rt), rs = rt) := by
  sorry

end AegisSpec.SumScores
