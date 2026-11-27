import Aegis.AppealSum.Code.Funs

/-!
# Specifications of `Aegis.AppealSum.appeal_sum`

LeetCode problem `total-appeal-of-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.AppealSum

  namespace AegisSpec.AppealSum

  set_option autoImplicit false

  def byteList (s : Slice U8) : List Nat := s.val.map (fun b => b.val)

  def byteAt (s : Slice U8) (i : Nat) : Nat := ((byteList s)[i]?).getD 0

  def Lowercase (s : Slice U8) : Prop :=
    ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122

  def nDistinct (l : List Nat) : Nat := l.dedup.length

  def nDistinctSlice (s : Slice U8) : Nat := nDistinct (byteList s)

  def subAppeal (s : Slice U8) (i j : Nat) : Nat :=
    nDistinct (((byteList s).drop i).take (j + 1 - i))

  def appealTotal (s : Slice U8) : Nat :=
    ∑ i ∈ Finset.range s.val.length, ∑ j ∈ Finset.Ico i s.val.length, subAppeal s i j

  def tri (n : Nat) : Nat := n * (n + 1) / 2

  def tri3 (n : Nat) : Nat := n * (n + 1) * (n + 2) / 6

  def prevIndex (s : Slice U8) (c p : Nat) : Int :=
    match ((byteList s).take p).reverse.findIdx? (fun x => x == c) with
    | none => -1
    | some k => (p : Int) - 1 - (k : Int)

  /-- Let n = len(s), and let T(s) = Σ over all pairs (i,j) with 0 ≤ i ≤ j < n of |{ s[k] | i ≤ k ≤ j }|. The function returns a result r and r = T(s).
    Preconditions: len(s) ≥ 1, len(s) ≤ 100000, and for every i with 0 ≤ i < len(s), 97 ≤ s[i] ≤ 122 (s consists of lowercase English letters). -/
  theorem spec_1 (s : Slice U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
      (hlow : Lowercase s) :
      ∃ r : I64, appeal_sum s = ok r ∧ r.val = (appealTotal s : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
        (hlow : Lowercase s), ∃ r : I64, appeal_sum s = ok r ∧ r.val = (appealTotal s : Int)) := by
    sorry

  /-- For every such s, appeal_sum(s) returns a result r (the call does not fail, panic, go out of bounds, or overflow), and 1 ≤ r ≤ 130001300000. The upper bound is 26 · 100000 · 100001 / 2, which is less than 2^63 - 1, so the returned I64 value cannot overflow.
    Preconditions: len(s) ≥ 1, len(s) ≤ 100000, and for every i with 0 ≤ i < len(s), 97 ≤ s[i] ≤ 122. -/
  theorem spec_2 (s : Slice U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
      (hlow : Lowercase s) :
      ∃ r : I64, appeal_sum s = ok r ∧ 1 ≤ r.val ∧ r.val ≤ 130001300000 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
        (hlow : Lowercase s), ∃ r : I64, appeal_sum s = ok r ∧ 1 ≤ r.val ∧ r.val ≤ 130001300000) := by
    sorry

  /-- Whenever appeal_sum(s) returns a result r, r ≥ N, where n = len(s) and N = n(n+1)/2 is the number of nonempty contiguous substrings of s. This holds because every nonempty substring has appeal at least 1.
    Preconditions: len(s) ≥ 1, len(s) ≤ 100000, and for every i with 0 ≤ i < len(s), 97 ≤ s[i] ≤ 122. -/
  theorem spec_3 (s : Slice U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
      (hlow : Lowercase s) (r : I64) (hr : appeal_sum s = ok r) :
      (tri s.val.length : Int) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
        (hlow : Lowercase s) (r : I64) (hr : appeal_sum s = ok r), (tri s.val.length : Int) ≤ r.val) := by
    sorry

  /-- Whenever appeal_sum(s) returns a result r, r ≤ d · N, where n = len(s), N = n(n+1)/2, and d = |{ s[i] | 0 ≤ i < n }| is the number of distinct bytes in s. Each substring has at most d distinct bytes.
    Preconditions: len(s) ≥ 1, len(s) ≤ 100000, and for every i with 0 ≤ i < len(s), 97 ≤ s[i] ≤ 122. -/
  theorem spec_4 (s : Slice U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
      (hlow : Lowercase s) (r : I64) (hr : appeal_sum s = ok r) :
      r.val ≤ ((nDistinctSlice s * tri s.val.length : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
        (hlow : Lowercase s) (r : I64) (hr : appeal_sum s = ok r), r.val ≤ ((nDistinctSlice s * tri s.val.length : Nat) : Int)) := by
    sorry

  /-- Whenever appeal_sum(s) returns a result r, r ≥ N + d - 1, where n = len(s), N = n(n+1)/2, and d = |{ s[i] | 0 ≤ i < n }|. The whole string contributes d distinct bytes and each of the other N-1 nonempty substrings contributes at least 1.
    Preconditions: len(s) ≥ 1, len(s) ≤ 100000, and for every i with 0 ≤ i < len(s), 97 ≤ s[i] ≤ 122. -/
  theorem spec_5 (s : Slice U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
      (hlow : Lowercase s) (r : I64) (hr : appeal_sum s = ok r) :
      ((tri s.val.length + nDistinctSlice s - 1 : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
        (hlow : Lowercase s) (r : I64) (hr : appeal_sum s = ok r), ((tri s.val.length + nDistinctSlice s - 1 : Nat) : Int) ≤ r.val) := by
    sorry

  /-- Whenever appeal_sum(s) returns a result r, r = 1.
    Preconditions: len(s) = 1 and 97 ≤ s[0] ≤ 122. -/
  theorem spec_6 (s : Slice U8) (hlen : s.val.length = 1) (hlow : Lowercase s)
      (r : I64) (hr : appeal_sum s = ok r) : r.val = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice U8) (hlen : s.val.length = 1) (hlow : Lowercase s)
        (r : I64) (hr : appeal_sum s = ok r), r.val = 1) := by
    sorry

  /-- Whenever appeal_sum(s) returns a result r, if s[0] = s[1] then r = 3, and if s[0] ≠ s[1] then r = 4.
    Preconditions: len(s) = 2 and for every i with 0 ≤ i < 2, 97 ≤ s[i] ≤ 122. -/
  theorem spec_7 (s : Slice U8) (hlen : s.val.length = 2) (hlow : Lowercase s)
      (r : I64) (hr : appeal_sum s = ok r) :
      (byteAt s 0 = byteAt s 1 → r.val = 3) ∧ (byteAt s 0 ≠ byteAt s 1 → r.val = 4) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice U8) (hlen : s.val.length = 2) (hlow : Lowercase s)
        (r : I64) (hr : appeal_sum s = ok r), (byteAt s 0 = byteAt s 1 → r.val = 3) ∧ (byteAt s 0 ≠ byteAt s 1 → r.val = 4)) := by
    sorry

  /-- Whenever appeal_sum(s) returns a result r, r = N if and only if s[0] = s[1] = ... = s[n-1], where n = len(s) and N = n(n+1)/2.
    Preconditions: len(s) ≥ 1, len(s) ≤ 100000, and for every i with 0 ≤ i < len(s), 97 ≤ s[i] ≤ 122. -/
  theorem spec_8 (s : Slice U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
      (hlow : Lowercase s) (r : I64) (hr : appeal_sum s = ok r) :
      (r.val = (tri s.val.length : Int)) ↔
        (∀ i j, i < s.val.length → j < s.val.length → byteAt s i = byteAt s j) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
        (hlow : Lowercase s) (r : I64) (hr : appeal_sum s = ok r), (r.val = (tri s.val.length : Int)) ↔
          (∀ i j, i < s.val.length → j < s.val.length → byteAt s i = byteAt s j)) := by
    sorry

  /-- Whenever appeal_sum(s) returns a result r, r = n(n+1)(n+2)/6 if and only if for every pair i,j with 0 ≤ i < j < n, s[i] ≠ s[j], where n = len(s).
    Preconditions: len(s) ≥ 1, len(s) ≤ 26, and for every i with 0 ≤ i < len(s), 97 ≤ s[i] ≤ 122. -/
  theorem spec_9 (s : Slice U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 26)
      (hlow : Lowercase s) (r : I64) (hr : appeal_sum s = ok r) :
      (r.val = (tri3 s.val.length : Int)) ↔
        (∀ i j, i < j → j < s.val.length → byteAt s i ≠ byteAt s j) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 26)
        (hlow : Lowercase s) (r : I64) (hr : appeal_sum s = ok r), (r.val = (tri3 s.val.length : Int)) ↔
          (∀ i j, i < j → j < s.val.length → byteAt s i ≠ byteAt s j)) := by
    sorry

  /-- Whenever appeal_sum(s) returns a result r, r ≤ n(n+1)(n+2)/6, where n = len(s). A substring of length L has appeal at most L, and the sum of the lengths of all nonempty substrings is n(n+1)(n+2)/6.
    Preconditions: len(s) ≥ 1, len(s) ≤ 100000, and for every i with 0 ≤ i < len(s), 97 ≤ s[i] ≤ 122. -/
  theorem spec_10 (s : Slice U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
      (hlow : Lowercase s) (r : I64) (hr : appeal_sum s = ok r) :
      r.val ≤ (tri3 s.val.length : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
        (hlow : Lowercase s) (r : I64) (hr : appeal_sum s = ok r), r.val ≤ (tri3 s.val.length : Int)) := by
    sorry

  /-- Whenever appeal_sum(s) returns a result r, r = Σ_{c=97}^{122} Σ_{p : 0 ≤ p < n and s[p] = c} (p - prev_c(p)) · (n - p), where n = len(s) and prev_c(p) is the largest index q < p with s[q] = c, or -1 if no such q exists.
    Preconditions: len(s) ≥ 1, len(s) ≤ 100000, and for every i with 0 ≤ i < len(s), 97 ≤ s[i] ≤ 122. -/
  theorem spec_11 (s : Slice U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
      (hlow : Lowercase s) (r : I64) (hr : appeal_sum s = ok r) :
      r.val = ∑ c ∈ Finset.Icc 97 122,
        (∑ p ∈ (Finset.range s.val.length).filter (fun p => byteAt s p = c),
          ((p : Int) - prevIndex s c p) * ((s.val.length : Int) - (p : Int))) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice U8) (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
        (hlow : Lowercase s) (r : I64) (hr : appeal_sum s = ok r), r.val = ∑ c ∈ Finset.Icc 97 122,
          (∑ p ∈ (Finset.range s.val.length).filter (fun p => byteAt s p = c),
            ((p : Int) - prevIndex s c p) * ((s.val.length : Int) - (p : Int)))) := by
    sorry

  /-- Whenever appeal_sum(s) returns r_s and appeal_sum(t) returns r_t, r_s = r_t.
    Preconditions: len(s) = len(t) = n with 1 ≤ n ≤ 100000, all bytes of s and t satisfy 97 ≤ byte ≤ 122, and for every i with 0 ≤ i < n, t[i] = s[n-1-i]. -/
  theorem spec_12 (s t : Slice U8) (hlen_eq : s.val.length = t.val.length)
      (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
      (hlow_s : Lowercase s) (hlow_t : Lowercase t)
      (hrev : ∀ i, i < s.val.length → byteAt t i = byteAt s (s.val.length - 1 - i))
      (rs rt : I64) (hrs : appeal_sum s = ok rs) (hrt : appeal_sum t = ok rt) :
      rs.val = rt.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s t : Slice U8) (hlen_eq : s.val.length = t.val.length)
        (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
        (hlow_s : Lowercase s) (hlow_t : Lowercase t)
        (hrev : ∀ i, i < s.val.length → byteAt t i = byteAt s (s.val.length - 1 - i))
        (rs rt : I64) (hrs : appeal_sum s = ok rs) (hrt : appeal_sum t = ok rt), rs.val = rt.val) := by
    sorry

  /-- Whenever appeal_sum(s) returns r_s and appeal_sum(t) returns r_t, r_s ≤ r_t; moreover, if len(s) < len(t), then r_s < r_t.
    Preconditions: len(s) ≥ 1, len(s) ≤ 100000, len(t) ≥ 1, len(t) ≤ 100000, for every i with 0 ≤ i < len(s), 97 ≤ s[i] ≤ 122, for every i with 0 ≤ i < len(t), 97 ≤ t[i] ≤ 122, and s occurs as a contiguous substring of t: there exists k with 0 ≤ k and k + len(s) ≤ len(t) such that for every i with 0 ≤ i < len(s), t[k+i] = s[i]. -/
  theorem spec_13 (s t : Slice U8) (hsl1 : 1 ≤ s.val.length) (hsl2 : s.val.length ≤ 100000)
      (htl1 : 1 ≤ t.val.length) (htl2 : t.val.length ≤ 100000)
      (hlow_s : Lowercase s) (hlow_t : Lowercase t)
      (hsub : ∃ k : Nat, k + s.val.length ≤ t.val.length ∧
        ∀ i, i < s.val.length → byteAt t (k + i) = byteAt s i)
      (rs rt : I64) (hrs : appeal_sum s = ok rs) (hrt : appeal_sum t = ok rt) :
      rs.val ≤ rt.val ∧ (s.val.length < t.val.length → rs.val < rt.val) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s t : Slice U8) (hsl1 : 1 ≤ s.val.length) (hsl2 : s.val.length ≤ 100000)
        (htl1 : 1 ≤ t.val.length) (htl2 : t.val.length ≤ 100000)
        (hlow_s : Lowercase s) (hlow_t : Lowercase t)
        (hsub : ∃ k : Nat, k + s.val.length ≤ t.val.length ∧
          ∀ i, i < s.val.length → byteAt t (k + i) = byteAt s i)
        (rs rt : I64) (hrs : appeal_sum s = ok rs) (hrt : appeal_sum t = ok rt), rs.val ≤ rt.val ∧ (s.val.length < t.val.length → rs.val < rt.val)) := by
    sorry

  end AegisSpec.AppealSum
