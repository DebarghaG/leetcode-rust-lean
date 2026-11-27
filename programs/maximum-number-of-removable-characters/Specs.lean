import Aegis.MaximumRemovals.Code.Funs

/-!
# Specifications of `Aegis.MaximumRemovals.maximum_removals`

LeetCode problem `maximum-number-of-removable-characters`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumRemovals

def IsLowerAscii (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def AllLowerAscii (l : List Std.U8) : Prop := ∀ b ∈ l, IsLowerAscii b

def IsSubseq (p t : List Std.U8) : Prop :=
  ∃ idx : ℕ → ℕ,
    (∀ q, q < p.length → idx q < t.length ∧ t[idx q]? = p[q]?) ∧
      (∀ q₁ q₂, q₁ < q₂ → q₂ < p.length → idx q₁ < idx q₂)

def Del (s : List Std.U8) (removable : List Std.I64) (k : ℤ) : List Std.U8 :=
  ((s.zipIdx).filter
      (fun p => (removable.take k.toNat).all (fun x => x.val != (p.2 : ℤ)))).map
    (fun p => p.1)

def IsSubseqDel (s : List Std.U8) (p : List Std.U8) (removable : List Std.I64)
    (k : ℤ) : Prop :=
  IsSubseq p (Del s removable k)

def SurvivesSingle (s : List Std.U8) (p : List Std.U8) (removable : List Std.I64)
    (k : ℤ) : Prop :=
  ∃ j : ℕ,
    j < s.length ∧ s[j]? = p[0]? ∧
      ∀ (i : ℕ), (i : ℤ) < k → ∀ (x : Std.I64), removable[i]? = some x → x.val ≠ (j : ℤ)

def AdmissibleSingleK (s : List Std.U8) (p : List Std.U8)
    (removable : List Std.I64) (k : ℤ) : Prop :=
  0 ≤ k ∧ k ≤ (removable.length : ℤ) ∧ SurvivesSingle s p removable k

/-- Write Del(k), for 0 <= k <= len(removable), for the byte array obtained from s by deleting the characters at positions removable[0], removable[1], ..., removable[k-1] (Del(0) = s). Here p is a subsequence of a byte array t iff there exist indices 0 <= j_0 < j_1 < ... < j_{len(p)-1} < len(t) with t[j_q] = p[q] for every q. The function returns a result r, and r is the maximum integer k such that 0 <= k <= len(removable) and p is a subsequence of Del(k).
  Preconditions: Valid input: len(p) >= 1, len(p) <= len(s), len(s) <= 100000, len(removable) <= len(s), every i with 0 <= i < len(removable) has 0 <= removable[i] < len(s), the values removable[i] are pairwise distinct, s and p consist only of lowercase English letters (ASCII bytes), and p is a subsequence of s before any deletion. -/
theorem spec_1 (s : Slice Std.U8) (p : Slice Std.U8) (removable : Slice Std.I64)
    (h_p_len : 1 ≤ p.val.length)
    (h_p_le_s : p.val.length ≤ s.val.length)
    (h_s_bound : s.val.length ≤ 100000)
    (h_r_len : removable.val.length ≤ s.val.length)
    (h_r_nonneg : ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → 0 ≤ x.val)
    (h_r_lt_s :
      ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → x.val < (s.val.length : ℤ))
    (h_r_distinct : (removable.val.map (fun x => x.val)).Nodup)
    (h_s_ascii : AllLowerAscii s.val)
    (h_p_ascii : AllLowerAscii p.val)
    (h_sub : IsSubseq p.val s.val) :
    ∃ r : Std.I64,
      Aegis.MaximumRemovals.maximum_removals s p removable = ok r ∧
        0 ≤ r.val ∧ r.val ≤ (removable.val.length : ℤ) ∧
          IsSubseqDel s.val p.val removable.val r.val ∧
            ∀ k : ℤ,
              0 ≤ k →
                k ≤ (removable.val.length : ℤ) →
                  IsSubseqDel s.val p.val removable.val k → k ≤ r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (p : Slice Std.U8) (removable : Slice Std.I64)
    (h_p_len : 1 ≤ p.val.length)
    (h_p_le_s : p.val.length ≤ s.val.length)
    (h_s_bound : s.val.length ≤ 100000)
    (h_r_len : removable.val.length ≤ s.val.length)
    (h_r_nonneg : ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → 0 ≤ x.val)
    (h_r_lt_s :
      ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → x.val < (s.val.length : ℤ))
    (h_r_distinct : (removable.val.map (fun x => x.val)).Nodup)
    (h_s_ascii : AllLowerAscii s.val)
    (h_p_ascii : AllLowerAscii p.val)
    (h_sub : IsSubseq p.val s.val), ∃ r : Std.I64,
      Aegis.MaximumRemovals.maximum_removals s p removable = ok r ∧
        0 ≤ r.val ∧ r.val ≤ (removable.val.length : ℤ) ∧
          IsSubseqDel s.val p.val removable.val r.val ∧
            ∀ k : ℤ,
              0 ≤ k →
                k ≤ (removable.val.length : ℤ) →
                  IsSubseqDel s.val p.val removable.val k → k ≤ r.val) := by
  sorry

/-- The function returns a result for every valid input; it does not fail, panic, overflow, or get stuck.
  Preconditions: Valid input: len(p) >= 1, len(p) <= len(s), len(s) <= 100000, len(removable) <= len(s), every i with 0 <= i < len(removable) has 0 <= removable[i] < len(s), the values removable[i] are pairwise distinct, s and p consist only of lowercase English letters (ASCII bytes), and p is a subsequence of s before any deletion. -/
theorem spec_2 (s : Slice Std.U8) (p : Slice Std.U8) (removable : Slice Std.I64)
    (h_p_len : 1 ≤ p.val.length)
    (h_p_le_s : p.val.length ≤ s.val.length)
    (h_s_bound : s.val.length ≤ 100000)
    (h_r_len : removable.val.length ≤ s.val.length)
    (h_r_nonneg : ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → 0 ≤ x.val)
    (h_r_lt_s :
      ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → x.val < (s.val.length : ℤ))
    (h_r_distinct : (removable.val.map (fun x => x.val)).Nodup)
    (h_s_ascii : AllLowerAscii s.val)
    (h_p_ascii : AllLowerAscii p.val)
    (h_sub : IsSubseq p.val s.val) :
    ∃ r : Std.I64, Aegis.MaximumRemovals.maximum_removals s p removable = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (p : Slice Std.U8) (removable : Slice Std.I64)
    (h_p_len : 1 ≤ p.val.length)
    (h_p_le_s : p.val.length ≤ s.val.length)
    (h_s_bound : s.val.length ≤ 100000)
    (h_r_len : removable.val.length ≤ s.val.length)
    (h_r_nonneg : ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → 0 ≤ x.val)
    (h_r_lt_s :
      ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → x.val < (s.val.length : ℤ))
    (h_r_distinct : (removable.val.map (fun x => x.val)).Nodup)
    (h_s_ascii : AllLowerAscii s.val)
    (h_p_ascii : AllLowerAscii p.val)
    (h_sub : IsSubseq p.val s.val), ∃ r : Std.I64, Aegis.MaximumRemovals.maximum_removals s p removable = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(removable).
  Preconditions: Valid input: len(p) >= 1, len(p) <= len(s), len(s) <= 100000, len(removable) <= len(s), every i with 0 <= i < len(removable) has 0 <= removable[i] < len(s), the values removable[i] are pairwise distinct, s and p consist only of lowercase English letters (ASCII bytes), and p is a subsequence of s before any deletion. -/
theorem spec_3 (s : Slice Std.U8) (p : Slice Std.U8) (removable : Slice Std.I64)
    (h_p_len : 1 ≤ p.val.length)
    (h_p_le_s : p.val.length ≤ s.val.length)
    (h_s_bound : s.val.length ≤ 100000)
    (h_r_len : removable.val.length ≤ s.val.length)
    (h_r_nonneg : ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → 0 ≤ x.val)
    (h_r_lt_s :
      ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → x.val < (s.val.length : ℤ))
    (h_r_distinct : (removable.val.map (fun x => x.val)).Nodup)
    (h_s_ascii : AllLowerAscii s.val)
    (h_p_ascii : AllLowerAscii p.val)
    (h_sub : IsSubseq p.val s.val) (r : Std.I64)
    (h_r : Aegis.MaximumRemovals.maximum_removals s p removable = ok r) :
    0 ≤ r.val ∧ r.val ≤ (removable.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (p : Slice Std.U8) (removable : Slice Std.I64)
    (h_p_len : 1 ≤ p.val.length)
    (h_p_le_s : p.val.length ≤ s.val.length)
    (h_s_bound : s.val.length ≤ 100000)
    (h_r_len : removable.val.length ≤ s.val.length)
    (h_r_nonneg : ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → 0 ≤ x.val)
    (h_r_lt_s :
      ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → x.val < (s.val.length : ℤ))
    (h_r_distinct : (removable.val.map (fun x => x.val)).Nodup)
    (h_s_ascii : AllLowerAscii s.val)
    (h_p_ascii : AllLowerAscii p.val)
    (h_sub : IsSubseq p.val s.val) (r : Std.I64)
    (h_r : Aegis.MaximumRemovals.maximum_removals s p removable = ok r), 0 ≤ r.val ∧ r.val ≤ (removable.val.length : ℤ)) := by
  sorry

/-- Write Del(k) for the byte array obtained from s by deleting the characters at positions removable[0], ..., removable[k-1] (nothing is deleted when k=0). Whenever the function returns a result r, p is a subsequence of Del(r).
  Preconditions: Valid input: len(p) >= 1, len(p) <= len(s), len(s) <= 100000, len(removable) <= len(s), every i with 0 <= i < len(removable) has 0 <= removable[i] < len(s), the values removable[i] are pairwise distinct, s and p consist only of lowercase English letters (ASCII bytes), and p is a subsequence of s before any deletion. -/
theorem spec_4 (s : Slice Std.U8) (p : Slice Std.U8) (removable : Slice Std.I64)
    (h_p_len : 1 ≤ p.val.length)
    (h_p_le_s : p.val.length ≤ s.val.length)
    (h_s_bound : s.val.length ≤ 100000)
    (h_r_len : removable.val.length ≤ s.val.length)
    (h_r_nonneg : ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → 0 ≤ x.val)
    (h_r_lt_s :
      ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → x.val < (s.val.length : ℤ))
    (h_r_distinct : (removable.val.map (fun x => x.val)).Nodup)
    (h_s_ascii : AllLowerAscii s.val)
    (h_p_ascii : AllLowerAscii p.val)
    (h_sub : IsSubseq p.val s.val) (r : Std.I64)
    (h_r : Aegis.MaximumRemovals.maximum_removals s p removable = ok r) :
    IsSubseqDel s.val p.val removable.val r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (p : Slice Std.U8) (removable : Slice Std.I64)
    (h_p_len : 1 ≤ p.val.length)
    (h_p_le_s : p.val.length ≤ s.val.length)
    (h_s_bound : s.val.length ≤ 100000)
    (h_r_len : removable.val.length ≤ s.val.length)
    (h_r_nonneg : ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → 0 ≤ x.val)
    (h_r_lt_s :
      ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → x.val < (s.val.length : ℤ))
    (h_r_distinct : (removable.val.map (fun x => x.val)).Nodup)
    (h_s_ascii : AllLowerAscii s.val)
    (h_p_ascii : AllLowerAscii p.val)
    (h_sub : IsSubseq p.val s.val) (r : Std.I64)
    (h_r : Aegis.MaximumRemovals.maximum_removals s p removable = ok r), IsSubseqDel s.val p.val removable.val r.val) := by
  sorry

/-- Write Del(k) for the byte array obtained from s by deleting the characters at positions removable[0], ..., removable[k-1] (nothing is deleted when k=0). Whenever the function returns a result r, for every integer k with r < k <= len(removable), p is not a subsequence of Del(k).
  Preconditions: Valid input: len(p) >= 1, len(p) <= len(s), len(s) <= 100000, len(removable) <= len(s), every i with 0 <= i < len(removable) has 0 <= removable[i] < len(s), the values removable[i] are pairwise distinct, s and p consist only of lowercase English letters (ASCII bytes), and p is a subsequence of s before any deletion. -/
theorem spec_5 (s : Slice Std.U8) (p : Slice Std.U8) (removable : Slice Std.I64)
    (h_p_len : 1 ≤ p.val.length)
    (h_p_le_s : p.val.length ≤ s.val.length)
    (h_s_bound : s.val.length ≤ 100000)
    (h_r_len : removable.val.length ≤ s.val.length)
    (h_r_nonneg : ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → 0 ≤ x.val)
    (h_r_lt_s :
      ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → x.val < (s.val.length : ℤ))
    (h_r_distinct : (removable.val.map (fun x => x.val)).Nodup)
    (h_s_ascii : AllLowerAscii s.val)
    (h_p_ascii : AllLowerAscii p.val)
    (h_sub : IsSubseq p.val s.val) (r : Std.I64)
    (h_r : Aegis.MaximumRemovals.maximum_removals s p removable = ok r) :
    ∀ k : ℤ,
      r.val < k → k ≤ (removable.val.length : ℤ) →
        ¬ IsSubseqDel s.val p.val removable.val k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (p : Slice Std.U8) (removable : Slice Std.I64)
    (h_p_len : 1 ≤ p.val.length)
    (h_p_le_s : p.val.length ≤ s.val.length)
    (h_s_bound : s.val.length ≤ 100000)
    (h_r_len : removable.val.length ≤ s.val.length)
    (h_r_nonneg : ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → 0 ≤ x.val)
    (h_r_lt_s :
      ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → x.val < (s.val.length : ℤ))
    (h_r_distinct : (removable.val.map (fun x => x.val)).Nodup)
    (h_s_ascii : AllLowerAscii s.val)
    (h_p_ascii : AllLowerAscii p.val)
    (h_sub : IsSubseq p.val s.val) (r : Std.I64)
    (h_r : Aegis.MaximumRemovals.maximum_removals s p removable = ok r), ∀ k : ℤ,
      r.val < k → k ≤ (removable.val.length : ℤ) →
        ¬ IsSubseqDel s.val p.val removable.val k) := by
  sorry

/-- Write Del(k) for the byte array obtained from s by deleting the characters at positions removable[0], ..., removable[k-1] (nothing is deleted when k=0). Whenever the function returns a result r, for every integer k with 0 <= k < r, p is a subsequence of Del(k).
  Preconditions: Valid input: len(p) >= 1, len(p) <= len(s), len(s) <= 100000, len(removable) <= len(s), every i with 0 <= i < len(removable) has 0 <= removable[i] < len(s), the values removable[i] are pairwise distinct, s and p consist only of lowercase English letters (ASCII bytes), and p is a subsequence of s before any deletion. -/
theorem spec_6 (s : Slice Std.U8) (p : Slice Std.U8) (removable : Slice Std.I64)
    (h_p_len : 1 ≤ p.val.length)
    (h_p_le_s : p.val.length ≤ s.val.length)
    (h_s_bound : s.val.length ≤ 100000)
    (h_r_len : removable.val.length ≤ s.val.length)
    (h_r_nonneg : ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → 0 ≤ x.val)
    (h_r_lt_s :
      ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → x.val < (s.val.length : ℤ))
    (h_r_distinct : (removable.val.map (fun x => x.val)).Nodup)
    (h_s_ascii : AllLowerAscii s.val)
    (h_p_ascii : AllLowerAscii p.val)
    (h_sub : IsSubseq p.val s.val) (r : Std.I64)
    (h_r : Aegis.MaximumRemovals.maximum_removals s p removable = ok r) :
    ∀ k : ℤ, 0 ≤ k → k < r.val → IsSubseqDel s.val p.val removable.val k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (p : Slice Std.U8) (removable : Slice Std.I64)
    (h_p_len : 1 ≤ p.val.length)
    (h_p_le_s : p.val.length ≤ s.val.length)
    (h_s_bound : s.val.length ≤ 100000)
    (h_r_len : removable.val.length ≤ s.val.length)
    (h_r_nonneg : ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → 0 ≤ x.val)
    (h_r_lt_s :
      ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → x.val < (s.val.length : ℤ))
    (h_r_distinct : (removable.val.map (fun x => x.val)).Nodup)
    (h_s_ascii : AllLowerAscii s.val)
    (h_p_ascii : AllLowerAscii p.val)
    (h_sub : IsSubseq p.val s.val) (r : Std.I64)
    (h_r : Aegis.MaximumRemovals.maximum_removals s p removable = ok r), ∀ k : ℤ, 0 ≤ k → k < r.val → IsSubseqDel s.val p.val removable.val k) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: Valid input: len(p) >= 1, len(p) <= len(s), len(s) <= 100000, len(removable) <= len(s), every i with 0 <= i < len(removable) has 0 <= removable[i] < len(s), the values removable[i] are pairwise distinct, s and p consist only of lowercase English letters (ASCII bytes), p is a subsequence of s before any deletion, and len(p) = len(s). -/
theorem spec_7 (s : Slice Std.U8) (p : Slice Std.U8) (removable : Slice Std.I64)
    (h_p_len : 1 ≤ p.val.length)
    (h_p_le_s : p.val.length ≤ s.val.length)
    (h_s_bound : s.val.length ≤ 100000)
    (h_r_len : removable.val.length ≤ s.val.length)
    (h_r_nonneg : ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → 0 ≤ x.val)
    (h_r_lt_s :
      ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → x.val < (s.val.length : ℤ))
    (h_r_distinct : (removable.val.map (fun x => x.val)).Nodup)
    (h_s_ascii : AllLowerAscii s.val)
    (h_p_ascii : AllLowerAscii p.val)
    (h_sub : IsSubseq p.val s.val) (h_p_eq_s : p.val.length = s.val.length)
    (r : Std.I64)
    (h_r : Aegis.MaximumRemovals.maximum_removals s p removable = ok r) :
    r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (p : Slice Std.U8) (removable : Slice Std.I64)
    (h_p_len : 1 ≤ p.val.length)
    (h_p_le_s : p.val.length ≤ s.val.length)
    (h_s_bound : s.val.length ≤ 100000)
    (h_r_len : removable.val.length ≤ s.val.length)
    (h_r_nonneg : ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → 0 ≤ x.val)
    (h_r_lt_s :
      ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → x.val < (s.val.length : ℤ))
    (h_r_distinct : (removable.val.map (fun x => x.val)).Nodup)
    (h_s_ascii : AllLowerAscii s.val)
    (h_p_ascii : AllLowerAscii p.val)
    (h_sub : IsSubseq p.val s.val) (h_p_eq_s : p.val.length = s.val.length)
    (r : Std.I64)
    (h_r : Aegis.MaximumRemovals.maximum_removals s p removable = ok r), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = len(removable).
  Preconditions: Valid input: len(p) >= 1, len(p) <= len(s), len(s) <= 100000, len(removable) <= len(s), every i with 0 <= i < len(removable) has 0 <= removable[i] < len(s), the values removable[i] are pairwise distinct, s and p consist only of lowercase English letters (ASCII bytes), p is a subsequence of s before any deletion, and after deleting all indices removable[0], removable[1], ..., removable[len(removable)-1] from s, p is still a subsequence. -/
theorem spec_8 (s : Slice Std.U8) (p : Slice Std.U8) (removable : Slice Std.I64)
    (h_p_len : 1 ≤ p.val.length)
    (h_p_le_s : p.val.length ≤ s.val.length)
    (h_s_bound : s.val.length ≤ 100000)
    (h_r_len : removable.val.length ≤ s.val.length)
    (h_r_nonneg : ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → 0 ≤ x.val)
    (h_r_lt_s :
      ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → x.val < (s.val.length : ℤ))
    (h_r_distinct : (removable.val.map (fun x => x.val)).Nodup)
    (h_s_ascii : AllLowerAscii s.val)
    (h_p_ascii : AllLowerAscii p.val)
    (h_sub : IsSubseq p.val s.val)
    (h_all : IsSubseqDel s.val p.val removable.val (removable.val.length : ℤ))
    (r : Std.I64)
    (h_r : Aegis.MaximumRemovals.maximum_removals s p removable = ok r) :
    r.val = (removable.val.length : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (p : Slice Std.U8) (removable : Slice Std.I64)
    (h_p_len : 1 ≤ p.val.length)
    (h_p_le_s : p.val.length ≤ s.val.length)
    (h_s_bound : s.val.length ≤ 100000)
    (h_r_len : removable.val.length ≤ s.val.length)
    (h_r_nonneg : ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → 0 ≤ x.val)
    (h_r_lt_s :
      ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → x.val < (s.val.length : ℤ))
    (h_r_distinct : (removable.val.map (fun x => x.val)).Nodup)
    (h_s_ascii : AllLowerAscii s.val)
    (h_p_ascii : AllLowerAscii p.val)
    (h_sub : IsSubseq p.val s.val)
    (h_all : IsSubseqDel s.val p.val removable.val (removable.val.length : ℤ))
    (r : Std.I64)
    (h_r : Aegis.MaximumRemovals.maximum_removals s p removable = ok r), r.val = (removable.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r is the largest integer k with 0 <= k <= len(removable) such that there exists an index j with 0 <= j < len(s), s[j] = p[0], and for every i with 0 <= i < k, removable[i] != j.
  Preconditions: Valid input: len(p) >= 1, len(p) <= len(s), len(s) <= 100000, len(removable) <= len(s), every i with 0 <= i < len(removable) has 0 <= removable[i] < len(s), the values removable[i] are pairwise distinct, s and p consist only of lowercase English letters (ASCII bytes), p is a subsequence of s before any deletion, and len(p) = 1. -/
theorem spec_9 (s : Slice Std.U8) (p : Slice Std.U8) (removable : Slice Std.I64)
    (h_p_len : 1 ≤ p.val.length)
    (h_p_le_s : p.val.length ≤ s.val.length)
    (h_s_bound : s.val.length ≤ 100000)
    (h_r_len : removable.val.length ≤ s.val.length)
    (h_r_nonneg : ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → 0 ≤ x.val)
    (h_r_lt_s :
      ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → x.val < (s.val.length : ℤ))
    (h_r_distinct : (removable.val.map (fun x => x.val)).Nodup)
    (h_s_ascii : AllLowerAscii s.val)
    (h_p_ascii : AllLowerAscii p.val)
    (h_sub : IsSubseq p.val s.val) (h_p_one : p.val.length = 1)
    (r : Std.I64)
    (h_r : Aegis.MaximumRemovals.maximum_removals s p removable = ok r) :
    AdmissibleSingleK s.val p.val removable.val r.val ∧
      ∀ k : ℤ, AdmissibleSingleK s.val p.val removable.val k → k ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (p : Slice Std.U8) (removable : Slice Std.I64)
    (h_p_len : 1 ≤ p.val.length)
    (h_p_le_s : p.val.length ≤ s.val.length)
    (h_s_bound : s.val.length ≤ 100000)
    (h_r_len : removable.val.length ≤ s.val.length)
    (h_r_nonneg : ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → 0 ≤ x.val)
    (h_r_lt_s :
      ∀ (i : ℕ) (x : Std.I64), removable.val[i]? = some x → x.val < (s.val.length : ℤ))
    (h_r_distinct : (removable.val.map (fun x => x.val)).Nodup)
    (h_s_ascii : AllLowerAscii s.val)
    (h_p_ascii : AllLowerAscii p.val)
    (h_sub : IsSubseq p.val s.val) (h_p_one : p.val.length = 1)
    (r : Std.I64)
    (h_r : Aegis.MaximumRemovals.maximum_removals s p removable = ok r), AdmissibleSingleK s.val p.val removable.val r.val ∧
      ∀ k : ℤ, AdmissibleSingleK s.val p.val removable.val k → k ≤ r.val) := by
  sorry

end AegisSpec.MaximumRemovals
