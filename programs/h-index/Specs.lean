import Aegis.HIndex.Code.Funs

/-!
# Specifications of `Aegis.HIndex.h_index`

LeetCode problem `h-index`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace AegisSpec.HIndex

def countGe (xs : List Aeneas.Std.I64) (h : ℤ) : ℕ :=
  (xs.filter (fun c => decide (h ≤ c.val))).length

def listMax : List ℤ → ℤ
  | [] => 0
  | x :: xs => xs.foldr max x

def citationSum (citations : Aeneas.Std.Slice Aeneas.Std.I64) : ℤ :=
  (citations.val.map (fun c => c.val)).sum

/-- The function returns a result r, and r is the maximum h such that 0 <= h <= n and C(h) >= h, where C(h) is the number of indices i with 0 <= i < n and citations[i] >= h. (Equivalently, r is the largest h in [0, n] for which at least h papers have at least h citations each.)
  Preconditions: n = len(citations), 1 <= n <= 5000, and 0 <= citations[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_1 (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000) :
    ∃ r : Aeneas.Std.I64,
      Aegis.HIndex.h_index citations = ok r ∧
      (0 ≤ r.val ∧ r.val ≤ (n : ℤ) ∧ (countGe citations.val r.val : ℤ) ≥ r.val) ∧
      (∀ h : ℤ, 0 ≤ h → h ≤ (n : ℤ) → (countGe citations.val h : ℤ) ≥ h → h ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000), ∃ r : Aeneas.Std.I64,
      Aegis.HIndex.h_index citations = ok r ∧
      (0 ≤ r.val ∧ r.val ≤ (n : ℤ) ∧ (countGe citations.val r.val : ℤ) ≥ r.val) ∧
      (∀ h : ℤ, 0 ≤ h → h ≤ (n : ℤ) → (countGe citations.val h : ℤ) ≥ h → h ≤ r.val)) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r and r <= len(citations).
  Preconditions: n = len(citations), 1 <= n <= 5000, and 0 <= citations[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_2 (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000) :
    ∀ r : Aeneas.Std.I64, Aegis.HIndex.h_index citations = ok r → 0 ≤ r.val ∧ r.val ≤ (n : ℤ) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000), ∀ r : Aeneas.Std.I64, Aegis.HIndex.h_index citations = ok r → 0 ≤ r.val ∧ r.val ≤ (n : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, the number of indices i with 0 <= i < n and citations[i] >= r is at least r; i.e., there are at least r distinct papers each cited at least r times.
  Preconditions: n = len(citations), 1 <= n <= 5000, and 0 <= citations[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_3 (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000) :
    ∀ r : Aeneas.Std.I64,
      Aegis.HIndex.h_index citations = ok r → (countGe citations.val r.val : ℤ) ≥ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000), ∀ r : Aeneas.Std.I64,
      Aegis.HIndex.h_index citations = ok r → (countGe citations.val r.val : ℤ) ≥ r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer h with r < h <= n the number of indices i with 0 <= i < n and citations[i] >= h is strictly less than h.
  Preconditions: n = len(citations), 1 <= n <= 5000, and 0 <= citations[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_4 (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000) :
    ∀ r : Aeneas.Std.I64, Aegis.HIndex.h_index citations = ok r →
      ∀ h : ℤ, r.val < h → h ≤ (n : ℤ) → (countGe citations.val h : ℤ) < h := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000), ∀ r : Aeneas.Std.I64, Aegis.HIndex.h_index citations = ok r →
      ∀ h : ℤ, r.val < h → h ≤ (n : ℤ) → (countGe citations.val h : ℤ) < h) := by
  sorry

/-- Whenever the function returns a result r, for every integer h with 0 <= h <= r, the number of indices i with 0 <= i < n and citations[i] >= h is at least h.
  Preconditions: n = len(citations), 1 <= n <= 5000, and 0 <= citations[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_5 (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000) :
    ∀ r : Aeneas.Std.I64, Aegis.HIndex.h_index citations = ok r →
      ∀ h : ℤ, 0 ≤ h → h ≤ r.val → (countGe citations.val h : ℤ) ≥ h := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000), ∀ r : Aeneas.Std.I64, Aegis.HIndex.h_index citations = ok r →
      ∀ h : ℤ, 0 ≤ h → h ≤ r.val → (countGe citations.val h : ℤ) ≥ h) := by
  sorry

/-- Whenever the function returns a result r, r * r <= the sum of citations[i] over all i with 0 <= i < n, the sum being taken over the mathematical integers (not machine integers).
  Preconditions: n = len(citations), 1 <= n <= 5000, and 0 <= citations[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_6 (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000) :
    ∀ r : Aeneas.Std.I64,
      Aegis.HIndex.h_index citations = ok r → r.val * r.val ≤ citationSum citations := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000), ∀ r : Aeneas.Std.I64,
      Aegis.HIndex.h_index citations = ok r → r.val * r.val ≤ citationSum citations) := by
  sorry

/-- Whenever the function returns a result r, r <= max{citations[i] : 0 <= i < n} (the maximum exists because n >= 1).
  Preconditions: n = len(citations), 1 <= n <= 5000, and 0 <= citations[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_7 (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000) :
    ∀ r : Aeneas.Std.I64, Aegis.HIndex.h_index citations = ok r →
      r.val ≤ listMax (citations.val.map (fun c => c.val)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000), ∀ r : Aeneas.Std.I64, Aegis.HIndex.h_index citations = ok r →
      r.val ≤ listMax (citations.val.map (fun c => c.val))) := by
  sorry

/-- Whenever the function returns a result r, r is at most the number of indices i with 0 <= i < n and citations[i] >= 1.
  Preconditions: n = len(citations), 1 <= n <= 5000, and 0 <= citations[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_8 (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000) :
    ∀ r : Aeneas.Std.I64,
      Aegis.HIndex.h_index citations = ok r → r.val ≤ (countGe citations.val 1 : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000), ∀ r : Aeneas.Std.I64,
      Aegis.HIndex.h_index citations = ok r → r.val ≤ (countGe citations.val 1 : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if citations[i] = 0 for every i with 0 <= i < n.
  Preconditions: n = len(citations), 1 <= n <= 5000, and 0 <= citations[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_9 (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000) :
    ∀ r : Aeneas.Std.I64, Aegis.HIndex.h_index citations = ok r →
      (r.val = 0 ↔ ∀ c ∈ citations.val, c.val = 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000), ∀ r : Aeneas.Std.I64, Aegis.HIndex.h_index citations = ok r →
      (r.val = 0 ↔ ∀ c ∈ citations.val, c.val = 0)) := by
  sorry

/-- Whenever the function returns a result r, r = n if and only if citations[i] >= n for every i with 0 <= i < n.
  Preconditions: n = len(citations), 1 <= n <= 5000, and 0 <= citations[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_10 (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000) :
    ∀ r : Aeneas.Std.I64, Aegis.HIndex.h_index citations = ok r →
      (r.val = (n : ℤ) ↔ ∀ c ∈ citations.val, (n : ℤ) ≤ c.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000), ∀ r : Aeneas.Std.I64, Aegis.HIndex.h_index citations = ok r →
      (r.val = (n : ℤ) ↔ ∀ c ∈ citations.val, (n : ℤ) ≤ c.val)) := by
  sorry

/-- Whenever the function returns a result r, if there is an integer c such that citations[i] = c for every i with 0 <= i < n, then r = min(c, n).
  Preconditions: n = len(citations), 1 <= n <= 5000, and 0 <= citations[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_11 (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000) :
    ∀ r : Aeneas.Std.I64, Aegis.HIndex.h_index citations = ok r →
      ∀ c : ℤ, (∀ d ∈ citations.val, d.val = c) → r.val = min c (n : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000), ∀ r : Aeneas.Std.I64, Aegis.HIndex.h_index citations = ok r →
      ∀ c : ℤ, (∀ d ∈ citations.val, d.val = c) → r.val = min c (n : ℤ)) := by
  sorry

/-- For every slice citations satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: n = len(citations), 1 <= n <= 5000, and 0 <= citations[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_12 (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000) :
    ∃ r : Aeneas.Std.I64, Aegis.HIndex.h_index citations = ok r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (citations : Aeneas.Std.Slice Aeneas.Std.I64) (n : ℕ)
    (hn : n = citations.val.length) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 5000)
    (hc : ∀ c ∈ citations.val, 0 ≤ c.val ∧ c.val ≤ 1000), ∃ r : Aeneas.Std.I64, Aegis.HIndex.h_index citations = ok r) := by
  sorry

end AegisSpec.HIndex
