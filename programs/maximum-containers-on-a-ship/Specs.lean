import Aegis.MaxContainers.Code.Funs

/-!
# Specifications of `Aegis.MaxContainers.max_containers`

LeetCode problem `maximum-containers-on-a-ship`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxContainers

def qdiv (a b : ℤ) : ℤ := a / b

/-- Whenever the function returns a result r, interpreting n, w, maxWeight, and r as mathematical integers, r = min(n * n, floor(maxWeight / w)), where floor(maxWeight / w) is the integer quotient of maxWeight divided by w, equivalently the greatest integer q with q * w <= maxWeight.
  Preconditions: n, w, and maxWeight are integers satisfying 1 <= n <= 1000, 1 <= w <= 1000, and 1 <= maxWeight <= 10^9. -/
theorem spec_1 (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9) :
    ∀ r : Std.I64,
      Aegis.MaxContainers.max_containers n w maxWeight = ok r →
      r.val = min (n.val * n.val) (qdiv maxWeight.val w.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9), ∀ r : Std.I64,
      Aegis.MaxContainers.max_containers n w maxWeight = ok r →
      r.val = min (n.val * n.val) (qdiv maxWeight.val w.val)) := by
  sorry

/-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
  Preconditions: n, w, and maxWeight are integers satisfying 1 <= n <= 1000, 1 <= w <= 1000, and 1 <= maxWeight <= 10^9. -/
theorem spec_2 (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9) :
    ∃ r : Std.I64, Aegis.MaxContainers.max_containers n w maxWeight = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9), ∃ r : Std.I64, Aegis.MaxContainers.max_containers n w maxWeight = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= n * n.
  Preconditions: n, w, and maxWeight are integers satisfying 1 <= n <= 1000, 1 <= w <= 1000, and 1 <= maxWeight <= 10^9. -/
theorem spec_3 (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9) :
    ∀ r : Std.I64,
      Aegis.MaxContainers.max_containers n w maxWeight = ok r →
      r.val ≤ n.val * n.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9), ∀ r : Std.I64,
      Aegis.MaxContainers.max_containers n w maxWeight = ok r →
      r.val ≤ n.val * n.val) := by
  sorry

/-- Whenever the function returns a result r, r <= floor(maxWeight / w).
  Preconditions: n, w, and maxWeight are integers satisfying 1 <= n <= 1000, 1 <= w <= 1000, and 1 <= maxWeight <= 10^9. -/
theorem spec_4 (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9) :
    ∀ r : Std.I64,
      Aegis.MaxContainers.max_containers n w maxWeight = ok r →
      r.val ≤ qdiv maxWeight.val w.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9), ∀ r : Std.I64,
      Aegis.MaxContainers.max_containers n w maxWeight = ok r →
      r.val ≤ qdiv maxWeight.val w.val) := by
  sorry

/-- Whenever the function returns a result r, r * w <= maxWeight.
  Preconditions: n, w, and maxWeight are integers satisfying 1 <= n <= 1000, 1 <= w <= 1000, and 1 <= maxWeight <= 10^9. -/
theorem spec_5 (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9) :
    ∀ r : Std.I64,
      Aegis.MaxContainers.max_containers n w maxWeight = ok r →
      r.val * w.val ≤ maxWeight.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9), ∀ r : Std.I64,
      Aegis.MaxContainers.max_containers n w maxWeight = ok r →
      r.val * w.val ≤ maxWeight.val) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: n, w, and maxWeight are integers satisfying 1 <= n <= 1000, 1 <= w <= 1000, and 1 <= maxWeight <= 10^9. -/
theorem spec_6 (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9) :
    ∀ r : Std.I64,
      Aegis.MaxContainers.max_containers n w maxWeight = ok r →
      0 ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9), ∀ r : Std.I64,
      Aegis.MaxContainers.max_containers n w maxWeight = ok r →
      0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer k with r < k <= n * n, we have k * w > maxWeight.
  Preconditions: n, w, and maxWeight are integers satisfying 1 <= n <= 1000, 1 <= w <= 1000, and 1 <= maxWeight <= 10^9. -/
theorem spec_7 (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9) :
    ∀ r : Std.I64,
      Aegis.MaxContainers.max_containers n w maxWeight = ok r →
      ∀ k : ℤ, r.val < k → k ≤ n.val * n.val → maxWeight.val < k * w.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9), ∀ r : Std.I64,
      Aegis.MaxContainers.max_containers n w maxWeight = ok r →
      ∀ k : ℤ, r.val < k → k ≤ n.val * n.val → maxWeight.val < k * w.val) := by
  sorry

/-- Whenever the function returns a result r, r = n * n if and only if n * n * w <= maxWeight.
  Preconditions: n, w, and maxWeight are integers satisfying 1 <= n <= 1000, 1 <= w <= 1000, and 1 <= maxWeight <= 10^9. -/
theorem spec_8 (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9) :
    ∀ r : Std.I64,
      Aegis.MaxContainers.max_containers n w maxWeight = ok r →
      (r.val = n.val * n.val ↔ n.val * n.val * w.val ≤ maxWeight.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9), ∀ r : Std.I64,
      Aegis.MaxContainers.max_containers n w maxWeight = ok r →
      (r.val = n.val * n.val ↔ n.val * n.val * w.val ≤ maxWeight.val)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if maxWeight < w.
  Preconditions: n, w, and maxWeight are integers satisfying 1 <= n <= 1000, 1 <= w <= 1000, and 1 <= maxWeight <= 10^9. -/
theorem spec_9 (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9) :
    ∀ r : Std.I64,
      Aegis.MaxContainers.max_containers n w maxWeight = ok r →
      (r.val = 0 ↔ maxWeight.val < w.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9), ∀ r : Std.I64,
      Aegis.MaxContainers.max_containers n w maxWeight = ok r →
      (r.val = 0 ↔ maxWeight.val < w.val)) := by
  sorry

/-- Whenever the function returns a result r, if floor(maxWeight / w) < n * n, then r = floor(maxWeight / w).
  Preconditions: n, w, and maxWeight are integers satisfying 1 <= n <= 1000, 1 <= w <= 1000, and 1 <= maxWeight <= 10^9. -/
theorem spec_10 (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9) :
    ∀ r : Std.I64,
      Aegis.MaxContainers.max_containers n w maxWeight = ok r →
      qdiv maxWeight.val w.val < n.val * n.val → r.val = qdiv maxWeight.val w.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n w maxWeight : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9), ∀ r : Std.I64,
      Aegis.MaxContainers.max_containers n w maxWeight = ok r →
      qdiv maxWeight.val w.val < n.val * n.val → r.val = qdiv maxWeight.val w.val) := by
  sorry

/-- If the function returns r1 on input (n, w, m1) and returns r2 on input (n, w, m2), then r1 <= r2.
  Preconditions: n, w, m1, and m2 are integers with 1 <= n <= 1000, 1 <= w <= 1000, 1 <= m1 <= m2 <= 10^9. -/
theorem spec_11 (n w m1 m2 : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm1_lo : 1 ≤ m1.val) (hm12 : m1.val ≤ m2.val) (hm2_hi : m2.val ≤ 10 ^ 9) :
    ∀ r1 r2 : Std.I64,
      Aegis.MaxContainers.max_containers n w m1 = ok r1 →
      Aegis.MaxContainers.max_containers n w m2 = ok r2 →
      r1.val ≤ r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n w m1 m2 : Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm1_lo : 1 ≤ m1.val) (hm12 : m1.val ≤ m2.val) (hm2_hi : m2.val ≤ 10 ^ 9), ∀ r1 r2 : Std.I64,
      Aegis.MaxContainers.max_containers n w m1 = ok r1 →
      Aegis.MaxContainers.max_containers n w m2 = ok r2 →
      r1.val ≤ r2.val) := by
  sorry

/-- If the function returns r1 on input (n1, w, maxWeight) and returns r2 on input (n2, w, maxWeight), then r1 <= r2.
  Preconditions: n1, n2, w, and maxWeight are integers with 1 <= n1 <= n2 <= 1000, 1 <= w <= 1000, and 1 <= maxWeight <= 10^9. -/
theorem spec_12 (n1 n2 w maxWeight : Std.I64)
    (hn1_lo : 1 ≤ n1.val) (hn12 : n1.val ≤ n2.val) (hn2_hi : n2.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9) :
    ∀ r1 r2 : Std.I64,
      Aegis.MaxContainers.max_containers n1 w maxWeight = ok r1 →
      Aegis.MaxContainers.max_containers n2 w maxWeight = ok r2 →
      r1.val ≤ r2.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n1 n2 w maxWeight : Std.I64)
    (hn1_lo : 1 ≤ n1.val) (hn12 : n1.val ≤ n2.val) (hn2_hi : n2.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9), ∀ r1 r2 : Std.I64,
      Aegis.MaxContainers.max_containers n1 w maxWeight = ok r1 →
      Aegis.MaxContainers.max_containers n2 w maxWeight = ok r2 →
      r1.val ≤ r2.val) := by
  sorry

/-- If the function returns r1 on input (n1, w, maxWeight) and returns r2 on input (n2, w, maxWeight), and if n1 * n1 >= floor(maxWeight / w) and n2 * n2 >= floor(maxWeight / w), then r1 = r2 = floor(maxWeight / w).
  Preconditions: n1, n2, w, and maxWeight are integers with 1 <= n1 <= 1000, 1 <= n2 <= 1000, 1 <= w <= 1000, and 1 <= maxWeight <= 10^9. -/
theorem spec_13 (n1 n2 w maxWeight : Std.I64)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9) :
    ∀ r1 r2 : Std.I64,
      Aegis.MaxContainers.max_containers n1 w maxWeight = ok r1 →
      Aegis.MaxContainers.max_containers n2 w maxWeight = ok r2 →
      qdiv maxWeight.val w.val ≤ n1.val * n1.val →
      qdiv maxWeight.val w.val ≤ n2.val * n2.val →
      r1.val = qdiv maxWeight.val w.val ∧ r2.val = qdiv maxWeight.val w.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n1 n2 w maxWeight : Std.I64)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000)
    (hw_lo : 1 ≤ w.val) (hw_hi : w.val ≤ 1000)
    (hm_lo : 1 ≤ maxWeight.val) (hm_hi : maxWeight.val ≤ 10 ^ 9), ∀ r1 r2 : Std.I64,
      Aegis.MaxContainers.max_containers n1 w maxWeight = ok r1 →
      Aegis.MaxContainers.max_containers n2 w maxWeight = ok r2 →
      qdiv maxWeight.val w.val ≤ n1.val * n1.val →
      qdiv maxWeight.val w.val ≤ n2.val * n2.val →
      r1.val = qdiv maxWeight.val w.val ∧ r2.val = qdiv maxWeight.val w.val) := by
  sorry

end AegisSpec.MaxContainers
