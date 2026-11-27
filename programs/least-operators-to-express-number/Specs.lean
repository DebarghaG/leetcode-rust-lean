import Aegis.LeastOpsExpressTarget.Code.Funs

/-!
# Specifications of `Aegis.LeastOpsExpressTarget.least_ops_express_target`

LeetCode problem `least-operators-to-express-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LeastOpsExpressTarget

  def termCost (p : ℤ × ℤ) : ℕ := (p.2 - 1).natAbs

  def repCost (l : List (ℤ × ℤ)) : ℕ := (l.map termCost).sum + (l.length - 1)

  def IsSignedPowerRep (x target : ℚ) (l : List (ℤ × ℤ)) : Prop :=
    l ≠ [] ∧
    (∀ (s e : ℤ) (tl : List (ℤ × ℤ)), l = (s, e) :: tl → s = 1) ∧
    (∀ p ∈ l, p.1 = 1 ∨ p.1 = -1) ∧
    (l.map (fun p => (p.1 : ℚ) * x ^ p.2)).sum = target

  def IsNonnegSignedPowerRep (x target : ℚ) (l : List (ℤ × ℤ)) : Prop :=
    IsSignedPowerRep x target l ∧ ∀ p ∈ l, 0 ≤ p.2

  def IsLeastCost (x target : ℚ) (r : ℤ) : Prop :=
    (∃ l : List (ℤ × ℤ), IsSignedPowerRep x target l ∧ (repCost l : ℤ) = r) ∧
    ∀ l : List (ℤ × ℤ), IsSignedPowerRep x target l → r ≤ (repCost l : ℤ)

  def IsLeastExp (x target : ℤ) (k : ℕ) : Prop :=
    target ≤ x ^ k ∧ ∀ j : ℕ, j < k → x ^ j < target

  /-- The function returns a result r, and r equals the minimum cost over all signed power representations of target (with respect to x). A signed power representation of target is a finite sequence of m >= 1 terms (s_1,e_1),...,(s_m,e_m) with s_1 = +1, s_j in {+1,-1} for 2 <= j <= m, and integer exponents e_j in Z (where x^e = 1/x^(-e) for e < 0, and x^0 = 1), such that the exact rational sum Sum_{j=1..m} s_j * x^(e_j) equals target. The cost of such a representation is Sum_{j=1..m} |e_j - 1| + (m - 1). (Representations exist, e.g. target copies of x^0 = 1, so the minimum is well defined.)
    Preconditions: x and target are integers with 2 <= x <= 100 and 1 <= target <= 2*10^8. -/
  theorem spec_1 (x target : Std.I64)
      (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8) :
      ∃ r : Std.I64,
        Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r ∧
          IsLeastCost (x.val : ℚ) (target.val : ℚ) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (x target : Std.I64)
        (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
        (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8), ∃ r : Std.I64,
          Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r ∧
            IsLeastCost (x.val : ℚ) (target.val : ℚ) r.val) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r and r <= 2*target - 1.
    Preconditions: 2 <= x <= 100 and 1 <= target <= 2*10^8. -/
  theorem spec_2 (x target : Std.I64)
      (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8) :
      ∀ r : Std.I64,
        Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
          0 ≤ r.val ∧ r.val ≤ 2 * target.val - 1 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (x target : Std.I64)
        (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
        (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8), ∀ r : Std.I64,
          Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
            0 ≤ r.val ∧ r.val ≤ 2 * target.val - 1) := by
    sorry

  /-- Whenever the function returns a result r, r >= k - 1, where k is the smallest non-negative integer with x^k >= target (equivalently x^(k-1) < target <= x^k for k >= 1, and k = 0 when target = 1).
    Preconditions: 2 <= x <= 100 and 1 <= target <= 2*10^8. -/
  theorem spec_3 (x target : Std.I64) (k : ℕ)
      (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8)
      (hk : IsLeastExp x.val target.val k) :
      ∀ r : Std.I64,
        Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
          (k : ℤ) - 1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (x target : Std.I64) (k : ℕ)
        (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
        (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8)
        (hk : IsLeastExp x.val target.val k), ∀ r : Std.I64,
          Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
            (k : ℤ) - 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if target = x.
    Preconditions: 2 <= x <= 100 and 1 <= target <= 2*10^8. -/
  theorem spec_4 (x target : Std.I64)
      (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8) :
      ∀ r : Std.I64,
        Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
          (r.val = 0 ↔ target.val = x.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (x target : Std.I64)
        (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
        (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8), ∀ r : Std.I64,
          Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
            (r.val = 0 ↔ target.val = x.val)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k >= 1, if target = x^k then r = k - 1.
    Preconditions: 2 <= x <= 100 and 1 <= target <= 2*10^8. -/
  theorem spec_5 (x target : Std.I64)
      (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8) :
      ∀ r : Std.I64,
        Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
          ∀ k : ℕ, 1 ≤ k → target.val = x.val ^ k → r.val = (k : ℤ) - 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (x target : Std.I64)
        (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
        (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8), ∀ r : Std.I64,
          Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
            ∀ k : ℕ, 1 ≤ k → target.val = x.val ^ k → r.val = (k : ℤ) - 1) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if target = 1 or target = x*x or target = 2*x.
    Preconditions: 2 <= x <= 100 and 1 <= target <= 2*10^8. -/
  theorem spec_6 (x target : Std.I64)
      (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8) :
      ∀ r : Std.I64,
        Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
          (r.val = 1 ↔
            (target.val = 1 ∨ target.val = x.val * x.val ∨ target.val = 2 * x.val)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (x target : Std.I64)
        (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
        (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8), ∀ r : Std.I64,
          Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
            (r.val = 1 ↔
              (target.val = 1 ∨ target.val = x.val * x.val ∨ target.val = 2 * x.val))) := by
    sorry

  /-- Whenever the function returns a result r, if target < x then r = min(2*target - 1, 2*(x - target)).
    Preconditions: 2 <= x <= 100 and 1 <= target <= 2*10^8. -/
  theorem spec_7 (x target : Std.I64)
      (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8) :
      ∀ r : Std.I64,
        Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
          target.val < x.val →
            r.val = min (2 * target.val - 1) (2 * (x.val - target.val)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (x target : Std.I64)
        (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
        (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8), ∀ r : Std.I64,
          Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
            target.val < x.val →
              r.val = min (2 * target.val - 1) (2 * (x.val - target.val))) := by
    sorry

  /-- Whenever the function returns a result r, there exist m >= 1, signs s_1 = +1 and s_j in {+1,-1} for 2 <= j <= m, and non-negative integers e_1,...,e_m >= 0 such that Sum_{j=1..m} s_j * x^(e_j) = target and Sum_{j=1..m} |e_j - 1| + (m - 1) = r.
    Preconditions: 2 <= x <= 100 and 1 <= target <= 2*10^8. -/
  theorem spec_8 (x target : Std.I64)
      (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8) :
      ∀ r : Std.I64,
        Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
          ∃ l : List (ℤ × ℤ),
            IsNonnegSignedPowerRep (x.val : ℚ) (target.val : ℚ) l ∧ (repCost l : ℤ) = r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (x target : Std.I64)
        (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
        (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8), ∀ r : Std.I64,
          Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
            ∃ l : List (ℤ × ℤ),
              IsNonnegSignedPowerRep (x.val : ℚ) (target.val : ℚ) l ∧ (repCost l : ℤ) = r.val) := by
    sorry

  /-- Whenever the function returns a result r, if target = x + 1 then r = 2.
    Preconditions: 2 <= x <= 100 and 1 <= target <= 2*10^8. -/
  theorem spec_9 (x target : Std.I64)
      (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8) :
      ∀ r : Std.I64,
        Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
          target.val = x.val + 1 → r.val = 2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (x target : Std.I64)
        (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
        (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8), ∀ r : Std.I64,
          Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
            target.val = x.val + 1 → r.val = 2) := by
    sorry

  /-- For every valid pair (x, target) the function returns a result r; it neither overflows, indexes out of bounds, nor panics.
    Preconditions: 2 <= x <= 100 and 1 <= target <= 2*10^8. -/
  theorem spec_10 (x target : Std.I64)
      (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8) :
      ∃ r : Std.I64, Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (x target : Std.I64)
        (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
        (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8), ∃ r : Std.I64, Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every signed power representation of target (m >= 1 terms with first sign +1, other signs in {+1,-1}, and arbitrary integer exponents, whose exact rational value is target), its cost Sum_{j=1..m} |e_j - 1| + (m - 1) is at least r.
    Preconditions: 2 <= x <= 100 and 1 <= target <= 2*10^8. -/
  theorem spec_11 (x target : Std.I64)
      (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8) :
      ∀ r : Std.I64,
        Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
          ∀ l : List (ℤ × ℤ),
            IsSignedPowerRep (x.val : ℚ) (target.val : ℚ) l → r.val ≤ (repCost l : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (x target : Std.I64)
        (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
        (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8), ∀ r : Std.I64,
          Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
            ∀ l : List (ℤ × ℤ),
              IsSignedPowerRep (x.val : ℚ) (target.val : ℚ) l → r.val ≤ (repCost l : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = k + 1.
    Preconditions: 2 <= x <= 100, 1 <= target <= 2*10^8, and target = x^k + 1 for some unique integer k >= 1. -/
  theorem spec_12 (x target : Std.I64) (k : ℕ)
      (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
      (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8)
      (hk : 1 ≤ k) (htk : target.val = x.val ^ k + 1) :
      ∀ r : Std.I64,
        Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
          r.val = (k : ℤ) + 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (x target : Std.I64) (k : ℕ)
        (hx_lo : 2 ≤ x.val) (hx_hi : x.val ≤ 100)
        (ht_lo : 1 ≤ target.val) (ht_hi : target.val ≤ 2 * 10 ^ 8)
        (hk : 1 ≤ k) (htk : target.val = x.val ^ k + 1), ∀ r : Std.I64,
          Aegis.LeastOpsExpressTarget.least_ops_express_target x target = ok r →
            r.val = (k : ℤ) + 1) := by
    sorry

  end AegisSpec.LeastOpsExpressTarget
