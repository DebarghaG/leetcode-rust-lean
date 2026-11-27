import Aegis.UniquePaths.Code.Funs

/-!
# Specifications of `Aegis.UniquePaths.unique_paths`

LeetCode problem `unique-paths`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.UniquePaths

  def pathsCount (m n : ℤ) : ℤ :=
    ((m + n - 2).toNat.choose (m - 1).toNat : ℤ)

  def centralBinom (k : ℤ) : ℤ :=
    (k.toNat.choose (k.toNat / 2) : ℤ)

  def i64OfInt (z : ℤ) : Std.I64 :=
    ⟨BitVec.ofInt 64 z⟩

  /-- Whenever unique_paths m n returns a result r, r equals the binomial coefficient C(m+n-2, m-1) = (m+n-2)! / ((m-1)! (n-1)!).
    Preconditions: 1 <= m <= 100 and 1 <= n <= 100. -/
  theorem spec_1 (m n : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100) :
      ∀ r : Std.I64, Aegis.UniquePaths.unique_paths m n = ok r →
        r.val = pathsCount m.val n.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (m n : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100), ∀ r : Std.I64, Aegis.UniquePaths.unique_paths m n = ok r →
          r.val = pathsCount m.val n.val) := by
    sorry

  /-- unique_paths m n returns a result r (it does not fail).
    Preconditions: 1 <= m <= 100, 1 <= n <= 100, and C(m+n-2, m-1) <= 2^63 - 1. -/
  theorem spec_2 (m n : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
      (hbound : pathsCount m.val n.val ≤ 2 ^ 63 - 1) :
      ∃ r : Std.I64, Aegis.UniquePaths.unique_paths m n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (m n : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
        (hbound : pathsCount m.val n.val ≤ 2 ^ 63 - 1), ∃ r : Std.I64, Aegis.UniquePaths.unique_paths m n = ok r) := by
    sorry

  /-- unique_paths m n does not return a result (it fails).
    Preconditions: 1 <= m <= 100, 1 <= n <= 100, and C(m+n-2, m-1) > 2^63 - 1. -/
  theorem spec_3 (m n : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
      (hbound : 2 ^ 63 - 1 < pathsCount m.val n.val) :
      ¬ ∃ r : Std.I64, Aegis.UniquePaths.unique_paths m n = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (m n : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
        (hbound : 2 ^ 63 - 1 < pathsCount m.val n.val), ¬ ∃ r : Std.I64, Aegis.UniquePaths.unique_paths m n = ok r) := by
    sorry

  /-- unique_paths m n returns a result r1, unique_paths n m returns a result r2, and r1 = r2.
    Preconditions: 1 <= m <= 100, 1 <= n <= 100, and C(m+n-2, m-1) <= 2^63 - 1. -/
  theorem spec_4 (m n : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
      (hbound : pathsCount m.val n.val ≤ 2 ^ 63 - 1) :
      ∃ r1 r2 : Std.I64,
        Aegis.UniquePaths.unique_paths m n = ok r1 ∧
          Aegis.UniquePaths.unique_paths n m = ok r2 ∧ r1.val = r2.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (m n : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
        (hbound : pathsCount m.val n.val ≤ 2 ^ 63 - 1), ∃ r1 r2 : Std.I64,
          Aegis.UniquePaths.unique_paths m n = ok r1 ∧
            Aegis.UniquePaths.unique_paths n m = ok r2 ∧ r1.val = r2.val) := by
    sorry

  /-- unique_paths m n returns a result r, unique_paths (m-1) n returns a result r1, unique_paths m (n-1) returns a result r2, and r = r1 + r2.
    Preconditions: 2 <= m <= 100, 2 <= n <= 100, and C(m+n-2, m-1) <= 2^63 - 1. -/
  theorem spec_5 (m n : Std.I64) (hm_lo : 2 ≤ m.val) (hm_hi : m.val ≤ 100)
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
      (hbound : pathsCount m.val n.val ≤ 2 ^ 63 - 1) :
      ∃ r r1 r2 : Std.I64,
        Aegis.UniquePaths.unique_paths m n = ok r ∧
          Aegis.UniquePaths.unique_paths (i64OfInt (m.val - 1)) n = ok r1 ∧
            Aegis.UniquePaths.unique_paths m (i64OfInt (n.val - 1)) = ok r2 ∧
              r.val = r1.val + r2.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (m n : Std.I64) (hm_lo : 2 ≤ m.val) (hm_hi : m.val ≤ 100)
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
        (hbound : pathsCount m.val n.val ≤ 2 ^ 63 - 1), ∃ r r1 r2 : Std.I64,
          Aegis.UniquePaths.unique_paths m n = ok r ∧
            Aegis.UniquePaths.unique_paths (i64OfInt (m.val - 1)) n = ok r1 ∧
              Aegis.UniquePaths.unique_paths m (i64OfInt (n.val - 1)) = ok r2 ∧
                r.val = r1.val + r2.val) := by
    sorry

  /-- unique_paths m1 n returns a result r1, unique_paths m2 n returns a result r2, and r1 <= r2.
    Preconditions: 1 <= n <= 100, 1 <= m1 <= m2 <= 100, and C(m2+n-2, m2-1) <= 2^63 - 1. -/
  theorem spec_6 (n m1 m2 : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
      (h1_lo : 1 ≤ m1.val) (h12 : m1.val ≤ m2.val) (h2_hi : m2.val ≤ 100)
      (hbound : pathsCount m2.val n.val ≤ 2 ^ 63 - 1) :
      ∃ r1 r2 : Std.I64,
        Aegis.UniquePaths.unique_paths m1 n = ok r1 ∧
          Aegis.UniquePaths.unique_paths m2 n = ok r2 ∧ r1.val ≤ r2.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n m1 m2 : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
        (h1_lo : 1 ≤ m1.val) (h12 : m1.val ≤ m2.val) (h2_hi : m2.val ≤ 100)
        (hbound : pathsCount m2.val n.val ≤ 2 ^ 63 - 1), ∃ r1 r2 : Std.I64,
          Aegis.UniquePaths.unique_paths m1 n = ok r1 ∧
            Aegis.UniquePaths.unique_paths m2 n = ok r2 ∧ r1.val ≤ r2.val) := by
    sorry

  /-- unique_paths m n1 returns a result r1, unique_paths m n2 returns a result r2, and r1 <= r2.
    Preconditions: 1 <= m <= 100, 1 <= n1 <= n2 <= 100, and C(m+n2-2, m-1) <= 2^63 - 1. -/
  theorem spec_7 (m n1 n2 : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
      (h1_lo : 1 ≤ n1.val) (h12 : n1.val ≤ n2.val) (h2_hi : n2.val ≤ 100)
      (hbound : pathsCount m.val n2.val ≤ 2 ^ 63 - 1) :
      ∃ r1 r2 : Std.I64,
        Aegis.UniquePaths.unique_paths m n1 = ok r1 ∧
          Aegis.UniquePaths.unique_paths m n2 = ok r2 ∧ r1.val ≤ r2.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (m n1 n2 : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
        (h1_lo : 1 ≤ n1.val) (h12 : n1.val ≤ n2.val) (h2_hi : n2.val ≤ 100)
        (hbound : pathsCount m.val n2.val ≤ 2 ^ 63 - 1), ∃ r1 r2 : Std.I64,
          Aegis.UniquePaths.unique_paths m n1 = ok r1 ∧
            Aegis.UniquePaths.unique_paths m n2 = ok r2 ∧ r1.val ≤ r2.val) := by
    sorry

  /-- unique_paths m n returns a result r and r >= m + n - 2.
    Preconditions: 2 <= m <= 100, 2 <= n <= 100, and C(m+n-2, m-1) <= 2^63 - 1. -/
  theorem spec_8 (m n : Std.I64) (hm_lo : 2 ≤ m.val) (hm_hi : m.val ≤ 100)
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
      (hbound : pathsCount m.val n.val ≤ 2 ^ 63 - 1) :
      ∃ r : Std.I64,
        Aegis.UniquePaths.unique_paths m n = ok r ∧ m.val + n.val - 2 ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (m n : Std.I64) (hm_lo : 2 ≤ m.val) (hm_hi : m.val ≤ 100)
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
        (hbound : pathsCount m.val n.val ≤ 2 ^ 63 - 1), ∃ r : Std.I64,
          Aegis.UniquePaths.unique_paths m n = ok r ∧ m.val + n.val - 2 ≤ r.val) := by
    sorry

  /-- unique_paths m n returns a result r and r <= C(m+n-2, floor((m+n-2)/2)) (as mathematical integers).
    Preconditions: 1 <= m <= 100, 1 <= n <= 100, and C(m+n-2, m-1) <= 2^63 - 1. -/
  theorem spec_9 (m n : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
      (hbound : pathsCount m.val n.val ≤ 2 ^ 63 - 1) :
      ∃ r : Std.I64,
        Aegis.UniquePaths.unique_paths m n = ok r ∧
          r.val ≤ centralBinom (m.val + n.val - 2) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (m n : Std.I64) (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
        (hbound : pathsCount m.val n.val ≤ 2 ^ 63 - 1), ∃ r : Std.I64,
          Aegis.UniquePaths.unique_paths m n = ok r ∧
            r.val ≤ centralBinom (m.val + n.val - 2)) := by
    sorry

  end AegisSpec.UniquePaths
