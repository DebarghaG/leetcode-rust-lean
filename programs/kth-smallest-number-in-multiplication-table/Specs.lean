import Aegis.FindKthNumber.Code.Funs

/-!
# Specifications of `Aegis.FindKthNumber.find_kth_number`

LeetCode problem `kth-smallest-number-in-multiplication-table`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.FindKthNumber

namespace AegisSpec.FindKthNumber

def productsList (m n : ℕ) : List ℕ :=
  (List.range m).flatMap (fun i => (List.range n).map (fun j => (i + 1) * (j + 1)))

def countLeq (m n x : ℤ) : ℤ :=
  (((productsList m.toNat n.toNat).filter (fun p => (p : ℤ) ≤ x)).length : ℤ)

/-- The function returns a result r such that, letting C(x) be the number of integer pairs (i,j) with 1 <= i <= m, 1 <= j <= n, and i*j <= x, we have C(r-1) < k <= C(r). Equivalently, r is the kth smallest entry when the multiset of all m*n products i*j (1 <= i <= m, 1 <= j <= n) is sorted in nondecreasing order, counting equal products with multiplicity.
  Preconditions: m, n, k are integers with 1 <= m <= 30000, 1 <= n <= 30000, and 1 <= k <= m*n. -/
theorem spec_1 (m n k : Aeneas.Std.I64)
    (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 30000)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 30000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ m.val * n.val) :
    ∃ r : Aeneas.Std.I64,
      find_kth_number m n k = ok r ∧
        countLeq m.val n.val (r.val - 1) < k.val ∧ k.val ≤ countLeq m.val n.val r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (m n k : Aeneas.Std.I64)
    (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 30000)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 30000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ m.val * n.val), ∃ r : Aeneas.Std.I64,
      find_kth_number m n k = ok r ∧
        countLeq m.val n.val (r.val - 1) < k.val ∧ k.val ≤ countLeq m.val n.val r.val) := by
  sorry

/-- The function does not fail: for every input satisfying the preconditions, find_kth_number returns a Result.ok value (no overflow, out-of-bounds access, or panic occurs).
  Preconditions: m, n, k are integers with 1 <= m <= 30000, 1 <= n <= 30000, and 1 <= k <= m*n. -/
theorem spec_2 (m n k : Aeneas.Std.I64)
    (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 30000)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 30000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ m.val * n.val) :
    ∃ r : Aeneas.Std.I64, find_kth_number m n k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (m n k : Aeneas.Std.I64)
    (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 30000)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 30000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ m.val * n.val), ∃ r : Aeneas.Std.I64, find_kth_number m n k = ok r) := by
  sorry

/-- The function returns a result r with 1 <= r <= m*n.
  Preconditions: m, n, k are integers with 1 <= m <= 30000, 1 <= n <= 30000, and 1 <= k <= m*n. -/
theorem spec_3 (m n k : Aeneas.Std.I64)
    (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 30000)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 30000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ m.val * n.val) :
    ∃ r : Aeneas.Std.I64,
      find_kth_number m n k = ok r ∧ 1 ≤ r.val ∧ r.val ≤ m.val * n.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (m n k : Aeneas.Std.I64)
    (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 30000)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 30000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ m.val * n.val), ∃ r : Aeneas.Std.I64,
      find_kth_number m n k = ok r ∧ 1 ≤ r.val ∧ r.val ≤ m.val * n.val) := by
  sorry

/-- The function returns a result r for which there exist integers i and j with 1 <= i <= m, 1 <= j <= n, and r = i*j.
  Preconditions: m, n, k are integers with 1 <= m <= 30000, 1 <= n <= 30000, and 1 <= k <= m*n. -/
theorem spec_4 (m n k : Aeneas.Std.I64)
    (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 30000)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 30000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ m.val * n.val) :
    ∃ r : Aeneas.Std.I64,
      find_kth_number m n k = ok r ∧
        ∃ i j : ℤ, 1 ≤ i ∧ i ≤ m.val ∧ 1 ≤ j ∧ j ≤ n.val ∧ r.val = i * j := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (m n k : Aeneas.Std.I64)
    (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 30000)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 30000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ m.val * n.val), ∃ r : Aeneas.Std.I64,
      find_kth_number m n k = ok r ∧
        ∃ i j : ℤ, 1 ≤ i ∧ i ≤ m.val ∧ 1 ≤ j ∧ j ≤ n.val ∧ r.val = i * j) := by
  sorry

/-- The function returns a result r such that, letting C(x) be the number of integer pairs (i,j) with 1 <= i <= m, 1 <= j <= n, and i*j <= x, we have C(r) >= k.
  Preconditions: m, n, k are integers with 1 <= m <= 30000, 1 <= n <= 30000, and 1 <= k <= m*n. -/
theorem spec_5 (m n k : Aeneas.Std.I64)
    (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 30000)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 30000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ m.val * n.val) :
    ∃ r : Aeneas.Std.I64,
      find_kth_number m n k = ok r ∧ k.val ≤ countLeq m.val n.val r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (m n k : Aeneas.Std.I64)
    (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 30000)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 30000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ m.val * n.val), ∃ r : Aeneas.Std.I64,
      find_kth_number m n k = ok r ∧ k.val ≤ countLeq m.val n.val r.val) := by
  sorry

/-- The function returns a result r such that, letting C(x) be the number of integer pairs (i,j) with 1 <= i <= m, 1 <= j <= n, and i*j <= x, we have C(r-1) < k.
  Preconditions: m, n, k are integers with 1 <= m <= 30000, 1 <= n <= 30000, and 1 <= k <= m*n. -/
theorem spec_6 (m n k : Aeneas.Std.I64)
    (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 30000)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 30000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ m.val * n.val) :
    ∃ r : Aeneas.Std.I64,
      find_kth_number m n k = ok r ∧ countLeq m.val n.val (r.val - 1) < k.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (m n k : Aeneas.Std.I64)
    (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 30000)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 30000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ m.val * n.val), ∃ r : Aeneas.Std.I64,
      find_kth_number m n k = ok r ∧ countLeq m.val n.val (r.val - 1) < k.val) := by
  sorry

/-- The function returns results r1 = find_kth_number(m,n,k1) and r2 = find_kth_number(m,n,k2), and r1 <= r2.
  Preconditions: m, n, k1, k2 are integers with 1 <= m <= 30000, 1 <= n <= 30000, and 1 <= k1 <= k2 <= m*n. -/
theorem spec_7 (m n k1 k2 : Aeneas.Std.I64)
    (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 30000)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 30000)
    (hk1_lb : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_ub : k2.val ≤ m.val * n.val) :
    ∃ r1 r2 : Aeneas.Std.I64,
      find_kth_number m n k1 = ok r1 ∧ find_kth_number m n k2 = ok r2 ∧ r1.val ≤ r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (m n k1 k2 : Aeneas.Std.I64)
    (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 30000)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 30000)
    (hk1_lb : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_ub : k2.val ≤ m.val * n.val), ∃ r1 r2 : Aeneas.Std.I64,
      find_kth_number m n k1 = ok r1 ∧ find_kth_number m n k2 = ok r2 ∧ r1.val ≤ r2.val) := by
  sorry

/-- The function returns results r1 = find_kth_number(m,n,k) and r2 = find_kth_number(n,m,k), and r1 = r2.
  Preconditions: m, n, k are integers with 1 <= m <= 30000, 1 <= n <= 30000, and 1 <= k <= m*n. -/
theorem spec_8 (m n k : Aeneas.Std.I64)
    (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 30000)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 30000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ m.val * n.val) :
    ∃ r1 r2 : Aeneas.Std.I64,
      find_kth_number m n k = ok r1 ∧ find_kth_number n m k = ok r2 ∧ r1.val = r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (m n k : Aeneas.Std.I64)
    (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 30000)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 30000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ m.val * n.val), ∃ r1 r2 : Aeneas.Std.I64,
      find_kth_number m n k = ok r1 ∧ find_kth_number n m k = ok r2 ∧ r1.val = r2.val) := by
  sorry

/-- Let r be the result of find_kth_number(m,n,k) and let r' be the result of find_kth_number(m,n,k+1). Then r <= r', and r = r' if and only if C(r) >= k+1, where C(x) is the number of integer pairs (i,j) with 1 <= i <= m, 1 <= j <= n, and i*j <= x.
  Preconditions: m, n, k are integers with 1 <= m <= 30000, 1 <= n <= 30000, and 1 <= k < m*n. -/
theorem spec_9 (m n k k' : Aeneas.Std.I64)
    (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 30000)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 30000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val < m.val * n.val)
    (hk' : k'.val = k.val + 1) :
    ∃ r r' : Aeneas.Std.I64,
      find_kth_number m n k = ok r ∧ find_kth_number m n k' = ok r' ∧
        r.val ≤ r'.val ∧
          (r.val = r'.val ↔ k.val + 1 ≤ countLeq m.val n.val r.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (m n k k' : Aeneas.Std.I64)
    (hm_lb : 1 ≤ m.val) (hm_ub : m.val ≤ 30000)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 30000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val < m.val * n.val)
    (hk' : k'.val = k.val + 1), ∃ r r' : Aeneas.Std.I64,
      find_kth_number m n k = ok r ∧ find_kth_number m n k' = ok r' ∧
        r.val ≤ r'.val ∧
          (r.val = r'.val ↔ k.val + 1 ≤ countLeq m.val n.val r.val)) := by
  sorry

end AegisSpec.FindKthNumber
