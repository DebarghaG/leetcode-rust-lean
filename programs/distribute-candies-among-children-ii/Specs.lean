import Aegis.DistributeCandies.Code.Funs
import Mathlib.Data.Int.Interval

/-!
# Specifications of `Aegis.DistributeCandies.distribute_candies`

LeetCode problem `distribute-candies-among-children-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DistributeCandies

open Aegis.DistributeCandies

def toI64 (k : ℤ) : Std.I64 := ⟨BitVec.ofInt 64 k⟩

def D (n limit : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  ((Finset.Icc (0 : ℤ) limit) ×ˢ ((Finset.Icc (0 : ℤ) limit) ×ˢ (Finset.Icc (0 : ℤ) limit))).filter
    (fun p => p.1 + p.2.1 + p.2.2 = n)

def DUncapped (n : ℤ) : Finset (ℤ × ℤ × ℤ) := D n n

def pairCount (m limit : ℤ) : ℕ :=
  (((Finset.Icc (0 : ℤ) limit) ×ˢ (Finset.Icc (0 : ℤ) limit)).filter (fun p => p.1 + p.2 = m)).card

def totalTriples (n : ℤ) : ℤ := ((n + 1) * (n + 2)) / 2

/-- Let D(n, limit) be the set of ordered triples (a,b,c) of integers such that 0 <= a <= limit, 0 <= b <= limit, 0 <= c <= limit, and a+b+c = n. Whenever distribute_candies n limit returns a result r, the integer value of r is exactly the cardinality |D(n, limit)|. In other words, r is the number of ways to distribute the n candies among the three children so that each child receives at most limit candies.
  Preconditions: n and limit are the Std.I64 parameters, with integer values satisfying 1 <= n <= 10^6 and 1 <= limit <= 10^6. -/
theorem spec_1 (n limit : Std.I64)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 6)
    (hl_lb : 1 ≤ limit.val) (hl_ub : limit.val ≤ 10 ^ 6)
    (r : Std.I64) (hr : distribute_candies n limit = ok r) :
    r.val = ((D n.val limit.val).card : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 6)
    (hl_lb : 1 ≤ limit.val) (hl_ub : limit.val ≤ 10 ^ 6)
    (r : Std.I64) (hr : distribute_candies n limit = ok r), r.val = ((D n.val limit.val).card : ℤ)) := by
  sorry

/-- For every n and limit satisfying the preconditions, the call distribute_candies n limit returns a result r; it does not fail by overflow, panic, or out-of-bounds.
  Preconditions: n and limit are the Std.I64 parameters, with integer values satisfying 1 <= n <= 10^6 and 1 <= limit <= 10^6. -/
theorem spec_2 (n limit : Std.I64)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 6)
    (hl_lb : 1 ≤ limit.val) (hl_ub : limit.val ≤ 10 ^ 6) :
    ∃ r, distribute_candies n limit = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 6)
    (hl_lb : 1 ≤ limit.val) (hl_ub : limit.val ≤ 10 ^ 6), ∃ r, distribute_candies n limit = ok r) := by
  sorry

/-- Let D(n, limit) be the set of ordered triples (a,b,c) of integers such that 0 <= a <= limit, 0 <= b <= limit, 0 <= c <= limit, and a+b+c = n. Whenever distribute_candies n limit returns a result r, the integer value of r satisfies 0 <= r <= ((n+1)*(n+2))/2. The upper bound is the total number of ordered triples of nonnegative integers summing to n before imposing the per-child limit.
  Preconditions: n and limit are the Std.I64 parameters, with integer values satisfying 1 <= n <= 10^6 and 1 <= limit <= 10^6. -/
theorem spec_3 (n limit : Std.I64)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 6)
    (hl_lb : 1 ≤ limit.val) (hl_ub : limit.val ≤ 10 ^ 6)
    (r : Std.I64) (hr : distribute_candies n limit = ok r) :
    0 ≤ r.val ∧ r.val ≤ totalTriples n.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 6)
    (hl_lb : 1 ≤ limit.val) (hl_ub : limit.val ≤ 10 ^ 6)
    (r : Std.I64) (hr : distribute_candies n limit = ok r), 0 ≤ r.val ∧ r.val ≤ totalTriples n.val) := by
  sorry

/-- Let D(n, limit) be the set of ordered triples (a,b,c) of integers such that 0 <= a <= limit, 0 <= b <= limit, 0 <= c <= limit, and a+b+c = n. If n > 3*limit, then D(n, limit) is empty; consequently, whenever distribute_candies n limit returns a result r, the integer value of r is 0.
  Preconditions: n and limit are the Std.I64 parameters, with integer values satisfying 1 <= n <= 10^6, 1 <= limit <= 10^6, and n > 3*limit. -/
theorem spec_4 (n limit : Std.I64)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 6)
    (hl_lb : 1 ≤ limit.val) (hl_ub : limit.val ≤ 10 ^ 6)
    (h : 3 * limit.val < n.val)
    (r : Std.I64) (hr : distribute_candies n limit = ok r) :
    D n.val limit.val = ∅ ∧ r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 6)
    (hl_lb : 1 ≤ limit.val) (hl_ub : limit.val ≤ 10 ^ 6)
    (h : 3 * limit.val < n.val)
    (r : Std.I64) (hr : distribute_candies n limit = ok r), D n.val limit.val = ∅ ∧ r.val = 0) := by
  sorry

/-- Let D(n, limit) be the set of ordered triples (a,b,c) of integers such that 0 <= a <= limit, 0 <= b <= limit, 0 <= c <= limit, and a+b+c = n. If limit >= n, then the per-child cap is not binding: D(n, limit) = {(a,b,c) in Z^3 : a >= 0, b >= 0, c >= 0, and a+b+c = n}. Consequently, whenever distribute_candies n limit returns a result r, the integer value of r is ((n+1)*(n+2))/2.
  Preconditions: n and limit are the Std.I64 parameters, with integer values satisfying 1 <= n <= 10^6, 1 <= limit <= 10^6, and limit >= n. -/
theorem spec_5 (n limit : Std.I64)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 6)
    (hl_lb : 1 ≤ limit.val) (hl_ub : limit.val ≤ 10 ^ 6)
    (h : n.val ≤ limit.val)
    (r : Std.I64) (hr : distribute_candies n limit = ok r) :
    D n.val limit.val = DUncapped n.val ∧ r.val = totalTriples n.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 6)
    (hl_lb : 1 ≤ limit.val) (hl_ub : limit.val ≤ 10 ^ 6)
    (h : n.val ≤ limit.val)
    (r : Std.I64) (hr : distribute_candies n limit = ok r), D n.val limit.val = DUncapped n.val ∧ r.val = totalTriples n.val) := by
  sorry

/-- Let F(m, limit) be the number of ordered pairs (b,c) of integers with 0 <= b <= limit, 0 <= c <= limit, and b+c = m. Whenever distribute_candies n limit returns a result r, the integer value of r equals sum_{a=0}^{min(limit,n)} F(n-a, limit).
  Preconditions: n and limit are the Std.I64 parameters, with integer values satisfying 1 <= n <= 10^6 and 1 <= limit <= 10^6. -/
theorem spec_6 (n limit : Std.I64)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 6)
    (hl_lb : 1 ≤ limit.val) (hl_ub : limit.val ≤ 10 ^ 6)
    (r : Std.I64) (hr : distribute_candies n limit = ok r) :
    r.val = ∑ a ∈ Finset.Icc (0 : ℤ) (min limit.val n.val), ((pairCount (n.val - a) limit.val : ℕ) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 6)
    (hl_lb : 1 ≤ limit.val) (hl_ub : limit.val ≤ 10 ^ 6)
    (r : Std.I64) (hr : distribute_candies n limit = ok r), r.val = ∑ a ∈ Finset.Icc (0 : ℤ) (min limit.val n.val), ((pairCount (n.val - a) limit.val : ℕ) : ℤ)) := by
  sorry

/-- Let r = distribute_candies n limit and r' = distribute_candies n (limit+1). Whenever both calls return results, the integer value of r is at most the integer value of r'.
  Preconditions: n and limit are the Std.I64 parameters, with integer values satisfying 1 <= n <= 10^6 and 1 <= limit <= 10^6 - 1. -/
theorem spec_7 (n limit : Std.I64)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 6)
    (hl_lb : 1 ≤ limit.val) (hl_ub : limit.val ≤ 10 ^ 6 - 1)
    (r r' : Std.I64)
    (hr : distribute_candies n limit = ok r)
    (hr' : distribute_candies n (toI64 (limit.val + 1)) = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 6)
    (hl_lb : 1 ≤ limit.val) (hl_ub : limit.val ≤ 10 ^ 6 - 1)
    (r r' : Std.I64)
    (hr : distribute_candies n limit = ok r)
    (hr' : distribute_candies n (toI64 (limit.val + 1)) = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Let r = distribute_candies n limit and r' = distribute_candies (3*limit - n) limit. Whenever both calls return results, the integer value of r equals the integer value of r'.
  Preconditions: n and limit are the Std.I64 parameters, with integer values satisfying 1 <= n <= 10^6, 1 <= limit <= 10^6, n < 3*limit, and 3*limit - n <= 10^6. -/
theorem spec_8 (n limit : Std.I64)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 6)
    (hl_lb : 1 ≤ limit.val) (hl_ub : limit.val ≤ 10 ^ 6)
    (hlt : n.val < 3 * limit.val) (hsub : 3 * limit.val - n.val ≤ 10 ^ 6)
    (r r' : Std.I64)
    (hr : distribute_candies n limit = ok r)
    (hr' : distribute_candies (toI64 (3 * limit.val - n.val)) limit = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 6)
    (hl_lb : 1 ≤ limit.val) (hl_ub : limit.val ≤ 10 ^ 6)
    (hlt : n.val < 3 * limit.val) (hsub : 3 * limit.val - n.val ≤ 10 ^ 6)
    (r r' : Std.I64)
    (hr : distribute_candies n limit = ok r)
    (hr' : distribute_candies (toI64 (3 * limit.val - n.val)) limit = ok r'), r.val = r'.val) := by
  sorry

/-- Let D(n, limit) be the set of ordered triples (a,b,c) of integers such that 0 <= a <= limit, 0 <= b <= limit, 0 <= c <= limit, and a+b+c = n. If n <= 3*limit, then D(n, limit) is nonempty. Equivalently, whenever distribute_candies n limit returns a result r, the integer value of r is at least 1.
  Preconditions: n and limit are the Std.I64 parameters, with integer values satisfying 1 <= n <= 10^6, 1 <= limit <= 10^6, and n <= 3*limit. -/
theorem spec_9 (n limit : Std.I64)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 6)
    (hl_lb : 1 ≤ limit.val) (hl_ub : limit.val ≤ 10 ^ 6)
    (h : n.val ≤ 3 * limit.val)
    (r : Std.I64) (hr : distribute_candies n limit = ok r) :
    (D n.val limit.val).Nonempty ∧ 1 ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 6)
    (hl_lb : 1 ≤ limit.val) (hl_ub : limit.val ≤ 10 ^ 6)
    (h : n.val ≤ 3 * limit.val)
    (r : Std.I64) (hr : distribute_candies n limit = ok r), (D n.val limit.val).Nonempty ∧ 1 ≤ r.val) := by
  sorry

end AegisSpec.DistributeCandies
