import Aegis.DistributeCandies.Code.Funs

/-!
# Specifications of `Aegis.DistributeCandies.distribute_candies`

LeetCode problem `distribute-candies-among-children-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.DistributeCandies (distribute_candies)

namespace AegisSpec.DistributeCandies

def triplesSummingTo (N L : ℤ) : Finset (ℕ × ℕ × ℕ) :=
  if 0 ≤ L then
    ((Finset.Icc 0 L.toNat).product
        ((Finset.Icc 0 L.toNat).product (Finset.Icc 0 L.toNat))).filter
      (fun p => (p.1 : ℤ) + (p.2.1 : ℤ) + (p.2.2 : ℤ) = N)
  else ∅

def countTriples (N L : ℤ) : ℤ := ((triplesSummingTo N L).card : ℤ)

/-- Whenever the function returns a result r, the integer value R of r equals the number of ordered triples (a,b,c) of integers such that 0 <= a <= L, 0 <= b <= L, 0 <= c <= L, and a + b + c = N.
  Preconditions: Let N and L be the integer values of n and limit. Assume 1 <= N <= 100000000 and 1 <= L <= 100000000. -/
theorem spec_1 (n limit : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000) :
    ∀ r : Std.I64, distribute_candies n limit = ok r → r.val = countTriples n.val limit.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n limit : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000), ∀ r : Std.I64, distribute_candies n limit = ok r → r.val = countTriples n.val limit.val) := by
  sorry

/-- The function returns a result r; it does not fail.
  Preconditions: Let N and L be the integer values of n and limit. Assume 1 <= N <= 100000000 and 1 <= L <= 100000000. -/
theorem spec_2 (n limit : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000) :
    ∃ r : Std.I64, distribute_candies n limit = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n limit : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000), ∃ r : Std.I64, distribute_candies n limit = ok r) := by
  sorry

/-- Whenever the function returns a result r, its integer value R satisfies R <= (N+1)*(N+2)/2.
  Preconditions: Let N and L be the integer values of n and limit. Assume 1 <= N <= 100000000 and 1 <= L <= 100000000. -/
theorem spec_3 (n limit : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000) :
    ∀ r : Std.I64,
      distribute_candies n limit = ok r → r.val ≤ (n.val + 1) * (n.val + 2) / 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n limit : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000), ∀ r : Std.I64,
      distribute_candies n limit = ok r → r.val ≤ (n.val + 1) * (n.val + 2) / 2) := by
  sorry

/-- Whenever the function returns a result r, its integer value R satisfies R <= (min(L,N)+1)^2.
  Preconditions: Let N and L be the integer values of n and limit. Assume 1 <= N <= 100000000 and 1 <= L <= 100000000. -/
theorem spec_4 (n limit : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000) :
    ∀ r : Std.I64,
      distribute_candies n limit = ok r → r.val ≤ (min limit.val n.val + 1) ^ 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n limit : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000), ∀ r : Std.I64,
      distribute_candies n limit = ok r → r.val ≤ (min limit.val n.val + 1) ^ 2) := by
  sorry

/-- Whenever the function returns a result r, its integer value R equals (N+1)*(N+2)/2.
  Preconditions: Let N and L be the integer values of n and limit. Assume 1 <= N <= 100000000, 1 <= L <= 100000000, and L >= N. -/
theorem spec_5 (n limit : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000)
    (hNL : n.val ≤ limit.val) :
    ∀ r : Std.I64,
      distribute_candies n limit = ok r → r.val = (n.val + 1) * (n.val + 2) / 2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n limit : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000)
    (hNL : n.val ≤ limit.val), ∀ r : Std.I64,
      distribute_candies n limit = ok r → r.val = (n.val + 1) * (n.val + 2) / 2) := by
  sorry

/-- Whenever the function returns a result r, its integer value R equals 0.
  Preconditions: Let N and L be the integer values of n and limit. Assume 1 <= N <= 100000000, 1 <= L <= 100000000, and N > 3*L. -/
theorem spec_6 (n limit : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000)
    (hNL : 3 * limit.val < n.val) :
    ∀ r : Std.I64, distribute_candies n limit = ok r → r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n limit : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000)
    (hNL : 3 * limit.val < n.val), ∀ r : Std.I64, distribute_candies n limit = ok r → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, its integer value R equals 1.
  Preconditions: Let N and L be the integer values of n and limit. Assume 1 <= N <= 100000000, 1 <= L <= 100000000, and N = 3*L. -/
theorem spec_7 (n limit : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000)
    (hNL : n.val = 3 * limit.val) :
    ∀ r : Std.I64, distribute_candies n limit = ok r → r.val = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n limit : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000)
    (hNL : n.val = 3 * limit.val), ∀ r : Std.I64, distribute_candies n limit = ok r → r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, its integer value R satisfies R >= 1.
  Preconditions: Let N and L be the integer values of n and limit. Assume 1 <= N <= 100000000, 1 <= L <= 100000000, and N <= 3*L. -/
theorem spec_8 (n limit : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000)
    (hNL : n.val ≤ 3 * limit.val) :
    ∀ r : Std.I64, distribute_candies n limit = ok r → 1 ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n limit : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000)
    (hNL : n.val ≤ 3 * limit.val), ∀ r : Std.I64, distribute_candies n limit = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, its integer value R equals 3 if N = 1 or N = 2, equals 1 if N = 3, and equals 0 if N >= 4.
  Preconditions: Let N and L be the integer values of n and limit. Assume 1 <= N <= 100000000, 1 <= L <= 100000000, and L = 1. -/
theorem spec_9 (n limit : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000)
    (hL : limit.val = 1) :
    ∀ r : Std.I64,
      distribute_candies n limit = ok r →
        r.val = (if n.val = 1 ∨ n.val = 2 then 3 else if n.val = 3 then 1 else 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n limit : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000)
    (hL : limit.val = 1), ∀ r : Std.I64,
      distribute_candies n limit = ok r →
        r.val = (if n.val = 1 ∨ n.val = 2 then 3 else if n.val = 3 then 1 else 0)) := by
  sorry

/-- Whenever the function returns a result r, its integer value R equals ((N+1)*(N+2)/2) - 3.
  Preconditions: Let N and L be the integer values of n and limit. Assume 1 <= N <= 100000000, 1 <= L <= 100000000, N >= 2, and L = N - 1. -/
theorem spec_10 (n limit : Std.I64)
    (hN_lb : 2 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000)
    (hL : limit.val = n.val - 1) :
    ∀ r : Std.I64,
      distribute_candies n limit = ok r → r.val = (n.val + 1) * (n.val + 2) / 2 - 3 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n limit : Std.I64)
    (hN_lb : 2 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ limit.val) (hL_ub : limit.val ≤ 100000000)
    (hL : limit.val = n.val - 1), ∀ r : Std.I64,
      distribute_candies n limit = ok r → r.val = (n.val + 1) * (n.val + 2) / 2 - 3) := by
  sorry

/-- Whenever the function returns results r and r2 on these two calls, the integer value R of r is at most the integer value R2 of r2.
  Preconditions: Let N, L, and L2 be integers with 1 <= N <= 100000000 and 1 <= L <= L2 <= 100000000. Consider two calls: one with n value N and limit value L, and one with n value N and limit value L2. -/
theorem spec_11 (n l₁ l₂ : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ l₁.val) (hLL : l₁.val ≤ l₂.val) (hL_ub : l₂.val ≤ 100000000) :
    ∀ r r₂ : Std.I64,
      distribute_candies n l₁ = ok r → distribute_candies n l₂ = ok r₂ → r.val ≤ r₂.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n l₁ l₂ : Std.I64)
    (hN_lb : 1 ≤ n.val) (hN_ub : n.val ≤ 100000000)
    (hL_lb : 1 ≤ l₁.val) (hLL : l₁.val ≤ l₂.val) (hL_ub : l₂.val ≤ 100000000), ∀ r r₂ : Std.I64,
      distribute_candies n l₁ = ok r → distribute_candies n l₂ = ok r₂ → r.val ≤ r₂.val) := by
  sorry

/-- Whenever the function returns results r1 and r2 on these two calls, their integer values satisfy R1 = R2, because (a,b,c) -> (L-a,L-b,L-c) is a bijection between valid triples summing to N1 and valid triples summing to N2.
  Preconditions: Let L, N1, and N2 be integers with 1 <= L <= 100000000, 1 <= N1 <= 100000000, 1 <= N2 <= 100000000, and N1 + N2 = 3*L. Consider the calls with n value N1 and limit value L, and with n value N2 and limit value L. -/
theorem spec_12 (n₁ n₂ l : Std.I64)
    (hL_lb : 1 ≤ l.val) (hL_ub : l.val ≤ 100000000)
    (hN₁_lb : 1 ≤ n₁.val) (hN₁_ub : n₁.val ≤ 100000000)
    (hN₂_lb : 1 ≤ n₂.val) (hN₂_ub : n₂.val ≤ 100000000)
    (hsum : n₁.val + n₂.val = 3 * l.val) :
    ∀ r₁ r₂ : Std.I64,
      distribute_candies n₁ l = ok r₁ →
      distribute_candies n₂ l = ok r₂ → r₁.val = r₂.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n₁ n₂ l : Std.I64)
    (hL_lb : 1 ≤ l.val) (hL_ub : l.val ≤ 100000000)
    (hN₁_lb : 1 ≤ n₁.val) (hN₁_ub : n₁.val ≤ 100000000)
    (hN₂_lb : 1 ≤ n₂.val) (hN₂_ub : n₂.val ≤ 100000000)
    (hsum : n₁.val + n₂.val = 3 * l.val), ∀ r₁ r₂ : Std.I64,
      distribute_candies n₁ l = ok r₁ →
      distribute_candies n₂ l = ok r₂ → r₁.val = r₂.val) := by
  sorry

end AegisSpec.DistributeCandies
