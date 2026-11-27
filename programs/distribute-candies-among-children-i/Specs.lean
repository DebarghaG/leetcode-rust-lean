import Aegis.DistributeCandies.Code.Funs

/-!
# Specifications of `Aegis.DistributeCandies.distribute_candies`

LeetCode problem `distribute-candies-among-children-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DistributeCandies

open Aegis.DistributeCandies

def countTriples (n limit : ℤ) : ℕ :=
  if limit < 0 then 0
  else
    (((Finset.range (limit.toNat + 1)).product
        ((Finset.range (limit.toNat + 1)).product (Finset.range (limit.toNat + 1)))).filter
      (fun p : ℕ × ℕ × ℕ => (p.1 : ℤ) + (p.2.1 : ℤ) + (p.2.2 : ℤ) = n)).card

def countSubsetsOfThree (n : ℤ) : ℕ :=
  ((Finset.range 3).powerset.filter (fun s => s.card = n.toNat)).card

def B (m : ℤ) : ℤ := if 2 ≤ m then m * (m - 1) / 2 else 0

/-- The function returns Result.ok r for some Std.I64 r, and the integer value of r is exactly the number of ordered triples (x, y, z) of nonnegative integers such that x <= limit, y <= limit, z <= limit, and x + y + z = n.
  Preconditions: Let n and limit denote the integer values of the parameters. The constraints are 1 <= n <= 50 and 1 <= limit <= 50. -/
theorem spec_1 (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50) :
    ∃ r : Std.I64,
      distribute_candies n limit = ok r ∧ r.val = (countTriples n.val limit.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50), ∃ r : Std.I64,
      distribute_candies n limit = ok r ∧ r.val = (countTriples n.val limit.val : ℤ)) := by
  sorry

/-- The function returns Result.ok r for some Std.I64 r; equivalently, it does not fail (for example, by arithmetic overflow or other error) on any input satisfying the preconditions.
  Preconditions: Let n and limit denote the integer values of the parameters. The constraints are 1 <= n <= 50 and 1 <= limit <= 50. -/
theorem spec_2 (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50) :
    ∃ r : Std.I64, distribute_candies n limit = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50), ∃ r : Std.I64, distribute_candies n limit = ok r) := by
  sorry

/-- Whenever the function returns Result.ok r, the integer value of r satisfies 0 <= r <= ((n + 1) * (n + 2)) / 2.
  Preconditions: Let n and limit denote the integer values of the parameters. The constraints are 1 <= n <= 50 and 1 <= limit <= 50. -/
theorem spec_3 (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50) :
    ∀ r : Std.I64,
      distribute_candies n limit = ok r → 0 ≤ r.val ∧ r.val ≤ (n.val + 1) * (n.val + 2) / 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50), ∀ r : Std.I64,
      distribute_candies n limit = ok r → 0 ≤ r.val ∧ r.val ≤ (n.val + 1) * (n.val + 2) / 2) := by
  sorry

/-- Whenever the function returns Result.ok r, the integer value of r is 0.
  Preconditions: Let n and limit denote the integer values of the parameters. The constraints are 1 <= n <= 50 and 1 <= limit <= 50, and moreover n > 3 * limit. -/
theorem spec_4 (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50)
    (hgt : 3 * limit.val < n.val) :
    ∀ r : Std.I64, distribute_candies n limit = ok r → r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50)
    (hgt : 3 * limit.val < n.val), ∀ r : Std.I64, distribute_candies n limit = ok r → r.val = 0) := by
  sorry

/-- Whenever the function returns Result.ok r, the integer value of r is ((k + 1) * (k + 2)) / 2.
  Preconditions: Let n and limit denote the integer values of the parameters. The constraints are 1 <= n <= 50 and 1 <= limit <= 50. Let k = 3 * limit - n, and suppose 0 <= k <= limit. -/
theorem spec_5 (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50)
    (hk0 : 0 ≤ 3 * limit.val - n.val) (hkl : 3 * limit.val - n.val ≤ limit.val) :
    ∀ r : Std.I64,
      distribute_candies n limit = ok r →
        r.val = (3 * limit.val - n.val + 1) * (3 * limit.val - n.val + 2) / 2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50)
    (hk0 : 0 ≤ 3 * limit.val - n.val) (hkl : 3 * limit.val - n.val ≤ limit.val), ∀ r : Std.I64,
      distribute_candies n limit = ok r →
        r.val = (3 * limit.val - n.val + 1) * (3 * limit.val - n.val + 2) / 2) := by
  sorry

/-- Whenever the function returns Result.ok r, the integer value of r is the number of subsets S of {0,1,2} with |S| = n; equivalently, r = 3 for n=1 or n=2, r = 1 for n=3, and r = 0 for n >= 4.
  Preconditions: Let n and limit denote the integer values of the parameters. The constraints are 1 <= n <= 50 and 1 <= limit <= 50, and moreover limit = 1. -/
theorem spec_6 (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50)
    (hl : limit.val = 1) :
    ∀ r : Std.I64,
      distribute_candies n limit = ok r → r.val = (countSubsetsOfThree n.val : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50)
    (hl : limit.val = 1), ∀ r : Std.I64,
      distribute_candies n limit = ok r → r.val = (countSubsetsOfThree n.val : ℤ)) := by
  sorry

/-- Whenever the function returns Result.ok r, the integer value of r is ((n + 1) * (n + 2)) / 2.
  Preconditions: Let n and limit denote the integer values of the parameters. The constraints are 1 <= n <= 50 and 1 <= limit <= 50, and moreover limit >= n. -/
theorem spec_7 (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50)
    (hle : n.val ≤ limit.val) :
    ∀ r : Std.I64,
      distribute_candies n limit = ok r → r.val = (n.val + 1) * (n.val + 2) / 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50)
    (hle : n.val ≤ limit.val), ∀ r : Std.I64,
      distribute_candies n limit = ok r → r.val = (n.val + 1) * (n.val + 2) / 2) := by
  sorry

/-- Whenever the function returns Result.ok r, the integer value of r is at least 1.
  Preconditions: Let n and limit denote the integer values of the parameters. The constraints are 1 <= n <= 50 and 1 <= limit <= 50, and moreover n <= 3 * limit. -/
theorem spec_8 (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50)
    (hle : n.val ≤ 3 * limit.val) :
    ∀ r : Std.I64, distribute_candies n limit = ok r → 1 ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50)
    (hle : n.val ≤ 3 * limit.val), ∀ r : Std.I64, distribute_candies n limit = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns Result.ok r, the integer value of r equals the number of ordered triples (x, y, z) of nonnegative integers such that x <= limit, y <= limit, z <= limit, and x + y + z = 3 * limit - n.
  Preconditions: Let n and limit denote the integer values of the parameters. The constraints are 1 <= n <= 50 and 1 <= limit <= 50, and moreover n <= 3 * limit. -/
theorem spec_9 (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50)
    (hle : n.val ≤ 3 * limit.val) :
    ∀ r : Std.I64,
      distribute_candies n limit = ok r →
        r.val = (countTriples (3 * limit.val - n.val) limit.val : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50)
    (hle : n.val ≤ 3 * limit.val), ∀ r : Std.I64,
      distribute_candies n limit = ok r →
        r.val = (countTriples (3 * limit.val - n.val) limit.val : ℤ)) := by
  sorry

/-- Whenever the function returns Result.ok r, the integer value of r is at least the number of ordered triples (x, y, z) of nonnegative integers such that x <= limit - 1, y <= limit - 1, z <= limit - 1, and x + y + z = n.
  Preconditions: Let n and limit denote the integer values of the parameters. The constraints are 1 <= n <= 50 and 1 <= limit <= 50, and moreover limit >= 2. -/
theorem spec_10 (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50)
    (hl : 2 ≤ limit.val) :
    ∀ r : Std.I64,
      distribute_candies n limit = ok r →
        (countTriples n.val (limit.val - 1) : ℤ) ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50)
    (hl : 2 ≤ limit.val), ∀ r : Std.I64,
      distribute_candies n limit = ok r →
        (countTriples n.val (limit.val - 1) : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns Result.ok r, the integer value of r is B(n + 2) - 3 * B(n - limit + 1) + 3 * B(n - 2 * limit) - B(n - 3 * limit - 1), where for an integer m, B(m) is defined to be m * (m - 1) / 2 if m >= 2, and 0 if m < 2.
  Preconditions: Let n and limit denote the integer values of the parameters. The constraints are 1 <= n <= 50 and 1 <= limit <= 50. -/
theorem spec_11 (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50) :
    ∀ r : Std.I64,
      distribute_candies n limit = ok r →
        r.val = B (n.val + 2) - 3 * B (n.val - limit.val + 1) + 3 * B (n.val - 2 * limit.val)
          - B (n.val - 3 * limit.val - 1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n limit : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50) (hl1 : 1 ≤ limit.val) (hl2 : limit.val ≤ 50), ∀ r : Std.I64,
      distribute_candies n limit = ok r →
        r.val = B (n.val + 2) - 3 * B (n.val - limit.val + 1) + 3 * B (n.val - 2 * limit.val)
          - B (n.val - 3 * limit.val - 1)) := by
  sorry

end AegisSpec.DistributeCandies
