import Aegis.CountHousePlacements.Code.Funs

/-!
# Specifications of `Aegis.CountHousePlacements.count_house_placements`

LeetCode problem `count-number-of-ways-to-place-houses`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountHousePlacements

def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | k + 2 => fib (k + 1) + fib k

def IsValidSide (n : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ Finset.Icc 1 n ∧ ∀ i ∈ Finset.Icc 1 (n - 1), ¬ (i ∈ S ∧ i + 1 ∈ S)

instance decidablePredIsValidSide (n : ℕ) : DecidablePred (IsValidSide n) := fun S => by
  unfold IsValidSide
  infer_instance

def validSides (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter (IsValidSide n)

def A (n : ℕ) : ℕ := (validSides n).card

def validPlacements (n : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  validSides n ×ˢ validSides n

def V (n : ℕ) : ℕ := (validPlacements n).card

/-- The function returns a result r. Let V(n) be the number of valid house placements: a placement is a pair (L,R) of subsets of {1,2,...,n}, where L is the set of plots with houses on one side and R on the other side, such that for every i with 1 <= i < n, not (i in L and i+1 in L) and not (i in R and i+1 in R). Then the integer value represented by r is V(n) mod 1_000_000_007 (the least nonnegative residue).
  Preconditions: n is an integer with 1 <= n <= 10^4 (the problem's constraints). -/
theorem spec_1 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) :
    ∃ r : Std.I64, Aegis.CountHousePlacements.count_house_placements n = ok r ∧
      r.val = (V n.val.toNat : ℤ) % 1000000007 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000), ∃ r : Std.I64, Aegis.CountHousePlacements.count_house_placements n = ok r ∧
      r.val = (V n.val.toNat : ℤ) % 1000000007) := by
  sorry

/-- For every integer n with 1 <= n <= 10^4, the function returns a result and does not fail (no panic, out-of-bounds access, or arithmetic overflow).
  Preconditions: n is an integer with 1 <= n <= 10^4. -/
theorem spec_2 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) :
    ∃ r : Std.I64, Aegis.CountHousePlacements.count_house_placements n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000), ∃ r : Std.I64, Aegis.CountHousePlacements.count_house_placements n = ok r) := by
  sorry

/-- Whenever the function returns a result r, the integer value of r satisfies 0 <= r <= 1_000_000_006.
  Preconditions: n is an integer with 1 <= n <= 10^4. -/
theorem spec_3 (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hr : Aegis.CountHousePlacements.count_house_placements n = ok r) :
    0 ≤ r.val ∧ r.val ≤ 1000000006 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hr : Aegis.CountHousePlacements.count_house_placements n = ok r), 0 ≤ r.val ∧ r.val ≤ 1000000006) := by
  sorry

/-- Whenever the function returns successfully with integer value r, let A(n) be the number of subsets S of {1,2,...,n} such that for every i with 1 <= i < n, i and i+1 are not both in S. Let V(n) be the exact number of valid placements as defined in spec_1. Then V(n) = A(n) * A(n), and r is (A(n) * A(n)) mod 1_000_000_007, the least nonnegative residue.
  Preconditions: n is an integer with 1 <= n <= 10^4. -/
theorem spec_4 (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hr : Aegis.CountHousePlacements.count_house_placements n = ok r) :
    V n.val.toNat = A n.val.toNat * A n.val.toNat ∧
      r.val = ((A n.val.toNat * A n.val.toNat : ℕ) : ℤ) % 1000000007 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hr : Aegis.CountHousePlacements.count_house_placements n = ok r), V n.val.toNat = A n.val.toNat * A n.val.toNat ∧
      r.val = ((A n.val.toNat * A n.val.toNat : ℕ) : ℤ) % 1000000007) := by
  sorry

/-- Whenever the function returns a result r, let F be the sequence with F(0)=0, F(1)=1, and F(k+2)=F(k+1)+F(k) for all k >= 0. Then the integer value of r is (F(n+2) * F(n+2)) mod 1_000_000_007.
  Preconditions: n is an integer with 1 <= n <= 10^4. -/
theorem spec_5 (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hr : Aegis.CountHousePlacements.count_house_placements n = ok r) :
    r.val = ((fib (n.val.toNat + 2) * fib (n.val.toNat + 2) : ℕ) : ℤ) % 1000000007 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hr : Aegis.CountHousePlacements.count_house_placements n = ok r), r.val = ((fib (n.val.toNat + 2) * fib (n.val.toNat + 2) : ℕ) : ℤ) % 1000000007) := by
  sorry

/-- Suppose the function returns r for n, and let r1, r2, r3 be the integer results returned by count_house_placements for n-1, n-2, n-3 respectively. Then r is congruent to 2*r1 + 2*r2 - r3 modulo 1_000_000_007.
  Preconditions: n is an integer with 4 <= n <= 10^4. -/
theorem spec_6 (n n1 n2 n3 r r1 r2 r3 : Std.I64)
    (hn : 4 ≤ n.val ∧ n.val ≤ 10000)
    (h1 : n1.val = n.val - 1) (h2 : n2.val = n.val - 2) (h3 : n3.val = n.val - 3)
    (hr : Aegis.CountHousePlacements.count_house_placements n = ok r)
    (hr1 : Aegis.CountHousePlacements.count_house_placements n1 = ok r1)
    (hr2 : Aegis.CountHousePlacements.count_house_placements n2 = ok r2)
    (hr3 : Aegis.CountHousePlacements.count_house_placements n3 = ok r3) :
    r.val % 1000000007 = (2 * r1.val + 2 * r2.val - r3.val) % 1000000007 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n n1 n2 n3 r r1 r2 r3 : Std.I64)
    (hn : 4 ≤ n.val ∧ n.val ≤ 10000)
    (h1 : n1.val = n.val - 1) (h2 : n2.val = n.val - 2) (h3 : n3.val = n.val - 3)
    (hr : Aegis.CountHousePlacements.count_house_placements n = ok r)
    (hr1 : Aegis.CountHousePlacements.count_house_placements n1 = ok r1)
    (hr2 : Aegis.CountHousePlacements.count_house_placements n2 = ok r2)
    (hr3 : Aegis.CountHousePlacements.count_house_placements n3 = ok r3), r.val % 1000000007 = (2 * r1.val + 2 * r2.val - r3.val) % 1000000007) := by
  sorry

end AegisSpec.CountHousePlacements
