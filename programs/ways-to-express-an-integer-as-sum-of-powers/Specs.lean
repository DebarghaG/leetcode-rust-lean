import Aegis.NumberOfWays.Code.Funs

/-!
# Specifications of `Aegis.NumberOfWays.number_of_ways`

LeetCode problem `ways-to-express-an-integer-as-sum-of-powers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.NumberOfWays

namespace AegisSpec.NumberOfWays

def MOD : ℕ := 1000000007

noncomputable def count (n x : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun S => ∑ a ∈ S, a ^ x = n)).card

def Representable (n x : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ a ∈ S, 1 ≤ a) ∧ ∑ a ∈ S, a ^ x = n

noncomputable def countDistinctPartitions (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun S => ∑ a ∈ S, a = n)).card

noncomputable def countSeq (n x : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 n)).filter
      (fun f => StrictMono f ∧ ∑ i, (f i) ^ x = n)).card

noncomputable def countBounded (n x : ℕ) : ℕ :=
  (((Finset.Icc 1 n).filter (fun a => a ^ x ≤ n)).powerset.filter
    (fun T => ∑ a ∈ T, a ^ x = n)).card

def IsResidue (r : ℤ) (c : ℕ) : Prop :=
  0 ≤ r ∧ r < (MOD : ℤ) ∧ r % (MOD : ℤ) = (c : ℤ) % (MOD : ℤ)

/-- Let M = 1000000007. Whenever number_of_ways n x returns a result r, r is the unique integer with 0 <= r < M and r is congruent modulo M to C(n,x), where C(n,x) is the number of finite sets S of positive integers such that all elements of S are distinct and the sum of a^x over a in S is exactly n.
  Preconditions: 1 <= n <= 300 and 1 <= x <= 5. -/
theorem spec_1 (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5) :
    ∀ r, number_of_ways n x = ok r → IsResidue r.val (count n.val.toNat x.val.toNat) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5), ∀ r, number_of_ways n x = ok r → IsResidue r.val (count n.val.toNat x.val.toNat)) := by
  sorry

/-- The call number_of_ways n x returns a result r for every such n and x; it does not fail, panic, or overflow.
  Preconditions: 1 <= n <= 300 and 1 <= x <= 5. -/
theorem spec_2 (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5) :
    ∃ r, number_of_ways n x = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5), ∃ r, number_of_ways n x = ok r) := by
  sorry

/-- Let M = 1000000007. Whenever number_of_ways n x returns a result r, 0 <= r < M.
  Preconditions: 1 <= n <= 300 and 1 <= x <= 5. -/
theorem spec_3 (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5) :
    ∀ r, number_of_ways n x = ok r → 0 ≤ r.val ∧ r.val < (MOD : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5), ∀ r, number_of_ways n x = ok r → 0 ≤ r.val ∧ r.val < (MOD : ℤ)) := by
  sorry

/-- Whenever number_of_ways n x returns a result r, if there is no finite set S of pairwise distinct positive integers with sum over a in S of a^x equal to n, then r = 0.
  Preconditions: 1 <= n <= 300 and 1 <= x <= 5. -/
theorem spec_4 (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5) :
    ∀ r, number_of_ways n x = ok r →
      ¬ Representable n.val.toNat x.val.toNat → r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5), ∀ r, number_of_ways n x = ok r →
      ¬ Representable n.val.toNat x.val.toNat → r.val = 0) := by
  sorry

/-- Whenever number_of_ways 1 x returns a result r, r = 1.
  Preconditions: n = 1 and 1 <= x <= 5. -/
theorem spec_5 (n x : I64) (hn : n.val = 1) (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5) :
    ∀ r, number_of_ways n x = ok r → r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n x : I64) (hn : n.val = 1) (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5), ∀ r, number_of_ways n x = ok r → r.val = 1) := by
  sorry

/-- Let M = 1000000007. Whenever number_of_ways n 1 returns a result r, r is the unique integer with 0 <= r < M and r is congruent modulo M to D(n), where D(n) is the number of finite sets of pairwise distinct positive integers whose ordinary sum is n, equivalently the number of partitions of n into distinct positive parts.
  Preconditions: 1 <= n <= 300 and x = 1. -/
theorem spec_6 (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300) (hx : x.val = 1) :
    ∀ r, number_of_ways n x = ok r → IsResidue r.val (countDistinctPartitions n.val.toNat) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300) (hx : x.val = 1), ∀ r, number_of_ways n x = ok r → IsResidue r.val (countDistinctPartitions n.val.toNat)) := by
  sorry

/-- Whenever number_of_ways n x returns a result r, r = 0.
  Preconditions: 1 <= n <= 300, 1 <= x <= 5, and 2 <= n < 2^x. -/
theorem spec_7 (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5) (hn3 : 2 ≤ n.val) (hn4 : n.val < (2 : ℤ) ^ x.val.toNat) :
    ∀ r, number_of_ways n x = ok r → r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5) (hn3 : 2 ≤ n.val) (hn4 : n.val < (2 : ℤ) ^ x.val.toNat), ∀ r, number_of_ways n x = ok r → r.val = 0) := by
  sorry

/-- Whenever number_of_ways n x returns a result r with r not equal to 0, there exists at least one finite set S of pairwise distinct positive integers such that the sum of a^x over a in S is n.
  Preconditions: 1 <= n <= 300 and 1 <= x <= 5. -/
theorem spec_8 (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5) :
    ∀ r, number_of_ways n x = ok r → r.val ≠ 0 → Representable n.val.toNat x.val.toNat := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5), ∀ r, number_of_ways n x = ok r → r.val ≠ 0 → Representable n.val.toNat x.val.toNat) := by
  sorry

/-- Let M = 1000000007. Whenever number_of_ways n x returns a result r, r is the unique integer with 0 <= r < M and r is congruent modulo M to E(n,x), where E(n,x) is the number of finite strictly increasing sequences (a_1 < a_2 < ... < a_k) of positive integers with k >= 0 and sum from i = 1 to k of a_i^x equal to n.
  Preconditions: 1 <= n <= 300 and 1 <= x <= 5. -/
theorem spec_9 (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5) :
    ∀ r, number_of_ways n x = ok r → IsResidue r.val (countSeq n.val.toNat x.val.toNat) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5), ∀ r, number_of_ways n x = ok r → IsResidue r.val (countSeq n.val.toNat x.val.toNat)) := by
  sorry

/-- Whenever number_of_ways n x returns a result r, the true count C(n,x) is at least 1, because the singleton set {m} is one of the counted representations, and r is the residue of C(n,x) modulo M where M = 1000000007.
  Preconditions: 1 <= n <= 300, 1 <= x <= 5, and n = m^x for some positive integer m. -/
theorem spec_10 (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5)
    (hm : ∃ m : ℕ, 0 < m ∧ n.val.toNat = m ^ x.val.toNat) :
    ∀ r, number_of_ways n x = ok r →
      1 ≤ count n.val.toNat x.val.toNat ∧ IsResidue r.val (count n.val.toNat x.val.toNat) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5)
    (hm : ∃ m : ℕ, 0 < m ∧ n.val.toNat = m ^ x.val.toNat), ∀ r, number_of_ways n x = ok r →
      1 ≤ count n.val.toNat x.val.toNat ∧ IsResidue r.val (count n.val.toNat x.val.toNat)) := by
  sorry

/-- Whenever number_of_ways n x returns a result r, r is the residue modulo M = 1000000007 of the number of subsets T of the finite set {a : a is a positive integer and a^x <= n} such that the sum of a^x over a in T is n.
  Preconditions: 1 <= n <= 300 and 1 <= x <= 5. -/
theorem spec_11 (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5) :
    ∀ r, number_of_ways n x = ok r → IsResidue r.val (countBounded n.val.toNat x.val.toNat) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n x : I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 300)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 5), ∀ r, number_of_ways n x = ok r → IsResidue r.val (countBounded n.val.toNat x.val.toNat)) := by
  sorry

end AegisSpec.NumberOfWays
