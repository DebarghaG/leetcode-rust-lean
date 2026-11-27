import Aegis.SmallestValue.Code.Funs

/-!
# Specifications of `Aegis.SmallestValue.smallest_value`

LeetCode problem `smallest-value-after-replacing-with-sum-of-prime-factors`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std
open Aeneas.Std.Result

namespace AegisSpec.SmallestValue

def sumPrimeFactors (m : ℕ) : ℕ := (Nat.primeFactorsList m).sum

def S (m : ℤ) : ℤ := (sumPrimeFactors m.toNat : ℤ)

def seq (n : ℤ) : ℕ → ℤ
  | 0 => n
  | k + 1 => S (seq n k)

def IsSmallestValue (n r : ℤ) : Prop :=
  (∃ k : ℕ, seq n k = r) ∧ ∀ k : ℕ, r ≤ seq n k

def IsPrimeInt (m : ℤ) : Prop := Nat.Prime m.natAbs

def IsCompositeInt (m : ℤ) : Prop := 1 < m ∧ ¬ IsPrimeInt m

/-- The function returns a result r, and r is the smallest value in the infinite sequence a_0, a_1, ... defined by a_0 = n and a_{k+1} = S(a_k) for every k >= 0, where S(m) is the sum of the prime factors of m counted with multiplicity (if m = p_1 * ... * p_t with all p_i prime, then S(m) = p_1 + ... + p_t). Equivalently, r = min {a_k | k >= 0}.
  Preconditions: 2 <= n <= 100000, where n denotes the integer value of the parameter. -/
theorem spec_1 (n : Aeneas.Std.I64) (hn2 : 2 ≤ n.val) (hn100000 : n.val ≤ 100000) :
    ∃ r, Aegis.SmallestValue.smallest_value n = ok r ∧ IsSmallestValue n.val r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn2 : 2 ≤ n.val) (hn100000 : n.val ≤ 100000), ∃ r, Aegis.SmallestValue.smallest_value n = ok r ∧ IsSmallestValue n.val r.val) := by
  sorry

/-- The function returns a result r for every n satisfying 2 <= n <= 100000; in particular, it does not fail.
  Preconditions: 2 <= n <= 100000, where n denotes the integer value of the parameter. -/
theorem spec_2 (n : Aeneas.Std.I64) (hn2 : 2 ≤ n.val) (hn100000 : n.val ≤ 100000) :
    ∃ r, Aegis.SmallestValue.smallest_value n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn2 : 2 ≤ n.val) (hn100000 : n.val ≤ 100000), ∃ r, Aegis.SmallestValue.smallest_value n = ok r) := by
  sorry

/-- Whenever the function returns a result r, it satisfies 2 <= r <= n.
  Preconditions: 2 <= n <= 100000, where n denotes the integer value of the parameter. -/
theorem spec_3 (n : Aeneas.Std.I64) (hn2 : 2 ≤ n.val) (hn100000 : n.val ≤ 100000) :
    ∀ r, Aegis.SmallestValue.smallest_value n = ok r → 2 ≤ r.val ∧ r.val ≤ n.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn2 : 2 ≤ n.val) (hn100000 : n.val ≤ 100000), ∀ r, Aegis.SmallestValue.smallest_value n = ok r → 2 ≤ r.val ∧ r.val ≤ n.val) := by
  sorry

/-- Whenever the function returns a result r, r is either a prime number or r = 4.
  Preconditions: 2 <= n <= 100000, where n denotes the integer value of the parameter. -/
theorem spec_4 (n : Aeneas.Std.I64) (hn2 : 2 ≤ n.val) (hn100000 : n.val ≤ 100000) :
    ∀ r, Aegis.SmallestValue.smallest_value n = ok r → IsPrimeInt r.val ∨ r.val = 4 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn2 : 2 ≤ n.val) (hn100000 : n.val ≤ 100000), ∀ r, Aegis.SmallestValue.smallest_value n = ok r → IsPrimeInt r.val ∨ r.val = 4) := by
  sorry

/-- Whenever the function returns a result r, there exists an integer k >= 0 such that a_k = r, where a_0 = n and a_{k+1} = S(a_k) with S the sum of prime factors counted with multiplicity.
  Preconditions: 2 <= n <= 100000, where n denotes the integer value of the parameter. -/
theorem spec_5 (n : Aeneas.Std.I64) (hn2 : 2 ≤ n.val) (hn100000 : n.val ≤ 100000) :
    ∀ r, Aegis.SmallestValue.smallest_value n = ok r → ∃ k : ℕ, seq n.val k = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn2 : 2 ≤ n.val) (hn100000 : n.val ≤ 100000), ∀ r, Aegis.SmallestValue.smallest_value n = ok r → ∃ k : ℕ, seq n.val k = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer k >= 0, a_k >= r, where a_0 = n and a_{k+1} = S(a_k) with S the sum of prime factors counted with multiplicity.
  Preconditions: 2 <= n <= 100000, where n denotes the integer value of the parameter. -/
theorem spec_6 (n : Aeneas.Std.I64) (hn2 : 2 ≤ n.val) (hn100000 : n.val ≤ 100000) :
    ∀ r, Aegis.SmallestValue.smallest_value n = ok r → ∀ k : ℕ, r.val ≤ seq n.val k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn2 : 2 ≤ n.val) (hn100000 : n.val ≤ 100000), ∀ r, Aegis.SmallestValue.smallest_value n = ok r → ∀ k : ℕ, r.val ≤ seq n.val k) := by
  sorry

/-- Whenever the function returns a result r, r = n.
  Preconditions: 2 <= n <= 100000 and n is prime. -/
theorem spec_7 (n : Aeneas.Std.I64) (hn2 : 2 ≤ n.val) (hn100000 : n.val ≤ 100000)
    (hnprime : IsPrimeInt n.val) :
    ∀ r, Aegis.SmallestValue.smallest_value n = ok r → r.val = n.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn2 : 2 ≤ n.val) (hn100000 : n.val ≤ 100000)
    (hnprime : IsPrimeInt n.val), ∀ r, Aegis.SmallestValue.smallest_value n = ok r → r.val = n.val) := by
  sorry

/-- Whenever the function returns a result r, r = 4.
  Preconditions: n = 4. -/
theorem spec_8 (n : Aeneas.Std.I64) (hn : n.val = 4) :
    ∀ r, Aegis.SmallestValue.smallest_value n = ok r → r.val = 4 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : n.val = 4), ∀ r, Aegis.SmallestValue.smallest_value n = ok r → r.val = 4) := by
  sorry

/-- Whenever the function returns a result r, r is a prime number and r >= 5.
  Preconditions: 5 <= n <= 100000. -/
theorem spec_9 (n : Aeneas.Std.I64) (hn5 : 5 ≤ n.val) (hn100000 : n.val ≤ 100000) :
    ∀ r, Aegis.SmallestValue.smallest_value n = ok r → IsPrimeInt r.val ∧ 5 ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn5 : 5 ≤ n.val) (hn100000 : n.val ≤ 100000), ∀ r, Aegis.SmallestValue.smallest_value n = ok r → IsPrimeInt r.val ∧ 5 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r < n.
  Preconditions: 2 <= n <= 100000, n is composite, and n != 4. -/
theorem spec_10 (n : Aeneas.Std.I64) (hn2 : 2 ≤ n.val) (hn100000 : n.val ≤ 100000)
    (hncomp : IsCompositeInt n.val) (hn4 : n.val ≠ 4) :
    ∀ r, Aegis.SmallestValue.smallest_value n = ok r → r.val < n.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn2 : 2 ≤ n.val) (hn100000 : n.val ≤ 100000)
    (hncomp : IsCompositeInt n.val) (hn4 : n.val ≠ 4), ∀ r, Aegis.SmallestValue.smallest_value n = ok r → r.val < n.val) := by
  sorry

end AegisSpec.SmallestValue
