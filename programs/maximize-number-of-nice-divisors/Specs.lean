import Mathlib
import Aegis.MaxNiceDivisors.Code.Funs

/-!
# Specifications of `Aegis.MaxNiceDivisors.max_nice_divisors`

LeetCode problem `maximize-number-of-nice-divisors`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open scoped BigOperators

namespace AegisSpec.MaxNiceDivisors

def P (k : ℕ) : ℕ :=
  (Finset.range (k + 1)).sup fun m =>
    ((Fintype.piFinset fun _ : Fin m => Finset.Icc 1 k).filter
        (fun f : Fin m → ℕ => (∑ i, f i) ≤ k)).sup fun f => ∏ i, f i

def Omega (n : ℕ) : ℕ := (Nat.factorization n).sum fun _ e => e

def niceDivisorCount (n : ℕ) : ℕ :=
  ((Nat.divisors n).filter fun d => ∀ p ∈ Nat.primeFactors n, p ∣ d).card

/-- Whenever max_nice_divisors primeFactors returns a result r, r is congruent to P(k) modulo M, that is, r ≡ P(k) (mod M).
  Preconditions: Let k be the integer value of primeFactors. Assume 1 <= k <= 10^9. Let M = 1000000007. Define P(k) = max { product_{j=1}^m a_j : m >= 0, each a_j is an integer with a_j >= 1, and sum_{j=1}^m a_j <= k }, where the empty product (m = 0) is 1. -/
theorem spec_1 (primeFactors : Aeneas.Std.I64)
    (hk1 : 1 ≤ primeFactors.val) (hk2 : primeFactors.val ≤ 1000000000) :
    ∀ r : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors primeFactors = ok r →
        Int.ModEq 1000000007 r.val ((P primeFactors.val.toNat : ℕ) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (primeFactors : Aeneas.Std.I64)
    (hk1 : 1 ≤ primeFactors.val) (hk2 : primeFactors.val ≤ 1000000000), ∀ r : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors primeFactors = ok r →
        Int.ModEq 1000000007 r.val ((P primeFactors.val.toNat : ℕ) : ℤ)) := by
  sorry

/-- The call max_nice_divisors primeFactors returns a result; it does not fail (no overflow, panic, or out-of-bounds).
  Preconditions: Let k be the integer value of primeFactors. Assume 1 <= k <= 10^9. -/
theorem spec_2 (primeFactors : Aeneas.Std.I64)
    (hk1 : 1 ≤ primeFactors.val) (hk2 : primeFactors.val ≤ 1000000000) :
    ∃ r : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors primeFactors = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (primeFactors : Aeneas.Std.I64)
    (hk1 : 1 ≤ primeFactors.val) (hk2 : primeFactors.val ≤ 1000000000), ∃ r : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors primeFactors = ok r) := by
  sorry

/-- Whenever max_nice_divisors primeFactors returns a result r, 0 <= r < 1000000007.
  Preconditions: Let k be the integer value of primeFactors. Assume 1 <= k <= 10^9. -/
theorem spec_3 (primeFactors : Aeneas.Std.I64)
    (hk1 : 1 ≤ primeFactors.val) (hk2 : primeFactors.val ≤ 1000000000) :
    ∀ r : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors primeFactors = ok r →
        0 ≤ r.val ∧ r.val < 1000000007 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (primeFactors : Aeneas.Std.I64)
    (hk1 : 1 ≤ primeFactors.val) (hk2 : primeFactors.val ≤ 1000000000), ∀ r : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors primeFactors = ok r →
        0 ≤ r.val ∧ r.val < 1000000007) := by
  sorry

/-- Whenever max_nice_divisors primeFactors returns a result r, r != 0 (equivalently, 1 <= r < 1000000007).
  Preconditions: Let k be the integer value of primeFactors. Assume 1 <= k <= 10^9. -/
theorem spec_4 (primeFactors : Aeneas.Std.I64)
    (hk1 : 1 ≤ primeFactors.val) (hk2 : primeFactors.val ≤ 1000000000) :
    ∀ r : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors primeFactors = ok r → r.val ≠ 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (primeFactors : Aeneas.Std.I64)
    (hk1 : 1 ≤ primeFactors.val) (hk2 : primeFactors.val ≤ 1000000000), ∀ r : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors primeFactors = ok r → r.val ≠ 0) := by
  sorry

/-- Whenever max_nice_divisors primeFactors returns a result r, r = 1.
  Preconditions: Let k be the integer value of primeFactors. Assume k = 1 (which satisfies 1 <= k <= 10^9). -/
theorem spec_5 (primeFactors : Aeneas.Std.I64)
    (hk : primeFactors.val = 1) :
    ∀ r : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors primeFactors = ok r → r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (primeFactors : Aeneas.Std.I64)
    (hk : primeFactors.val = 1), ∀ r : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors primeFactors = ok r → r.val = 1) := by
  sorry

/-- Whenever max_nice_divisors primeFactors returns a result r, r ≡ 3^(k/3) (mod 1000000007), where k/3 is exact integer division.
  Preconditions: Let k be the integer value of primeFactors. Assume 1 <= k <= 10^9 and k mod 3 = 0 (so k >= 3). -/
theorem spec_6 (primeFactors : Aeneas.Std.I64)
    (hk1 : 1 ≤ primeFactors.val) (hk2 : primeFactors.val ≤ 1000000000)
    (hmod : primeFactors.val.toNat % 3 = 0) :
    ∀ r : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors primeFactors = ok r →
        Int.ModEq 1000000007 r.val ((3 : ℤ) ^ (primeFactors.val.toNat / 3)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (primeFactors : Aeneas.Std.I64)
    (hk1 : 1 ≤ primeFactors.val) (hk2 : primeFactors.val ≤ 1000000000)
    (hmod : primeFactors.val.toNat % 3 = 0), ∀ r : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors primeFactors = ok r →
        Int.ModEq 1000000007 r.val ((3 : ℤ) ^ (primeFactors.val.toNat / 3))) := by
  sorry

/-- Whenever max_nice_divisors primeFactors returns a result r, r ≡ 4 * 3^((k-4)/3) (mod 1000000007), where (k-4)/3 is exact integer division.
  Preconditions: Let k be the integer value of primeFactors. Assume 1 <= k <= 10^9, k mod 3 = 1, and k >= 4. -/
theorem spec_7 (primeFactors : Aeneas.Std.I64)
    (hk1 : 1 ≤ primeFactors.val) (hk2 : primeFactors.val ≤ 1000000000)
    (hmod : primeFactors.val.toNat % 3 = 1) (hk4 : 4 ≤ primeFactors.val.toNat) :
    ∀ r : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors primeFactors = ok r →
        Int.ModEq 1000000007 r.val
          (4 * (3 : ℤ) ^ ((primeFactors.val.toNat - 4) / 3)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (primeFactors : Aeneas.Std.I64)
    (hk1 : 1 ≤ primeFactors.val) (hk2 : primeFactors.val ≤ 1000000000)
    (hmod : primeFactors.val.toNat % 3 = 1) (hk4 : 4 ≤ primeFactors.val.toNat), ∀ r : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors primeFactors = ok r →
        Int.ModEq 1000000007 r.val
          (4 * (3 : ℤ) ^ ((primeFactors.val.toNat - 4) / 3))) := by
  sorry

/-- Whenever max_nice_divisors primeFactors returns a result r, r ≡ 2 * 3^((k-2)/3) (mod 1000000007), where (k-2)/3 is exact integer division.
  Preconditions: Let k be the integer value of primeFactors. Assume 1 <= k <= 10^9 and k mod 3 = 2 (so k >= 2). -/
theorem spec_8 (primeFactors : Aeneas.Std.I64)
    (hk1 : 1 ≤ primeFactors.val) (hk2 : primeFactors.val ≤ 1000000000)
    (hmod : primeFactors.val.toNat % 3 = 2) :
    ∀ r : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors primeFactors = ok r →
        Int.ModEq 1000000007 r.val
          (2 * (3 : ℤ) ^ ((primeFactors.val.toNat - 2) / 3)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (primeFactors : Aeneas.Std.I64)
    (hk1 : 1 ≤ primeFactors.val) (hk2 : primeFactors.val ≤ 1000000000)
    (hmod : primeFactors.val.toNat % 3 = 2), ∀ r : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors primeFactors = ok r →
        Int.ModEq 1000000007 r.val
          (2 * (3 : ℤ) ^ ((primeFactors.val.toNat - 2) / 3))) := by
  sorry

/-- If max_nice_divisors on input k returns a and max_nice_divisors on input k+3 returns b, then b ≡ 3*a (mod 1000000007).
  Preconditions: Let k be an integer with 2 <= k <= 999999997. -/
theorem spec_9 (x y : Aeneas.Std.I64)
    (hk1 : 2 ≤ x.val) (hk2 : x.val ≤ 999999997) (hy : y.val = x.val + 3) :
    ∀ a b : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors x = ok a →
        Aegis.MaxNiceDivisors.max_nice_divisors y = ok b →
          Int.ModEq 1000000007 b.val (3 * a.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (x y : Aeneas.Std.I64)
    (hk1 : 2 ≤ x.val) (hk2 : x.val ≤ 999999997) (hy : y.val = x.val + 3), ∀ a b : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors x = ok a →
        Aegis.MaxNiceDivisors.max_nice_divisors y = ok b →
          Int.ModEq 1000000007 b.val (3 * a.val)) := by
  sorry

/-- Whenever max_nice_divisors primeFactors returns a result r, there exists a positive integer n such that Ω(n) <= k and r ≡ N(n) (mod 1000000007), where Ω(n) is the number of prime factors of n counted with multiplicity (Ω(1)=0), and N(n) is the number of divisors of n that are divisible by every prime that divides n (with N(1)=1).
  Preconditions: Let k be the integer value of primeFactors. Assume 1 <= k <= 10^9. -/
theorem spec_10 (primeFactors : Aeneas.Std.I64)
    (hk1 : 1 ≤ primeFactors.val) (hk2 : primeFactors.val ≤ 1000000000) :
    ∀ r : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors primeFactors = ok r →
        ∃ n : ℕ, 0 < n ∧ Omega n ≤ primeFactors.val.toNat ∧
          Int.ModEq 1000000007 r.val ((niceDivisorCount n : ℕ) : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (primeFactors : Aeneas.Std.I64)
    (hk1 : 1 ≤ primeFactors.val) (hk2 : primeFactors.val ≤ 1000000000), ∀ r : Aeneas.Std.I64,
      Aegis.MaxNiceDivisors.max_nice_divisors primeFactors = ok r →
        ∃ n : ℕ, 0 < n ∧ Omega n ≤ primeFactors.val.toNat ∧
          Int.ModEq 1000000007 r.val ((niceDivisorCount n : ℕ) : ℤ)) := by
  sorry

end AegisSpec.MaxNiceDivisors
