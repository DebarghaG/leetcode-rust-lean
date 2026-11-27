import Aegis.NumPrimeArrangements.Code.Funs

/-!
# Specifications of `Aegis.NumPrimeArrangements.num_prime_arrangements`

LeetCode problem `prime-arrangements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumPrimeArrangements

def M : Int := 1000000007

def IsPrimeInt (p : Int) : Prop :=
  1 < p ∧ ∀ d : Int, 0 < d → d ∣ p → d = 1 ∨ d = p

theorem isPrimeInt_natCast_iff (p : Nat) : IsPrimeInt (p : Int) ↔ Nat.Prime p := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [Nat.prime_def_lt]
    refine ⟨by omega, ?_⟩
    intro m hmp hm
    have hp0 : p ≠ 0 := by omega
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hp0 (Nat.eq_zero_of_zero_dvd hm)
    have hdvd : (m : Int) ∣ (p : Int) := Int.natCast_dvd_natCast.mpr hm
    have hpos : 0 < (m : Int) := by
      have h : 0 < m := Nat.pos_of_ne_zero hm0
      omega
    rcases h2 (m : Int) hpos hdvd with h | h
    · omega
    · omega
  · intro hp
    refine ⟨by have := hp.two_le; omega, ?_⟩
    intro d hd hdvd
    have hdvd' : d.natAbs ∣ p := by
      have h1 : d.natAbs ∣ (p : Int).natAbs := Int.natAbs_dvd_natAbs.mpr hdvd
      rwa [Int.natAbs_natCast] at h1
    have h' : (d.natAbs : Int) = d := Int.natAbs_of_nonneg (by omega)
    rcases hp.eq_one_or_self_of_dvd _ hdvd' with h | h
    · left; omega
    · right; omega

def primeCount (n : Int) : Int :=
  ↑((Finset.Icc 1 n.toNat).filter Nat.Prime).card

def arrangementCount (n : Int) : Nat :=
  (primeCount n).toNat.factorial * (n - primeCount n).toNat.factorial

def arrangementCountMod (n : Int) : Int := (arrangementCount n : Int) % M

/-- Let M = 1000000007. Let P(n) be the number of primes p with 1 <= p <= n, where an integer p is prime iff p > 1 and its only positive divisors are 1 and p. Let k! denote the factorial of k with 0! = 1. The function returns a result r and r = (P(n)! * (n - P(n))!) mod M, where mod M denotes the unique integer in [0, M-1] congruent modulo M. Equivalently, r is the number of permutations of 1,2,...,n in which every prime number occurs at a prime 1-indexed position, reduced modulo M.
  Preconditions: n is an integer with 1 <= n <= 100. -/
theorem spec_1 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 100) :
    ∃ r : Std.I64, Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r ∧
      r.val = arrangementCountMod n.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 100), ∃ r : Std.I64, Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r ∧
      r.val = arrangementCountMod n.val) := by
  sorry

/-- For every integer n with 1 <= n <= 100, the function returns a result; in particular, it does not fail, panic, overflow, or go out of bounds.
  Preconditions: n is an integer with 1 <= n <= 100. -/
theorem spec_2 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 100) :
    ∃ r : Std.I64, Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 100), ∃ r : Std.I64, Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r) := by
  sorry

/-- Whenever the function returns a result r for an integer n with 1 <= n <= 100, the value r satisfies 0 <= r < 1000000007.
  Preconditions: n is an integer with 1 <= n <= 100. -/
theorem spec_3 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 100) (r : Std.I64)
    (hr : Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r) :
    0 ≤ r.val ∧ r.val < M := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 100) (r : Std.I64)
    (hr : Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r), 0 ≤ r.val ∧ r.val < M) := by
  sorry

/-- Whenever the function returns a result r for an integer n with 1 <= n <= 100, the value r satisfies 1 <= r < 1000000007.
  Preconditions: n is an integer with 1 <= n <= 100. -/
theorem spec_4 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 100) (r : Std.I64)
    (hr : Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r) :
    1 ≤ r.val ∧ r.val < M := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 100) (r : Std.I64)
    (hr : Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r), 1 ≤ r.val ∧ r.val < M) := by
  sorry

/-- Whenever the function returns a result r for an integer n with 1 <= n <= 100, r is congruent modulo 1000000007 to P(n)! * (n - P(n))!, where P(n) is the number of primes p with 1 <= p <= n.
  Preconditions: n is an integer with 1 <= n <= 100. -/
theorem spec_5 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 100) (r : Std.I64)
    (hr : Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r) :
    Int.ModEq M r.val (arrangementCount n.val : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 100) (r : Std.I64)
    (hr : Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r), Int.ModEq M r.val (arrangementCount n.val : Int)) := by
  sorry

/-- The function returns result 1.
  Preconditions: n is an integer with n = 1. -/
theorem spec_6 (n : Std.I64) (hn : n.val = 1) :
    ∃ r : Std.I64, Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r ∧ r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 1), ∃ r : Std.I64, Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r ∧ r.val = 1) := by
  sorry

/-- The function returns result 2.
  Preconditions: n is an integer with n = 3. -/
theorem spec_7 (n : Std.I64) (hn : n.val = 3) :
    ∃ r : Std.I64, Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r ∧ r.val = 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 3), ∃ r : Std.I64, Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r ∧ r.val = 2) := by
  sorry

/-- Whenever the function returns a result r on input n and a result s on input n-1, r is congruent modulo 1000000007 to (P(n-1) + 1) * s, where P(n-1) is the number of primes p with 1 <= p <= n-1.
  Preconditions: n is an integer with 2 <= n <= 100 and n is prime. -/
theorem spec_8 (n m : Std.I64) (h1 : 2 ≤ n.val) (h2 : n.val ≤ 100) (hm : m.val = n.val - 1)
    (hp : IsPrimeInt n.val) (r s : Std.I64)
    (hr : Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r)
    (hs : Aegis.NumPrimeArrangements.num_prime_arrangements m = ok s) :
    Int.ModEq M r.val ((primeCount (n.val - 1) + 1) * s.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n m : Std.I64) (h1 : 2 ≤ n.val) (h2 : n.val ≤ 100) (hm : m.val = n.val - 1)
    (hp : IsPrimeInt n.val) (r s : Std.I64)
    (hr : Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r)
    (hs : Aegis.NumPrimeArrangements.num_prime_arrangements m = ok s), Int.ModEq M r.val ((primeCount (n.val - 1) + 1) * s.val)) := by
  sorry

/-- Whenever the function returns a result r on input n and a result s on input n-1, r is congruent modulo 1000000007 to (n - P(n-1)) * s, where P(n-1) is the number of primes p with 1 <= p <= n-1.
  Preconditions: n is an integer with 2 <= n <= 100 and n is not prime. -/
theorem spec_9 (n m : Std.I64) (h1 : 2 ≤ n.val) (h2 : n.val ≤ 100) (hm : m.val = n.val - 1)
    (hp : ¬ IsPrimeInt n.val) (r s : Std.I64)
    (hr : Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r)
    (hs : Aegis.NumPrimeArrangements.num_prime_arrangements m = ok s) :
    Int.ModEq M r.val ((n.val - primeCount (n.val - 1)) * s.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n m : Std.I64) (h1 : 2 ≤ n.val) (h2 : n.val ≤ 100) (hm : m.val = n.val - 1)
    (hp : ¬ IsPrimeInt n.val) (r s : Std.I64)
    (hr : Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r)
    (hs : Aegis.NumPrimeArrangements.num_prime_arrangements m = ok s), Int.ModEq M r.val ((n.val - primeCount (n.val - 1)) * s.val)) := by
  sorry

/-- The function returns result 12.
  Preconditions: n is an integer with n = 5. -/
theorem spec_10 (n : Std.I64) (hn : n.val = 5) :
    ∃ r : Std.I64, Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r ∧ r.val = 12 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 5), ∃ r : Std.I64, Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r ∧ r.val = 12) := by
  sorry

/-- The function returns result 682289015.
  Preconditions: n is an integer with n = 100. -/
theorem spec_11 (n : Std.I64) (hn : n.val = 100) :
    ∃ r : Std.I64, Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r ∧
      r.val = 682289015 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 100), ∃ r : Std.I64, Aegis.NumPrimeArrangements.num_prime_arrangements n = ok r ∧
      r.val = 682289015) := by
  sorry

end AegisSpec.NumPrimeArrangements
