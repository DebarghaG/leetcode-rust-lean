import Aegis.SelfDivisiblePermutationCount.Code.Funs

/-!
# Specifications of `Aegis.SelfDivisiblePermutationCount.self_divisible_permutation_count`

LeetCode problem `number-of-self-divisible-permutations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SelfDivisiblePermutationCount

open Classical

def IsPerm (n : Nat) (p : Fin n → Fin n) : Prop :=
  Function.Bijective p

def SelfDivisible (n : Nat) (p : Fin n → Fin n) : Prop :=
  ∀ j : Fin n, Nat.gcd ((p j).val + 1) (j.val + 1) = 1

noncomputable def selfDivisiblePerms (n : Nat) : Finset (Fin n → Fin n) :=
  Finset.univ.filter (fun p => IsPerm n p ∧ SelfDivisible n p)

noncomputable def selfDivisiblePermCount (n : Nat) : Nat :=
  (selfDivisiblePerms n).card

def oddCount (n : Nat) : Nat :=
  ((Finset.range n).filter (fun i => (i + 1) % 2 = 1)).card

def fact (n : Nat) : Int :=
  (Nat.factorial n : Int)

def gcdMatrix (n : Nat) (i j : Fin n) : Int :=
  if Nat.gcd (i.val + 1) (j.val + 1) = 1 then 1 else 0

def permGcdMatrix (n : Nat) : Int :=
  ∑ p ∈ (Finset.univ.filter (fun p : Fin n → Fin n => Function.Bijective p)),
    ∏ i : Fin n, gcdMatrix n i (p i)

/-- Let a permutation of [1, n] be a bijection p : {1, 2, ..., n} -> {1, 2, ..., n}, represented as a 1-indexed sequence of length n containing each integer from 1 to n exactly once. Call such a permutation self-divisible if for every i with 1 <= i <= n, gcd(p(i), i) = 1. Let C(n) be the number of self-divisible permutations of [1, n]. Whenever self_divisible_permutation_count(n) returns a result r, it holds that r = C(n).
  Preconditions: n is an integer with 1 <= n <= 12. -/
theorem spec_1 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 12) :
    ∀ r : Std.I64,
      Aegis.SelfDivisiblePermutationCount.self_divisible_permutation_count n = ok r →
      r.val = (selfDivisiblePermCount n.val.toNat : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 12), ∀ r : Std.I64,
      Aegis.SelfDivisiblePermutationCount.self_divisible_permutation_count n = ok r →
      r.val = (selfDivisiblePermCount n.val.toNat : Int)) := by
  sorry

/-- self_divisible_permutation_count(n) returns a result (it does not fail, overflow, or panic).
  Preconditions: n is an integer with 1 <= n <= 12. -/
theorem spec_2 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 12) :
    ∃ r : Std.I64, Aegis.SelfDivisiblePermutationCount.self_divisible_permutation_count n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 12), ∃ r : Std.I64, Aegis.SelfDivisiblePermutationCount.self_divisible_permutation_count n = ok r) := by
  sorry

/-- Whenever self_divisible_permutation_count(n) returns a result r, 0 <= r <= n!, where n! = 1 * 2 * ... * n (and 0! = 1).
  Preconditions: n is an integer with 1 <= n <= 12. -/
theorem spec_3 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 12) :
    ∀ r : Std.I64,
      Aegis.SelfDivisiblePermutationCount.self_divisible_permutation_count n = ok r →
      0 ≤ r.val ∧ r.val ≤ fact n.val.toNat := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 12), ∀ r : Std.I64,
      Aegis.SelfDivisiblePermutationCount.self_divisible_permutation_count n = ok r →
      0 ≤ r.val ∧ r.val ≤ fact n.val.toNat) := by
  sorry

/-- Whenever self_divisible_permutation_count(n) returns a result r, r <= odd_count(n) * (n-1)!, where odd_count(n) is the number of odd integers in {1, 2, ..., n}.
  Preconditions: n is an integer with 1 <= n <= 12. -/
theorem spec_4 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 12) :
    ∀ r : Std.I64,
      Aegis.SelfDivisiblePermutationCount.self_divisible_permutation_count n = ok r →
      r.val ≤ (oddCount n.val.toNat : Int) * fact (n.val.toNat - 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 12), ∀ r : Std.I64,
      Aegis.SelfDivisiblePermutationCount.self_divisible_permutation_count n = ok r →
      r.val ≤ (oddCount n.val.toNat : Int) * fact (n.val.toNat - 1)) := by
  sorry

/-- Whenever self_divisible_permutation_count(n) returns a result r, r >= 1.
  Preconditions: n is an integer with 1 <= n <= 12. -/
theorem spec_5 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 12) :
    ∀ r : Std.I64,
      Aegis.SelfDivisiblePermutationCount.self_divisible_permutation_count n = ok r →
      1 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 12), ∀ r : Std.I64,
      Aegis.SelfDivisiblePermutationCount.self_divisible_permutation_count n = ok r →
      1 ≤ r.val) := by
  sorry

/-- Whenever self_divisible_permutation_count(n) returns a result r, r equals the permanent of the n x n matrix A (1-indexed) defined by A[i][j] = 1 if gcd(i, j) = 1, and A[i][j] = 0 otherwise. The permanent is sum_{p} product_{i=1}^n A[i][p(i)], where the sum is over all permutations p of {1, 2, ..., n}.
  Preconditions: n is an integer with 1 <= n <= 12. -/
theorem spec_6 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 12) :
    ∀ r : Std.I64,
      Aegis.SelfDivisiblePermutationCount.self_divisible_permutation_count n = ok r →
      r.val = permGcdMatrix n.val.toNat := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 12), ∀ r : Std.I64,
      Aegis.SelfDivisiblePermutationCount.self_divisible_permutation_count n = ok r →
      r.val = permGcdMatrix n.val.toNat) := by
  sorry

end AegisSpec.SelfDivisiblePermutationCount
