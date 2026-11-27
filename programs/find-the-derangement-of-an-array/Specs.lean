import Aegis.FindDerangement.Code.Funs

/-!
# Specifications of `Aegis.FindDerangement.find_derangement`

LeetCode problem `find-the-derangement-of-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindDerangement

  noncomputable def numDerangements (n : ℕ) : ℕ :=
    Nat.card { σ : Equiv.Perm (Fin n) // ∀ i : Fin n, σ i ≠ i }

  def alternatingBinomialFactorialSum (n : ℕ) : ℤ :=
    ∑ k ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ k * (n.choose k : ℤ) * (Nat.factorial (n - k) : ℤ)

  noncomputable def modInv (a : ℕ) : ℕ :=
    if h : ∃ x : ℕ, x < 1000000007 ∧ a * x % 1000000007 = 1 then Nat.find h else 0

  noncomputable def inverseFactorialSum (n : ℕ) : ℤ :=
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (modInv (Nat.factorial k) : ℤ)

  /-- Let D(n) be the number of permutations π of {1,...,n} for which π(i) ≠ i for every i with 1 ≤ i ≤ n. For every n with 1 ≤ n ≤ 1,000,000, find_derangement n returns a result r such that 0 ≤ r < 1,000,000,007 and r ≡ D(n) (mod 1,000,000,007); equivalently r is the least nonnegative residue of D(n) modulo 1,000,000,007.
    Preconditions: 1 ≤ n ≤ 1,000,000 -/
  theorem spec_1 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000) :
      ∃ r : Std.I64,
        Aegis.FindDerangement.find_derangement n = ok r ∧
          0 ≤ r.val ∧ r.val < 1000000007 ∧
            Int.ModEq (1000000007 : ℤ) r.val ((numDerangements n.val.toNat : ℕ) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000), ∃ r : Std.I64,
          Aegis.FindDerangement.find_derangement n = ok r ∧
            0 ≤ r.val ∧ r.val < 1000000007 ∧
              Int.ModEq (1000000007 : ℤ) r.val ((numDerangements n.val.toNat : ℕ) : ℤ)) := by
    sorry

  /-- For every n with 1 ≤ n ≤ 1,000,000, find_derangement n returns a result; it does not fail, overflow, or panic.
    Preconditions: 1 ≤ n ≤ 1,000,000 -/
  theorem spec_2 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000) :
      ∃ r : Std.I64, Aegis.FindDerangement.find_derangement n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000), ∃ r : Std.I64, Aegis.FindDerangement.find_derangement n = ok r) := by
    sorry

  /-- Let D(k) be the number of derangements of {1,...,k}. For every n with 3 ≤ n ≤ 1,000,000, whenever find_derangement n returns a result r, r ≡ (n-1) * (D(n-1) + D(n-2)) (mod 1,000,000,007).
    Preconditions: 3 ≤ n ≤ 1,000,000 -/
  theorem spec_3 (n : Std.I64) (hn_lo : 3 ≤ n.val) (hn_hi : n.val ≤ 1000000) :
      ∀ r : Std.I64,
        Aegis.FindDerangement.find_derangement n = ok r →
          Int.ModEq (1000000007 : ℤ) r.val
            ((n.val - 1) *
              ((numDerangements (n.val.toNat - 1) : ℕ) +
                (numDerangements (n.val.toNat - 2) : ℕ))) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 3 ≤ n.val) (hn_hi : n.val ≤ 1000000), ∀ r : Std.I64,
          Aegis.FindDerangement.find_derangement n = ok r →
            Int.ModEq (1000000007 : ℤ) r.val
              ((n.val - 1) *
                ((numDerangements (n.val.toNat - 1) : ℕ) +
                  (numDerangements (n.val.toNat - 2) : ℕ)))) := by
    sorry

  /-- Let D(k) be the number of derangements of {1,...,k}, with D(1)=0. For every n with 2 ≤ n ≤ 1,000,000, whenever find_derangement n returns a result r, r ≡ n * D(n-1) + (-1)^n (mod 1,000,000,007), where (-1)^n means +1 for even n and -1 for odd n.
    Preconditions: 2 ≤ n ≤ 1,000,000 -/
  theorem spec_4 (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000000) :
      ∀ r : Std.I64,
        Aegis.FindDerangement.find_derangement n = ok r →
          Int.ModEq (1000000007 : ℤ) r.val
            (n.val * ((numDerangements (n.val.toNat - 1) : ℕ) : ℤ) +
              (-1 : ℤ) ^ n.val.toNat) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000000), ∀ r : Std.I64,
          Aegis.FindDerangement.find_derangement n = ok r →
            Int.ModEq (1000000007 : ℤ) r.val
              (n.val * ((numDerangements (n.val.toNat - 1) : ℕ) : ℤ) +
                (-1 : ℤ) ^ n.val.toNat)) := by
    sorry

  /-- For every n with 1 ≤ n ≤ 1,000,000, whenever find_derangement n returns a result r, r ≡ Σ_{k=0}^{n} (-1)^k * C(n,k) * (n-k)! (mod 1,000,000,007), where C(n,k) is the binomial coefficient and 0! = 1.
    Preconditions: 1 ≤ n ≤ 1,000,000 -/
  theorem spec_5 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000) :
      ∀ r : Std.I64,
        Aegis.FindDerangement.find_derangement n = ok r →
          Int.ModEq (1000000007 : ℤ) r.val
            (alternatingBinomialFactorialSum n.val.toNat) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000), ∀ r : Std.I64,
          Aegis.FindDerangement.find_derangement n = ok r →
            Int.ModEq (1000000007 : ℤ) r.val
              (alternatingBinomialFactorialSum n.val.toNat)) := by
    sorry

  /-- For every n with 1 ≤ n ≤ 1,000,000, whenever find_derangement n returns a result r, r ≡ n! * Σ_{k=0}^{n} (-1)^k * inv(k!) (mod 1,000,000,007), where inv(k!) is the modular inverse of k! modulo 1,000,000,007 and 0! = 1.
    Preconditions: 1 ≤ n ≤ 1,000,000 -/
  theorem spec_6 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000) :
      ∀ r : Std.I64,
        Aegis.FindDerangement.find_derangement n = ok r →
          Int.ModEq (1000000007 : ℤ) r.val
            ((Nat.factorial n.val.toNat : ℤ) * inverseFactorialSum n.val.toNat) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000), ∀ r : Std.I64,
          Aegis.FindDerangement.find_derangement n = ok r →
            Int.ModEq (1000000007 : ℤ) r.val
              ((Nat.factorial n.val.toNat : ℤ) * inverseFactorialSum n.val.toNat)) := by
    sorry

  end AegisSpec.FindDerangement
