import Aegis.SuperEggDrop.Code.Funs

/-!
# Specifications of `Aegis.SuperEggDrop.super_egg_drop`

LeetCode problem `super-egg-drop`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SuperEggDrop

def binomial (m i : ℕ) : ℕ := m.choose i

def F (e m : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 (min e m), binomial m i

def IsLeastMoves (k n r : ℕ) : Prop :=
  1 ≤ r ∧ n ≤ F k r ∧ ∀ m, 1 ≤ m → m < r → F k m < n

def L (n : ℕ) : ℕ :=
  Nat.find (p := fun m => n + 1 ≤ 2 ^ m)
    ⟨n + 1, le_of_lt (Nat.lt_two_pow_self (n := n + 1))⟩

def T (n : ℕ) : ℕ :=
  Nat.find (p := fun m => 1 ≤ m ∧ n ≤ m * (m + 1) / 2)
    ⟨n + 1, by
      refine ⟨by omega, ?_⟩
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      nlinarith⟩

def IsLeastTri (n r : ℕ) : Prop :=
  1 ≤ r ∧ n ≤ r * (r + 1) / 2 ∧ (r - 1) * r / 2 < n

/-- Whenever super_egg_drop(k,n) returns a result r (i.e. Result.ok r), r is the least integer m >= 1 such that F(k,m) >= n, where for integers e >= 0 and m >= 0, F(e,m) = sum_{i=1}^{min(e,m)} binom(m,i). Here binom(m,i) is the usual binomial coefficient (the number of i-element subsets of an m-element set, and 0 if i < 0 or i > m). Equivalently, F(e,m) is the maximum number N of floors such that the unknown break floor f in {0,...,N} can be determined with certainty using at most m drops and e eggs. Thus r is the minimum worst-case number of drops needed with k eggs on n floors.
  Preconditions: The parameters k and n are the mathematical integer values of the Std.I64 arguments, and 1 <= k <= 100 and 1 <= n <= 10000. -/
theorem spec_1 (k n : Std.I64)
    (hk1 : (1 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r →
      IsLeastMoves k.val.toNat n.val.toNat r.val.toNat := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (k n : Std.I64)
    (hk1 : (1 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r →
      IsLeastMoves k.val.toNat n.val.toNat r.val.toNat) := by
  sorry

/-- For every pair (k,n) satisfying the preconditions, super_egg_drop(k,n) returns a result (Result.ok r) and does not fail; in particular there is no arithmetic overflow, panic, or out-of-bounds access.
  Preconditions: The parameters k and n are the mathematical integer values of the Std.I64 arguments, and 1 <= k <= 100 and 1 <= n <= 10000. -/
theorem spec_2 (k n : Std.I64)
    (hk1 : (1 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∃ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (k n : Std.I64)
    (hk1 : (1 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000), ∃ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r) := by
  sorry

/-- Whenever super_egg_drop(k,n) returns r, 2^r >= n + 1. Equivalently, r is at least the least integer L with 2^L >= n+1.
  Preconditions: The parameters k and n are the mathematical integer values of the Std.I64 arguments, and 1 <= k <= 100 and 1 <= n <= 10000. -/
theorem spec_3 (k n : Std.I64)
    (hk1 : (1 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r →
      n.val + 1 ≤ 2 ^ r.val.toNat := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (k n : Std.I64)
    (hk1 : (1 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r →
      n.val + 1 ≤ 2 ^ r.val.toNat) := by
  sorry

/-- Whenever super_egg_drop(k,n) returns r, r <= n.
  Preconditions: The parameters k and n are the mathematical integer values of the Std.I64 arguments, and 1 <= k <= 100 and 1 <= n <= 10000. -/
theorem spec_4 (k n : Std.I64)
    (hk1 : (1 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r → r.val ≤ n.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (k n : Std.I64)
    (hk1 : (1 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r → r.val ≤ n.val) := by
  sorry

/-- Whenever super_egg_drop(1,n) returns r, r = n.
  Preconditions: The parameters k and n are the mathematical integer values of the Std.I64 arguments, with k = 1 and 1 <= n <= 10000. -/
theorem spec_5 (k n : Std.I64)
    (hk : k.val = 1)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r → r.val = n.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (k n : Std.I64)
    (hk : k.val = 1)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r → r.val = n.val) := by
  sorry

/-- Whenever super_egg_drop(k,1) returns r, r = 1.
  Preconditions: The parameters k and n are the mathematical integer values of the Std.I64 arguments, with 1 <= k <= 100 and n = 1. -/
theorem spec_6 (k n : Std.I64)
    (hk1 : (1 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hn : n.val = 1) :
    ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r → r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (k n : Std.I64)
    (hk1 : (1 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hn : n.val = 1), ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r → r.val = 1) := by
  sorry

/-- Whenever super_egg_drop(2,n) returns r, r is the least integer m >= 1 with m(m+1)/2 >= n. Equivalently, r >= 1, r(r+1)/2 >= n, and (r-1)r/2 < n.
  Preconditions: The parameters k and n are the mathematical integer values of the Std.I64 arguments, with k = 2 and 1 <= n <= 10000. -/
theorem spec_7 (n : Std.I64)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r : Std.I64,
      Aegis.SuperEggDrop.super_egg_drop (Std.I64.ofInt 2) n = ok r →
      IsLeastTri n.val.toNat r.val.toNat := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r : Std.I64,
      Aegis.SuperEggDrop.super_egg_drop (Std.I64.ofInt 2) n = ok r →
      IsLeastTri n.val.toNat r.val.toNat) := by
  sorry

/-- Whenever super_egg_drop(k,n) returns r, r = L(n).
  Preconditions: The parameters k and n are the mathematical integer values of the Std.I64 arguments, with 1 <= n <= 10000, 1 <= k <= 100, and k >= L(n), where L(n) is the least integer m >= 0 with 2^m >= n+1. -/
theorem spec_8 (k n : Std.I64)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000)
    (hk1 : (1 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hkL : (L n.val.toNat : ℤ) ≤ k.val) :
    ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r →
      r.val = (L n.val.toNat : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (k n : Std.I64)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000)
    (hk1 : (1 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hkL : (L n.val.toNat : ℤ) ≤ k.val), ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r →
      r.val = (L n.val.toNat : ℤ)) := by
  sorry

/-- Let F(e,m) = sum_{i=1}^{min(e,m)} binom(m,i), where binom is the usual binomial coefficient. Whenever super_egg_drop(k,n) returns r, F(k,r) >= n; therefore r drops are sufficient: there exists a strategy using k eggs and at most r drops that determines f with certainty for every possible f in {0,...,n}.
  Preconditions: The parameters k and n are the mathematical integer values of the Std.I64 arguments, and 1 <= k <= 100 and 1 <= n <= 10000. -/
theorem spec_9 (k n : Std.I64)
    (hk1 : (1 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r →
      n.val ≤ (F k.val.toNat r.val.toNat : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (k n : Std.I64)
    (hk1 : (1 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r →
      n.val ≤ (F k.val.toNat r.val.toNat : ℤ)) := by
  sorry

/-- Let F(e,m) = sum_{i=1}^{min(e,m)} binom(m,i), where binom is the usual binomial coefficient. Whenever super_egg_drop(k,n) returns r, for every integer m with 0 <= m < r, F(k,m) < n. Equivalently, no strategy with k eggs and at most r-1 drops can determine f with certainty for all f in {0,...,n}.
  Preconditions: The parameters k and n are the mathematical integer values of the Std.I64 arguments, and 1 <= k <= 100 and 1 <= n <= 10000. -/
theorem spec_10 (k n : Std.I64)
    (hk1 : (1 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r →
      ∀ m : ℕ, (m : ℤ) < r.val → (F k.val.toNat m : ℤ) < n.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (k n : Std.I64)
    (hk1 : (1 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r →
      ∀ m : ℕ, (m : ℤ) < r.val → (F k.val.toNat m : ℤ) < n.val) := by
  sorry

/-- If super_egg_drop(k,n1) returns r1 and super_egg_drop(k,n2) returns r2, then r1 <= r2.
  Preconditions: The parameters k, n1, and n2 are mathematical integer values of Std.I64 arguments, with 1 <= k <= 100 and 1 <= n1 <= n2 <= 10000. -/
theorem spec_11 (k n₁ n₂ : Std.I64)
    (hk1 : (1 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hn1' : (1 : ℤ) ≤ n₁.val) (hn12 : n₁.val ≤ n₂.val) (hn2' : n₂.val ≤ 10000) :
    ∀ r₁ r₂ : Std.I64,
      Aegis.SuperEggDrop.super_egg_drop k n₁ = ok r₁ →
      Aegis.SuperEggDrop.super_egg_drop k n₂ = ok r₂ → r₁.val ≤ r₂.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (k n₁ n₂ : Std.I64)
    (hk1 : (1 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hn1' : (1 : ℤ) ≤ n₁.val) (hn12 : n₁.val ≤ n₂.val) (hn2' : n₂.val ≤ 10000), ∀ r₁ r₂ : Std.I64,
      Aegis.SuperEggDrop.super_egg_drop k n₁ = ok r₁ →
      Aegis.SuperEggDrop.super_egg_drop k n₂ = ok r₂ → r₁.val ≤ r₂.val) := by
  sorry

/-- If super_egg_drop(k1,n) returns r1 and super_egg_drop(k2,n) returns r2, then r2 <= r1.
  Preconditions: The parameters n, k1, and k2 are mathematical integer values of Std.I64 arguments, with 1 <= n <= 10000 and 1 <= k1 <= k2 <= 100. -/
theorem spec_12 (n k₁ k₂ : Std.I64)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000)
    (hk1' : (1 : ℤ) ≤ k₁.val) (hk12 : k₁.val ≤ k₂.val) (hk2' : k₂.val ≤ 100) :
    ∀ r₁ r₂ : Std.I64,
      Aegis.SuperEggDrop.super_egg_drop k₁ n = ok r₁ →
      Aegis.SuperEggDrop.super_egg_drop k₂ n = ok r₂ → r₂.val ≤ r₁.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n k₁ k₂ : Std.I64)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000)
    (hk1' : (1 : ℤ) ≤ k₁.val) (hk12 : k₁.val ≤ k₂.val) (hk2' : k₂.val ≤ 100), ∀ r₁ r₂ : Std.I64,
      Aegis.SuperEggDrop.super_egg_drop k₁ n = ok r₁ →
      Aegis.SuperEggDrop.super_egg_drop k₂ n = ok r₂ → r₂.val ≤ r₁.val) := by
  sorry

/-- If super_egg_drop(k1,n) returns r and k1 >= r, then if super_egg_drop(k2,n) returns r2, we have r2 = r.
  Preconditions: The parameters n, k1, and k2 are mathematical integer values of Std.I64 arguments, with 1 <= n <= 10000 and 1 <= k1 <= k2 <= 100. -/
theorem spec_13 (n k₁ k₂ : Std.I64)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000)
    (hk1' : (1 : ℤ) ≤ k₁.val) (hk12 : k₁.val ≤ k₂.val) (hk2' : k₂.val ≤ 100) :
    ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k₁ n = ok r → r.val ≤ k₁.val →
      ∀ r₂ : Std.I64, Aegis.SuperEggDrop.super_egg_drop k₂ n = ok r₂ → r₂.val = r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n k₁ k₂ : Std.I64)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000)
    (hk1' : (1 : ℤ) ≤ k₁.val) (hk12 : k₁.val ≤ k₂.val) (hk2' : k₂.val ≤ 100), ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k₁ n = ok r → r.val ≤ k₁.val →
      ∀ r₂ : Std.I64, Aegis.SuperEggDrop.super_egg_drop k₂ n = ok r₂ → r₂.val = r.val) := by
  sorry

/-- Let T(n) be the least integer m >= 1 with m(m+1)/2 >= n. Whenever super_egg_drop(k,n) returns r, r <= T(n).
  Preconditions: The parameters k and n are mathematical integer values of Std.I64 arguments, with 2 <= k <= 100 and 1 <= n <= 10000. -/
theorem spec_14 (k n : Std.I64)
    (hk1 : (2 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r →
      r.val ≤ (T n.val.toNat : ℤ) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (k n : Std.I64)
    (hk1 : (2 : ℤ) ≤ k.val) (hk2 : k.val ≤ 100)
    (hn1 : (1 : ℤ) ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r : Std.I64, Aegis.SuperEggDrop.super_egg_drop k n = ok r →
      r.val ≤ (T n.val.toNat : ℤ)) := by
  sorry

end AegisSpec.SuperEggDrop
