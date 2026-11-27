import Aegis.MinSteps.Code.Funs

/-!
# Specifications of `Aegis.MinSteps.min_steps`

LeetCode problem `2-keys-keyboard`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinSteps

inductive Op where
  | copyAll
  | paste
  deriving DecidableEq, Repr

def Op.step : Op → ℤ × ℤ → ℤ × ℤ
  | .copyAll, st => (st.1, st.1)
  | .paste, st => (st.1 + st.2, st.2)

def runOps (st : ℤ × ℤ) : List Op → ℤ × ℤ
  | [] => st
  | o :: os => runOps (Op.step o st) os

def ReachesIn (n : ℤ) (k : ℕ) : Prop :=
  ∃ ops : List Op, ops.length = k ∧ (runOps (1, 0) ops).1 = n

def IsLeastStepCount (n r : ℤ) : Prop :=
  0 ≤ r ∧ ReachesIn n r.toNat ∧ ∀ k : ℕ, ReachesIn n k → r.toNat ≤ k

def IntPrime (m : ℤ) : Prop :=
  2 ≤ m ∧ ∀ d : ℤ, 1 ≤ d → d ∣ m → d = 1 ∨ d = m

def IntOddPrime (m : ℤ) : Prop :=
  2 < m ∧ ∀ d : ℤ, 1 ≤ d → d ∣ m → d = 1 ∨ d = m

def IntComposite (m : ℤ) : Prop :=
  ∃ a b : ℤ, 2 ≤ a ∧ 2 ≤ b ∧ a * b = m

def IntPrimePower (n p : ℤ) (k : ℕ) : Prop :=
  IntPrime p ∧ 2 ≤ k ∧ n = p ^ k

def IntTwoPrimePower (n p q : ℤ) (a b : ℕ) : Prop :=
  IntPrime p ∧ IntPrime q ∧ p ≠ q ∧ 1 ≤ a ∧ 1 ≤ b ∧ n = p ^ a * q ^ b

def IntLeastPrimeDivisor (p n : ℤ) : Prop :=
  IntPrime p ∧ p ∣ n ∧ ∀ q : ℤ, IntPrime q → q ∣ n → p ≤ q

def FactorSums (n s : ℤ) : Prop :=
  ∃ l : List ℤ, (∀ a ∈ l, 2 ≤ a) ∧ l.prod = n ∧ l.sum = s

/-- The function returns a result r and r is the least nonnegative integer k for which there exists a finite sequence of k operations, each operation being either Copy All or Paste, starting from the state (screen = 1, clipboard = 0), where Copy All changes a state (s, c) to (s, s) and Paste changes (s, c) to (s + c, c), such that after the k operations the screen equals n. The clipboard after the last operation is unconstrained.
  Preconditions: 1 <= n <= 1000 (n is the i64 parameter, interpreted as a mathematical integer). -/
theorem spec_1 (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000) :
    ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ IsLeastStepCount n.val r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000), ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ IsLeastStepCount n.val r.val) := by
  sorry

/-- The function returns a result r; in particular, it does not fail, overflow, or panic on any input in this range.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_2 (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000) :
    ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000), ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r) := by
  sorry

/-- The function returns a result r and r >= 0.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_3 (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000) :
    ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000), ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= n.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_4 (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000) :
    ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ r.val ≤ n.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000), ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ r.val ≤ n.val) := by
  sorry

/-- The function returns a result r and r >= 2.
  Preconditions: 2 <= n <= 1000. -/
theorem spec_5 (n : Aeneas.Std.I64) (h1 : 2 ≤ n.val) (h2 : n.val ≤ 1000) :
    ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ 2 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (h1 : 2 ≤ n.val) (h2 : n.val ≤ 1000), ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ 2 ≤ r.val) := by
  sorry

/-- The function returns a result r and r = 0.
  Preconditions: n = 1. -/
theorem spec_6 (n : Aeneas.Std.I64) (hn : n.val = 1) :
    ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : n.val = 1), ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r and r = 2.
  Preconditions: n = 2. -/
theorem spec_7 (n : Aeneas.Std.I64) (hn : n.val = 2) :
    ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ r.val = 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : n.val = 2), ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ r.val = 2) := by
  sorry

/-- The function returns a result r and r >= 3.
  Preconditions: 3 <= n <= 1000. -/
theorem spec_8 (n : Aeneas.Std.I64) (h1 : 3 ≤ n.val) (h2 : n.val ≤ 1000) :
    ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ 3 ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (h1 : 3 ≤ n.val) (h2 : n.val ≤ 1000), ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ 3 ≤ r.val) := by
  sorry

/-- The function returns a result r and r = n.
  Preconditions: 1 <= n <= 1000 and n is an odd prime (n > 2 and its only positive divisors are 1 and n). -/
theorem spec_9 (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000)
    (hp : IntOddPrime n.val) :
    ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ r.val = n.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000)
    (hp : IntOddPrime n.val), ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ r.val = n.val) := by
  sorry

/-- The function returns a result r and r < n.
  Preconditions: 1 <= n <= 1000, n is composite, and n != 4. -/
theorem spec_10 (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000)
    (hc : IntComposite n.val) (h4 : n.val ≠ 4) :
    ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ r.val < n.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000)
    (hc : IntComposite n.val) (h4 : n.val ≠ 4), ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ r.val < n.val) := by
  sorry

/-- The function returns a result r and r = k * p.
  Preconditions: 1 <= n <= 1000 and n = p^k for some prime p and integer k >= 2. -/
theorem spec_11 (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000)
    (p : ℤ) (k : ℕ) (hpk : IntPrimePower n.val p k) :
    ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ r.val = (k : ℤ) * p := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000)
    (p : ℤ) (k : ℕ) (hpk : IntPrimePower n.val p k), ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ r.val = (k : ℤ) * p) := by
  sorry

/-- The function returns a result r and r = a * p + b * q.
  Preconditions: 1 <= n <= 1000 and n = p^a * q^b where p and q are distinct primes and a >= 1, b >= 1 are integers. -/
theorem spec_12 (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000)
    (p q : ℤ) (a b : ℕ) (hpq : IntTwoPrimePower n.val p q a b) :
    ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ r.val = (a : ℤ) * p + (b : ℤ) * q := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000)
    (p q : ℤ) (a b : ℕ) (hpq : IntTwoPrimePower n.val p q a b), ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ r.val = (a : ℤ) * p + (b : ℤ) * q) := by
  sorry

/-- The function returns a result r and n <= 2^r, where 2^r is the usual integer power and r is the nonnegative operation count.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_13 (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000) :
    ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ n.val ≤ (2 : ℤ) ^ r.val.toNat := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000), ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ n.val ≤ (2 : ℤ) ^ r.val.toNat) := by
  sorry

/-- The function returns a result r and r >= p.
  Preconditions: 1 <= n <= 1000, n > 1, and p is the smallest prime divisor of n (the least prime p such that p divides n). -/
theorem spec_14 (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000) (hgt : 1 < n.val)
    (p : ℤ) (hp : IntLeastPrimeDivisor p n.val) :
    ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ p ≤ r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000) (hgt : 1 < n.val)
    (p : ℤ) (hp : IntLeastPrimeDivisor p n.val), ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ p ≤ r.val) := by
  sorry

/-- The function returns a result r and there exists a finite sequence of exactly r operations, each being Copy All or Paste, starting from the state (screen = 1, clipboard = 0), where Copy All changes (s, c) to (s, s) and Paste changes (s, c) to (s + c, c), such that after the r operations the screen equals n.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_15 (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000) :
    ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ ReachesIn n.val r.val.toNat := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000), ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧ ReachesIn n.val r.val.toNat) := by
  sorry

/-- The function returns a result r; r = 0 when n = 1, and for n >= 2, r equals the sum of the prime factors of n counted with multiplicity (equivalently, the minimum over all factorizations n = a1 * ... * ak with each ai >= 2 of a1 + ... + ak).
  Preconditions: 1 <= n <= 1000. -/
theorem spec_16 (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000) :
    ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧
      (n.val = 1 → r.val = 0) ∧
      (2 ≤ n.val →
        FactorSums n.val r.val ∧ ∀ s : ℤ, FactorSums n.val s → r.val ≤ s) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 1000), ∃ r : Aeneas.Std.I64, Aegis.MinSteps.min_steps n = ok r ∧
      (n.val = 1 → r.val = 0) ∧
      (2 ≤ n.val →
        FactorSums n.val r.val ∧ ∀ s : ℤ, FactorSums n.val s → r.val ≤ s)) := by
  sorry

end AegisSpec.MinSteps
