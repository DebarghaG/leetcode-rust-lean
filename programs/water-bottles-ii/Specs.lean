import Aegis.MaxBottlesDrunk.Code.Funs

/-!
# Specifications of `Aegis.MaxBottlesDrunk.max_bottles_drunk`

LeetCode problem `water-bottles-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxBottlesDrunk

def ExchangesFeasible (numBottles numExchange k : ℤ) : Prop :=
  k = 0 ∨ (1 ≤ k ∧ k * numExchange + (k - 1) * (k - 2) / 2 ≤ numBottles)

def IsMaxNumExchanges (numBottles numExchange k : ℤ) : Prop :=
  0 ≤ k ∧ ExchangesFeasible numBottles numExchange k ∧
    ∀ k' : ℤ, ExchangesFeasible numBottles numExchange k' → k' ≤ k

/-- The function returns a result r, and r = numBottles + K, where K is the greatest nonnegative integer satisfying: either K = 0, or K >= 1 and numBottles >= K*numExchange + (K-1)*(K-2)/2. This K is exactly the maximum number of successful exchanges that can be performed when all initial bottles are drunk first and every exchanged full bottle is drunk before the next exchange; hence r is the maximum total number of water bottles that can be drunk.
  Preconditions: 1 <= numBottles <= 100 and 1 <= numExchange <= 100. -/
theorem spec_1 (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100) :
    ∃ (r : I64) (K : ℤ),
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        IsMaxNumExchanges numBottles.val numExchange.val K ∧
        r.val = numBottles.val + K := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100), ∃ (r : I64) (K : ℤ),
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        IsMaxNumExchanges numBottles.val numExchange.val K ∧
        r.val = numBottles.val + K) := by
  sorry

/-- The function returns a result r; it never fails on these inputs.
  Preconditions: 1 <= numBottles <= 100 and 1 <= numExchange <= 100. -/
theorem spec_2 (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100) :
    ∃ r : I64, Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100), ∃ r : I64, Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r) := by
  sorry

/-- The function returns a result r and r >= numBottles.
  Preconditions: 1 <= numBottles <= 100 and 1 <= numExchange <= 100. -/
theorem spec_3 (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100) :
    ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        numBottles.val ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100), ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        numBottles.val ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= 2*numBottles.
  Preconditions: 1 <= numBottles <= 100 and 1 <= numExchange <= 100. -/
theorem spec_4 (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100) :
    ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        r.val ≤ 2 * numBottles.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100), ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        r.val ≤ 2 * numBottles.val) := by
  sorry

/-- The function returns a result r and, setting k = r - numBottles, after drinking all initial bottles the following k exchanges are feasible in order: for every integer i with 0 <= i < k, before the i-th exchange the number of empty bottles, numBottles + i - (i*numExchange + i*(i-1)/2), is at least the current exchange cost numExchange + i. Thus r is achievable by a legal sequence of operations.
  Preconditions: 1 <= numBottles <= 100 and 1 <= numExchange <= 100. -/
theorem spec_5 (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100) :
    ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        ∀ i : ℤ, 0 ≤ i → i < r.val - numBottles.val →
          numExchange.val + i ≤
            numBottles.val + i - (i * numExchange.val + i * (i - 1) / 2) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100), ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        ∀ i : ℤ, 0 ≤ i → i < r.val - numBottles.val →
          numExchange.val + i ≤
            numBottles.val + i - (i * numExchange.val + i * (i - 1) / 2)) := by
  sorry

/-- The function returns a result r and, setting k = r - numBottles, no feasible legal sequence of exchanges has length k+1; equivalently, numBottles < (k+1)*numExchange + k*(k-1)/2.
  Preconditions: 1 <= numBottles <= 100 and 1 <= numExchange <= 100. -/
theorem spec_6 (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100) :
    ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        numBottles.val <
          (r.val - numBottles.val + 1) * numExchange.val +
            (r.val - numBottles.val) * (r.val - numBottles.val - 1) / 2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100), ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        numBottles.val <
          (r.val - numBottles.val + 1) * numExchange.val +
            (r.val - numBottles.val) * (r.val - numBottles.val - 1) / 2) := by
  sorry

/-- The function returns a result r and r = numBottles.
  Preconditions: 1 <= numBottles <= 100, 1 <= numExchange <= 100, and numExchange > numBottles. -/
theorem spec_7 (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100)
    (h : numBottles.val < numExchange.val) :
    ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        r.val = numBottles.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100)
    (h : numBottles.val < numExchange.val), ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        r.val = numBottles.val) := by
  sorry

/-- The function returns a result r and r = numBottles + 1.
  Preconditions: 1 <= numBottles <= 100, 1 <= numExchange <= 100, and numExchange = numBottles. -/
theorem spec_8 (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100)
    (h : numExchange.val = numBottles.val) :
    ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        r.val = numBottles.val + 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100)
    (h : numExchange.val = numBottles.val), ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        r.val = numBottles.val + 1) := by
  sorry

/-- The function returns a result r, and r = 2 if numExchange = 1, while r = 1 otherwise.
  Preconditions: 1 <= numBottles <= 100, 1 <= numExchange <= 100, and numBottles = 1. -/
theorem spec_9 (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100)
    (h : numBottles.val = 1) :
    ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        r.val = if numExchange.val = 1 then 2 else 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100)
    (h : numBottles.val = 1), ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        r.val = if numExchange.val = 1 then 2 else 1) := by
  sorry

/-- The function returns a result r and r >= numBottles + 1.
  Preconditions: 1 <= numBottles <= 100, 1 <= numExchange <= 100, and numExchange = 1. -/
theorem spec_10 (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100)
    (h : numExchange.val = 1) :
    ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        numBottles.val + 1 ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100)
    (h : numExchange.val = 1), ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        numBottles.val + 1 ≤ r.val) := by
  sorry

/-- The function returns a result r, and for every integer n' with 1 <= n' <= numBottles, if max_bottles_drunk(n', numExchange) returns r', then r' <= r.
  Preconditions: 1 <= numBottles <= 100 and 1 <= numExchange <= 100. -/
theorem spec_11 (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100) :
    ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        ∀ (n' r' : I64), 1 ≤ n'.val → n'.val ≤ numBottles.val →
          Aegis.MaxBottlesDrunk.max_bottles_drunk n' numExchange = ok r' →
            r'.val ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100), ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        ∀ (n' r' : I64), 1 ≤ n'.val → n'.val ≤ numBottles.val →
          Aegis.MaxBottlesDrunk.max_bottles_drunk n' numExchange = ok r' →
            r'.val ≤ r.val) := by
  sorry

/-- The function returns a result r, and for every integer e' with numExchange <= e' <= 100, if max_bottles_drunk(numBottles, e') returns r', then r' <= r.
  Preconditions: 1 <= numBottles <= 100 and 1 <= numExchange <= 100. -/
theorem spec_12 (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100) :
    ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        ∀ (e' r' : I64), numExchange.val ≤ e'.val → e'.val ≤ 100 →
          Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles e' = ok r' →
            r'.val ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (numBottles numExchange : I64)
    (hB1 : 1 ≤ numBottles.val) (hB2 : numBottles.val ≤ 100)
    (hE1 : 1 ≤ numExchange.val) (hE2 : numExchange.val ≤ 100), ∃ r : I64,
      Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles numExchange = ok r ∧
        ∀ (e' r' : I64), numExchange.val ≤ e'.val → e'.val ≤ 100 →
          Aegis.MaxBottlesDrunk.max_bottles_drunk numBottles e' = ok r' →
            r'.val ≤ r.val) := by
  sorry

end AegisSpec.MaxBottlesDrunk
