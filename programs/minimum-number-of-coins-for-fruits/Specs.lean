import Aegis.MinimumCoins.Code.Funs

/-!
# Specifications of `Aegis.MinimumCoins.minimum_coins`

LeetCode problem `minimum-number-of-coins-for-fruits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumCoins

def price (prices : Slice I64) (i : ℕ) : Int :=
  (prices.val[i]?).map (fun x => x.val) |>.getD 0

def Feasible (n : ℕ) (P : Finset ℕ) : Prop :=
  P ⊆ Finset.range n ∧ ∀ j ∈ Finset.range n, j ∈ P ∨ ∃ i ∈ P, i < j ∧ j ≤ 2 * i + 1

def sumOn (prices : Slice I64) (P : Finset ℕ) : Int :=
  ∑ i ∈ P, price prices i

def feasibleCosts (prices : Slice I64) : Set Int :=
  {s : Int | ∃ P : Finset ℕ, Feasible prices.length P ∧ s = sumOn prices P}

def ValidInput (prices : Slice I64) : Prop :=
  1 ≤ prices.length ∧ prices.length ≤ 1000 ∧
    (∀ i, i < prices.length → 1 ≤ price prices i ∧ price prices i ≤ 100000)

/-- Let n = len(prices). Call a subset P of {0,...,n-1} feasible if for every j with 0 <= j < n, either j is in P, or there exists i in P with i < j and j <= 2*i + 1 (equivalently, j is among the next i+1 fruits after i). The function returns a result r and r = min { sum_{i in P} prices[i] | P is a feasible subset of {0,...,n-1} }.
  Preconditions: Let n = len(prices). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= prices[i] <= 100000. -/
theorem spec_1 (prices : Slice I64) (hvalid : ValidInput prices) :
    ∃ r : I64, Aegis.MinimumCoins.minimum_coins prices = ok r ∧
      IsLeast (feasibleCosts prices) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (prices : Slice I64) (hvalid : ValidInput prices), ∃ r : I64, Aegis.MinimumCoins.minimum_coins prices = ok r ∧
      IsLeast (feasibleCosts prices) r.val) := by
  sorry

/-- For every prices array satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: Let n = len(prices). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= prices[i] <= 100000. -/
theorem spec_2 (prices : Slice I64) (hvalid : ValidInput prices) :
    ∃ r : I64, Aegis.MinimumCoins.minimum_coins prices = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (prices : Slice I64) (hvalid : ValidInput prices), ∃ r : I64, Aegis.MinimumCoins.minimum_coins prices = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= prices[0].
  Preconditions: Let n = len(prices). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= prices[i] <= 100000. -/
theorem spec_3 (prices : Slice I64) (hvalid : ValidInput prices) :
    ∀ r : I64, Aegis.MinimumCoins.minimum_coins prices = ok r → price prices 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (prices : Slice I64) (hvalid : ValidInput prices), ∀ r : I64, Aegis.MinimumCoins.minimum_coins prices = ok r → price prices 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= prices[0] + sum_{i=2}^{n-1} prices[i], where the sum is 0 if n <= 2.
  Preconditions: Let n = len(prices). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= prices[i] <= 100000. -/
theorem spec_4 (prices : Slice I64) (hvalid : ValidInput prices) :
    ∀ r : I64, Aegis.MinimumCoins.minimum_coins prices = ok r →
      r.val ≤ price prices 0 + ∑ i ∈ Finset.Icc 2 (prices.length - 1), price prices i := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (prices : Slice I64) (hvalid : ValidInput prices), ∀ r : I64, Aegis.MinimumCoins.minimum_coins prices = ok r →
      r.val ≤ price prices 0 + ∑ i ∈ Finset.Icc 2 (prices.length - 1), price prices i) := by
  sorry

/-- Whenever the function returns a result r, there exists a feasible subset P of {0,...,n-1} such that r = sum_{i in P} prices[i], where feasible means that for every j with 0 <= j < n, either j is in P or there exists i in P with i < j and j <= 2*i + 1.
  Preconditions: Let n = len(prices). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= prices[i] <= 100000. -/
theorem spec_5 (prices : Slice I64) (hvalid : ValidInput prices) :
    ∀ r : I64, Aegis.MinimumCoins.minimum_coins prices = ok r →
      ∃ P : Finset ℕ, Feasible prices.length P ∧ r.val = sumOn prices P := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (prices : Slice I64) (hvalid : ValidInput prices), ∀ r : I64, Aegis.MinimumCoins.minimum_coins prices = ok r →
      ∃ P : Finset ℕ, Feasible prices.length P ∧ r.val = sumOn prices P) := by
  sorry

/-- Whenever the function returns a result r, for every feasible subset P of {0,...,n-1} (where feasible means that for every j with 0 <= j < n, either j is in P or there exists i in P with i < j and j <= 2*i + 1), we have r <= sum_{i in P} prices[i].
  Preconditions: Let n = len(prices). Assume 1 <= n <= 1000 and for every i with 0 <= i < n, 1 <= prices[i] <= 100000. -/
theorem spec_6 (prices : Slice I64) (hvalid : ValidInput prices) :
    ∀ r : I64, Aegis.MinimumCoins.minimum_coins prices = ok r →
      ∀ P : Finset ℕ, Feasible prices.length P → r.val ≤ sumOn prices P := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (prices : Slice I64) (hvalid : ValidInput prices), ∀ r : I64, Aegis.MinimumCoins.minimum_coins prices = ok r →
      ∀ P : Finset ℕ, Feasible prices.length P → r.val ≤ sumOn prices P) := by
  sorry

/-- Whenever the function returns a result r, r >= prices[0] + min(prices[1], prices[2]).
  Preconditions: Assume n = len(prices), 3 <= n <= 1000, and 1 <= prices[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_7 (prices : Slice I64) (hn3 : 3 ≤ prices.length) (hvalid : ValidInput prices) :
    ∀ r : I64, Aegis.MinimumCoins.minimum_coins prices = ok r →
      price prices 0 + min (price prices 1) (price prices 2) ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (prices : Slice I64) (hn3 : 3 ≤ prices.length) (hvalid : ValidInput prices), ∀ r : I64, Aegis.MinimumCoins.minimum_coins prices = ok r →
      price prices 0 + min (price prices 1) (price prices 2) ≤ r.val) := by
  sorry

/-- r_a <= r_b.
  Preconditions: Let a and b be two arrays both satisfying the valid-input preconditions with the same length n (1 <= n <= 1000 and entries in [1,100000]). Suppose a[i] <= b[i] for every i with 0 <= i < n. Let r_a be the result returned for a and r_b the result returned for b. -/
theorem spec_8 (a b : Slice I64) (hva : ValidInput a) (hvb : ValidInput b)
    (hlen : b.length = a.length)
    (hle : ∀ i, i < a.length → price a i ≤ price b i) :
    ∀ ra rb : I64, Aegis.MinimumCoins.minimum_coins a = ok ra →
      Aegis.MinimumCoins.minimum_coins b = ok rb → ra.val ≤ rb.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (a b : Slice I64) (hva : ValidInput a) (hvb : ValidInput b)
    (hlen : b.length = a.length)
    (hle : ∀ i, i < a.length → price a i ≤ price b i), ∀ ra rb : I64, Aegis.MinimumCoins.minimum_coins a = ok ra →
      Aegis.MinimumCoins.minimum_coins b = ok rb → ra.val ≤ rb.val) := by
  sorry

/-- r_b = r_a + d.
  Preconditions: Let a be a valid array with n = len(a), 1 <= n <= 1000, entries in [1,100000]. Let d be an integer with d >= 0 such that b defined by b[0] = a[0] + d and b[i] = a[i] for 1 <= i < n also satisfies 1 <= b[0] <= 100000 (so b is valid). Let r_a and r_b be the results returned for a and b. -/
theorem spec_9 (a b : Slice I64) (d : Int)
    (hva : ValidInput a) (hvb : ValidInput b) (hlen : b.length = a.length) (hd : 0 ≤ d)
    (h0 : price b 0 = price a 0 + d)
    (hrest : ∀ i, 1 ≤ i → i < a.length → price b i = price a i) :
    ∀ ra rb : I64, Aegis.MinimumCoins.minimum_coins a = ok ra →
      Aegis.MinimumCoins.minimum_coins b = ok rb → rb.val = ra.val + d := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (a b : Slice I64) (d : Int)
    (hva : ValidInput a) (hvb : ValidInput b) (hlen : b.length = a.length) (hd : 0 ≤ d)
    (h0 : price b 0 = price a 0 + d)
    (hrest : ∀ i, 1 ≤ i → i < a.length → price b i = price a i), ∀ ra rb : I64, Aegis.MinimumCoins.minimum_coins a = ok ra →
      Aegis.MinimumCoins.minimum_coins b = ok rb → rb.val = ra.val + d) := by
  sorry

/-- r_b = c * r_a.
  Preconditions: Let a be a valid array with n = len(a), 1 <= n <= 1000, entries in [1,100000]. Let c be an integer with c >= 1 such that b[i] = c * a[i] satisfies 1 <= b[i] <= 100000 for every i with 0 <= i < n (so b is valid). Let r_a and r_b be the results returned for a and b. -/
theorem spec_10 (a b : Slice I64) (c : Int)
    (hva : ValidInput a) (hvb : ValidInput b) (hlen : b.length = a.length) (hc : 1 ≤ c)
    (hscale : ∀ i, i < a.length → price b i = c * price a i) :
    ∀ ra rb : I64, Aegis.MinimumCoins.minimum_coins a = ok ra →
      Aegis.MinimumCoins.minimum_coins b = ok rb → rb.val = c * ra.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (a b : Slice I64) (c : Int)
    (hva : ValidInput a) (hvb : ValidInput b) (hlen : b.length = a.length) (hc : 1 ≤ c)
    (hscale : ∀ i, i < a.length → price b i = c * price a i), ∀ ra rb : I64, Aegis.MinimumCoins.minimum_coins a = ok ra →
      Aegis.MinimumCoins.minimum_coins b = ok rb → rb.val = c * ra.val) := by
  sorry

end AegisSpec.MinimumCoins
