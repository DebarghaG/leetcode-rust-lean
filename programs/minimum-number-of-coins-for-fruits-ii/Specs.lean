import Aegis.MinimumCoins.Code.Funs

/-!
# Specifications of `Aegis.MinimumCoins.minimum_coins`

LeetCode problem `minimum-number-of-coins-for-fruits-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinimumCoins

  namespace AegisSpec.MinimumCoins

  def IsIndexSet (n : ℕ) (P : Finset ℕ) : Prop := ∀ p ∈ P, p < n

  def Covers (n : ℕ) (P : Finset ℕ) : Prop :=
    ∀ q, q < n → q ∈ P ∨ ∃ p ∈ P, p < q ∧ q ≤ 2 * p + 1

  def coinsSum (prices : Slice Std.I64) (P : Finset ℕ) : ℤ :=
    ∑ p ∈ P, (prices.val[p]!).val

  /-- Whenever the function returns a result r, r is the minimum over all subsets P of {0,...,n-1} satisfying the coverage condition of the sum sum_{p in P} prices[p], where the coverage condition is: for every q with 0 <= q < n, either q is in P, or there exists p in P with p < q <= 2*p + 1.
    Preconditions: Let n = len(prices). The slice satisfies 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= prices[i] <= 100000. -/
  theorem spec_1 (prices : Slice Std.I64) (n : ℕ) (hn : n = prices.val.length)
      (hn1 : 1 ≤ n) (hnb : n ≤ 100000)
      (hp : ∀ i, i < n → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000) :
      ∀ r, minimum_coins prices = ok r →
        (∃ P : Finset ℕ, IsIndexSet n P ∧ Covers n P ∧ r.val = coinsSum prices P) ∧
        (∀ P : Finset ℕ, IsIndexSet n P → Covers n P → r.val ≤ coinsSum prices P) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (prices : Slice Std.I64) (n : ℕ) (hn : n = prices.val.length)
        (hn1 : 1 ≤ n) (hnb : n ≤ 100000)
        (hp : ∀ i, i < n → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000), ∀ r, minimum_coins prices = ok r →
          (∃ P : Finset ℕ, IsIndexSet n P ∧ Covers n P ∧ r.val = coinsSum prices P) ∧
          (∀ P : Finset ℕ, IsIndexSet n P → Covers n P → r.val ≤ coinsSum prices P)) := by
    sorry

  /-- The function returns a result (it does not fail) for every input satisfying the preconditions.
    Preconditions: Let n = len(prices). The slice satisfies 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= prices[i] <= 100000. -/
  theorem spec_2 (prices : Slice Std.I64) (n : ℕ) (hn : n = prices.val.length)
      (hn1 : 1 ≤ n) (hnb : n ≤ 100000)
      (hp : ∀ i, i < n → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000) :
      ∃ r : Std.I64, minimum_coins prices = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (prices : Slice Std.I64) (n : ℕ) (hn : n = prices.val.length)
        (hn1 : 1 ≤ n) (hnb : n ≤ 100000)
        (hp : ∀ i, i < n → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000), ∃ r : Std.I64, minimum_coins prices = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= prices[0].
    Preconditions: Let n = len(prices). The slice satisfies 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= prices[i] <= 100000. -/
  theorem spec_3 (prices : Slice Std.I64) (n : ℕ) (hn : n = prices.val.length)
      (hn1 : 1 ≤ n) (hnb : n ≤ 100000)
      (hp : ∀ i, i < n → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000) :
      ∀ r, minimum_coins prices = ok r → (prices.val[0]!).val ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (prices : Slice Std.I64) (n : ℕ) (hn : n = prices.val.length)
        (hn1 : 1 ≤ n) (hnb : n ≤ 100000)
        (hp : ∀ i, i < n → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000), ∀ r, minimum_coins prices = ok r → (prices.val[0]!).val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= sum_{i=0}^{n-2} prices[i].
    Preconditions: Let n = len(prices). The slice satisfies 2 <= n <= 100000, and for every i with 0 <= i < n, 1 <= prices[i] <= 100000. -/
  theorem spec_4 (prices : Slice Std.I64) (n : ℕ) (hn : n = prices.val.length)
      (hn1 : 2 ≤ n) (hnb : n ≤ 100000)
      (hp : ∀ i, i < n → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000) :
      ∀ r, minimum_coins prices = ok r →
        r.val ≤ ∑ i ∈ Finset.range (n - 1), (prices.val[i]!).val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (prices : Slice Std.I64) (n : ℕ) (hn : n = prices.val.length)
        (hn1 : 2 ≤ n) (hnb : n ≤ 100000)
        (hp : ∀ i, i < n → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000), ∀ r, minimum_coins prices = ok r →
          r.val ≤ ∑ i ∈ Finset.range (n - 1), (prices.val[i]!).val) := by
    sorry

  /-- Whenever the function returns a result r, r >= prices[0] + min(prices[1], prices[2]).
    Preconditions: Let n = len(prices). The slice satisfies 3 <= n <= 100000, and for every i with 0 <= i < n, 1 <= prices[i] <= 100000. -/
  theorem spec_5 (prices : Slice Std.I64) (n : ℕ) (hn : n = prices.val.length)
      (hn1 : 3 ≤ n) (hnb : n ≤ 100000)
      (hp : ∀ i, i < n → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000) :
      ∀ r, minimum_coins prices = ok r →
        (prices.val[0]!).val + min (prices.val[1]!).val (prices.val[2]!).val ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (prices : Slice Std.I64) (n : ℕ) (hn : n = prices.val.length)
        (hn1 : 3 ≤ n) (hnb : n ≤ 100000)
        (hp : ∀ i, i < n → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000), ∀ r, minimum_coins prices = ok r →
          (prices.val[0]!).val + min (prices.val[1]!).val (prices.val[2]!).val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = prices[0].
    Preconditions: Let n = len(prices). The slice satisfies n = 1 and 1 <= prices[0] <= 100000. -/
  theorem spec_6 (prices : Slice Std.I64) (n : ℕ) (hn : n = prices.val.length)
      (hn1 : n = 1)
      (hp0 : 1 ≤ (prices.val[0]!).val ∧ (prices.val[0]!).val ≤ 100000) :
      ∀ r, minimum_coins prices = ok r → r.val = (prices.val[0]!).val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (prices : Slice Std.I64) (n : ℕ) (hn : n = prices.val.length)
        (hn1 : n = 1)
        (hp0 : 1 ≤ (prices.val[0]!).val ∧ (prices.val[0]!).val ≤ 100000), ∀ r, minimum_coins prices = ok r → r.val = (prices.val[0]!).val) := by
    sorry

  /-- Whenever the function returns a result r, r = prices[0] + min(prices[1], prices[2]).
    Preconditions: Let n = len(prices). The slice satisfies n = 3, and for every i with 0 <= i < 3, 1 <= prices[i] <= 100000. -/
  theorem spec_7 (prices : Slice Std.I64) (n : ℕ) (hn : n = prices.val.length)
      (hn3 : n = 3)
      (hp : ∀ i, i < 3 → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000) :
      ∀ r, minimum_coins prices = ok r →
        r.val = (prices.val[0]!).val + min (prices.val[1]!).val (prices.val[2]!).val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (prices : Slice Std.I64) (n : ℕ) (hn : n = prices.val.length)
        (hn3 : n = 3)
        (hp : ∀ i, i < 3 → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000), ∀ r, minimum_coins prices = ok r →
          r.val = (prices.val[0]!).val + min (prices.val[1]!).val (prices.val[2]!).val) := by
    sorry

  /-- Whenever the function returns a result r, r = prices[0] + min(prices[2], prices[1] + min(prices[3], prices[4])).
    Preconditions: Let n = len(prices). The slice satisfies n = 5, and for every i with 0 <= i < 5, 1 <= prices[i] <= 100000. -/
  theorem spec_8 (prices : Slice Std.I64) (n : ℕ) (hn : n = prices.val.length)
      (hn5 : n = 5)
      (hp : ∀ i, i < 5 → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000) :
      ∀ r, minimum_coins prices = ok r →
        r.val = (prices.val[0]!).val +
          min (prices.val[2]!).val
            ((prices.val[1]!).val + min (prices.val[3]!).val (prices.val[4]!).val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (prices : Slice Std.I64) (n : ℕ) (hn : n = prices.val.length)
        (hn5 : n = 5)
        (hp : ∀ i, i < 5 → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000), ∀ r, minimum_coins prices = ok r →
          r.val = (prices.val[0]!).val +
            min (prices.val[2]!).val
              ((prices.val[1]!).val + min (prices.val[3]!).val (prices.val[4]!).val)) := by
    sorry

  /-- Whenever the function returns a result r on prices and a result r2 on prices2, r <= r2.
    Preconditions: Let n = len(prices) = len(prices2). Both slices satisfy 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= prices[i] <= 100000 and 1 <= prices2[i] <= 100000. Assume prices[i] <= prices2[i] for every i with 0 <= i < n. -/
  theorem spec_9 (prices prices2 : Slice Std.I64) (n : ℕ)
      (hn : n = prices.val.length) (hn' : n = prices2.val.length)
      (hn1 : 1 ≤ n) (hnb : n ≤ 100000)
      (hp : ∀ i, i < n → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000)
      (hp2 : ∀ i, i < n → 1 ≤ (prices2.val[i]!).val ∧ (prices2.val[i]!).val ≤ 100000)
      (hle : ∀ i, i < n → (prices.val[i]!).val ≤ (prices2.val[i]!).val) :
      ∀ r r2, minimum_coins prices = ok r → minimum_coins prices2 = ok r2 → r.val ≤ r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (prices prices2 : Slice Std.I64) (n : ℕ)
        (hn : n = prices.val.length) (hn' : n = prices2.val.length)
        (hn1 : 1 ≤ n) (hnb : n ≤ 100000)
        (hp : ∀ i, i < n → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000)
        (hp2 : ∀ i, i < n → 1 ≤ (prices2.val[i]!).val ∧ (prices2.val[i]!).val ≤ 100000)
        (hle : ∀ i, i < n → (prices.val[i]!).val ≤ (prices2.val[i]!).val), ∀ r r2, minimum_coins prices = ok r → minimum_coins prices2 = ok r2 → r.val ≤ r2.val) := by
    sorry

  /-- Whenever the function returns a result r on prices and a result r2 on prices2, r2 >= r.
    Preconditions: Let n = len(prices). The slice prices satisfies 1 <= n <= 99999, and for every i with 0 <= i < n, 1 <= prices[i] <= 100000. Let prices2 be a slice with len(prices2) = n+1 (hence 2 <= len(prices2) <= 100000) such that 1 <= prices2[i] <= 100000 for every 0 <= i <= n and prices2[i] = prices[i] for every 0 <= i < n. -/
  theorem spec_10 (prices prices2 : Slice Std.I64) (n : ℕ)
      (hn : n = prices.val.length) (hn' : prices2.val.length = n + 1)
      (hn1 : 1 ≤ n) (hnb : n ≤ 99999)
      (hp : ∀ i, i < n → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000)
      (hp2 : ∀ i, i ≤ n → 1 ≤ (prices2.val[i]!).val ∧ (prices2.val[i]!).val ≤ 100000)
      (hagree : ∀ i, i < n → (prices2.val[i]!).val = (prices.val[i]!).val) :
      ∀ r r2, minimum_coins prices = ok r → minimum_coins prices2 = ok r2 → r.val ≤ r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (prices prices2 : Slice Std.I64) (n : ℕ)
        (hn : n = prices.val.length) (hn' : prices2.val.length = n + 1)
        (hn1 : 1 ≤ n) (hnb : n ≤ 99999)
        (hp : ∀ i, i < n → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000)
        (hp2 : ∀ i, i ≤ n → 1 ≤ (prices2.val[i]!).val ∧ (prices2.val[i]!).val ≤ 100000)
        (hagree : ∀ i, i < n → (prices2.val[i]!).val = (prices.val[i]!).val), ∀ r r2, minimum_coins prices = ok r → minimum_coins prices2 = ok r2 → r.val ≤ r2.val) := by
    sorry

  /-- Whenever the function returns a result r on prices and a result r2 on prices2, r2 = c * r.
    Preconditions: Let n = len(prices). Both prices and prices2 are slices of length n with 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= prices[i] <= 100000 and 1 <= prices2[i] <= 100000. Let c be a positive integer such that prices2[i] = c * prices[i] for every i with 0 <= i < n. -/
  theorem spec_11 (prices prices2 : Slice Std.I64) (n : ℕ) (c : ℤ)
      (hn : n = prices.val.length) (hn' : n = prices2.val.length)
      (hn1 : 1 ≤ n) (hnb : n ≤ 100000)
      (hp : ∀ i, i < n → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000)
      (hp2 : ∀ i, i < n → 1 ≤ (prices2.val[i]!).val ∧ (prices2.val[i]!).val ≤ 100000)
      (hc : 0 < c)
      (hmul : ∀ i, i < n → (prices2.val[i]!).val = c * (prices.val[i]!).val) :
      ∀ r r2, minimum_coins prices = ok r → minimum_coins prices2 = ok r2 → r2.val = c * r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (prices prices2 : Slice Std.I64) (n : ℕ) (c : ℤ)
        (hn : n = prices.val.length) (hn' : n = prices2.val.length)
        (hn1 : 1 ≤ n) (hnb : n ≤ 100000)
        (hp : ∀ i, i < n → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000)
        (hp2 : ∀ i, i < n → 1 ≤ (prices2.val[i]!).val ∧ (prices2.val[i]!).val ≤ 100000)
        (hc : 0 < c)
        (hmul : ∀ i, i < n → (prices2.val[i]!).val = c * (prices.val[i]!).val), ∀ r r2, minimum_coins prices = ok r → minimum_coins prices2 = ok r2 → r2.val = c * r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists a subset P of {0,...,n-1} satisfying the coverage condition (for every q with 0 <= q < n, either q is in P, or there exists p in P with p < q <= 2*p + 1) such that r = sum_{p in P} prices[p].
    Preconditions: Let n = len(prices). The slice satisfies 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= prices[i] <= 100000. -/
  theorem spec_12 (prices : Slice Std.I64) (n : ℕ) (hn : n = prices.val.length)
      (hn1 : 1 ≤ n) (hnb : n ≤ 100000)
      (hp : ∀ i, i < n → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000) :
      ∀ r, minimum_coins prices = ok r →
        ∃ P : Finset ℕ, IsIndexSet n P ∧ Covers n P ∧ r.val = coinsSum prices P := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (prices : Slice Std.I64) (n : ℕ) (hn : n = prices.val.length)
        (hn1 : 1 ≤ n) (hnb : n ≤ 100000)
        (hp : ∀ i, i < n → 1 ≤ (prices.val[i]!).val ∧ (prices.val[i]!).val ≤ 100000), ∀ r, minimum_coins prices = ok r →
          ∃ P : Finset ℕ, IsIndexSet n P ∧ Covers n P ∧ r.val = coinsSum prices P) := by
    sorry

  end AegisSpec.MinimumCoins
