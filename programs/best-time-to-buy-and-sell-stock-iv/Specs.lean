import Aegis.MaxProfit.Code.Funs

/-!
# Specifications of `Aegis.MaxProfit.max_profit`

LeetCode problem `best-time-to-buy-and-sell-stock-iv`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxProfit

  def pricesOf (prices : Slice Std.I64) : List Int := prices.val.map (fun p => p.val)

  def nthD (l : List Int) (i : Nat) : Int := l.getD i 0

  def PricesInRange (l : List Int) (lo hi : Int) : Prop :=
    ∀ i, i < l.length → lo ≤ nthD l i ∧ nthD l i ≤ hi

  def IsListMax (l : List Int) (M : Int) : Prop :=
    (∀ x ∈ l, x ≤ M) ∧ ∃ x ∈ l, x = M

  def IsListMin (l : List Int) (m : Int) : Prop :=
    (∀ x ∈ l, m ≤ x) ∧ ∃ x ∈ l, x = m

  def sumInt : List Int → Int
    | [] => 0
    | x :: xs => x + sumInt xs

  def incrementsSum : List Int → Int
    | [] => 0
    | [_] => 0
    | x :: y :: rest => max 0 (y - x) + incrementsSum (y :: rest)

  def Nonincreasing (l : List Int) : Prop :=
    ∀ i, i + 1 < l.length → nthD l (i + 1) ≤ nthD l i

  def NoUpwardPair (l : List Int) : Prop :=
    ∀ i j, i < j → j < l.length → ¬ nthD l i < nthD l j

  def ValidSchemeFrom (lo n : Nat) : List (Nat × Nat) → Prop
    | [] => True
    | (b, s) :: rest => lo ≤ b ∧ b < s ∧ s < n ∧ ValidSchemeFrom (s + 1) n rest

  def IsValidScheme (n : Nat) (k : Int) (sch : List (Nat × Nat)) : Prop :=
    (sch.length : Int) ≤ k ∧ ValidSchemeFrom 0 n sch

  def schemeProfit (l : List Int) (sch : List (Nat × Nat)) : Int :=
    sumInt (sch.map (fun t => nthD l t.2 - nthD l t.1))

  def IsMaxSchemeProfit (l : List Int) (k : Int) (r : Int) : Prop :=
    (∀ sch, IsValidScheme l.length k sch → schemeProfit l sch ≤ r) ∧
      ∃ sch, IsValidScheme l.length k sch ∧ schemeProfit l sch = r

  def IsMaxSingleTrade (l : List Int) (r : Int) : Prop :=
    (∀ i j, i < j → j < l.length → nthD l j - nthD l i ≤ r) ∧
      (r = 0 ∨ ∃ i j, i < j ∧ j < l.length ∧ r = nthD l j - nthD l i)

  /-- The function returns a result r. Call a transaction any pair of indices (b, s) with 0 <= b < s < len(prices). Call a valid scheme any sequence of transactions (b_1, s_1), ..., (b_m, s_m) with 0 <= m <= k and s_j < b_{j+1} for every 1 <= j < m. Its profit is the sum over j = 1..m of (prices[s_j] - prices[b_j]); the empty scheme (m = 0) has profit 0. Then r equals the maximum profit over all valid schemes with at most k transactions.
    Preconditions: 1 <= k <= 100, 1 <= len(prices) <= 1000, and 0 <= prices[i] <= 1000 for every i with 0 <= i < len(prices). -/
  theorem spec_1 (k : Std.I64) (prices : Slice Std.I64)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
      (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
      (hprices : PricesInRange (pricesOf prices) 0 1000) :
      ∃ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r ∧
        IsMaxSchemeProfit (pricesOf prices) k.val r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (k : Std.I64) (prices : Slice Std.I64)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
        (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
        (hprices : PricesInRange (pricesOf prices) 0 1000), ∃ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r ∧
          IsMaxSchemeProfit (pricesOf prices) k.val r.val) := by
    sorry

  /-- The function returns a result r and does not fail (no overflow, no out-of-bounds access, no panic) for every input satisfying the preconditions.
    Preconditions: 1 <= k <= 100, 1 <= len(prices) <= 1000, and 0 <= prices[i] <= 1000 for every i with 0 <= i < len(prices). -/
  theorem spec_2 (k : Std.I64) (prices : Slice Std.I64)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
      (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
      (hprices : PricesInRange (pricesOf prices) 0 1000) :
      ∃ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (k : Std.I64) (prices : Slice Std.I64)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
        (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
        (hprices : PricesInRange (pricesOf prices) 0 1000), ∃ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= k * (M - m), where M = max { prices[i] : 0 <= i < len(prices) } and m = min { prices[i] : 0 <= i < len(prices) }.
    Preconditions: 1 <= k <= 100, 1 <= len(prices) <= 1000, and 0 <= prices[i] <= 1000 for every i with 0 <= i < len(prices). -/
  theorem spec_3 (k : Std.I64) (prices : Slice Std.I64)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
      (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
      (hprices : PricesInRange (pricesOf prices) 0 1000) :
      ∀ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r →
        ∀ M m : Int, IsListMax (pricesOf prices) M → IsListMin (pricesOf prices) m →
          0 ≤ r.val ∧ r.val ≤ k.val * (M - m) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (k : Std.I64) (prices : Slice Std.I64)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
        (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
        (hprices : PricesInRange (pricesOf prices) 0 1000), ∀ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r →
          ∀ M m : Int, IsListMax (pricesOf prices) M → IsListMin (pricesOf prices) m →
            0 ≤ r.val ∧ r.val ≤ k.val * (M - m)) := by
    sorry

  /-- Whenever the function returns a result r, r is at most the sum of max(0, prices[i+1] - prices[i]) over all i with 0 <= i < len(prices)-1.
    Preconditions: 1 <= k <= 100, 1 <= len(prices) <= 1000, and 0 <= prices[i] <= 1000 for every i with 0 <= i < len(prices). -/
  theorem spec_4 (k : Std.I64) (prices : Slice Std.I64)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
      (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
      (hprices : PricesInRange (pricesOf prices) 0 1000) :
      ∀ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r →
        r.val ≤ incrementsSum (pricesOf prices) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (k : Std.I64) (prices : Slice Std.I64)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
        (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
        (hprices : PricesInRange (pricesOf prices) 0 1000), ∀ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r →
          r.val ≤ incrementsSum (pricesOf prices)) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of indices i, j with 0 <= i < j < len(prices), r >= prices[j] - prices[i].
    Preconditions: 1 <= k <= 100, 1 <= len(prices) <= 1000, and 0 <= prices[i] <= 1000 for every i with 0 <= i < len(prices). -/
  theorem spec_5 (k : Std.I64) (prices : Slice Std.I64)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
      (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
      (hprices : PricesInRange (pricesOf prices) 0 1000) :
      ∀ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r →
        ∀ i j : Nat, i < j → j < (pricesOf prices).length →
          nthD (pricesOf prices) j - nthD (pricesOf prices) i ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (k : Std.I64) (prices : Slice Std.I64)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
        (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
        (hprices : PricesInRange (pricesOf prices) 0 1000), ∀ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r →
          ∀ i j : Nat, i < j → j < (pricesOf prices).length →
            nthD (pricesOf prices) j - nthD (pricesOf prices) i ≤ r.val) := by
    sorry

  /-- If max_profit(k1, prices) returns r1 and max_profit(k2, prices) returns r2, then r1 <= r2.
    Preconditions: 1 <= k1 <= k2 <= 100, 1 <= len(prices) <= 1000, and 0 <= prices[i] <= 1000 for every i with 0 <= i < len(prices). -/
  theorem spec_6 (k1 k2 : Std.I64) (prices : Slice Std.I64)
      (hk1_lo : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_hi : k2.val ≤ 100)
      (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
      (hprices : PricesInRange (pricesOf prices) 0 1000) :
      ∀ r1 r2 : Std.I64, Aegis.MaxProfit.max_profit k1 prices = ok r1 →
        Aegis.MaxProfit.max_profit k2 prices = ok r2 → r1.val ≤ r2.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (k1 k2 : Std.I64) (prices : Slice Std.I64)
        (hk1_lo : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_hi : k2.val ≤ 100)
        (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
        (hprices : PricesInRange (pricesOf prices) 0 1000), ∀ r1 r2 : Std.I64, Aegis.MaxProfit.max_profit k1 prices = ok r1 →
          Aegis.MaxProfit.max_profit k2 prices = ok r2 → r1.val ≤ r2.val) := by
    sorry

  /-- The function returns a result r and r equals the sum of max(0, prices[i+1] - prices[i]) over all i with 0 <= i < len(prices)-1.
    Preconditions: 1 <= k <= 100, 1 <= len(prices) <= 1000, 0 <= prices[i] <= 1000 for every i with 0 <= i < len(prices), and 2*k >= len(prices) - 1. -/
  theorem spec_7 (k : Std.I64) (prices : Slice Std.I64)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
      (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
      (hprices : PricesInRange (pricesOf prices) 0 1000)
      (hk_big : ((pricesOf prices).length : Int) - 1 ≤ 2 * k.val) :
      ∃ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r ∧
        r.val = incrementsSum (pricesOf prices) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (k : Std.I64) (prices : Slice Std.I64)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
        (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
        (hprices : PricesInRange (pricesOf prices) 0 1000)
        (hk_big : ((pricesOf prices).length : Int) - 1 ≤ 2 * k.val), ∃ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r ∧
          r.val = incrementsSum (pricesOf prices)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: 1 <= k <= 100, 1 <= len(prices) <= 1000, 0 <= prices[i] <= 1000 for every i with 0 <= i < len(prices), and prices[i] = prices[0] for every i. -/
  theorem spec_8 (k : Std.I64) (prices : Slice Std.I64)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
      (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
      (hprices : PricesInRange (pricesOf prices) 0 1000)
      (hconst : ∀ i, i < (pricesOf prices).length →
        nthD (pricesOf prices) i = nthD (pricesOf prices) 0) :
      ∀ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r → r.val = 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (k : Std.I64) (prices : Slice Std.I64)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
        (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
        (hprices : PricesInRange (pricesOf prices) 0 1000)
        (hconst : ∀ i, i < (pricesOf prices).length →
          nthD (pricesOf prices) i = nthD (pricesOf prices) 0), ∀ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r = prices[len(prices)-1] - prices[0].
    Preconditions: 1 <= k <= 100, 1 <= len(prices) <= 1000, 0 <= prices[i] <= 1000 for every i with 0 <= i < len(prices), and prices[i] <= prices[i+1] for every 0 <= i < len(prices)-1. -/
  theorem spec_9 (k : Std.I64) (prices : Slice Std.I64)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
      (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
      (hprices : PricesInRange (pricesOf prices) 0 1000)
      (hmono : ∀ i, i + 1 < (pricesOf prices).length →
        nthD (pricesOf prices) i ≤ nthD (pricesOf prices) (i + 1)) :
      ∀ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r →
        r.val = nthD (pricesOf prices) ((pricesOf prices).length - 1) -
          nthD (pricesOf prices) 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (k : Std.I64) (prices : Slice Std.I64)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
        (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
        (hprices : PricesInRange (pricesOf prices) 0 1000)
        (hmono : ∀ i, i + 1 < (pricesOf prices).length →
          nthD (pricesOf prices) i ≤ nthD (pricesOf prices) (i + 1)), ∀ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r →
          r.val = nthD (pricesOf prices) ((pricesOf prices).length - 1) -
            nthD (pricesOf prices) 0) := by
    sorry

  /-- Whenever the function returns a result r, there exists a valid scheme with at most k transactions (a sequence of index pairs (b_1, s_1), ..., (b_m, s_m) with 0 <= m <= k and 0 <= b_1 < s_1 < b_2 < s_2 < ... < b_m < s_m < len(prices)) whose profit, sum over j = 1..m of (prices[s_j] - prices[b_j]), equals r.
    Preconditions: 1 <= k <= 100, 1 <= len(prices) <= 1000, and 0 <= prices[i] <= 1000 for every i with 0 <= i < len(prices). -/
  theorem spec_10 (k : Std.I64) (prices : Slice Std.I64)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
      (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
      (hprices : PricesInRange (pricesOf prices) 0 1000) :
      ∃ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r ∧
        ∃ sch : List (Nat × Nat),
          IsValidScheme (pricesOf prices).length k.val sch ∧
            schemeProfit (pricesOf prices) sch = r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (k : Std.I64) (prices : Slice Std.I64)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
        (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
        (hprices : PricesInRange (pricesOf prices) 0 1000), ∃ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r ∧
          ∃ sch : List (Nat × Nat),
            IsValidScheme (pricesOf prices).length k.val sch ∧
              schemeProfit (pricesOf prices) sch = r.val) := by
    sorry

  /-- If max_profit(k, p) returns r and max_profit(k, q) returns r', then r = r'.
    Preconditions: 1 <= k <= 100, 1 <= len(p) = len(q) <= 1000, 0 <= p[i] <= 1000 and 0 <= q[i] <= 1000 for every i with 0 <= i < len(p), and there is an integer c such that q[i] = p[i] + c for every i. -/
  theorem spec_11 (k : Std.I64) (p q : Slice Std.I64)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
      (hlen_eq : p.val.length = q.val.length)
      (hlen_lo : 1 ≤ p.val.length) (hlen_hi : p.val.length ≤ 1000)
      (hp : PricesInRange (pricesOf p) 0 1000)
      (hq : PricesInRange (pricesOf q) 0 1000)
      (hshift : ∃ c : Int, ∀ i, i < (pricesOf p).length →
        nthD (pricesOf q) i = nthD (pricesOf p) i + c) :
      ∀ r r' : Std.I64, Aegis.MaxProfit.max_profit k p = ok r →
        Aegis.MaxProfit.max_profit k q = ok r' → r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (k : Std.I64) (p q : Slice Std.I64)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
        (hlen_eq : p.val.length = q.val.length)
        (hlen_lo : 1 ≤ p.val.length) (hlen_hi : p.val.length ≤ 1000)
        (hp : PricesInRange (pricesOf p) 0 1000)
        (hq : PricesInRange (pricesOf q) 0 1000)
        (hshift : ∃ c : Int, ∀ i, i < (pricesOf p).length →
          nthD (pricesOf q) i = nthD (pricesOf p) i + c), ∀ r r' : Std.I64, Aegis.MaxProfit.max_profit k p = ok r →
          Aegis.MaxProfit.max_profit k q = ok r' → r.val = r'.val) := by
    sorry

  /-- The function returns a result r and r = 0 if and only if prices[i] >= prices[i+1] for every i with 0 <= i < len(prices)-1; equivalently, no pair i < j has prices[i] < prices[j].
    Preconditions: 1 <= k <= 100, 1 <= len(prices) <= 1000, and 0 <= prices[i] <= 1000 for every i with 0 <= i < len(prices). -/
  theorem spec_12 (k : Std.I64) (prices : Slice Std.I64)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
      (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
      (hprices : PricesInRange (pricesOf prices) 0 1000) :
      ∃ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r ∧
        (r.val = 0 ↔ Nonincreasing (pricesOf prices)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (k : Std.I64) (prices : Slice Std.I64)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
        (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
        (hprices : PricesInRange (pricesOf prices) 0 1000), ∃ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r ∧
          (r.val = 0 ↔ Nonincreasing (pricesOf prices))) := by
    sorry

  /-- The function returns a result r and r = max({0} union { prices[j] - prices[i] : 0 <= i < j < len(prices) }).
    Preconditions: k = 1, 1 <= len(prices) <= 1000, and 0 <= prices[i] <= 1000 for every i with 0 <= i < len(prices). -/
  theorem spec_13 (k : Std.I64) (prices : Slice Std.I64)
      (hk : k.val = 1)
      (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
      (hprices : PricesInRange (pricesOf prices) 0 1000) :
      ∃ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r ∧
        IsMaxSingleTrade (pricesOf prices) r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (k : Std.I64) (prices : Slice Std.I64)
        (hk : k.val = 1)
        (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 1000)
        (hprices : PricesInRange (pricesOf prices) 0 1000), ∃ r : Std.I64, Aegis.MaxProfit.max_profit k prices = ok r ∧
          IsMaxSingleTrade (pricesOf prices) r.val) := by
    sorry

  end AegisSpec.MaxProfit
