import Aegis.MaxProfit.Code.Funs

/-!
# Specifications of `Aegis.MaxProfit.max_profit`

LeetCode problem `best-time-to-buy-and-sell-stock`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxProfit

  def vals (prices : Slice Std.I64) : List Int := prices.val.map (fun x => x.val)

  def pairProfits : List Int → List Int
    | [] => []
    | a :: rest => rest.map (fun b => b - a) ++ pairProfits rest

  def bestProfit (l : List Int) : Int := (pairProfits l).foldr max 0

  def listMax : List Int → Int
    | [] => 0
    | a :: rest => rest.foldr max a

  def listMin : List Int → Int
    | [] => 0
    | a :: rest => rest.foldr min a

  def hasIncrease (l : List Int) : Prop := ∃ d ∈ pairProfits l, 0 < d

  def NonIncreasing (l : List Int) : Prop := ∀ d ∈ pairProfits l, d ≤ 0

  /-- Whenever max_profit(prices) returns a result r, r = max({0} ∪ { prices[j] - prices[i] | 0 <= i < j < len(prices) }), where max is the largest element of the finite set; in particular, if len(prices) = 1 or no pair has prices[j] > prices[i], then r = 0.
    Preconditions: prices is a nonempty slice of 64-bit signed integers with 1 <= len(prices) <= 100000 and, for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000. -/
  theorem spec_1 (prices : Slice Std.I64)
      (hlen : 1 ≤ prices.val.length)
      (hlen_ub : prices.val.length ≤ 100000)
      (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
        0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000) :
      ∀ r, Aegis.MaxProfit.max_profit prices = ok r → r.val = bestProfit (vals prices) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (hlen : 1 ≤ prices.val.length)
        (hlen_ub : prices.val.length ≤ 100000)
        (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
          0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000), ∀ r, Aegis.MaxProfit.max_profit prices = ok r → r.val = bestProfit (vals prices)) := by
    sorry

  /-- The function max_profit(prices) returns a result (an Ok value) for every input satisfying the preconditions; it does not fail, panic, go out of bounds, or overflow.
    Preconditions: prices is a nonempty slice of 64-bit signed integers with 1 <= len(prices) <= 100000 and, for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000. -/
  theorem spec_2 (prices : Slice Std.I64)
      (hlen : 1 ≤ prices.val.length)
      (hlen_ub : prices.val.length ≤ 100000)
      (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
        0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000) :
      ∃ r, Aegis.MaxProfit.max_profit prices = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (hlen : 1 ≤ prices.val.length)
        (hlen_ub : prices.val.length ≤ 100000)
        (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
          0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000), ∃ r, Aegis.MaxProfit.max_profit prices = ok r) := by
    sorry

  /-- Whenever max_profit(prices) returns a result r, 0 <= r.
    Preconditions: prices is a nonempty slice of 64-bit signed integers with 1 <= len(prices) <= 100000 and, for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000. -/
  theorem spec_3 (prices : Slice Std.I64)
      (hlen : 1 ≤ prices.val.length)
      (hlen_ub : prices.val.length ≤ 100000)
      (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
        0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000) :
      ∀ r, Aegis.MaxProfit.max_profit prices = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (hlen : 1 ≤ prices.val.length)
        (hlen_ub : prices.val.length ≤ 100000)
        (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
          0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000), ∀ r, Aegis.MaxProfit.max_profit prices = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever max_profit(prices) returns a result r, r <= max_price - min_price, where max_price = max{ prices[i] | 0 <= i < len(prices) } and min_price = min{ prices[i] | 0 <= i < len(prices) }.
    Preconditions: prices is a nonempty slice of 64-bit signed integers with 1 <= len(prices) <= 100000 and, for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000. -/
  theorem spec_4 (prices : Slice Std.I64)
      (hlen : 1 ≤ prices.val.length)
      (hlen_ub : prices.val.length ≤ 100000)
      (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
        0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000) :
      ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
        r.val ≤ listMax (vals prices) - listMin (vals prices) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (hlen : 1 ≤ prices.val.length)
        (hlen_ub : prices.val.length ≤ 100000)
        (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
          0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000), ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
          r.val ≤ listMax (vals prices) - listMin (vals prices)) := by
    sorry

  /-- Whenever max_profit(prices) returns a result r, for every i and j with 0 <= i < j < len(prices), prices[j] - prices[i] <= r.
    Preconditions: prices is a nonempty slice of 64-bit signed integers with 1 <= len(prices) <= 100000 and, for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000. -/
  theorem spec_5 (prices : Slice Std.I64)
      (hlen : 1 ≤ prices.val.length)
      (hlen_ub : prices.val.length ≤ 100000)
      (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
        0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000) :
      ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
        ∀ (i j : Nat) (hij : i < j) (hj : j < prices.val.length),
          prices.val[j].val - prices.val[i].val ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (hlen : 1 ≤ prices.val.length)
        (hlen_ub : prices.val.length ≤ 100000)
        (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
          0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000), ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
          ∀ (i j : Nat) (hij : i < j) (hj : j < prices.val.length),
            prices.val[j].val - prices.val[i].val ≤ r.val) := by
    sorry

  /-- Whenever max_profit(prices) returns a result r and r > 0, there exist indices i and j with 0 <= i < j < len(prices) such that prices[j] - prices[i] = r.
    Preconditions: prices is a nonempty slice of 64-bit signed integers with 1 <= len(prices) <= 100000 and, for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000. -/
  theorem spec_6 (prices : Slice Std.I64)
      (hlen : 1 ≤ prices.val.length)
      (hlen_ub : prices.val.length ≤ 100000)
      (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
        0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000) :
      ∀ r, Aegis.MaxProfit.max_profit prices = ok r → 0 < r.val →
        ∃ (i j : Nat) (hij : i < j) (hj : j < prices.val.length),
          prices.val[j].val - prices.val[i].val = r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (hlen : 1 ≤ prices.val.length)
        (hlen_ub : prices.val.length ≤ 100000)
        (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
          0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000), ∀ r, Aegis.MaxProfit.max_profit prices = ok r → 0 < r.val →
          ∃ (i j : Nat) (hij : i < j) (hj : j < prices.val.length),
            prices.val[j].val - prices.val[i].val = r.val) := by
    sorry

  /-- Whenever max_profit(prices) returns a result r, r > 0 if and only if there exist indices i and j with 0 <= i < j < len(prices) such that prices[j] > prices[i].
    Preconditions: prices is a nonempty slice of 64-bit signed integers with 1 <= len(prices) <= 100000 and, for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000. -/
  theorem spec_7 (prices : Slice Std.I64)
      (hlen : 1 ≤ prices.val.length)
      (hlen_ub : prices.val.length ≤ 100000)
      (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
        0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000) :
      ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
        (0 < r.val ↔ hasIncrease (vals prices)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (hlen : 1 ≤ prices.val.length)
        (hlen_ub : prices.val.length ≤ 100000)
        (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
          0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000), ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
          (0 < r.val ↔ hasIncrease (vals prices))) := by
    sorry

  /-- Whenever max_profit(prices) returns a result r, r = 0 if and only if for all i and j with 0 <= i < j < len(prices), prices[j] <= prices[i].
    Preconditions: prices is a nonempty slice of 64-bit signed integers with 1 <= len(prices) <= 100000 and, for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000. -/
  theorem spec_8 (prices : Slice Std.I64)
      (hlen : 1 ≤ prices.val.length)
      (hlen_ub : prices.val.length ≤ 100000)
      (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
        0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000) :
      ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
        (r.val = 0 ↔ NonIncreasing (vals prices)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (hlen : 1 ≤ prices.val.length)
        (hlen_ub : prices.val.length ≤ 100000)
        (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
          0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000), ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
          (r.val = 0 ↔ NonIncreasing (vals prices))) := by
    sorry

  /-- For every such c and q, whenever max_profit(prices) returns r and max_profit(q) returns r', we have r' = r.
    Preconditions: prices is a nonempty slice with 1 <= len(prices) <= 100000 and 0 <= prices[i] <= 10000 for all i. Let c be any integer such that 0 <= prices[i] + c <= 10000 for every i, and let q be the slice of the same length with q[i] = prices[i] + c. -/
  theorem spec_9 (prices q : Slice Std.I64) (c : Int)
      (hlen : 1 ≤ prices.val.length)
      (hlen_ub : prices.val.length ≤ 100000)
      (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
        0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000)
      (hshift_lo : ∀ (i : Nat) (hi : i < prices.val.length), 0 ≤ prices.val[i].val + c)
      (hshift_hi : ∀ (i : Nat) (hi : i < prices.val.length), prices.val[i].val + c ≤ 10000)
      (hq : vals q = (vals prices).map (fun x => x + c)) :
      ∀ r r', Aegis.MaxProfit.max_profit prices = ok r →
        Aegis.MaxProfit.max_profit q = ok r' → r'.val = r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (prices q : Slice Std.I64) (c : Int)
        (hlen : 1 ≤ prices.val.length)
        (hlen_ub : prices.val.length ≤ 100000)
        (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
          0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000)
        (hshift_lo : ∀ (i : Nat) (hi : i < prices.val.length), 0 ≤ prices.val[i].val + c)
        (hshift_hi : ∀ (i : Nat) (hi : i < prices.val.length), prices.val[i].val + c ≤ 10000)
        (hq : vals q = (vals prices).map (fun x => x + c)), ∀ r r', Aegis.MaxProfit.max_profit prices = ok r →
          Aegis.MaxProfit.max_profit q = ok r' → r'.val = r.val) := by
    sorry

  /-- For every such c and q, whenever max_profit(prices) returns r and max_profit(q) returns r', we have r' = c * r.
    Preconditions: prices is a nonempty slice with 1 <= len(prices) <= 100000 and 0 <= prices[i] <= 10000 for all i. Let c be a positive integer such that 0 <= c * prices[i] <= 10000 for every i, and let q be the slice of the same length with q[i] = c * prices[i]. -/
  theorem spec_10 (prices q : Slice Std.I64) (c : Int)
      (hlen : 1 ≤ prices.val.length)
      (hlen_ub : prices.val.length ≤ 100000)
      (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
        0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000)
      (hc : 0 < c)
      (hscale_lo : ∀ (i : Nat) (hi : i < prices.val.length), 0 ≤ c * prices.val[i].val)
      (hscale_hi : ∀ (i : Nat) (hi : i < prices.val.length), c * prices.val[i].val ≤ 10000)
      (hq : vals q = (vals prices).map (fun x => c * x)) :
      ∀ r r', Aegis.MaxProfit.max_profit prices = ok r →
        Aegis.MaxProfit.max_profit q = ok r' → r'.val = c * r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (prices q : Slice Std.I64) (c : Int)
        (hlen : 1 ≤ prices.val.length)
        (hlen_ub : prices.val.length ≤ 100000)
        (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
          0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000)
        (hc : 0 < c)
        (hscale_lo : ∀ (i : Nat) (hi : i < prices.val.length), 0 ≤ c * prices.val[i].val)
        (hscale_hi : ∀ (i : Nat) (hi : i < prices.val.length), c * prices.val[i].val ≤ 10000)
        (hq : vals q = (vals prices).map (fun x => c * x)), ∀ r r', Aegis.MaxProfit.max_profit prices = ok r →
          Aegis.MaxProfit.max_profit q = ok r' → r'.val = c * r.val) := by
    sorry

  /-- Whenever max_profit(prices) returns a result r, for every k with 1 <= k <= len(prices), r >= max({0} ∪ { prices[j] - prices[i] | 0 <= i < j < k }), where max is the largest element of the finite set.
    Preconditions: prices is a nonempty slice of 64-bit signed integers with 1 <= len(prices) <= 100000 and, for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000. -/
  theorem spec_11 (prices : Slice Std.I64)
      (hlen : 1 ≤ prices.val.length)
      (hlen_ub : prices.val.length ≤ 100000)
      (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
        0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000) :
      ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
        ∀ k, 1 ≤ k → k ≤ prices.val.length → bestProfit ((vals prices).take k) ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (hlen : 1 ≤ prices.val.length)
        (hlen_ub : prices.val.length ≤ 100000)
        (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
          0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000), ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
          ∀ k, 1 ≤ k → k ≤ prices.val.length → bestProfit ((vals prices).take k) ≤ r.val) := by
    sorry

  /-- Whenever max_profit(prices) returns a result r, for every k with 0 <= k < len(prices), r >= max({0} ∪ { prices[j] - prices[i] | k <= i < j < len(prices) }), where max is the largest element of the finite set.
    Preconditions: prices is a nonempty slice of 64-bit signed integers with 1 <= len(prices) <= 100000 and, for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000. -/
  theorem spec_12 (prices : Slice Std.I64)
      (hlen : 1 ≤ prices.val.length)
      (hlen_ub : prices.val.length ≤ 100000)
      (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
        0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000) :
      ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
        ∀ k, k < prices.val.length → bestProfit ((vals prices).drop k) ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (hlen : 1 ≤ prices.val.length)
        (hlen_ub : prices.val.length ≤ 100000)
        (hbound : ∀ (i : Nat) (hi : i < prices.val.length),
          0 ≤ prices.val[i].val ∧ prices.val[i].val ≤ 10000), ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
          ∀ k, k < prices.val.length → bestProfit ((vals prices).drop k) ≤ r.val) := by
    sorry

  end AegisSpec.MaxProfit
