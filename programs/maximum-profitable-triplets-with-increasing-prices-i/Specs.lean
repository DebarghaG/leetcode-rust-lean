import Aegis.MaxProfit.Code.Funs

/-!
# Specifications of `Aegis.MaxProfit.max_profit`

LeetCode problem `maximum-profitable-triplets-with-increasing-prices-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxProfit

  def valAt (s : Slice Std.I64) (t : Nat) : Int :=
    match s.val[t]? with
    | some x => x.val
    | none => 0

  theorem valAt_eq_getElem (s : Slice Std.I64) (t : Nat) (h : t < s.val.length) :
      valAt s t = (s.val[t]).val := by
    simp only [valAt, List.getElem?_eq_getElem h]

  theorem valAt_eq_zero (s : Slice Std.I64) (t : Nat) (h : s.val.length ≤ t) :
      valAt s t = 0 := by
    have h' : s.val[t]? = none := by
      rw [List.getElem?_eq_none_iff]
      exact h
    simp only [valAt, h']

  def GoodTriple (prices profits : Slice Std.I64) (i j k : Nat) : Prop :=
    i < j ∧ j < k ∧ k < prices.val.length ∧ k < profits.val.length ∧
      valAt prices i < valAt prices j ∧ valAt prices j < valAt prices k

  def tripleSum (profits : Slice Std.I64) (i j k : Nat) : Int :=
    valAt profits i + valAt profits j + valAt profits k

  def HasGoodTriple (prices profits : Slice Std.I64) : Prop :=
    ∃ i j k, GoodTriple prices profits i j k

  def IsGoodMax (prices profits : Slice Std.I64) (x : Int) : Prop :=
    (∀ i j k, GoodTriple prices profits i j k → tripleSum profits i j k ≤ x) ∧
      ∃ i j k, GoodTriple prices profits i j k ∧ tripleSum profits i j k = x

  def IsAllTripleMax (profits : Slice Std.I64) (x : Int) : Prop :=
    (∀ a b c, a < b → b < c → c < profits.val.length → tripleSum profits a b c ≤ x) ∧
      ∃ a b c, a < b ∧ b < c ∧ c < profits.val.length ∧ tripleSum profits a b c = x

  def IsProfitsMin (profits : Slice Std.I64) (x : Int) : Prop :=
    (∀ t, t < profits.val.length → x ≤ valAt profits t) ∧
      ∃ t, t < profits.val.length ∧ valAt profits t = x

  /-- Let T = { profits[i] + profits[j] + profits[k] | 0 <= i < j < k < n and prices[i] < prices[j] < prices[k] }. Whenever max_profit(prices, profits) returns a result r, if T is nonempty then r = max(T); if T is empty then r = -1.
    Preconditions: Let n = len(prices). Preconditions: len(prices) = len(profits) = n; 3 <= n <= 2000; for every t with 0 <= t < n, 1 <= prices[t] <= 1000000 and 1 <= profits[t] <= 1000000. -/
  theorem spec_1 (prices profits : Slice Std.I64)
      (hlen : prices.val.length = profits.val.length)
      (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
      (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
      (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
      (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r) :
      (HasGoodTriple prices profits → IsGoodMax prices profits r.val) ∧
        (¬ HasGoodTriple prices profits → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (prices profits : Slice Std.I64)
        (hlen : prices.val.length = profits.val.length)
        (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
        (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
        (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
        (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r), (HasGoodTriple prices profits → IsGoodMax prices profits r.val) ∧
          (¬ HasGoodTriple prices profits → r.val = -1)) := by
    sorry

  /-- For every input satisfying the preconditions, max_profit(prices, profits) returns a result r; it does not fail, panic, or overflow.
    Preconditions: Let n = len(prices). Preconditions: len(prices) = len(profits) = n; 3 <= n <= 2000; for every t with 0 <= t < n, 1 <= prices[t] <= 1000000 and 1 <= profits[t] <= 1000000. -/
  theorem spec_2 (prices profits : Slice Std.I64)
      (hlen : prices.val.length = profits.val.length)
      (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
      (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
      (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000) :
      ∃ r, Aegis.MaxProfit.max_profit prices profits = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (prices profits : Slice Std.I64)
        (hlen : prices.val.length = profits.val.length)
        (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
        (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
        (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000), ∃ r, Aegis.MaxProfit.max_profit prices profits = ok r) := by
    sorry

  /-- Whenever max_profit(prices, profits) returns a result r, r = -1 if and only if there do not exist indices i, j, k such that 0 <= i < j < k < n and prices[i] < prices[j] < prices[k].
    Preconditions: Let n = len(prices). Preconditions: len(prices) = len(profits) = n; 3 <= n <= 2000; for every t with 0 <= t < n, 1 <= prices[t] <= 1000000 and 1 <= profits[t] <= 1000000. -/
  theorem spec_3 (prices profits : Slice Std.I64)
      (hlen : prices.val.length = profits.val.length)
      (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
      (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
      (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
      (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r) :
      (r.val = -1 ↔ ¬ HasGoodTriple prices profits) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (prices profits : Slice Std.I64)
        (hlen : prices.val.length = profits.val.length)
        (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
        (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
        (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
        (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r), (r.val = -1 ↔ ¬ HasGoodTriple prices profits)) := by
    sorry

  /-- Whenever max_profit(prices, profits) returns a result r with r != -1, there exist indices i, j, k such that 0 <= i < j < k < n, prices[i] < prices[j] < prices[k], and r = profits[i] + profits[j] + profits[k].
    Preconditions: Let n = len(prices). Preconditions: len(prices) = len(profits) = n; 3 <= n <= 2000; for every t with 0 <= t < n, 1 <= prices[t] <= 1000000 and 1 <= profits[t] <= 1000000. -/
  theorem spec_4 (prices profits : Slice Std.I64)
      (hlen : prices.val.length = profits.val.length)
      (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
      (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
      (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
      (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r)
      (hne : r.val ≠ -1) :
      ∃ i j k, GoodTriple prices profits i j k ∧ r.val = tripleSum profits i j k := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (prices profits : Slice Std.I64)
        (hlen : prices.val.length = profits.val.length)
        (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
        (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
        (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
        (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r)
        (hne : r.val ≠ -1), ∃ i j k, GoodTriple prices profits i j k ∧ r.val = tripleSum profits i j k) := by
    sorry

  /-- Whenever max_profit(prices, profits) returns a result r with r != -1, for every choice of indices i, j, k with 0 <= i < j < k < n and prices[i] < prices[j] < prices[k], we have profits[i] + profits[j] + profits[k] <= r.
    Preconditions: Let n = len(prices). Preconditions: len(prices) = len(profits) = n; 3 <= n <= 2000; for every t with 0 <= t < n, 1 <= prices[t] <= 1000000 and 1 <= profits[t] <= 1000000. -/
  theorem spec_5 (prices profits : Slice Std.I64)
      (hlen : prices.val.length = profits.val.length)
      (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
      (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
      (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
      (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r)
      (hne : r.val ≠ -1) :
      ∀ i j k, GoodTriple prices profits i j k → tripleSum profits i j k ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (prices profits : Slice Std.I64)
        (hlen : prices.val.length = profits.val.length)
        (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
        (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
        (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
        (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r)
        (hne : r.val ≠ -1), ∀ i j k, GoodTriple prices profits i j k → tripleSum profits i j k ≤ r.val) := by
    sorry

  /-- Whenever max_profit(prices, profits) returns a result r, if r != -1 then 3 <= r <= 3000000.
    Preconditions: Let n = len(prices). Preconditions: len(prices) = len(profits) = n; 3 <= n <= 2000; for every t with 0 <= t < n, 1 <= prices[t] <= 1000000 and 1 <= profits[t] <= 1000000. -/
  theorem spec_6 (prices profits : Slice Std.I64)
      (hlen : prices.val.length = profits.val.length)
      (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
      (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
      (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
      (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r) :
      r.val ≠ -1 → 3 ≤ r.val ∧ r.val ≤ 3000000 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (prices profits : Slice Std.I64)
        (hlen : prices.val.length = profits.val.length)
        (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
        (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
        (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
        (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r), r.val ≠ -1 → 3 ≤ r.val ∧ r.val ≤ 3000000) := by
    sorry

  /-- Whenever max_profit(prices, profits) returns a result r, if prices[0] < prices[1] < prices[2] then r = profits[0] + profits[1] + profits[2]; otherwise r = -1.
    Preconditions: Let n = len(prices). Preconditions: len(prices) = len(profits) = n; n = 3; for every t with 0 <= t < n, 1 <= prices[t] <= 1000000 and 1 <= profits[t] <= 1000000. -/
  theorem spec_7 (prices profits : Slice Std.I64)
      (hlen : prices.val.length = profits.val.length)
      (hn : prices.val.length = 3)
      (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
      (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
      (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r) :
      (valAt prices 0 < valAt prices 1 ∧ valAt prices 1 < valAt prices 2 →
          r.val = valAt profits 0 + valAt profits 1 + valAt profits 2) ∧
        (¬ (valAt prices 0 < valAt prices 1 ∧ valAt prices 1 < valAt prices 2) → r.val = -1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (prices profits : Slice Std.I64)
        (hlen : prices.val.length = profits.val.length)
        (hn : prices.val.length = 3)
        (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
        (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
        (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r), (valAt prices 0 < valAt prices 1 ∧ valAt prices 1 < valAt prices 2 →
            r.val = valAt profits 0 + valAt profits 1 + valAt profits 2) ∧
          (¬ (valAt prices 0 < valAt prices 1 ∧ valAt prices 1 < valAt prices 2) → r.val = -1)) := by
    sorry

  /-- Whenever max_profit(prices, profits) returns a result r, r = max { profits[i] + profits[j] + profits[k] | 0 <= i < j < k < n }.
    Preconditions: Let n = len(prices). Preconditions: len(prices) = len(profits) = n; 3 <= n <= 2000; for every t with 0 <= t < n, 1 <= prices[t] <= 1000000 and 1 <= profits[t] <= 1000000; for every t with 0 <= t < n-1, prices[t] < prices[t+1]. -/
  theorem spec_8 (prices profits : Slice Std.I64)
      (hlen : prices.val.length = profits.val.length)
      (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
      (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
      (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
      (hmono : ∀ t, t + 1 < prices.val.length → valAt prices t < valAt prices (t + 1))
      (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r) :
      IsAllTripleMax profits r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (prices profits : Slice Std.I64)
        (hlen : prices.val.length = profits.val.length)
        (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
        (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
        (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
        (hmono : ∀ t, t + 1 < prices.val.length → valAt prices t < valAt prices (t + 1))
        (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r), IsAllTripleMax profits r.val) := by
    sorry

  /-- Whenever max_profit(prices, profits) returns a result r, if there exist indices i, j, k with 0 <= i < j < k < n and prices[i] < prices[j] < prices[k], then r = 3*c; otherwise r = -1.
    Preconditions: Let n = len(prices). Preconditions: len(prices) = len(profits) = n; 3 <= n <= 2000; for every t with 0 <= t < n, 1 <= prices[t] <= 1000000 and 1 <= profits[t] <= 1000000; there exists an integer c with 1 <= c <= 1000000 such that profits[t] = c for every t with 0 <= t < n. -/
  theorem spec_9 (prices profits : Slice Std.I64)
      (hlen : prices.val.length = profits.val.length)
      (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
      (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
      (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
      (c : Int) (hc_low : 1 ≤ c) (hc_high : c ≤ 1000000)
      (hconst : ∀ t, t < profits.val.length → valAt profits t = c)
      (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r) :
      (HasGoodTriple prices profits → r.val = 3 * c) ∧
        (¬ HasGoodTriple prices profits → r.val = -1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (prices profits : Slice Std.I64)
        (hlen : prices.val.length = profits.val.length)
        (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
        (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
        (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
        (c : Int) (hc_low : 1 ≤ c) (hc_high : c ≤ 1000000)
        (hconst : ∀ t, t < profits.val.length → valAt profits t = c)
        (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r), (HasGoodTriple prices profits → r.val = 3 * c) ∧
          (¬ HasGoodTriple prices profits → r.val = -1)) := by
    sorry

  /-- Let Q be the maximum of profits[a] + profits[b] + profits[c] over all triples 0 <= a < b < c < n (over all distinct-index triples, ignoring prices). Whenever max_profit(prices, profits) returns a result r, if r != -1 then r <= Q.
    Preconditions: Let n = len(prices). Preconditions: len(prices) = len(profits) = n; 3 <= n <= 2000; for every t with 0 <= t < n, 1 <= prices[t] <= 1000000 and 1 <= profits[t] <= 1000000. -/
  theorem spec_10 (prices profits : Slice Std.I64)
      (hlen : prices.val.length = profits.val.length)
      (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
      (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
      (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
      (Q : Int) (hQ : IsAllTripleMax profits Q)
      (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r) :
      r.val ≠ -1 → r.val ≤ Q := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (prices profits : Slice Std.I64)
        (hlen : prices.val.length = profits.val.length)
        (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
        (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
        (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
        (Q : Int) (hQ : IsAllTripleMax profits Q)
        (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r), r.val ≠ -1 → r.val ≤ Q) := by
    sorry

  /-- Let m be the minimum of profits[t] for 0 <= t < n. Whenever max_profit(prices, profits) returns a result r, if r != -1 then r >= 3*m.
    Preconditions: Let n = len(prices). Preconditions: len(prices) = len(profits) = n; 3 <= n <= 2000; for every t with 0 <= t < n, 1 <= prices[t] <= 1000000 and 1 <= profits[t] <= 1000000. -/
  theorem spec_11 (prices profits : Slice Std.I64)
      (hlen : prices.val.length = profits.val.length)
      (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
      (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
      (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
      (m : Int) (hm : IsProfitsMin profits m)
      (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r) :
      r.val ≠ -1 → 3 * m ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (prices profits : Slice Std.I64)
        (hlen : prices.val.length = profits.val.length)
        (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
        (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
        (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
        (m : Int) (hm : IsProfitsMin profits m)
        (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r), r.val ≠ -1 → 3 * m ≤ r.val) := by
    sorry

  /-- Let Q be the maximum of profits[a] + profits[b] + profits[c] over all triples 0 <= a < b < c < n. Whenever max_profit(prices, profits) returns a result r, if there exist indices i, j, k with 0 <= i < j < k < n, prices[i] < prices[j] < prices[k], and profits[i] + profits[j] + profits[k] = Q, then r = Q.
    Preconditions: Let n = len(prices). Preconditions: len(prices) = len(profits) = n; 3 <= n <= 2000; for every t with 0 <= t < n, 1 <= prices[t] <= 1000000 and 1 <= profits[t] <= 1000000. -/
  theorem spec_12 (prices profits : Slice Std.I64)
      (hlen : prices.val.length = profits.val.length)
      (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
      (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
      (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
      (Q : Int) (hQ : IsAllTripleMax profits Q)
      (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r) :
      (∃ i j k, GoodTriple prices profits i j k ∧ tripleSum profits i j k = Q) → r.val = Q := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (prices profits : Slice Std.I64)
        (hlen : prices.val.length = profits.val.length)
        (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
        (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
        (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
        (Q : Int) (hQ : IsAllTripleMax profits Q)
        (r : Std.I64) (hr : Aegis.MaxProfit.max_profit prices profits = ok r), (∃ i j k, GoodTriple prices profits i j k ∧ tripleSum profits i j k = Q) → r.val = Q) := by
    sorry

  /-- Whenever max_profit(prices, profits) returns a result r and max_profit(prices', profits) returns a result r', if for every a and b with 0 <= a < n and 0 <= b < n we have prices[a] < prices[b] exactly when prices'[a] < prices'[b], then r = r'.
    Preconditions: Let n = len(prices). Preconditions: len(prices) = len(profits) = len(prices') = n; 3 <= n <= 2000; for every t with 0 <= t < n, 1 <= prices[t] <= 1000000, 1 <= prices'[t] <= 1000000, and 1 <= profits[t] <= 1000000. -/
  theorem spec_13 (prices prices' profits : Slice Std.I64)
      (hlen : prices.val.length = profits.val.length)
      (hlen' : prices'.val.length = prices.val.length)
      (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
      (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
      (hprices' : ∀ t, t < prices'.val.length → 1 ≤ valAt prices' t ∧ valAt prices' t ≤ 1000000)
      (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
      (horder : ∀ a b, a < prices.val.length → b < prices.val.length →
        (valAt prices a < valAt prices b ↔ valAt prices' a < valAt prices' b))
      (r r' : Std.I64)
      (hr : Aegis.MaxProfit.max_profit prices profits = ok r)
      (hr' : Aegis.MaxProfit.max_profit prices' profits = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (prices prices' profits : Slice Std.I64)
        (hlen : prices.val.length = profits.val.length)
        (hlen' : prices'.val.length = prices.val.length)
        (hlo : 3 ≤ prices.val.length) (hhi : prices.val.length ≤ 2000)
        (hprices : ∀ t, t < prices.val.length → 1 ≤ valAt prices t ∧ valAt prices t ≤ 1000000)
        (hprices' : ∀ t, t < prices'.val.length → 1 ≤ valAt prices' t ∧ valAt prices' t ≤ 1000000)
        (hprofits : ∀ t, t < profits.val.length → 1 ≤ valAt profits t ∧ valAt profits t ≤ 1000000)
        (horder : ∀ a b, a < prices.val.length → b < prices.val.length →
          (valAt prices a < valAt prices b ↔ valAt prices' a < valAt prices' b))
        (r r' : Std.I64)
        (hr : Aegis.MaxProfit.max_profit prices profits = ok r)
        (hr' : Aegis.MaxProfit.max_profit prices' profits = ok r'), r.val = r'.val) := by
    sorry

  end AegisSpec.MaxProfit
