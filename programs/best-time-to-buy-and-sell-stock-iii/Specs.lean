import Aegis.MaxProfit.Code.Funs

/-!
# Specifications of `Aegis.MaxProfit.max_profit`

LeetCode problem `best-time-to-buy-and-sell-stock-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxProfit

open Aegis.MaxProfit

def vals (prices : Slice I64) : List Int := prices.val.map (fun x => x.val)

def size (prices : Slice I64) : Nat := prices.val.length

def valueAt (prices : Slice I64) (i : Nat) : Int := (vals prices).getD i 0

def planProfit (prices : Slice I64) (t : List (Nat × Nat)) : Int :=
  (t.map (fun p => valueAt prices p.2 - valueAt prices p.1)).sum

def IsPlan (prices : Slice I64) : List (Nat × Nat) → Prop
  | [] => True
  | [(b, s)] => b ≤ s ∧ s < size prices
  | [(b1, s1), (b2, s2)] =>
    b1 ≤ s1 ∧ s1 < size prices ∧ b2 ≤ s2 ∧ s2 < size prices ∧ s1 ≤ b2
  | _ => False

def Profitable (prices : Slice I64) (p : Nat × Nat) : Prop :=
  p.1 < p.2 ∧ valueAt prices p.1 < valueAt prices p.2

def IsProfitablePlan (prices : Slice I64) (t : List (Nat × Nat)) : Prop :=
  IsPlan prices t ∧ ∀ p ∈ t, Profitable prices p

def riseSum (prices : Slice I64) : Int :=
  (((vals prices).zip ((vals prices).drop 1)).map (fun p => max 0 (p.2 - p.1))).sum

/-- Whenever max_profit(prices) returns a result r, r equals the maximum over all plans of the plan's total profit, where a plan is either the empty sequence of transactions (profit 0), a single transaction (b, s) with 0 <= b <= s < len(prices) and profit prices[s] - prices[b], or two transactions (b1, s1) and (b2, s2) with 0 <= b1 <= s1 < len(prices), 0 <= b2 <= s2 < len(prices), s1 <= b2, and total profit (prices[s1] - prices[b1]) + (prices[s2] - prices[b2]).
  Preconditions: 1 <= len(prices) <= 100000, and for every i with 0 <= i < len(prices), 0 <= prices[i] <= 100000. -/
theorem spec_1 (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000)
    (r : I64) (hr : max_profit prices = ok r) :
    (∀ t, IsPlan prices t → planProfit prices t ≤ r.val) ∧
      ∃ t, IsPlan prices t ∧ planProfit prices t = r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000)
    (r : I64) (hr : max_profit prices = ok r), (∀ t, IsPlan prices t → planProfit prices t ≤ r.val) ∧
      ∃ t, IsPlan prices t ∧ planProfit prices t = r.val) := by
  sorry

/-- max_profit(prices) returns a successful result (i.e., it does not fail, overflow, or panic) for every input satisfying the preconditions.
  Preconditions: 1 <= len(prices) <= 100000, and for every i with 0 <= i < len(prices), 0 <= prices[i] <= 100000. -/
theorem spec_2 (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000) :
    ∃ r, max_profit prices = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000), ∃ r, max_profit prices = ok r) := by
  sorry

/-- Whenever max_profit(prices) returns a result r, r <= sum_{i=0}^{len(prices)-2} max(0, prices[i+1] - prices[i]).
  Preconditions: 1 <= len(prices) <= 100000, and for every i with 0 <= i < len(prices), 0 <= prices[i] <= 100000. -/
theorem spec_3 (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000)
    (r : I64) (hr : max_profit prices = ok r) :
    r.val ≤ riseSum prices := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000)
    (r : I64) (hr : max_profit prices = ok r), r.val ≤ riseSum prices) := by
  sorry

/-- Whenever max_profit(prices) returns a result r, r = max(0, prices[1] - prices[0]).
  Preconditions: len(prices) = 2, 0 <= prices[0] <= 100000, and 0 <= prices[1] <= 100000. -/
theorem spec_4 (prices : Slice I64)
    (hlen : size prices = 2)
    (h0 : 0 ≤ valueAt prices 0 ∧ valueAt prices 0 ≤ 100000)
    (h1 : 0 ≤ valueAt prices 1 ∧ valueAt prices 1 ≤ 100000)
    (r : I64) (hr : max_profit prices = ok r) :
    r.val = max 0 (valueAt prices 1 - valueAt prices 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (prices : Slice I64)
    (hlen : size prices = 2)
    (h0 : 0 ≤ valueAt prices 0 ∧ valueAt prices 0 ≤ 100000)
    (h1 : 0 ≤ valueAt prices 1 ∧ valueAt prices 1 ≤ 100000)
    (r : I64) (hr : max_profit prices = ok r), r.val = max 0 (valueAt prices 1 - valueAt prices 0)) := by
  sorry

/-- Whenever max_profit(prices) returns a result r, r = 0.
  Preconditions: 1 <= len(prices) <= 100000, for every i with 0 <= i < len(prices), 0 <= prices[i] <= 100000, and for every i with 0 <= i < len(prices)-1, prices[i] >= prices[i+1]. -/
theorem spec_5 (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000)
    (hdec : ∀ i, i < size prices - 1 → valueAt prices (i + 1) ≤ valueAt prices i)
    (r : I64) (hr : max_profit prices = ok r) :
    r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000)
    (hdec : ∀ i, i < size prices - 1 → valueAt prices (i + 1) ≤ valueAt prices i)
    (r : I64) (hr : max_profit prices = ok r), r.val = 0) := by
  sorry

/-- Whenever max_profit(prices) returns a result r, r = prices[len(prices)-1] - prices[0].
  Preconditions: 1 <= len(prices) <= 100000, for every i with 0 <= i < len(prices), 0 <= prices[i] <= 100000, and for every i with 0 <= i < len(prices)-1, prices[i] <= prices[i+1]. -/
theorem spec_6 (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000)
    (hinc : ∀ i, i < size prices - 1 → valueAt prices i ≤ valueAt prices (i + 1))
    (r : I64) (hr : max_profit prices = ok r) :
    r.val = valueAt prices (size prices - 1) - valueAt prices 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000)
    (hinc : ∀ i, i < size prices - 1 → valueAt prices i ≤ valueAt prices (i + 1))
    (r : I64) (hr : max_profit prices = ok r), r.val = valueAt prices (size prices - 1) - valueAt prices 0) := by
  sorry

/-- Whenever max_profit(prices) returns a result r, for every plan P (as defined in spec_1), the total profit of P is at most r.
  Preconditions: 1 <= len(prices) <= 100000, and for every i with 0 <= i < len(prices), 0 <= prices[i] <= 100000. -/
theorem spec_7 (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000)
    (r : I64) (hr : max_profit prices = ok r) :
    ∀ t, IsPlan prices t → planProfit prices t ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000)
    (r : I64) (hr : max_profit prices = ok r), ∀ t, IsPlan prices t → planProfit prices t ≤ r.val) := by
  sorry

/-- Whenever max_profit(prices) returns a result r, there exists a plan P (as defined in spec_1) whose total profit equals r.
  Preconditions: 1 <= len(prices) <= 100000, and for every i with 0 <= i < len(prices), 0 <= prices[i] <= 100000. -/
theorem spec_8 (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000)
    (r : I64) (hr : max_profit prices = ok r) :
    ∃ t, IsPlan prices t ∧ planProfit prices t = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000)
    (r : I64) (hr : max_profit prices = ok r), ∃ t, IsPlan prices t ∧ planProfit prices t = r.val) := by
  sorry

/-- For every integer c such that 0 <= prices[i] + c <= 100000 for every i with 0 <= i < len(prices), let prices' be the slice defined by prices'[i] = prices[i] + c. Then max_profit(prices) and max_profit(prices') return the same result.
  Preconditions: 1 <= len(prices) <= 100000, and for every i with 0 <= i < len(prices), 0 <= prices[i] <= 100000. -/
theorem spec_9 (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000)
    (c : Int)
    (hc : ∀ i, i < size prices → 0 ≤ valueAt prices i + c ∧ valueAt prices i + c ≤ 100000)
    (prices' : Slice I64)
    (hvals : vals prices' = (vals prices).map (fun x => x + c)) :
    max_profit prices = max_profit prices' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000)
    (c : Int)
    (hc : ∀ i, i < size prices → 0 ≤ valueAt prices i + c ∧ valueAt prices i + c ≤ 100000)
    (prices' : Slice I64)
    (hvals : vals prices' = (vals prices).map (fun x => x + c)), max_profit prices = max_profit prices') := by
  sorry

/-- Whenever max_profit(prices) returns a result r, r equals the maximum total profit over the set of plans (as defined in spec_1) in which every transaction (b, s) satisfies b < s and prices[s] > prices[b], together with the empty plan (total profit 0).
  Preconditions: 1 <= len(prices) <= 100000, and for every i with 0 <= i < len(prices), 0 <= prices[i] <= 100000. -/
theorem spec_10 (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000)
    (r : I64) (hr : max_profit prices = ok r) :
    (∀ t, IsProfitablePlan prices t → planProfit prices t ≤ r.val) ∧
      (∃ t, IsProfitablePlan prices t ∧ planProfit prices t = r.val) ∧
        0 ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000)
    (r : I64) (hr : max_profit prices = ok r), (∀ t, IsProfitablePlan prices t → planProfit prices t ≤ r.val) ∧
      (∃ t, IsProfitablePlan prices t ∧ planProfit prices t = r.val) ∧
        0 ≤ r.val) := by
  sorry

/-- For every positive integer c such that 0 <= c * prices[i] <= 100000 for every i with 0 <= i < len(prices), let prices' be the slice defined by prices'[i] = c * prices[i]. Then max_profit(prices') = c * max_profit(prices) (whenever both return results; by spec_2 they do).
  Preconditions: 1 <= len(prices) <= 100000, and for every i with 0 <= i < len(prices), 0 <= prices[i] <= 100000. -/
theorem spec_11 (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000)
    (c : Nat) (hc : 0 < c)
    (hcrange : ∀ i, i < size prices →
      0 ≤ (c : Int) * valueAt prices i ∧ (c : Int) * valueAt prices i ≤ 100000)
    (prices' : Slice I64)
    (hvals : vals prices' = (vals prices).map (fun x => (c : Int) * x))
    (r r' : I64) (hr : max_profit prices = ok r) (hr' : max_profit prices' = ok r') :
    r'.val = (c : Int) * r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (prices : Slice I64)
    (hlen : 1 ≤ size prices) (hlen' : size prices ≤ 100000)
    (hrange : ∀ i, i < size prices → 0 ≤ valueAt prices i ∧ valueAt prices i ≤ 100000)
    (c : Nat) (hc : 0 < c)
    (hcrange : ∀ i, i < size prices →
      0 ≤ (c : Int) * valueAt prices i ∧ (c : Int) * valueAt prices i ≤ 100000)
    (prices' : Slice I64)
    (hvals : vals prices' = (vals prices).map (fun x => (c : Int) * x))
    (r r' : I64) (hr : max_profit prices = ok r) (hr' : max_profit prices' = ok r'), r'.val = (c : Int) * r.val) := by
  sorry

end AegisSpec.MaxProfit
