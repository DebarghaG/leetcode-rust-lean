import Aegis.MaxProfit.Code.Funs

/-!
# Specifications of `Aegis.MaxProfit.max_profit`

LeetCode problem `best-time-to-buy-and-sell-stock-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxProfit

def priceAt (prices : Slice Std.I64) (i : ℕ) : ℤ :=
  if h : i < prices.val.length then (prices.val.get ⟨i, h⟩).val else 0

def refProfit (prices : Slice Std.I64) : ℤ :=
  (List.range (prices.val.length - 1)).foldl
    (fun acc k => acc + max (priceAt prices (k + 1) - priceAt prices k) 0) 0

def adjacentOK : List (ℕ × ℕ) → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => p.2 ≤ q.1 ∧ adjacentOK (q :: rest)

def chainValid (prices : Slice Std.I64) (ps : List (ℕ × ℕ)) : Prop :=
  (∀ p ∈ ps, p.1 ≤ p.2 ∧ p.2 < prices.val.length) ∧ adjacentOK ps

def chainProfit (prices : Slice Std.I64) (ps : List (ℕ × ℕ)) : ℤ :=
  (ps.map (fun p => priceAt prices p.2 - priceAt prices p.1)).sum

/-- Whenever max_profit(prices) returns a result r, r = sum over i from 1 to len(prices)-1 of max(prices[i] - prices[i-1], 0). When len(prices)=1 this is the empty sum and equals 0.
  Preconditions: 1 <= len(prices) <= 30000 and for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000. -/
theorem spec_1 (prices : Slice Std.I64)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000) :
    ∀ r, Aegis.MaxProfit.max_profit prices = ok r → r.val = refProfit prices := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (prices : Slice Std.I64)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000), ∀ r, Aegis.MaxProfit.max_profit prices = ok r → r.val = refProfit prices) := by
  sorry

/-- For every prices satisfying the preconditions, max_profit(prices) returns a result r; it does not fail, panic, or overflow.
  Preconditions: 1 <= len(prices) <= 30000 and for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000. -/
theorem spec_2 (prices : Slice Std.I64)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000) :
    ∃ r, Aegis.MaxProfit.max_profit prices = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (prices : Slice Std.I64)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000), ∃ r, Aegis.MaxProfit.max_profit prices = ok r) := by
  sorry

/-- Whenever max_profit(prices) returns a result r, 0 <= r <= 10000 * (len(prices) - 1).
  Preconditions: 1 <= len(prices) <= 30000 and for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000. -/
theorem spec_3 (prices : Slice Std.I64)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000) :
    ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
      0 ≤ r.val ∧ r.val ≤ 10000 * ((prices.val.length : ℤ) - 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (prices : Slice Std.I64)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000), ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
      0 ≤ r.val ∧ r.val ≤ 10000 * ((prices.val.length : ℤ) - 1)) := by
  sorry

/-- Whenever max_profit(prices) returns a result r, r = 0 if and only if for every i with 0 <= i < len(prices)-1, prices[i+1] <= prices[i].
  Preconditions: 1 <= len(prices) <= 30000 and for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000. -/
theorem spec_4 (prices : Slice Std.I64)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000) :
    ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
      (r.val = 0 ↔ ∀ i, i + 1 < prices.val.length → priceAt prices (i + 1) ≤ priceAt prices i) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (prices : Slice Std.I64)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000), ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
      (r.val = 0 ↔ ∀ i, i + 1 < prices.val.length → priceAt prices (i + 1) ≤ priceAt prices i)) := by
  sorry

/-- Whenever max_profit(prices) returns a result r, r = prices[len(prices)-1] - prices[0].
  Preconditions: 1 <= len(prices) <= 30000; for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000; and for every i with 0 <= i < len(prices)-1, prices[i] <= prices[i+1]. -/
theorem spec_5 (prices : Slice Std.I64)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000)
    (hmono : ∀ i, i + 1 < prices.val.length → priceAt prices i ≤ priceAt prices (i + 1)) :
    ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
      r.val = priceAt prices (prices.val.length - 1) - priceAt prices 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (prices : Slice Std.I64)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000)
    (hmono : ∀ i, i + 1 < prices.val.length → priceAt prices i ≤ priceAt prices (i + 1)), ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
      r.val = priceAt prices (prices.val.length - 1) - priceAt prices 0) := by
  sorry

/-- Whenever max_profit(prices) returns r and max_profit(prices2) returns r2, we have r = r2.
  Preconditions: 1 <= len(prices) <= 30000; for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000. Let c be an integer and let prices2 be the array of the same length with prices2[i] = prices[i] + c for every i. Assume that for every i, 0 <= prices2[i] <= 10000, so prices2 also satisfies the problem constraints. -/
theorem spec_6 (prices prices2 : Slice Std.I64) (c : ℤ)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000)
    (hlen2 : prices2.val.length = prices.val.length)
    (hshift : ∀ i, i < prices.val.length → priceAt prices2 i = priceAt prices i + c)
    (hbounds2 : ∀ i, i < prices2.val.length → 0 ≤ priceAt prices2 i ∧ priceAt prices2 i ≤ 10000) :
    ∀ r r2, Aegis.MaxProfit.max_profit prices = ok r →
      Aegis.MaxProfit.max_profit prices2 = ok r2 → r.val = r2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (prices prices2 : Slice Std.I64) (c : ℤ)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000)
    (hlen2 : prices2.val.length = prices.val.length)
    (hshift : ∀ i, i < prices.val.length → priceAt prices2 i = priceAt prices i + c)
    (hbounds2 : ∀ i, i < prices2.val.length → 0 ≤ priceAt prices2 i ∧ priceAt prices2 i ≤ 10000), ∀ r r2, Aegis.MaxProfit.max_profit prices = ok r →
      Aegis.MaxProfit.max_profit prices2 = ok r2 → r.val = r2.val) := by
  sorry

/-- Whenever max_profit(prices) returns r and max_profit(prices2) returns r2, we have r2 = k * r.
  Preconditions: 1 <= len(prices) <= 30000; for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000. Let k be a nonnegative integer and let prices2 be the array of the same length with prices2[i] = k * prices[i] for every i. Assume that for every i, 0 <= prices2[i] <= 10000, so prices2 also satisfies the problem constraints. -/
theorem spec_7 (prices prices2 : Slice Std.I64) (k : ℕ)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000)
    (hlen2 : prices2.val.length = prices.val.length)
    (hscale : ∀ i, i < prices.val.length → priceAt prices2 i = (k : ℤ) * priceAt prices i)
    (hbounds2 : ∀ i, i < prices2.val.length → 0 ≤ priceAt prices2 i ∧ priceAt prices2 i ≤ 10000) :
    ∀ r r2, Aegis.MaxProfit.max_profit prices = ok r →
      Aegis.MaxProfit.max_profit prices2 = ok r2 → r2.val = (k : ℤ) * r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (prices prices2 : Slice Std.I64) (k : ℕ)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000)
    (hlen2 : prices2.val.length = prices.val.length)
    (hscale : ∀ i, i < prices.val.length → priceAt prices2 i = (k : ℤ) * priceAt prices i)
    (hbounds2 : ∀ i, i < prices2.val.length → 0 ≤ priceAt prices2 i ∧ priceAt prices2 i ≤ 10000), ∀ r r2, Aegis.MaxProfit.max_profit prices = ok r →
      Aegis.MaxProfit.max_profit prices2 = ok r2 → r2.val = (k : ℤ) * r.val) := by
  sorry

/-- Whenever max_profit(prices) returns a result r, for every b and s with 0 <= b <= s < len(prices), prices[s] - prices[b] <= r.
  Preconditions: 1 <= len(prices) <= 30000 and for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000. -/
theorem spec_8 (prices : Slice Std.I64)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000) :
    ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
      ∀ b s : ℕ, b ≤ s → s < prices.val.length →
        priceAt prices s - priceAt prices b ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (prices : Slice Std.I64)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000), ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
      ∀ b s : ℕ, b ≤ s → s < prices.val.length →
        priceAt prices s - priceAt prices b ≤ r.val) := by
  sorry

/-- Whenever max_profit(prices) returns a result r, there exists a finite sequence of pairs (b_j, s_j) for j = 0, ..., m-1 with m >= 0 such that for every j, 0 <= b_j <= s_j < len(prices), for every j with 0 <= j < m-1 we have s_j <= b_{j+1}, and sum over j of (prices[s_j] - prices[b_j]) = r. The empty sequence m=0 has profit 0.
  Preconditions: 1 <= len(prices) <= 30000 and for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000. -/
theorem spec_9 (prices : Slice Std.I64)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000) :
    ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
      ∃ ps : List (ℕ × ℕ), chainValid prices ps ∧ chainProfit prices ps = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (prices : Slice Std.I64)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000), ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
      ∃ ps : List (ℕ × ℕ), chainValid prices ps ∧ chainProfit prices ps = r.val) := by
  sorry

/-- Whenever max_profit(prices) returns a result r, for every finite sequence of pairs (b_j, s_j) for j = 0, ..., m-1 with m >= 0 satisfying for every j 0 <= b_j <= s_j < len(prices) and for every j with 0 <= j < m-1 s_j <= b_{j+1}, the total profit sum over j of (prices[s_j] - prices[b_j]) is at most r.
  Preconditions: 1 <= len(prices) <= 30000 and for every i with 0 <= i < len(prices), 0 <= prices[i] <= 10000. -/
theorem spec_10 (prices : Slice Std.I64)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000) :
    ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
      ∀ ps : List (ℕ × ℕ), chainValid prices ps → chainProfit prices ps ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (prices : Slice Std.I64)
    (hlen_lo : 1 ≤ prices.val.length) (hlen_hi : prices.val.length ≤ 30000)
    (hbounds : ∀ i, i < prices.val.length → 0 ≤ priceAt prices i ∧ priceAt prices i ≤ 10000), ∀ r, Aegis.MaxProfit.max_profit prices = ok r →
      ∀ ps : List (ℕ × ℕ), chainValid prices ps → chainProfit prices ps ≤ r.val) := by
  sorry

end AegisSpec.MaxProfit
