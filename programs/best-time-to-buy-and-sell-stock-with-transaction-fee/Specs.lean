import Aegis.MaxProfit.Code.Funs

/-!
# Specifications of `Aegis.MaxProfit.max_profit`

LeetCode problem `best-time-to-buy-and-sell-stock-with-transaction-fee`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxProfit (max_profit)

  namespace AegisSpec.MaxProfit

  structure Trade where

    buy : Nat

    sell : Nat

  def TradesOrdered : List Trade → Prop
    | [] => True
    | [_] => True
    | t₁ :: t₂ :: ts => t₁.sell < t₂.buy ∧ TradesOrdered (t₂ :: ts)

  def IsTradeSeq (n : Nat) (T : List Trade) : Prop :=
    (∀ t ∈ T, t.buy < t.sell ∧ t.sell < n) ∧ TradesOrdered T

  def priceAt (p : List Int) (i : Nat) : Int := p.getD i 0

  def netProfit (p : List Int) (fee : Int) (T : List Trade) : Int :=
    (T.map (fun t => priceAt p t.sell - priceAt p t.buy - fee)).sum

  def riseSum (p : List Int) : Int :=
    ((p.zip p.tail).map (fun q => max 0 (q.2 - q.1))).sum

  def maxPrice (p : List Int) : Int := p.max?.getD 0

  def minPrice (p : List Int) : Int := p.min?.getD 0

  /-- Let n = len(prices). A trade sequence is a finite sequence ((b_1,s_1),...,(b_k,s_k)) with k >= 0 such that for every j with 1 <= j <= k, 0 <= b_j < s_j < n, and for every j with 1 <= j < k, s_j < b_{j+1}. Its net profit is sum_{j=1}^k (prices[s_j] - prices[b_j] - fee), and the empty sequence has net profit 0. The function returns a result r and r is the maximum net profit over all such trade sequences.
    Preconditions: len(prices) >= 1 and len(prices) <= 50000; for every i with 0 <= i < len(prices), 1 <= prices[i] < 50000; 0 <= fee < 50000. -/
  theorem spec_1 (prices : Slice Std.I64) (fee : Std.I64)
      (hlen_pos : 1 ≤ prices.val.length)
      (hlen_le : prices.val.length ≤ 50000)
      (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
        1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
      (hfee_lo : 0 ≤ fee.val)
      (hfee_hi : fee.val < 50000) :
      ∃ r : Std.I64,
        max_profit prices fee = ok r ∧
        (∃ T : List Trade,
          IsTradeSeq prices.val.length T ∧
          r.val = netProfit (prices.val.map (fun x => x.val)) fee.val T) ∧
        (∀ T : List Trade,
          IsTradeSeq prices.val.length T →
          netProfit (prices.val.map (fun x => x.val)) fee.val T ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (prices : Slice Std.I64) (fee : Std.I64)
        (hlen_pos : 1 ≤ prices.val.length)
        (hlen_le : prices.val.length ≤ 50000)
        (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
          1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
        (hfee_lo : 0 ≤ fee.val)
        (hfee_hi : fee.val < 50000), ∃ r : Std.I64,
          max_profit prices fee = ok r ∧
          (∃ T : List Trade,
            IsTradeSeq prices.val.length T ∧
            r.val = netProfit (prices.val.map (fun x => x.val)) fee.val T) ∧
          (∀ T : List Trade,
            IsTradeSeq prices.val.length T →
            netProfit (prices.val.map (fun x => x.val)) fee.val T ≤ r.val)) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail because of arithmetic overflow, out-of-bounds access, or panic.
    Preconditions: len(prices) >= 1 and len(prices) <= 50000; for every i with 0 <= i < len(prices), 1 <= prices[i] < 50000; 0 <= fee < 50000. -/
  theorem spec_2 (prices : Slice Std.I64) (fee : Std.I64)
      (hlen_pos : 1 ≤ prices.val.length)
      (hlen_le : prices.val.length ≤ 50000)
      (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
        1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
      (hfee_lo : 0 ≤ fee.val)
      (hfee_hi : fee.val < 50000) :
      ∃ r : Std.I64, max_profit prices fee = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (prices : Slice Std.I64) (fee : Std.I64)
        (hlen_pos : 1 ≤ prices.val.length)
        (hlen_le : prices.val.length ≤ 50000)
        (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
          1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
        (hfee_lo : 0 ≤ fee.val)
        (hfee_hi : fee.val < 50000), ∃ r : Std.I64, max_profit prices fee = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r.
    Preconditions: len(prices) >= 1 and len(prices) <= 50000; for every i with 0 <= i < len(prices), 1 <= prices[i] < 50000; 0 <= fee < 50000. -/
  theorem spec_3 (prices : Slice Std.I64) (fee : Std.I64)
      (hlen_pos : 1 ≤ prices.val.length)
      (hlen_le : prices.val.length ≤ 50000)
      (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
        1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
      (hfee_lo : 0 ≤ fee.val)
      (hfee_hi : fee.val < 50000) :
      ∀ r : Std.I64, max_profit prices fee = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (prices : Slice Std.I64) (fee : Std.I64)
        (hlen_pos : 1 ≤ prices.val.length)
        (hlen_le : prices.val.length ≤ 50000)
        (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
          1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
        (hfee_lo : 0 ≤ fee.val)
        (hfee_hi : fee.val < 50000), ∀ r : Std.I64, max_profit prices fee = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= sum_{i=0}^{len(prices)-2} max(0, prices[i+1] - prices[i]), where the empty sum is 0 when len(prices)=1 and max(0,x) is x when x>0 and 0 otherwise.
    Preconditions: len(prices) >= 1 and len(prices) <= 50000; for every i with 0 <= i < len(prices), 1 <= prices[i] < 50000; 0 <= fee < 50000. -/
  theorem spec_4 (prices : Slice Std.I64) (fee : Std.I64)
      (hlen_pos : 1 ≤ prices.val.length)
      (hlen_le : prices.val.length ≤ 50000)
      (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
        1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
      (hfee_lo : 0 ≤ fee.val)
      (hfee_hi : fee.val < 50000) :
      ∀ r : Std.I64,
        max_profit prices fee = ok r →
        r.val ≤ riseSum (prices.val.map (fun x => x.val)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (prices : Slice Std.I64) (fee : Std.I64)
        (hlen_pos : 1 ≤ prices.val.length)
        (hlen_le : prices.val.length ≤ 50000)
        (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
          1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
        (hfee_lo : 0 ≤ fee.val)
        (hfee_hi : fee.val < 50000), ∀ r : Std.I64,
          max_profit prices fee = ok r →
          r.val ≤ riseSum (prices.val.map (fun x => x.val))) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: len(prices) >= 1 and len(prices) <= 50000; for every i with 0 <= i < len(prices), 1 <= prices[i] < 50000; 0 <= fee < 50000; for every i with 0 <= i < len(prices)-1, prices[i] >= prices[i+1]. -/
  theorem spec_5 (prices : Slice Std.I64) (fee : Std.I64)
      (hlen_pos : 1 ≤ prices.val.length)
      (hlen_le : prices.val.length ≤ 50000)
      (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
        1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
      (hfee_lo : 0 ≤ fee.val)
      (hfee_hi : fee.val < 50000)
      (hmono : ∀ (i : Nat) (hi : i < prices.val.length - 1),
        (prices.val.get ⟨i + 1, by omega⟩).val ≤ (prices.val.get ⟨i, by omega⟩).val) :
      ∀ r : Std.I64, max_profit prices fee = ok r → r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (prices : Slice Std.I64) (fee : Std.I64)
        (hlen_pos : 1 ≤ prices.val.length)
        (hlen_le : prices.val.length ≤ 50000)
        (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
          1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
        (hfee_lo : 0 ≤ fee.val)
        (hfee_hi : fee.val < 50000)
        (hmono : ∀ (i : Nat) (hi : i < prices.val.length - 1),
          (prices.val.get ⟨i + 1, by omega⟩).val ≤ (prices.val.get ⟨i, by omega⟩).val), ∀ r : Std.I64, max_profit prices fee = ok r → r.val = 0) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: len(prices) >= 1 and len(prices) <= 50000; for every i with 0 <= i < len(prices), 1 <= prices[i] < 50000; 0 <= fee < 50000; let maxP = max_{0 <= i < len(prices)} prices[i] and minP = min_{0 <= i < len(prices)} prices[i]; fee >= maxP - minP. -/
  theorem spec_6 (prices : Slice Std.I64) (fee : Std.I64)
      (hlen_pos : 1 ≤ prices.val.length)
      (hlen_le : prices.val.length ≤ 50000)
      (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
        1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
      (hfee_lo : 0 ≤ fee.val)
      (hfee_hi : fee.val < 50000)
      (hgap : maxPrice (prices.val.map (fun x => x.val)) -
        minPrice (prices.val.map (fun x => x.val)) ≤ fee.val) :
      ∃ r : Std.I64, max_profit prices fee = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (prices : Slice Std.I64) (fee : Std.I64)
        (hlen_pos : 1 ≤ prices.val.length)
        (hlen_le : prices.val.length ≤ 50000)
        (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
          1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
        (hfee_lo : 0 ≤ fee.val)
        (hfee_hi : fee.val < 50000)
        (hgap : maxPrice (prices.val.map (fun x => x.val)) -
          minPrice (prices.val.map (fun x => x.val)) ≤ fee.val), ∃ r : Std.I64, max_profit prices fee = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r and r = sum_{i=0}^{len(prices)-2} max(0, prices[i+1] - prices[i]), where the empty sum is 0 when len(prices)=1.
    Preconditions: len(prices) >= 1 and len(prices) <= 50000; for every i with 0 <= i < len(prices), 1 <= prices[i] < 50000; fee = 0. -/
  theorem spec_7 (prices : Slice Std.I64) (fee : Std.I64)
      (hlen_pos : 1 ≤ prices.val.length)
      (hlen_le : prices.val.length ≤ 50000)
      (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
        1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
      (hfee : fee.val = 0) :
      ∃ r : Std.I64,
        max_profit prices fee = ok r ∧
        r.val = riseSum (prices.val.map (fun x => x.val)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (prices : Slice Std.I64) (fee : Std.I64)
        (hlen_pos : 1 ≤ prices.val.length)
        (hlen_le : prices.val.length ≤ 50000)
        (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
          1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
        (hfee : fee.val = 0), ∃ r : Std.I64,
          max_profit prices fee = ok r ∧
          r.val = riseSum (prices.val.map (fun x => x.val))) := by
    sorry

  /-- Whenever the function returns a result r, there exists a trade sequence T = ((b_1,s_1),...,(b_k,s_k)) with k >= 0, 0 <= b_j < s_j < len(prices) for all j, and s_j < b_{j+1} for all j < k, such that T has net profit r and every transaction (b_j,s_j) in T satisfies prices[s_j] - prices[b_j] - fee > 0.
    Preconditions: len(prices) >= 1 and len(prices) <= 50000; for every i with 0 <= i < len(prices), 1 <= prices[i] < 50000; 0 <= fee < 50000. -/
  theorem spec_8 (prices : Slice Std.I64) (fee : Std.I64)
      (hlen_pos : 1 ≤ prices.val.length)
      (hlen_le : prices.val.length ≤ 50000)
      (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
        1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
      (hfee_lo : 0 ≤ fee.val)
      (hfee_hi : fee.val < 50000) :
      ∀ r : Std.I64,
        max_profit prices fee = ok r →
        ∃ T : List Trade,
          IsTradeSeq prices.val.length T ∧
          r.val = netProfit (prices.val.map (fun x => x.val)) fee.val T ∧
          (∀ t ∈ T,
            0 < priceAt (prices.val.map (fun x => x.val)) t.sell -
              priceAt (prices.val.map (fun x => x.val)) t.buy - fee.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (prices : Slice Std.I64) (fee : Std.I64)
        (hlen_pos : 1 ≤ prices.val.length)
        (hlen_le : prices.val.length ≤ 50000)
        (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
          1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
        (hfee_lo : 0 ≤ fee.val)
        (hfee_hi : fee.val < 50000), ∀ r : Std.I64,
          max_profit prices fee = ok r →
          ∃ T : List Trade,
            IsTradeSeq prices.val.length T ∧
            r.val = netProfit (prices.val.map (fun x => x.val)) fee.val T ∧
            (∀ t ∈ T,
              0 < priceAt (prices.val.map (fun x => x.val)) t.sell -
                priceAt (prices.val.map (fun x => x.val)) t.buy - fee.val)) := by
    sorry

  /-- Whenever the function returns a result r, for every b and s with 0 <= b < s < len(prices), r >= max(0, prices[s] - prices[b] - fee).
    Preconditions: len(prices) >= 1 and len(prices) <= 50000; for every i with 0 <= i < len(prices), 1 <= prices[i] < 50000; 0 <= fee < 50000. -/
  theorem spec_9 (prices : Slice Std.I64) (fee : Std.I64)
      (hlen_pos : 1 ≤ prices.val.length)
      (hlen_le : prices.val.length ≤ 50000)
      (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
        1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
      (hfee_lo : 0 ≤ fee.val)
      (hfee_hi : fee.val < 50000) :
      ∀ r : Std.I64,
        max_profit prices fee = ok r →
        ∀ (b s : Nat) (hb : b < s) (hs : s < prices.val.length),
          max 0 ((prices.val.get ⟨s, hs⟩).val - (prices.val.get ⟨b, Nat.lt_trans hb hs⟩).val -
            fee.val) ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (prices : Slice Std.I64) (fee : Std.I64)
        (hlen_pos : 1 ≤ prices.val.length)
        (hlen_le : prices.val.length ≤ 50000)
        (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
          1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
        (hfee_lo : 0 ≤ fee.val)
        (hfee_hi : fee.val < 50000), ∀ r : Std.I64,
          max_profit prices fee = ok r →
          ∀ (b s : Nat) (hb : b < s) (hs : s < prices.val.length),
            max 0 ((prices.val.get ⟨s, hs⟩).val - (prices.val.get ⟨b, Nat.lt_trans hb hs⟩).val -
              fee.val) ≤ r.val) := by
    sorry

  /-- For every pair fee1, fee2 with 0 <= fee1 <= fee2 < 50000, if max_profit(prices, fee1) returns r1 and max_profit(prices, fee2) returns r2, then r2 <= r1.
    Preconditions: len(prices) >= 1 and len(prices) <= 50000; for every i with 0 <= i < len(prices), 1 <= prices[i] < 50000; for every pair of integers fee1, fee2 with 0 <= fee1 <= fee2 < 50000. -/
  theorem spec_10 (prices : Slice Std.I64)
      (hlen_pos : 1 ≤ prices.val.length)
      (hlen_le : prices.val.length ≤ 50000)
      (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
        1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000) :
      ∀ (fee1 fee2 : Std.I64),
        0 ≤ fee1.val → fee1.val ≤ fee2.val → fee2.val < 50000 →
        ∀ (r1 r2 : Std.I64),
          max_profit prices fee1 = ok r1 →
          max_profit prices fee2 = ok r2 →
          r2.val ≤ r1.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (hlen_pos : 1 ≤ prices.val.length)
        (hlen_le : prices.val.length ≤ 50000)
        (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
          1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000), ∀ (fee1 fee2 : Std.I64),
          0 ≤ fee1.val → fee1.val ≤ fee2.val → fee2.val < 50000 →
          ∀ (r1 r2 : Std.I64),
            max_profit prices fee1 = ok r1 →
            max_profit prices fee2 = ok r2 →
            r2.val ≤ r1.val) := by
    sorry

  /-- Let q be the slice of the same length as prices with q[i] = prices[i] + c for every i. If max_profit(prices, fee) returns r and max_profit(q, fee) returns r', then r = r'.
    Preconditions: len(prices) >= 1 and len(prices) <= 50000; for every i with 0 <= i < len(prices), 1 <= prices[i] < 50000; 0 <= fee < 50000; c is an integer such that for every i with 0 <= i < len(prices), 1 <= prices[i] + c < 50000. -/
  theorem spec_11 (prices : Slice Std.I64) (fee : Std.I64) (c : Int)
      (hlen_pos : 1 ≤ prices.val.length)
      (hlen_le : prices.val.length ≤ 50000)
      (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
        1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
      (hfee_lo : 0 ≤ fee.val)
      (hfee_hi : fee.val < 50000)
      (hshift : ∀ (i : Nat) (hi : i < prices.val.length),
        1 ≤ (prices.val.get ⟨i, hi⟩).val + c ∧ (prices.val.get ⟨i, hi⟩).val + c < 50000) :
      ∀ (q : Slice Std.I64) (hq : q.val.length = prices.val.length),
        (∀ (i : Nat) (hi : i < q.val.length),
          (q.val.get ⟨i, hi⟩).val = (prices.val.get ⟨i, by omega⟩).val + c) →
        ∀ (r r' : Std.I64),
          max_profit prices fee = ok r →
          max_profit q fee = ok r' →
          r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (prices : Slice Std.I64) (fee : Std.I64) (c : Int)
        (hlen_pos : 1 ≤ prices.val.length)
        (hlen_le : prices.val.length ≤ 50000)
        (hprices : ∀ (i : Nat) (hi : i < prices.val.length),
          1 ≤ (prices.val.get ⟨i, hi⟩).val ∧ (prices.val.get ⟨i, hi⟩).val < 50000)
        (hfee_lo : 0 ≤ fee.val)
        (hfee_hi : fee.val < 50000)
        (hshift : ∀ (i : Nat) (hi : i < prices.val.length),
          1 ≤ (prices.val.get ⟨i, hi⟩).val + c ∧ (prices.val.get ⟨i, hi⟩).val + c < 50000), ∀ (q : Slice Std.I64) (hq : q.val.length = prices.val.length),
          (∀ (i : Nat) (hi : i < q.val.length),
            (q.val.get ⟨i, hi⟩).val = (prices.val.get ⟨i, by omega⟩).val + c) →
          ∀ (r r' : Std.I64),
            max_profit prices fee = ok r →
            max_profit q fee = ok r' →
            r.val = r'.val) := by
    sorry

  end AegisSpec.MaxProfit
