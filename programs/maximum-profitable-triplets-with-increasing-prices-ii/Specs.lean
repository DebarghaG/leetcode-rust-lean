import Aegis.MaxProfit.Code.Funs

/-!
# Specifications of `Aegis.MaxProfit.max_profit`

LeetCode problem `maximum-profitable-triplets-with-increasing-prices-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxProfit

  namespace AegisSpec.MaxProfit

  def contents (s : Slice Std.I64) : List Int := s.val.map (fun x => x.val)

  def entry (s : Slice Std.I64) (i : Nat) : Int := (contents s).getD i 0

  def increasingTriple (prices : Slice Std.I64) (i j k : Nat) : Prop :=
    i < j ∧ j < k ∧ k < prices.val.length ∧
      entry prices i < entry prices j ∧ entry prices j < entry prices k

  def hasIncreasingTriple (prices : Slice Std.I64) : Prop :=
    ∃ i j k, increasingTriple prices i j k

  def tripleSums (prices profits : Slice Std.I64) : Set Int :=
    {x | ∃ i j k, increasingTriple prices i j k ∧
        x = entry profits i + entry profits j + entry profits k}

  def top3Sum (l : List Int) : Int :=
    match l.insertionSort (· ≥ ·) with
    | a :: b :: c :: _ => a + b + c
    | _ => 0

  def top3Profits (profits : Slice Std.I64) : Int := top3Sum (contents profits)

  /-- The function returns a result r, and if S = {profits[i] + profits[j] + profits[k] | 0 <= i < j < k < n and prices[i] < prices[j] < prices[k]} is nonempty, then r = max(S) and r != -1; if S is empty, then r = -1.
    Preconditions: Let n = len(prices). The inputs satisfy len(prices) = len(profits) = n, 3 <= n <= 50000, and for every i with 0 <= i < n, 1 <= prices[i] <= 5000 and 1 <= profits[i] <= 1000000. -/
  theorem spec_1 (prices profits : Slice Std.I64)
      (hlen : prices.val.length = profits.val.length)
      (hn_lo : 3 ≤ prices.val.length) (hn_hi : prices.val.length ≤ 50000)
      (hprices : ∀ i, i < prices.val.length → 1 ≤ entry prices i ∧ entry prices i ≤ 5000)
      (hprofits : ∀ i, i < profits.val.length → 1 ≤ entry profits i ∧ entry profits i ≤ 1000000) :
      ∃ r, max_profit prices profits = ok r ∧
        ((tripleSums prices profits).Nonempty →
          r.val ≠ -1 ∧ r.val ∈ tripleSums prices profits ∧
            ∀ x, x ∈ tripleSums prices profits → x ≤ r.val) ∧
        (¬ (tripleSums prices profits).Nonempty → r.val = (-1 : Int)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (prices profits : Slice Std.I64)
        (hlen : prices.val.length = profits.val.length)
        (hn_lo : 3 ≤ prices.val.length) (hn_hi : prices.val.length ≤ 50000)
        (hprices : ∀ i, i < prices.val.length → 1 ≤ entry prices i ∧ entry prices i ≤ 5000)
        (hprofits : ∀ i, i < profits.val.length → 1 ≤ entry profits i ∧ entry profits i ≤ 1000000), ∃ r, max_profit prices profits = ok r ∧
          ((tripleSums prices profits).Nonempty →
            r.val ≠ -1 ∧ r.val ∈ tripleSums prices profits ∧
              ∀ x, x ∈ tripleSums prices profits → x ≤ r.val) ∧
          (¬ (tripleSums prices profits).Nonempty → r.val = (-1 : Int))) := by
    sorry

  /-- The function returns a result r; it does not fail, overflow, go out of bounds, or panic.
    Preconditions: Let n = len(prices). The inputs satisfy len(prices) = len(profits) = n, 3 <= n <= 50000, and for every i with 0 <= i < n, 1 <= prices[i] <= 5000 and 1 <= profits[i] <= 1000000. -/
  theorem spec_2 (prices profits : Slice Std.I64)
      (hlen : prices.val.length = profits.val.length)
      (hn_lo : 3 ≤ prices.val.length) (hn_hi : prices.val.length ≤ 50000)
      (hprices : ∀ i, i < prices.val.length → 1 ≤ entry prices i ∧ entry prices i ≤ 5000)
      (hprofits : ∀ i, i < profits.val.length → 1 ≤ entry profits i ∧ entry profits i ≤ 1000000) :
      ∃ r, max_profit prices profits = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (prices profits : Slice Std.I64)
        (hlen : prices.val.length = profits.val.length)
        (hn_lo : 3 ≤ prices.val.length) (hn_hi : prices.val.length ≤ 50000)
        (hprices : ∀ i, i < prices.val.length → 1 ≤ entry prices i ∧ entry prices i ≤ 5000)
        (hprofits : ∀ i, i < profits.val.length → 1 ≤ entry profits i ∧ entry profits i ≤ 1000000), ∃ r, max_profit prices profits = ok r) := by
    sorry

  /-- The function returns a result r, and r != -1 if and only if there exist indices i, j, k with 0 <= i < j < k < n and prices[i] < prices[j] < prices[k].
    Preconditions: Let n = len(prices). The inputs satisfy len(prices) = len(profits) = n, 3 <= n <= 50000, and for every i with 0 <= i < n, 1 <= prices[i] <= 5000 and 1 <= profits[i] <= 1000000. -/
  theorem spec_3 (prices profits : Slice Std.I64)
      (hlen : prices.val.length = profits.val.length)
      (hn_lo : 3 ≤ prices.val.length) (hn_hi : prices.val.length ≤ 50000)
      (hprices : ∀ i, i < prices.val.length → 1 ≤ entry prices i ∧ entry prices i ≤ 5000)
      (hprofits : ∀ i, i < profits.val.length → 1 ≤ entry profits i ∧ entry profits i ≤ 1000000) :
      ∃ r, max_profit prices profits = ok r ∧ (r.val ≠ -1 ↔ hasIncreasingTriple prices) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (prices profits : Slice Std.I64)
        (hlen : prices.val.length = profits.val.length)
        (hn_lo : 3 ≤ prices.val.length) (hn_hi : prices.val.length ≤ 50000)
        (hprices : ∀ i, i < prices.val.length → 1 ≤ entry prices i ∧ entry prices i ≤ 5000)
        (hprofits : ∀ i, i < profits.val.length → 1 ≤ entry profits i ∧ entry profits i ≤ 1000000), ∃ r, max_profit prices profits = ok r ∧ (r.val ≠ -1 ↔ hasIncreasingTriple prices)) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, there exist indices i, j, k such that 0 <= i < j < k < n, prices[i] < prices[j] < prices[k], and r = profits[i] + profits[j] + profits[k].
    Preconditions: Let n = len(prices). The inputs satisfy len(prices) = len(profits) = n, 3 <= n <= 50000, and for every i with 0 <= i < n, 1 <= prices[i] <= 5000 and 1 <= profits[i] <= 1000000. -/
  theorem spec_4 (prices profits : Slice Std.I64)
      (hlen : prices.val.length = profits.val.length)
      (hn_lo : 3 ≤ prices.val.length) (hn_hi : prices.val.length ≤ 50000)
      (hprices : ∀ i, i < prices.val.length → 1 ≤ entry prices i ∧ entry prices i ≤ 5000)
      (hprofits : ∀ i, i < profits.val.length → 1 ≤ entry profits i ∧ entry profits i ≤ 1000000)
      (r : Std.I64) (hres : max_profit prices profits = ok r) (hne : r.val ≠ -1) :
      ∃ i j k, increasingTriple prices i j k ∧
        r.val = entry profits i + entry profits j + entry profits k := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (prices profits : Slice Std.I64)
        (hlen : prices.val.length = profits.val.length)
        (hn_lo : 3 ≤ prices.val.length) (hn_hi : prices.val.length ≤ 50000)
        (hprices : ∀ i, i < prices.val.length → 1 ≤ entry prices i ∧ entry prices i ≤ 5000)
        (hprofits : ∀ i, i < profits.val.length → 1 ≤ entry profits i ∧ entry profits i ≤ 1000000)
        (r : Std.I64) (hres : max_profit prices profits = ok r) (hne : r.val ≠ -1), ∃ i j k, increasingTriple prices i j k ∧
          r.val = entry profits i + entry profits j + entry profits k) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, for every choice of indices i, j, k with 0 <= i < j < k < n and prices[i] < prices[j] < prices[k], we have profits[i] + profits[j] + profits[k] <= r.
    Preconditions: Let n = len(prices). The inputs satisfy len(prices) = len(profits) = n, 3 <= n <= 50000, and for every i with 0 <= i < n, 1 <= prices[i] <= 5000 and 1 <= profits[i] <= 1000000. -/
  theorem spec_5 (prices profits : Slice Std.I64)
      (hlen : prices.val.length = profits.val.length)
      (hn_lo : 3 ≤ prices.val.length) (hn_hi : prices.val.length ≤ 50000)
      (hprices : ∀ i, i < prices.val.length → 1 ≤ entry prices i ∧ entry prices i ≤ 5000)
      (hprofits : ∀ i, i < profits.val.length → 1 ≤ entry profits i ∧ entry profits i ≤ 1000000)
      (r : Std.I64) (hres : max_profit prices profits = ok r) (hne : r.val ≠ -1) :
      ∀ i j k, increasingTriple prices i j k →
        entry profits i + entry profits j + entry profits k ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (prices profits : Slice Std.I64)
        (hlen : prices.val.length = profits.val.length)
        (hn_lo : 3 ≤ prices.val.length) (hn_hi : prices.val.length ≤ 50000)
        (hprices : ∀ i, i < prices.val.length → 1 ≤ entry prices i ∧ entry prices i ≤ 5000)
        (hprofits : ∀ i, i < profits.val.length → 1 ≤ entry profits i ∧ entry profits i ≤ 1000000)
        (r : Std.I64) (hres : max_profit prices profits = ok r) (hne : r.val ≠ -1), ∀ i j k, increasingTriple prices i j k →
          entry profits i + entry profits j + entry profits k ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, 3 <= r <= P, where P is the sum of the three largest entries of profits, counting multiplicities.
    Preconditions: Let n = len(prices). The inputs satisfy len(prices) = len(profits) = n, 3 <= n <= 50000, and for every i with 0 <= i < n, 1 <= prices[i] <= 5000 and 1 <= profits[i] <= 1000000. -/
  theorem spec_6 (prices profits : Slice Std.I64)
      (hlen : prices.val.length = profits.val.length)
      (hn_lo : 3 ≤ prices.val.length) (hn_hi : prices.val.length ≤ 50000)
      (hprices : ∀ i, i < prices.val.length → 1 ≤ entry prices i ∧ entry prices i ≤ 5000)
      (hprofits : ∀ i, i < profits.val.length → 1 ≤ entry profits i ∧ entry profits i ≤ 1000000)
      (r : Std.I64) (hres : max_profit prices profits = ok r) (hne : r.val ≠ -1) :
      3 ≤ r.val ∧ r.val ≤ top3Profits profits := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (prices profits : Slice Std.I64)
        (hlen : prices.val.length = profits.val.length)
        (hn_lo : 3 ≤ prices.val.length) (hn_hi : prices.val.length ≤ 50000)
        (hprices : ∀ i, i < prices.val.length → 1 ≤ entry prices i ∧ entry prices i ≤ 5000)
        (hprofits : ∀ i, i < profits.val.length → 1 ≤ entry profits i ∧ entry profits i ≤ 1000000)
        (r : Std.I64) (hres : max_profit prices profits = ok r) (hne : r.val ≠ -1), 3 ≤ r.val ∧ r.val ≤ top3Profits profits) := by
    sorry

  /-- The function returns a result r for (prices, profits) and a result r' for (prices', profits), and r = r'.
    Preconditions: Let n = len(prices). The inputs satisfy len(prices) = len(profits) = n, 3 <= n <= 50000, and for every i with 0 <= i < n, 1 <= prices[i] <= 5000 and 1 <= profits[i] <= 1000000. In addition, let c be an integer such that 1 <= prices[i] + c <= 5000 for every i with 0 <= i < n, and let prices' be the slice of length n with prices'[i] = prices[i] + c for all i. -/
  theorem spec_7 (prices prices' profits : Slice Std.I64) (c : Int)
      (hlen : prices.val.length = profits.val.length)
      (hn_lo : 3 ≤ prices.val.length) (hn_hi : prices.val.length ≤ 50000)
      (hprices : ∀ i, i < prices.val.length → 1 ≤ entry prices i ∧ entry prices i ≤ 5000)
      (hprofits : ∀ i, i < profits.val.length → 1 ≤ entry profits i ∧ entry profits i ≤ 1000000)
      (hc_lo : ∀ i, i < prices.val.length → 1 ≤ entry prices i + c)
      (hc_hi : ∀ i, i < prices.val.length → entry prices i + c ≤ 5000)
      (hprices' : contents prices' = (contents prices).map (fun x => x + c)) :
      ∃ r r', max_profit prices profits = ok r ∧ max_profit prices' profits = ok r' ∧ r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (prices prices' profits : Slice Std.I64) (c : Int)
        (hlen : prices.val.length = profits.val.length)
        (hn_lo : 3 ≤ prices.val.length) (hn_hi : prices.val.length ≤ 50000)
        (hprices : ∀ i, i < prices.val.length → 1 ≤ entry prices i ∧ entry prices i ≤ 5000)
        (hprofits : ∀ i, i < profits.val.length → 1 ≤ entry profits i ∧ entry profits i ≤ 1000000)
        (hc_lo : ∀ i, i < prices.val.length → 1 ≤ entry prices i + c)
        (hc_hi : ∀ i, i < prices.val.length → entry prices i + c ≤ 5000)
        (hprices' : contents prices' = (contents prices).map (fun x => x + c)), ∃ r r', max_profit prices profits = ok r ∧ max_profit prices' profits = ok r' ∧ r = r') := by
    sorry

  end AegisSpec.MaxProfit
