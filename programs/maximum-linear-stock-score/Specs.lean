import Aegis.MaxScore.Code.Funs

/-!
# Specifications of `Aegis.MaxScore.max_score`

LeetCode problem `maximum-linear-stock-score`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxScore

  def keyOf (p : Std.I64 × ℕ) : ℤ := p.1.val - (p.2 : ℤ)

  def indexed (prices : Slice Std.I64) : List (Std.I64 × ℕ) := prices.val.zipIdx 0

  def Occurs (prices : Slice Std.I64) (c : ℤ) : Prop := ∃ p ∈ indexed prices, keyOf p = c

  def groupSum (prices : Slice Std.I64) (c : ℤ) : ℤ :=
    (((indexed prices).filter (fun p => keyOf p = c)).map (fun p => p.1.val)).sum

  def complSum (prices : Slice Std.I64) (c : ℤ) : ℤ :=
    (((indexed prices).filter (fun p => keyOf p ≠ c)).map (fun p => p.1.val)).sum

  def totalSum (prices : Slice Std.I64) : ℤ := (prices.val.map (fun x => x.val)).sum

  def maxGroupSum (prices : Slice Std.I64) : ℤ :=
    (((indexed prices).map (fun p => groupSum prices (keyOf p))).max?).getD 0

  def priceAt (prices : Slice Std.I64) (i : ℕ) : ℤ := (prices.val.getD i 0#i64).val

  def sumAt (prices : Slice Std.I64) (l : List ℕ) : ℤ := (l.map (priceAt prices)).sum

  def Linear (prices : Slice Std.I64) : List ℕ → Prop
    | [] => True
    | [_] => True
    | i :: j :: rest =>
        priceAt prices j - priceAt prices i = (j : ℤ) - (i : ℤ) ∧ Linear prices (j :: rest)

  /-- The function returns a result r and r = max_{0 <= i < n} S(prices[i] - i), where for any integer c, S(c) = sum_{0 <= j < n and prices[j] - j = c} prices[j].
    Preconditions: Let n = len(prices). The input satisfies the problem constraints: 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= prices[i] <= 1000000000. -/
  theorem spec_1 (prices : Slice Std.I64)
      (h_pos : 1 ≤ prices.val.length) (h_len : prices.val.length ≤ 100000)
      (h_bounds : ∀ (i : ℕ) (hi : i < prices.val.length),
        1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000000000) :
      ∃ r, Aegis.MaxScore.max_score prices = ok r ∧ r.val = maxGroupSum prices := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (h_pos : 1 ≤ prices.val.length) (h_len : prices.val.length ≤ 100000)
        (h_bounds : ∀ (i : ℕ) (hi : i < prices.val.length),
          1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000000000), ∃ r, Aegis.MaxScore.max_score prices = ok r ∧ r.val = maxGroupSum prices) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: Let n = len(prices). The input satisfies the problem constraints: 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= prices[i] <= 1000000000. -/
  theorem spec_2 (prices : Slice Std.I64)
      (h_pos : 1 ≤ prices.val.length) (h_len : prices.val.length ≤ 100000)
      (h_bounds : ∀ (i : ℕ) (hi : i < prices.val.length),
        1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000000000) :
      ∃ r, Aegis.MaxScore.max_score prices = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (h_pos : 1 ≤ prices.val.length) (h_len : prices.val.length ≤ 100000)
        (h_bounds : ∀ (i : ℕ) (hi : i < prices.val.length),
          1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000000000), ∃ r, Aegis.MaxScore.max_score prices = ok r) := by
    sorry

  /-- The function returns a result r and r <= sum_{i=0}^{n-1} prices[i].
    Preconditions: Let n = len(prices). The input satisfies the problem constraints: 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= prices[i] <= 1000000000. -/
  theorem spec_3 (prices : Slice Std.I64)
      (h_pos : 1 ≤ prices.val.length) (h_len : prices.val.length ≤ 100000)
      (h_bounds : ∀ (i : ℕ) (hi : i < prices.val.length),
        1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000000000) :
      ∃ r, Aegis.MaxScore.max_score prices = ok r ∧ r.val ≤ totalSum prices := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (h_pos : 1 ≤ prices.val.length) (h_len : prices.val.length ≤ 100000)
        (h_bounds : ∀ (i : ℕ) (hi : i < prices.val.length),
          1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000000000), ∃ r, Aegis.MaxScore.max_score prices = ok r ∧ r.val ≤ totalSum prices) := by
    sorry

  /-- The function returns a result r and, for every integer c such that I_c = { i | 0 <= i < n and prices[i] - i = c } is nonempty, r >= sum_{i in I_c} prices[i].
    Preconditions: Let n = len(prices). The input satisfies the problem constraints: 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= prices[i] <= 1000000000. -/
  theorem spec_4 (prices : Slice Std.I64)
      (h_pos : 1 ≤ prices.val.length) (h_len : prices.val.length ≤ 100000)
      (h_bounds : ∀ (i : ℕ) (hi : i < prices.val.length),
        1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000000000) :
      ∃ r, Aegis.MaxScore.max_score prices = ok r ∧
        ∀ c : ℤ, Occurs prices c → groupSum prices c ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (h_pos : 1 ≤ prices.val.length) (h_len : prices.val.length ≤ 100000)
        (h_bounds : ∀ (i : ℕ) (hi : i < prices.val.length),
          1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000000000), ∃ r, Aegis.MaxScore.max_score prices = ok r ∧
          ∀ c : ℤ, Occurs prices c → groupSum prices c ≤ r.val) := by
    sorry

  /-- The function returns a result r and there exists an integer c such that I_c = { i | 0 <= i < n and prices[i] - i = c } is nonempty and r = sum_{i in I_c} prices[i].
    Preconditions: Let n = len(prices). The input satisfies the problem constraints: 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= prices[i] <= 1000000000. -/
  theorem spec_5 (prices : Slice Std.I64)
      (h_pos : 1 ≤ prices.val.length) (h_len : prices.val.length ≤ 100000)
      (h_bounds : ∀ (i : ℕ) (hi : i < prices.val.length),
        1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000000000) :
      ∃ r, Aegis.MaxScore.max_score prices = ok r ∧
        ∃ c : ℤ, Occurs prices c ∧ r.val = groupSum prices c := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (h_pos : 1 ≤ prices.val.length) (h_len : prices.val.length ≤ 100000)
        (h_bounds : ∀ (i : ℕ) (hi : i < prices.val.length),
          1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000000000), ∃ r, Aegis.MaxScore.max_score prices = ok r ∧
          ∃ c : ℤ, Occurs prices c ∧ r.val = groupSum prices c) := by
    sorry

  /-- The function returns a result r and for every nonempty list of indices i_0 < i_1 < ... < i_{k-1} with 0 <= i_0 and i_{k-1} < n that is linear, meaning prices[i_j] - prices[i_{j-1}] = i_j - i_{j-1} for every 1 <= j < k, one has sum_{j=0}^{k-1} prices[i_j] <= r.
    Preconditions: Let n = len(prices). The input satisfies the problem constraints: 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= prices[i] <= 1000000000. -/
  theorem spec_6 (prices : Slice Std.I64)
      (h_pos : 1 ≤ prices.val.length) (h_len : prices.val.length ≤ 100000)
      (h_bounds : ∀ (i : ℕ) (hi : i < prices.val.length),
        1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000000000) :
      ∃ r, Aegis.MaxScore.max_score prices = ok r ∧
        ∀ (l : List ℕ), l ≠ [] → (∀ i ∈ l, i < prices.val.length) →
          List.Pairwise (· < ·) l → Linear prices l → sumAt prices l ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (h_pos : 1 ≤ prices.val.length) (h_len : prices.val.length ≤ 100000)
        (h_bounds : ∀ (i : ℕ) (hi : i < prices.val.length),
          1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000000000), ∃ r, Aegis.MaxScore.max_score prices = ok r ∧
          ∀ (l : List ℕ), l ≠ [] → (∀ i ∈ l, i < prices.val.length) →
            List.Pairwise (· < ·) l → Linear prices l → sumAt prices l ≤ r.val) := by
    sorry

  /-- The function returns a result r and, if there exists an integer c such that I_c = { i | 0 <= i < n and prices[i] - i = c } is nonempty and sum_{i in I_c} prices[i] > sum_{0 <= i < n, i not in I_c} prices[i], then r = sum_{i in I_c} prices[i].
    Preconditions: Let n = len(prices). The input satisfies the problem constraints: 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= prices[i] <= 1000000000. -/
  theorem spec_7 (prices : Slice Std.I64)
      (h_pos : 1 ≤ prices.val.length) (h_len : prices.val.length ≤ 100000)
      (h_bounds : ∀ (i : ℕ) (hi : i < prices.val.length),
        1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000000000) :
      ∃ r, Aegis.MaxScore.max_score prices = ok r ∧
        ∀ c : ℤ, Occurs prices c → groupSum prices c > complSum prices c →
          r.val = groupSum prices c := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (prices : Slice Std.I64)
        (h_pos : 1 ≤ prices.val.length) (h_len : prices.val.length ≤ 100000)
        (h_bounds : ∀ (i : ℕ) (hi : i < prices.val.length),
          1 ≤ (prices.val[i]).val ∧ (prices.val[i]).val ≤ 1000000000), ∃ r, Aegis.MaxScore.max_score prices = ok r ∧
          ∀ c : ℤ, Occurs prices c → groupSum prices c > complSum prices c →
            r.val = groupSum prices c) := by
    sorry

  end AegisSpec.MaxScore
