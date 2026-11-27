import Aegis.BuyChoco.Code.Funs

/-!
# Specifications of `Aegis.BuyChoco.buy_choco`

LeetCode problem `buy-two-chocolates`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.BuyChoco

  def vals (prices : Slice Std.I64) : List ℤ := prices.val.map (fun p => p.val)

  def getVal (prices : Slice Std.I64) (i : ℕ) : ℤ := (vals prices)[i]!

  def pairSums : List ℤ → List ℤ
    | [] => []
    | x :: xs => xs.map (fun y => x + y) ++ pairSums xs

  def pairSumMin (l : List ℤ) : ℤ :=
    match pairSums l with
    | [] => 0
    | x :: xs => xs.foldr min x

  def IsReordering (l l' : List ℤ) : Prop := l.Perm l'

  /-- Let n = len(prices), and let s be the minimum of prices[i] + prices[j] over all integer pairs (i, j) with 0 <= i < j < n. The function returns a result r and r = (if s <= money then money - s else money).
    Preconditions: prices is a slice of 64-bit integers with n = len(prices) satisfying 2 <= n <= 50; for every i with 0 <= i < n, 1 <= prices[i] <= 100; money is a 64-bit integer with 1 <= money <= 100. -/
  theorem spec_1 (prices : Slice Std.I64) (money : Std.I64) (n : ℕ) (s : ℤ)
      (hlen : n = prices.val.length) (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
      (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100)
      (hs : s = pairSumMin (vals prices)) :
      ∃ r : Std.I64, Aegis.BuyChoco.buy_choco prices money = ok r ∧
        r.val = if s ≤ money.val then money.val - s else money.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (prices : Slice Std.I64) (money : Std.I64) (n : ℕ) (s : ℤ)
        (hlen : n = prices.val.length) (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
        (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
        (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100)
        (hs : s = pairSumMin (vals prices)), ∃ r : Std.I64, Aegis.BuyChoco.buy_choco prices money = ok r ∧
          r.val = if s ≤ money.val then money.val - s else money.val) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail due to overflow, out-of-bounds access, panic, or any other reason.
    Preconditions: prices is a slice of 64-bit integers with n = len(prices) satisfying 2 <= n <= 50; for every i with 0 <= i < n, 1 <= prices[i] <= 100; money is a 64-bit integer with 1 <= money <= 100. -/
  theorem spec_2 (prices : Slice Std.I64) (money : Std.I64) (n : ℕ)
      (hlen : n = prices.val.length) (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
      (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100) :
      ∃ r : Std.I64, Aegis.BuyChoco.buy_choco prices money = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (prices : Slice Std.I64) (money : Std.I64) (n : ℕ)
        (hlen : n = prices.val.length) (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
        (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
        (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100), ∃ r : Std.I64, Aegis.BuyChoco.buy_choco prices money = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= money.
    Preconditions: prices is a slice of 64-bit integers with n = len(prices) satisfying 2 <= n <= 50; for every i with 0 <= i < n, 1 <= prices[i] <= 100; money is a 64-bit integer with 1 <= money <= 100. -/
  theorem spec_3 (prices : Slice Std.I64) (money : Std.I64) (n : ℕ)
      (hlen : n = prices.val.length) (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
      (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100)
      (r : Std.I64) (hr : Aegis.BuyChoco.buy_choco prices money = ok r) :
      0 ≤ r.val ∧ r.val ≤ money.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (prices : Slice Std.I64) (money : Std.I64) (n : ℕ)
        (hlen : n = prices.val.length) (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
        (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
        (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100)
        (r : Std.I64) (hr : Aegis.BuyChoco.buy_choco prices money = ok r), 0 ≤ r.val ∧ r.val ≤ money.val) := by
    sorry

  /-- Whenever the function returns a result r and there exist indices i, j with 0 <= i < j < n and prices[i] + prices[j] <= money, then 0 <= r <= money - 2, and in particular r < money.
    Preconditions: prices is a slice of 64-bit integers with n = len(prices) satisfying 2 <= n <= 50; for every i with 0 <= i < n, 1 <= prices[i] <= 100; money is a 64-bit integer with 1 <= money <= 100. -/
  theorem spec_4 (prices : Slice Std.I64) (money : Std.I64) (n : ℕ)
      (hlen : n = prices.val.length) (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
      (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100)
      (r : Std.I64) (hr : Aegis.BuyChoco.buy_choco prices money = ok r)
      (hpair : ∃ i j, i < j ∧ j < n ∧ getVal prices i + getVal prices j ≤ money.val) :
      0 ≤ r.val ∧ r.val ≤ money.val - 2 ∧ r.val < money.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (prices : Slice Std.I64) (money : Std.I64) (n : ℕ)
        (hlen : n = prices.val.length) (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
        (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
        (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100)
        (r : Std.I64) (hr : Aegis.BuyChoco.buy_choco prices money = ok r)
        (hpair : ∃ i j, i < j ∧ j < n ∧ getVal prices i + getVal prices j ≤ money.val), 0 ≤ r.val ∧ r.val ≤ money.val - 2 ∧ r.val < money.val) := by
    sorry

  /-- Whenever the function returns a result r, the equality r = money holds if and only if for every pair of indices i, j with 0 <= i < j < n, prices[i] + prices[j] > money.
    Preconditions: prices is a slice of 64-bit integers with n = len(prices) satisfying 2 <= n <= 50; for every i with 0 <= i < n, 1 <= prices[i] <= 100; money is a 64-bit integer with 1 <= money <= 100. -/
  theorem spec_5 (prices : Slice Std.I64) (money : Std.I64) (n : ℕ)
      (hlen : n = prices.val.length) (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
      (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100)
      (r : Std.I64) (hr : Aegis.BuyChoco.buy_choco prices money = ok r) :
      (r.val = money.val ↔
        ∀ i j, i < j → j < n → money.val < getVal prices i + getVal prices j) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (prices : Slice Std.I64) (money : Std.I64) (n : ℕ)
        (hlen : n = prices.val.length) (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
        (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
        (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100)
        (r : Std.I64) (hr : Aegis.BuyChoco.buy_choco prices money = ok r), (r.val = money.val ↔
          ∀ i j, i < j → j < n → money.val < getVal prices i + getVal prices j)) := by
    sorry

  /-- Whenever the function returns a result r with r < money, there exist indices i, j with 0 <= i < j < n such that prices[i] + prices[j] = money - r.
    Preconditions: prices is a slice of 64-bit integers with n = len(prices) satisfying 2 <= n <= 50; for every i with 0 <= i < n, 1 <= prices[i] <= 100; money is a 64-bit integer with 1 <= money <= 100. -/
  theorem spec_6 (prices : Slice Std.I64) (money : Std.I64) (n : ℕ)
      (hlen : n = prices.val.length) (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
      (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100)
      (r : Std.I64) (hr : Aegis.BuyChoco.buy_choco prices money = ok r)
      (hlt : r.val < money.val) :
      ∃ i j, i < j ∧ j < n ∧ getVal prices i + getVal prices j = money.val - r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (prices : Slice Std.I64) (money : Std.I64) (n : ℕ)
        (hlen : n = prices.val.length) (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
        (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
        (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100)
        (r : Std.I64) (hr : Aegis.BuyChoco.buy_choco prices money = ok r)
        (hlt : r.val < money.val), ∃ i j, i < j ∧ j < n ∧ getVal prices i + getVal prices j = money.val - r.val) := by
    sorry

  /-- Whenever the function returns a result r, every pair of indices i, j with 0 <= i < j < n satisfies prices[i] + prices[j] >= money - r.
    Preconditions: prices is a slice of 64-bit integers with n = len(prices) satisfying 2 <= n <= 50; for every i with 0 <= i < n, 1 <= prices[i] <= 100; money is a 64-bit integer with 1 <= money <= 100. -/
  theorem spec_7 (prices : Slice Std.I64) (money : Std.I64) (n : ℕ)
      (hlen : n = prices.val.length) (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
      (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100)
      (r : Std.I64) (hr : Aegis.BuyChoco.buy_choco prices money = ok r) :
      ∀ i j, i < j → j < n → money.val - r.val ≤ getVal prices i + getVal prices j := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (prices : Slice Std.I64) (money : Std.I64) (n : ℕ)
        (hlen : n = prices.val.length) (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
        (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
        (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100)
        (r : Std.I64) (hr : Aegis.BuyChoco.buy_choco prices money = ok r), ∀ i j, i < j → j < n → money.val - r.val ≤ getVal prices i + getVal prices j) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if there exist indices i, j with 0 <= i < j < n such that prices[i] + prices[j] = money, and for every pair of indices a, b with 0 <= a < b < n, prices[a] + prices[b] >= money.
    Preconditions: prices is a slice of 64-bit integers with n = len(prices) satisfying 2 <= n <= 50; for every i with 0 <= i < n, 1 <= prices[i] <= 100; money is a 64-bit integer with 1 <= money <= 100. -/
  theorem spec_8 (prices : Slice Std.I64) (money : Std.I64) (n : ℕ)
      (hlen : n = prices.val.length) (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
      (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100)
      (r : Std.I64) (hr : Aegis.BuyChoco.buy_choco prices money = ok r) :
      (r.val = 0 ↔
        (∃ i j, i < j ∧ j < n ∧ getVal prices i + getVal prices j = money.val) ∧
          (∀ a b, a < b → b < n → money.val ≤ getVal prices a + getVal prices b)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (prices : Slice Std.I64) (money : Std.I64) (n : ℕ)
        (hlen : n = prices.val.length) (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
        (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
        (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100)
        (r : Std.I64) (hr : Aegis.BuyChoco.buy_choco prices money = ok r), (r.val = 0 ↔
          (∃ i j, i < j ∧ j < n ∧ getVal prices i + getVal prices j = money.val) ∧
            (∀ a b, a < b → b < n → money.val ≤ getVal prices a + getVal prices b))) := by
    sorry

  /-- Whenever the function returns r on (prices, money) and returns r' on (prices', money), r = r'.
    Preconditions: prices and prices' are slices of 64-bit integers of the same length n with 2 <= n <= 50; every entry of prices and of prices' is between 1 and 100; prices' is a reordering (permutation) of the entries of prices; money is a 64-bit integer with 1 <= money <= 100. -/
  theorem spec_9 (prices prices' : Slice Std.I64) (money : Std.I64) (n : ℕ)
      (hlen : n = prices.val.length) (hlen' : n = prices'.val.length)
      (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
      (hbound' : ∀ i, i < n → 1 ≤ getVal prices' i ∧ getVal prices' i ≤ 100)
      (hperm : IsReordering (vals prices) (vals prices'))
      (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100)
      (r r' : Std.I64) (hr : Aegis.BuyChoco.buy_choco prices money = ok r)
      (hr' : Aegis.BuyChoco.buy_choco prices' money = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (prices prices' : Slice Std.I64) (money : Std.I64) (n : ℕ)
        (hlen : n = prices.val.length) (hlen' : n = prices'.val.length)
        (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
        (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
        (hbound' : ∀ i, i < n → 1 ≤ getVal prices' i ∧ getVal prices' i ≤ 100)
        (hperm : IsReordering (vals prices) (vals prices'))
        (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100)
        (r r' : Std.I64) (hr : Aegis.BuyChoco.buy_choco prices money = ok r)
        (hr' : Aegis.BuyChoco.buy_choco prices' money = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever the function returns r on (prices, money) and returns r' on (prices', money), r' <= r.
    Preconditions: prices and prices' are slices of 64-bit integers of the same length n with 2 <= n <= 50; for every i with 0 <= i < n, 1 <= prices[i] <= 100 and 1 <= prices'[i] <= 100; for every i with 0 <= i < n, prices'[i] >= prices[i]; money is a 64-bit integer with 1 <= money <= 100; each of prices and prices' has at least one pair of distinct indices whose sum is at most money. -/
  theorem spec_10 (prices prices' : Slice Std.I64) (money : Std.I64) (n : ℕ)
      (hlen : n = prices.val.length) (hlen' : n = prices'.val.length)
      (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
      (hbound' : ∀ i, i < n → 1 ≤ getVal prices' i ∧ getVal prices' i ≤ 100)
      (hmono : ∀ i, i < n → getVal prices i ≤ getVal prices' i)
      (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100)
      (hpair : ∃ i j, i < j ∧ j < n ∧ getVal prices i + getVal prices j ≤ money.val)
      (hpair' : ∃ i j, i < j ∧ j < n ∧ getVal prices' i + getVal prices' j ≤ money.val)
      (r r' : Std.I64) (hr : Aegis.BuyChoco.buy_choco prices money = ok r)
      (hr' : Aegis.BuyChoco.buy_choco prices' money = ok r') :
      r'.val ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (prices prices' : Slice Std.I64) (money : Std.I64) (n : ℕ)
        (hlen : n = prices.val.length) (hlen' : n = prices'.val.length)
        (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
        (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
        (hbound' : ∀ i, i < n → 1 ≤ getVal prices' i ∧ getVal prices' i ≤ 100)
        (hmono : ∀ i, i < n → getVal prices i ≤ getVal prices' i)
        (hmoney1 : 1 ≤ money.val) (hmoney100 : money.val ≤ 100)
        (hpair : ∃ i j, i < j ∧ j < n ∧ getVal prices i + getVal prices j ≤ money.val)
        (hpair' : ∃ i j, i < j ∧ j < n ∧ getVal prices' i + getVal prices' j ≤ money.val)
        (r r' : Std.I64) (hr : Aegis.BuyChoco.buy_choco prices money = ok r)
        (hr' : Aegis.BuyChoco.buy_choco prices' money = ok r'), r'.val ≤ r.val) := by
    sorry

  /-- Let s be the minimum of prices[i] + prices[j] over all 0 <= i < j < n. If s <= money1, and the function returns r1 on (prices, money1) and r2 on (prices, money2), then r2 = r1 + d.
    Preconditions: prices is a slice of 64-bit integers with n = len(prices) satisfying 2 <= n <= 50; for every i with 0 <= i < n, 1 <= prices[i] <= 100; money1 and money2 are 64-bit integers with 1 <= money1 <= money2 <= 100, and d = money2 - money1. -/
  theorem spec_11 (prices : Slice Std.I64) (money1 money2 : Std.I64) (n : ℕ) (d : ℤ)
      (hlen : n = prices.val.length) (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
      (hmoney1 : 1 ≤ money1.val) (hmoney12 : money1.val ≤ money2.val)
      (hmoney2 : money2.val ≤ 100)
      (hd : d = money2.val - money1.val)
      (s : ℤ) (hs : s = pairSumMin (vals prices)) (hsm : s ≤ money1.val)
      (r1 r2 : Std.I64) (hr1 : Aegis.BuyChoco.buy_choco prices money1 = ok r1)
      (hr2 : Aegis.BuyChoco.buy_choco prices money2 = ok r2) :
      r2.val = r1.val + d := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (prices : Slice Std.I64) (money1 money2 : Std.I64) (n : ℕ) (d : ℤ)
        (hlen : n = prices.val.length) (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
        (hbound : ∀ i, i < n → 1 ≤ getVal prices i ∧ getVal prices i ≤ 100)
        (hmoney1 : 1 ≤ money1.val) (hmoney12 : money1.val ≤ money2.val)
        (hmoney2 : money2.val ≤ 100)
        (hd : d = money2.val - money1.val)
        (s : ℤ) (hs : s = pairSumMin (vals prices)) (hsm : s ≤ money1.val)
        (r1 r2 : Std.I64) (hr1 : Aegis.BuyChoco.buy_choco prices money1 = ok r1)
        (hr2 : Aegis.BuyChoco.buy_choco prices money2 = ok r2), r2.val = r1.val + d) := by
    sorry

  end AegisSpec.BuyChoco
