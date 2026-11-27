import Aegis.CoinChange.Code.Funs

/-!
# Specifications of `Aegis.CoinChange.coin_change`

LeetCode problem `coin-change`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CoinChange

  namespace AegisSpec.CoinChange

  def coinValue (coins : Slice Std.I64) (i : ℕ) : ℤ :=
    match coins.val[i]? with
    | some c => c.val
    | none => 0

  def IsCoinSeq (coins : Slice Std.I64) (x : ℤ) (s : List ℕ) : Prop :=
    (∀ i ∈ s, i < coins.val.length) ∧ (s.map (coinValue coins)).sum = x

  def listMax : List ℤ → ℤ
    | [] => 0
    | x :: xs => max x (listMax xs)

  def listMin : List ℤ → ℤ
    | [] => 0
    | x :: xs => min x (listMin xs)

  def maxCoin (coins : Slice Std.I64) : ℤ :=
    listMax (coins.val.map fun c => c.val)

  def minCoin (coins : Slice Std.I64) : ℤ :=
    listMin (coins.val.map fun c => c.val)

  /-- Whenever coin_change(coins, amount) returns a result r, the following holds. Call a finite sequence of indices (i_1, ..., i_n) a coin sequence for x if n >= 0 (the empty sequence is allowed), each 0 <= i_t < len(coins), and the sum of coins[i_t] over t = 1..n equals x (the empty sum is 0). Then: (a) r = -1 if and only if there is no coin sequence for amount; and (b) if there is a coin sequence for amount, then r >= 0, there exists a coin sequence for amount of length exactly r, and every coin sequence for amount has length at least r.
    Preconditions: coins is a slice of 64-bit integers with 1 <= len(coins) <= 12; for every i with 0 <= i < len(coins), 1 <= coins[i] <= 2^31 - 1; amount is a 64-bit integer with 0 <= amount <= 10000. -/
  theorem spec_1
      (coins : Slice Std.I64) (amount : Std.I64)
      (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
      (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
      (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
      (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000) :
      ∀ r, coin_change coins amount = ok r →
        ((r.val = -1 ↔ ¬ ∃ s : List ℕ, IsCoinSeq coins amount.val s) ∧
          ((∃ s : List ℕ, IsCoinSeq coins amount.val s) →
            (0 ≤ r.val ∧
              (∃ s : List ℕ, IsCoinSeq coins amount.val s ∧ (s.length : ℤ) = r.val) ∧
              (∀ s : List ℕ, IsCoinSeq coins amount.val s →
                r.val ≤ (s.length : ℤ))))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (coins : Slice Std.I64) (amount : Std.I64)
        (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
        (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
        (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
        (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000), ∀ r, coin_change coins amount = ok r →
          ((r.val = -1 ↔ ¬ ∃ s : List ℕ, IsCoinSeq coins amount.val s) ∧
            ((∃ s : List ℕ, IsCoinSeq coins amount.val s) →
              (0 ≤ r.val ∧
                (∃ s : List ℕ, IsCoinSeq coins amount.val s ∧ (s.length : ℤ) = r.val) ∧
                (∀ s : List ℕ, IsCoinSeq coins amount.val s →
                  r.val ≤ (s.length : ℤ)))))) := by
    sorry

  /-- For every coins and amount satisfying the preconditions, coin_change(coins, amount) returns a result r; it does not fail, panic, overflow, or access an out-of-bounds index.
    Preconditions: coins is a slice of 64-bit integers with 1 <= len(coins) <= 12; for every i with 0 <= i < len(coins), 1 <= coins[i] <= 2^31 - 1; amount is a 64-bit integer with 0 <= amount <= 10000. -/
  theorem spec_2
      (coins : Slice Std.I64) (amount : Std.I64)
      (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
      (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
      (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
      (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000) :
      ∃ r, coin_change coins amount = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (coins : Slice Std.I64) (amount : Std.I64)
        (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
        (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
        (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
        (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000), ∃ r, coin_change coins amount = ok r) := by
    sorry

  /-- Whenever coin_change(coins, amount) returns a result r, either r = -1 or (0 <= r and r <= amount).
    Preconditions: coins is a slice of 64-bit integers with 1 <= len(coins) <= 12; for every i with 0 <= i < len(coins), 1 <= coins[i] <= 2^31 - 1; amount is a 64-bit integer with 0 <= amount <= 10000. -/
  theorem spec_3
      (coins : Slice Std.I64) (amount : Std.I64)
      (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
      (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
      (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
      (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000) :
      ∀ r, coin_change coins amount = ok r →
        (r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ amount.val)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (coins : Slice Std.I64) (amount : Std.I64)
        (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
        (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
        (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
        (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000), ∀ r, coin_change coins amount = ok r →
          (r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ amount.val))) := by
    sorry

  /-- Whenever coin_change(coins, amount) returns a result r with r >= 0, let M = max { coins[i] | 0 <= i < len(coins) }. Then amount <= r * M.
    Preconditions: coins is a slice of 64-bit integers with 1 <= len(coins) <= 12; for every i with 0 <= i < len(coins), 1 <= coins[i] <= 2^31 - 1; amount is a 64-bit integer with 0 <= amount <= 10000. -/
  theorem spec_4
      (coins : Slice Std.I64) (amount : Std.I64)
      (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
      (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
      (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
      (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000) :
      ∀ r, coin_change coins amount = ok r → 0 ≤ r.val →
        amount.val ≤ r.val * maxCoin coins := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (coins : Slice Std.I64) (amount : Std.I64)
        (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
        (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
        (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
        (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000), ∀ r, coin_change coins amount = ok r → 0 ≤ r.val →
          amount.val ≤ r.val * maxCoin coins) := by
    sorry

  /-- Whenever coin_change(coins, amount) returns a result r with r >= 0, let m = min { coins[i] | 0 <= i < len(coins) }. Then r <= amount / m, equivalently r * m <= amount, where / is integer division.
    Preconditions: coins is a slice of 64-bit integers with 1 <= len(coins) <= 12; for every i with 0 <= i < len(coins), 1 <= coins[i] <= 2^31 - 1; amount is a 64-bit integer with 0 <= amount <= 10000; additionally amount > 0. -/
  theorem spec_5
      (coins : Slice Std.I64) (amount : Std.I64)
      (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
      (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
      (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
      (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000)
      (hampos : 0 < amount.val) :
      ∀ r, coin_change coins amount = ok r → 0 ≤ r.val →
        (r.val ≤ amount.val / minCoin coins ∧ r.val * minCoin coins ≤ amount.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (coins : Slice Std.I64) (amount : Std.I64)
        (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
        (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
        (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
        (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000)
        (hampos : 0 < amount.val), ∀ r, coin_change coins amount = ok r → 0 ≤ r.val →
          (r.val ≤ amount.val / minCoin coins ∧ r.val * minCoin coins ≤ amount.val)) := by
    sorry

  /-- For every index i with 0 <= i < len(coins) such that coins[i] divides amount, whenever coin_change(coins, amount) returns a result r, we have r >= 0 and r <= amount / coins[i].
    Preconditions: coins is a slice of 64-bit integers with 1 <= len(coins) <= 12; for every i with 0 <= i < len(coins), 1 <= coins[i] <= 2^31 - 1; amount is a 64-bit integer with 0 <= amount <= 10000; additionally amount > 0. -/
  theorem spec_6
      (coins : Slice Std.I64) (amount : Std.I64)
      (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
      (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
      (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
      (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000)
      (hampos : 0 < amount.val) :
      ∀ i, i < coins.val.length → coinValue coins i ∣ amount.val →
        ∀ r, coin_change coins amount = ok r →
          (0 ≤ r.val ∧ r.val ≤ amount.val / coinValue coins i) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (coins : Slice Std.I64) (amount : Std.I64)
        (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
        (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
        (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
        (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000)
        (hampos : 0 < amount.val), ∀ i, i < coins.val.length → coinValue coins i ∣ amount.val →
          ∀ r, coin_change coins amount = ok r →
            (0 ≤ r.val ∧ r.val ≤ amount.val / coinValue coins i)) := by
    sorry

  /-- Let π be any permutation of the index set {0, ..., len(coins)-1}, and define coins' by coins'[j] = coins[π(j)] for 0 <= j < len(coins). Whenever coin_change(coins, amount) returns r and coin_change(coins', amount) returns r', we have r = r'.
    Preconditions: coins is a slice of 64-bit integers with 1 <= len(coins) <= 12; for every i with 0 <= i < len(coins), 1 <= coins[i] <= 2^31 - 1; amount is a 64-bit integer with 0 <= amount <= 10000. -/
  theorem spec_7
      (coins : Slice Std.I64) (amount : Std.I64)
      (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
      (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
      (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
      (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000)
      (coins' : Slice Std.I64) (hperm : coins'.val.Perm coins.val) :
      ∀ r r', coin_change coins amount = ok r → coin_change coins' amount = ok r' →
        r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (coins : Slice Std.I64) (amount : Std.I64)
        (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
        (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
        (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
        (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000)
        (coins' : Slice Std.I64) (hperm : coins'.val.Perm coins.val), ∀ r r', coin_change coins amount = ok r → coin_change coins' amount = ok r' →
          r = r') := by
    sorry

  /-- Let coins' be any slice obtained from coins by deleting all but one occurrence of each denomination value that appears, so coins' has no repeated values and the set of values occurring in coins' equals the set of values occurring in coins. Whenever coin_change(coins, amount) returns r and coin_change(coins', amount) returns r', we have r = r'.
    Preconditions: coins is a slice of 64-bit integers with 1 <= len(coins) <= 12; for every i with 0 <= i < len(coins), 1 <= coins[i] <= 2^31 - 1; amount is a 64-bit integer with 0 <= amount <= 10000. -/
  theorem spec_8
      (coins : Slice Std.I64) (amount : Std.I64)
      (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
      (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
      (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
      (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000)
      (coins' : Slice Std.I64) (hnodup : coins'.val.Nodup)
      (hset : ∀ v : Std.I64, v ∈ coins'.val ↔ v ∈ coins.val) :
      ∀ r r', coin_change coins amount = ok r → coin_change coins' amount = ok r' →
        r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (coins : Slice Std.I64) (amount : Std.I64)
        (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
        (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
        (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
        (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000)
        (coins' : Slice Std.I64) (hnodup : coins'.val.Nodup)
        (hset : ∀ v : Std.I64, v ∈ coins'.val ↔ v ∈ coins.val), ∀ r r', coin_change coins amount = ok r → coin_change coins' amount = ok r' →
          r = r') := by
    sorry

  /-- Whenever coin_change(coins, amount) returns a result r with r >= 0, we have r >= 1.
    Preconditions: coins is a slice of 64-bit integers with 1 <= len(coins) <= 12; for every i with 0 <= i < len(coins), 1 <= coins[i] <= 2^31 - 1; amount is a 64-bit integer with 0 <= amount <= 10000; additionally amount > 0. -/
  theorem spec_9
      (coins : Slice Std.I64) (amount : Std.I64)
      (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
      (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
      (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
      (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000)
      (hampos : 0 < amount.val) :
      ∀ r, coin_change coins amount = ok r → 0 ≤ r.val → 1 ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (coins : Slice Std.I64) (amount : Std.I64)
        (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
        (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
        (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
        (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000)
        (hampos : 0 < amount.val), ∀ r, coin_change coins amount = ok r → 0 ≤ r.val → 1 ≤ r.val) := by
    sorry

  /-- Whenever coin_change(coins, amount) returns r and coin_change(coins', amount) returns r', we have: if r = -1 then r' = -1 or r' >= 0; and if r >= 0 then r' >= 0 and r' <= r.
    Preconditions: coins and coins' are slices of 64-bit integers with 1 <= len(coins) <= 12 and 1 <= len(coins') <= 12; for every i with 0 <= i < len(coins), 1 <= coins[i] <= 2^31 - 1; for every i with 0 <= i < len(coins'), 1 <= coins'[i] <= 2^31 - 1; amount is a 64-bit integer with 0 <= amount <= 10000; additionally every value occurring in coins also occurs in coins' (i.e., coins' is obtained from coins by adding zero or more coins). -/
  theorem spec_10
      (coins coins' : Slice Std.I64) (amount : Std.I64)
      (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
      (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
      (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
      (hlen' : 1 ≤ coins'.val.length ∧ coins'.val.length ≤ 12)
      (hpos' : ∀ i, i < coins'.val.length → 1 ≤ coinValue coins' i)
      (hle' : ∀ i, i < coins'.val.length → coinValue coins' i ≤ 2 ^ 31 - 1)
      (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000)
      (hsub : ∀ v : Std.I64, v ∈ coins.val → v ∈ coins'.val) :
      ∀ r r', coin_change coins amount = ok r → coin_change coins' amount = ok r' →
        ((r.val = -1 → r'.val = -1 ∨ 0 ≤ r'.val) ∧
          (0 ≤ r.val → 0 ≤ r'.val ∧ r'.val ≤ r.val)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (coins coins' : Slice Std.I64) (amount : Std.I64)
        (hlen : 1 ≤ coins.val.length ∧ coins.val.length ≤ 12)
        (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
        (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
        (hlen' : 1 ≤ coins'.val.length ∧ coins'.val.length ≤ 12)
        (hpos' : ∀ i, i < coins'.val.length → 1 ≤ coinValue coins' i)
        (hle' : ∀ i, i < coins'.val.length → coinValue coins' i ≤ 2 ^ 31 - 1)
        (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000)
        (hsub : ∀ v : Std.I64, v ∈ coins.val → v ∈ coins'.val), ∀ r r', coin_change coins amount = ok r → coin_change coins' amount = ok r' →
          ((r.val = -1 → r'.val = -1 ∨ 0 ≤ r'.val) ∧
            (0 ≤ r.val → 0 ≤ r'.val ∧ r'.val ≤ r.val))) := by
    sorry

  /-- For any index j with 0 <= j < len(coins) and coins[j] > amount, let coins' be the slice obtained from coins by deleting index j (so len(coins') = len(coins)-1 and coins'[i] = coins[i] for i < j, coins'[i] = coins[i+1] for i >= j). Then coin_change(coins, amount) = coin_change(coins', amount).
    Preconditions: coins is a slice of 64-bit integers with 2 <= len(coins) <= 12; for every i with 0 <= i < len(coins), 1 <= coins[i] <= 2^31 - 1; amount is a 64-bit integer with 0 <= amount <= 10000; additionally there exists j with 0 <= j < len(coins) and coins[j] > amount. -/
  theorem spec_11
      (coins : Slice Std.I64) (amount : Std.I64)
      (hlen : 2 ≤ coins.val.length ∧ coins.val.length ≤ 12)
      (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
      (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
      (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000)
      (hex : ∃ j, j < coins.val.length ∧ amount.val < coinValue coins j) :
      ∀ (coins' : Slice Std.I64) (j : ℕ) (hj : j < coins.val.length)
        (hgt : amount.val < coinValue coins j)
        (hdel : coins'.val = coins.val.eraseIdx j),
        coin_change coins amount = coin_change coins' amount := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (coins : Slice Std.I64) (amount : Std.I64)
        (hlen : 2 ≤ coins.val.length ∧ coins.val.length ≤ 12)
        (hpos : ∀ i, i < coins.val.length → 1 ≤ coinValue coins i)
        (hle : ∀ i, i < coins.val.length → coinValue coins i ≤ 2 ^ 31 - 1)
        (ham0 : 0 ≤ amount.val) (ham1 : amount.val ≤ 10000)
        (hex : ∃ j, j < coins.val.length ∧ amount.val < coinValue coins j), ∀ (coins' : Slice Std.I64) (j : ℕ) (hj : j < coins.val.length)
          (hgt : amount.val < coinValue coins j)
          (hdel : coins'.val = coins.val.eraseIdx j),
          coin_change coins amount = coin_change coins' amount) := by
    sorry

  end AegisSpec.CoinChange
