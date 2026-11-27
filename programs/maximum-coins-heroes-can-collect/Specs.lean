import Aegis.MaximumCoins.Code.Funs

/-!
# Specifications of `Aegis.MaximumCoins.maximum_coins`

LeetCode problem `maximum-coins-heroes-can-collect`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  open Aegis.MaximumCoins

  namespace AegisSpec.MaximumCoins

  def toInt (x : Std.I64) : ℤ := x.val

  def values (l : List Std.I64) : List ℤ := l.map toInt

  def nth (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

  def hnth (l : List Std.I64) (i : ℕ) : ℤ := nth (values l) i

  def sumLe (monsters coins : List ℤ) (h : ℤ) : ℤ :=
    (((monsters.zip coins).filter (fun p => p.1 ≤ h)).map (fun p => p.2)).sum

  def sumGt (monsters coins : List ℤ) (h : ℤ) : ℤ :=
    (((monsters.zip coins).filter (fun p => h < p.1)).map (fun p => p.2)).sum

  def total (coins : List ℤ) : ℤ := coins.sum

  def within (l : List ℤ) (lo hi : ℤ) : Prop := ∀ x ∈ l, lo ≤ x ∧ x ≤ hi

  def allLe (monsters : List ℤ) (h : ℤ) : Prop := ∀ x ∈ monsters, x ≤ h

  def allGt (monsters : List ℤ) (h : ℤ) : Prop := ∀ x ∈ monsters, h < x

  /-- The function returns a result r and len(r) = len(heroes); for every i with 0 <= i < len(heroes), r[i] equals the sum of coins[j] over all j with 0 <= j < len(monsters) and monsters[j] <= heroes[i]. The sum over an empty index set is 0.
    Preconditions: n = len(heroes), m = len(monsters), len(coins) = m, 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, 1 <= heroes[i] <= 1000000000; for every j with 0 <= j < m, 1 <= monsters[j] <= 1000000000 and 1 <= coins[j] <= 1000000000. -/
  theorem spec_1
      (heroes monsters coins : Slice Std.I64) (n m : ℕ)
      (hn : n = heroes.val.length) (hm : m = monsters.val.length)
      (hc : coins.val.length = m)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
      (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
      (h_heroes : within (values heroes.val) 1 1000000000)
      (h_monsters : within (values monsters.val) 1 1000000000)
      (h_coins : within (values coins.val) 1 1000000000) :
      ∃ r : alloc.vec.Vec Std.I64,
        maximum_coins heroes monsters coins = ok r ∧
          r.val.length = heroes.val.length ∧
          ∀ i : ℕ, i < heroes.val.length →
            hnth r.val i =
              sumLe (values monsters.val) (values coins.val) (hnth heroes.val i) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (heroes monsters coins : Slice Std.I64) (n m : ℕ)
        (hn : n = heroes.val.length) (hm : m = monsters.val.length)
        (hc : coins.val.length = m)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
        (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
        (h_heroes : within (values heroes.val) 1 1000000000)
        (h_monsters : within (values monsters.val) 1 1000000000)
        (h_coins : within (values coins.val) 1 1000000000), ∃ r : alloc.vec.Vec Std.I64,
          maximum_coins heroes monsters coins = ok r ∧
            r.val.length = heroes.val.length ∧
            ∀ i : ℕ, i < heroes.val.length →
              hnth r.val i =
                sumLe (values monsters.val) (values coins.val) (hnth heroes.val i)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; in particular, it does not fail with a panic, an out-of-bounds access, or arithmetic overflow.
    Preconditions: n = len(heroes), m = len(monsters), len(coins) = m, 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, 1 <= heroes[i] <= 1000000000; for every j with 0 <= j < m, 1 <= monsters[j] <= 1000000000 and 1 <= coins[j] <= 1000000000. -/
  theorem spec_2
      (heroes monsters coins : Slice Std.I64) (n m : ℕ)
      (hn : n = heroes.val.length) (hm : m = monsters.val.length)
      (hc : coins.val.length = m)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
      (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
      (h_heroes : within (values heroes.val) 1 1000000000)
      (h_monsters : within (values monsters.val) 1 1000000000)
      (h_coins : within (values coins.val) 1 1000000000) :
      ∃ r : alloc.vec.Vec Std.I64, maximum_coins heroes monsters coins = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (heroes monsters coins : Slice Std.I64) (n m : ℕ)
        (hn : n = heroes.val.length) (hm : m = monsters.val.length)
        (hc : coins.val.length = m)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
        (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
        (h_heroes : within (values heroes.val) 1 1000000000)
        (h_monsters : within (values monsters.val) 1 1000000000)
        (h_coins : within (values coins.val) 1 1000000000), ∃ r : alloc.vec.Vec Std.I64, maximum_coins heroes monsters coins = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(heroes).
    Preconditions: n = len(heroes), m = len(monsters), len(coins) = m, 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, 1 <= heroes[i] <= 1000000000; for every j with 0 <= j < m, 1 <= monsters[j] <= 1000000000 and 1 <= coins[j] <= 1000000000. -/
  theorem spec_3
      (heroes monsters coins : Slice Std.I64) (n m : ℕ)
      (hn : n = heroes.val.length) (hm : m = monsters.val.length)
      (hc : coins.val.length = m)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
      (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
      (h_heroes : within (values heroes.val) 1 1000000000)
      (h_monsters : within (values monsters.val) 1 1000000000)
      (h_coins : within (values coins.val) 1 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        maximum_coins heroes monsters coins = ok r → r.val.length = heroes.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (heroes monsters coins : Slice Std.I64) (n m : ℕ)
        (hn : n = heroes.val.length) (hm : m = monsters.val.length)
        (hc : coins.val.length = m)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
        (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
        (h_heroes : within (values heroes.val) 1 1000000000)
        (h_monsters : within (values monsters.val) 1 1000000000)
        (h_coins : within (values coins.val) 1 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          maximum_coins heroes monsters coins = ok r → r.val.length = heroes.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(heroes), 0 <= r[i].
    Preconditions: n = len(heroes), m = len(monsters), len(coins) = m, 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, 1 <= heroes[i] <= 1000000000; for every j with 0 <= j < m, 1 <= monsters[j] <= 1000000000 and 1 <= coins[j] <= 1000000000. -/
  theorem spec_4
      (heroes monsters coins : Slice Std.I64) (n m : ℕ)
      (hn : n = heroes.val.length) (hm : m = monsters.val.length)
      (hc : coins.val.length = m)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
      (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
      (h_heroes : within (values heroes.val) 1 1000000000)
      (h_monsters : within (values monsters.val) 1 1000000000)
      (h_coins : within (values coins.val) 1 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        maximum_coins heroes monsters coins = ok r →
          ∀ i : ℕ, i < heroes.val.length → 0 ≤ hnth r.val i := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (heroes monsters coins : Slice Std.I64) (n m : ℕ)
        (hn : n = heroes.val.length) (hm : m = monsters.val.length)
        (hc : coins.val.length = m)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
        (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
        (h_heroes : within (values heroes.val) 1 1000000000)
        (h_monsters : within (values monsters.val) 1 1000000000)
        (h_coins : within (values coins.val) 1 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          maximum_coins heroes monsters coins = ok r →
            ∀ i : ℕ, i < heroes.val.length → 0 ≤ hnth r.val i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(heroes), r[i] is at most the sum of coins[j] over all j with 0 <= j < len(monsters).
    Preconditions: n = len(heroes), m = len(monsters), len(coins) = m, 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, 1 <= heroes[i] <= 1000000000; for every j with 0 <= j < m, 1 <= monsters[j] <= 1000000000 and 1 <= coins[j] <= 1000000000. -/
  theorem spec_5
      (heroes monsters coins : Slice Std.I64) (n m : ℕ)
      (hn : n = heroes.val.length) (hm : m = monsters.val.length)
      (hc : coins.val.length = m)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
      (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
      (h_heroes : within (values heroes.val) 1 1000000000)
      (h_monsters : within (values monsters.val) 1 1000000000)
      (h_coins : within (values coins.val) 1 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        maximum_coins heroes monsters coins = ok r →
          ∀ i : ℕ, i < heroes.val.length →
            hnth r.val i ≤ total (values coins.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (heroes monsters coins : Slice Std.I64) (n m : ℕ)
        (hn : n = heroes.val.length) (hm : m = monsters.val.length)
        (hc : coins.val.length = m)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
        (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
        (h_heroes : within (values heroes.val) 1 1000000000)
        (h_monsters : within (values monsters.val) 1 1000000000)
        (h_coins : within (values coins.val) 1 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          maximum_coins heroes monsters coins = ok r →
            ∀ i : ℕ, i < heroes.val.length →
              hnth r.val i ≤ total (values coins.val)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(heroes), r[i] = 0 if and only if for every j with 0 <= j < len(monsters), monsters[j] > heroes[i].
    Preconditions: n = len(heroes), m = len(monsters), len(coins) = m, 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, 1 <= heroes[i] <= 1000000000; for every j with 0 <= j < m, 1 <= monsters[j] <= 1000000000 and 1 <= coins[j] <= 1000000000. -/
  theorem spec_6
      (heroes monsters coins : Slice Std.I64) (n m : ℕ)
      (hn : n = heroes.val.length) (hm : m = monsters.val.length)
      (hc : coins.val.length = m)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
      (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
      (h_heroes : within (values heroes.val) 1 1000000000)
      (h_monsters : within (values monsters.val) 1 1000000000)
      (h_coins : within (values coins.val) 1 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        maximum_coins heroes monsters coins = ok r →
          ∀ i : ℕ, i < heroes.val.length →
            (hnth r.val i = 0 ↔ allGt (values monsters.val) (hnth heroes.val i)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (heroes monsters coins : Slice Std.I64) (n m : ℕ)
        (hn : n = heroes.val.length) (hm : m = monsters.val.length)
        (hc : coins.val.length = m)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
        (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
        (h_heroes : within (values heroes.val) 1 1000000000)
        (h_monsters : within (values monsters.val) 1 1000000000)
        (h_coins : within (values coins.val) 1 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          maximum_coins heroes monsters coins = ok r →
            ∀ i : ℕ, i < heroes.val.length →
              (hnth r.val i = 0 ↔ allGt (values monsters.val) (hnth heroes.val i))) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(heroes), if for every j with 0 <= j < len(monsters) we have monsters[j] <= heroes[i], then r[i] equals the sum of coins[j] over all j with 0 <= j < len(monsters).
    Preconditions: n = len(heroes), m = len(monsters), len(coins) = m, 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, 1 <= heroes[i] <= 1000000000; for every j with 0 <= j < m, 1 <= monsters[j] <= 1000000000 and 1 <= coins[j] <= 1000000000. -/
  theorem spec_7
      (heroes monsters coins : Slice Std.I64) (n m : ℕ)
      (hn : n = heroes.val.length) (hm : m = monsters.val.length)
      (hc : coins.val.length = m)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
      (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
      (h_heroes : within (values heroes.val) 1 1000000000)
      (h_monsters : within (values monsters.val) 1 1000000000)
      (h_coins : within (values coins.val) 1 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        maximum_coins heroes monsters coins = ok r →
          ∀ i : ℕ, i < heroes.val.length →
            allLe (values monsters.val) (hnth heroes.val i) →
              hnth r.val i = total (values coins.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (heroes monsters coins : Slice Std.I64) (n m : ℕ)
        (hn : n = heroes.val.length) (hm : m = monsters.val.length)
        (hc : coins.val.length = m)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
        (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
        (h_heroes : within (values heroes.val) 1 1000000000)
        (h_monsters : within (values monsters.val) 1 1000000000)
        (h_coins : within (values coins.val) 1 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          maximum_coins heroes monsters coins = ok r →
            ∀ i : ℕ, i < heroes.val.length →
              allLe (values monsters.val) (hnth heroes.val i) →
                hnth r.val i = total (values coins.val)) := by
    sorry

  /-- Whenever the function returns a result r, for every i and k with 0 <= i < len(heroes) and 0 <= k < len(heroes), if heroes[i] <= heroes[k], then r[i] <= r[k].
    Preconditions: n = len(heroes), m = len(monsters), len(coins) = m, 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, 1 <= heroes[i] <= 1000000000; for every j with 0 <= j < m, 1 <= monsters[j] <= 1000000000 and 1 <= coins[j] <= 1000000000. -/
  theorem spec_8
      (heroes monsters coins : Slice Std.I64) (n m : ℕ)
      (hn : n = heroes.val.length) (hm : m = monsters.val.length)
      (hc : coins.val.length = m)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
      (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
      (h_heroes : within (values heroes.val) 1 1000000000)
      (h_monsters : within (values monsters.val) 1 1000000000)
      (h_coins : within (values coins.val) 1 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        maximum_coins heroes monsters coins = ok r →
          ∀ i k : ℕ, i < heroes.val.length → k < heroes.val.length →
            hnth heroes.val i ≤ hnth heroes.val k → hnth r.val i ≤ hnth r.val k := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (heroes monsters coins : Slice Std.I64) (n m : ℕ)
        (hn : n = heroes.val.length) (hm : m = monsters.val.length)
        (hc : coins.val.length = m)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
        (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
        (h_heroes : within (values heroes.val) 1 1000000000)
        (h_monsters : within (values monsters.val) 1 1000000000)
        (h_coins : within (values coins.val) 1 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          maximum_coins heroes monsters coins = ok r →
            ∀ i k : ℕ, i < heroes.val.length → k < heroes.val.length →
              hnth heroes.val i ≤ hnth heroes.val k → hnth r.val i ≤ hnth r.val k) := by
    sorry

  /-- Whenever the function returns a result r, for every i and k with 0 <= i < len(heroes) and 0 <= k < len(heroes), if heroes[i] = heroes[k], then r[i] = r[k].
    Preconditions: n = len(heroes), m = len(monsters), len(coins) = m, 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, 1 <= heroes[i] <= 1000000000; for every j with 0 <= j < m, 1 <= monsters[j] <= 1000000000 and 1 <= coins[j] <= 1000000000. -/
  theorem spec_9
      (heroes monsters coins : Slice Std.I64) (n m : ℕ)
      (hn : n = heroes.val.length) (hm : m = monsters.val.length)
      (hc : coins.val.length = m)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
      (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
      (h_heroes : within (values heroes.val) 1 1000000000)
      (h_monsters : within (values monsters.val) 1 1000000000)
      (h_coins : within (values coins.val) 1 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        maximum_coins heroes monsters coins = ok r →
          ∀ i k : ℕ, i < heroes.val.length → k < heroes.val.length →
            hnth heroes.val i = hnth heroes.val k → hnth r.val i = hnth r.val k := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (heroes monsters coins : Slice Std.I64) (n m : ℕ)
        (hn : n = heroes.val.length) (hm : m = monsters.val.length)
        (hc : coins.val.length = m)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
        (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
        (h_heroes : within (values heroes.val) 1 1000000000)
        (h_monsters : within (values monsters.val) 1 1000000000)
        (h_coins : within (values coins.val) 1 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          maximum_coins heroes monsters coins = ok r →
            ∀ i k : ℕ, i < heroes.val.length → k < heroes.val.length →
              hnth heroes.val i = hnth heroes.val k → hnth r.val i = hnth r.val k) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(heroes) and every j with 0 <= j < len(monsters), if monsters[j] <= heroes[i], then r[i] >= coins[j].
    Preconditions: n = len(heroes), m = len(monsters), len(coins) = m, 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, 1 <= heroes[i] <= 1000000000; for every j with 0 <= j < m, 1 <= monsters[j] <= 1000000000 and 1 <= coins[j] <= 1000000000. -/
  theorem spec_10
      (heroes monsters coins : Slice Std.I64) (n m : ℕ)
      (hn : n = heroes.val.length) (hm : m = monsters.val.length)
      (hc : coins.val.length = m)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
      (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
      (h_heroes : within (values heroes.val) 1 1000000000)
      (h_monsters : within (values monsters.val) 1 1000000000)
      (h_coins : within (values coins.val) 1 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        maximum_coins heroes monsters coins = ok r →
          ∀ i j : ℕ, i < heroes.val.length → j < monsters.val.length →
            hnth monsters.val j ≤ hnth heroes.val i → hnth coins.val j ≤ hnth r.val i := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (heroes monsters coins : Slice Std.I64) (n m : ℕ)
        (hn : n = heroes.val.length) (hm : m = monsters.val.length)
        (hc : coins.val.length = m)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
        (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
        (h_heroes : within (values heroes.val) 1 1000000000)
        (h_monsters : within (values monsters.val) 1 1000000000)
        (h_coins : within (values coins.val) 1 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          maximum_coins heroes monsters coins = ok r →
            ∀ i j : ℕ, i < heroes.val.length → j < monsters.val.length →
              hnth monsters.val j ≤ hnth heroes.val i → hnth coins.val j ≤ hnth r.val i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(heroes), for every pair of distinct indices j and k with 0 <= j < len(monsters), 0 <= k < len(monsters), and j != k, if monsters[j] <= heroes[i] and monsters[k] <= heroes[i], then r[i] >= coins[j] + coins[k].
    Preconditions: n = len(heroes), m = len(monsters), len(coins) = m, 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, 1 <= heroes[i] <= 1000000000; for every j with 0 <= j < m, 1 <= monsters[j] <= 1000000000 and 1 <= coins[j] <= 1000000000. -/
  theorem spec_11
      (heroes monsters coins : Slice Std.I64) (n m : ℕ)
      (hn : n = heroes.val.length) (hm : m = monsters.val.length)
      (hc : coins.val.length = m)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
      (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
      (h_heroes : within (values heroes.val) 1 1000000000)
      (h_monsters : within (values monsters.val) 1 1000000000)
      (h_coins : within (values coins.val) 1 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        maximum_coins heroes monsters coins = ok r →
          ∀ i j k : ℕ, i < heroes.val.length → j < monsters.val.length →
            k < monsters.val.length → j ≠ k →
              hnth monsters.val j ≤ hnth heroes.val i →
                hnth monsters.val k ≤ hnth heroes.val i →
                  hnth coins.val j + hnth coins.val k ≤ hnth r.val i := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (heroes monsters coins : Slice Std.I64) (n m : ℕ)
        (hn : n = heroes.val.length) (hm : m = monsters.val.length)
        (hc : coins.val.length = m)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
        (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
        (h_heroes : within (values heroes.val) 1 1000000000)
        (h_monsters : within (values monsters.val) 1 1000000000)
        (h_coins : within (values coins.val) 1 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          maximum_coins heroes monsters coins = ok r →
            ∀ i j k : ℕ, i < heroes.val.length → j < monsters.val.length →
              k < monsters.val.length → j ≠ k →
                hnth monsters.val j ≤ hnth heroes.val i →
                  hnth monsters.val k ≤ hnth heroes.val i →
                    hnth coins.val j + hnth coins.val k ≤ hnth r.val i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(heroes), r[i] equals the total sum of coins[j] over all j with 0 <= j < len(monsters), minus the sum of coins[j] over all j with 0 <= j < len(monsters) and monsters[j] > heroes[i].
    Preconditions: n = len(heroes), m = len(monsters), len(coins) = m, 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, 1 <= heroes[i] <= 1000000000; for every j with 0 <= j < m, 1 <= monsters[j] <= 1000000000 and 1 <= coins[j] <= 1000000000. -/
  theorem spec_12
      (heroes monsters coins : Slice Std.I64) (n m : ℕ)
      (hn : n = heroes.val.length) (hm : m = monsters.val.length)
      (hc : coins.val.length = m)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
      (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
      (h_heroes : within (values heroes.val) 1 1000000000)
      (h_monsters : within (values monsters.val) 1 1000000000)
      (h_coins : within (values coins.val) 1 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        maximum_coins heroes monsters coins = ok r →
          ∀ i : ℕ, i < heroes.val.length →
            hnth r.val i =
              total (values coins.val) -
                sumGt (values monsters.val) (values coins.val) (hnth heroes.val i) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (heroes monsters coins : Slice Std.I64) (n m : ℕ)
        (hn : n = heroes.val.length) (hm : m = monsters.val.length)
        (hc : coins.val.length = m)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
        (hm_lo : 1 ≤ m) (hm_hi : m ≤ 100000)
        (h_heroes : within (values heroes.val) 1 1000000000)
        (h_monsters : within (values monsters.val) 1 1000000000)
        (h_coins : within (values coins.val) 1 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          maximum_coins heroes monsters coins = ok r →
            ∀ i : ℕ, i < heroes.val.length →
              hnth r.val i =
                total (values coins.val) -
                  sumGt (values monsters.val) (values coins.val) (hnth heroes.val i)) := by
    sorry

  end AegisSpec.MaximumCoins
