import Aegis.MaxPower.Code.Funs

/-!
# Specifications of `Aegis.MaxPower.max_power`

LeetCode problem `maximize-the-minimum-powered-city`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxPower (max_power)
  open scoped BigOperators

  namespace AegisSpec.MaxPower

  def contents (stations : Slice I64) : List Int := stations.val.map (fun x => x.val)

  def stval (stations : Slice I64) (i : Nat) : Int := (contents stations).getD i 0

  def base (stations : Slice I64) (r : Int) (j : Nat) : Int :=
    ∑ i ∈ Finset.range stations.val.length,
      if |(i : Int) - (j : Int)| ≤ r then stval stations i else 0

  def baseMin (stations : Slice I64) (r : Int) : Int :=
    ((List.range stations.val.length).map (fun j => base stations r j)).min?.getD 0

  def IsAlloc (stations : Slice I64) (k : Int) (a : List Nat) : Prop :=
    a.length = stations.val.length ∧ (a.sum : Int) = k

  def power (stations : Slice I64) (r : Int) (a : List Nat) (j : Nat) : Int :=
    ∑ i ∈ Finset.range stations.val.length,
      if |(i : Int) - (j : Int)| ≤ r then stval stations i + (a.getD i 0 : Int) else 0

  def minPower (stations : Slice I64) (r : Int) (a : List Nat) : Int :=
    ((List.range stations.val.length).map (fun j => power stations r a j)).min?.getD 0

  def needToReach (stations : Slice I64) (t : Int) : Int :=
    ∑ i ∈ Finset.range stations.val.length, max 0 (t - stval stations i)

  /-- Whenever max_power(stations, r, k) returns a result ans, ans is the least integer u such that for every allocation a = (a_0,...,a_{n-1}) of nonnegative integers with sum_{i=0}^{n-1} a_i = k, the minimum post-allocation city power is at most u. The post-allocation power of city j under allocation a is P(a,j) = sum over i with 0 <= i < n and |i-j| <= r of (stations[i] + a_i), and the minimum is taken over all j with 0 <= j < n. Equivalently, ans is the maximum over all such allocations a of min_{0<=j<n} P(a,j).
    Preconditions: n = len(stations), 1 <= n <= 100000, for every i with 0 <= i < n, 0 <= stations[i] <= 100000, 0 <= r <= n-1, and 0 <= k <= 1000000000. -/
  theorem spec_1 (stations : Slice I64) (r k : I64) (n : Nat)
      (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
      (hr0 : 0 ≤ r.val) (hr1 : r.val ≤ (n : Int) - 1)
      (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000) :
      ∀ ans, max_power stations r k = ok ans →
        (∀ a, IsAlloc stations k.val a → minPower stations r.val a ≤ ans) ∧
        (∀ u : Int, (∀ a, IsAlloc stations k.val a → minPower stations r.val a ≤ u) → ans ≤ u) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (stations : Slice I64) (r k : I64) (n : Nat)
        (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
        (hr0 : 0 ≤ r.val) (hr1 : r.val ≤ (n : Int) - 1)
        (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000), ∀ ans, max_power stations r k = ok ans →
          (∀ a, IsAlloc stations k.val a → minPower stations r.val a ≤ ans) ∧
          (∀ u : Int, (∀ a, IsAlloc stations k.val a → minPower stations r.val a ≤ u) → ans ≤ u)) := by
    sorry

  /-- max_power(stations, r, k) returns a result; it does not fail, panic, overflow, or perform an out-of-bounds access.
    Preconditions: n = len(stations), 1 <= n <= 100000, for every i with 0 <= i < n, 0 <= stations[i] <= 100000, 0 <= r <= n-1, and 0 <= k <= 1000000000. -/
  theorem spec_2 (stations : Slice I64) (r k : I64) (n : Nat)
      (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
      (hr0 : 0 ≤ r.val) (hr1 : r.val ≤ (n : Int) - 1)
      (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000) :
      ∃ ans, max_power stations r k = ok ans := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (stations : Slice I64) (r k : I64) (n : Nat)
        (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
        (hr0 : 0 ≤ r.val) (hr1 : r.val ≤ (n : Int) - 1)
        (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000), ∃ ans, max_power stations r k = ok ans) := by
    sorry

  /-- Whenever max_power(stations, r, k) returns ans, ans >= Bmin, where Bmin = min_{0<=j<n} B(j) and B(j) = sum over i with 0 <= i < n and |i-j| <= r of stations[i].
    Preconditions: n = len(stations), 1 <= n <= 100000, for every i with 0 <= i < n, 0 <= stations[i] <= 100000, 0 <= r <= n-1, and 0 <= k <= 1000000000. -/
  theorem spec_3 (stations : Slice I64) (r k : I64) (n : Nat)
      (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
      (hr0 : 0 ≤ r.val) (hr1 : r.val ≤ (n : Int) - 1)
      (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000) :
      ∀ ans, max_power stations r k = ok ans → baseMin stations r.val ≤ ans := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (stations : Slice I64) (r k : I64) (n : Nat)
        (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
        (hr0 : 0 ≤ r.val) (hr1 : r.val ≤ (n : Int) - 1)
        (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000), ∀ ans, max_power stations r k = ok ans → baseMin stations r.val ≤ ans) := by
    sorry

  /-- Whenever max_power(stations, r, k) returns ans, ans <= Bmin + k, where Bmin = min_{0<=j<n} B(j) and B(j) = sum over i with 0 <= i < n and |i-j| <= r of stations[i].
    Preconditions: n = len(stations), 1 <= n <= 100000, for every i with 0 <= i < n, 0 <= stations[i] <= 100000, 0 <= r <= n-1, and 0 <= k <= 1000000000. -/
  theorem spec_4 (stations : Slice I64) (r k : I64) (n : Nat)
      (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
      (hr0 : 0 ≤ r.val) (hr1 : r.val ≤ (n : Int) - 1)
      (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000) :
      ∀ ans, max_power stations r k = ok ans → ans ≤ baseMin stations r.val + k.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (stations : Slice I64) (r k : I64) (n : Nat)
        (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
        (hr0 : 0 ≤ r.val) (hr1 : r.val ≤ (n : Int) - 1)
        (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000), ∀ ans, max_power stations r k = ok ans → ans ≤ baseMin stations r.val + k.val) := by
    sorry

  /-- Whenever max_power(stations, r, 0) returns ans, ans = Bmin, where Bmin = min_{0<=j<n} B(j) and B(j) = sum over i with 0 <= i < n and |i-j| <= r of stations[i].
    Preconditions: n = len(stations), 1 <= n <= 100000, for every i with 0 <= i < n, 0 <= stations[i] <= 100000, 0 <= r <= n-1, and k = 0. -/
  theorem spec_5 (stations : Slice I64) (r k : I64) (n : Nat)
      (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
      (hr0 : 0 ≤ r.val) (hr1 : r.val ≤ (n : Int) - 1)
      (hk : k.val = 0) :
      ∀ ans, max_power stations r k = ok ans → ans = baseMin stations r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (stations : Slice I64) (r k : I64) (n : Nat)
        (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
        (hr0 : 0 ≤ r.val) (hr1 : r.val ≤ (n : Int) - 1)
        (hk : k.val = 0), ∀ ans, max_power stations r k = ok ans → ans = baseMin stations r.val) := by
    sorry

  /-- Whenever max_power(stations, 0, k) returns ans, ans is the greatest integer t such that sum_{i=0}^{n-1} max(0, t - stations[i]) <= k. Equivalently, ans = max over allocations a=(a_0,...,a_{n-1}) with a_i >= 0 and sum_{i=0}^{n-1} a_i = k of min_{0<=i<n} (stations[i]+a_i).
    Preconditions: n = len(stations), 1 <= n <= 100000, for every i with 0 <= i < n, 0 <= stations[i] <= 100000, r = 0, and 0 <= k <= 1000000000. -/
  theorem spec_6 (stations : Slice I64) (r k : I64) (n : Nat)
      (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
      (hr : r.val = 0)
      (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000) :
      ∀ ans, max_power stations r k = ok ans →

        needToReach stations ans ≤ k.val ∧

        (∀ t : Int, needToReach stations t ≤ k.val → t ≤ ans) ∧

        (∀ a, IsAlloc stations k.val a → minPower stations 0 a ≤ ans) ∧

        (∀ u : Int, (∀ a, IsAlloc stations k.val a → minPower stations 0 a ≤ u) → ans ≤ u) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (stations : Slice I64) (r k : I64) (n : Nat)
        (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
        (hr : r.val = 0)
        (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000), ∀ ans, max_power stations r k = ok ans →

          needToReach stations ans ≤ k.val ∧

          (∀ t : Int, needToReach stations t ≤ k.val → t ≤ ans) ∧

          (∀ a, IsAlloc stations k.val a → minPower stations 0 a ≤ ans) ∧

          (∀ u : Int, (∀ a, IsAlloc stations k.val a → minPower stations 0 a ≤ u) → ans ≤ u)) := by
    sorry

  /-- Whenever max_power(stations, n-1, k) returns ans, ans = (sum_{i=0}^{n-1} stations[i]) + k.
    Preconditions: n = len(stations), 1 <= n <= 100000, for every i with 0 <= i < n, 0 <= stations[i] <= 100000, r = n-1, and 0 <= k <= 1000000000. -/
  theorem spec_7 (stations : Slice I64) (r k : I64) (n : Nat)
      (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
      (hr : r.val = (n : Int) - 1)
      (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000) :
      ∀ ans, max_power stations r k = ok ans → ans = (contents stations).sum + k.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (stations : Slice I64) (r k : I64) (n : Nat)
        (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
        (hr : r.val = (n : Int) - 1)
        (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000), ∀ ans, max_power stations r k = ok ans → ans = (contents stations).sum + k.val) := by
    sorry

  /-- If max_power(stations, r, k1) returns ans1 and max_power(stations, r, k2) returns ans2, then ans1 <= ans2.
    Preconditions: n = len(stations), 1 <= n <= 100000, for every i with 0 <= i < n, 0 <= stations[i] <= 100000, 0 <= r <= n-1, and 0 <= k1 <= k2 <= 1000000000. -/
  theorem spec_8 (stations : Slice I64) (r k1 k2 : I64) (n : Nat)
      (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
      (hr0 : 0 ≤ r.val) (hr1 : r.val ≤ (n : Int) - 1)
      (hk1_0 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_1 : k2.val ≤ 1000000000) :
      ∀ ans1 ans2, max_power stations r k1 = ok ans1 → max_power stations r k2 = ok ans2 →
        ans1 ≤ ans2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (stations : Slice I64) (r k1 k2 : I64) (n : Nat)
        (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
        (hr0 : 0 ≤ r.val) (hr1 : r.val ≤ (n : Int) - 1)
        (hk1_0 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_1 : k2.val ≤ 1000000000), ∀ ans1 ans2, max_power stations r k1 = ok ans1 → max_power stations r k2 = ok ans2 →
          ans1 ≤ ans2) := by
    sorry

  /-- If max_power(stations, r1, k) returns ans1 and max_power(stations, r2, k) returns ans2, then ans1 <= ans2.
    Preconditions: n = len(stations), 1 <= n <= 100000, for every i with 0 <= i < n, 0 <= stations[i] <= 100000, 0 <= r1 <= r2 <= n-1, and 0 <= k <= 1000000000. -/
  theorem spec_9 (stations : Slice I64) (r1 r2 k : I64) (n : Nat)
      (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
      (hr1_0 : 0 ≤ r1.val) (hr12 : r1.val ≤ r2.val) (hr2_1 : r2.val ≤ (n : Int) - 1)
      (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000) :
      ∀ ans1 ans2, max_power stations r1 k = ok ans1 → max_power stations r2 k = ok ans2 →
        ans1 ≤ ans2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (stations : Slice I64) (r1 r2 k : I64) (n : Nat)
        (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
        (hr1_0 : 0 ≤ r1.val) (hr12 : r1.val ≤ r2.val) (hr2_1 : r2.val ≤ (n : Int) - 1)
        (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000), ∀ ans1 ans2, max_power stations r1 k = ok ans1 → max_power stations r2 k = ok ans2 →
          ans1 ≤ ans2) := by
    sorry

  /-- If max_power(stations1, r, k) returns ans1 and max_power(stations2, r, k) returns ans2, then ans1 <= ans2.
    Preconditions: len(stations1) = len(stations2) = n, 1 <= n <= 100000, for every i with 0 <= i < n, 0 <= stations1[i] <= stations2[i] <= 100000, 0 <= r <= n-1, and 0 <= k <= 1000000000. -/
  theorem spec_10 (stations1 stations2 : Slice I64) (r k : I64) (n : Nat)
      (hlen1 : stations1.val.length = n) (hlen2 : stations2.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hst : ∀ i, i < n → 0 ≤ stval stations1 i ∧ stval stations1 i ≤ stval stations2 i ∧
        stval stations2 i ≤ 100000)
      (hr0 : 0 ≤ r.val) (hr1 : r.val ≤ (n : Int) - 1)
      (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000) :
      ∀ ans1 ans2, max_power stations1 r k = ok ans1 → max_power stations2 r k = ok ans2 →
        ans1 ≤ ans2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (stations1 stations2 : Slice I64) (r k : I64) (n : Nat)
        (hlen1 : stations1.val.length = n) (hlen2 : stations2.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hst : ∀ i, i < n → 0 ≤ stval stations1 i ∧ stval stations1 i ≤ stval stations2 i ∧
          stval stations2 i ≤ 100000)
        (hr0 : 0 ≤ r.val) (hr1 : r.val ≤ (n : Int) - 1)
        (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000), ∀ ans1 ans2, max_power stations1 r k = ok ans1 → max_power stations2 r k = ok ans2 →
          ans1 ≤ ans2) := by
    sorry

  /-- If max_power(stations, r, k) returns ans and max_power(rev, r, k) returns ans_rev, then ans = ans_rev.
    Preconditions: n = len(stations), 1 <= n <= 100000, for every i with 0 <= i < n, 0 <= stations[i] <= 100000, 0 <= r <= n-1, and 0 <= k <= 1000000000. Let rev be the slice of length n defined by rev[i] = stations[n-1-i] for every 0 <= i < n. -/
  theorem spec_11 (stations rev : Slice I64) (r k : I64) (n : Nat)
      (hn : stations.val.length = n) (hrev : rev.val = stations.val.reverse)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
      (hr0 : 0 ≤ r.val) (hr1 : r.val ≤ (n : Int) - 1)
      (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000) :
      ∀ ans ans_rev, max_power stations r k = ok ans → max_power rev r k = ok ans_rev →
        ans = ans_rev := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (stations rev : Slice I64) (r k : I64) (n : Nat)
        (hn : stations.val.length = n) (hrev : rev.val = stations.val.reverse)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
        (hr0 : 0 ≤ r.val) (hr1 : r.val ≤ (n : Int) - 1)
        (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000), ∀ ans ans_rev, max_power stations r k = ok ans → max_power rev r k = ok ans_rev →
          ans = ans_rev) := by
    sorry

  /-- Whenever max_power(stations, r, k) returns ans, there exists an allocation a = (a_0,...,a_{n-1}) of nonnegative integers with sum_{i=0}^{n-1} a_i = k such that min_{0<=j<n} P(a,j) = ans, where P(a,j) = sum over i with 0 <= i < n and |i-j| <= r of (stations[i] + a_i).
    Preconditions: n = len(stations), 1 <= n <= 100000, for every i with 0 <= i < n, 0 <= stations[i] <= 100000, 0 <= r <= n-1, and 0 <= k <= 1000000000. -/
  theorem spec_12 (stations : Slice I64) (r k : I64) (n : Nat)
      (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
      (hr0 : 0 ≤ r.val) (hr1 : r.val ≤ (n : Int) - 1)
      (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000) :
      ∀ ans, max_power stations r k = ok ans →
        ∃ a, IsAlloc stations k.val a ∧ minPower stations r.val a = ans := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (stations : Slice I64) (r k : I64) (n : Nat)
        (hn : stations.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hst : ∀ i, i < n → 0 ≤ stval stations i ∧ stval stations i ≤ 100000)
        (hr0 : 0 ≤ r.val) (hr1 : r.val ≤ (n : Int) - 1)
        (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 1000000000), ∀ ans, max_power stations r k = ok ans →
          ∃ a, IsAlloc stations k.val a ∧ minPower stations r.val a = ans) := by
    sorry

  end AegisSpec.MaxPower
