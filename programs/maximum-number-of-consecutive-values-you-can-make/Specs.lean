import Aegis.GetMaximumConsecutive.Code.Funs

/-!
# Specifications of `Aegis.GetMaximumConsecutive.get_maximum_consecutive`

LeetCode problem `maximum-number-of-consecutive-values-you-can-make`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.GetMaximumConsecutive

  def IsSubsetSum (coins : List Std.I64) (x : Int) : Prop :=
    ∃ S : Finset (Fin coins.length), x = S.sum (fun i => (coins.get i).val)

  def IsMaxConsecutive (coins : List Std.I64) (r : Int) : Prop :=
    1 ≤ r ∧ (∀ x, 0 ≤ x → x < r → IsSubsetSum coins x) ∧
      (∀ k, 1 ≤ k → (∀ x, 0 ≤ x → x < k → IsSubsetSum coins x) → k ≤ r)

  def IsLeastNonSubsetSum (coins : List Std.I64) (r : Int) : Prop :=
    0 ≤ r ∧ ¬ IsSubsetSum coins r ∧ ∀ x, 0 ≤ x → ¬ IsSubsetSum coins x → r ≤ x

  def totalSum (coins : List Std.I64) : Int := (coins.map fun c => c.val).sum

  def IsSortedValues (coins : List Std.I64) (a : List Int) : Prop :=
    a.Perm (coins.map fun c => c.val) ∧ a.Pairwise (· ≤ ·)

  def prefixSum (a : List Int) (j : Nat) : Int := (a.take j).sum

  def JumpsAt (a : List Int) (j : Nat) : Prop :=
    ∃ v, a[j]? = some v ∧ prefixSum a j + 1 < v

  def IsFirstJump (a : List Int) (m : Nat) : Prop :=
    m ≤ a.length ∧ (∀ j, j < m → ¬ JumpsAt a j) ∧ (m < a.length → JumpsAt a m)

  /-- For every such coins, the function returns a result r; it does not fail by panic, overflow, or out-of-bounds access.
    Preconditions: coins is a slice of 64-bit integers with 1 <= len(coins) <= 40000 and, for every index i with 0 <= i < len(coins), 1 <= coins[i] <= 40000. -/
  theorem spec_1 (coins : Slice Std.I64)
      (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
      (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000) :
      ∃ r, Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (coins : Slice Std.I64)
        (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
        (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000), ∃ r, Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r equals the largest integer k with k >= 1 such that every integer x satisfying 0 <= x < k is equal to sum_{i in S} coins[i] for some set S of distinct indices with 0 <= i < len(coins) for every i in S. Equivalently, r is the smallest nonnegative integer that is not equal to such a subset sum.
    Preconditions: coins is a slice of 64-bit integers with 1 <= len(coins) <= 40000 and, for every index i with 0 <= i < len(coins), 1 <= coins[i] <= 40000. -/
  theorem spec_2 (coins : Slice Std.I64)
      (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
      (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
      (r : Std.I64)
      (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r) :
      IsMaxConsecutive coins.val r.val ∧ IsLeastNonSubsetSum coins.val r.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (coins : Slice Std.I64)
        (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
        (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
        (r : Std.I64)
        (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r), IsMaxConsecutive coins.val r.val ∧ IsLeastNonSubsetSum coins.val r.val) := by
    sorry

  /-- Whenever the function returns a result r, r >= 1.
    Preconditions: coins is a slice of 64-bit integers with 1 <= len(coins) <= 40000 and, for every index i with 0 <= i < len(coins), 1 <= coins[i] <= 40000. -/
  theorem spec_3 (coins : Slice Std.I64)
      (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
      (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
      (r : Std.I64)
      (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r) :
      1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (coins : Slice Std.I64)
        (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
        (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
        (r : Std.I64)
        (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r), 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= 1 + sum_{i=0}^{len(coins)-1} coins[i].
    Preconditions: coins is a slice of 64-bit integers with 1 <= len(coins) <= 40000 and, for every index i with 0 <= i < len(coins), 1 <= coins[i] <= 40000. -/
  theorem spec_4 (coins : Slice Std.I64)
      (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
      (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
      (r : Std.I64)
      (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r) :
      r.val ≤ 1 + totalSum coins.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (coins : Slice Std.I64)
        (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
        (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
        (r : Std.I64)
        (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r), r.val ≤ 1 + totalSum coins.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 1.
    Preconditions: coins is a slice of 64-bit integers with 1 <= len(coins) <= 40000, for every index i with 0 <= i < len(coins), 1 <= coins[i] <= 40000, and for every index i with 0 <= i < len(coins), coins[i] != 1. -/
  theorem spec_5 (coins : Slice Std.I64)
      (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
      (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
      (hnoOne : ∀ x ∈ coins.val, x.val ≠ 1)
      (r : Std.I64)
      (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r) :
      r.val = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (coins : Slice Std.I64)
        (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
        (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
        (hnoOne : ∀ x ∈ coins.val, x.val ≠ 1)
        (r : Std.I64)
        (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r), r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, r >= 2.
    Preconditions: coins is a slice of 64-bit integers with 1 <= len(coins) <= 40000, for every index i with 0 <= i < len(coins), 1 <= coins[i] <= 40000, and there exists an index i with 0 <= i < len(coins) and coins[i] = 1. -/
  theorem spec_6 (coins : Slice Std.I64)
      (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
      (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
      (hOne : ∃ x ∈ coins.val, x.val = 1)
      (r : Std.I64)
      (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r) :
      2 ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (coins : Slice Std.I64)
        (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
        (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
        (hOne : ∃ x ∈ coins.val, x.val = 1)
        (r : Std.I64)
        (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r), 2 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = len(coins) + 1.
    Preconditions: coins is a slice of 64-bit integers with 1 <= len(coins) <= 40000, for every index i with 0 <= i < len(coins), 1 <= coins[i] <= 40000, and for every index i with 0 <= i < len(coins), coins[i] = 1. -/
  theorem spec_7 (coins : Slice Std.I64)
      (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
      (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
      (hallOne : ∀ x ∈ coins.val, x.val = 1)
      (r : Std.I64)
      (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r) :
      r.val = (coins.val.length : Int) + 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (coins : Slice Std.I64)
        (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
        (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
        (hallOne : ∀ x ∈ coins.val, x.val = 1)
        (r : Std.I64)
        (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r), r.val = (coins.val.length : Int) + 1) := by
    sorry

  /-- Whenever the function returns a result r, there is no set S of distinct indices with 0 <= i < len(coins) for every i in S such that sum_{i in S} coins[i] = r.
    Preconditions: coins is a slice of 64-bit integers with 1 <= len(coins) <= 40000 and, for every index i with 0 <= i < len(coins), 1 <= coins[i] <= 40000. -/
  theorem spec_8 (coins : Slice Std.I64)
      (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
      (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
      (r : Std.I64)
      (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r) :
      ¬ IsSubsetSum coins.val r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (coins : Slice Std.I64)
        (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
        (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
        (r : Std.I64)
        (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r), ¬ IsSubsetSum coins.val r.val) := by
    sorry

  /-- If get_maximum_consecutive(coins) returns r and get_maximum_consecutive(coins2) returns r2, then r = r2.
    Preconditions: coins and coins2 are slices of 64-bit integers, both satisfy 1 <= len(coins), len(coins2) <= 40000 and all their entries lie in [1,40000], and coins2 is a permutation of coins (same length and same multiset of values). -/
  theorem spec_9 (coins coins2 : Slice Std.I64)
      (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
      (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
      (hlen1' : 1 ≤ coins2.val.length) (hlen2' : coins2.val.length ≤ 40000)
      (hval' : ∀ x ∈ coins2.val, 1 ≤ x.val ∧ x.val ≤ 40000)
      (hperm : coins2.val.Perm coins.val)
      (r r2 : Std.I64)
      (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r)
      (hr2 : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins2 = ok r2) :
      r.val = r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (coins coins2 : Slice Std.I64)
        (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
        (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
        (hlen1' : 1 ≤ coins2.val.length) (hlen2' : coins2.val.length ≤ 40000)
        (hval' : ∀ x ∈ coins2.val, 1 ≤ x.val ∧ x.val ≤ 40000)
        (hperm : coins2.val.Perm coins.val)
        (r r2 : Std.I64)
        (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r)
        (hr2 : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins2 = ok r2), r.val = r2.val) := by
    sorry

  /-- If get_maximum_consecutive(coins) returns r and get_maximum_consecutive(coins2) returns r2, then r2 >= r.
    Preconditions: coins and coins2 satisfy the input constraints, len(coins) < 40000, len(coins2) = len(coins) + 1, and there is a value v with 1 <= v <= 40000 such that coins2[i] = coins[i] for 0 <= i < len(coins) and coins2[len(coins)] = v. -/
  theorem spec_10 (coins coins2 : Slice Std.I64)
      (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
      (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
      (hlen1' : 1 ≤ coins2.val.length) (hlen2' : coins2.val.length ≤ 40000)
      (hval' : ∀ x ∈ coins2.val, 1 ≤ x.val ∧ x.val ≤ 40000)
      (hlt : coins.val.length < 40000)
      (hlen : coins2.val.length = coins.val.length + 1)
      (v : Std.I64) (hv1 : 1 ≤ v.val) (hv2 : v.val ≤ 40000)
      (happend : coins2.val = coins.val ++ [v])
      (r r2 : Std.I64)
      (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r)
      (hr2 : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins2 = ok r2) :
      r.val ≤ r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (coins coins2 : Slice Std.I64)
        (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
        (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
        (hlen1' : 1 ≤ coins2.val.length) (hlen2' : coins2.val.length ≤ 40000)
        (hval' : ∀ x ∈ coins2.val, 1 ≤ x.val ∧ x.val ≤ 40000)
        (hlt : coins.val.length < 40000)
        (hlen : coins2.val.length = coins.val.length + 1)
        (v : Std.I64) (hv1 : 1 ≤ v.val) (hv2 : v.val ≤ 40000)
        (happend : coins2.val = coins.val ++ [v])
        (r r2 : Std.I64)
        (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r)
        (hr2 : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins2 = ok r2), r.val ≤ r2.val) := by
    sorry

  /-- If get_maximum_consecutive(coins) returns r, get_maximum_consecutive(coins2) returns r2, and 1 <= v <= r, then r2 >= r + v.
    Preconditions: coins and coins2 satisfy the input constraints, len(coins) < 40000, len(coins2) = len(coins) + 1, and there is a value v with 1 <= v <= 40000 such that coins2[i] = coins[i] for 0 <= i < len(coins) and coins2[len(coins)] = v. -/
  theorem spec_11 (coins coins2 : Slice Std.I64)
      (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
      (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
      (hlen1' : 1 ≤ coins2.val.length) (hlen2' : coins2.val.length ≤ 40000)
      (hval' : ∀ x ∈ coins2.val, 1 ≤ x.val ∧ x.val ≤ 40000)
      (hlt : coins.val.length < 40000)
      (hlen : coins2.val.length = coins.val.length + 1)
      (v : Std.I64) (hv1 : 1 ≤ v.val) (hv2 : v.val ≤ 40000)
      (happend : coins2.val = coins.val ++ [v])
      (r r2 : Std.I64)
      (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r)
      (hr2 : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins2 = ok r2)
      (hvle : v.val ≤ r.val) :
      r.val + v.val ≤ r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (coins coins2 : Slice Std.I64)
        (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
        (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
        (hlen1' : 1 ≤ coins2.val.length) (hlen2' : coins2.val.length ≤ 40000)
        (hval' : ∀ x ∈ coins2.val, 1 ≤ x.val ∧ x.val ≤ 40000)
        (hlt : coins.val.length < 40000)
        (hlen : coins2.val.length = coins.val.length + 1)
        (v : Std.I64) (hv1 : 1 ≤ v.val) (hv2 : v.val ≤ 40000)
        (happend : coins2.val = coins.val ++ [v])
        (r r2 : Std.I64)
        (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r)
        (hr2 : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins2 = ok r2)
        (hvle : v.val ≤ r.val), r.val + v.val ≤ r2.val) := by
    sorry

  /-- Whenever the function returns a result r, the equality r = 1 + sum_{i=0}^{len(coins)-1} coins[i] holds if and only if every integer x with 0 <= x <= sum_{i=0}^{len(coins)-1} coins[i] is equal to sum_{i in S} coins[i] for some set S of distinct indices with 0 <= i < len(coins) for every i in S.
    Preconditions: coins is a slice of 64-bit integers with 1 <= len(coins) <= 40000 and, for every index i with 0 <= i < len(coins), 1 <= coins[i] <= 40000. -/
  theorem spec_12 (coins : Slice Std.I64)
      (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
      (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
      (r : Std.I64)
      (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r) :
      (r.val = 1 + totalSum coins.val ↔
        ∀ x, 0 ≤ x → x ≤ totalSum coins.val → IsSubsetSum coins.val x) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (coins : Slice Std.I64)
        (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
        (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
        (r : Std.I64)
        (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r), (r.val = 1 + totalSum coins.val ↔
          ∀ x, 0 ≤ x → x ≤ totalSum coins.val → IsSubsetSum coins.val x)) := by
    sorry

  /-- If get_maximum_consecutive(coins) returns r, get_maximum_consecutive(coins2) returns r2, and v > r, then r2 = r.
    Preconditions: coins and coins2 satisfy the input constraints, len(coins) < 40000, len(coins2) = len(coins) + 1, and there is a value v with 1 <= v <= 40000 such that coins2[i] = coins[i] for 0 <= i < len(coins) and coins2[len(coins)] = v. -/
  theorem spec_13 (coins coins2 : Slice Std.I64)
      (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
      (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
      (hlen1' : 1 ≤ coins2.val.length) (hlen2' : coins2.val.length ≤ 40000)
      (hval' : ∀ x ∈ coins2.val, 1 ≤ x.val ∧ x.val ≤ 40000)
      (hlt : coins.val.length < 40000)
      (hlen : coins2.val.length = coins.val.length + 1)
      (v : Std.I64) (hv1 : 1 ≤ v.val) (hv2 : v.val ≤ 40000)
      (happend : coins2.val = coins.val ++ [v])
      (r r2 : Std.I64)
      (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r)
      (hr2 : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins2 = ok r2)
      (hvg : r.val < v.val) :
      r2.val = r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (coins coins2 : Slice Std.I64)
        (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
        (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
        (hlen1' : 1 ≤ coins2.val.length) (hlen2' : coins2.val.length ≤ 40000)
        (hval' : ∀ x ∈ coins2.val, 1 ≤ x.val ∧ x.val ≤ 40000)
        (hlt : coins.val.length < 40000)
        (hlen : coins2.val.length = coins.val.length + 1)
        (v : Std.I64) (hv1 : 1 ≤ v.val) (hv2 : v.val ≤ 40000)
        (happend : coins2.val = coins.val ++ [v])
        (r r2 : Std.I64)
        (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r)
        (hr2 : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins2 = ok r2)
        (hvg : r.val < v.val), r2.val = r.val) := by
    sorry

  /-- Let a be the nondecreasing sort of coins, and let p_j = sum_{i=0}^{j-1} a_i, with p_0 = 0. Let m be the least index j with 0 <= j < len(a) and a_j > 1 + p_j; if no such j exists, let m = len(a). Whenever the function returns a result r, r = 1 + p_m.
    Preconditions: coins is a slice of 64-bit integers with 1 <= len(coins) <= 40000 and, for every index i with 0 <= i < len(coins), 1 <= coins[i] <= 40000. -/
  theorem spec_14 (coins : Slice Std.I64)
      (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
      (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
      (a : List Int)
      (hsorted : IsSortedValues coins.val a)
      (m : Nat) (hm : IsFirstJump a m)
      (r : Std.I64)
      (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r) :
      r.val = 1 + prefixSum a m := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (coins : Slice Std.I64)
        (hlen1 : 1 ≤ coins.val.length) (hlen2 : coins.val.length ≤ 40000)
        (hval : ∀ x ∈ coins.val, 1 ≤ x.val ∧ x.val ≤ 40000)
        (a : List Int)
        (hsorted : IsSortedValues coins.val a)
        (m : Nat) (hm : IsFirstJump a m)
        (r : Std.I64)
        (hr : Aegis.GetMaximumConsecutive.get_maximum_consecutive coins = ok r), r.val = 1 + prefixSum a m) := by
    sorry

  end AegisSpec.GetMaximumConsecutive
