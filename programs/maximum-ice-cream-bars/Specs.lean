import Aegis.MaxIceCream.Code.Funs

/-!
# Specifications of `Aegis.MaxIceCream.max_ice_cream`

LeetCode problem `maximum-ice-cream-bars`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxIceCream

open Aegis.MaxIceCream

def costsOf (costs : Slice Std.I64) : List Int := costs.val.map (fun c => c.val)

def CanBuy (l : List Int) (c : Int) (k : Nat) : Prop :=
  ∃ S : Finset (Fin l.length), S.card = k ∧ S.sum (fun i => l.get i) ≤ c

def maxBarsSet (costs : Slice Std.I64) (coins : Std.I64) : Set Int :=
  {k | 0 ≤ k ∧ k ≤ ((costsOf costs).length : Int) ∧ CanBuy (costsOf costs) coins.val k.toNat}

def IsMaxBars (costs : Slice Std.I64) (coins : Std.I64) (r : Std.I64) : Prop :=
  IsGreatest (maxBarsSet costs coins) r.val

def sortedCosts (l : List Int) : List Int := l.insertionSort (· ≤ ·)

def sumFirst (l : List Int) (k : Nat) : Int := (l.take k).sum

def countAffordable (l : List Int) (c : Int) : Nat := (l.filter (fun x => decide (x ≤ c))).length

/-- The function returns a result r, and r is the maximum of the set of all k with 0 <= k <= len(costs) for which there exists a set S of exactly k distinct indices, each satisfying 0 <= i < len(costs), such that the sum of costs[i] over i in S is at most coins. In other words, r is the largest number of bars the boy can buy, where buying a bar costs its price, each bar is bought at most once, and the total spent may not exceed coins.
  Preconditions: 1 <= len(costs); for every i with 0 <= i < len(costs), 1 <= costs[i] <= 100000; 1 <= coins <= 100000000. -/
theorem spec_1 (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000) :
    ∃ r : Std.I64, max_ice_cream costs coins = ok r ∧ IsMaxBars costs coins r := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000), ∃ r : Std.I64, max_ice_cream costs coins = ok r ∧ IsMaxBars costs coins r) := by
  sorry

/-- The function returns a result r (it never fails, in particular it does not overflow or index out of bounds), and 0 <= r <= len(costs).
  Preconditions: 1 <= len(costs); for every i with 0 <= i < len(costs), 1 <= costs[i] <= 100000; 1 <= coins <= 100000000. -/
theorem spec_2 (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000) :
    ∃ r : Std.I64,
      max_ice_cream costs coins = ok r ∧ 0 ≤ r.val ∧ r.val ≤ ((costsOf costs).length : Int) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000), ∃ r : Std.I64,
      max_ice_cream costs coins = ok r ∧ 0 ≤ r.val ∧ r.val ≤ ((costsOf costs).length : Int)) := by
  sorry

/-- The function returns a result r, and there exist r distinct indices i_1, ..., i_r, each satisfying 0 <= i_j < len(costs), such that costs[i_1] + ... + costs[i_r] <= coins. (For r = 0 the family is empty and the sum is 0.)
  Preconditions: 1 <= len(costs); for every i with 0 <= i < len(costs), 1 <= costs[i] <= 100000; 1 <= coins <= 100000000. -/
theorem spec_3 (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000) :
    ∃ r : Std.I64,
      max_ice_cream costs coins = ok r ∧
        ∃ S : Finset (Fin (costsOf costs).length),
          S.card = r.val.toNat ∧ S.sum (fun i => (costsOf costs).get i) ≤ coins.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000), ∃ r : Std.I64,
      max_ice_cream costs coins = ok r ∧
        ∃ S : Finset (Fin (costsOf costs).length),
          S.card = r.val.toNat ∧ S.sum (fun i => (costsOf costs).get i) ≤ coins.val) := by
  sorry

/-- The function returns a result r, and for every set S of r + 1 distinct indices with 0 <= i < len(costs) for each i in S, the sum of costs[i] over i in S is strictly greater than coins. (When r = len(costs) no such set S exists and the condition holds vacuously.)
  Preconditions: 1 <= len(costs); for every i with 0 <= i < len(costs), 1 <= costs[i] <= 100000; 1 <= coins <= 100000000. -/
theorem spec_4 (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000) :
    ∃ r : Std.I64,
      max_ice_cream costs coins = ok r ∧
        ∀ S : Finset (Fin (costsOf costs).length),
          S.card = r.val.toNat + 1 → coins.val < S.sum (fun i => (costsOf costs).get i) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000), ∃ r : Std.I64,
      max_ice_cream costs coins = ok r ∧
        ∀ S : Finset (Fin (costsOf costs).length),
          S.card = r.val.toNat + 1 → coins.val < S.sum (fun i => (costsOf costs).get i)) := by
  sorry

/-- The function returns a result r, and if s_0 <= s_1 <= ... <= s_{len(costs)-1} is the multiset of values costs[0], ..., costs[len(costs)-1] arranged in non-decreasing order, then s_0 + s_1 + ... + s_{r-1} <= coins (the empty sum when r = 0 is 0).
  Preconditions: 1 <= len(costs); for every i with 0 <= i < len(costs), 1 <= costs[i] <= 100000; 1 <= coins <= 100000000. -/
theorem spec_5 (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000) :
    ∃ r : Std.I64,
      max_ice_cream costs coins = ok r ∧
        sumFirst (sortedCosts (costsOf costs)) r.val.toNat ≤ coins.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000), ∃ r : Std.I64,
      max_ice_cream costs coins = ok r ∧
        sumFirst (sortedCosts (costsOf costs)) r.val.toNat ≤ coins.val) := by
  sorry

/-- The function returns a result r, and if s_0 <= s_1 <= ... <= s_{len(costs)-1} is the multiset of values costs[0], ..., costs[len(costs)-1] in non-decreasing order and r < len(costs), then s_0 + s_1 + ... + s_r > coins.
  Preconditions: 1 <= len(costs); for every i with 0 <= i < len(costs), 1 <= costs[i] <= 100000; 1 <= coins <= 100000000. -/
theorem spec_6 (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000) :
    ∃ r : Std.I64,
      max_ice_cream costs coins = ok r ∧
        (r.val < ((costsOf costs).length : Int) →
          coins.val < sumFirst (sortedCosts (costsOf costs)) (r.val.toNat + 1)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000), ∃ r : Std.I64,
      max_ice_cream costs coins = ok r ∧
        (r.val < ((costsOf costs).length : Int) →
          coins.val < sumFirst (sortedCosts (costsOf costs)) (r.val.toNat + 1))) := by
  sorry

/-- The function returns a result r, and r <= coins.
  Preconditions: 1 <= len(costs); for every i with 0 <= i < len(costs), 1 <= costs[i] <= 100000; 1 <= coins <= 100000000. -/
theorem spec_7 (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000) :
    ∃ r : Std.I64, max_ice_cream costs coins = ok r ∧ r.val ≤ coins.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000), ∃ r : Std.I64, max_ice_cream costs coins = ok r ∧ r.val ≤ coins.val) := by
  sorry

/-- The function returns a result r, and r <= the number of indices i with 0 <= i < len(costs) and costs[i] <= coins.
  Preconditions: 1 <= len(costs); for every i with 0 <= i < len(costs), 1 <= costs[i] <= 100000; 1 <= coins <= 100000000. -/
theorem spec_8 (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000) :
    ∃ r : Std.I64,
      max_ice_cream costs coins = ok r ∧
        r.val ≤ ((countAffordable (costsOf costs) coins.val : Nat) : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000), ∃ r : Std.I64,
      max_ice_cream costs coins = ok r ∧
        r.val ≤ ((countAffordable (costsOf costs) coins.val : Nat) : Int)) := by
  sorry

/-- The function returns a result r, and r = 0 if and only if costs[i] > coins for every i with 0 <= i < len(costs).
  Preconditions: 1 <= len(costs); for every i with 0 <= i < len(costs), 1 <= costs[i] <= 100000; 1 <= coins <= 100000000. -/
theorem spec_9 (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000) :
    ∃ r : Std.I64,
      max_ice_cream costs coins = ok r ∧
        (r.val = 0 ↔ ∀ x ∈ costsOf costs, coins.val < x) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000), ∃ r : Std.I64,
      max_ice_cream costs coins = ok r ∧
        (r.val = 0 ↔ ∀ x ∈ costsOf costs, coins.val < x)) := by
  sorry

/-- The function returns a result r, and r = len(costs) if and only if costs[0] + costs[1] + ... + costs[len(costs)-1] <= coins.
  Preconditions: 1 <= len(costs); for every i with 0 <= i < len(costs), 1 <= costs[i] <= 100000; 1 <= coins <= 100000000. -/
theorem spec_10 (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000) :
    ∃ r : Std.I64,
      max_ice_cream costs coins = ok r ∧
        (r.val = ((costsOf costs).length : Int) ↔ (costsOf costs).sum ≤ coins.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000), ∃ r : Std.I64,
      max_ice_cream costs coins = ok r ∧
        (r.val = ((costsOf costs).length : Int) ↔ (costsOf costs).sum ≤ coins.val)) := by
  sorry

/-- The function returns a result r, and for every k with 0 <= k <= r there exists a set S of exactly k distinct indices, each satisfying 0 <= i < len(costs), such that the sum of costs[i] over i in S is at most coins.
  Preconditions: 1 <= len(costs); for every i with 0 <= i < len(costs), 1 <= costs[i] <= 100000; 1 <= coins <= 100000000. -/
theorem spec_11 (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000) :
    ∃ r : Std.I64,
      max_ice_cream costs coins = ok r ∧
        ∀ k : Nat, k ≤ r.val.toNat → CanBuy (costsOf costs) coins.val k := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (costs : Slice Std.I64) (coins : Std.I64)
    (hlen : 1 ≤ (costsOf costs).length)
    (hcosts : ∀ x ∈ costsOf costs, 1 ≤ x ∧ x ≤ 100000)
    (hcoins : 1 ≤ coins.val ∧ coins.val ≤ 100000000), ∃ r : Std.I64,
      max_ice_cream costs coins = ok r ∧
        ∀ k : Nat, k ≤ r.val.toNat → CanBuy (costsOf costs) coins.val k) := by
  sorry

end AegisSpec.MaxIceCream
