import Aegis.MinimumCost.Code.Funs

/-!
# Specifications of `Aegis.MinimumCost.minimum_cost`

LeetCode problem `minimum-cost-of-buying-candies-with-discount`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AegisSpec.MinimumCost

def costAt (cost : Slice Std.I64) (i : Nat) : Int := (cost.val[i]!).val

def costVals (cost : Slice Std.I64) : List Int := cost.val.map (fun x => x.val)

abbrev Group (n : Nat) := Fin n × Fin n × Fin n

structure Plan (n : Nat) where

  groups : List (Group n)

  distinct : (groups.flatMap (fun g => [g.1, g.2.1, g.2.2])).Nodup

namespace Plan

variable {n : Nat}

def indices (p : Plan n) : List (Fin n) :=
  p.groups.flatMap (fun g => [g.1, g.2.1, g.2.2])

def freeIndices (p : Plan n) : List (Fin n) := p.groups.map (fun g => g.1)

abbrev isFree (p : Plan n) (i : Fin n) : Prop := i ∈ p.freeIndices

abbrev isBought (p : Plan n) (i : Fin n) : Prop := ¬ p.isFree i

def numFree (p : Plan n) : Nat := p.groups.length

def numBought (p : Plan n) : Nat :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => p.isBought i)).card

def cost (p : Plan n) (cost : Slice Std.I64) : Int :=
  ∑ i : Fin n, if p.isFree i then 0 else costAt cost i

def Valid (p : Plan n) (cost : Slice Std.I64) : Prop :=
  ∀ g ∈ p.groups, costAt cost g.1 ≤ costAt cost g.2.1 ∧ costAt cost g.1 ≤ costAt cost g.2.2

def FreeAtRanks (p : Plan n) (σ : Fin n → Fin n) : Prop :=
  ∀ i : Fin n, p.isFree i ↔ ∃ k : Fin n, k.val % 3 = 2 ∧ σ k = i

end Plan

def IsMinPlanCost (n : Nat) (cost : Slice Std.I64) (m : Int) : Prop :=
  (∃ p : Plan n, p.Valid cost ∧ p.cost cost = m) ∧
    (∀ p : Plan n, p.Valid cost → m ≤ p.cost cost)

def IsNonIncreasingRearr (cost : Slice Std.I64) (d : List Int) : Prop :=
  d.length = cost.val.length ∧
    (∀ i j, i ≤ j → j < d.length → d[i]! ≥ d[j]!) ∧
      d.Perm (costVals cost)

def largestSum (d : List Int) (k : Nat) : Int := (d.take k).sum

def smallestSum (d : List Int) (k : Nat) : Int := (d.drop (d.length - k)).sum

def keptSum (d : List Int) : Int :=
  ((List.range d.length).map (fun i => if i % 3 = 2 then (0 : Int) else d[i]!)).sum

/-- Whenever the function returns a result r, r equals M, where M is the minimum total cost of buying all n candies under the discount rule: a purchase plan chooses an integer f with 0 <= f <= floor(n/3), partitions the index set {0,...,n-1} into f three-element groups and one possibly empty remaining group of size n - 3f, designates in each three-element group exactly two indices as bought and one as free with cost[free] <= cost[p] for each bought p in that group, and designates every index in the remaining group as bought; the cost of the plan is the sum of cost[i] over all bought indices; M is the minimum of this cost over all such plans.
  Preconditions: len(cost) = n, 1 <= n <= 100, and 1 <= cost[i] <= 100 for every i with 0 <= i < n. -/
theorem spec_1 (n : Nat) (cost : Slice Std.I64)
    (hlen : cost.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100)
    (r : Std.I64) (hres : Aegis.MinimumCost.minimum_cost cost = ok r) :
    IsMinPlanCost n cost r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Nat) (cost : Slice Std.I64)
    (hlen : cost.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100)
    (r : Std.I64) (hres : Aegis.MinimumCost.minimum_cost cost = ok r), IsMinPlanCost n cost r.val) := by
  sorry

/-- The function returns a result r (it does not fail, overflow, or panic).
  Preconditions: len(cost) = n, 1 <= n <= 100, and 1 <= cost[i] <= 100 for every i with 0 <= i < n. -/
theorem spec_2 (n : Nat) (cost : Slice Std.I64)
    (hlen : cost.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100) :
    ∃ r : Std.I64, Aegis.MinimumCost.minimum_cost cost = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Nat) (cost : Slice Std.I64)
    (hlen : cost.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100), ∃ r : Std.I64, Aegis.MinimumCost.minimum_cost cost = ok r) := by
  sorry

/-- Let n = len(cost), k = n - floor(n/3), and let d be a non-increasing rearrangement of the costs, so d[0] >= ... >= d[n-1] and d is a permutation of cost. Whenever the function returns a result r, r <= sum_{i=0}^{k-1} d[i], the sum of the k largest costs.
  Preconditions: len(cost) = n, 1 <= n <= 100, and 1 <= cost[i] <= 100 for every i with 0 <= i < n. -/
theorem spec_3 (n : Nat) (cost : Slice Std.I64) (d : List Int)
    (hlen : cost.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100)
    (hd : IsNonIncreasingRearr cost d)
    (r : Std.I64) (hres : Aegis.MinimumCost.minimum_cost cost = ok r) :
    r.val ≤ largestSum d (n - n / 3) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Nat) (cost : Slice Std.I64) (d : List Int)
    (hlen : cost.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100)
    (hd : IsNonIncreasingRearr cost d)
    (r : Std.I64) (hres : Aegis.MinimumCost.minimum_cost cost = ok r), r.val ≤ largestSum d (n - n / 3)) := by
  sorry

/-- Let n = len(cost), k = n - floor(n/3), and let d be a non-increasing rearrangement of the costs. Whenever the function returns a result r, r >= sum_{i=n-k}^{n-1} d[i], the sum of the k smallest costs.
  Preconditions: len(cost) = n, 1 <= n <= 100, and 1 <= cost[i] <= 100 for every i with 0 <= i < n. -/
theorem spec_4 (n : Nat) (cost : Slice Std.I64) (d : List Int)
    (hlen : cost.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100)
    (hd : IsNonIncreasingRearr cost d)
    (r : Std.I64) (hres : Aegis.MinimumCost.minimum_cost cost = ok r) :
    smallestSum d (n - n / 3) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Nat) (cost : Slice Std.I64) (d : List Int)
    (hlen : cost.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100)
    (hd : IsNonIncreasingRearr cost d)
    (r : Std.I64) (hres : Aegis.MinimumCost.minimum_cost cost = ok r), smallestSum d (n - n / 3) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists a valid purchase plan (as in spec_1) with exactly floor(n/3) free candies and n - floor(n/3) bought candies whose total bought cost is r.
  Preconditions: len(cost) = n, 1 <= n <= 100, and 1 <= cost[i] <= 100 for every i with 0 <= i < n. -/
theorem spec_5 (n : Nat) (cost : Slice Std.I64)
    (hlen : cost.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100)
    (r : Std.I64) (hres : Aegis.MinimumCost.minimum_cost cost = ok r) :
    ∃ p : Plan n, p.Valid cost ∧ p.numFree = n / 3 ∧ p.numBought = n - n / 3 ∧
      p.cost cost = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Nat) (cost : Slice Std.I64)
    (hlen : cost.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100)
    (r : Std.I64) (hres : Aegis.MinimumCost.minimum_cost cost = ok r), ∃ p : Plan n, p.Valid cost ∧ p.numFree = n / 3 ∧ p.numBought = n - n / 3 ∧
      p.cost cost = r.val) := by
  sorry

/-- Whenever the function returns a result r for cost and a result r' for cost', r = r'.
  Preconditions: len(cost) = len(cost') = n, 1 <= n <= 100, every cost[i] and cost'[i] lies in [1,100], and there is a bijection p on {0,...,n-1} such that cost'[i] = cost[p(i)] for every i with 0 <= i < n. -/
theorem spec_6 (n : Nat) (cost cost' : Slice Std.I64) (p : Fin n → Fin n)
    (hlen : cost.val.length = n) (hlen' : cost'.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100)
    (hcost' : ∀ i, i < n → 1 ≤ costAt cost' i ∧ costAt cost' i ≤ 100)
    (hp : Function.Bijective p)
    (hperm : ∀ i (h : i < n), costAt cost' i = costAt cost (p ⟨i, h⟩))
    (r r' : Std.I64) (hres : Aegis.MinimumCost.minimum_cost cost = ok r)
    (hres' : Aegis.MinimumCost.minimum_cost cost' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Nat) (cost cost' : Slice Std.I64) (p : Fin n → Fin n)
    (hlen : cost.val.length = n) (hlen' : cost'.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100)
    (hcost' : ∀ i, i < n → 1 ≤ costAt cost' i ∧ costAt cost' i ≤ 100)
    (hp : Function.Bijective p)
    (hperm : ∀ i (h : i < n), costAt cost' i = costAt cost (p ⟨i, h⟩))
    (r r' : Std.I64) (hres : Aegis.MinimumCost.minimum_cost cost = ok r)
    (hres' : Aegis.MinimumCost.minimum_cost cost' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r for cost and a result r' for cost', r' = r + t * (n - floor(n/3)).
  Preconditions: len(cost) = len(cost') = n, 1 <= n <= 100, every cost[i] and cost'[i] lies in [1,100], and there is an integer t such that cost'[i] = cost[i] + t for every i with 0 <= i < n. -/
theorem spec_7 (n : Nat) (cost cost' : Slice Std.I64) (t : Int)
    (hlen : cost.val.length = n) (hlen' : cost'.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100)
    (hcost' : ∀ i, i < n → 1 ≤ costAt cost' i ∧ costAt cost' i ≤ 100)
    (hshift : ∀ i, i < n → costAt cost' i = costAt cost i + t)
    (r r' : Std.I64) (hres : Aegis.MinimumCost.minimum_cost cost = ok r)
    (hres' : Aegis.MinimumCost.minimum_cost cost' = ok r') :
    r'.val = r.val + t * ((n - n / 3 : Nat) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Nat) (cost cost' : Slice Std.I64) (t : Int)
    (hlen : cost.val.length = n) (hlen' : cost'.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100)
    (hcost' : ∀ i, i < n → 1 ≤ costAt cost' i ∧ costAt cost' i ≤ 100)
    (hshift : ∀ i, i < n → costAt cost' i = costAt cost i + t)
    (r r' : Std.I64) (hres : Aegis.MinimumCost.minimum_cost cost = ok r)
    (hres' : Aegis.MinimumCost.minimum_cost cost' = ok r'), r'.val = r.val + t * ((n - n / 3 : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r for cost and a result r' for cost', r' = c * r.
  Preconditions: len(cost) = len(cost') = n, 1 <= n <= 100, every cost[i] and cost'[i] lies in [1,100], and there is an integer c >= 1 such that cost'[i] = c * cost[i] for every i with 0 <= i < n. -/
theorem spec_8 (n : Nat) (cost cost' : Slice Std.I64) (c : Int)
    (hlen : cost.val.length = n) (hlen' : cost'.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100)
    (hcost' : ∀ i, i < n → 1 ≤ costAt cost' i ∧ costAt cost' i ≤ 100)
    (hc : 1 ≤ c)
    (hscale : ∀ i, i < n → costAt cost' i = c * costAt cost i)
    (r r' : Std.I64) (hres : Aegis.MinimumCost.minimum_cost cost = ok r)
    (hres' : Aegis.MinimumCost.minimum_cost cost' = ok r') :
    r'.val = c * r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Nat) (cost cost' : Slice Std.I64) (c : Int)
    (hlen : cost.val.length = n) (hlen' : cost'.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100)
    (hcost' : ∀ i, i < n → 1 ≤ costAt cost' i ∧ costAt cost' i ≤ 100)
    (hc : 1 ≤ c)
    (hscale : ∀ i, i < n → costAt cost' i = c * costAt cost i)
    (r r' : Std.I64) (hres : Aegis.MinimumCost.minimum_cost cost = ok r)
    (hres' : Aegis.MinimumCost.minimum_cost cost' = ok r'), r'.val = c * r.val) := by
  sorry

/-- Let d be a non-increasing rearrangement of the costs, so len(d) = n and d[0] >= ... >= d[n-1] and d is a permutation of cost. Whenever the function returns a result r, r = sum_{i=0}^{n-1} e[i], where e[i] = d[i] if i mod 3 is not 2, and e[i] = 0 if i mod 3 = 2.
  Preconditions: len(cost) = n, 1 <= n <= 100, and 1 <= cost[i] <= 100 for every i with 0 <= i < n. -/
theorem spec_9 (n : Nat) (cost : Slice Std.I64) (d : List Int)
    (hlen : cost.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100)
    (hd : IsNonIncreasingRearr cost d)
    (r : Std.I64) (hres : Aegis.MinimumCost.minimum_cost cost = ok r) :
    r.val = keptSum d := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Nat) (cost : Slice Std.I64) (d : List Int)
    (hlen : cost.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100)
    (hd : IsNonIncreasingRearr cost d)
    (r : Std.I64) (hres : Aegis.MinimumCost.minimum_cost cost = ok r), r.val = keptSum d) := by
  sorry

/-- Whenever the function returns a result r, there exists a valid purchase plan attaining total cost r in which, after ordering the candies by non-increasing cost with ties broken arbitrarily as d[0] >= ... >= d[n-1], the free candies are exactly the candies at 0-based ranks i with i mod 3 = 2 and i < n, and all other candies are bought.
  Preconditions: len(cost) = n, 1 <= n <= 100, and 1 <= cost[i] <= 100 for every i with 0 <= i < n. -/
theorem spec_10 (n : Nat) (cost : Slice Std.I64)
    (hlen : cost.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100)
    (r : Std.I64) (hres : Aegis.MinimumCost.minimum_cost cost = ok r) :
    ∃ (σ : Fin n → Fin n), Function.Bijective σ ∧
        (∀ i j : Fin n, i ≤ j → costAt cost (σ i) ≥ costAt cost (σ j)) ∧
      ∃ p : Plan n, p.Valid cost ∧ p.FreeAtRanks σ ∧ p.cost cost = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Nat) (cost : Slice Std.I64)
    (hlen : cost.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
    (hcost : ∀ i, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 100)
    (r : Std.I64) (hres : Aegis.MinimumCost.minimum_cost cost = ok r), ∃ (σ : Fin n → Fin n), Function.Bijective σ ∧
        (∀ i j : Fin n, i ≤ j → costAt cost (σ i) ≥ costAt cost (σ j)) ∧
      ∃ p : Plan n, p.Valid cost ∧ p.FreeAtRanks σ ∧ p.cost cost = r.val) := by
  sorry

end AegisSpec.MinimumCost
