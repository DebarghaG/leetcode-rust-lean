import Aegis.MinCostClimbingStairs.Code.Funs

/-!
# Specifications of `Aegis.MinCostClimbingStairs.min_cost_climbing_stairs`

LeetCode problem `min-cost-climbing-stairs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinCostClimbingStairs

  def costAt (cost : Slice I64) (i : Nat) : Int :=
    match cost.val[i]? with
    | some x => x.val
    | none => 0

  def pathNth (p : List Nat) (j : Nat) : Nat :=
    (p[j]?).getD 0

  def pathCost (cost : Slice I64) (p : List Nat) : Int :=
    (p.map (costAt cost)).sum

  def IsValidPath (n : Nat) (p : List Nat) : Prop :=
    (p.head? = some 0 ∨ p.head? = some 1) ∧
      (∀ j, j + 1 < p.length →
        pathNth p (j + 1) = pathNth p j + 1 ∨ pathNth p (j + 1) = pathNth p j + 2) ∧
      (p.getLast? = some (n - 1) ∨ p.getLast? = some (n - 2))

  def IsMinPathCost (cost : Slice I64) (r : Int) : Prop :=
    (∃ p, IsValidPath cost.val.length p ∧ pathCost cost p = r) ∧
      (∀ p, IsValidPath cost.val.length p → r ≤ pathCost cost p)

  def indexSum (cost : Slice I64) (sel : Nat → Bool) : Int :=
    ((List.range cost.val.length).filter sel).map (costAt cost) |>.sum

  def sumEvenCost (cost : Slice I64) : Int :=
    indexSum cost (fun i => i % 2 == 0)

  def sumOddCost (cost : Slice I64) : Int :=
    indexSum cost (fun i => i % 2 == 1)

  /-- The function returns a result r (it does not fail). A valid path is a sequence of indices p_0, p_1, ..., p_k with k >= 0 such that: (1) p_0 = 0 or p_0 = 1; (2) for every j with 0 <= j < k, p_{j+1} - p_j is either 1 or 2; (3) p_k = n-1 or p_k = n-2. The cost of a valid path is the sum of cost[p_j] for 0 <= j <= k. Then r is the minimum cost among all valid paths.
    Preconditions: cost is a slice of 64-bit integers. Let n = len(cost). We have 2 <= n <= 1000, and for every i with 0 <= i < n, 0 <= cost[i] <= 999. -/
  theorem spec_1 (cost : Slice I64)
      (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
      (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999) :
      ∃ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r ∧
        IsMinPathCost cost r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (cost : Slice I64)
        (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
        (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999), ∃ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r ∧
          IsMinPathCost cost r.val) := by
    sorry

  /-- The returned value r satisfies 0 <= r <= 999 * len(cost).
    Preconditions: cost is a slice of 64-bit integers. Let n = len(cost). We have 2 <= n <= 1000, and for every i with 0 <= i < n, 0 <= cost[i] <= 999. -/
  theorem spec_2 (cost : Slice I64)
      (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
      (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999) :
      ∀ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r →
        0 ≤ r.val ∧ r.val ≤ 999 * (cost.val.length : Int) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (cost : Slice I64)
        (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
        (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999), ∀ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r →
          0 ≤ r.val ∧ r.val ≤ 999 * (cost.val.length : Int)) := by
    sorry

  /-- Let S_even = sum of cost[i] for all even i with 0 <= i < len(cost), and S_odd = sum of cost[i] for all odd i with 0 <= i < len(cost). The returned value r satisfies r <= S_even and r <= S_odd.
    Preconditions: cost is a slice of 64-bit integers. Let n = len(cost). We have 2 <= n <= 1000, and for every i with 0 <= i < n, 0 <= cost[i] <= 999. -/
  theorem spec_3 (cost : Slice I64)
      (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
      (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999) :
      ∀ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r →
        r.val ≤ sumEvenCost cost ∧ r.val ≤ sumOddCost cost := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (cost : Slice I64)
        (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
        (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999), ∀ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r →
          r.val ≤ sumEvenCost cost ∧ r.val ≤ sumOddCost cost) := by
    sorry

  /-- The returned value r satisfies r >= min(cost[0], cost[1]).
    Preconditions: cost is a slice of 64-bit integers. Let n = len(cost). We have 2 <= n <= 1000, and for every i with 0 <= i < n, 0 <= cost[i] <= 999. -/
  theorem spec_4 (cost : Slice I64)
      (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
      (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999) :
      ∀ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r →
        min (costAt cost 0) (costAt cost 1) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (cost : Slice I64)
        (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
        (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999), ∀ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r →
          min (costAt cost 0) (costAt cost 1) ≤ r.val) := by
    sorry

  /-- min_cost_climbing_stairs(cost) = min_cost_climbing_stairs(cost').
    Preconditions: cost is a slice of 64-bit integers. Let n = len(cost). We have 2 <= n <= 1000, and for every i with 0 <= i < n, 0 <= cost[i] <= 999. Let cost' be the reverse of cost: len(cost') = len(cost) and cost'[i] = cost[len(cost)-1-i] for all i. (cost' also satisfies the problem constraints.) -/
  theorem spec_5 (cost cost' : Slice I64)
      (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
      (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999)
      (h_len' : cost'.val.length = cost.val.length)
      (h_rev : ∀ i, i < cost'.val.length → costAt cost' i = costAt cost (cost.val.length - 1 - i))
      (h_cost' : ∀ i, i < cost'.val.length → 0 ≤ costAt cost' i ∧ costAt cost' i ≤ 999) :
      Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost =
        Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost' := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (cost cost' : Slice I64)
        (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
        (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999)
        (h_len' : cost'.val.length = cost.val.length)
        (h_rev : ∀ i, i < cost'.val.length → costAt cost' i = costAt cost (cost.val.length - 1 - i))
        (h_cost' : ∀ i, i < cost'.val.length → 0 ≤ costAt cost' i ∧ costAt cost' i ≤ 999), Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost =
          Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost') := by
    sorry

  /-- min_cost_climbing_stairs(cost) <= min_cost_climbing_stairs(cost').
    Preconditions: cost and cost' are slices of 64-bit integers with len(cost) = len(cost'). Let n = len(cost). We have 2 <= n <= 1000, and for every i with 0 <= i < n, 0 <= cost[i] <= 999, 0 <= cost'[i] <= 999, and cost[i] <= cost'[i]. -/
  theorem spec_6 (cost cost' : Slice I64)
      (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
      (h_len' : cost'.val.length = cost.val.length)
      (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999)
      (h_cost' : ∀ i, i < cost'.val.length → 0 ≤ costAt cost' i ∧ costAt cost' i ≤ 999)
      (h_le : ∀ i, i < cost.val.length → costAt cost i ≤ costAt cost' i) :
      ∀ r r' : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r →
        Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost' = ok r' → r.val ≤ r'.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (cost cost' : Slice I64)
        (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
        (h_len' : cost'.val.length = cost.val.length)
        (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999)
        (h_cost' : ∀ i, i < cost'.val.length → 0 ≤ costAt cost' i ∧ costAt cost' i ≤ 999)
        (h_le : ∀ i, i < cost.val.length → costAt cost i ≤ costAt cost' i), ∀ r r' : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r →
          Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost' = ok r' → r.val ≤ r'.val) := by
    sorry

  /-- There exists a valid path (as defined in spec_1) whose total cost equals r.
    Preconditions: cost is a slice of 64-bit integers. Let n = len(cost). We have 2 <= n <= 1000, and for every i with 0 <= i < n, 0 <= cost[i] <= 999. -/
  theorem spec_7 (cost : Slice I64)
      (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
      (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999) :
      ∀ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r →
        ∃ p : List Nat, IsValidPath cost.val.length p ∧ pathCost cost p = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (cost : Slice I64)
        (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
        (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999), ∀ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r →
          ∃ p : List Nat, IsValidPath cost.val.length p ∧ pathCost cost p = r.val) := by
    sorry

  /-- For every valid path (as defined in spec_1), its total cost is greater than or equal to r.
    Preconditions: cost is a slice of 64-bit integers. Let n = len(cost). We have 2 <= n <= 1000, and for every i with 0 <= i < n, 0 <= cost[i] <= 999. -/
  theorem spec_8 (cost : Slice I64)
      (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
      (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999) :
      ∀ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r →
        ∀ p : List Nat, IsValidPath cost.val.length p → r.val ≤ pathCost cost p := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (cost : Slice I64)
        (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
        (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999), ∀ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r →
          ∀ p : List Nat, IsValidPath cost.val.length p → r.val ≤ pathCost cost p) := by
    sorry

  /-- The returned value r equals min(cost[0], cost[1]).
    Preconditions: cost is a slice of 64-bit integers. Let n = len(cost). We have 2 <= n <= 1000, and for every i with 0 <= i < n, 0 <= cost[i] <= 999. Additionally, len(cost) = 2. -/
  theorem spec_9 (cost : Slice I64)
      (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
      (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999)
      (h_len_two : cost.val.length = 2) :
      ∀ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r →
        r.val = min (costAt cost 0) (costAt cost 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (cost : Slice I64)
        (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
        (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999)
        (h_len_two : cost.val.length = 2), ∀ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r →
          r.val = min (costAt cost 0) (costAt cost 1)) := by
    sorry

  /-- The returned value r equals 0.
    Preconditions: cost is a slice of 64-bit integers. Let n = len(cost). We have 2 <= n <= 1000, and for every i with 0 <= i < n, 0 <= cost[i] <= 999. Additionally, cost[i] = 0 for all i with 0 <= i < len(cost). -/
  theorem spec_10 (cost : Slice I64)
      (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
      (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999)
      (h_zero : ∀ i, i < cost.val.length → costAt cost i = 0) :
      ∀ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r → r.val = 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (cost : Slice I64)
        (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
        (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999)
        (h_zero : ∀ i, i < cost.val.length → costAt cost i = 0), ∀ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r → r.val = 0) := by
    sorry

  /-- The returned value r equals min(cost[1], cost[0] + cost[2]).
    Preconditions: cost is a slice of 64-bit integers. Let n = len(cost). We have n = 3, and for every i with 0 <= i < n, 0 <= cost[i] <= 999. -/
  theorem spec_11 (cost : Slice I64)
      (h_len : cost.val.length = 3)
      (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999) :
      ∀ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r →
        r.val = min (costAt cost 1) (costAt cost 0 + costAt cost 2) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (cost : Slice I64)
        (h_len : cost.val.length = 3)
        (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999), ∀ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r →
          r.val = min (costAt cost 1) (costAt cost 0 + costAt cost 2)) := by
    sorry

  /-- The returned value r satisfies r >= min(cost[n-1], cost[n-2]).
    Preconditions: cost is a slice of 64-bit integers. Let n = len(cost). We have 2 <= n <= 1000, and for every i with 0 <= i < n, 0 <= cost[i] <= 999. -/
  theorem spec_12 (cost : Slice I64)
      (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
      (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999) :
      ∀ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r →
        min (costAt cost (cost.val.length - 1)) (costAt cost (cost.val.length - 2)) ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (cost : Slice I64)
        (h_len : 2 ≤ cost.val.length) (h_len_ub : cost.val.length ≤ 1000)
        (h_cost : ∀ i, i < cost.val.length → 0 ≤ costAt cost i ∧ costAt cost i ≤ 999), ∀ r : I64, Aegis.MinCostClimbingStairs.min_cost_climbing_stairs cost = ok r →
          min (costAt cost (cost.val.length - 1)) (costAt cost (cost.val.length - 2)) ≤ r.val) := by
    sorry

  end AegisSpec.MinCostClimbingStairs
