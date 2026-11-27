import Aegis.MinCost.Code.Funs

/-!
# Specifications of `Aegis.MinCost.min_cost`

LeetCode problem `paint-house-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinCost

open Aegis.MinCost

def houseVals (houses : Slice I64) : List Int := houses.val.map (fun h => h.val)

def costVals (cost : Slice (alloc.vec.Vec I64)) : List (List Int) :=
  cost.val.map (fun row => row.val.map (fun x => x.val))

def natOf (x : I64) : Nat := x.val.toNat

def houseAt (houses : List Int) (i : Nat) : Int := houses.getD i 0

def rowAt (cost : List (List Int)) (i : Nat) : List Int := cost.getD i []

def entryAt (cost : List (List Int)) (i j : Nat) : Int := (rowAt cost i).getD j 0

def cellAt (cost : List (List Int)) (i : Nat) (k : Int) : Int := entryAt cost i (k - 1).toNat

def unpainted (houses : List Int) (m : Nat) : List Nat :=
  (List.range m).filter (fun i => houseAt houses i = 0)

def blockCount (m : Nat) (c : Nat → Int) : Nat :=
  ((List.range m).filter (fun i => i = 0 ∨ c i ≠ c (i - 1))).length

def paintCost (houses : List Int) (cost : List (List Int)) (m : Nat) (c : Nat → Int) : Int :=
  ((unpainted houses m).map (fun i => cellAt cost i (c i))).sum

def Admissible (houses : List Int) (n m : Nat) (c : Nat → Int) : Prop :=
  (∀ i, i < m → 1 ≤ c i ∧ c i ≤ (n : Int)) ∧
  (∀ i, i < m → houseAt houses i ≠ 0 → c i = houseAt houses i)

def Feasible (houses : List Int) (n m : Nat) (target : Int) (c : Nat → Int) : Prop :=
  Admissible houses n m c ∧ (blockCount m c : Int) = target

def feasibleSet (houses : List Int) (n m : Nat) (target : Int) : Set (Nat → Int) :=
  {c | Feasible houses n m target c}

def feasibleCosts (houses : List Int) (cost : List (List Int)) (n m : Nat)
    (target : Int) : Set Int :=
  {v | ∃ c, Feasible houses n m target c ∧ paintCost houses cost m c = v}

def houseBlocks (houses : List Int) (m : Nat) : Nat := blockCount m (houseAt houses)

def rowMin (row : List Int) (n : Nat) : Int :=
  ((List.range n).map (fun k => row.getD k 0)).min?.getD 0

def rowMax (row : List Int) (n : Nat) : Int :=
  ((List.range n).map (fun k => row.getD k 0)).max?.getD 0

def lowerBound (houses : List Int) (cost : List (List Int)) (m n : Nat) : Int :=
  ((unpainted houses m).map (fun i => rowMin (rowAt cost i) n)).sum

def upperBound (houses : List Int) (cost : List (List Int)) (m n : Nat) : Int :=
  ((unpainted houses m).map (fun i => rowMax (rowAt cost i) n)).sum

def compatibleColor (houses : List Int) (n m : Nat) (k : Nat) : Prop :=
  1 ≤ k ∧ k ≤ n ∧ ∀ i, i < m → houseAt houses i ≠ 0 → houseAt houses i = (k : Int)

def monoCost (houses : List Int) (cost : List (List Int)) (m : Nat) (k : Nat) : Int :=
  ((unpainted houses m).map (fun i => cellAt cost i (k : Int))).sum

def Alternating (houses : List Int) (n m : Nat) (c : Nat → Int) : Prop :=
  Admissible houses n m c ∧ ∀ i, 1 ≤ i → i < m → c i ≠ c (i - 1)

def alternatingCosts (houses : List Int) (cost : List (List Int)) (n m : Nat) : Set Int :=
  {v | ∃ c, Alternating houses n m c ∧ paintCost houses cost m c = v}

/-- Define a sequence c[0..m-1] to be admissible if 1 <= c[i] <= n for every i and c[i] = houses[i] for every i with houses[i] != 0. Define its neighborhood count by N(c) = the number of indices i with 0 <= i < m and (i = 0 or c[i] != c[i-1]). Define its painting cost by C(c) = sum over i with houses[i] = 0 of cost[i][c[i]-1]. Let A be the set of admissible c with N(c) = target. Whenever min_cost(houses, cost, m, n, target) returns a result r, if A is nonempty then r = min { C(c) | c in A }, and if A is empty then r = -1.
  Preconditions: m = len(houses), m = len(cost), 1 <= m <= 100, 1 <= n <= 20, 1 <= target <= m, for every i with 0 <= i < m, len(cost[i]) = n and 0 <= houses[i] <= n, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= cost[i][j] <= 10000. -/
theorem spec_1
    (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000) :
    ∀ r : I64, min_cost houses cost m n target = ok r →
      ((feasibleSet (houseVals houses) (natOf n) (natOf m) target.val).Nonempty →
        IsLeast
          (feasibleCosts (houseVals houses) (costVals cost) (natOf n) (natOf m) target.val)
          r.val) ∧
      (¬ (feasibleSet (houseVals houses) (natOf n) (natOf m) target.val).Nonempty →
        r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000), ∀ r : I64, min_cost houses cost m n target = ok r →
      ((feasibleSet (houseVals houses) (natOf n) (natOf m) target.val).Nonempty →
        IsLeast
          (feasibleCosts (houseVals houses) (costVals cost) (natOf n) (natOf m) target.val)
          r.val) ∧
      (¬ (feasibleSet (houseVals houses) (natOf n) (natOf m) target.val).Nonempty →
        r.val = -1)) := by
  sorry

/-- Under the preconditions, min_cost(houses, cost, m, n, target) returns a result r; it does not fail, overflow, or panic.
  Preconditions: m = len(houses), m = len(cost), 1 <= m <= 100, 1 <= n <= 20, 1 <= target <= m, for every i with 0 <= i < m, len(cost[i]) = n and 0 <= houses[i] <= n, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= cost[i][j] <= 10000. -/
theorem spec_2
    (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000) :
    ∃ r : I64, min_cost houses cost m n target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000), ∃ r : I64, min_cost houses cost m n target = ok r) := by
  sorry

/-- Let U = { i | 0 <= i < m and houses[i] = 0 }. Whenever min_cost(houses, cost, m, n, target) returns a result r with r != -1, sum_{i in U} min_{1 <= k <= n} cost[i][k-1] <= r <= sum_{i in U} max_{1 <= k <= n} cost[i][k-1].
  Preconditions: m = len(houses), m = len(cost), 1 <= m <= 100, 1 <= n <= 20, 1 <= target <= m, for every i with 0 <= i < m, len(cost[i]) = n and 0 <= houses[i] <= n, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= cost[i][j] <= 10000. -/
theorem spec_3
    (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000) :
    ∀ r : I64, min_cost houses cost m n target = ok r → r.val ≠ -1 →
      lowerBound (houseVals houses) (costVals cost) (natOf m) (natOf n) ≤ r.val ∧
      r.val ≤ upperBound (houseVals houses) (costVals cost) (natOf m) (natOf n) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000), ∀ r : I64, min_cost houses cost m n target = ok r → r.val ≠ -1 →
      lowerBound (houseVals houses) (costVals cost) (natOf m) (natOf n) ≤ r.val ∧
      r.val ≤ upperBound (houseVals houses) (costVals cost) (natOf m) (natOf n)) := by
  sorry

/-- Whenever min_cost(houses, cost, m, n, target) returns a result r with r != -1, there exists a sequence c[0..m-1] such that 1 <= c[i] <= n for every i, c[i] = houses[i] for every i with houses[i] != 0, the number of indices i with (i = 0 or c[i] != c[i-1]) is exactly target, and sum over i with houses[i] = 0 of cost[i][c[i]-1] equals r.
  Preconditions: m = len(houses), m = len(cost), 1 <= m <= 100, 1 <= n <= 20, 1 <= target <= m, for every i with 0 <= i < m, len(cost[i]) = n and 0 <= houses[i] <= n, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= cost[i][j] <= 10000. -/
theorem spec_4
    (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000) :
    ∀ r : I64, min_cost houses cost m n target = ok r → r.val ≠ -1 →
      ∃ c : Nat → Int,
        Feasible (houseVals houses) (natOf n) (natOf m) target.val c ∧
        paintCost (houseVals houses) (costVals cost) (natOf m) c = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000), ∀ r : I64, min_cost houses cost m n target = ok r → r.val ≠ -1 →
      ∃ c : Nat → Int,
        Feasible (houseVals houses) (natOf n) (natOf m) target.val c ∧
        paintCost (houseVals houses) (costVals cost) (natOf m) c = r.val) := by
  sorry

/-- Whenever min_cost(houses, cost, m, n, target) returns a result r, r = -1 if and only if there is no sequence c[0..m-1] such that 1 <= c[i] <= n for every i, c[i] = houses[i] for every i with houses[i] != 0, and the number of indices i with (i = 0 or c[i] != c[i-1]) is exactly target.
  Preconditions: m = len(houses), m = len(cost), 1 <= m <= 100, 1 <= n <= 20, 1 <= target <= m, for every i with 0 <= i < m, len(cost[i]) = n and 0 <= houses[i] <= n, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= cost[i][j] <= 10000. -/
theorem spec_5
    (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000) :
    ∀ r : I64, min_cost houses cost m n target = ok r →
      (r.val = -1 ↔
        ¬ (feasibleSet (houseVals houses) (natOf n) (natOf m) target.val).Nonempty) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000), ∀ r : I64, min_cost houses cost m n target = ok r →
      (r.val = -1 ↔
        ¬ (feasibleSet (houseVals houses) (natOf n) (natOf m) target.val).Nonempty)) := by
  sorry

/-- Let N0 be the number of indices i with 0 <= i < m and (i = 0 or houses[i] != houses[i-1]). Whenever min_cost(houses, cost, m, n, target) returns a result r, r = 0 if N0 = target, and r = -1 otherwise.
  Preconditions: m = len(houses), m = len(cost), 1 <= m <= 100, 1 <= n <= 20, 1 <= target <= m, for every i with 0 <= i < m, len(cost[i]) = n and 0 <= houses[i] <= n, for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= cost[i][j] <= 10000, and for every i with 0 <= i < m, houses[i] != 0. -/
theorem spec_6
    (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000)
    (h_painted : ∀ i, i < natOf m → houseAt (houseVals houses) i ≠ 0) :
    ∀ r : I64, min_cost houses cost m n target = ok r →
      ((houseBlocks (houseVals houses) (natOf m) : Int) = target.val → r.val = 0) ∧
      ((houseBlocks (houseVals houses) (natOf m) : Int) ≠ target.val → r.val = -1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000)
    (h_painted : ∀ i, i < natOf m → houseAt (houseVals houses) i ≠ 0), ∀ r : I64, min_cost houses cost m n target = ok r →
      ((houseBlocks (houseVals houses) (natOf m) : Int) = target.val → r.val = 0) ∧
      ((houseBlocks (houseVals houses) (natOf m) : Int) ≠ target.val → r.val = -1)) := by
  sorry

/-- Whenever min_cost(houses, cost, m, n, target) returns a result r: if houses[0] != 0 then r = 0; if houses[0] = 0 then r = min_{1 <= k <= n} cost[0][k-1].
  Preconditions: m = len(houses), m = len(cost), 1 <= m <= 100, 1 <= n <= 20, 1 <= target <= m, for every i with 0 <= i < m, len(cost[i]) = n and 0 <= houses[i] <= n, for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= cost[i][j] <= 10000, and m = 1. -/
theorem spec_7
    (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000)
    (hm_one : m.val = 1) :
    ∀ r : I64, min_cost houses cost m n target = ok r →
      (houseAt (houseVals houses) 0 ≠ 0 → r.val = 0) ∧
      (houseAt (houseVals houses) 0 = 0 →
        r.val = rowMin (rowAt (costVals cost) 0) (natOf n)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000)
    (hm_one : m.val = 1), ∀ r : I64, min_cost houses cost m n target = ok r →
      (houseAt (houseVals houses) 0 ≠ 0 → r.val = 0) ∧
      (houseAt (houseVals houses) 0 = 0 →
        r.val = rowMin (rowAt (costVals cost) 0) (natOf n))) := by
  sorry

/-- Whenever min_cost(houses, cost, m, n, target) returns a result r: if target = 1 then r = sum over i with houses[i] = 0 of cost[i][0]; if target != 1 then r = -1.
  Preconditions: m = len(houses), m = len(cost), 1 <= m <= 100, 1 <= n <= 20, 1 <= target <= m, for every i with 0 <= i < m, len(cost[i]) = n and 0 <= houses[i] <= n, for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= cost[i][j] <= 10000, and n = 1. -/
theorem spec_8
    (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000)
    (hn_one : n.val = 1) :
    ∀ r : I64, min_cost houses cost m n target = ok r →
      (target.val = 1 →
        r.val = monoCost (houseVals houses) (costVals cost) (natOf m) 1) ∧
      (target.val ≠ 1 → r.val = -1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000)
    (hn_one : n.val = 1), ∀ r : I64, min_cost houses cost m n target = ok r →
      (target.val = 1 →
        r.val = monoCost (houseVals houses) (costVals cost) (natOf m) 1) ∧
      (target.val ≠ 1 → r.val = -1)) := by
  sorry

/-- Let K = { k | 1 <= k <= n and for every i with houses[i] != 0, houses[i] = k }. Whenever min_cost(houses, cost, m, n, target) returns a result r: if K is nonempty then r = min_{k in K} sum over i with houses[i] = 0 of cost[i][k-1]; if K is empty then r = -1.
  Preconditions: m = len(houses), m = len(cost), 1 <= m <= 100, 1 <= n <= 20, 1 <= target <= m, for every i with 0 <= i < m, len(cost[i]) = n and 0 <= houses[i] <= n, for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= cost[i][j] <= 10000, and target = 1. -/
theorem spec_9
    (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000)
    (ht_one : target.val = 1) :
    ∀ r : I64, min_cost houses cost m n target = ok r →
      ((∃ k : Nat, compatibleColor (houseVals houses) (natOf n) (natOf m) k) →
        IsLeast
          {v : Int | ∃ k : Nat,
            compatibleColor (houseVals houses) (natOf n) (natOf m) k ∧
            monoCost (houseVals houses) (costVals cost) (natOf m) k = v} r.val) ∧
      ((¬ ∃ k : Nat, compatibleColor (houseVals houses) (natOf n) (natOf m) k) →
        r.val = -1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000)
    (ht_one : target.val = 1), ∀ r : I64, min_cost houses cost m n target = ok r →
      ((∃ k : Nat, compatibleColor (houseVals houses) (natOf n) (natOf m) k) →
        IsLeast
          {v : Int | ∃ k : Nat,
            compatibleColor (houseVals houses) (natOf n) (natOf m) k ∧
            monoCost (houseVals houses) (costVals cost) (natOf m) k = v} r.val) ∧
      ((¬ ∃ k : Nat, compatibleColor (houseVals houses) (natOf n) (natOf m) k) →
        r.val = -1)) := by
  sorry

/-- Let B be the set of sequences c[0..m-1] such that 1 <= c[i] <= n for every i, c[i] = houses[i] for every i with houses[i] != 0, and c[i] != c[i-1] for every i with 1 <= i < m. Whenever min_cost(houses, cost, m, n, target) returns a result r: if B is nonempty then r = min_{c in B} sum over i with houses[i] = 0 of cost[i][c[i]-1]; if B is empty then r = -1.
  Preconditions: m = len(houses), m = len(cost), 1 <= m <= 100, 1 <= n <= 20, 1 <= target <= m, for every i with 0 <= i < m, len(cost[i]) = n and 0 <= houses[i] <= n, for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= cost[i][j] <= 10000, and target = m. -/
theorem spec_10
    (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000)
    (ht_m : target.val = m.val) :
    ∀ r : I64, min_cost houses cost m n target = ok r →
      ((∃ c : Nat → Int, Alternating (houseVals houses) (natOf n) (natOf m) c) →
        IsLeast
          (alternatingCosts (houseVals houses) (costVals cost) (natOf n) (natOf m))
          r.val) ∧
      ((¬ ∃ c : Nat → Int, Alternating (houseVals houses) (natOf n) (natOf m) c) →
        r.val = -1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000)
    (ht_m : target.val = m.val), ∀ r : I64, min_cost houses cost m n target = ok r →
      ((∃ c : Nat → Int, Alternating (houseVals houses) (natOf n) (natOf m) c) →
        IsLeast
          (alternatingCosts (houseVals houses) (costVals cost) (natOf n) (natOf m))
          r.val) ∧
      ((¬ ∃ c : Nat → Int, Alternating (houseVals houses) (natOf n) (natOf m) c) →
        r.val = -1)) := by
  sorry

/-- Whenever min_cost(houses, cost, m, n, target) returns a result r and min_cost(houses, cost', m, n, target) returns a result r', we have r = r'.
  Preconditions: m = len(houses), m = len(cost), 1 <= m <= 100, 1 <= n <= 20, 1 <= target <= m, for every i with 0 <= i < m, len(cost[i]) = n and 0 <= houses[i] <= n, for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= cost[i][j] <= 10000. Let i0 be an index with 0 <= i0 < m and houses[i0] != 0. Let cost' be a slice of m vectors, each of length n, such that cost'[k][j] = cost[k][j] for every k != i0 and every 0 <= j < n, and 1 <= cost'[i0][j] <= 10000 for every 0 <= j < n. -/
theorem spec_11
    (houses : Slice I64) (cost cost' : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (i0 : Nat)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000)
    (hi0 : i0 < natOf m)
    (hi0_painted : houseAt (houseVals houses) i0 ≠ 0)
    (hm_cost' : ((cost'.val.length : Int)) = m.val)
    (h_rows' : ∀ i, i < natOf m → ((rowAt (costVals cost') i).length : Int) = n.val)
    (h_agree : ∀ k, k < natOf m → k ≠ i0 → ∀ j, j < natOf n →
      entryAt (costVals cost') k j = entryAt (costVals cost) k j)
    (h_cost' : ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost') i0 j ∧ entryAt (costVals cost') i0 j ≤ 10000) :
    ∀ r r' : I64, min_cost houses cost m n target = ok r →
      min_cost houses cost' m n target = ok r' → r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (houses : Slice I64) (cost cost' : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (i0 : Nat)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000)
    (hi0 : i0 < natOf m)
    (hi0_painted : houseAt (houseVals houses) i0 ≠ 0)
    (hm_cost' : ((cost'.val.length : Int)) = m.val)
    (h_rows' : ∀ i, i < natOf m → ((rowAt (costVals cost') i).length : Int) = n.val)
    (h_agree : ∀ k, k < natOf m → k ≠ i0 → ∀ j, j < natOf n →
      entryAt (costVals cost') k j = entryAt (costVals cost) k j)
    (h_cost' : ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost') i0 j ∧ entryAt (costVals cost') i0 j ≤ 10000), ∀ r r' : I64, min_cost houses cost m n target = ok r →
      min_cost houses cost' m n target = ok r' → r = r') := by
  sorry

/-- For every sequence c[0..m-1] satisfying 1 <= c[i] <= n for every i, c[i] = houses[i] for every i with houses[i] != 0, and the number of indices i with (i = 0 or c[i] != c[i-1]) equal to target, whenever min_cost(houses, cost, m, n, target) returns a result r, we have r != -1 and r <= sum over i with houses[i] = 0 of cost[i][c[i]-1].
  Preconditions: m = len(houses), m = len(cost), 1 <= m <= 100, 1 <= n <= 20, 1 <= target <= m, for every i with 0 <= i < m, len(cost[i]) = n and 0 <= houses[i] <= n, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= cost[i][j] <= 10000. -/
theorem spec_12
    (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000) :
    ∀ c : Nat → Int, Admissible (houseVals houses) (natOf n) (natOf m) c →
      (blockCount (natOf m) c : Int) = target.val →
      ∀ r : I64, min_cost houses cost m n target = ok r →
        r.val ≠ -1 ∧
        r.val ≤ paintCost (houseVals houses) (costVals cost) (natOf m) c := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (houses : Slice I64) (cost : Slice (alloc.vec.Vec I64)) (m n target : I64)
    (hm_houses : ((houses.val.length : Int)) = m.val)
    (hm_cost : ((cost.val.length : Int)) = m.val)
    (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100)
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 20)
    (ht_lower : 1 ≤ target.val) (ht_upper : target.val ≤ m.val)
    (h_rows : ∀ i, i < natOf m → ((rowAt (costVals cost) i).length : Int) = n.val)
    (h_houses : ∀ i, i < natOf m →
      0 ≤ houseAt (houseVals houses) i ∧ houseAt (houseVals houses) i ≤ n.val)
    (h_cost : ∀ i, i < natOf m → ∀ j, j < natOf n →
      1 ≤ entryAt (costVals cost) i j ∧ entryAt (costVals cost) i j ≤ 10000), ∀ c : Nat → Int, Admissible (houseVals houses) (natOf n) (natOf m) c →
      (blockCount (natOf m) c : Int) = target.val →
      ∀ r : I64, min_cost houses cost m n target = ok r →
        r.val ≠ -1 ∧
        r.val ≤ paintCost (houseVals houses) (costVals cost) (natOf m) c) := by
  sorry

end AegisSpec.MinCost
