import Aegis.MinCostIi.Code.Funs

/-!
# Specifications of `Aegis.MinCostIi.min_cost_ii`

LeetCode problem `paint-house-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinCostIi

  def nrows (costs : Slice (alloc.vec.Vec Std.I64)) : Nat :=
    costs.val.length

  def rowOf (costs : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Std.I64 :=
    match costs.val[i]? with
    | some row => row.val
    | none => []

  def ncols (costs : Slice (alloc.vec.Vec Std.I64)) : Nat :=
    (rowOf costs 0).length

  def cost (costs : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    match (rowOf costs i)[j]? with
    | some x => x.val
    | none => 0

  def rowSum (costs : Slice (alloc.vec.Vec Std.I64)) (f : Nat → Int) : Int :=
    Finset.sum (Finset.range (nrows costs)) f

  def listMin : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl (fun acc y => min acc y) x

  def listMax : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl (fun acc y => max acc y) x

  def rowMin (costs : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    listMin ((List.range (ncols costs)).map (fun j => cost costs i j))

  def rowMax (costs : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    listMax ((List.range (ncols costs)).map (fun j => cost costs i j))

  def IsColoring (costs : Slice (alloc.vec.Vec Std.I64)) (c : List Nat) : Prop :=
    c.length = nrows costs ∧
      (∀ i, i < nrows costs → c.getD i 0 < ncols costs) ∧
      (∀ i, i + 1 < nrows costs → c.getD i 0 ≠ c.getD (i + 1) 0)

  def totalCost (costs : Slice (alloc.vec.Vec Std.I64)) (c : List Nat) : Int :=
    rowSum costs (fun i => cost costs i (c.getD i 0))

  /-- Whenever min_cost_ii(costs) returns a result r, r is the minimum over all colorings c of length n with 0 <= c[i] < k for every 0 <= i < n and c[i] != c[i+1] for every 0 <= i < n-1, of the total cost sum_{i=0}^{n-1} costs[i][c[i]]; that is, r <= sum_{i=0}^{n-1} costs[i][c[i]] for every such coloring c, and r = sum_{i=0}^{n-1} costs[i][c*[i]] for at least one such coloring c*.
    Preconditions: Let n = len(costs) and k = len(costs[0]). Assume 1 <= n <= 100, 2 <= k <= 20, len(costs[i]) = k for every 0 <= i < n, and 1 <= costs[i][j] <= 20 for every 0 <= i < n and 0 <= j < k. -/
  theorem spec_1 (costs : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
      (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
      (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
      (hbound : ∀ i j, i < nrows costs → j < ncols costs →
        1 ≤ cost costs i j ∧ cost costs i j ≤ 20)
      (r : Std.I64) (hr : Aegis.MinCostIi.min_cost_ii costs = ok r) :
      (∃ c : List Nat, IsColoring costs c ∧ r.val = totalCost costs c) ∧
        (∀ c : List Nat, IsColoring costs c → r.val ≤ totalCost costs c) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (costs : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
        (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
        (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
        (hbound : ∀ i j, i < nrows costs → j < ncols costs →
          1 ≤ cost costs i j ∧ cost costs i j ≤ 20)
        (r : Std.I64) (hr : Aegis.MinCostIi.min_cost_ii costs = ok r), (∃ c : List Nat, IsColoring costs c ∧ r.val = totalCost costs c) ∧
          (∀ c : List Nat, IsColoring costs c → r.val ≤ totalCost costs c)) := by
    sorry

  /-- The function min_cost_ii(costs) returns a result r; it does not fail, panic, overflow, or access costs out of bounds for any input satisfying the preconditions.
    Preconditions: Let n = len(costs) and k = len(costs[0]). Assume 1 <= n <= 100, 2 <= k <= 20, len(costs[i]) = k for every 0 <= i < n, and 1 <= costs[i][j] <= 20 for every 0 <= i < n and 0 <= j < k. -/
  theorem spec_2 (costs : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
      (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
      (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
      (hbound : ∀ i j, i < nrows costs → j < ncols costs →
        1 ≤ cost costs i j ∧ cost costs i j ≤ 20) :
      ∃ r : Std.I64, Aegis.MinCostIi.min_cost_ii costs = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (costs : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
        (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
        (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
        (hbound : ∀ i j, i < nrows costs → j < ncols costs →
          1 ≤ cost costs i j ∧ cost costs i j ≤ 20), ∃ r : Std.I64, Aegis.MinCostIi.min_cost_ii costs = ok r) := by
    sorry

  /-- Whenever min_cost_ii(costs) returns a result r, there exists a coloring c of length n with 0 <= c[i] < k for every 0 <= i < n and c[i] != c[i+1] for every 0 <= i < n-1, such that r = sum_{i=0}^{n-1} costs[i][c[i]].
    Preconditions: Let n = len(costs) and k = len(costs[0]). Assume 1 <= n <= 100, 2 <= k <= 20, len(costs[i]) = k for every 0 <= i < n, and 1 <= costs[i][j] <= 20 for every 0 <= i < n and 0 <= j < k. -/
  theorem spec_3 (costs : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
      (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
      (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
      (hbound : ∀ i j, i < nrows costs → j < ncols costs →
        1 ≤ cost costs i j ∧ cost costs i j ≤ 20)
      (r : Std.I64) (hr : Aegis.MinCostIi.min_cost_ii costs = ok r) :
      ∃ c : List Nat, IsColoring costs c ∧ r.val = totalCost costs c := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (costs : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
        (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
        (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
        (hbound : ∀ i j, i < nrows costs → j < ncols costs →
          1 ≤ cost costs i j ∧ cost costs i j ≤ 20)
        (r : Std.I64) (hr : Aegis.MinCostIi.min_cost_ii costs = ok r), ∃ c : List Nat, IsColoring costs c ∧ r.val = totalCost costs c) := by
    sorry

  /-- Whenever min_cost_ii(costs) returns a result r, for every coloring c of length n with 0 <= c[i] < k for every 0 <= i < n and c[i] != c[i+1] for every 0 <= i < n-1, we have r <= sum_{i=0}^{n-1} costs[i][c[i]].
    Preconditions: Let n = len(costs) and k = len(costs[0]). Assume 1 <= n <= 100, 2 <= k <= 20, len(costs[i]) = k for every 0 <= i < n, and 1 <= costs[i][j] <= 20 for every 0 <= i < n and 0 <= j < k. -/
  theorem spec_4 (costs : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
      (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
      (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
      (hbound : ∀ i j, i < nrows costs → j < ncols costs →
        1 ≤ cost costs i j ∧ cost costs i j ≤ 20)
      (r : Std.I64) (hr : Aegis.MinCostIi.min_cost_ii costs = ok r) :
      ∀ c : List Nat, IsColoring costs c → r.val ≤ totalCost costs c := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (costs : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
        (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
        (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
        (hbound : ∀ i j, i < nrows costs → j < ncols costs →
          1 ≤ cost costs i j ∧ cost costs i j ≤ 20)
        (r : Std.I64) (hr : Aegis.MinCostIi.min_cost_ii costs = ok r), ∀ c : List Nat, IsColoring costs c → r.val ≤ totalCost costs c) := by
    sorry

  /-- Whenever min_cost_ii(costs) returns a result r, r >= sum_{i=0}^{n-1} (min_{0 <= j < k} costs[i][j]).
    Preconditions: Let n = len(costs) and k = len(costs[0]). Assume 1 <= n <= 100, 2 <= k <= 20, len(costs[i]) = k for every 0 <= i < n, and 1 <= costs[i][j] <= 20 for every 0 <= i < n and 0 <= j < k. -/
  theorem spec_5 (costs : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
      (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
      (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
      (hbound : ∀ i j, i < nrows costs → j < ncols costs →
        1 ≤ cost costs i j ∧ cost costs i j ≤ 20)
      (r : Std.I64) (hr : Aegis.MinCostIi.min_cost_ii costs = ok r) :
      rowSum costs (rowMin costs) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (costs : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
        (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
        (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
        (hbound : ∀ i j, i < nrows costs → j < ncols costs →
          1 ≤ cost costs i j ∧ cost costs i j ≤ 20)
        (r : Std.I64) (hr : Aegis.MinCostIi.min_cost_ii costs = ok r), rowSum costs (rowMin costs) ≤ r.val) := by
    sorry

  /-- Whenever min_cost_ii(costs) returns a result r, r <= sum_{i=0}^{n-1} (max_{0 <= j < k} costs[i][j]).
    Preconditions: Let n = len(costs) and k = len(costs[0]). Assume 1 <= n <= 100, 2 <= k <= 20, len(costs[i]) = k for every 0 <= i < n, and 1 <= costs[i][j] <= 20 for every 0 <= i < n and 0 <= j < k. -/
  theorem spec_6 (costs : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
      (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
      (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
      (hbound : ∀ i j, i < nrows costs → j < ncols costs →
        1 ≤ cost costs i j ∧ cost costs i j ≤ 20)
      (r : Std.I64) (hr : Aegis.MinCostIi.min_cost_ii costs = ok r) :
      r.val ≤ rowSum costs (rowMax costs) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (costs : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
        (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
        (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
        (hbound : ∀ i j, i < nrows costs → j < ncols costs →
          1 ≤ cost costs i j ∧ cost costs i j ≤ 20)
        (r : Std.I64) (hr : Aegis.MinCostIi.min_cost_ii costs = ok r), r.val ≤ rowSum costs (rowMax costs)) := by
    sorry

  /-- Let pi be a permutation of {0,1,...,k-1}. Define costs_pi with the same dimensions by costs_pi[i][j] = costs[i][pi(j)] for every 0 <= i < n and 0 <= j < k. Whenever min_cost_ii(costs) returns r and min_cost_ii(costs_pi) returns r_pi, we have r_pi = r.
    Preconditions: Let n = len(costs) and k = len(costs[0]). Assume 1 <= n <= 100, 2 <= k <= 20, len(costs[i]) = k for every 0 <= i < n, and 1 <= costs[i][j] <= 20 for every 0 <= i < n and 0 <= j < k. -/
  theorem spec_7 (costs costs_pi : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
      (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
      (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
      (hbound : ∀ i j, i < nrows costs → j < ncols costs →
        1 ≤ cost costs i j ∧ cost costs i j ≤ 20)
      (pi : Equiv.Perm (Fin (ncols costs)))
      (hpi_rows : nrows costs_pi = nrows costs)
      (hpi_cols : ncols costs_pi = ncols costs)
      (hpi : ∀ (i j : Nat) (hi : i < nrows costs) (hj : j < ncols costs),
        cost costs_pi i j = cost costs i (pi ⟨j, hj⟩).val)
      (r r_pi : Std.I64)
      (hr : Aegis.MinCostIi.min_cost_ii costs = ok r)
      (hr_pi : Aegis.MinCostIi.min_cost_ii costs_pi = ok r_pi) :
      r_pi.val = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (costs costs_pi : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
        (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
        (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
        (hbound : ∀ i j, i < nrows costs → j < ncols costs →
          1 ≤ cost costs i j ∧ cost costs i j ≤ 20)
        (pi : Equiv.Perm (Fin (ncols costs)))
        (hpi_rows : nrows costs_pi = nrows costs)
        (hpi_cols : ncols costs_pi = ncols costs)
        (hpi : ∀ (i j : Nat) (hi : i < nrows costs) (hj : j < ncols costs),
          cost costs_pi i j = cost costs i (pi ⟨j, hj⟩).val)
        (r r_pi : Std.I64)
        (hr : Aegis.MinCostIi.min_cost_ii costs = ok r)
        (hr_pi : Aegis.MinCostIi.min_cost_ii costs_pi = ok r_pi), r_pi.val = r.val) := by
    sorry

  /-- Define costs_rev by costs_rev[i][j] = costs[n-1-i][j] for every 0 <= i < n and 0 <= j < k. Whenever min_cost_ii(costs) returns r and min_cost_ii(costs_rev) returns r_rev, we have r_rev = r.
    Preconditions: Let n = len(costs) and k = len(costs[0]). Assume 1 <= n <= 100, 2 <= k <= 20, len(costs[i]) = k for every 0 <= i < n, and 1 <= costs[i][j] <= 20 for every 0 <= i < n and 0 <= j < k. -/
  theorem spec_8 (costs costs_rev : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
      (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
      (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
      (hbound : ∀ i j, i < nrows costs → j < ncols costs →
        1 ≤ cost costs i j ∧ cost costs i j ≤ 20)
      (hrev_rows : nrows costs_rev = nrows costs)
      (hrev_cols : ncols costs_rev = ncols costs)
      (hrev : ∀ i j, i < nrows costs → j < ncols costs →
        cost costs_rev i j = cost costs (nrows costs - 1 - i) j)
      (r r_rev : Std.I64)
      (hr : Aegis.MinCostIi.min_cost_ii costs = ok r)
      (hr_rev : Aegis.MinCostIi.min_cost_ii costs_rev = ok r_rev) :
      r_rev.val = r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (costs costs_rev : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
        (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
        (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
        (hbound : ∀ i j, i < nrows costs → j < ncols costs →
          1 ≤ cost costs i j ∧ cost costs i j ≤ 20)
        (hrev_rows : nrows costs_rev = nrows costs)
        (hrev_cols : ncols costs_rev = ncols costs)
        (hrev : ∀ i j, i < nrows costs → j < ncols costs →
          cost costs_rev i j = cost costs (nrows costs - 1 - i) j)
        (r r_rev : Std.I64)
        (hr : Aegis.MinCostIi.min_cost_ii costs = ok r)
        (hr_rev : Aegis.MinCostIi.min_cost_ii costs_rev = ok r_rev), r_rev.val = r.val) := by
    sorry

  /-- Whenever min_cost_ii(costs) returns r and min_cost_ii(costs2) returns r2, we have r2 = r + d.
    Preconditions: Let n = len(costs) and k = len(costs[0]). Assume 1 <= n <= 100, 2 <= k <= 20, len(costs[i]) = k for every 0 <= i < n, and 1 <= costs[i][j] <= 20 for every 0 <= i < n and 0 <= j < k. Let costs2 be another matrix with len(costs2) = n, len(costs2[i]) = k for every 0 <= i < n, and 1 <= costs2[i][j] <= 20 for every 0 <= i < n and 0 <= j < k. Fix an index i0 with 0 <= i0 < n, and suppose there is an integer d such that costs2[i0][j] = costs[i0][j] + d for every 0 <= j < k, and costs2[i][j] = costs[i][j] for every i != i0 and every 0 <= j < k. -/
  theorem spec_9 (costs costs2 : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
      (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
      (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
      (hbound : ∀ i j, i < nrows costs → j < ncols costs →
        1 ≤ cost costs i j ∧ cost costs i j ≤ 20)
      (h2_rows : nrows costs2 = nrows costs)
      (h2_cols : ncols costs2 = ncols costs)
      (h2_len : ∀ i, i < nrows costs2 → (rowOf costs2 i).length = ncols costs2)
      (h2_bound : ∀ i j, i < nrows costs → j < ncols costs →
        1 ≤ cost costs2 i j ∧ cost costs2 i j ≤ 20)
      (i0 : Nat) (hi0 : i0 < nrows costs) (d : Int)
      (h_row : ∀ j, j < ncols costs → cost costs2 i0 j = cost costs i0 j + d)
      (h_other : ∀ i, i < nrows costs → i ≠ i0 →
        ∀ j, j < ncols costs → cost costs2 i j = cost costs i j)
      (r r2 : Std.I64)
      (hr : Aegis.MinCostIi.min_cost_ii costs = ok r)
      (hr2 : Aegis.MinCostIi.min_cost_ii costs2 = ok r2) :
      r2.val = r.val + d := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (costs costs2 : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
        (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
        (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
        (hbound : ∀ i j, i < nrows costs → j < ncols costs →
          1 ≤ cost costs i j ∧ cost costs i j ≤ 20)
        (h2_rows : nrows costs2 = nrows costs)
        (h2_cols : ncols costs2 = ncols costs)
        (h2_len : ∀ i, i < nrows costs2 → (rowOf costs2 i).length = ncols costs2)
        (h2_bound : ∀ i j, i < nrows costs → j < ncols costs →
          1 ≤ cost costs2 i j ∧ cost costs2 i j ≤ 20)
        (i0 : Nat) (hi0 : i0 < nrows costs) (d : Int)
        (h_row : ∀ j, j < ncols costs → cost costs2 i0 j = cost costs i0 j + d)
        (h_other : ∀ i, i < nrows costs → i ≠ i0 →
          ∀ j, j < ncols costs → cost costs2 i j = cost costs i j)
        (r r2 : Std.I64)
        (hr : Aegis.MinCostIi.min_cost_ii costs = ok r)
        (hr2 : Aegis.MinCostIi.min_cost_ii costs2 = ok r2), r2.val = r.val + d) := by
    sorry

  /-- Whenever min_cost_ii(costs) returns r and min_cost_ii(costs2) returns r2, we have r2 >= r.
    Preconditions: Let n = len(costs) and k = len(costs[0]). Assume 1 <= n <= 100, 2 <= k <= 20, len(costs[i]) = k for every 0 <= i < n, and 1 <= costs[i][j] <= 20 for every 0 <= i < n and 0 <= j < k. Let costs2 be another matrix with len(costs2) = n, len(costs2[i]) = k for every 0 <= i < n, 1 <= costs2[i][j] <= 20 for every 0 <= i < n and 0 <= j < k, and costs2[i][j] >= costs[i][j] for every 0 <= i < n and 0 <= j < k. -/
  theorem spec_10 (costs costs2 : Slice (alloc.vec.Vec Std.I64))
      (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
      (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
      (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
      (hbound : ∀ i j, i < nrows costs → j < ncols costs →
        1 ≤ cost costs i j ∧ cost costs i j ≤ 20)
      (h2_rows : nrows costs2 = nrows costs)
      (h2_cols : ncols costs2 = ncols costs)
      (h2_len : ∀ i, i < nrows costs2 → (rowOf costs2 i).length = ncols costs2)
      (h2_bound : ∀ i j, i < nrows costs → j < ncols costs →
        1 ≤ cost costs2 i j ∧ cost costs2 i j ≤ 20)
      (h_mono : ∀ i j, i < nrows costs → j < ncols costs →
        cost costs i j ≤ cost costs2 i j)
      (r r2 : Std.I64)
      (hr : Aegis.MinCostIi.min_cost_ii costs = ok r)
      (hr2 : Aegis.MinCostIi.min_cost_ii costs2 = ok r2) :
      r.val ≤ r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (costs costs2 : Slice (alloc.vec.Vec Std.I64))
        (hn_pos : 1 ≤ nrows costs) (hn_le : nrows costs ≤ 100)
        (hk_pos : 2 ≤ ncols costs) (hk_le : ncols costs ≤ 20)
        (hlen : ∀ i, i < nrows costs → (rowOf costs i).length = ncols costs)
        (hbound : ∀ i j, i < nrows costs → j < ncols costs →
          1 ≤ cost costs i j ∧ cost costs i j ≤ 20)
        (h2_rows : nrows costs2 = nrows costs)
        (h2_cols : ncols costs2 = ncols costs)
        (h2_len : ∀ i, i < nrows costs2 → (rowOf costs2 i).length = ncols costs2)
        (h2_bound : ∀ i j, i < nrows costs → j < ncols costs →
          1 ≤ cost costs2 i j ∧ cost costs2 i j ≤ 20)
        (h_mono : ∀ i j, i < nrows costs → j < ncols costs →
          cost costs i j ≤ cost costs2 i j)
        (r r2 : Std.I64)
        (hr : Aegis.MinCostIi.min_cost_ii costs = ok r)
        (hr2 : Aegis.MinCostIi.min_cost_ii costs2 = ok r2), r.val ≤ r2.val) := by
    sorry

  end AegisSpec.MinCostIi
