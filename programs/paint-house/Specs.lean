import Aegis.MinCost.Code.Funs

/-!
# Specifications of `Aegis.MinCost.min_cost`

LeetCode problem `paint-house`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinCost

namespace AegisSpec.MinCost

def rows (costs : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  costs.val.map (fun v => v.val.map (fun x => x.val))

theorem rows_length (costs : Slice (alloc.vec.Vec Std.I64)) :
    (rows costs).length = costs.val.length := by
  simp [rows]

def rowOf (m : List (List Int)) (i : Nat) : List Int :=
  m.getD i []

def entry (m : List (List Int)) (i j : Nat) : Int :=
  (rowOf m i).getD j 0

def ValidInput (costs : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  let m := rows costs
  1 ≤ m.length ∧ m.length ≤ 100 ∧
    (∀ i, i < m.length → (rowOf m i).length = 3) ∧
    (∀ i, i < m.length → ∀ j, j < 3 → 1 ≤ entry m i j ∧ entry m i j ≤ 20)

def IsColoring (n : Nat) (c : Nat → Nat) : Prop :=
  (∀ i, i < n → c i < 3) ∧ ∀ i, i + 1 < n → c i ≠ c (i + 1)

def costOf (m : List (List Int)) (c : Nat → Nat) : Int :=
  (List.range m.length).foldl (fun acc i => acc + entry m i (c i)) 0

def rowMin (r : List Int) : Int :=
  min (r.getD 0 0) (min (r.getD 1 0) (r.getD 2 0))

def rowMax (r : List Int) : Int :=
  max (r.getD 0 0) (max (r.getD 1 0) (r.getD 2 0))

def sumRowMin (m : List (List Int)) : Int :=
  (m.map rowMin).sum

def sumRowMax (m : List (List Int)) : Int :=
  (m.map rowMax).sum

def permuteCols (pi : Equiv.Perm (Fin 3)) (m : List (List Int)) : List (List Int) :=
  m.map (fun r => [r.getD (pi 0).val 0, r.getD (pi 1).val 0, r.getD (pi 2).val 0])

/-- The function returns a result r, and r is the minimum cost over all valid colorings of the row: a valid coloring is a sequence c[0],...,c[n-1] with each c[i] in {0,1,2} and c[i] != c[i+1] for every 0 <= i < n-1, and its cost is sum_{i=0}^{n-1} costs[i][c[i]]. Equivalently, there exists a valid coloring c with total cost r, and every valid coloring c has total cost at least r.
  Preconditions: Let n = len(costs). Assume 1 <= n <= 100, len(costs[i]) = 3 for every 0 <= i < n, and 1 <= costs[i][j] <= 20 for every 0 <= i < n and 0 <= j < 3. -/
theorem spec_1 (costs : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput costs) :
    ∃ r : Std.I64,
      min_cost costs = ok r ∧
        (∃ c : Nat → Nat, IsColoring (rows costs).length c ∧
          costOf (rows costs) c = r.val) ∧
        (∀ c : Nat → Nat, IsColoring (rows costs).length c →
          r.val ≤ costOf (rows costs) c) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (costs : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput costs), ∃ r : Std.I64,
      min_cost costs = ok r ∧
        (∃ c : Nat → Nat, IsColoring (rows costs).length c ∧
          costOf (rows costs) c = r.val) ∧
        (∀ c : Nat → Nat, IsColoring (rows costs).length c →
          r.val ≤ costOf (rows costs) c)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, overflow, or panic.
  Preconditions: Let n = len(costs). Assume 1 <= n <= 100, len(costs[i]) = 3 for every 0 <= i < n, and 1 <= costs[i][j] <= 20 for every 0 <= i < n and 0 <= j < 3. -/
theorem spec_2 (costs : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput costs) :
    ∃ r : Std.I64, min_cost costs = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (costs : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput costs), ∃ r : Std.I64, min_cost costs = ok r) := by
  sorry

/-- The function returns a result r, and r >= sum_{i=0}^{n-1} min(costs[i][0], costs[i][1], costs[i][2]).
  Preconditions: Let n = len(costs). Assume 1 <= n <= 100, len(costs[i]) = 3 for every 0 <= i < n, and 1 <= costs[i][j] <= 20 for every 0 <= i < n and 0 <= j < 3. -/
theorem spec_3 (costs : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput costs) :
    ∃ r : Std.I64, min_cost costs = ok r ∧ sumRowMin (rows costs) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (costs : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput costs), ∃ r : Std.I64, min_cost costs = ok r ∧ sumRowMin (rows costs) ≤ r.val) := by
  sorry

/-- The function returns a result r, and r <= sum_{i=0}^{n-1} max(costs[i][0], costs[i][1], costs[i][2]).
  Preconditions: Let n = len(costs). Assume 1 <= n <= 100, len(costs[i]) = 3 for every 0 <= i < n, and 1 <= costs[i][j] <= 20 for every 0 <= i < n and 0 <= j < 3. -/
theorem spec_4 (costs : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput costs) :
    ∃ r : Std.I64, min_cost costs = ok r ∧ r.val ≤ sumRowMax (rows costs) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (costs : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput costs), ∃ r : Std.I64, min_cost costs = ok r ∧ r.val ≤ sumRowMax (rows costs)) := by
  sorry

/-- The function returns a result r, and r = min(costs[0][0], costs[0][1], costs[0][2]).
  Preconditions: Let n = len(costs). Assume n = 1, len(costs[0]) = 3, and 1 <= costs[0][j] <= 20 for j = 0,1,2. -/
theorem spec_5 (costs : Slice (alloc.vec.Vec Std.I64))
    (hn : (rows costs).length = 1)
    (hlen : (rowOf (rows costs) 0).length = 3)
    (hrange : ∀ j, j < 3 → 1 ≤ entry (rows costs) 0 j ∧ entry (rows costs) 0 j ≤ 20) :
    ∃ r : Std.I64, min_cost costs = ok r ∧ r.val = rowMin (rowOf (rows costs) 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (costs : Slice (alloc.vec.Vec Std.I64))
    (hn : (rows costs).length = 1)
    (hlen : (rowOf (rows costs) 0).length = 3)
    (hrange : ∀ j, j < 3 → 1 ≤ entry (rows costs) 0 j ∧ entry (rows costs) 0 j ≤ 20), ∃ r : Std.I64, min_cost costs = ok r ∧ r.val = rowMin (rowOf (rows costs) 0)) := by
  sorry

/-- The function returns a result r, and r = min{ costs[0][a] + costs[1][b] | a,b in {0,1,2} and a != b }.
  Preconditions: Let n = len(costs). Assume n = 2, len(costs[0]) = 3, len(costs[1]) = 3, and 1 <= costs[i][j] <= 20 for i = 0,1 and j = 0,1,2. -/
theorem spec_6 (costs : Slice (alloc.vec.Vec Std.I64))
    (hn : (rows costs).length = 2)
    (hlen : ∀ i, i < 2 → (rowOf (rows costs) i).length = 3)
    (hrange : ∀ i, i < 2 → ∀ j, j < 3 →
      1 ≤ entry (rows costs) i j ∧ entry (rows costs) i j ≤ 20) :
    ∃ r : Std.I64,
      min_cost costs = ok r ∧
        (∃ a b, a < 3 ∧ b < 3 ∧ a ≠ b ∧
          r.val = entry (rows costs) 0 a + entry (rows costs) 1 b) ∧
        (∀ a b, a < 3 → b < 3 → a ≠ b →
          r.val ≤ entry (rows costs) 0 a + entry (rows costs) 1 b) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (costs : Slice (alloc.vec.Vec Std.I64))
    (hn : (rows costs).length = 2)
    (hlen : ∀ i, i < 2 → (rowOf (rows costs) i).length = 3)
    (hrange : ∀ i, i < 2 → ∀ j, j < 3 →
      1 ≤ entry (rows costs) i j ∧ entry (rows costs) i j ≤ 20), ∃ r : Std.I64,
      min_cost costs = ok r ∧
        (∃ a b, a < 3 ∧ b < 3 ∧ a ≠ b ∧
          r.val = entry (rows costs) 0 a + entry (rows costs) 1 b) ∧
        (∀ a b, a < 3 → b < 3 → a ≠ b →
          r.val ≤ entry (rows costs) 0 a + entry (rows costs) 1 b)) := by
  sorry

/-- The function returns a result r, and there exists a valid coloring c[0],...,c[n-1] with c[i] in {0,1,2} for all i, c[i] != c[i+1] for all 0 <= i < n-1, such that r = sum_{i=0}^{n-1} costs[i][c[i]].
  Preconditions: Let n = len(costs). Assume 1 <= n <= 100, len(costs[i]) = 3 for every 0 <= i < n, and 1 <= costs[i][j] <= 20 for every 0 <= i < n and 0 <= j < 3. -/
theorem spec_7 (costs : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput costs) :
    ∃ r : Std.I64,
      min_cost costs = ok r ∧
        ∃ c : Nat → Nat, IsColoring (rows costs).length c ∧
          r.val = costOf (rows costs) c := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (costs : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput costs), ∃ r : Std.I64,
      min_cost costs = ok r ∧
        ∃ c : Nat → Nat, IsColoring (rows costs).length c ∧
          r.val = costOf (rows costs) c) := by
  sorry

/-- The function returns a result r, and for every valid coloring c[0],...,c[n-1] with c[i] in {0,1,2} for all i and c[i] != c[i+1] for all 0 <= i < n-1, we have r <= sum_{i=0}^{n-1} costs[i][c[i]].
  Preconditions: Let n = len(costs). Assume 1 <= n <= 100, len(costs[i]) = 3 for every 0 <= i < n, and 1 <= costs[i][j] <= 20 for every 0 <= i < n and 0 <= j < 3. -/
theorem spec_8 (costs : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput costs) :
    ∃ r : Std.I64,
      min_cost costs = ok r ∧
        ∀ c : Nat → Nat, IsColoring (rows costs).length c →
          r.val ≤ costOf (rows costs) c := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (costs : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput costs), ∃ r : Std.I64,
      min_cost costs = ok r ∧
        ∀ c : Nat → Nat, IsColoring (rows costs).length c →
          r.val ≤ costOf (rows costs) c) := by
  sorry

/-- The function returns a result r on costs and a result r' on costs', and r = r'.
  Preconditions: Let n = len(costs). Assume 1 <= n <= 100, len(costs[i]) = 3 for every 0 <= i < n, and 1 <= costs[i][j] <= 20 for every 0 <= i < n and 0 <= j < 3. Let pi be any permutation of {0,1,2}, and define costs'[i][j] = costs[i][pi(j)] for all i,j. -/
theorem spec_9 (costs costs' : Slice (alloc.vec.Vec Std.I64))
    (pi : Equiv.Perm (Fin 3))
    (h : ValidInput costs) (h' : ValidInput costs')
    (hperm : rows costs' = permuteCols pi (rows costs)) :
    ∃ r r' : Std.I64,
      min_cost costs = ok r ∧ min_cost costs' = ok r' ∧ r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (costs costs' : Slice (alloc.vec.Vec Std.I64))
    (pi : Equiv.Perm (Fin 3))
    (h : ValidInput costs) (h' : ValidInput costs')
    (hperm : rows costs' = permuteCols pi (rows costs)), ∃ r r' : Std.I64,
      min_cost costs = ok r ∧ min_cost costs' = ok r' ∧ r.val = r'.val) := by
  sorry

/-- The function returns a result r on costs and a result r' on revcosts, and r = r'.
  Preconditions: Let n = len(costs). Assume 1 <= n <= 100, len(costs[i]) = 3 for every 0 <= i < n, and 1 <= costs[i][j] <= 20 for every 0 <= i < n and 0 <= j < 3. Define revcosts[i][j] = costs[n-1-i][j] for all i,j. -/
theorem spec_10 (costs costs' : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput costs) (h' : ValidInput costs')
    (hrev : rows costs' = (rows costs).reverse) :
    ∃ r r' : Std.I64,
      min_cost costs = ok r ∧ min_cost costs' = ok r' ∧ r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (costs costs' : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput costs) (h' : ValidInput costs')
    (hrev : rows costs' = (rows costs).reverse), ∃ r r' : Std.I64,
      min_cost costs = ok r ∧ min_cost costs' = ok r' ∧ r.val = r'.val) := by
  sorry

/-- The function returns a result r1 on costs1 and a result r2 on costs2, and r1 <= r2.
  Preconditions: Let n = len(costs1) = len(costs2). Assume 1 <= n <= 100, len(costs1[i]) = len(costs2[i]) = 3 for every 0 <= i < n, and 1 <= costs1[i][j] <= 20 and 1 <= costs2[i][j] <= 20 for every 0 <= i < n and 0 <= j < 3. Assume costs1[i][j] <= costs2[i][j] for every 0 <= i < n and 0 <= j < 3. -/
theorem spec_11 (costs1 costs2 : Slice (alloc.vec.Vec Std.I64))
    (h1 : ValidInput costs1) (h2 : ValidInput costs2)
    (hlen : (rows costs1).length = (rows costs2).length)
    (hle : ∀ i, i < (rows costs1).length → ∀ j, j < 3 →
      entry (rows costs1) i j ≤ entry (rows costs2) i j) :
    ∃ r1 r2 : Std.I64,
      min_cost costs1 = ok r1 ∧ min_cost costs2 = ok r2 ∧ r1.val ≤ r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (costs1 costs2 : Slice (alloc.vec.Vec Std.I64))
    (h1 : ValidInput costs1) (h2 : ValidInput costs2)
    (hlen : (rows costs1).length = (rows costs2).length)
    (hle : ∀ i, i < (rows costs1).length → ∀ j, j < 3 →
      entry (rows costs1) i j ≤ entry (rows costs2) i j), ∃ r1 r2 : Std.I64,
      min_cost costs1 = ok r1 ∧ min_cost costs2 = ok r2 ∧ r1.val ≤ r2.val) := by
  sorry

/-- The function returns a result r on costs and a result r' on costs', and r' = r + K.
  Preconditions: Let n = len(costs). Assume 1 <= n <= 100, len(costs[i]) = 3 for every 0 <= i < n, and 1 <= costs[i][j] <= 20 for every 0 <= i < n and 0 <= j < 3. Fix a house index i0 with 0 <= i0 < n and an integer K such that 1 <= costs[i0][j] + K <= 20 for j = 0,1,2. Define costs' to be identical to costs except that costs'[i0][j] = costs[i0][j] + K for j = 0,1,2. -/
theorem spec_12 (costs costs' : Slice (alloc.vec.Vec Std.I64)) (i0 : Nat) (K : Int)
    (h : ValidInput costs) (h' : ValidInput costs')
    (hi0 : i0 < (rows costs).length)
    (hK : ∀ j, j < 3 →
      1 ≤ entry (rows costs) i0 j + K ∧ entry (rows costs) i0 j + K ≤ 20)
    (hlen : (rows costs').length = (rows costs).length)
    (hother : ∀ i, i < (rows costs).length → i ≠ i0 →
      rowOf (rows costs') i = rowOf (rows costs) i)
    (hi0row : rowOf (rows costs') i0 = (rowOf (rows costs) i0).map (fun x => x + K)) :
    ∃ r r' : Std.I64,
      min_cost costs = ok r ∧ min_cost costs' = ok r' ∧ r'.val = r.val + K := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (costs costs' : Slice (alloc.vec.Vec Std.I64)) (i0 : Nat) (K : Int)
    (h : ValidInput costs) (h' : ValidInput costs')
    (hi0 : i0 < (rows costs).length)
    (hK : ∀ j, j < 3 →
      1 ≤ entry (rows costs) i0 j + K ∧ entry (rows costs) i0 j + K ≤ 20)
    (hlen : (rows costs').length = (rows costs).length)
    (hother : ∀ i, i < (rows costs).length → i ≠ i0 →
      rowOf (rows costs') i = rowOf (rows costs) i)
    (hi0row : rowOf (rows costs') i0 = (rowOf (rows costs) i0).map (fun x => x + K)), ∃ r r' : Std.I64,
      min_cost costs = ok r ∧ min_cost costs' = ok r' ∧ r'.val = r.val + K) := by
  sorry

end AegisSpec.MinCost
