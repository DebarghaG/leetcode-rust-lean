import Aegis.MinCost.Code.Funs

/-!
# Specifications of `Aegis.MinCost.min_cost`

LeetCode problem `minimum-cost-to-reach-destination-in-time`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinCost

def edgeAt (edges : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Std.I64 :=
  (edges.val.getD i (alloc.vec.Vec.new Std.I64)).val

def edgeVal (edges : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  ((edgeAt edges i).getD j (0#i64)).val

def edgeTime (edges : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Nat :=
  (edgeVal edges i 2).toNat

def feeVal (passingFees : Slice Std.I64) (j : Nat) : Int :=
  (passingFees.val.getD j (0#i64)).val

def fee (passingFees : Slice Std.I64) (j : Nat) : Nat :=
  (feeVal passingFees j).toNat

def numCities (passingFees : Slice Std.I64) : Nat :=
  passingFees.val.length

def numEdges (edges : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  edges.val.length

def dest (passingFees : Slice Std.I64) : Nat :=
  numCities passingFees - 1

def budget (maxTime : Std.I64) : Nat :=
  maxTime.val.toNat

def totalFees (passingFees : Slice Std.I64) : Nat :=
  (passingFees.val.map (fun f => f.val.toNat)).sum

def InputsValid (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) : Prop :=
  (1 : Int) ≤ maxTime.val ∧ maxTime.val ≤ 1000 ∧
  (2 : Nat) ≤ numCities passingFees ∧ numCities passingFees ≤ 1000 ∧
  numCities passingFees - 1 ≤ numEdges edges ∧ numEdges edges ≤ 1000 ∧
  (∀ j, j < numCities passingFees →
    (1 : Int) ≤ feeVal passingFees j ∧ feeVal passingFees j ≤ 1000) ∧
  (∀ i, i < numEdges edges →
    (edgeAt edges i).length = 3 ∧
    (0 : Int) ≤ edgeVal edges i 0 ∧ edgeVal edges i 0 < (numCities passingFees : Int) ∧
    (0 : Int) ≤ edgeVal edges i 1 ∧ edgeVal edges i 1 < (numCities passingFees : Int) ∧
    edgeVal edges i 0 ≠ edgeVal edges i 1 ∧
    (1 : Int) ≤ edgeVal edges i 2 ∧ edgeVal edges i 2 ≤ 1000)

def journeyTime (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Nat) : Nat :=
  (es.map (edgeTime edges)).sum

def visitedCities (cities : List Nat) : List Nat :=
  cities.eraseDups

def journeyCost (passingFees : Slice Std.I64) (cities : List Nat) : Nat :=
  ((visitedCities cities).map (fee passingFees)).sum

def IsJourney (edges : Slice (alloc.vec.Vec Std.I64)) (maxTime n : Nat)
    (cities : List Nat) (es : List Nat) : Prop :=
  cities.length = es.length + 1 ∧
  cities.head? = some 0 ∧
  cities.getLast? = some (n - 1) ∧
  (∀ i, i < es.length →
    es[i]! < numEdges edges ∧
    (edgeAt edges es[i]!).length = 3 ∧
    ((edgeVal edges es[i]! 0 = (cities[i]! : Int) ∧
        edgeVal edges es[i]! 1 = (cities[i + 1]! : Int)) ∨
      (edgeVal edges es[i]! 1 = (cities[i]! : Int) ∧
        edgeVal edges es[i]! 0 = (cities[i + 1]! : Int)))) ∧
  journeyTime edges es ≤ maxTime

def IsSimplePath (edges : Slice (alloc.vec.Vec Std.I64)) (maxTime n : Nat)
    (cities : List Nat) (es : List Nat) : Prop :=
  IsJourney edges maxTime n cities es ∧ cities.Nodup

def Adjacent (edges : Slice (alloc.vec.Vec Std.I64)) (a b : Nat) : Prop :=
  ∃ i, i < numEdges edges ∧ (edgeAt edges i).length = 3 ∧
    ((edgeVal edges i 0 = (a : Int) ∧ edgeVal edges i 1 = (b : Int)) ∨
      (edgeVal edges i 1 = (a : Int) ∧ edgeVal edges i 0 = (b : Int)))

def Connected (edges : Slice (alloc.vec.Vec Std.I64)) (a b : Nat) : Prop :=
  Relation.ReflTransGen (Adjacent edges) a b

def NoJourney (edges : Slice (alloc.vec.Vec Std.I64)) (maxTime n : Nat) : Prop :=
  ¬ ∃ cities es, IsJourney edges maxTime n cities es

def NoSimplePath (edges : Slice (alloc.vec.Vec Std.I64)) (maxTime n : Nat) : Prop :=
  ¬ ∃ cities es, IsSimplePath edges maxTime n cities es

/-- Let n = len(passingFees). A valid journey is a finite sequence of cities c_0, c_1, ..., c_k (k ≥ 0) together with a finite sequence of edges e_0, ..., e_{k-1} such that c_0 = 0, c_k = n - 1, for each i with 0 ≤ i < k the edge e_i is in edges and connects c_i and c_{i+1} (i.e., {edges[e_i][0], edges[e_i][1]} = {c_i, c_{i+1}}), and the total travel time Σ_{i=0}^{k-1} edges[e_i][2] is at most maxTime. The cost of a valid journey is the sum of passingFees[j] over the set of distinct cities j that appear in the sequence c_0, ..., c_k. The function returns a result r such that: if there is no valid journey, then r = -1; if there is at least one valid journey, then r = min{ cost(J) | J is a valid journey } and there exists a valid journey J with cost(J) = r.
  Preconditions: Let n = len(passingFees) and m = len(edges). The inputs satisfy: 1 ≤ maxTime ≤ 1000; 2 ≤ n ≤ 1000; m ≥ n - 1 and m ≤ 1000; for every j with 0 ≤ j < n, 1 ≤ passingFees[j] ≤ 1000; for every i with 0 ≤ i < m, len(edges[i]) = 3, 0 ≤ edges[i][0] < n, 0 ≤ edges[i][1] < n, edges[i][0] ≠ edges[i][1], and 1 ≤ edges[i][2] ≤ 1000. -/
theorem spec_1 (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees) :
    ∀ r, Aegis.MinCost.min_cost maxTime edges passingFees = ok r →
      (NoJourney edges (budget maxTime) (dest passingFees) → r.val = -1) ∧
      (∀ cities es, IsJourney edges (budget maxTime) (dest passingFees) cities es →
        (∃ cities' es', IsJourney edges (budget maxTime) (dest passingFees) cities' es' ∧
          (journeyCost passingFees cities' : Int) = r.val) ∧
        r.val ≤ (journeyCost passingFees cities : Int)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees), ∀ r, Aegis.MinCost.min_cost maxTime edges passingFees = ok r →
      (NoJourney edges (budget maxTime) (dest passingFees) → r.val = -1) ∧
      (∀ cities es, IsJourney edges (budget maxTime) (dest passingFees) cities es →
        (∃ cities' es', IsJourney edges (budget maxTime) (dest passingFees) cities' es' ∧
          (journeyCost passingFees cities' : Int) = r.val) ∧
        r.val ≤ (journeyCost passingFees cities : Int))) := by
  sorry

/-- For every input satisfying the preconditions, there exists an i64 value r such that min_cost maxTime edges passingFees = Result.ok r. In other words, the function never fails, panics, or overflows.
  Preconditions: Let n = len(passingFees) and m = len(edges). The inputs satisfy: 1 ≤ maxTime ≤ 1000; 2 ≤ n ≤ 1000; m ≥ n - 1 and m ≤ 1000; for every j with 0 ≤ j < n, 1 ≤ passingFees[j] ≤ 1000; for every i with 0 ≤ i < m, len(edges[i]) = 3, 0 ≤ edges[i][0] < n, 0 ≤ edges[i][1] < n, edges[i][0] ≠ edges[i][1], and 1 ≤ edges[i][2] ≤ 1000. -/
theorem spec_2 (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees) :
    ∃ r : Std.I64, Aegis.MinCost.min_cost maxTime edges passingFees = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees), ∃ r : Std.I64, Aegis.MinCost.min_cost maxTime edges passingFees = ok r) := by
  sorry

/-- Let n = len(passingFees). If the function returns a result r and r ≠ -1, then r ≥ passingFees[0] + passingFees[n-1].
  Preconditions: Let n = len(passingFees) and m = len(edges). The inputs satisfy: 1 ≤ maxTime ≤ 1000; 2 ≤ n ≤ 1000; m ≥ n - 1 and m ≤ 1000; for every j with 0 ≤ j < n, 1 ≤ passingFees[j] ≤ 1000; for every i with 0 ≤ i < m, len(edges[i]) = 3, 0 ≤ edges[i][0] < n, 0 ≤ edges[i][1] < n, edges[i][0] ≠ edges[i][1], and 1 ≤ edges[i][2] ≤ 1000. -/
theorem spec_3 (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees) :
    ∀ r, Aegis.MinCost.min_cost maxTime edges passingFees = ok r → r.val ≠ -1 →
      feeVal passingFees 0 + feeVal passingFees (dest passingFees) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees), ∀ r, Aegis.MinCost.min_cost maxTime edges passingFees = ok r → r.val ≠ -1 →
      feeVal passingFees 0 + feeVal passingFees (dest passingFees) ≤ r.val) := by
  sorry

/-- Let n = len(passingFees). If the function returns a result r and r ≠ -1, then r ≤ Σ_{j=0}^{n-1} passingFees[j].
  Preconditions: Let n = len(passingFees) and m = len(edges). The inputs satisfy: 1 ≤ maxTime ≤ 1000; 2 ≤ n ≤ 1000; m ≥ n - 1 and m ≤ 1000; for every j with 0 ≤ j < n, 1 ≤ passingFees[j] ≤ 1000; for every i with 0 ≤ i < m, len(edges[i]) = 3, 0 ≤ edges[i][0] < n, 0 ≤ edges[i][1] < n, edges[i][0] ≠ edges[i][1], and 1 ≤ edges[i][2] ≤ 1000. -/
theorem spec_4 (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees) :
    ∀ r, Aegis.MinCost.min_cost maxTime edges passingFees = ok r → r.val ≠ -1 →
      r.val ≤ (totalFees passingFees : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees), ∀ r, Aegis.MinCost.min_cost maxTime edges passingFees = ok r → r.val ≠ -1 →
      r.val ≤ (totalFees passingFees : Int)) := by
  sorry

/-- Let n = len(passingFees). If the function returns a result r and r ≠ -1, then there exists a valid journey from city 0 to city n-1 (as defined in the main specification) with total travel time at most maxTime and cost exactly r.
  Preconditions: Let n = len(passingFees) and m = len(edges). The inputs satisfy: 1 ≤ maxTime ≤ 1000; 2 ≤ n ≤ 1000; m ≥ n - 1 and m ≤ 1000; for every j with 0 ≤ j < n, 1 ≤ passingFees[j] ≤ 1000; for every i with 0 ≤ i < m, len(edges[i]) = 3, 0 ≤ edges[i][0] < n, 0 ≤ edges[i][1] < n, edges[i][0] ≠ edges[i][1], and 1 ≤ edges[i][2] ≤ 1000. -/
theorem spec_5 (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees) :
    ∀ r, Aegis.MinCost.min_cost maxTime edges passingFees = ok r → r.val ≠ -1 →
      ∃ cities es, IsJourney edges (budget maxTime) (dest passingFees) cities es ∧
        (journeyCost passingFees cities : Int) = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees), ∀ r, Aegis.MinCost.min_cost maxTime edges passingFees = ok r → r.val ≠ -1 →
      ∃ cities es, IsJourney edges (budget maxTime) (dest passingFees) cities es ∧
        (journeyCost passingFees cities : Int) = r.val) := by
  sorry

/-- Let n = len(passingFees). If the function returns a result r and r ≠ -1, then for every valid journey from city 0 to city n-1 (as defined in the main specification) with total travel time at most maxTime, the cost of that journey is at least r.
  Preconditions: Let n = len(passingFees) and m = len(edges). The inputs satisfy: 1 ≤ maxTime ≤ 1000; 2 ≤ n ≤ 1000; m ≥ n - 1 and m ≤ 1000; for every j with 0 ≤ j < n, 1 ≤ passingFees[j] ≤ 1000; for every i with 0 ≤ i < m, len(edges[i]) = 3, 0 ≤ edges[i][0] < n, 0 ≤ edges[i][1] < n, edges[i][0] ≠ edges[i][1], and 1 ≤ edges[i][2] ≤ 1000. -/
theorem spec_6 (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees) :
    ∀ r, Aegis.MinCost.min_cost maxTime edges passingFees = ok r → r.val ≠ -1 →
      ∀ cities es, IsJourney edges (budget maxTime) (dest passingFees) cities es →
        r.val ≤ (journeyCost passingFees cities : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees), ∀ r, Aegis.MinCost.min_cost maxTime edges passingFees = ok r → r.val ≠ -1 →
      ∀ cities es, IsJourney edges (budget maxTime) (dest passingFees) cities es →
        r.val ≤ (journeyCost passingFees cities : Int)) := by
  sorry

/-- Let n = len(passingFees). Whenever the function returns a result r, r = -1 if and only if there is no valid journey from city 0 to city n-1 with total travel time at most maxTime.
  Preconditions: Let n = len(passingFees) and m = len(edges). The inputs satisfy: 1 ≤ maxTime ≤ 1000; 2 ≤ n ≤ 1000; m ≥ n - 1 and m ≤ 1000; for every j with 0 ≤ j < n, 1 ≤ passingFees[j] ≤ 1000; for every i with 0 ≤ i < m, len(edges[i]) = 3, 0 ≤ edges[i][0] < n, 0 ≤ edges[i][1] < n, edges[i][0] ≠ edges[i][1], and 1 ≤ edges[i][2] ≤ 1000. -/
theorem spec_7 (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees) :
    ∀ r, Aegis.MinCost.min_cost maxTime edges passingFees = ok r →
      (r.val = -1 ↔ NoJourney edges (budget maxTime) (dest passingFees)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees), ∀ r, Aegis.MinCost.min_cost maxTime edges passingFees = ok r →
      (r.val = -1 ↔ NoJourney edges (budget maxTime) (dest passingFees))) := by
  sorry

/-- Let n = len(passingFees). If the function returns a result r and r ≠ -1, then there exists a simple path from city 0 to city n-1 with total travel time at most maxTime and cost exactly r. A simple path is a sequence of distinct cities c_0, c_1, ..., c_k with c_0 = 0, c_k = n-1, c_i ≠ c_j for all i ≠ j, and for each i with 0 ≤ i < k there is an edge in edges connecting c_i and c_{i+1}; the cost is the sum of passingFees over these cities, and the total time is the sum of the travel times of chosen edges.
  Preconditions: Let n = len(passingFees) and m = len(edges). The inputs satisfy: 1 ≤ maxTime ≤ 1000; 2 ≤ n ≤ 1000; m ≥ n - 1 and m ≤ 1000; for every j with 0 ≤ j < n, 1 ≤ passingFees[j] ≤ 1000; for every i with 0 ≤ i < m, len(edges[i]) = 3, 0 ≤ edges[i][0] < n, 0 ≤ edges[i][1] < n, edges[i][0] ≠ edges[i][1], and 1 ≤ edges[i][2] ≤ 1000. -/
theorem spec_8 (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees) :
    ∀ r, Aegis.MinCost.min_cost maxTime edges passingFees = ok r → r.val ≠ -1 →
      ∃ cities es, IsSimplePath edges (budget maxTime) (dest passingFees) cities es ∧
        (journeyCost passingFees cities : Int) = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees), ∀ r, Aegis.MinCost.min_cost maxTime edges passingFees = ok r → r.val ≠ -1 →
      ∃ cities es, IsSimplePath edges (budget maxTime) (dest passingFees) cities es ∧
        (journeyCost passingFees cities : Int) = r.val) := by
  sorry

/-- Let n = len(passingFees). Let P be the set of all simple paths from city 0 to city n-1 with total travel time at most maxTime (a simple path is a sequence of distinct cities c_0, ..., c_k with c_0 = 0, c_k = n-1, and for each consecutive pair there is an edge in edges connecting them; the total time is the sum of the travel times of chosen edges, and the cost is the sum of passingFees over the cities in the sequence). If P is empty, the function returns r = -1; otherwise, the function returns r = min{ cost(p) | p ∈ P } and there exists p ∈ P with cost(p) = r.
  Preconditions: Let n = len(passingFees) and m = len(edges). The inputs satisfy: 1 ≤ maxTime ≤ 1000; 2 ≤ n ≤ 1000; m ≥ n - 1 and m ≤ 1000; for every j with 0 ≤ j < n, 1 ≤ passingFees[j] ≤ 1000; for every i with 0 ≤ i < m, len(edges[i]) = 3, 0 ≤ edges[i][0] < n, 0 ≤ edges[i][1] < n, edges[i][0] ≠ edges[i][1], and 1 ≤ edges[i][2] ≤ 1000. -/
theorem spec_9 (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees) :
    ∀ r, Aegis.MinCost.min_cost maxTime edges passingFees = ok r →
      (NoSimplePath edges (budget maxTime) (dest passingFees) → r.val = -1) ∧
      (∀ cities es, IsSimplePath edges (budget maxTime) (dest passingFees) cities es →
        (∃ cities' es', IsSimplePath edges (budget maxTime) (dest passingFees) cities' es' ∧
          (journeyCost passingFees cities' : Int) = r.val) ∧
        r.val ≤ (journeyCost passingFees cities : Int)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees), ∀ r, Aegis.MinCost.min_cost maxTime edges passingFees = ok r →
      (NoSimplePath edges (budget maxTime) (dest passingFees) → r.val = -1) ∧
      (∀ cities es, IsSimplePath edges (budget maxTime) (dest passingFees) cities es →
        (∃ cities' es', IsSimplePath edges (budget maxTime) (dest passingFees) cities' es' ∧
          (journeyCost passingFees cities' : Int) = r.val) ∧
        r.val ≤ (journeyCost passingFees cities : Int))) := by
  sorry

/-- Let n = len(passingFees). If there is no path from city 0 to city n-1 in the undirected graph with vertices {0, ..., n-1} and edges {{edges[i][0], edges[i][1]} | 0 ≤ i < len(edges)}, then the function returns r = -1.
  Preconditions: Let n = len(passingFees) and m = len(edges). The inputs satisfy: 1 ≤ maxTime ≤ 1000; 2 ≤ n ≤ 1000; m ≥ n - 1 and m ≤ 1000; for every j with 0 ≤ j < n, 1 ≤ passingFees[j] ≤ 1000; for every i with 0 ≤ i < m, len(edges[i]) = 3, 0 ≤ edges[i][0] < n, 0 ≤ edges[i][1] < n, edges[i][0] ≠ edges[i][1], and 1 ≤ edges[i][2] ≤ 1000. -/
theorem spec_10 (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees) :
    ∀ r, Aegis.MinCost.min_cost maxTime edges passingFees = ok r →
      ¬ Connected edges 0 (dest passingFees) → r.val = -1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (maxTime : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (passingFees : Slice Std.I64) (h : InputsValid maxTime edges passingFees), ∀ r, Aegis.MinCost.min_cost maxTime edges passingFees = ok r →
      ¬ Connected edges 0 (dest passingFees) → r.val = -1) := by
  sorry

end AegisSpec.MinCost
