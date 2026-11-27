import Aegis.EdgeScore.Code.Funs

/-!
# Specifications of `Aegis.EdgeScore.edge_score`

LeetCode problem `node-with-highest-edge-score`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.EdgeScore

def edgeList (edges : Slice I64) : List Int :=
  edges.val.map (fun x => x.val)

def score (edges : Slice I64) (n : Nat) (i : Int) : Int :=
  (((List.range n).filter (fun j => (edgeList edges)[j]? = some i)).map
    (fun j => (j : Int))).sum

/-- Let score(i) = sum of j over all j with 0 <= j < n and edges[j] = i (empty sum 0). The function returns a result r (it does not fail), and r is an integer node index such that: 0 <= r < n; score(r) >= score(k) for every k with 0 <= k < n; and for every k with 0 <= k < n, if score(k) = score(r) then r <= k. Equivalently, r is the smallest index among all nodes whose edge score is maximal.
  Preconditions: n = len(edges); 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= edges[i] < n and edges[i] != i. -/
theorem spec_1 (edges : Slice I64) (n : Nat)
    (hlen : n = edges.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hvalid : ∀ i : Nat, i < n → ∃ x : I64, edges.val[i]? = some x ∧
      0 ≤ x.val ∧ x.val < (n : Int) ∧ x.val ≠ (i : Int)) :
    ∃ r : I64, Aegis.EdgeScore.edge_score edges = ok r ∧
      0 ≤ r.val ∧ r.val < (n : Int) ∧
      (∀ k : Int, 0 ≤ k → k < (n : Int) → score edges n k ≤ score edges n r.val) ∧
      (∀ k : Int, 0 ≤ k → k < (n : Int) →
        score edges n k = score edges n r.val → r.val ≤ k) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (edges : Slice I64) (n : Nat)
    (hlen : n = edges.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hvalid : ∀ i : Nat, i < n → ∃ x : I64, edges.val[i]? = some x ∧
      0 ≤ x.val ∧ x.val < (n : Int) ∧ x.val ≠ (i : Int)), ∃ r : I64, Aegis.EdgeScore.edge_score edges = ok r ∧
      0 ≤ r.val ∧ r.val < (n : Int) ∧
      (∀ k : Int, 0 ≤ k → k < (n : Int) → score edges n k ≤ score edges n r.val) ∧
      (∀ k : Int, 0 ≤ k → k < (n : Int) →
        score edges n k = score edges n r.val → r.val ≤ k)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail (no overflow, out-of-bounds access, or panic).
  Preconditions: n = len(edges); 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= edges[i] < n and edges[i] != i. -/
theorem spec_2 (edges : Slice I64) (n : Nat)
    (hlen : n = edges.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hvalid : ∀ i : Nat, i < n → ∃ x : I64, edges.val[i]? = some x ∧
      0 ≤ x.val ∧ x.val < (n : Int) ∧ x.val ≠ (i : Int)) :
    ∃ r : I64, Aegis.EdgeScore.edge_score edges = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (edges : Slice I64) (n : Nat)
    (hlen : n = edges.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hvalid : ∀ i : Nat, i < n → ∃ x : I64, edges.val[i]? = some x ∧
      0 ≤ x.val ∧ x.val < (n : Int) ∧ x.val ≠ (i : Int)), ∃ r : I64, Aegis.EdgeScore.edge_score edges = ok r) := by
  sorry

/-- The function returns a result r and 0 <= r < n.
  Preconditions: n = len(edges); 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= edges[i] < n and edges[i] != i. -/
theorem spec_3 (edges : Slice I64) (n : Nat)
    (hlen : n = edges.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hvalid : ∀ i : Nat, i < n → ∃ x : I64, edges.val[i]? = some x ∧
      0 ≤ x.val ∧ x.val < (n : Int) ∧ x.val ≠ (i : Int)) :
    ∃ r : I64, Aegis.EdgeScore.edge_score edges = ok r ∧
      0 ≤ r.val ∧ r.val < (n : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (edges : Slice I64) (n : Nat)
    (hlen : n = edges.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hvalid : ∀ i : Nat, i < n → ∃ x : I64, edges.val[i]? = some x ∧
      0 ≤ x.val ∧ x.val < (n : Int) ∧ x.val ≠ (i : Int)), ∃ r : I64, Aegis.EdgeScore.edge_score edges = ok r ∧
      0 ≤ r.val ∧ r.val < (n : Int)) := by
  sorry

/-- Let score(i) = sum of j over all j with 0 <= j < n and edges[j] = i (empty sum 0). The function returns a result r and score(r) >= score(k) for every k with 0 <= k < n.
  Preconditions: n = len(edges); 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= edges[i] < n and edges[i] != i. -/
theorem spec_4 (edges : Slice I64) (n : Nat)
    (hlen : n = edges.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hvalid : ∀ i : Nat, i < n → ∃ x : I64, edges.val[i]? = some x ∧
      0 ≤ x.val ∧ x.val < (n : Int) ∧ x.val ≠ (i : Int)) :
    ∃ r : I64, Aegis.EdgeScore.edge_score edges = ok r ∧
      (∀ k : Int, 0 ≤ k → k < (n : Int) → score edges n k ≤ score edges n r.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (edges : Slice I64) (n : Nat)
    (hlen : n = edges.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hvalid : ∀ i : Nat, i < n → ∃ x : I64, edges.val[i]? = some x ∧
      0 ≤ x.val ∧ x.val < (n : Int) ∧ x.val ≠ (i : Int)), ∃ r : I64, Aegis.EdgeScore.edge_score edges = ok r ∧
      (∀ k : Int, 0 ≤ k → k < (n : Int) → score edges n k ≤ score edges n r.val)) := by
  sorry

/-- Let score(i) = sum of j over all j with 0 <= j < n and edges[j] = i (empty sum 0). The function returns a result r and for every k with 0 <= k < r, score(k) < score(r).
  Preconditions: n = len(edges); 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= edges[i] < n and edges[i] != i. -/
theorem spec_5 (edges : Slice I64) (n : Nat)
    (hlen : n = edges.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hvalid : ∀ i : Nat, i < n → ∃ x : I64, edges.val[i]? = some x ∧
      0 ≤ x.val ∧ x.val < (n : Int) ∧ x.val ≠ (i : Int)) :
    ∃ r : I64, Aegis.EdgeScore.edge_score edges = ok r ∧
      (∀ k : Int, 0 ≤ k → k < r.val → score edges n k < score edges n r.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (edges : Slice I64) (n : Nat)
    (hlen : n = edges.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hvalid : ∀ i : Nat, i < n → ∃ x : I64, edges.val[i]? = some x ∧
      0 ≤ x.val ∧ x.val < (n : Int) ∧ x.val ≠ (i : Int)), ∃ r : I64, Aegis.EdgeScore.edge_score edges = ok r ∧
      (∀ k : Int, 0 ≤ k → k < r.val → score edges n k < score edges n r.val)) := by
  sorry

/-- Let score(i) = sum of j over all j with 0 <= j < n and edges[j] = i (empty sum 0). The function returns a result r and n - 1 <= score(r) <= n*(n-1)/2.
  Preconditions: n = len(edges); 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= edges[i] < n and edges[i] != i. -/
theorem spec_6 (edges : Slice I64) (n : Nat)
    (hlen : n = edges.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hvalid : ∀ i : Nat, i < n → ∃ x : I64, edges.val[i]? = some x ∧
      0 ≤ x.val ∧ x.val < (n : Int) ∧ x.val ≠ (i : Int)) :
    ∃ r : I64, Aegis.EdgeScore.edge_score edges = ok r ∧
      (n : Int) - 1 ≤ score edges n r.val ∧
      score edges n r.val ≤ ((n : Int) * ((n : Int) - 1)) / 2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (edges : Slice I64) (n : Nat)
    (hlen : n = edges.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hvalid : ∀ i : Nat, i < n → ∃ x : I64, edges.val[i]? = some x ∧
      0 ≤ x.val ∧ x.val < (n : Int) ∧ x.val ≠ (i : Int)), ∃ r : I64, Aegis.EdgeScore.edge_score edges = ok r ∧
      (n : Int) - 1 ≤ score edges n r.val ∧
      score edges n r.val ≤ ((n : Int) * ((n : Int) - 1)) / 2) := by
  sorry

/-- The function returns a result r and there exists j with 0 <= j < n such that edges[j] = r.
  Preconditions: n = len(edges); 2 <= n <= 100000; for every i with 0 <= i < n, 0 <= edges[i] < n and edges[i] != i. -/
theorem spec_7 (edges : Slice I64) (n : Nat)
    (hlen : n = edges.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hvalid : ∀ i : Nat, i < n → ∃ x : I64, edges.val[i]? = some x ∧
      0 ≤ x.val ∧ x.val < (n : Int) ∧ x.val ≠ (i : Int)) :
    ∃ r : I64, Aegis.EdgeScore.edge_score edges = ok r ∧
      ∃ j : Nat, j < n ∧ (edgeList edges)[j]? = some r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (edges : Slice I64) (n : Nat)
    (hlen : n = edges.val.length)
    (hlo : 2 ≤ n) (hhi : n ≤ 100000)
    (hvalid : ∀ i : Nat, i < n → ∃ x : I64, edges.val[i]? = some x ∧
      0 ≤ x.val ∧ x.val < (n : Int) ∧ x.val ≠ (i : Int)), ∃ r : I64, Aegis.EdgeScore.edge_score edges = ok r ∧
      ∃ j : Nat, j < n ∧ (edgeList edges)[j]? = some r.val) := by
  sorry

end AegisSpec.EdgeScore
