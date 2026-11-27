import Aegis.MinimumCost.Code.Funs

/-!
# Specifications of `Aegis.MinimumCost.minimum_cost`

LeetCode problem `minimum-cost-walk-in-weighted-graph`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumCost

  open Aegis.MinimumCost (minimum_cost)

  def ivec (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map IScalar.val

  def out (r : alloc.vec.Vec Std.I64) (i : ℕ) : ℤ := (r.val[i]!).val

  def edgeTriples (edges : Slice (alloc.vec.Vec Std.I64)) : List (ℤ × ℤ × ℤ) :=
    (edges.val.map ivec).filterMap fun row =>
      match row with
      | [u, v, w] => some (u, v, w)
      | _ => none

  def walkFrom (G : List (ℤ × ℤ × ℤ)) : List (ℤ × ℤ × ℤ) → ℤ → ℤ → Prop
    | [], s, t => s = t
    | e :: rest, s, t =>
        e ∈ G ∧ ((e.1 = s ∧ walkFrom G rest e.2.1 t) ∨ (e.2.1 = s ∧ walkFrom G rest e.1 t))

  def allOnes : ℕ := 2 ^ 64 - 1

  def walkCost : List (ℤ × ℤ × ℤ) → ℕ
    | [] => allOnes
    | e :: rest => e.2.2.toNat &&& walkCost rest

  def reachable (G : List (ℤ × ℤ × ℤ)) (s t : ℤ) : Prop := ∃ W, walkFrom G W s t

  def sameComp (G : List (ℤ × ℤ × ℤ)) (s t : ℤ) : Prop := reachable G s t ∨ reachable G t s

  def isMinCost (G : List (ℤ × ℤ × ℤ)) (s t : ℤ) (v : ℤ) : Prop :=
    (∃ W, walkFrom G W s t ∧ (walkCost W : ℤ) = v) ∧
      ∀ W, walkFrom G W s t → v ≤ (walkCost W : ℤ)

  noncomputable def compAnd (G : List (ℤ × ℤ × ℤ)) (s : ℤ) : ℕ := by
    classical
    exact (G.filter fun e => decide (sameComp G e.1 s ∧ sameComp G e.2.1 s)).foldr
      (fun e acc => e.2.2.toNat &&& acc) allOnes

  def edgesWF (n : ℤ) (edges : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    edges.val.length ≤ 100000 ∧
      ∀ (j : ℕ) (hj : j < edges.val.length),
        ∃ u v w : ℤ, ivec (edges.val[j]) = [u, v, w] ∧
          0 ≤ u ∧ u ≤ n - 1 ∧ 0 ≤ v ∧ v ≤ n - 1 ∧ u ≠ v ∧ 0 ≤ w ∧ w ≤ 100000

  def queryWF (n : ℤ) (query : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    1 ≤ query.val.length ∧ query.val.length ≤ 100000 ∧
      ∀ (i : ℕ) (hi : i < query.val.length),
        ∃ s t : ℤ, ivec (query.val[i]) = [s, t] ∧
          0 ≤ s ∧ s ≤ n - 1 ∧ 0 ≤ t ∧ t ≤ n - 1 ∧ s ≠ t

  /-- Let G be the undirected multigraph whose vertices are 0,...,n-1 and which has one edge between edges[j][0] and edges[j][1] of weight edges[j][2] for every j with 0 <= j < len(edges). For a walk W in G, let cost(W) be the bitwise AND of the weights of all edges traversed by W, counting repetitions. Whenever the function returns a result r, it holds that len(r) = len(query) and, for every i with 0 <= i < len(query), writing s = query[i][0] and t = query[i][1], if there exists a walk from s to t in G then r[i] is the minimum of cost(W) over all walks W from s to t in G, and if there is no walk from s to t in G then r[i] = -1.
    Preconditions: n is an integer with 2 <= n <= 100000. len(edges) <= 100000, and for every j with 0 <= j < len(edges), len(edges[j]) = 3, 0 <= edges[j][0] <= n-1, 0 <= edges[j][1] <= n-1, edges[j][0] != edges[j][1], and 0 <= edges[j][2] <= 100000. Also 1 <= len(query) <= 100000, and for every i with 0 <= i < len(query), len(query[i]) = 2, 0 <= query[i][0] <= n-1, 0 <= query[i][1] <= n-1, and query[i][0] != query[i][1]. -/
  theorem spec_1
      (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
      (hn : 2 ≤ n.val ∧ n.val ≤ 100000)
      (hedges : edgesWF n.val edges)
      (hquery : queryWF n.val query) :
      ∀ (r : alloc.vec.Vec Std.I64), minimum_cost n edges query = ok r →
        r.val.length = query.val.length ∧
          ∀ (i : ℕ) (hi : i < query.val.length),
            ∀ s t : ℤ, ivec (query.val[i]) = [s, t] →
              (reachable (edgeTriples edges) s t →
                  isMinCost (edgeTriples edges) s t (out r i)) ∧
                (¬ reachable (edgeTriples edges) s t → out r i = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
        (hn : 2 ≤ n.val ∧ n.val ≤ 100000)
        (hedges : edgesWF n.val edges)
        (hquery : queryWF n.val query), ∀ (r : alloc.vec.Vec Std.I64), minimum_cost n edges query = ok r →
          r.val.length = query.val.length ∧
            ∀ (i : ℕ) (hi : i < query.val.length),
              ∀ s t : ℤ, ivec (query.val[i]) = [s, t] →
                (reachable (edgeTriples edges) s t →
                    isMinCost (edgeTriples edges) s t (out r i)) ∧
                  (¬ reachable (edgeTriples edges) s t → out r i = -1)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r, and does not fail with overflow, out-of-bounds access, or panic.
    Preconditions: n is an integer with 2 <= n <= 100000. len(edges) <= 100000, and for every j with 0 <= j < len(edges), len(edges[j]) = 3, 0 <= edges[j][0] <= n-1, 0 <= edges[j][1] <= n-1, edges[j][0] != edges[j][1], and 0 <= edges[j][2] <= 100000. Also 1 <= len(query) <= 100000, and for every i with 0 <= i < len(query), len(query[i]) = 2, 0 <= query[i][0] <= n-1, 0 <= query[i][1] <= n-1, and query[i][0] != query[i][1]. -/
  theorem spec_2
      (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
      (hn : 2 ≤ n.val ∧ n.val ≤ 100000)
      (hedges : edgesWF n.val edges)
      (hquery : queryWF n.val query) :
      ∃ r : alloc.vec.Vec Std.I64, minimum_cost n edges query = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
        (hn : 2 ≤ n.val ∧ n.val ≤ 100000)
        (hedges : edgesWF n.val edges)
        (hquery : queryWF n.val query), ∃ r : alloc.vec.Vec Std.I64, minimum_cost n edges query = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(query), either r[i] = -1 or 0 <= r[i] <= 100000.
    Preconditions: n is an integer with 2 <= n <= 100000. len(edges) <= 100000, and for every j with 0 <= j < len(edges), len(edges[j]) = 3, 0 <= edges[j][0] <= n-1, 0 <= edges[j][1] <= n-1, edges[j][0] != edges[j][1], and 0 <= edges[j][2] <= 100000. Also 1 <= len(query) <= 100000, and for every i with 0 <= i < len(query), len(query[i]) = 2, 0 <= query[i][0] <= n-1, 0 <= query[i][1] <= n-1, and query[i][0] != query[i][1]. -/
  theorem spec_3
      (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
      (hn : 2 ≤ n.val ∧ n.val ≤ 100000)
      (hedges : edgesWF n.val edges)
      (hquery : queryWF n.val query)
      (r : alloc.vec.Vec Std.I64) (hr : minimum_cost n edges query = ok r) :
      ∀ (i : ℕ) (hi : i < query.val.length), out r i = -1 ∨ 0 ≤ out r i ∧ out r i ≤ 100000 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
        (hn : 2 ≤ n.val ∧ n.val ≤ 100000)
        (hedges : edgesWF n.val edges)
        (hquery : queryWF n.val query)
        (r : alloc.vec.Vec Std.I64) (hr : minimum_cost n edges query = ok r), ∀ (i : ℕ) (hi : i < query.val.length), out r i = -1 ∨ 0 ≤ out r i ∧ out r i ≤ 100000) := by
    sorry

  /-- Let G be the undirected multigraph whose vertices are 0,...,n-1 and which has an edge between edges[j][0] and edges[j][1] of weight edges[j][2] for every j with 0 <= j < len(edges). Whenever the function returns a result r, for every i with 0 <= i < len(query), let s = query[i][0], t = query[i][1], and let C be the connected component of G containing s. If t is also in C, then r[i] equals the bitwise AND of edges[j][2] over all j with 0 <= j < len(edges) such that both edges[j][0] and edges[j][1] belong to C.
    Preconditions: n is an integer with 2 <= n <= 100000. len(edges) <= 100000, and for every j with 0 <= j < len(edges), len(edges[j]) = 3, 0 <= edges[j][0] <= n-1, 0 <= edges[j][1] <= n-1, edges[j][0] != edges[j][1], and 0 <= edges[j][2] <= 100000. Also 1 <= len(query) <= 100000, and for every i with 0 <= i < len(query), len(query[i]) = 2, 0 <= query[i][0] <= n-1, 0 <= query[i][1] <= n-1, and query[i][0] != query[i][1]. -/
  theorem spec_4
      (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
      (hn : 2 ≤ n.val ∧ n.val ≤ 100000)
      (hedges : edgesWF n.val edges)
      (hquery : queryWF n.val query)
      (r : alloc.vec.Vec Std.I64) (hr : minimum_cost n edges query = ok r) :
      ∀ (i : ℕ) (hi : i < query.val.length),
        ∀ s t : ℤ, ivec (query.val[i]) = [s, t] →
          sameComp (edgeTriples edges) s t → out r i = (compAnd (edgeTriples edges) s : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
        (hn : 2 ≤ n.val ∧ n.val ≤ 100000)
        (hedges : edgesWF n.val edges)
        (hquery : queryWF n.val query)
        (r : alloc.vec.Vec Std.I64) (hr : minimum_cost n edges query = ok r), ∀ (i : ℕ) (hi : i < query.val.length),
          ∀ s t : ℤ, ivec (query.val[i]) = [s, t] →
            sameComp (edgeTriples edges) s t → out r i = (compAnd (edgeTriples edges) s : ℤ)) := by
    sorry

  /-- Let G be the undirected multigraph whose vertices are 0,...,n-1 and which has an edge between edges[j][0] and edges[j][1] of weight edges[j][2] for every j with 0 <= j < len(edges). Whenever the function returns a result r, for every i with 0 <= i < len(query) and r[i] != -1, there exists a walk W in G from query[i][0] to query[i][1] such that cost(W) = r[i], where cost(W) is the bitwise AND of the weights of the edges traversed by W.
    Preconditions: n is an integer with 2 <= n <= 100000. len(edges) <= 100000, and for every j with 0 <= j < len(edges), len(edges[j]) = 3, 0 <= edges[j][0] <= n-1, 0 <= edges[j][1] <= n-1, edges[j][0] != edges[j][1], and 0 <= edges[j][2] <= 100000. Also 1 <= len(query) <= 100000, and for every i with 0 <= i < len(query), len(query[i]) = 2, 0 <= query[i][0] <= n-1, 0 <= query[i][1] <= n-1, and query[i][0] != query[i][1]. -/
  theorem spec_5
      (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
      (hn : 2 ≤ n.val ∧ n.val ≤ 100000)
      (hedges : edgesWF n.val edges)
      (hquery : queryWF n.val query)
      (r : alloc.vec.Vec Std.I64) (hr : minimum_cost n edges query = ok r) :
      ∀ (i : ℕ) (hi : i < query.val.length), out r i ≠ -1 →
        ∀ s t : ℤ, ivec (query.val[i]) = [s, t] →
          ∃ W, walkFrom (edgeTriples edges) W s t ∧ (walkCost W : ℤ) = out r i := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
        (hn : 2 ≤ n.val ∧ n.val ≤ 100000)
        (hedges : edgesWF n.val edges)
        (hquery : queryWF n.val query)
        (r : alloc.vec.Vec Std.I64) (hr : minimum_cost n edges query = ok r), ∀ (i : ℕ) (hi : i < query.val.length), out r i ≠ -1 →
          ∀ s t : ℤ, ivec (query.val[i]) = [s, t] →
            ∃ W, walkFrom (edgeTriples edges) W s t ∧ (walkCost W : ℤ) = out r i) := by
    sorry

  /-- Let G be the undirected multigraph whose vertices are 0,...,n-1 and which has an edge between edges[j][0] and edges[j][1] of weight edges[j][2] for every j with 0 <= j < len(edges). Whenever the function returns a result r, for every i with 0 <= i < len(query) and r[i] != -1, every walk W in G from query[i][0] to query[i][1] satisfies r[i] <= cost(W), comparing the integer values, where cost(W) is the bitwise AND of the weights of the edges traversed by W.
    Preconditions: n is an integer with 2 <= n <= 100000. len(edges) <= 100000, and for every j with 0 <= j < len(edges), len(edges[j]) = 3, 0 <= edges[j][0] <= n-1, 0 <= edges[j][1] <= n-1, edges[j][0] != edges[j][1], and 0 <= edges[j][2] <= 100000. Also 1 <= len(query) <= 100000, and for every i with 0 <= i < len(query), len(query[i]) = 2, 0 <= query[i][0] <= n-1, 0 <= query[i][1] <= n-1, and query[i][0] != query[i][1]. -/
  theorem spec_6
      (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
      (hn : 2 ≤ n.val ∧ n.val ≤ 100000)
      (hedges : edgesWF n.val edges)
      (hquery : queryWF n.val query)
      (r : alloc.vec.Vec Std.I64) (hr : minimum_cost n edges query = ok r) :
      ∀ (i : ℕ) (hi : i < query.val.length), out r i ≠ -1 →
        ∀ s t : ℤ, ivec (query.val[i]) = [s, t] →
          ∀ W, walkFrom (edgeTriples edges) W s t → out r i ≤ (walkCost W : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
        (hn : 2 ≤ n.val ∧ n.val ≤ 100000)
        (hedges : edgesWF n.val edges)
        (hquery : queryWF n.val query)
        (r : alloc.vec.Vec Std.I64) (hr : minimum_cost n edges query = ok r), ∀ (i : ℕ) (hi : i < query.val.length), out r i ≠ -1 →
          ∀ s t : ℤ, ivec (query.val[i]) = [s, t] →
            ∀ W, walkFrom (edgeTriples edges) W s t → out r i ≤ (walkCost W : ℤ)) := by
    sorry

  /-- Let G be the undirected multigraph whose vertices are 0,...,n-1 and which has an edge between edges[j][0] and edges[j][1] of weight edges[j][2] for every j with 0 <= j < len(edges). Whenever the function returns a result r, for every i,j with 0 <= i,j < len(query), if query[i][0] = query[j][1] and query[i][1] = query[j][0], then r[i] = r[j].
    Preconditions: n is an integer with 2 <= n <= 100000. len(edges) <= 100000, and for every j with 0 <= j < len(edges), len(edges[j]) = 3, 0 <= edges[j][0] <= n-1, 0 <= edges[j][1] <= n-1, edges[j][0] != edges[j][1], and 0 <= edges[j][2] <= 100000. Also 1 <= len(query) <= 100000, and for every i with 0 <= i < len(query), len(query[i]) = 2, 0 <= query[i][0] <= n-1, 0 <= query[i][1] <= n-1, and query[i][0] != query[i][1]. -/
  theorem spec_7
      (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
      (hn : 2 ≤ n.val ∧ n.val ≤ 100000)
      (hedges : edgesWF n.val edges)
      (hquery : queryWF n.val query)
      (r : alloc.vec.Vec Std.I64) (hr : minimum_cost n edges query = ok r) :
      ∀ (i j : ℕ) (hi : i < query.val.length) (hj : j < query.val.length),
        ∀ s t s' t' : ℤ, ivec (query.val[i]) = [s, t] → ivec (query.val[j]) = [s', t'] →
          s = t' → t = s' → out r i = out r j := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
        (hn : 2 ≤ n.val ∧ n.val ≤ 100000)
        (hedges : edgesWF n.val edges)
        (hquery : queryWF n.val query)
        (r : alloc.vec.Vec Std.I64) (hr : minimum_cost n edges query = ok r), ∀ (i j : ℕ) (hi : i < query.val.length) (hj : j < query.val.length),
          ∀ s t s' t' : ℤ, ivec (query.val[i]) = [s, t] → ivec (query.val[j]) = [s', t'] →
            s = t' → t = s' → out r i = out r j) := by
    sorry

  /-- Whenever the function returns r on (n, edges, query) and returns r' on (n, edges', query), it holds that len(r) = len(r') and r[i] = r'[i] for every i with 0 <= i < len(query).
    Preconditions: n is an integer with 2 <= n <= 100000. len(edges) <= 100000, and for every j with 0 <= j < len(edges), len(edges[j]) = 3, 0 <= edges[j][0] <= n-1, 0 <= edges[j][1] <= n-1, edges[j][0] != edges[j][1], and 0 <= edges[j][2] <= 100000. Also 1 <= len(query) <= 100000, and for every i with 0 <= i < len(query), len(query[i]) = 2, 0 <= query[i][0] <= n-1, 0 <= query[i][1] <= n-1, and query[i][0] != query[i][1]. Let edges' be any permutation of the vectors in edges; edges' satisfies the same bounds. -/
  theorem spec_8
      (n : Std.I64) (edges edges' query : Slice (alloc.vec.Vec Std.I64))
      (hn : 2 ≤ n.val ∧ n.val ≤ 100000)
      (hedges : edgesWF n.val edges)
      (hedges' : edgesWF n.val edges')
      (hquery : queryWF n.val query)
      (hperm : edges'.val.Perm edges.val) :
      ∀ (r r' : alloc.vec.Vec Std.I64),
        minimum_cost n edges query = ok r → minimum_cost n edges' query = ok r' →
          r.val.length = r'.val.length ∧
            ∀ (i : ℕ) (hi : i < query.val.length), out r i = out r' i := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (edges edges' query : Slice (alloc.vec.Vec Std.I64))
        (hn : 2 ≤ n.val ∧ n.val ≤ 100000)
        (hedges : edgesWF n.val edges)
        (hedges' : edgesWF n.val edges')
        (hquery : queryWF n.val query)
        (hperm : edges'.val.Perm edges.val), ∀ (r r' : alloc.vec.Vec Std.I64),
          minimum_cost n edges query = ok r → minimum_cost n edges' query = ok r' →
            r.val.length = r'.val.length ∧
              ∀ (i : ℕ) (hi : i < query.val.length), out r i = out r' i) := by
    sorry

  /-- Whenever the function returns r on (n, edges, query) and returns r' on (n, edges, query'), it holds that r'[i] = r[pi(i)] for every i with 0 <= i < len(query).
    Preconditions: n is an integer with 2 <= n <= 100000. len(edges) <= 100000, and for every j with 0 <= j < len(edges), len(edges[j]) = 3, 0 <= edges[j][0] <= n-1, 0 <= edges[j][1] <= n-1, edges[j][0] != edges[j][1], and 0 <= edges[j][2] <= 100000. Also 1 <= len(query) <= 100000, and for every i with 0 <= i < len(query), len(query[i]) = 2, 0 <= query[i][0] <= n-1, 0 <= query[i][1] <= n-1, and query[i][0] != query[i][1]. Let query' be any permutation of the vectors in query, and let pi be a bijection on {0,...,len(query)-1} such that query'[i] = query[pi(i)] for every i. -/
  theorem spec_9
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (query query' : Slice (alloc.vec.Vec Std.I64))
      (hn : 2 ≤ n.val ∧ n.val ≤ 100000)
      (hedges : edgesWF n.val edges)
      (hquery : queryWF n.val query)
      (hquery' : queryWF n.val query')
      (hperm : query'.val.Perm query.val)
      (pi : ℕ → ℕ)
      (hpi_mem : ∀ (i : ℕ), i < query.val.length → pi i < query.val.length)
      (hpi_inj : ∀ (i j : ℕ), i < query.val.length → j < query.val.length → pi i = pi j → i = j)
      (hpi : ∀ (i : ℕ) (hi : i < query.val.length),
        query'.val[i]'(by have h := hperm.length_eq; omega) =
          query.val[pi i]'(by have := hpi_mem i hi; omega)) :
      ∀ (r r' : alloc.vec.Vec Std.I64),
        minimum_cost n edges query = ok r → minimum_cost n edges query' = ok r' →
          ∀ (i : ℕ) (hi : i < query.val.length), out r' i = out r (pi i) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (query query' : Slice (alloc.vec.Vec Std.I64))
        (hn : 2 ≤ n.val ∧ n.val ≤ 100000)
        (hedges : edgesWF n.val edges)
        (hquery : queryWF n.val query)
        (hquery' : queryWF n.val query')
        (hperm : query'.val.Perm query.val)
        (pi : ℕ → ℕ)
        (hpi_mem : ∀ (i : ℕ), i < query.val.length → pi i < query.val.length)
        (hpi_inj : ∀ (i j : ℕ), i < query.val.length → j < query.val.length → pi i = pi j → i = j)
        (hpi : ∀ (i : ℕ) (hi : i < query.val.length),
          query'.val[i]'(by have h := hperm.length_eq; omega) =
            query.val[pi i]'(by have := hpi_mem i hi; omega)), ∀ (r r' : alloc.vec.Vec Std.I64),
          minimum_cost n edges query = ok r → minimum_cost n edges query' = ok r' →
            ∀ (i : ℕ) (hi : i < query.val.length), out r' i = out r (pi i)) := by
    sorry

  end AegisSpec.MinimumCost
