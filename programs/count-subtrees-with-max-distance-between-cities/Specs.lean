import Aegis.CountSubgraphsForEachDiameter.Code.Funs

/-!
# Specifications of `Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter`

LeetCode problem `count-subtrees-with-max-distance-between-cities`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountSubgraphsForEachDiameter

def vertexSet (n : ℤ) : Finset ℤ := (Finset.range n.toNat).image (fun k : ℕ => (k : ℤ) + 1)

def edgeEnds (e : alloc.vec.Vec I64) : Option (ℤ × ℤ) :=
  match e.val with
  | [a, b] => some (a.val, b.val)
  | _ => none

def Adj (edges : Slice (alloc.vec.Vec I64)) (u v : ℤ) : Prop :=
  u ≠ v ∧ ∃ e ∈ edges.val, edgeEnds e = some (u, v) ∨ edgeEnds e = some (v, u)

def IsChain (edges : Slice (alloc.vec.Vec I64)) : List ℤ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => Adj edges a b ∧ IsChain edges (b :: rest)

def IsWalk (edges : Slice (alloc.vec.Vec I64)) (u v : ℤ) (p : List ℤ) : Prop :=
  p.head? = some u ∧ p.getLast? = some v ∧ IsChain edges p

def IsSimplePath (edges : Slice (alloc.vec.Vec I64)) (u v : ℤ) (p : List ℤ) : Prop :=
  IsWalk edges u v p ∧ p.Nodup

def IsTree (n : ℤ) (edges : Slice (alloc.vec.Vec I64)) : Prop :=
  ∀ u ∈ vertexSet n, ∀ v ∈ vertexSet n, ∃! p : List ℤ, IsSimplePath edges u v p

noncomputable def dist (edges : Slice (alloc.vec.Vec I64)) (u v : ℤ) : ℕ :=
  sInf {d : ℕ | ∃ p : List ℤ, IsSimplePath edges u v p ∧ p.length = d + 1}

def IsConnectedSubset (edges : Slice (alloc.vec.Vec I64)) (S : Finset ℤ) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ∀ p : List ℤ, IsSimplePath edges u v p → ∀ x ∈ p, x ∈ S

noncomputable def subsetDiameter (edges : Slice (alloc.vec.Vec I64)) (S : Finset ℤ) : ℕ :=
  ((S.product S).filter (fun q : ℤ × ℤ => q.1 ≠ q.2)).sup (fun q => dist edges q.1 q.2)

noncomputable def graphDiameter (n : ℤ) (edges : Slice (alloc.vec.Vec I64)) : ℕ :=
  subsetDiameter edges (vertexSet n)

noncomputable def countWithDiameter (n : ℤ) (edges : Slice (alloc.vec.Vec I64)) (d : ℕ) : ℕ := by
  classical
  exact ((vertexSet n).powerset.filter fun S =>
    (2 ≤ S.card ∧ IsConnectedSubset edges S ∧ subsetDiameter edges S = d)).card

noncomputable def countConnectedSubsets (n : ℤ) (edges : Slice (alloc.vec.Vec I64)) : ℕ := by
  classical
  exact ((vertexSet n).powerset.filter fun S => (2 ≤ S.card ∧ IsConnectedSubset edges S)).card

def entry (r : alloc.vec.Vec I64) (i : ℕ) : ℤ := (r.val.getD i 0#i64).val

structure TreeInput (n : ℤ) (edges : Slice (alloc.vec.Vec I64)) : Prop where

  n_lower : 2 ≤ n

  n_upper : n ≤ 15

  edges_length : (edges.val.length : ℤ) = n - 1

  edge_length : ∀ e ∈ edges.val, e.val.length = 2

  edge_lower : ∀ e ∈ edges.val, ∀ x ∈ e.val, 1 ≤ x.val

  edge_upper : ∀ e ∈ edges.val, ∀ x ∈ e.val, x.val ≤ n

  is_tree : IsTree n edges

def IsPathGraph (n : ℤ) (edges : Slice (alloc.vec.Vec I64)) : Prop :=
  ∃ vs : List ℤ,
    vs.length = n.toNat ∧ vs.Nodup ∧ (∀ x ∈ vs, x ∈ vertexSet n) ∧
      ∀ x y : ℤ,
        Adj edges x y ↔
          ∃ (i : ℕ) (hi : i + 1 < vs.length),
            (x = vs.get ⟨i, by omega⟩ ∧ y = vs.get ⟨i + 1, hi⟩) ∨
            (y = vs.get ⟨i, by omega⟩ ∧ x = vs.get ⟨i + 1, hi⟩)

def IsStarGraph (n : ℤ) (edges : Slice (alloc.vec.Vec I64)) : Prop :=
  ∃ c ∈ vertexSet n,
    ∀ x y : ℤ,
      Adj edges x y ↔
        (x = c ∧ y ∈ vertexSet n ∧ y ≠ c) ∨ (y = c ∧ x ∈ vertexSet n ∧ x ≠ c)

def SameOrReversed (e e' : alloc.vec.Vec I64) : Prop :=
  e' = e ∨ ∃ a b : I64, e.val = [a, b] ∧ e'.val = [b, a]

/-- The function returns a result r and: (1) len(r) = n-1; (2) for every d with 1 <= d <= n-1, r[d-1] is exactly the number of subsets S of {1,...,n} such that S is connected in G (for every u,v in S, all vertices on the unique path between u and v in G lie in S), |S| >= 2, and max{dist_G(u,v) : u,v in S, u != v} = d. Here dist_G(u,v) is the number of edges on the unique simple path between u and v in G, and each subset is counted once by its set of cities.
  Preconditions: P(n, edges): n is an integer with 2 <= n <= 15; edges is a slice with len(edges) = n-1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n; let G be the undirected graph on vertex set {1,...,n} whose edges are the unordered pairs {edges[i][0], edges[i][1]} for 0 <= i < len(edges); G is a tree, i.e. it is connected and acyclic (equivalently, every two distinct vertices have a unique simple path in G). -/
theorem spec_1 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges) :
    ∃ r : alloc.vec.Vec I64,
      Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r ∧
        (r.val.length : ℤ) = n.val - 1 ∧
          ∀ (d : ℕ), 1 ≤ d → (d : ℤ) ≤ n.val - 1 →
            entry r (d - 1) = (countWithDiameter n.val edges d : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges), ∃ r : alloc.vec.Vec I64,
      Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r ∧
        (r.val.length : ℤ) = n.val - 1 ∧
          ∀ (d : ℕ), 1 ≤ d → (d : ℤ) ≤ n.val - 1 →
            entry r (d - 1) = (countWithDiameter n.val edges d : ℤ)) := by
  sorry

/-- For every input satisfying P(n, edges), the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: P(n, edges): n is an integer with 2 <= n <= 15; edges is a slice with len(edges) = n-1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n; let G be the undirected graph on vertex set {1,...,n} whose edges are the unordered pairs {edges[i][0], edges[i][1]} for 0 <= i < len(edges); G is a tree, i.e. it is connected and acyclic (equivalently, every two distinct vertices have a unique simple path in G). -/
theorem spec_2 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges) :
    ∃ r : alloc.vec.Vec I64,
      Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges), ∃ r : alloc.vec.Vec I64,
      Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying P(n, edges), len(r) = n-1.
  Preconditions: P(n, edges): n is an integer with 2 <= n <= 15; edges is a slice with len(edges) = n-1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n; let G be the undirected graph on vertex set {1,...,n} whose edges are the unordered pairs {edges[i][0], edges[i][1]} for 0 <= i < len(edges); G is a tree, i.e. it is connected and acyclic (equivalently, every two distinct vertices have a unique simple path in G). -/
theorem spec_3 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    {r : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r) :
    (r.val.length : ℤ) = n.val - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    {r : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r), (r.val.length : ℤ) = n.val - 1) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying P(n, edges), for every i with 0 <= i < len(r), r[i] >= 0.
  Preconditions: P(n, edges): n is an integer with 2 <= n <= 15; edges is a slice with len(edges) = n-1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n; let G be the undirected graph on vertex set {1,...,n} whose edges are the unordered pairs {edges[i][0], edges[i][1]} for 0 <= i < len(edges); G is a tree, i.e. it is connected and acyclic (equivalently, every two distinct vertices have a unique simple path in G). -/
theorem spec_4 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    {r : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r) :
    ∀ i : ℕ, i < r.val.length → 0 ≤ entry r i := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    {r : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r), ∀ i : ℕ, i < r.val.length → 0 ≤ entry r i) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying P(n, edges), r[0] = n-1.
  Preconditions: P(n, edges): n is an integer with 2 <= n <= 15; edges is a slice with len(edges) = n-1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n; let G be the undirected graph on vertex set {1,...,n} whose edges are the unordered pairs {edges[i][0], edges[i][1]} for 0 <= i < len(edges); G is a tree, i.e. it is connected and acyclic (equivalently, every two distinct vertices have a unique simple path in G). -/
theorem spec_5 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    {r : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r) :
    entry r 0 = n.val - 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    {r : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r), entry r 0 = n.val - 1) := by
  sorry

/-- Let T be the number of subsets S of {1,...,n} such that S is connected in G and |S| >= 2. Whenever the function returns a result r on an input satisfying P(n, edges), sum_{i=0}^{n-2} r[i] = T.
  Preconditions: P(n, edges): n is an integer with 2 <= n <= 15; edges is a slice with len(edges) = n-1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n; let G be the undirected graph on vertex set {1,...,n} whose edges are the unordered pairs {edges[i][0], edges[i][1]} for 0 <= i < len(edges); G is a tree, i.e. it is connected and acyclic (equivalently, every two distinct vertices have a unique simple path in G). -/
theorem spec_6 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    {r : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r) :
    (Finset.range (n.val - 1).toNat).sum (fun i => entry r i) =
      (countConnectedSubsets n.val edges : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    {r : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r), (Finset.range (n.val - 1).toNat).sum (fun i => entry r i) =
      (countConnectedSubsets n.val edges : ℤ)) := by
  sorry

/-- Let D = max{dist_G(u,v) : u,v in {1,...,n}, u != v}. Whenever the function returns a result r on an input satisfying P(n, edges), for every d with D < d <= n-1, r[d-1] = 0.
  Preconditions: P(n, edges): n is an integer with 2 <= n <= 15; edges is a slice with len(edges) = n-1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n; let G be the undirected graph on vertex set {1,...,n} whose edges are the unordered pairs {edges[i][0], edges[i][1]} for 0 <= i < len(edges); G is a tree, i.e. it is connected and acyclic (equivalently, every two distinct vertices have a unique simple path in G). -/
theorem spec_7 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    {r : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r) :
    ∀ (d : ℕ), graphDiameter n.val edges < d → (d : ℤ) ≤ n.val - 1 → entry r (d - 1) = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    {r : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r), ∀ (d : ℕ), graphDiameter n.val edges < d → (d : ℤ) ≤ n.val - 1 → entry r (d - 1) = 0) := by
  sorry

/-- Let D = max{dist_G(u,v) : u,v in {1,...,n}, u != v}. Whenever the function returns a result r on an input satisfying P(n, edges), for every d with 1 <= d <= D, r[d-1] >= 1.
  Preconditions: P(n, edges): n is an integer with 2 <= n <= 15; edges is a slice with len(edges) = n-1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n; let G be the undirected graph on vertex set {1,...,n} whose edges are the unordered pairs {edges[i][0], edges[i][1]} for 0 <= i < len(edges); G is a tree, i.e. it is connected and acyclic (equivalently, every two distinct vertices have a unique simple path in G). -/
theorem spec_8 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    {r : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r) :
    ∀ (d : ℕ), 1 ≤ d → (d : ℤ) ≤ (graphDiameter n.val edges : ℤ) → 1 ≤ entry r (d - 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    {r : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r), ∀ (d : ℕ), 1 ≤ d → (d : ℤ) ≤ (graphDiameter n.val edges : ℤ) → 1 ≤ entry r (d - 1)) := by
  sorry

/-- For every permutation edges' of the entries of edges, if the function returns r on (n, edges) and r' on (n, edges'), then r = r'.
  Preconditions: P(n, edges): n is an integer with 2 <= n <= 15; edges is a slice with len(edges) = n-1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n; let G be the undirected graph on vertex set {1,...,n} whose edges are the unordered pairs {edges[i][0], edges[i][1]} for 0 <= i < len(edges); G is a tree, i.e. it is connected and acyclic (equivalently, every two distinct vertices have a unique simple path in G). -/
theorem spec_9 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    (edges' : Slice (alloc.vec.Vec I64)) (hperm : edges.val.Perm edges'.val)
    {r r' : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r)
    (hr' : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    (edges' : Slice (alloc.vec.Vec I64)) (hperm : edges.val.Perm edges'.val)
    {r r' : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r)
    (hr' : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges' = ok r'), r.val = r'.val) := by
  sorry

/-- For every slice edges' with len(edges') = len(edges) such that for each i, edges'[i] is either [edges[i][0], edges[i][1]] or [edges[i][1], edges[i][0]], if the function returns r on (n, edges) and r' on (n, edges'), then r = r'.
  Preconditions: P(n, edges): n is an integer with 2 <= n <= 15; edges is a slice with len(edges) = n-1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n; let G be the undirected graph on vertex set {1,...,n} whose edges are the unordered pairs {edges[i][0], edges[i][1]} for 0 <= i < len(edges); G is a tree, i.e. it is connected and acyclic (equivalently, every two distinct vertices have a unique simple path in G). -/
theorem spec_10 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    (edges' : Slice (alloc.vec.Vec I64)) (hlen : edges'.val.length = edges.val.length)
    (hcomp : ∀ (i : ℕ) (h₁ : i < edges.val.length) (h₂ : i < edges'.val.length),
      SameOrReversed (edges.val.get ⟨i, h₁⟩) (edges'.val.get ⟨i, h₂⟩))
    {r r' : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r)
    (hr' : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    (edges' : Slice (alloc.vec.Vec I64)) (hlen : edges'.val.length = edges.val.length)
    (hcomp : ∀ (i : ℕ) (h₁ : i < edges.val.length) (h₂ : i < edges'.val.length),
      SameOrReversed (edges.val.get ⟨i, h₁⟩) (edges'.val.get ⟨i, h₂⟩))
    {r r' : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r)
    (hr' : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges' = ok r'), r.val = r'.val) := by
  sorry

/-- Let D = max{dist_G(u,v) : u,v in {1,...,n}, u != v}. Whenever the function returns a result r on an input satisfying P(n, edges): if D = n-1 then r[n-2] = 1; if D < n-1 then r[n-2] = 0.
  Preconditions: P(n, edges): n is an integer with 2 <= n <= 15; edges is a slice with len(edges) = n-1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n; let G be the undirected graph on vertex set {1,...,n} whose edges are the unordered pairs {edges[i][0], edges[i][1]} for 0 <= i < len(edges); G is a tree, i.e. it is connected and acyclic (equivalently, every two distinct vertices have a unique simple path in G). -/
theorem spec_11 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    {r : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r) :
    (graphDiameter n.val edges = (n.val - 1).toNat → entry r (n.val - 2).toNat = 1) ∧
      (graphDiameter n.val edges < (n.val - 1).toNat → entry r (n.val - 2).toNat = 0) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    {r : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r), (graphDiameter n.val edges = (n.val - 1).toNat → entry r (n.val - 2).toNat = 1) ∧
      (graphDiameter n.val edges < (n.val - 1).toNat → entry r (n.val - 2).toNat = 0)) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying these preconditions, for every d with 1 <= d <= n-1, r[d-1] = n-d.
  Preconditions: P(n, edges): n is an integer with 2 <= n <= 15; edges is a slice with len(edges) = n-1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n; let G be the undirected graph on vertex set {1,...,n} whose edges are the unordered pairs {edges[i][0], edges[i][1]} for 0 <= i < len(edges); G is a tree, i.e. it is connected and acyclic (equivalently, every two distinct vertices have a unique simple path in G). Additionally, G is a path: there is an ordering v_0,...,v_{n-1} of {1,...,n} such that the set of edges of G is exactly {{v_i,v_{i+1}} : 0 <= i < n-1}. -/
theorem spec_12 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    (hpath : IsPathGraph n.val edges) {r : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r) :
    ∀ (d : ℕ), 1 ≤ d → (d : ℤ) ≤ n.val - 1 → entry r (d - 1) = n.val - (d : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    (hpath : IsPathGraph n.val edges) {r : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r), ∀ (d : ℕ), 1 ≤ d → (d : ℤ) ≤ n.val - 1 → entry r (d - 1) = n.val - (d : ℤ)) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying these preconditions, r[0] = n-1, r[1] = 2^{n-1} - n, and for every d with 3 <= d <= n-1, r[d-1] = 0.
  Preconditions: P(n, edges): n is an integer with 2 <= n <= 15; edges is a slice with len(edges) = n-1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 1 <= edges[i][0] <= n and 1 <= edges[i][1] <= n; let G be the undirected graph on vertex set {1,...,n} whose edges are the unordered pairs {edges[i][0], edges[i][1]} for 0 <= i < len(edges); G is a tree, i.e. it is connected and acyclic (equivalently, every two distinct vertices have a unique simple path in G). Additionally, n >= 3 and G is a star: there is a vertex c in {1,...,n} such that the set of edges of G is exactly {{c,v} : v in {1,...,n} and v != c}. -/
theorem spec_13 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    (hn : 3 ≤ n.val) (hstar : IsStarGraph n.val edges) {r : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r) :
    entry r 0 = n.val - 1 ∧ entry r 1 = (2 : ℤ) ^ (n.val - 1).toNat - n.val ∧
      ∀ (d : ℕ), 3 ≤ d → (d : ℤ) ≤ n.val - 1 → entry r (d - 1) = 0 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : TreeInput n.val edges)
    (hn : 3 ≤ n.val) (hstar : IsStarGraph n.val edges) {r : alloc.vec.Vec I64}
    (hr : Aegis.CountSubgraphsForEachDiameter.count_subgraphs_for_each_diameter n edges = ok r), entry r 0 = n.val - 1 ∧ entry r 1 = (2 : ℤ) ^ (n.val - 1).toNat - n.val ∧
      ∀ (d : ℕ), 3 ≤ d → (d : ℤ) ≤ n.val - 1 → entry r (d - 1) = 0) := by
  sorry

end AegisSpec.CountSubgraphsForEachDiameter
