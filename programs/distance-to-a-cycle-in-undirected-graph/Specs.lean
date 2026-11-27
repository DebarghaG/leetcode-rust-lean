import Aegis.DistanceToCycle.Code.Funs

/-!
# Specifications of `Aegis.DistanceToCycle.distance_to_cycle`

LeetCode problem `distance-to-a-cycle-in-undirected-graph`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.DistanceToCycle

  def vals (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map (fun x => x.val)

  def vecGet (v : alloc.vec.Vec Std.I64) (i : ℤ) : ℤ := (vals v).getD i.toNat 0

  def edgePairs (edges : List (alloc.vec.Vec Std.I64)) : List (ℤ × ℤ) :=
    edges.filterMap fun e =>
      match e.val with
      | [a, b] => some (a.val, b.val)
      | _ => none

  def canonPair (p : ℤ × ℤ) : ℤ × ℤ := (min p.1 p.2, max p.1 p.2)

  def IsGraphInput (n : ℤ) (edges : List (alloc.vec.Vec Std.I64)) : Prop :=
    (edges.length : ℤ) = n ∧
      (∀ e ∈ edges, e.val.length = 2) ∧
      (∀ p ∈ edgePairs edges, 0 ≤ p.1 ∧ p.1 < n ∧ 0 ≤ p.2 ∧ p.2 < n) ∧
      (∀ p ∈ edgePairs edges, p.1 ≠ p.2) ∧
      ((edgePairs edges).map canonPair).Nodup

  def Adj (edges : List (alloc.vec.Vec Std.I64)) (u v : ℤ) : Prop :=
    (u, v) ∈ edgePairs edges ∨ (v, u) ∈ edgePairs edges

  def AdjChain (edges : List (alloc.vec.Vec Std.I64)) : List ℤ → Prop
    | [] => True
    | [_] => True
    | a :: b :: rest => Adj edges a b ∧ AdjChain edges (b :: rest)

  def IsWalk (edges : List (alloc.vec.Vec Std.I64)) (p : List ℤ) : Prop :=
    p ≠ [] ∧ AdjChain edges p

  def IsPath (edges : List (alloc.vec.Vec Std.I64)) (u v : ℤ) (p : List ℤ) : Prop :=
    IsWalk edges p ∧ p.head? = some u ∧ p.getLast? = some v

  noncomputable def dist (edges : List (alloc.vec.Vec Std.I64)) (u v : ℤ) : ℕ :=
    sInf {k : ℕ | ∃ p : List ℤ, IsPath edges u v p ∧ p.length = k + 1}

  def Connected (n : ℤ) (edges : List (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ u v : ℤ, 0 ≤ u → u < n → 0 ≤ v → v < n → ∃ p : List ℤ, IsPath edges u v p

  def IsSimpleCycle (edges : List (alloc.vec.Vec Std.I64)) (v : List ℤ) : Prop :=
    ∃ a : ℤ, ∃ rest : List ℤ,
      v = a :: rest ∧ 3 ≤ v.length ∧ v.Nodup ∧ AdjChain edges (v ++ [a])

  def IsCycleVertexSet (n : ℤ) (edges : List (alloc.vec.Vec Std.I64)) (C : Finset ℤ) : Prop :=
    ∃ v : List ℤ, IsSimpleCycle edges v ∧ C = v.toFinset ∧ ∀ x ∈ C, 0 ≤ x ∧ x < n

  noncomputable def minDistToCycle (edges : List (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
      (i : ℤ) : ℕ :=
    sInf {k : ℕ | ∃ c ∈ C, dist edges i c = k}

  def neighborList (edges : List (alloc.vec.Vec Std.I64)) (i : ℤ) : List ℤ :=
    (edgePairs edges).filterMap fun p =>
      if p.1 = i then some p.2 else if p.2 = i then some p.1 else none

  def listMin (l : List ℤ) : ℤ :=
    match l with
    | [] => 0
    | x :: xs => xs.foldl (fun a b => min a b) x

  def minNeighborValue (edges : List (alloc.vec.Vec Std.I64))
      (r : alloc.vec.Vec Std.I64) (i : ℤ) : ℤ :=
    listMin ((neighborList edges i).map fun j => vecGet r j)

  def SwappedEdges (edges edges' : List (alloc.vec.Vec Std.I64)) : Prop :=
    List.Forall₂ (fun e e' => e'.val = e.val.reverse) edges edges'

  /-- Whenever distance_to_cycle(n, edges) returns a result r, r has length n, and for every i with 0 <= i < n, r[i] = min{ d(i,c) : c in C }.
    Preconditions: Assume the graph conditions of the problem: n is an integer with 3 <= n <= 100000; edges is a list of n pairs of distinct integers in [0, n-1] with no repeated unordered pair; the undirected graph G with vertex set V = {0,1,...,n-1} and edge set E = { {u,v} : [u,v] or [v,u] occurs in edges } is connected and has exactly one simple cycle. Let C be the unique set of vertices on that cycle (|C| >= 3). For a,b in V, let d(a,b) be the shortest-path distance in G. -/
  theorem spec_1
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
      (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
      (hgraph : IsGraphInput n.val edges.val)
      (hconn : Connected n.val edges.val)
      (hcyc : IsCycleVertexSet n.val edges.val C)
      (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
      (hcard : 3 ≤ C.card) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
          r.val.length = n.val.toNat ∧
            ∀ i : ℤ, 0 ≤ i → i < n.val → vecGet r i = (minDistToCycle edges.val C i : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
        (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
        (hgraph : IsGraphInput n.val edges.val)
        (hconn : Connected n.val edges.val)
        (hcyc : IsCycleVertexSet n.val edges.val C)
        (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
        (hcard : 3 ≤ C.card), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
            r.val.length = n.val.toNat ∧
              ∀ i : ℤ, 0 ≤ i → i < n.val → vecGet r i = (minDistToCycle edges.val C i : ℤ)) := by
    sorry

  /-- distance_to_cycle(n, edges) returns a result r (i.e., it does not fail, overflow, or panic).
    Preconditions: Assume the graph conditions of the problem: n is an integer with 3 <= n <= 100000; edges is a list of n pairs of distinct integers in [0, n-1] with no repeated unordered pair; the undirected graph G with vertex set V = {0,1,...,n-1} and edge set E = { {u,v} : [u,v] or [v,u] occurs in edges } is connected and has exactly one simple cycle. Let C be the unique set of vertices on that cycle (|C| >= 3). For a,b in V, let d(a,b) be the shortest-path distance in G. -/
  theorem spec_2
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
      (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
      (hgraph : IsGraphInput n.val edges.val)
      (hconn : Connected n.val edges.val)
      (hcyc : IsCycleVertexSet n.val edges.val C)
      (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
      (hcard : 3 ≤ C.card) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.DistanceToCycle.distance_to_cycle n edges = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
        (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
        (hgraph : IsGraphInput n.val edges.val)
        (hconn : Connected n.val edges.val)
        (hcyc : IsCycleVertexSet n.val edges.val C)
        (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
        (hcard : 3 ≤ C.card), ∃ r : alloc.vec.Vec Std.I64, Aegis.DistanceToCycle.distance_to_cycle n edges = ok r) := by
    sorry

  /-- Whenever distance_to_cycle(n, edges) returns a result r, len(r) = n.
    Preconditions: Assume the graph conditions of the problem: n is an integer with 3 <= n <= 100000; edges is a list of n pairs of distinct integers in [0, n-1] with no repeated unordered pair; the undirected graph G with vertex set V = {0,1,...,n-1} and edge set E = { {u,v} : [u,v] or [v,u] occurs in edges } is connected and has exactly one simple cycle. Let C be the unique set of vertices on that cycle (|C| >= 3). For a,b in V, let d(a,b) be the shortest-path distance in G. -/
  theorem spec_3
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
      (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
      (hgraph : IsGraphInput n.val edges.val)
      (hconn : Connected n.val edges.val)
      (hcyc : IsCycleVertexSet n.val edges.val C)
      (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
      (hcard : 3 ≤ C.card) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.DistanceToCycle.distance_to_cycle n edges = ok r → r.val.length = n.val.toNat := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
        (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
        (hgraph : IsGraphInput n.val edges.val)
        (hconn : Connected n.val edges.val)
        (hcyc : IsCycleVertexSet n.val edges.val C)
        (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
        (hcard : 3 ≤ C.card), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.DistanceToCycle.distance_to_cycle n edges = ok r → r.val.length = n.val.toNat) := by
    sorry

  /-- Whenever distance_to_cycle(n, edges) returns a result r, for every i with 0 <= i < n, r[i] >= 0.
    Preconditions: Assume the graph conditions of the problem: n is an integer with 3 <= n <= 100000; edges is a list of n pairs of distinct integers in [0, n-1] with no repeated unordered pair; the undirected graph G with vertex set V = {0,1,...,n-1} and edge set E = { {u,v} : [u,v] or [v,u] occurs in edges } is connected and has exactly one simple cycle. Let C be the unique set of vertices on that cycle (|C| >= 3). For a,b in V, let d(a,b) be the shortest-path distance in G. -/
  theorem spec_4
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
      (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
      (hgraph : IsGraphInput n.val edges.val)
      (hconn : Connected n.val edges.val)
      (hcyc : IsCycleVertexSet n.val edges.val C)
      (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
      (hcard : 3 ≤ C.card) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
          ∀ i : ℤ, 0 ≤ i → i < n.val → 0 ≤ vecGet r i := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
        (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
        (hgraph : IsGraphInput n.val edges.val)
        (hconn : Connected n.val edges.val)
        (hcyc : IsCycleVertexSet n.val edges.val C)
        (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
        (hcard : 3 ≤ C.card), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
            ∀ i : ℤ, 0 ≤ i → i < n.val → 0 ≤ vecGet r i) := by
    sorry

  /-- Whenever distance_to_cycle(n, edges) returns a result r, for every i with 0 <= i < n, r[i] <= n - |C|.
    Preconditions: Assume the graph conditions of the problem: n is an integer with 3 <= n <= 100000; edges is a list of n pairs of distinct integers in [0, n-1] with no repeated unordered pair; the undirected graph G with vertex set V = {0,1,...,n-1} and edge set E = { {u,v} : [u,v] or [v,u] occurs in edges } is connected and has exactly one simple cycle. Let C be the unique set of vertices on that cycle (|C| >= 3). For a,b in V, let d(a,b) be the shortest-path distance in G. -/
  theorem spec_5
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
      (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
      (hgraph : IsGraphInput n.val edges.val)
      (hconn : Connected n.val edges.val)
      (hcyc : IsCycleVertexSet n.val edges.val C)
      (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
      (hcard : 3 ≤ C.card) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
          ∀ i : ℤ, 0 ≤ i → i < n.val → vecGet r i ≤ n.val - (C.card : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
        (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
        (hgraph : IsGraphInput n.val edges.val)
        (hconn : Connected n.val edges.val)
        (hcyc : IsCycleVertexSet n.val edges.val C)
        (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
        (hcard : 3 ≤ C.card), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
            ∀ i : ℤ, 0 ≤ i → i < n.val → vecGet r i ≤ n.val - (C.card : ℤ)) := by
    sorry

  /-- Whenever distance_to_cycle(n, edges) returns a result r, for every i with 0 <= i < n, r[i] = 0 if and only if i is in C.
    Preconditions: Assume the graph conditions of the problem: n is an integer with 3 <= n <= 100000; edges is a list of n pairs of distinct integers in [0, n-1] with no repeated unordered pair; the undirected graph G with vertex set V = {0,1,...,n-1} and edge set E = { {u,v} : [u,v] or [v,u] occurs in edges } is connected and has exactly one simple cycle. Let C be the unique set of vertices on that cycle (|C| >= 3). For a,b in V, let d(a,b) be the shortest-path distance in G. -/
  theorem spec_6
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
      (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
      (hgraph : IsGraphInput n.val edges.val)
      (hconn : Connected n.val edges.val)
      (hcyc : IsCycleVertexSet n.val edges.val C)
      (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
      (hcard : 3 ≤ C.card) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
          ∀ i : ℤ, 0 ≤ i → i < n.val → (vecGet r i = 0 ↔ i ∈ C) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
        (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
        (hgraph : IsGraphInput n.val edges.val)
        (hconn : Connected n.val edges.val)
        (hcyc : IsCycleVertexSet n.val edges.val C)
        (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
        (hcard : 3 ≤ C.card), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
            ∀ i : ℤ, 0 ≤ i → i < n.val → (vecGet r i = 0 ↔ i ∈ C)) := by
    sorry

  /-- Whenever distance_to_cycle(n, edges) returns a result r, for every edge {u,v} in E, |r[u] - r[v]| <= 1.
    Preconditions: Assume the graph conditions of the problem: n is an integer with 3 <= n <= 100000; edges is a list of n pairs of distinct integers in [0, n-1] with no repeated unordered pair; the undirected graph G with vertex set V = {0,1,...,n-1} and edge set E = { {u,v} : [u,v] or [v,u] occurs in edges } is connected and has exactly one simple cycle. Let C be the unique set of vertices on that cycle (|C| >= 3). For a,b in V, let d(a,b) be the shortest-path distance in G. -/
  theorem spec_7
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
      (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
      (hgraph : IsGraphInput n.val edges.val)
      (hconn : Connected n.val edges.val)
      (hcyc : IsCycleVertexSet n.val edges.val C)
      (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
      (hcard : 3 ≤ C.card) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
          ∀ ⦃u v : ℤ⦄, Adj edges.val u v → |vecGet r u - vecGet r v| ≤ 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
        (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
        (hgraph : IsGraphInput n.val edges.val)
        (hconn : Connected n.val edges.val)
        (hcyc : IsCycleVertexSet n.val edges.val C)
        (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
        (hcard : 3 ≤ C.card), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
            ∀ ⦃u v : ℤ⦄, Adj edges.val u v → |vecGet r u - vecGet r v| ≤ 1) := by
    sorry

  /-- Whenever distance_to_cycle(n, edges) returns a result r, for every i with 0 <= i < n such that i is not in C, r[i] = 1 + min{ r[j] : j in V and {i,j} in E }.
    Preconditions: Assume the graph conditions of the problem: n is an integer with 3 <= n <= 100000; edges is a list of n pairs of distinct integers in [0, n-1] with no repeated unordered pair; the undirected graph G with vertex set V = {0,1,...,n-1} and edge set E = { {u,v} : [u,v] or [v,u] occurs in edges } is connected and has exactly one simple cycle. Let C be the unique set of vertices on that cycle (|C| >= 3). For a,b in V, let d(a,b) be the shortest-path distance in G. -/
  theorem spec_8
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
      (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
      (hgraph : IsGraphInput n.val edges.val)
      (hconn : Connected n.val edges.val)
      (hcyc : IsCycleVertexSet n.val edges.val C)
      (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
      (hcard : 3 ≤ C.card) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
          ∀ i : ℤ, 0 ≤ i → i < n.val → i ∉ C →
            vecGet r i = 1 + minNeighborValue edges.val r i := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
        (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
        (hgraph : IsGraphInput n.val edges.val)
        (hconn : Connected n.val edges.val)
        (hcyc : IsCycleVertexSet n.val edges.val C)
        (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
        (hcard : 3 ≤ C.card), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
            ∀ i : ℤ, 0 ≤ i → i < n.val → i ∉ C →
              vecGet r i = 1 + minNeighborValue edges.val r i) := by
    sorry

  /-- Whenever distance_to_cycle(n, edges) returns a result r, for every i with 0 <= i < n and every c in C, d(i,c) >= r[i].
    Preconditions: Assume the graph conditions of the problem: n is an integer with 3 <= n <= 100000; edges is a list of n pairs of distinct integers in [0, n-1] with no repeated unordered pair; the undirected graph G with vertex set V = {0,1,...,n-1} and edge set E = { {u,v} : [u,v] or [v,u] occurs in edges } is connected and has exactly one simple cycle. Let C be the unique set of vertices on that cycle (|C| >= 3). For a,b in V, let d(a,b) be the shortest-path distance in G. -/
  theorem spec_9
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
      (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
      (hgraph : IsGraphInput n.val edges.val)
      (hconn : Connected n.val edges.val)
      (hcyc : IsCycleVertexSet n.val edges.val C)
      (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
      (hcard : 3 ≤ C.card) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
          ∀ i : ℤ, 0 ≤ i → i < n.val → ∀ c ∈ C, vecGet r i ≤ (dist edges.val i c : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
        (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
        (hgraph : IsGraphInput n.val edges.val)
        (hconn : Connected n.val edges.val)
        (hcyc : IsCycleVertexSet n.val edges.val C)
        (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
        (hcard : 3 ≤ C.card), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
            ∀ i : ℤ, 0 ≤ i → i < n.val → ∀ c ∈ C, vecGet r i ≤ (dist edges.val i c : ℤ)) := by
    sorry

  /-- Whenever distance_to_cycle(n, edges) returns a result r, for every i with 0 <= i < n, there exists c in C such that d(i,c) = r[i].
    Preconditions: Assume the graph conditions of the problem: n is an integer with 3 <= n <= 100000; edges is a list of n pairs of distinct integers in [0, n-1] with no repeated unordered pair; the undirected graph G with vertex set V = {0,1,...,n-1} and edge set E = { {u,v} : [u,v] or [v,u] occurs in edges } is connected and has exactly one simple cycle. Let C be the unique set of vertices on that cycle (|C| >= 3). For a,b in V, let d(a,b) be the shortest-path distance in G. -/
  theorem spec_10
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
      (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
      (hgraph : IsGraphInput n.val edges.val)
      (hconn : Connected n.val edges.val)
      (hcyc : IsCycleVertexSet n.val edges.val C)
      (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
      (hcard : 3 ≤ C.card) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
          ∀ i : ℤ, 0 ≤ i → i < n.val → ∃ c ∈ C, (dist edges.val i c : ℤ) = vecGet r i := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
        (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
        (hgraph : IsGraphInput n.val edges.val)
        (hconn : Connected n.val edges.val)
        (hcyc : IsCycleVertexSet n.val edges.val C)
        (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
        (hcard : 3 ≤ C.card), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
            ∀ i : ℤ, 0 ≤ i → i < n.val → ∃ c ∈ C, (dist edges.val i c : ℤ) = vecGet r i) := by
    sorry

  /-- Whenever distance_to_cycle(n, edges) returns a result r, the number of indices i with 0 <= i < n and r[i] = 0 equals |C|.
    Preconditions: Assume the graph conditions of the problem: n is an integer with 3 <= n <= 100000; edges is a list of n pairs of distinct integers in [0, n-1] with no repeated unordered pair; the undirected graph G with vertex set V = {0,1,...,n-1} and edge set E = { {u,v} : [u,v] or [v,u] occurs in edges } is connected and has exactly one simple cycle. Let C be the unique set of vertices on that cycle (|C| >= 3). For a,b in V, let d(a,b) be the shortest-path distance in G. -/
  theorem spec_11
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
      (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
      (hgraph : IsGraphInput n.val edges.val)
      (hconn : Connected n.val edges.val)
      (hcyc : IsCycleVertexSet n.val edges.val C)
      (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
      (hcard : 3 ≤ C.card) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.DistanceToCycle.distance_to_cycle n edges = ok r → (vals r).count 0 = C.card := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
        (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
        (hgraph : IsGraphInput n.val edges.val)
        (hconn : Connected n.val edges.val)
        (hcyc : IsCycleVertexSet n.val edges.val C)
        (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
        (hcard : 3 ≤ C.card), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.DistanceToCycle.distance_to_cycle n edges = ok r → (vals r).count 0 = C.card) := by
    sorry

  /-- For every i with 0 <= i < n, let edges' be the list obtained from edges by replacing each pair [a,b] with [b,a]. If r is the result of distance_to_cycle(n, edges) and r' is the result of distance_to_cycle(n, edges'), then r'[i] = r[i].
    Preconditions: Assume the graph conditions of the problem: n is an integer with 3 <= n <= 100000; edges is a list of n pairs of distinct integers in [0, n-1] with no repeated unordered pair; the undirected graph G with vertex set V = {0,1,...,n-1} and edge set E = { {u,v} : [u,v] or [v,u] occurs in edges } is connected and has exactly one simple cycle. Let C be the unique set of vertices on that cycle (|C| >= 3). For a,b in V, let d(a,b) be the shortest-path distance in G. -/
  theorem spec_12
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
      (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
      (hgraph : IsGraphInput n.val edges.val)
      (hconn : Connected n.val edges.val)
      (hcyc : IsCycleVertexSet n.val edges.val C)
      (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
      (hcard : 3 ≤ C.card)
      (edges' : Slice (alloc.vec.Vec Std.I64))
      (hswap : SwappedEdges edges.val edges'.val) :
      ∀ (r r' : alloc.vec.Vec Std.I64),
        Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
          Aegis.DistanceToCycle.distance_to_cycle n edges' = ok r' →
            ∀ i : ℤ, 0 ≤ i → i < n.val → vecGet r' i = vecGet r i := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
        (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
        (hgraph : IsGraphInput n.val edges.val)
        (hconn : Connected n.val edges.val)
        (hcyc : IsCycleVertexSet n.val edges.val C)
        (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
        (hcard : 3 ≤ C.card)
        (edges' : Slice (alloc.vec.Vec Std.I64))
        (hswap : SwappedEdges edges.val edges'.val), ∀ (r r' : alloc.vec.Vec Std.I64),
          Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
            Aegis.DistanceToCycle.distance_to_cycle n edges' = ok r' →
              ∀ i : ℤ, 0 ≤ i → i < n.val → vecGet r' i = vecGet r i) := by
    sorry

  /-- For every i with 0 <= i < n, let edges' be any permutation of the list edges. If r is the result of distance_to_cycle(n, edges) and r' is the result of distance_to_cycle(n, edges'), then r'[i] = r[i].
    Preconditions: Assume the graph conditions of the problem: n is an integer with 3 <= n <= 100000; edges is a list of n pairs of distinct integers in [0, n-1] with no repeated unordered pair; the undirected graph G with vertex set V = {0,1,...,n-1} and edge set E = { {u,v} : [u,v] or [v,u] occurs in edges } is connected and has exactly one simple cycle. Let C be the unique set of vertices on that cycle (|C| >= 3). For a,b in V, let d(a,b) be the shortest-path distance in G. -/
  theorem spec_13
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
      (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
      (hgraph : IsGraphInput n.val edges.val)
      (hconn : Connected n.val edges.val)
      (hcyc : IsCycleVertexSet n.val edges.val C)
      (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
      (hcard : 3 ≤ C.card)
      (edges' : Slice (alloc.vec.Vec Std.I64))
      (hperm : edges'.val.Perm edges.val) :
      ∀ (r r' : alloc.vec.Vec Std.I64),
        Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
          Aegis.DistanceToCycle.distance_to_cycle n edges' = ok r' →
            ∀ i : ℤ, 0 ≤ i → i < n.val → vecGet r' i = vecGet r i := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (C : Finset ℤ)
        (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
        (hgraph : IsGraphInput n.val edges.val)
        (hconn : Connected n.val edges.val)
        (hcyc : IsCycleVertexSet n.val edges.val C)
        (huniq : ∀ C' : Finset ℤ, IsCycleVertexSet n.val edges.val C' → C' = C)
        (hcard : 3 ≤ C.card)
        (edges' : Slice (alloc.vec.Vec Std.I64))
        (hperm : edges'.val.Perm edges.val), ∀ (r r' : alloc.vec.Vec Std.I64),
          Aegis.DistanceToCycle.distance_to_cycle n edges = ok r →
            Aegis.DistanceToCycle.distance_to_cycle n edges' = ok r' →
              ∀ i : ℤ, 0 ≤ i → i < n.val → vecGet r' i = vecGet r i) := by
    sorry

  end AegisSpec.DistanceToCycle
