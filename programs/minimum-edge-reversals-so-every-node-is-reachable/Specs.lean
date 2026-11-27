import Aegis.MinEdgeReversals.Code.Funs

/-!
# Specifications of `Aegis.MinEdgeReversals.min_edge_reversals`

LeetCode problem `minimum-edge-reversals-so-every-node-is-reachable`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinEdgeReversals

  def vertexCount (n : I64) : ℕ := n.val.toNat

  def edgeCount (n : I64) : ℕ := n.val.toNat - 1

  def InVertex (n : ℕ) (v : ℤ) : Prop := 0 ≤ v ∧ v < (n : ℤ)

  def e0 (e : alloc.vec.Vec Std.I64) : ℤ := (e.val.getD 0 default).val

  def e1 (e : alloc.vec.Vec Std.I64) : ℤ := (e.val.getD 1 default).val

  def edgeList (edges : Slice (alloc.vec.Vec Std.I64)) : List (ℤ × ℤ) :=
    edges.val.map fun e => (e0 e, e1 e)

  def edgeAt (edges : Slice (alloc.vec.Vec Std.I64)) (j : ℕ) : ℤ × ℤ :=
    (edgeList edges).getD j (0, 0)

  def src (edges : Slice (alloc.vec.Vec Std.I64)) (j : ℕ) : ℤ := (edgeAt edges j).1

  def dst (edges : Slice (alloc.vec.Vec Std.I64)) (j : ℕ) : ℤ := (edgeAt edges j).2

  def atIdx (r : alloc.vec.Vec Std.I64) (i : ℕ) : ℤ := (r.val.getD i default).val

  def IsEdgeSet (m : ℕ) (S : Finset ℕ) : Prop := ∀ j ∈ S, j < m

  def Reach (R : ℤ → ℤ → Prop) (u v : ℤ) : Prop := Relation.ReflTransGen R u v

  def DAdj (E : List (ℤ × ℤ)) (x y : ℤ) : Prop := (x, y) ∈ E

  def UAdj (E : List (ℤ × ℤ)) (x y : ℤ) : Prop := (x, y) ∈ E ∨ (y, x) ∈ E

  def DReachesAll (n : ℕ) (E : List (ℤ × ℤ)) (i : ℤ) : Prop :=
    ∀ v : ℤ, InVertex n v → Reach (DAdj E) i v

  def reverseAt (E : List (ℤ × ℤ)) (S : Finset ℕ) : List (ℤ × ℤ) :=
    E.zipIdx.map fun p => if p.2 ∈ S then (p.1.2, p.1.1) else p.1

  def ReachesAllAfter (n : ℕ) (E : List (ℤ × ℤ)) (S : Finset ℕ) (i : ℤ) : Prop :=
    DReachesAll n (reverseAt E S) i

  def UConnected (n : ℕ) (E : List (ℤ × ℤ)) : Prop :=
    ∀ v : ℤ, InVertex n v → Reach (UAdj E) 0 v

  def cyclicPairs (c : List ℤ) : List (ℤ × ℤ) := c.zip (c.rotate 1)

  def IsCycle (E : List (ℤ × ℤ)) (c : List ℤ) : Prop :=
    3 ≤ c.length ∧ c.Nodup ∧ ∀ p ∈ cyclicPairs c, UAdj E p.1 p.2

  def UAcyclic (E : List (ℤ × ℤ)) : Prop := ∀ c : List ℤ, ¬ IsCycle E c

  def IsTree (n : ℕ) (E : List (ℤ × ℤ)) : Prop := UConnected n E ∧ UAcyclic E

  def InSideOf (E : List (ℤ × ℤ)) (j : ℕ) (b i : ℤ) : Prop :=
    Reach (UAdj (E.eraseIdx j)) b i

  noncomputable def towardSet (E : List (ℤ × ℤ)) (i : ℤ) : Finset ℕ := by
    classical
    exact (Finset.range E.length).filter fun j => InSideOf E j ((E.getD j (0, 0)).2) i

  theorem mem_towardSet {E : List (ℤ × ℤ)} {i : ℤ} {j : ℕ} :
      j ∈ towardSet E i ↔ j < E.length ∧ InSideOf E j ((E.getD j (0, 0)).2) i := by
    classical
    simp only [towardSet, Finset.mem_filter, Finset.mem_range]

  def IsMinCard (p : Finset ℕ → Prop) (k : ℤ) : Prop :=
    (∃ S, p S ∧ (S.card : ℤ) = k) ∧ ∀ S, p S → k ≤ (S.card : ℤ)

  /-- The function returns a result r with len(r) = n, and for every i with 0 ≤ i < n: r[i] is the minimum, over all subsets S of {0,...,n-2}, of |S| such that in the directed graph obtained from the original directed edges edges[j] = (edges[j][0] → edges[j][1]) by reversing every edge whose index lies in S, node i can reach every node of {0,...,n-1} by following zero or more directed edges. This minimum is well defined because the set being minimized over is nonempty (reversing exactly the edges currently pointing toward i's side achieves reachability of all nodes from i).
    Preconditions: n ≥ 2; len(edges) = n-1; for every j with 0 ≤ j < n-1: len(edges[j]) = 2, 0 ≤ edges[j][0] < n, 0 ≤ edges[j][1] < n, edges[j][0] ≠ edges[j][1]; and the undirected graph T on {0,...,n-1} whose edges are the unordered pairs {edges[j][0], edges[j][1]} for 0 ≤ j < n-1 is a tree (connected and acyclic). -/
  theorem spec_1 (n : I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (hn : 2 ≤ n.val)
      (hlen : (edges.val.length : ℤ) = n.val - 1)
      (hshape : ∀ e ∈ edges.val, e.val.length = 2)
      (hbounds : ∀ e ∈ edges.val,
        InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
      (htree : IsTree (vertexCount n) (edgeList edges)) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.MinEdgeReversals.min_edge_reversals n edges = ok r ∧
        r.val.length = vertexCount n ∧
        ∀ i, i < vertexCount n →
          IsMinCard (fun S =>
              IsEdgeSet (edgeCount n) S ∧
                ReachesAllAfter (vertexCount n) (edgeList edges) S (atIdx r i))
            (atIdx r i) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (hn : 2 ≤ n.val)
        (hlen : (edges.val.length : ℤ) = n.val - 1)
        (hshape : ∀ e ∈ edges.val, e.val.length = 2)
        (hbounds : ∀ e ∈ edges.val,
          InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
        (htree : IsTree (vertexCount n) (edgeList edges)), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.MinEdgeReversals.min_edge_reversals n edges = ok r ∧
          r.val.length = vertexCount n ∧
          ∀ i, i < vertexCount n →
            IsMinCard (fun S =>
                IsEdgeSet (edgeCount n) S ∧
                  ReachesAllAfter (vertexCount n) (edgeList edges) S (atIdx r i))
              (atIdx r i)) := by
    sorry

  /-- For every i with 0 ≤ i < n: 0 ≤ r[i] ≤ n-1.
    Preconditions: n ≥ 2; len(edges) = n-1; for every j with 0 ≤ j < n-1: len(edges[j]) = 2, 0 ≤ edges[j][0] < n, 0 ≤ edges[j][1] < n, edges[j][0] ≠ edges[j][1]; and the undirected graph T on {0,...,n-1} with edges {edges[j][0], edges[j][1]} is a tree. -/
  theorem spec_2 (n : I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (hn : 2 ≤ n.val)
      (hlen : (edges.val.length : ℤ) = n.val - 1)
      (hshape : ∀ e ∈ edges.val, e.val.length = 2)
      (hbounds : ∀ e ∈ edges.val,
        InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
      (htree : IsTree (vertexCount n) (edgeList edges)) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.MinEdgeReversals.min_edge_reversals n edges = ok r ∧
        ∀ i, i < vertexCount n → 0 ≤ atIdx r i ∧ atIdx r i ≤ n.val - 1 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (hn : 2 ≤ n.val)
        (hlen : (edges.val.length : ℤ) = n.val - 1)
        (hshape : ∀ e ∈ edges.val, e.val.length = 2)
        (hbounds : ∀ e ∈ edges.val,
          InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
        (htree : IsTree (vertexCount n) (edgeList edges)), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.MinEdgeReversals.min_edge_reversals n edges = ok r ∧
          ∀ i, i < vertexCount n → 0 ≤ atIdx r i ∧ atIdx r i ≤ n.val - 1) := by
    sorry

  /-- For each edge index j with 0 ≤ j < n-1 let a = edges[j][0] and b = edges[j][1]; deleting edge j from the tree T splits {0,...,n-1} into two components, and let side_j(b) denote the component that contains b. Then for every i with 0 ≤ i < n: r[i] = |{ j : 0 ≤ j < n-1 and i ∈ side_j(b) }|, i.e. r[i] equals the number of input edges whose direction points toward the side of i (the number of edges a→b for which i lies on b's side after the edge is removed).
    Preconditions: n ≥ 2; len(edges) = n-1; for every j with 0 ≤ j < n-1: len(edges[j]) = 2, 0 ≤ edges[j][0] < n, 0 ≤ edges[j][1] < n, edges[j][0] ≠ edges[j][1]; and the undirected graph T on {0,...,n-1} with edges {edges[j][0], edges[j][1]} is a tree. -/
  theorem spec_3 (n : I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (hn : 2 ≤ n.val)
      (hlen : (edges.val.length : ℤ) = n.val - 1)
      (hshape : ∀ e ∈ edges.val, e.val.length = 2)
      (hbounds : ∀ e ∈ edges.val,
        InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
      (htree : IsTree (vertexCount n) (edgeList edges)) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.MinEdgeReversals.min_edge_reversals n edges = ok r ∧
        ∀ i, i < vertexCount n →
          atIdx r i = ((towardSet (edgeList edges) i).card : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (hn : 2 ≤ n.val)
        (hlen : (edges.val.length : ℤ) = n.val - 1)
        (hshape : ∀ e ∈ edges.val, e.val.length = 2)
        (hbounds : ∀ e ∈ edges.val,
          InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
        (htree : IsTree (vertexCount n) (edgeList edges)), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.MinEdgeReversals.min_edge_reversals n edges = ok r ∧
          ∀ i, i < vertexCount n →
            atIdx r i = ((towardSet (edgeList edges) i).card : ℤ)) := by
    sorry

  /-- For every edge index j with 0 ≤ j < n-1, letting u = edges[j][0] and v = edges[j][1]: r[v] = r[u] + 1.
    Preconditions: n ≥ 2; len(edges) = n-1; for every j with 0 ≤ j < n-1: len(edges[j]) = 2, 0 ≤ edges[j][0] < n, 0 ≤ edges[j][1] < n, edges[j][0] ≠ edges[j][1]; and the undirected graph T on {0,...,n-1} with edges {edges[j][0], edges[j][1]} is a tree. -/
  theorem spec_4 (n : I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (hn : 2 ≤ n.val)
      (hlen : (edges.val.length : ℤ) = n.val - 1)
      (hshape : ∀ e ∈ edges.val, e.val.length = 2)
      (hbounds : ∀ e ∈ edges.val,
        InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
      (htree : IsTree (vertexCount n) (edgeList edges)) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.MinEdgeReversals.min_edge_reversals n edges = ok r ∧
        ∀ j, j < edgeCount n →
          atIdx r (dst edges j).toNat = atIdx r (src edges j).toNat + 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (hn : 2 ≤ n.val)
        (hlen : (edges.val.length : ℤ) = n.val - 1)
        (hshape : ∀ e ∈ edges.val, e.val.length = 2)
        (hbounds : ∀ e ∈ edges.val,
          InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
        (htree : IsTree (vertexCount n) (edgeList edges)), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.MinEdgeReversals.min_edge_reversals n edges = ok r ∧
          ∀ j, j < edgeCount n →
            atIdx r (dst edges j).toNat = atIdx r (src edges j).toNat + 1) := by
    sorry

  /-- For every i with 0 ≤ i < n: r[i] = 0 if and only if, using only the original directed edges edges[j] = (edges[j][0] → edges[j][1]) with no reversals at all, node i can reach every node of {0,...,n-1}.
    Preconditions: n ≥ 2; len(edges) = n-1; for every j with 0 ≤ j < n-1: len(edges[j]) = 2, 0 ≤ edges[j][0] < n, 0 ≤ edges[j][1] < n, edges[j][0] ≠ edges[j][1]; and the undirected graph T on {0,...,n-1} with edges {edges[j][0], edges[j][1]} is a tree. -/
  theorem spec_5 (n : I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (hn : 2 ≤ n.val)
      (hlen : (edges.val.length : ℤ) = n.val - 1)
      (hshape : ∀ e ∈ edges.val, e.val.length = 2)
      (hbounds : ∀ e ∈ edges.val,
        InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
      (htree : IsTree (vertexCount n) (edgeList edges)) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.MinEdgeReversals.min_edge_reversals n edges = ok r ∧
        ∀ i, i < vertexCount n →
          (atIdx r i = 0 ↔ DReachesAll (vertexCount n) (edgeList edges) i) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (hn : 2 ≤ n.val)
        (hlen : (edges.val.length : ℤ) = n.val - 1)
        (hshape : ∀ e ∈ edges.val, e.val.length = 2)
        (hbounds : ∀ e ∈ edges.val,
          InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
        (htree : IsTree (vertexCount n) (edgeList edges)), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.MinEdgeReversals.min_edge_reversals n edges = ok r ∧
          ∀ i, i < vertexCount n →
            (atIdx r i = 0 ↔ DReachesAll (vertexCount n) (edgeList edges) i)) := by
    sorry

  /-- For every i with 0 ≤ i < n and every subset S of {0,...,n-2} with |S| < r[i]: in the directed graph obtained by reversing exactly the edges whose indices lie in S, node i cannot reach every node of {0,...,n-1}; that is, at least one node is unreachable from i.
    Preconditions: n ≥ 2; len(edges) = n-1; for every j with 0 ≤ j < n-1: len(edges[j]) = 2, 0 ≤ edges[j][0] < n, 0 ≤ edges[j][1] < n, edges[j][0] ≠ edges[j][1]; and the undirected graph T on {0,...,n-1} with edges {edges[j][0], edges[j][1]} is a tree. -/
  theorem spec_6 (n : I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (hn : 2 ≤ n.val)
      (hlen : (edges.val.length : ℤ) = n.val - 1)
      (hshape : ∀ e ∈ edges.val, e.val.length = 2)
      (hbounds : ∀ e ∈ edges.val,
        InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
      (htree : IsTree (vertexCount n) (edgeList edges)) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.MinEdgeReversals.min_edge_reversals n edges = ok r ∧
        ∀ i, i < vertexCount n →
          ∀ S, IsEdgeSet (edgeCount n) S → (S.card : ℤ) < atIdx r i →
            ¬ ReachesAllAfter (vertexCount n) (edgeList edges) S i := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (hn : 2 ≤ n.val)
        (hlen : (edges.val.length : ℤ) = n.val - 1)
        (hshape : ∀ e ∈ edges.val, e.val.length = 2)
        (hbounds : ∀ e ∈ edges.val,
          InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
        (htree : IsTree (vertexCount n) (edgeList edges)), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.MinEdgeReversals.min_edge_reversals n edges = ok r ∧
          ∀ i, i < vertexCount n →
            ∀ S, IsEdgeSet (edgeCount n) S → (S.card : ℤ) < atIdx r i →
              ¬ ReachesAllAfter (vertexCount n) (edgeList edges) S i) := by
    sorry

  /-- For every i with 0 ≤ i < n define T_i = { j : 0 ≤ j < n-1 and i lies in the component containing edges[j][1] when edge j is deleted from T } (the input edges currently pointing toward i's side). Then |T_i| = r[i], and after reversing exactly the edges whose indices lie in T_i, node i can reach every node of {0,...,n-1} via directed edges.
    Preconditions: n ≥ 2; len(edges) = n-1; for every j with 0 ≤ j < n-1: len(edges[j]) = 2, 0 ≤ edges[j][0] < n, 0 ≤ edges[j][1] < n, edges[j][0] ≠ edges[j][1]; and the undirected graph T on {0,...,n-1} with edges {edges[j][0], edges[j][1]} is a tree. -/
  theorem spec_7 (n : I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (hn : 2 ≤ n.val)
      (hlen : (edges.val.length : ℤ) = n.val - 1)
      (hshape : ∀ e ∈ edges.val, e.val.length = 2)
      (hbounds : ∀ e ∈ edges.val,
        InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
      (htree : IsTree (vertexCount n) (edgeList edges)) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.MinEdgeReversals.min_edge_reversals n edges = ok r ∧
        ∀ i, i < vertexCount n →
          ((towardSet (edgeList edges) i).card : ℤ) = atIdx r i ∧
            ReachesAllAfter (vertexCount n) (edgeList edges) (towardSet (edgeList edges) i) i := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (hn : 2 ≤ n.val)
        (hlen : (edges.val.length : ℤ) = n.val - 1)
        (hshape : ∀ e ∈ edges.val, e.val.length = 2)
        (hbounds : ∀ e ∈ edges.val,
          InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
        (htree : IsTree (vertexCount n) (edgeList edges)), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.MinEdgeReversals.min_edge_reversals n edges = ok r ∧
          ∀ i, i < vertexCount n →
            ((towardSet (edgeList edges) i).card : ℤ) = atIdx r i ∧
              ReachesAllAfter (vertexCount n) (edgeList edges) (towardSet (edgeList edges) i) i) := by
    sorry

  /-- For every input satisfying the preconditions the function returns a result r (it never fails: no arithmetic overflow, no out-of-bounds access, no panic), and len(r) = n.
    Preconditions: n ≥ 2; len(edges) = n-1; for every j with 0 ≤ j < n-1: len(edges[j]) = 2, 0 ≤ edges[j][0] < n, 0 ≤ edges[j][1] < n, edges[j][0] ≠ edges[j][1]; and the undirected graph T on {0,...,n-1} with edges {edges[j][0], edges[j][1]} is a tree. -/
  theorem spec_8 (n : I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (hn : 2 ≤ n.val)
      (hlen : (edges.val.length : ℤ) = n.val - 1)
      (hshape : ∀ e ∈ edges.val, e.val.length = 2)
      (hbounds : ∀ e ∈ edges.val,
        InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
      (htree : IsTree (vertexCount n) (edgeList edges)) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.MinEdgeReversals.min_edge_reversals n edges = ok r ∧
        r.val.length = vertexCount n := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (hn : 2 ≤ n.val)
        (hlen : (edges.val.length : ℤ) = n.val - 1)
        (hshape : ∀ e ∈ edges.val, e.val.length = 2)
        (hbounds : ∀ e ∈ edges.val,
          InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
        (htree : IsTree (vertexCount n) (edgeList edges)), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.MinEdgeReversals.min_edge_reversals n edges = ok r ∧
          r.val.length = vertexCount n) := by
    sorry

  /-- The returned answer vector is invariant under reordering of the input edges: the vector r produced for (n, edges) equals, componentwise, the vector produced for (n, edges').
    Preconditions: n ≥ 2; len(edges) = n-1; both (n, edges) and (n, edges') satisfy: for every j with 0 ≤ j < n-1, len(edges[j]) = 2, 0 ≤ edges[j][0] < n, 0 ≤ edges[j][1] < n, edges[j][0] ≠ edges[j][1], the undirected graph with these edges is a tree, and edges' is a permutation of edges (there is a permutation π of {0,...,n-2} with edges'[k] = edges[π(k)] for all k). -/
  theorem spec_9 (n : I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
      (hn : 2 ≤ n.val)
      (hlen : (edges.val.length : ℤ) = n.val - 1)
      (hshape : ∀ e ∈ edges.val, e.val.length = 2)
      (hbounds : ∀ e ∈ edges.val,
        InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
      (htree : IsTree (vertexCount n) (edgeList edges))
      (hlen' : (edges'.val.length : ℤ) = n.val - 1)
      (hshape' : ∀ e ∈ edges'.val, e.val.length = 2)
      (hbounds' : ∀ e ∈ edges'.val,
        InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
      (htree' : IsTree (vertexCount n) (edgeList edges'))
      (hperm : ∃ π : Equiv.Perm (Fin (edgeCount n)),
        ∀ k (hk : k < edgeCount n),
          edges'.val.getD k default = edges.val.getD (π ⟨k, hk⟩).val default) :
      ∃ r r' : alloc.vec.Vec Std.I64,
        Aegis.MinEdgeReversals.min_edge_reversals n edges = ok r ∧
        Aegis.MinEdgeReversals.min_edge_reversals n edges' = ok r' ∧
        ∀ i, i < vertexCount n → atIdx r i = atIdx r' i := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
        (hn : 2 ≤ n.val)
        (hlen : (edges.val.length : ℤ) = n.val - 1)
        (hshape : ∀ e ∈ edges.val, e.val.length = 2)
        (hbounds : ∀ e ∈ edges.val,
          InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
        (htree : IsTree (vertexCount n) (edgeList edges))
        (hlen' : (edges'.val.length : ℤ) = n.val - 1)
        (hshape' : ∀ e ∈ edges'.val, e.val.length = 2)
        (hbounds' : ∀ e ∈ edges'.val,
          InVertex (vertexCount n) (e0 e) ∧ InVertex (vertexCount n) (e1 e) ∧ e0 e ≠ e1 e)
        (htree' : IsTree (vertexCount n) (edgeList edges'))
        (hperm : ∃ π : Equiv.Perm (Fin (edgeCount n)),
          ∀ k (hk : k < edgeCount n),
            edges'.val.getD k default = edges.val.getD (π ⟨k, hk⟩).val default), ∃ r r' : alloc.vec.Vec Std.I64,
          Aegis.MinEdgeReversals.min_edge_reversals n edges = ok r ∧
          Aegis.MinEdgeReversals.min_edge_reversals n edges' = ok r' ∧
          ∀ i, i < vertexCount n → atIdx r i = atIdx r' i) := by
    sorry

  end AegisSpec.MinEdgeReversals
