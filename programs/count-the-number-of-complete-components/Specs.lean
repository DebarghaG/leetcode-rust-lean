import Aegis.CountCompleteComponents.Code.Funs

/-!
# Specifications of `Aegis.CountCompleteComponents.count_complete_components`

LeetCode problem `count-the-number-of-complete-components`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

  namespace AegisSpec.CountCompleteComponents

  noncomputable def vertexSet (n : ℤ) : Finset ℤ :=
    (Finset.range (Int.toNat n)).image (fun k : ℕ => (k : ℤ))

  def HasEndpoints (e : alloc.vec.Vec I64) (i j : ℤ) : Prop :=
    ∃ a b : I64, e.val = [a, b] ∧ a.val = i ∧ b.val = j

  def SameUnorderedEdge (e₁ e₂ : alloc.vec.Vec I64) : Prop :=
    ∃ i j : ℤ, HasEndpoints e₁ i j ∧ (HasEndpoints e₂ i j ∨ HasEndpoints e₂ j i)

  def adj (edges : Slice (alloc.vec.Vec I64)) (i j : ℤ) : Prop :=
    ∃ e ∈ edges.val, HasEndpoints e i j ∨ HasEndpoints e j i

  inductive Path (edges : Slice (alloc.vec.Vec I64)) : ℤ → ℤ → Prop where
    | nil (u : ℤ) : Path edges u u
    | step {u v w : ℤ} : Path edges u v → adj edges v w → Path edges u w

  def connComp (edges : Slice (alloc.vec.Vec I64)) (u : ℤ) : Set ℤ :=
    {v | Path edges u v}

  def IsComplete (edges : Slice (alloc.vec.Vec I64)) (S : Set ℤ) : Prop :=
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → adj edges x y

  noncomputable def componentCount (n : ℤ) (edges : Slice (alloc.vec.Vec I64)) : ℕ :=
    ((vertexSet n).image (fun u => connComp edges u)).card

  noncomputable def completeComponentCount (n : ℤ) (edges : Slice (alloc.vec.Vec I64)) : ℕ :=
    by
      classical
      exact (((vertexSet n).image (fun u => connComp edges u)).filter
        (fun S => IsComplete edges S)).card

  noncomputable def isolatedVertices (n : ℤ) (edges : Slice (alloc.vec.Vec I64)) : Finset ℤ :=
    by
      classical
      exact (vertexSet n).filter (fun v => ∀ u ∈ vertexSet n, u ≠ v → ¬ adj edges v u)

  def IsIncident (e : alloc.vec.Vec I64) (v : ℤ) : Prop :=
    ∃ a b : I64, e.val = [a, b] ∧ (a.val = v ∨ b.val = v)

  structure GraphInput (n : I64) (edges : Slice (alloc.vec.Vec I64)) : Prop where

    n_lower : 1 ≤ n.val

    n_upper : n.val ≤ 50

    edge_len : ∀ e ∈ edges.val, e.val.length = 2

    edge_endpoints : ∀ e ∈ edges.val, ∃ a b : I64,
      e.val = [a, b] ∧ 0 ≤ a.val ∧ a.val < n.val ∧ 0 ≤ b.val ∧ b.val < n.val ∧ a.val ≠ b.val

    edge_no_dup : ∀ e₁ ∈ edges.val, ∀ e₂ ∈ edges.val, e₁ ≠ e₂ → ¬ SameUnorderedEdge e₁ e₂

    edge_count_le : (edges.val.length : ℤ) ≤ n.val * (n.val - 1) / 2

  /-- Define adj(i,j) for i,j in {0,...,n-1} to mean that there exists an index k with 0 <= k < len(edges) such that (edges[k][0] = i and edges[k][1] = j) or (edges[k][0] = j and edges[k][1] = i). Define a path from u to v as a sequence of vertices v0, v1, ..., vm (m >= 0) with v0 = u, vm = v, and for each t with 0 <= t < m, adj(v_t, v_{t+1}). Define u and v to be connected if there exists a path from u to v. For u in {0,...,n-1}, let C(u) = { v in {0,...,n-1} : v is connected to u }. A set C(u) is complete if for every pair of distinct vertices x, y in C(u), adj(x,y) holds. The function returns a result r and r is the number of distinct sets among { C(u) : 0 <= u < n } that are complete. Equivalently, r = |{ C(u) : 0 <= u < n and C(u) is complete }|.
    Preconditions: n is an integer with 1 <= n <= 50. edges is a list (slice) of vectors, each of length exactly 2. For each k with 0 <= k < len(edges), edges[k][0] and edges[k][1] are integers in {0,1,...,n-1} and edges[k][0] != edges[k][1]. No unordered pair of vertices appears more than once in edges (i.e., for k != l, the set {edges[k][0], edges[k][1]} is not equal to {edges[l][0], edges[l][1]}). Also len(edges) <= n*(n-1)/2. -/
  theorem spec_1 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : GraphInput n edges) :
      ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
        r.val = (completeComponentCount n.val edges : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : GraphInput n edges), ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
          r.val = (completeComponentCount n.val edges : ℤ)) := by
    sorry

  /-- The function returns a result r and 0 <= r <= n.
    Preconditions: n is an integer with 1 <= n <= 50. edges is a list (slice) of vectors, each of length exactly 2. For each k with 0 <= k < len(edges), edges[k][0] and edges[k][1] are integers in {0,1,...,n-1} and edges[k][0] != edges[k][1]. No unordered pair of vertices appears more than once in edges (i.e., for k != l, the set {edges[k][0], edges[k][1]} is not equal to {edges[l][0], edges[l][1]}). Also len(edges) <= n*(n-1)/2. -/
  theorem spec_2 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : GraphInput n edges) :
      ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
        0 ≤ r.val ∧ r.val ≤ n.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : GraphInput n edges), ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
          0 ≤ r.val ∧ r.val ≤ n.val) := by
    sorry

  /-- The function returns a result r. Let c be the number of connected components of the graph, i.e., c = |{ C(u) : 0 <= u < n }|, where C(u) is defined as in spec_1. Then r <= c.
    Preconditions: n and edges satisfy the constraints: 1 <= n <= 50, edges is a list of pairs of distinct vertices in {0,...,n-1} with no repeated unordered pair, len(edges) <= n*(n-1)/2, and each edge vector has length 2. -/
  theorem spec_3 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : GraphInput n edges) :
      ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
        r.val ≤ (componentCount n.val edges : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : GraphInput n edges), ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
          r.val ≤ (componentCount n.val edges : ℤ)) := by
    sorry

  /-- The function returns a result r. Let I = { v in {0,...,n-1} : for all u in {0,...,n-1}, u != v implies not adj(v,u) }, where adj is defined as in spec_1. (These are the vertices incident to no edge.) Then r >= |I|.
    Preconditions: n and edges satisfy the constraints: 1 <= n <= 50, edges is a list of pairs of distinct vertices in {0,...,n-1} with no repeated unordered pair, len(edges) <= n*(n-1)/2, and each edge vector has length 2. -/
  theorem spec_4 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : GraphInput n edges) :
      ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
        ((isolatedVertices n.val edges).card : ℤ) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : GraphInput n edges), ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
          ((isolatedVertices n.val edges).card : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns a result r. Then r = 0 if and only if every connected component of the graph is not complete, i.e., for every u in {0,...,n-1}, the set C(u) (as defined in spec_1) is not complete.
    Preconditions: n and edges satisfy the constraints: 1 <= n <= 50, edges is a list of pairs of distinct vertices in {0,...,n-1} with no repeated unordered pair, len(edges) <= n*(n-1)/2, and each edge vector has length 2. -/
  theorem spec_5 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : GraphInput n edges) :
      ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
        (r.val = 0 ↔ ∀ u ∈ vertexSet n.val, ¬ IsComplete edges (connComp edges u)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : GraphInput n edges), ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
          (r.val = 0 ↔ ∀ u ∈ vertexSet n.val, ¬ IsComplete edges (connComp edges u))) := by
    sorry

  /-- Let r be the result of count_complete_components(n, edges) and r' be the result of count_complete_components(n, edges'). Then r = r'.
    Preconditions: n and edges satisfy the constraints: 1 <= n <= 50, edges is a list of pairs of distinct vertices in {0,...,n-1} with no repeated unordered pair, len(edges) <= n*(n-1)/2, and each edge vector has length 2. Let edges' be any permutation of the list edges (same elements, possibly different order). Then n and edges' also satisfy the constraints. -/
  theorem spec_6 (n : I64) (edges edges' : Slice (alloc.vec.Vec I64))
      (h : GraphInput n edges) (hperm : edges.val.Perm edges'.val) :
      GraphInput n edges' ∧ ∃ r r' : I64,
        Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
        Aegis.CountCompleteComponents.count_complete_components n edges' = ok r' ∧ r = r' := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : I64) (edges edges' : Slice (alloc.vec.Vec I64))
        (h : GraphInput n edges) (hperm : edges.val.Perm edges'.val), GraphInput n edges' ∧ ∃ r r' : I64,
          Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
          Aegis.CountCompleteComponents.count_complete_components n edges' = ok r' ∧ r = r') := by
    sorry

  /-- For every n and edges satisfying the preconditions, the function returns a result r (i.e., it does not panic, overflow, or return an error).
    Preconditions: n and edges satisfy the constraints: 1 <= n <= 50, edges is a list of pairs of distinct vertices in {0,...,n-1} with no repeated unordered pair, len(edges) <= n*(n-1)/2, and each edge vector has length 2. -/
  theorem spec_7 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : GraphInput n edges) :
      ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : GraphInput n edges), ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r) := by
    sorry

  /-- The function returns a result r and r = m = n/2.
    Preconditions: n and edges satisfy the constraints: 1 <= n <= 50, edges is a list of pairs of distinct vertices in {0,...,n-1} with no repeated unordered pair, len(edges) <= n*(n-1)/2, and each edge vector has length 2. Additionally, n = 2*m for some integer m >= 1, and edges consists of exactly m disjoint edges that form a perfect matching on all n vertices: every vertex in {0,...,n-1} appears in exactly one edge (i.e., for each vertex v, the number of indices k with edges[k][0]=v or edges[k][1]=v is exactly 1). -/
  theorem spec_8 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (m : ℤ)
      (h : GraphInput n edges) (hm : 1 ≤ m) (hn : n.val = 2 * m)
      (hmatching : ∀ v ∈ vertexSet n.val, ∃! e : alloc.vec.Vec I64,
        e ∈ edges.val ∧ IsIncident e v) :
      ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
        r.val = m := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (m : ℤ)
        (h : GraphInput n edges) (hm : 1 ≤ m) (hn : n.val = 2 * m)
        (hmatching : ∀ v ∈ vertexSet n.val, ∃! e : alloc.vec.Vec I64,
          e ∈ edges.val ∧ IsIncident e v), ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
          r.val = m) := by
    sorry

  /-- The function returns a result r and r = 1 + (n - k).
    Preconditions: n and edges satisfy the constraints: 1 <= n <= 50, edges is a list of pairs of distinct vertices in {0,...,n-1} with no repeated unordered pair, len(edges) <= n*(n-1)/2, and each edge vector has length 2. Additionally, there exists an integer k with 1 <= k <= n such that the vertex set {0,1,...,k-1} induces a complete subgraph (for every distinct i, j in {0,...,k-1}, adj(i,j) holds), every vertex in {k,...,n-1} is isolated (has no incident edges), and there are no other edges. Equivalently, edges consists exactly of all unordered pairs {i,j} with 0 <= i < j < k. -/
  theorem spec_9 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (k : ℤ)
      (h : GraphInput n edges) (hk_lower : 1 ≤ k) (hk_upper : k ≤ n.val)
      (hclique : ∀ i j : ℤ, 0 ≤ i → i < j → j < k → adj edges i j)
      (hisolated : ∀ v ∈ vertexSet n.val, k ≤ v → ∀ u ∈ vertexSet n.val, ¬ adj edges v u) :
      ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
        r.val = 1 + (n.val - k) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (k : ℤ)
        (h : GraphInput n edges) (hk_lower : 1 ≤ k) (hk_upper : k ≤ n.val)
        (hclique : ∀ i j : ℤ, 0 ≤ i → i < j → j < k → adj edges i j)
        (hisolated : ∀ v ∈ vertexSet n.val, k ≤ v → ∀ u ∈ vertexSet n.val, ¬ adj edges v u), ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
          r.val = 1 + (n.val - k)) := by
    sorry

  /-- The function returns a result r. Then r = n if and only if len(edges) = 0.
    Preconditions: n is an integer with 1 <= n <= 50. edges is a list (slice) of vectors, each of length exactly 2. For each k with 0 <= k < len(edges), edges[k][0] and edges[k][1] are integers in {0,1,...,n-1} and edges[k][0] != edges[k][1]. No unordered pair of vertices appears more than once in edges, and len(edges) <= n*(n-1)/2. -/
  theorem spec_10 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : GraphInput n edges) :
      ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
        (r.val = n.val ↔ edges.val.length = 0) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : GraphInput n edges), ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
          (r.val = n.val ↔ edges.val.length = 0)) := by
    sorry

  /-- Let c = |{ C(u) : 0 <= u < n }|, where C(u) is the connected component of u as defined in spec_1. The function returns a result r. Then r = c if and only if every connected component of the graph is complete, i.e., for every u in {0,...,n-1}, C(u) is complete.
    Preconditions: n is an integer with 1 <= n <= 50. edges is a list (slice) of vectors, each of length exactly 2. For each k with 0 <= k < len(edges), edges[k][0] and edges[k][1] are integers in {0,1,...,n-1} and edges[k][0] != edges[k][1]. No unordered pair of vertices appears more than once in edges, and len(edges) <= n*(n-1)/2. -/
  theorem spec_11 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : GraphInput n edges) :
      ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
        (r.val = (componentCount n.val edges : ℤ) ↔
          ∀ u ∈ vertexSet n.val, IsComplete edges (connComp edges u)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : GraphInput n edges), ∃ r : I64, Aegis.CountCompleteComponents.count_complete_components n edges = ok r ∧
          (r.val = (componentCount n.val edges : ℤ) ↔
            ∀ u ∈ vertexSet n.val, IsComplete edges (connComp edges u))) := by
    sorry

  end AegisSpec.CountCompleteComponents
