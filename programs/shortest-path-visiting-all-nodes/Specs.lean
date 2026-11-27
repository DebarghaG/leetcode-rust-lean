import Aegis.ShortestPathLength.Code.Funs

/-!
# Specifications of `Aegis.ShortestPathLength.shortest_path_length`

LeetCode problem `shortest-path-visiting-all-nodes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ShortestPathLength

  def nOf (graph : Slice (alloc.vec.Vec I64)) : Nat :=
    graph.val.length

  def adj (graph : Slice (alloc.vec.Vec I64)) (i : Nat) : List Int :=
    match graph.val[i]? with
    | some row => row.val.map (fun x => IScalar.val x)
    | none => []

  def Occ (graph : Slice (alloc.vec.Vec I64)) (i j : Nat) : Prop :=
    (j : Int) ∈ adj graph i

  instance decidableOcc (graph : Slice (alloc.vec.Vec I64)) (i j : Nat) :
      Decidable (Occ graph i j) :=
    inferInstanceAs (Decidable ((j : Int) ∈ adj graph i))

  def SizeOk (graph : Slice (alloc.vec.Vec I64)) : Prop :=
    1 ≤ nOf graph ∧ nOf graph ≤ 12

  def ListsShort (graph : Slice (alloc.vec.Vec I64)) : Prop :=
    ∀ i, i < nOf graph → (adj graph i).length < nOf graph

  def InRangeNoLoops (graph : Slice (alloc.vec.Vec I64)) : Prop :=
    ∀ (i : Nat), i < nOf graph → ∀ x : Int, x ∈ adj graph i →
      0 ≤ x ∧ x < (nOf graph : Int) ∧ x ≠ (i : Int)

  def Symmetric (graph : Slice (alloc.vec.Vec I64)) : Prop :=
    ∀ i j, i < nOf graph → j < nOf graph → (Occ graph i j ↔ Occ graph j i)

  def Connected (graph : Slice (alloc.vec.Vec I64)) : Prop :=
    ∀ a b, a < nOf graph → b < nOf graph →
      ∃ (m : Nat) (u : Nat → Nat),
        u 0 = a ∧ u m = b ∧ ∀ t, t < m → Occ graph (u t) (u (t + 1))

  def Pre (graph : Slice (alloc.vec.Vec I64)) : Prop :=
    SizeOk graph ∧ ListsShort graph ∧ InRangeNoLoops graph ∧ Symmetric graph ∧
      Connected graph

  def EdgeCount (graph : Slice (alloc.vec.Vec I64)) : Nat :=
    (((Finset.range (nOf graph)).product (Finset.range (nOf graph))).filter
        (fun p : Nat × Nat => p.1 < p.2 ∧ Occ graph p.1 p.2)).card

  def TreeEdges (graph : Slice (alloc.vec.Vec I64)) : Prop :=
    EdgeCount graph = nOf graph - 1

  def VisitingWalk (graph : Slice (alloc.vec.Vec I64)) (L : Nat) : Prop :=
    ∃ v : Nat → Nat,
      (∀ t, t ≤ L → v t < nOf graph) ∧
      (∀ t, t < L → Occ graph (v t) (v (t + 1))) ∧
      (∀ u, u < nOf graph → ∃ t, t ≤ L ∧ v t = u)

  def IsMinVisitingWalk (graph : Slice (alloc.vec.Vec I64)) (L : Nat) : Prop :=
    VisitingWalk graph L ∧ ∀ L', VisitingWalk graph L' → L ≤ L'

  def HasHamiltonianPath (graph : Slice (alloc.vec.Vec I64)) : Prop :=
    ∃ w : Nat → Nat,
      (∀ t, t < nOf graph → w t < nOf graph) ∧
      (∀ t, t < nOf graph - 1 → Occ graph (w t) (w (t + 1))) ∧
      (∀ t t', t < nOf graph → t' < nOf graph → w t = w t' → t = t')

  def WalkFromTo (graph : Slice (alloc.vec.Vec I64)) (a b k : Nat) : Prop :=
    ∃ v : Nat → Nat,
      v 0 = a ∧ v k = b ∧ (∀ t, t ≤ k → v t < nOf graph) ∧
        ∀ t, t < k → Occ graph (v t) (v (t + 1))

  def IsDistance (graph : Slice (alloc.vec.Vec I64)) (a b k : Nat) : Prop :=
    WalkFromTo graph a b k ∧ ∀ k', WalkFromTo graph a b k' → k ≤ k'

  def IsDiameter (graph : Slice (alloc.vec.Vec I64)) (d : Nat) : Prop :=
    (∀ a b, a < nOf graph → b < nOf graph → ∃ k, IsDistance graph a b k ∧ k ≤ d) ∧
      (∃ a b, a < nOf graph ∧ b < nOf graph ∧ IsDistance graph a b d)

  /-- The function returns a result r (it does not fail) and r is the least L >= 0 for which there exists a sequence v_0, ..., v_L of integers such that: (1) 0 <= v_t < n for every t in [0,L]; (2) for every t with 0 <= t < L, v_{t+1} occurs in graph[v_t]; and (3) for every u in [0,n), there is some t in [0,L] with v_t = u. Equivalently, r is the number of edges in a shortest walk of graph that visits every node, with arbitrary start and end and with repetitions of nodes and edges allowed.
    Preconditions: Let n = len(graph). Assume: 1 <= n <= 12; for every i with 0 <= i < n, len(graph[i]) < n, and every integer x occurring in graph[i] satisfies 0 <= x < n and x != i; for every i,j with 0 <= i,j < n, j occurs in graph[i] iff i occurs in graph[j]; and the graph is connected, i.e. for every a,b in [0,n) there is a sequence a = u_0, u_1, ..., u_m = b (m >= 0) such that for every t < m, u_{t+1} occurs in graph[u_t]. -/
  theorem spec_1 (graph : Slice (alloc.vec.Vec I64)) (h : Pre graph) :
      ∃ r : I64,
        Aegis.ShortestPathLength.shortest_path_length graph = ok r ∧
          ∃ L : Nat, (r : Int) = (L : Int) ∧ IsMinVisitingWalk graph L := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (graph : Slice (alloc.vec.Vec I64)) (h : Pre graph), ∃ r : I64,
          Aegis.ShortestPathLength.shortest_path_length graph = ok r ∧
            ∃ L : Nat, (r : Int) = (L : Int) ∧ IsMinVisitingWalk graph L) := by
    sorry

  /-- The function returns a result r (Ok r) for every graph satisfying the preconditions; in particular it does not fail because of arithmetic overflow, out-of-bounds indexing, or panic.
    Preconditions: Let n = len(graph). Assume: 1 <= n <= 12; for every i with 0 <= i < n, len(graph[i]) < n, and every integer x occurring in graph[i] satisfies 0 <= x < n and x != i; for every i,j with 0 <= i,j < n, j occurs in graph[i] iff i occurs in graph[j]; and the graph is connected, i.e. for every a,b in [0,n) there is a sequence a = u_0, u_1, ..., u_m = b (m >= 0) such that for every t < m, u_{t+1} occurs in graph[u_t]. -/
  theorem spec_2 (graph : Slice (alloc.vec.Vec I64)) (h : Pre graph) :
      ∃ r : I64, Aegis.ShortestPathLength.shortest_path_length graph = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (graph : Slice (alloc.vec.Vec I64)) (h : Pre graph), ∃ r : I64, Aegis.ShortestPathLength.shortest_path_length graph = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= n - 1.
    Preconditions: Let n = len(graph). Assume: 1 <= n <= 12; for every i with 0 <= i < n, len(graph[i]) < n, and every integer x occurring in graph[i] satisfies 0 <= x < n and x != i; for every i,j with 0 <= i,j < n, j occurs in graph[i] iff i occurs in graph[j]; and the graph is connected, i.e. for every a,b in [0,n) there is a sequence a = u_0, u_1, ..., u_m = b (m >= 0) such that for every t < m, u_{t+1} occurs in graph[u_t]. -/
  theorem spec_3 (graph : Slice (alloc.vec.Vec I64)) (h : Pre graph) :
      ∀ r : I64,
        Aegis.ShortestPathLength.shortest_path_length graph = ok r →
          (nOf graph : Int) - 1 ≤ (r : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (graph : Slice (alloc.vec.Vec I64)) (h : Pre graph), ∀ r : I64,
          Aegis.ShortestPathLength.shortest_path_length graph = ok r →
            (nOf graph : Int) - 1 ≤ (r : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r <= 2*(n - 1).
    Preconditions: Let n = len(graph). Assume: 1 <= n <= 12; for every i with 0 <= i < n, len(graph[i]) < n, and every integer x occurring in graph[i] satisfies 0 <= x < n and x != i; for every i,j with 0 <= i,j < n, j occurs in graph[i] iff i occurs in graph[j]; and the graph is connected, i.e. for every a,b in [0,n) there is a sequence a = u_0, u_1, ..., u_m = b (m >= 0) such that for every t < m, u_{t+1} occurs in graph[u_t]. -/
  theorem spec_4 (graph : Slice (alloc.vec.Vec I64)) (h : Pre graph) :
      ∀ r : I64,
        Aegis.ShortestPathLength.shortest_path_length graph = ok r →
          (r : Int) ≤ 2 * ((nOf graph : Int) - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (graph : Slice (alloc.vec.Vec I64)) (h : Pre graph), ∀ r : I64,
          Aegis.ShortestPathLength.shortest_path_length graph = ok r →
            (r : Int) ≤ 2 * ((nOf graph : Int) - 1)) := by
    sorry

  /-- Whenever the function returns a result r, r = n - 1 if and only if there exists a sequence w_0, ..., w_{n-1} of nodes such that the values w_0, ..., w_{n-1} are pairwise distinct and, for every t with 0 <= t < n-1, w_{t+1} occurs in graph[w_t].
    Preconditions: Let n = len(graph). Assume: 1 <= n <= 12; for every i with 0 <= i < n, len(graph[i]) < n, and every integer x occurring in graph[i] satisfies 0 <= x < n and x != i; for every i,j with 0 <= i,j < n, j occurs in graph[i] iff i occurs in graph[j]; and the graph is connected, i.e. for every a,b in [0,n) there is a sequence a = u_0, u_1, ..., u_m = b (m >= 0) such that for every t < m, u_{t+1} occurs in graph[u_t]. -/
  theorem spec_5 (graph : Slice (alloc.vec.Vec I64)) (h : Pre graph) :
      ∀ r : I64,
        Aegis.ShortestPathLength.shortest_path_length graph = ok r →
          ((r : Int) = (nOf graph : Int) - 1 ↔ HasHamiltonianPath graph) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (graph : Slice (alloc.vec.Vec I64)) (h : Pre graph), ∀ r : I64,
          Aegis.ShortestPathLength.shortest_path_length graph = ok r →
            ((r : Int) = (nOf graph : Int) - 1 ↔ HasHamiltonianPath graph)) := by
    sorry

  /-- If the function returns r for graph and r' for graph', then r' <= r.
    Preconditions: Let n = len(graph) = len(graph'). Both graph and graph' satisfy the problem constraints: 1 <= n <= 12; for every i with 0 <= i < n, len(graph[i]) < n and len(graph'[i]) < n, every integer occurring in either adjacency list is in [0,n) and is not equal to its own index; adjacency is symmetric in each graph; each graph is connected. Moreover, for every i,j in [0,n), if j occurs in graph[i] then j occurs in graph'[i]. -/
  theorem spec_6 (graph graph' : Slice (alloc.vec.Vec I64))
      (h : Pre graph) (h' : Pre graph')
      (hlen : nOf graph = nOf graph')
      (hsub : ∀ i j, i < nOf graph → j < nOf graph → Occ graph i j → Occ graph' i j) :
      ∀ r r' : I64,
        Aegis.ShortestPathLength.shortest_path_length graph = ok r →
          Aegis.ShortestPathLength.shortest_path_length graph' = ok r' →
            (r' : Int) ≤ (r : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (graph graph' : Slice (alloc.vec.Vec I64))
        (h : Pre graph) (h' : Pre graph')
        (hlen : nOf graph = nOf graph')
        (hsub : ∀ i j, i < nOf graph → j < nOf graph → Occ graph i j → Occ graph' i j), ∀ r r' : I64,
          Aegis.ShortestPathLength.shortest_path_length graph = ok r →
            Aegis.ShortestPathLength.shortest_path_length graph' = ok r' →
              (r' : Int) ≤ (r : Int)) := by
    sorry

  /-- If the function returns r for graph and r' for graph', then r = r'.
    Preconditions: Let n = len(graph) = len(graph'). Both graph and graph' satisfy the problem constraints: 1 <= n <= 12; for every i with 0 <= i < n, len(graph[i]) < n and len(graph'[i]) < n, every integer occurring in either adjacency list is in [0,n) and is not equal to its own index; adjacency is symmetric in each graph; each graph is connected. Moreover, for every i,j in [0,n), j occurs in graph[i] iff j occurs in graph'[i]. -/
  theorem spec_7 (graph graph' : Slice (alloc.vec.Vec I64))
      (h : Pre graph) (h' : Pre graph')
      (hlen : nOf graph = nOf graph')
      (hsame : ∀ i j, i < nOf graph → j < nOf graph → (Occ graph i j ↔ Occ graph' i j)) :
      ∀ r r' : I64,
        Aegis.ShortestPathLength.shortest_path_length graph = ok r →
          Aegis.ShortestPathLength.shortest_path_length graph' = ok r' →
            (r' : Int) = (r : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (graph graph' : Slice (alloc.vec.Vec I64))
        (h : Pre graph) (h' : Pre graph')
        (hlen : nOf graph = nOf graph')
        (hsame : ∀ i j, i < nOf graph → j < nOf graph → (Occ graph i j ↔ Occ graph' i j)), ∀ r r' : I64,
          Aegis.ShortestPathLength.shortest_path_length graph = ok r →
            Aegis.ShortestPathLength.shortest_path_length graph' = ok r' →
              (r' : Int) = (r : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = 2*(n - 1) - d.
    Preconditions: Let n = len(graph). Assume: 1 <= n <= 12; for every i with 0 <= i < n, len(graph[i]) < n, and every integer x occurring in graph[i] satisfies 0 <= x < n and x != i; for every i,j with 0 <= i,j < n, j occurs in graph[i] iff i occurs in graph[j]; and the graph is connected. Additionally, graph is a tree: the number of unordered pairs {a,b} with 0 <= a < b < n and b occurs in graph[a] is exactly n-1. Let d be the maximum, over all a,b in [0,n), of the number of edges in the unique simple path from a to b in this tree, with d=0 when n=1. -/
  theorem spec_8 (graph : Slice (alloc.vec.Vec I64)) (h : Pre graph)
      (htree : TreeEdges graph) {d : Nat} (hd : IsDiameter graph d) :
      ∀ r : I64,
        Aegis.ShortestPathLength.shortest_path_length graph = ok r →
          (r : Int) = 2 * ((nOf graph : Int) - 1) - (d : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (graph : Slice (alloc.vec.Vec I64)) (h : Pre graph)
        (htree : TreeEdges graph) {d : Nat} (hd : IsDiameter graph d), ∀ r : I64,
          Aegis.ShortestPathLength.shortest_path_length graph = ok r →
            (r : Int) = 2 * ((nOf graph : Int) - 1) - (d : Int)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a sequence v_0, ..., v_r such that 0 <= v_t < n for all t in [0,r], v_{t+1} occurs in graph[v_t] for all t with 0 <= t < r, and every node u in [0,n) occurs among v_0, ..., v_r.
    Preconditions: Let n = len(graph). Assume: 1 <= n <= 12; for every i with 0 <= i < n, len(graph[i]) < n, and every integer x occurring in graph[i] satisfies 0 <= x < n and x != i; for every i,j with 0 <= i,j < n, j occurs in graph[i] iff i occurs in graph[j]; and the graph is connected, i.e. for every a,b in [0,n) there is a sequence a = u_0, u_1, ..., u_m = b (m >= 0) such that for every t < m, u_{t+1} occurs in graph[u_t]. -/
  theorem spec_9 (graph : Slice (alloc.vec.Vec I64)) (h : Pre graph) :
      ∀ r : I64,
        Aegis.ShortestPathLength.shortest_path_length graph = ok r →
          ∃ L : Nat, (r : Int) = (L : Int) ∧ VisitingWalk graph L := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (graph : Slice (alloc.vec.Vec I64)) (h : Pre graph), ∀ r : I64,
          Aegis.ShortestPathLength.shortest_path_length graph = ok r →
            ∃ L : Nat, (r : Int) = (L : Int) ∧ VisitingWalk graph L) := by
    sorry

  /-- Whenever the function returns a result r, for every L with 0 <= L < r and every sequence v_0, ..., v_L satisfying 0 <= v_t < n for all t in [0,L] and v_{t+1} occurs in graph[v_t] for all t with 0 <= t < L, there is some node u in [0,n) that does not occur among v_0, ..., v_L.
    Preconditions: Let n = len(graph). Assume: 1 <= n <= 12; for every i with 0 <= i < n, len(graph[i]) < n, and every integer x occurring in graph[i] satisfies 0 <= x < n and x != i; for every i,j with 0 <= i,j < n, j occurs in graph[i] iff i occurs in graph[j]; and the graph is connected, i.e. for every a,b in [0,n) there is a sequence a = u_0, u_1, ..., u_m = b (m >= 0) such that for every t < m, u_{t+1} occurs in graph[u_t]. -/
  theorem spec_10 (graph : Slice (alloc.vec.Vec I64)) (h : Pre graph) :
      ∀ r : I64,
        Aegis.ShortestPathLength.shortest_path_length graph = ok r →
          ∀ (L : Nat) (v : Nat → Nat),
            (L : Int) < (r : Int) →
              (∀ t, t ≤ L → v t < nOf graph) →
                (∀ t, t < L → Occ graph (v t) (v (t + 1))) →
                  ∃ u, u < nOf graph ∧ ∀ t, t ≤ L → v t ≠ u := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (graph : Slice (alloc.vec.Vec I64)) (h : Pre graph), ∀ r : I64,
          Aegis.ShortestPathLength.shortest_path_length graph = ok r →
            ∀ (L : Nat) (v : Nat → Nat),
              (L : Int) < (r : Int) →
                (∀ t, t ≤ L → v t < nOf graph) →
                  (∀ t, t < L → Occ graph (v t) (v (t + 1))) →
                    ∃ u, u < nOf graph ∧ ∀ t, t ≤ L → v t ≠ u) := by
    sorry

  end AegisSpec.ShortestPathLength
