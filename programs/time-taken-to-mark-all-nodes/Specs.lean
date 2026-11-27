import Aegis.TimeTaken.Code.Funs

/-!
# Specifications of `Aegis.TimeTaken.time_taken`

LeetCode problem `time-taken-to-mark-all-nodes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  open Aegis.TimeTaken

  namespace AegisSpec.TimeTaken

  def Delta (v : Nat) : Nat := if v % 2 = 0 then 2 else 1

  def Endpoints (e : alloc.vec.Vec Std.I64) : Int × Int :=
    ((e.val.getD 0 0#i64).val, (e.val.getD 1 0#i64).val)

  def EdgePairs (edges : Slice (alloc.vec.Vec Std.I64)) : List (Nat × Nat) :=
    edges.val.map fun e => ((Endpoints e).1.toNat, (Endpoints e).2.toNat)

  def UnorientedPairs (edges : Slice (alloc.vec.Vec Std.I64)) : List (Nat × Nat) :=
    (EdgePairs edges).map fun p => (min p.1 p.2, max p.1 p.2)

  def Adj (edges : Slice (alloc.vec.Vec Std.I64)) (a b : Nat) : Prop :=
    (a, b) ∈ EdgePairs edges ∨ (b, a) ∈ EdgePairs edges

  def Reaches (edges : Slice (alloc.vec.Vec Std.I64)) (a b : Nat) : Prop :=
    Relation.ReflTransGen (Adj edges) a b

  def ConnectedOn (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Prop :=
    ∀ a b, a < n → b < n → Reaches edges a b

  def AcyclicOn (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Prop :=
    (∀ a, a < n → ¬ Adj edges a a) ∧
      ¬ ∃ p : List Nat,
          3 ≤ p.length ∧ p.Nodup ∧ (∀ x ∈ p, x < n) ∧ p.IsChain (Adj edges) ∧
            Adj edges (p.getLast!) (p.head!)

  def IsTreeOn (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Prop :=
    ConnectedOn edges n ∧ AcyclicOn edges n

  def NeighborList (edges : Slice (alloc.vec.Vec Std.I64)) (v : Nat) : List Nat :=
    (EdgePairs edges).flatMap fun p =>
      if p.1 = v then [p.2] else if p.2 = v then [p.1] else []

  def Degree (edges : Slice (alloc.vec.Vec Std.I64)) (v : Nat) : Nat :=
    (NeighborList edges v).toFinset.card

  def IsLeaf (edges : Slice (alloc.vec.Vec Std.I64)) (l : Nat) : Prop := Degree edges l = 1

  def IsSimplePath (edges : Slice (alloc.vec.Vec Std.I64)) (i v : Nat) (p : List Nat) : Prop :=
    p.head? = some i ∧ p.getLast? = some v ∧ p.Nodup ∧ p.IsChain (Adj edges)

  def PathWeight (p : List Nat) : Nat := (p.map Delta).sum

  noncomputable def W (edges : Slice (alloc.vec.Vec Std.I64)) (i v : Nat) : Int :=
    ((sInf {k : Nat | ∃ p : List Nat, IsSimplePath edges i v p ∧ PathWeight p.tail = k} : Nat) :
      Int)

  /-- Let delta(v) = 1 if v is odd and 2 if v is even. For nodes i and v, let W(i,v) = 0 if i = v, and otherwise let W(i,v) be the sum of delta(x) over the nodes x on the unique simple path from i to v in the tree, excluding i and including v. The function returns a result r such that len(r) = n and, for every i with 0 <= i < n, r[i] is the maximum of W(i,v) over all v with 0 <= v < n. Equivalently, r[i] is the time when all nodes become marked if node i is marked at time 0 and all other nodes are initially unmarked.
    Preconditions: Let n = len(edges) + 1. The input satisfies 2 <= n <= 100000; len(edges) = n - 1; every edges[j] for 0 <= j < len(edges) has length 2; for every such j, 0 <= edges[j][0] < n and 0 <= edges[j][1] < n; and the undirected graph with vertices 0,...,n-1 and an edge between a and b iff some j has (edges[j][0]=a and edges[j][1]=b) or (edges[j][0]=b and edges[j][1]=a) is a tree (connected and acyclic). -/
  theorem spec_1 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = (Slice.len edges).val + 1)
      (h_len : edges.val.length = n - 1)
      (hn_lower : 2 ≤ n)
      (hn_upper : n ≤ 100000)
      (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
      (h_endpoints : ∀ j (hj : j < edges.val.length),
        0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
          0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
      (h_tree : IsTreeOn edges n) :
      ∃ r : alloc.vec.Vec Std.I64, time_taken edges = ok r ∧ r.val.length = n ∧
        ∀ i, i < n →
          (∀ v, v < n → W edges i v ≤ (r.val.getD i 0#i64).val) ∧
            ∃ v, v < n ∧ W edges i v = (r.val.getD i 0#i64).val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = (Slice.len edges).val + 1)
        (h_len : edges.val.length = n - 1)
        (hn_lower : 2 ≤ n)
        (hn_upper : n ≤ 100000)
        (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
        (h_endpoints : ∀ j (hj : j < edges.val.length),
          0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
            0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
        (h_tree : IsTreeOn edges n), ∃ r : alloc.vec.Vec Std.I64, time_taken edges = ok r ∧ r.val.length = n ∧
          ∀ i, i < n →
            (∀ v, v < n → W edges i v ≤ (r.val.getD i 0#i64).val) ∧
              ∃ v, v < n ∧ W edges i v = (r.val.getD i 0#i64).val) := by
    sorry

  /-- The function returns a result r with len(r) = len(edges) + 1. Thus r has exactly one entry for each node 0, 1, ..., n-1, where n = len(edges) + 1.
    Preconditions: Let n = len(edges) + 1. The input satisfies 2 <= n <= 100000; len(edges) = n - 1; every edges[j] for 0 <= j < len(edges) has length 2; for every such j, 0 <= edges[j][0] < n and 0 <= edges[j][1] < n; and the undirected graph with vertices 0,...,n-1 and an edge between a and b iff some j has (edges[j][0]=a and edges[j][1]=b) or (edges[j][0]=b and edges[j][1]=a) is a tree (connected and acyclic). -/
  theorem spec_2 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = (Slice.len edges).val + 1)
      (h_len : edges.val.length = n - 1)
      (hn_lower : 2 ≤ n)
      (hn_upper : n ≤ 100000)
      (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
      (h_endpoints : ∀ j (hj : j < edges.val.length),
        0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
          0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
      (h_tree : IsTreeOn edges n) :
      ∃ r : alloc.vec.Vec Std.I64,
        time_taken edges = ok r ∧ r.val.length = (Slice.len edges).val + 1 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = (Slice.len edges).val + 1)
        (h_len : edges.val.length = n - 1)
        (hn_lower : 2 ≤ n)
        (hn_upper : n ≤ 100000)
        (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
        (h_endpoints : ∀ j (hj : j < edges.val.length),
          0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
            0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
        (h_tree : IsTreeOn edges n), ∃ r : alloc.vec.Vec Std.I64,
          time_taken edges = ok r ∧ r.val.length = (Slice.len edges).val + 1) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < n, r[i] >= 1. In other words, starting from any single node, at least one further node must be marked at a positive time, so the final marking time is positive.
    Preconditions: Let n = len(edges) + 1. The input satisfies 2 <= n <= 100000; len(edges) = n - 1; every edges[j] for 0 <= j < len(edges) has length 2; for every such j, 0 <= edges[j][0] < n and 0 <= edges[j][1] < n; and the undirected graph with vertices 0,...,n-1 and an edge between a and b iff some j has (edges[j][0]=a and edges[j][1]=b) or (edges[j][0]=b and edges[j][1]=a) is a tree (connected and acyclic). -/
  theorem spec_3 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = (Slice.len edges).val + 1)
      (h_len : edges.val.length = n - 1)
      (hn_lower : 2 ≤ n)
      (hn_upper : n ≤ 100000)
      (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
      (h_endpoints : ∀ j (hj : j < edges.val.length),
        0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
          0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
      (h_tree : IsTreeOn edges n) :
      ∃ r : alloc.vec.Vec Std.I64,
        time_taken edges = ok r ∧ ∀ i, i < n → (1 : Int) ≤ (r.val.getD i 0#i64).val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = (Slice.len edges).val + 1)
        (h_len : edges.val.length = n - 1)
        (hn_lower : 2 ≤ n)
        (hn_upper : n ≤ 100000)
        (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
        (h_endpoints : ∀ j (hj : j < edges.val.length),
          0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
            0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
        (h_tree : IsTreeOn edges n), ∃ r : alloc.vec.Vec Std.I64,
          time_taken edges = ok r ∧ ∀ i, i < n → (1 : Int) ≤ (r.val.getD i 0#i64).val) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < n, r[i] <= 2 * (n - 1).
    Preconditions: Let n = len(edges) + 1. The input satisfies 2 <= n <= 100000; len(edges) = n - 1; every edges[j] for 0 <= j < len(edges) has length 2; for every such j, 0 <= edges[j][0] < n and 0 <= edges[j][1] < n; and the undirected graph with vertices 0,...,n-1 and an edge between a and b iff some j has (edges[j][0]=a and edges[j][1]=b) or (edges[j][0]=b and edges[j][1]=a) is a tree (connected and acyclic). -/
  theorem spec_4 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = (Slice.len edges).val + 1)
      (h_len : edges.val.length = n - 1)
      (hn_lower : 2 ≤ n)
      (hn_upper : n ≤ 100000)
      (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
      (h_endpoints : ∀ j (hj : j < edges.val.length),
        0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
          0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
      (h_tree : IsTreeOn edges n) :
      ∃ r : alloc.vec.Vec Std.I64,
        time_taken edges = ok r ∧
          ∀ i, i < n → (r.val.getD i 0#i64).val ≤ 2 * ((n : Int) - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = (Slice.len edges).val + 1)
        (h_len : edges.val.length = n - 1)
        (hn_lower : 2 ≤ n)
        (hn_upper : n ≤ 100000)
        (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
        (h_endpoints : ∀ j (hj : j < edges.val.length),
          0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
            0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
        (h_tree : IsTreeOn edges n), ∃ r : alloc.vec.Vec Std.I64,
          time_taken edges = ok r ∧
            ∀ i, i < n → (r.val.getD i 0#i64).val ≤ 2 * ((n : Int) - 1)) := by
    sorry

  /-- Let delta(v) = 1 if v is odd and 2 if v is even, and for nodes i and v let W(i,v) be the sum of delta(x) over the nodes x on the unique simple path from i to v, excluding i and including v, with W(i,i) = 0. The function returns a result r such that for every i and v with 0 <= i < n and 0 <= v < n, W(i,v) <= r[i]. In other words, no individual node can have a marking time larger than the reported time for all nodes to be marked.
    Preconditions: Let n = len(edges) + 1. The input satisfies 2 <= n <= 100000; len(edges) = n - 1; every edges[j] for 0 <= j < len(edges) has length 2; for every such j, 0 <= edges[j][0] < n and 0 <= edges[j][1] < n; and the undirected graph with vertices 0,...,n-1 and an edge between a and b iff some j has (edges[j][0]=a and edges[j][1]=b) or (edges[j][0]=b and edges[j][1]=a) is a tree (connected and acyclic). -/
  theorem spec_5 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = (Slice.len edges).val + 1)
      (h_len : edges.val.length = n - 1)
      (hn_lower : 2 ≤ n)
      (hn_upper : n ≤ 100000)
      (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
      (h_endpoints : ∀ j (hj : j < edges.val.length),
        0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
          0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
      (h_tree : IsTreeOn edges n) :
      ∃ r : alloc.vec.Vec Std.I64,
        time_taken edges = ok r ∧
          ∀ i v, i < n → v < n → W edges i v ≤ (r.val.getD i 0#i64).val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = (Slice.len edges).val + 1)
        (h_len : edges.val.length = n - 1)
        (hn_lower : 2 ≤ n)
        (hn_upper : n ≤ 100000)
        (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
        (h_endpoints : ∀ j (hj : j < edges.val.length),
          0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
            0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
        (h_tree : IsTreeOn edges n), ∃ r : alloc.vec.Vec Std.I64,
          time_taken edges = ok r ∧
            ∀ i v, i < n → v < n → W edges i v ≤ (r.val.getD i 0#i64).val) := by
    sorry

  /-- Let delta(v) = 1 if v is odd and 2 if v is even, and for nodes i and v let W(i,v) be the sum of delta(x) over the nodes x on the unique simple path from i to v, excluding i and including v, with W(i,i) = 0. The function returns a result r such that for every i with 0 <= i < n, there exists v with 0 <= v < n for which r[i] = W(i,v). Thus the maximum defining r[i] is actually attained by some node.
    Preconditions: Let n = len(edges) + 1. The input satisfies 2 <= n <= 100000; len(edges) = n - 1; every edges[j] for 0 <= j < len(edges) has length 2; for every such j, 0 <= edges[j][0] < n and 0 <= edges[j][1] < n; and the undirected graph with vertices 0,...,n-1 and an edge between a and b iff some j has (edges[j][0]=a and edges[j][1]=b) or (edges[j][0]=b and edges[j][1]=a) is a tree (connected and acyclic). -/
  theorem spec_6 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = (Slice.len edges).val + 1)
      (h_len : edges.val.length = n - 1)
      (hn_lower : 2 ≤ n)
      (hn_upper : n ≤ 100000)
      (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
      (h_endpoints : ∀ j (hj : j < edges.val.length),
        0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
          0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
      (h_tree : IsTreeOn edges n) :
      ∃ r : alloc.vec.Vec Std.I64,
        time_taken edges = ok r ∧
          ∀ i, i < n → ∃ v, v < n ∧ (r.val.getD i 0#i64).val = W edges i v := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = (Slice.len edges).val + 1)
        (h_len : edges.val.length = n - 1)
        (hn_lower : 2 ≤ n)
        (hn_upper : n ≤ 100000)
        (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
        (h_endpoints : ∀ j (hj : j < edges.val.length),
          0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
            0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
        (h_tree : IsTreeOn edges n), ∃ r : alloc.vec.Vec Std.I64,
          time_taken edges = ok r ∧
            ∀ i, i < n → ∃ v, v < n ∧ (r.val.getD i 0#i64).val = W edges i v) := by
    sorry

  /-- Let delta(v) = 1 if v is odd and 2 if v is even. The function returns a result r such that for every i and v with 0 <= i < n, 0 <= v < n, and i != v, r[i] >= delta(v).
    Preconditions: Let n = len(edges) + 1. The input satisfies 2 <= n <= 100000; len(edges) = n - 1; every edges[j] for 0 <= j < len(edges) has length 2; for every such j, 0 <= edges[j][0] < n and 0 <= edges[j][1] < n; and the undirected graph with vertices 0,...,n-1 and an edge between a and b iff some j has (edges[j][0]=a and edges[j][1]=b) or (edges[j][0]=b and edges[j][1]=a) is a tree (connected and acyclic). -/
  theorem spec_7 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = (Slice.len edges).val + 1)
      (h_len : edges.val.length = n - 1)
      (hn_lower : 2 ≤ n)
      (hn_upper : n ≤ 100000)
      (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
      (h_endpoints : ∀ j (hj : j < edges.val.length),
        0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
          0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
      (h_tree : IsTreeOn edges n) :
      ∃ r : alloc.vec.Vec Std.I64,
        time_taken edges = ok r ∧
          ∀ i v, i < n → v < n → i ≠ v → ((Delta v : Nat) : Int) ≤ (r.val.getD i 0#i64).val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = (Slice.len edges).val + 1)
        (h_len : edges.val.length = n - 1)
        (hn_lower : 2 ≤ n)
        (hn_upper : n ≤ 100000)
        (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
        (h_endpoints : ∀ j (hj : j < edges.val.length),
          0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
            0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
        (h_tree : IsTreeOn edges n), ∃ r : alloc.vec.Vec Std.I64,
          time_taken edges = ok r ∧
            ∀ i v, i < n → v < n → i ≠ v → ((Delta v : Nat) : Int) ≤ (r.val.getD i 0#i64).val) := by
    sorry

  /-- Let delta(v) = 1 if v is odd and 2 if v is even, and for nodes i and v let W(i,v) be the sum of delta(x) over the nodes x on the unique simple path from i to v, excluding i and including v, with W(i,i) = 0. Let L be the set of leaves of the tree, meaning nodes of degree exactly 1. The function returns a result r such that for every i with 0 <= i < n, r[i] equals the maximum of W(i,l) over all l in L.
    Preconditions: Let n = len(edges) + 1. The input satisfies 2 <= n <= 100000; len(edges) = n - 1; every edges[j] for 0 <= j < len(edges) has length 2; for every such j, 0 <= edges[j][0] < n and 0 <= edges[j][1] < n; and the undirected graph with vertices 0,...,n-1 and an edge between a and b iff some j has (edges[j][0]=a and edges[j][1]=b) or (edges[j][0]=b and edges[j][1]=a) is a tree (connected and acyclic). -/
  theorem spec_8 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = (Slice.len edges).val + 1)
      (h_len : edges.val.length = n - 1)
      (hn_lower : 2 ≤ n)
      (hn_upper : n ≤ 100000)
      (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
      (h_endpoints : ∀ j (hj : j < edges.val.length),
        0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
          0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
      (h_tree : IsTreeOn edges n) :
      ∃ r : alloc.vec.Vec Std.I64,
        time_taken edges = ok r ∧
          ∀ i, i < n →
            (∀ l, l < n → IsLeaf edges l → W edges i l ≤ (r.val.getD i 0#i64).val) ∧
              ∃ l, l < n ∧ IsLeaf edges l ∧ W edges i l = (r.val.getD i 0#i64).val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = (Slice.len edges).val + 1)
        (h_len : edges.val.length = n - 1)
        (hn_lower : 2 ≤ n)
        (hn_upper : n ≤ 100000)
        (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
        (h_endpoints : ∀ j (hj : j < edges.val.length),
          0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
            0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
        (h_tree : IsTreeOn edges n), ∃ r : alloc.vec.Vec Std.I64,
          time_taken edges = ok r ∧
            ∀ i, i < n →
              (∀ l, l < n → IsLeaf edges l → W edges i l ≤ (r.val.getD i 0#i64).val) ∧
                ∃ l, l < n ∧ IsLeaf edges l ∧ W edges i l = (r.val.getD i 0#i64).val) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r: it does not fail, panic, or overflow.
    Preconditions: Let n = len(edges) + 1. The input satisfies 2 <= n <= 100000; len(edges) = n - 1; every edges[j] for 0 <= j < len(edges) has length 2; for every such j, 0 <= edges[j][0] < n and 0 <= edges[j][1] < n; and the undirected graph with vertices 0,...,n-1 and an edge between a and b iff some j has (edges[j][0]=a and edges[j][1]=b) or (edges[j][0]=b and edges[j][1]=a) is a tree (connected and acyclic). -/
  theorem spec_9 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = (Slice.len edges).val + 1)
      (h_len : edges.val.length = n - 1)
      (hn_lower : 2 ≤ n)
      (hn_upper : n ≤ 100000)
      (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
      (h_endpoints : ∀ j (hj : j < edges.val.length),
        0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
          0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
      (h_tree : IsTreeOn edges n) :
      ∃ r : alloc.vec.Vec Std.I64, time_taken edges = ok r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = (Slice.len edges).val + 1)
        (h_len : edges.val.length = n - 1)
        (hn_lower : 2 ≤ n)
        (hn_upper : n ≤ 100000)
        (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
        (h_endpoints : ∀ j (hj : j < edges.val.length),
          0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
            0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
        (h_tree : IsTreeOn edges n), ∃ r : alloc.vec.Vec Std.I64, time_taken edges = ok r) := by
    sorry

  /-- Whenever the function returns r on input edges and returns r' on input edges', we have r = r'. Thus the answer does not depend on the order in which the edges are listed.
    Preconditions: Let n = len(edges) + 1. The input edges satisfies 2 <= n <= 100000; len(edges) = n - 1; every edges[j] for 0 <= j < len(edges) has length 2; for every such j, 0 <= edges[j][0] < n and 0 <= edges[j][1] < n; and the undirected graph with vertices 0,...,n-1 and an edge between a and b iff some j has (edges[j][0]=a and edges[j][1]=b) or (edges[j][0]=b and edges[j][1]=a) is a tree (connected and acyclic). Also let edges' be any slice of len(edges) pairs that is a permutation of the ordered pairs in edges. -/
  theorem spec_10 (edges edges' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = (Slice.len edges).val + 1)
      (h_len : edges.val.length = n - 1)
      (hn_lower : 2 ≤ n)
      (hn_upper : n ≤ 100000)
      (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
      (h_endpoints : ∀ j (hj : j < edges.val.length),
        0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
          0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
      (h_tree : IsTreeOn edges n)
      (h_entries' : ∀ j (hj : j < edges'.val.length), (edges'.val[j]'hj).val.length = 2)
      (h_perm : List.Perm (EdgePairs edges) (EdgePairs edges')) :
      ∀ r r' : alloc.vec.Vec Std.I64,
        time_taken edges = ok r → time_taken edges' = ok r' → r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (edges edges' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = (Slice.len edges).val + 1)
        (h_len : edges.val.length = n - 1)
        (hn_lower : 2 ≤ n)
        (hn_upper : n ≤ 100000)
        (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
        (h_endpoints : ∀ j (hj : j < edges.val.length),
          0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
            0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
        (h_tree : IsTreeOn edges n)
        (h_entries' : ∀ j (hj : j < edges'.val.length), (edges'.val[j]'hj).val.length = 2)
        (h_perm : List.Perm (EdgePairs edges) (EdgePairs edges')), ∀ r r' : alloc.vec.Vec Std.I64,
          time_taken edges = ok r → time_taken edges' = ok r' → r = r') := by
    sorry

  /-- Whenever the function returns r on input edges and returns r' on input edges', we have r = r'. Thus the answer does not depend on the orientation chosen for each undirected edge.
    Preconditions: Let n = len(edges) + 1. The input edges satisfies 2 <= n <= 100000; len(edges) = n - 1; every edges[j] for 0 <= j < len(edges) has length 2; for every such j, 0 <= edges[j][0] < n and 0 <= edges[j][1] < n; and the undirected graph with vertices 0,...,n-1 and an edge between a and b iff some j has (edges[j][0]=a and edges[j][1]=b) or (edges[j][0]=b and edges[j][1]=a) is a tree (connected and acyclic). Also let edges' be obtained from edges by replacing any subset of entries [a,b] by [b,a]. -/
  theorem spec_11 (edges edges' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hn : n = (Slice.len edges).val + 1)
      (h_len : edges.val.length = n - 1)
      (hn_lower : 2 ≤ n)
      (hn_upper : n ≤ 100000)
      (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
      (h_endpoints : ∀ j (hj : j < edges.val.length),
        0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
          0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
      (h_tree : IsTreeOn edges n)
      (h_entries' : ∀ j (hj : j < edges'.val.length), (edges'.val[j]'hj).val.length = 2)
      (h_perm : List.Perm (UnorientedPairs edges) (UnorientedPairs edges')) :
      ∀ r r' : alloc.vec.Vec Std.I64,
        time_taken edges = ok r → time_taken edges' = ok r' → r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (edges edges' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hn : n = (Slice.len edges).val + 1)
        (h_len : edges.val.length = n - 1)
        (hn_lower : 2 ≤ n)
        (hn_upper : n ≤ 100000)
        (h_entries : ∀ j (hj : j < edges.val.length), (edges.val[j]'hj).val.length = 2)
        (h_endpoints : ∀ j (hj : j < edges.val.length),
          0 ≤ (Endpoints (edges.val[j]'hj)).1 ∧ (Endpoints (edges.val[j]'hj)).1 < (n : Int) ∧
            0 ≤ (Endpoints (edges.val[j]'hj)).2 ∧ (Endpoints (edges.val[j]'hj)).2 < (n : Int))
        (h_tree : IsTreeOn edges n)
        (h_entries' : ∀ j (hj : j < edges'.val.length), (edges'.val[j]'hj).val.length = 2)
        (h_perm : List.Perm (UnorientedPairs edges) (UnorientedPairs edges')), ∀ r r' : alloc.vec.Vec Std.I64,
          time_taken edges = ok r → time_taken edges' = ok r' → r = r') := by
    sorry

  end AegisSpec.TimeTaken
