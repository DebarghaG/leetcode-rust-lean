import Aegis.ClosestNode.Code.Funs

/-!
# Specifications of `Aegis.ClosestNode.closest_node`

LeetCode problem `closest-node-to-path-in-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ClosestNode

  def vecInts (v : alloc.vec.Vec Std.I64) : List Int := v.val.map (fun x => x.val)

  def edgeAt (edges : List (alloc.vec.Vec Std.I64)) (i : Nat) : Option (Int × Int) :=
    match edges[i]? with
    | some e =>
      match vecInts e with
      | [a, b] => some (a, b)
      | _ => none
    | none => none

  def queryAt (query : List (alloc.vec.Vec Std.I64)) (i : Nat) : Option (Int × Int × Int) :=
    match query[i]? with
    | some q =>
      match vecInts q with
      | [s, t, z] => some (s, t, z)
      | _ => none
    | none => none

  def Adj (edges : List (alloc.vec.Vec Std.I64)) (x y : Int) : Prop :=
    ∃ e ∈ edges, vecInts e = [x, y] ∨ vecInts e = [y, x]

  def AdjChain (edges : List (alloc.vec.Vec Std.I64)) : List Int → Prop
    | [] => True
    | [_] => True
    | x :: y :: rest => Adj edges x y ∧ AdjChain edges (y :: rest)

  def Walk (edges : List (alloc.vec.Vec Std.I64)) (p : List Int) : Prop :=
    p ≠ [] ∧ AdjChain edges p

  def IsSimplePath (edges : List (alloc.vec.Vec Std.I64)) (x y : Int) (p : List Int) : Prop :=
    Walk edges p ∧ p.Nodup ∧ p.head? = some x ∧ p.getLast? = some y

  def IsTree (n : Int) (edges : List (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ x y : Int, 0 ≤ x → x < n → 0 ≤ y → y < n → ∃! p : List Int, IsSimplePath edges x y p

  noncomputable def dist (edges : List (alloc.vec.Vec Std.I64)) (x y : Int) : Int :=
    (((sInf {k : Nat | ∃ p : List Int, IsSimplePath edges x y p ∧ p.length = k + 1}) : Nat) : Int)

  def answerAt (r : alloc.vec.Vec Std.I64) (i : Nat) : Option Int := (vecInts r)[i]?

  def OnPath (edges : List (alloc.vec.Vec Std.I64)) (s t a : Int) : Prop :=
    dist edges s a + dist edges a t = dist edges s t

  def EdgesValid (n : Int) (edges : List (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ i, i < edges.length →
      ∃ a b : Int, edgeAt edges i = some (a, b) ∧
        0 ≤ a ∧ a < n ∧ 0 ≤ b ∧ b < n ∧ a ≠ b

  def QueryValid (n : Int) (query : List (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ i, i < query.length →
      ∃ s t z : Int, queryAt query i = some (s, t, z) ∧
        0 ≤ s ∧ s < n ∧ 0 ≤ t ∧ t < n ∧ 0 ≤ z ∧ z < n

  /-- Let d(x,y) be the number of edges on the unique simple path between nodes x and y in the tree described by edges. The function returns a result r (it does not fail). Let m = len(query). Then len(r)=m, and for every i with 0 <= i < m, writing s=query[i][0], t=query[i][1], z=query[i][2], and a=r[i], we have 0 <= a < n, d(s,a)+d(a,t)=d(s,t), and for every u with 0 <= u < n and d(s,u)+d(u,t)=d(s,t), d(a,z) <= d(u,z).
    Preconditions: 1 <= n <= 1000; len(edges)=n-1; for every i with 0 <= i < len(edges), len(edges[i])=2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; the undirected graph on vertices 0,...,n-1 with an edge between edges[i][0] and edges[i][1] for each i is a tree; 1 <= len(query) <= 1000; for every i with 0 <= i < len(query), len(query[i])=3 and 0 <= query[i][0], query[i][1], query[i][2] < n. -/
  theorem spec_1 (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
      (hlen : (edges.val.length : Int) = n.val - 1)
      (hedges : EdgesValid n.val edges.val)
      (htree : IsTree n.val edges.val)
      (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
      (hquery : QueryValid n.val query.val) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.ClosestNode.closest_node n edges query = Result.ok r ∧
        r.val.length = query.val.length ∧
        ∀ i, i < query.val.length → ∀ (s t z a : Int),
          queryAt query.val i = some (s, t, z) → answerAt r i = some a →
            0 ≤ a ∧ a < n.val ∧ OnPath edges.val s t a ∧
              ∀ u : Int, 0 ≤ u → u < n.val → OnPath edges.val s t u →
                dist edges.val a z ≤ dist edges.val u z := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
        (hlen : (edges.val.length : Int) = n.val - 1)
        (hedges : EdgesValid n.val edges.val)
        (htree : IsTree n.val edges.val)
        (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
        (hquery : QueryValid n.val query.val), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.ClosestNode.closest_node n edges query = Result.ok r ∧
          r.val.length = query.val.length ∧
          ∀ i, i < query.val.length → ∀ (s t z a : Int),
            queryAt query.val i = some (s, t, z) → answerAt r i = some a →
              0 ≤ a ∧ a < n.val ∧ OnPath edges.val s t a ∧
                ∀ u : Int, 0 ≤ u → u < n.val → OnPath edges.val s t u →
                  dist edges.val a z ≤ dist edges.val u z) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (it does not fail).
    Preconditions: 1 <= n <= 1000; len(edges)=n-1; for every i with 0 <= i < len(edges), len(edges[i])=2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; the undirected graph on vertices 0,...,n-1 with an edge between edges[i][0] and edges[i][1] for each i is a tree; 1 <= len(query) <= 1000; for every i with 0 <= i < len(query), len(query[i])=3 and 0 <= query[i][0], query[i][1], query[i][2] < n. -/
  theorem spec_2 (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
      (hlen : (edges.val.length : Int) = n.val - 1)
      (hedges : EdgesValid n.val edges.val)
      (htree : IsTree n.val edges.val)
      (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
      (hquery : QueryValid n.val query.val) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.ClosestNode.closest_node n edges query = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
        (hlen : (edges.val.length : Int) = n.val - 1)
        (hedges : EdgesValid n.val edges.val)
        (htree : IsTree n.val edges.val)
        (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
        (hquery : QueryValid n.val query.val), ∃ r : alloc.vec.Vec Std.I64, Aegis.ClosestNode.closest_node n edges query = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r)=len(query).
    Preconditions: 1 <= n <= 1000; len(edges)=n-1; for every i with 0 <= i < len(edges), len(edges[i])=2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; the undirected graph on vertices 0,...,n-1 with an edge between edges[i][0] and edges[i][1] for each i is a tree; 1 <= len(query) <= 1000; for every i with 0 <= i < len(query), len(query[i])=3 and 0 <= query[i][0], query[i][1], query[i][2] < n. -/
  theorem spec_3 (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
      (hlen : (edges.val.length : Int) = n.val - 1)
      (hedges : EdgesValid n.val edges.val)
      (htree : IsTree n.val edges.val)
      (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
      (hquery : QueryValid n.val query.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.ClosestNode.closest_node n edges query = Result.ok r →
          r.val.length = query.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
        (hlen : (edges.val.length : Int) = n.val - 1)
        (hedges : EdgesValid n.val edges.val)
        (htree : IsTree n.val edges.val)
        (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
        (hquery : QueryValid n.val query.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.ClosestNode.closest_node n edges query = Result.ok r →
            r.val.length = query.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(query), 0 <= r[i] < n.
    Preconditions: 1 <= n <= 1000; len(edges)=n-1; for every i with 0 <= i < len(edges), len(edges[i])=2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; the undirected graph on vertices 0,...,n-1 with an edge between edges[i][0] and edges[i][1] for each i is a tree; 1 <= len(query) <= 1000; for every i with 0 <= i < len(query), len(query[i])=3 and 0 <= query[i][0], query[i][1], query[i][2] < n. -/
  theorem spec_4 (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
      (hlen : (edges.val.length : Int) = n.val - 1)
      (hedges : EdgesValid n.val edges.val)
      (htree : IsTree n.val edges.val)
      (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
      (hquery : QueryValid n.val query.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.ClosestNode.closest_node n edges query = Result.ok r →
          ∀ i, i < query.val.length → ∀ a : Int, answerAt r i = some a → 0 ≤ a ∧ a < n.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
        (hlen : (edges.val.length : Int) = n.val - 1)
        (hedges : EdgesValid n.val edges.val)
        (htree : IsTree n.val edges.val)
        (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
        (hquery : QueryValid n.val query.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.ClosestNode.closest_node n edges query = Result.ok r →
            ∀ i, i < query.val.length → ∀ a : Int, answerAt r i = some a → 0 ≤ a ∧ a < n.val) := by
    sorry

  /-- Let d(x,y) be the number of edges on the unique simple path between nodes x and y in the tree described by edges. Whenever the function returns a result r, for every i with 0 <= i < len(query), writing s=query[i][0], t=query[i][1], and a=r[i], we have d(s,a)+d(a,t)=d(s,t).
    Preconditions: 1 <= n <= 1000; len(edges)=n-1; for every i with 0 <= i < len(edges), len(edges[i])=2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; the undirected graph on vertices 0,...,n-1 with an edge between edges[i][0] and edges[i][1] for each i is a tree; 1 <= len(query) <= 1000; for every i with 0 <= i < len(query), len(query[i])=3 and 0 <= query[i][0], query[i][1], query[i][2] < n. -/
  theorem spec_5 (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
      (hlen : (edges.val.length : Int) = n.val - 1)
      (hedges : EdgesValid n.val edges.val)
      (htree : IsTree n.val edges.val)
      (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
      (hquery : QueryValid n.val query.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.ClosestNode.closest_node n edges query = Result.ok r →
          ∀ i, i < query.val.length → ∀ (s t z a : Int),
            queryAt query.val i = some (s, t, z) → answerAt r i = some a →
              OnPath edges.val s t a := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
        (hlen : (edges.val.length : Int) = n.val - 1)
        (hedges : EdgesValid n.val edges.val)
        (htree : IsTree n.val edges.val)
        (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
        (hquery : QueryValid n.val query.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.ClosestNode.closest_node n edges query = Result.ok r →
            ∀ i, i < query.val.length → ∀ (s t z a : Int),
              queryAt query.val i = some (s, t, z) → answerAt r i = some a →
                OnPath edges.val s t a) := by
    sorry

  /-- Let d(x,y) be the number of edges on the unique simple path between nodes x and y in the tree described by edges. Whenever the function returns a result r, for every i with 0 <= i < len(query), writing s=query[i][0], t=query[i][1], z=query[i][2], and a=r[i], for every u with 0 <= u < n and d(s,u)+d(u,t)=d(s,t), we have d(a,z) <= d(u,z).
    Preconditions: 1 <= n <= 1000; len(edges)=n-1; for every i with 0 <= i < len(edges), len(edges[i])=2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; the undirected graph on vertices 0,...,n-1 with an edge between edges[i][0] and edges[i][1] for each i is a tree; 1 <= len(query) <= 1000; for every i with 0 <= i < len(query), len(query[i])=3 and 0 <= query[i][0], query[i][1], query[i][2] < n. -/
  theorem spec_6 (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
      (hlen : (edges.val.length : Int) = n.val - 1)
      (hedges : EdgesValid n.val edges.val)
      (htree : IsTree n.val edges.val)
      (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
      (hquery : QueryValid n.val query.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.ClosestNode.closest_node n edges query = Result.ok r →
          ∀ i, i < query.val.length → ∀ (s t z a : Int),
            queryAt query.val i = some (s, t, z) → answerAt r i = some a →
              ∀ u : Int, 0 ≤ u → u < n.val → OnPath edges.val s t u →
                dist edges.val a z ≤ dist edges.val u z := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
        (hlen : (edges.val.length : Int) = n.val - 1)
        (hedges : EdgesValid n.val edges.val)
        (htree : IsTree n.val edges.val)
        (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
        (hquery : QueryValid n.val query.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.ClosestNode.closest_node n edges query = Result.ok r →
            ∀ i, i < query.val.length → ∀ (s t z a : Int),
              queryAt query.val i = some (s, t, z) → answerAt r i = some a →
                ∀ u : Int, 0 ≤ u → u < n.val → OnPath edges.val s t u →
                  dist edges.val a z ≤ dist edges.val u z) := by
    sorry

  /-- Let d(x,y) be the number of edges on the unique simple path between nodes x and y in the tree described by edges. Whenever the function returns a result r, for every i with 0 <= i < len(query), writing s=query[i][0], t=query[i][1], z=query[i][2], and a=r[i], we have 2*d(a,z) = d(s,z)+d(t,z)-d(s,t).
    Preconditions: 1 <= n <= 1000; len(edges)=n-1; for every i with 0 <= i < len(edges), len(edges[i])=2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; the undirected graph on vertices 0,...,n-1 with an edge between edges[i][0] and edges[i][1] for each i is a tree; 1 <= len(query) <= 1000; for every i with 0 <= i < len(query), len(query[i])=3 and 0 <= query[i][0], query[i][1], query[i][2] < n. -/
  theorem spec_7 (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
      (hlen : (edges.val.length : Int) = n.val - 1)
      (hedges : EdgesValid n.val edges.val)
      (htree : IsTree n.val edges.val)
      (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
      (hquery : QueryValid n.val query.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.ClosestNode.closest_node n edges query = Result.ok r →
          ∀ i, i < query.val.length → ∀ (s t z a : Int),
            queryAt query.val i = some (s, t, z) → answerAt r i = some a →
              2 * dist edges.val a z = dist edges.val s z + dist edges.val t z - dist edges.val s t := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
        (hlen : (edges.val.length : Int) = n.val - 1)
        (hedges : EdgesValid n.val edges.val)
        (htree : IsTree n.val edges.val)
        (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
        (hquery : QueryValid n.val query.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.ClosestNode.closest_node n edges query = Result.ok r →
            ∀ i, i < query.val.length → ∀ (s t z a : Int),
              queryAt query.val i = some (s, t, z) → answerAt r i = some a →
                2 * dist edges.val a z = dist edges.val s z + dist edges.val t z - dist edges.val s t) := by
    sorry

  /-- Let d(x,y) be the number of edges on the unique simple path between nodes x and y in the tree described by edges. Whenever the function returns a result r, for every i with 0 <= i < len(query), writing s=query[i][0], t=query[i][1], z=query[i][2], and a=r[i], we have 2*d(s,a) = d(s,z)+d(s,t)-d(t,z).
    Preconditions: 1 <= n <= 1000; len(edges)=n-1; for every i with 0 <= i < len(edges), len(edges[i])=2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; the undirected graph on vertices 0,...,n-1 with an edge between edges[i][0] and edges[i][1] for each i is a tree; 1 <= len(query) <= 1000; for every i with 0 <= i < len(query), len(query[i])=3 and 0 <= query[i][0], query[i][1], query[i][2] < n. -/
  theorem spec_8 (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
      (hlen : (edges.val.length : Int) = n.val - 1)
      (hedges : EdgesValid n.val edges.val)
      (htree : IsTree n.val edges.val)
      (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
      (hquery : QueryValid n.val query.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.ClosestNode.closest_node n edges query = Result.ok r →
          ∀ i, i < query.val.length → ∀ (s t z a : Int),
            queryAt query.val i = some (s, t, z) → answerAt r i = some a →
              2 * dist edges.val s a = dist edges.val s z + dist edges.val s t - dist edges.val t z := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
        (hlen : (edges.val.length : Int) = n.val - 1)
        (hedges : EdgesValid n.val edges.val)
        (htree : IsTree n.val edges.val)
        (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
        (hquery : QueryValid n.val query.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.ClosestNode.closest_node n edges query = Result.ok r →
            ∀ i, i < query.val.length → ∀ (s t z a : Int),
              queryAt query.val i = some (s, t, z) → answerAt r i = some a →
                2 * dist edges.val s a = dist edges.val s z + dist edges.val s t - dist edges.val t z) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(query), if query[i][0]=query[i][1] then r[i]=query[i][0].
    Preconditions: 1 <= n <= 1000; len(edges)=n-1; for every i with 0 <= i < len(edges), len(edges[i])=2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; the undirected graph on vertices 0,...,n-1 with an edge between edges[i][0] and edges[i][1] for each i is a tree; 1 <= len(query) <= 1000; for every i with 0 <= i < len(query), len(query[i])=3 and 0 <= query[i][0], query[i][1], query[i][2] < n. -/
  theorem spec_9 (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
      (hlen : (edges.val.length : Int) = n.val - 1)
      (hedges : EdgesValid n.val edges.val)
      (htree : IsTree n.val edges.val)
      (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
      (hquery : QueryValid n.val query.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.ClosestNode.closest_node n edges query = Result.ok r →
          ∀ i, i < query.val.length → ∀ (s t z a : Int),
            queryAt query.val i = some (s, t, z) → answerAt r i = some a → s = t → a = s := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
        (hlen : (edges.val.length : Int) = n.val - 1)
        (hedges : EdgesValid n.val edges.val)
        (htree : IsTree n.val edges.val)
        (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
        (hquery : QueryValid n.val query.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.ClosestNode.closest_node n edges query = Result.ok r →
            ∀ i, i < query.val.length → ∀ (s t z a : Int),
              queryAt query.val i = some (s, t, z) → answerAt r i = some a → s = t → a = s) := by
    sorry

  /-- Let d(x,y) be the number of edges on the unique simple path between nodes x and y in the tree described by edges. Whenever the function returns a result r, for every i with 0 <= i < len(query), writing s=query[i][0], t=query[i][1], z=query[i][2], and a=r[i], if d(s,z)+d(z,t)=d(s,t), then a=z.
    Preconditions: 1 <= n <= 1000; len(edges)=n-1; for every i with 0 <= i < len(edges), len(edges[i])=2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; the undirected graph on vertices 0,...,n-1 with an edge between edges[i][0] and edges[i][1] for each i is a tree; 1 <= len(query) <= 1000; for every i with 0 <= i < len(query), len(query[i])=3 and 0 <= query[i][0], query[i][1], query[i][2] < n. -/
  theorem spec_10 (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
      (hlen : (edges.val.length : Int) = n.val - 1)
      (hedges : EdgesValid n.val edges.val)
      (htree : IsTree n.val edges.val)
      (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
      (hquery : QueryValid n.val query.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.ClosestNode.closest_node n edges query = Result.ok r →
          ∀ i, i < query.val.length → ∀ (s t z a : Int),
            queryAt query.val i = some (s, t, z) → answerAt r i = some a →
              OnPath edges.val s t z → a = z := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
        (hlen : (edges.val.length : Int) = n.val - 1)
        (hedges : EdgesValid n.val edges.val)
        (htree : IsTree n.val edges.val)
        (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
        (hquery : QueryValid n.val query.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.ClosestNode.closest_node n edges query = Result.ok r →
            ∀ i, i < query.val.length → ∀ (s t z a : Int),
              queryAt query.val i = some (s, t, z) → answerAt r i = some a →
                OnPath edges.val s t z → a = z) := by
    sorry

  /-- Let d(x,y) be the number of edges on the unique simple path between nodes x and y in the tree described by edges. Whenever the function returns a result r, for every i with 0 <= i < len(query), writing s=query[i][0], t=query[i][1], z=query[i][2], and a=r[i], if d(s,t)=1, then a=s if d(z,s)<d(z,t), and a=t if d(z,t)<d(z,s).
    Preconditions: 1 <= n <= 1000; len(edges)=n-1; for every i with 0 <= i < len(edges), len(edges[i])=2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; the undirected graph on vertices 0,...,n-1 with an edge between edges[i][0] and edges[i][1] for each i is a tree; 1 <= len(query) <= 1000; for every i with 0 <= i < len(query), len(query[i])=3 and 0 <= query[i][0], query[i][1], query[i][2] < n. -/
  theorem spec_11 (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
      (hlen : (edges.val.length : Int) = n.val - 1)
      (hedges : EdgesValid n.val edges.val)
      (htree : IsTree n.val edges.val)
      (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
      (hquery : QueryValid n.val query.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.ClosestNode.closest_node n edges query = Result.ok r →
          ∀ i, i < query.val.length → ∀ (s t z a : Int),
            queryAt query.val i = some (s, t, z) → answerAt r i = some a →
              dist edges.val s t = 1 →
                (dist edges.val z s < dist edges.val z t → a = s) ∧
                (dist edges.val z t < dist edges.val z s → a = t) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
        (hlen : (edges.val.length : Int) = n.val - 1)
        (hedges : EdgesValid n.val edges.val)
        (htree : IsTree n.val edges.val)
        (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
        (hquery : QueryValid n.val query.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.ClosestNode.closest_node n edges query = Result.ok r →
            ∀ i, i < query.val.length → ∀ (s t z a : Int),
              queryAt query.val i = some (s, t, z) → answerAt r i = some a →
                dist edges.val s t = 1 →
                  (dist edges.val z s < dist edges.val z t → a = s) ∧
                  (dist edges.val z t < dist edges.val z s → a = t)) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i,j < len(query), if query[j][0]=query[i][1], query[j][1]=query[i][0], and query[j][2]=query[i][2], then r[i]=r[j].
    Preconditions: 1 <= n <= 1000; len(edges)=n-1; for every i with 0 <= i < len(edges), len(edges[i])=2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; the undirected graph on vertices 0,...,n-1 with an edge between edges[i][0] and edges[i][1] for each i is a tree; 1 <= len(query) <= 1000; for every i with 0 <= i < len(query), len(query[i])=3 and 0 <= query[i][0], query[i][1], query[i][2] < n. -/
  theorem spec_12 (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
      (hlen : (edges.val.length : Int) = n.val - 1)
      (hedges : EdgesValid n.val edges.val)
      (htree : IsTree n.val edges.val)
      (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
      (hquery : QueryValid n.val query.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.ClosestNode.closest_node n edges query = Result.ok r →
          ∀ i j : Nat, i < query.val.length → j < query.val.length →
            ∀ (si ti zi sj tj zj ai aj : Int),
              queryAt query.val i = some (si, ti, zi) →
              queryAt query.val j = some (sj, tj, zj) →
              answerAt r i = some ai → answerAt r j = some aj →
              si = tj → ti = sj → zi = zj → ai = aj := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (edges query : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
        (hlen : (edges.val.length : Int) = n.val - 1)
        (hedges : EdgesValid n.val edges.val)
        (htree : IsTree n.val edges.val)
        (hq1 : 1 ≤ query.val.length) (hq2 : query.val.length ≤ 1000)
        (hquery : QueryValid n.val query.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.ClosestNode.closest_node n edges query = Result.ok r →
            ∀ i j : Nat, i < query.val.length → j < query.val.length →
              ∀ (si ti zi sj tj zj ai aj : Int),
                queryAt query.val i = some (si, ti, zi) →
                queryAt query.val j = some (sj, tj, zj) →
                answerAt r i = some ai → answerAt r j = some aj →
                si = tj → ti = sj → zi = zj → ai = aj) := by
    sorry

  end AegisSpec.ClosestNode
