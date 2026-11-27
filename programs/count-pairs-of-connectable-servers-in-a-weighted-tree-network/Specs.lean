import Aegis.CountPairsOfConnectableServers.Code.Funs

/-!
# Specifications of `Aegis.CountPairsOfConnectableServers.count_pairs_of_connectable_servers`

LeetCode problem `count-pairs-of-connectable-servers-in-a-weighted-tree-network`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  noncomputable section

  attribute [local instance] Classical.propDecidable

  namespace AegisSpec.CountPairsOfConnectableServers

  def countPairs (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64) :
      Result (alloc.vec.Vec I64) :=
    _root_.Aegis.CountPairsOfConnectableServers.count_pairs_of_connectable_servers edges
      signalSpeed

  def rows (edges : Slice (alloc.vec.Vec I64)) : List (List Int) :=
    edges.val.map (fun v => v.val.map (fun x => x.val))

  def numVertices (edges : Slice (alloc.vec.Vec I64)) : Nat :=
    edges.val.length + 1

  def rowA (row : List Int) : Nat := (row.getD 0 0).toNat

  def rowB (row : List Int) : Nat := (row.getD 1 0).toNat

  def rowW (row : List Int) : Int := row.getD 2 0

  def arrGet (r : alloc.vec.Vec I64) (c : Nat) : Int :=
    match r.val[c]? with
    | some x => x.val
    | none => 0

  def EdgesWellFormed (edges : Slice (alloc.vec.Vec I64)) : Prop :=
    ∀ row ∈ rows edges, ∃ (a b : Nat) (w : Int),
      row = [(a : Int), (b : Int), w] ∧
      a < numVertices edges ∧ b < numVertices edges ∧ a ≠ b ∧ 1 ≤ w ∧ w ≤ 1000000

  def IsEdge (edges : Slice (alloc.vec.Vec I64)) (u v : Nat) (w : Int) : Prop :=
    ∃ row ∈ rows edges,
      ((rowA row = u ∧ rowB row = v) ∨ (rowA row = v ∧ rowB row = u)) ∧ rowW row = w

  def Adj (edges : Slice (alloc.vec.Vec I64)) (u v : Nat) : Prop :=
    ∃ w, IsEdge edges u v w

  def edgeWeight (edges : Slice (alloc.vec.Vec I64)) (u v : Nat) : Int :=
    ((rows edges).filterMap (fun row =>
      if rowA row = u ∧ rowB row = v then some (rowW row)
      else if rowA row = v ∧ rowB row = u then some (rowW row)
      else none)).headD 0

  def IsWalk (edges : Slice (alloc.vec.Vec I64)) (vs : List Nat) : Prop :=
    ∀ i, i + 1 < vs.length → Adj edges (vs.getD i 0) (vs.getD (i + 1) 0)

  def IsSimplePath (edges : Slice (alloc.vec.Vec I64)) (x y : Nat) (vs : List Nat) : Prop :=
    vs.head? = some x ∧ vs.getLast? = some y ∧ vs.Nodup ∧ IsWalk edges vs

  def pathWeight (edges : Slice (alloc.vec.Vec I64)) (vs : List Nat) : Int :=
    ((vs.zip vs.tail).map (fun p : Nat × Nat => edgeWeight edges p.1 p.2)).sum

  def pathEdges (vs : List Nat) : Finset (Nat × Nat) :=
    ((vs.zip vs.tail).map (fun p : Nat × Nat => if p.1 ≤ p.2 then (p.1, p.2) else (p.2, p.1))).toFinset

  def OnPath (edges : Slice (alloc.vec.Vec I64)) (x y : Nat) (e : Nat × Nat) : Prop :=
    ∃ vs, IsSimplePath edges x y vs ∧ e ∈ pathEdges vs

  def PathEdgeDisjoint (edges : Slice (alloc.vec.Vec I64)) (c a b : Nat) : Prop :=
    ∀ e, OnPath edges c a e → ¬ OnPath edges c b e

  def Connected (edges : Slice (alloc.vec.Vec I64)) : Prop :=
    ∀ u v, u < numVertices edges → v < numVertices edges →
      ∃ vs, vs.head? = some u ∧ vs.getLast? = some v ∧ IsWalk edges vs

  def Acyclic (edges : Slice (alloc.vec.Vec I64)) : Prop :=
    ¬ ∃ (vs : List Nat) (w : Int), 2 ≤ vs.length ∧ vs.Nodup ∧ IsWalk edges vs ∧
        ∃ u v, vs.head? = some u ∧ vs.getLast? = some v ∧ u ≠ v ∧ IsEdge edges v u w

  def NoParallelEdges (edges : Slice (alloc.vec.Vec I64)) : Prop :=
    ∀ row₁ ∈ rows edges, ∀ row₂ ∈ rows edges,
      ((rowA row₁ = rowA row₂ ∧ rowB row₁ = rowB row₂) ∨
        (rowA row₁ = rowB row₂ ∧ rowB row₁ = rowA row₂)) → rowW row₁ = rowW row₂

  def IsTree (edges : Slice (alloc.vec.Vec I64)) : Prop :=
    Connected edges ∧ Acyclic edges ∧ NoParallelEdges edges

  def InComponentAfterDeleting (edges : Slice (alloc.vec.Vec I64)) (c u y : Nat) : Prop :=
    ∃ vs, vs.head? = some u ∧ vs.getLast? = some y ∧ vs.Nodup ∧ c ∉ vs ∧ IsWalk edges vs

  def nbrs (edges : Slice (alloc.vec.Vec I64)) (u : Nat) : List (Nat × Int) :=
    (rows edges).filterMap (fun row =>
      if rowA row = u then some (rowB row, rowW row)
      else if rowB row = u then some (rowA row, rowW row)
      else none)

  def dfsVisit (edges : Slice (alloc.vec.Vec I64)) :
      Nat → List (Nat × Int) → List (Nat × Int) → List (Nat × Int)
    | 0, seen, _ => seen
    | _ + 1, seen, [] => seen
    | fuel + 1, seen, (u, d) :: rest =>
        let fresh := (nbrs edges u).filterMap (fun p =>
          if (seen.map Prod.fst).contains p.1 then none else some (p.1, d + p.2))
        dfsVisit edges fuel ((u, d) :: seen) (fresh ++ rest)

  def dist (edges : Slice (alloc.vec.Vec I64)) (x y : Nat) : Int :=
    ((dfsVisit edges (numVertices edges) [] [(x, 0)]).lookup y).getD 0

  def verticesOf (edges : Slice (alloc.vec.Vec I64)) : Finset Nat :=
    Finset.range (numVertices edges)

  def connectablePairs (edges : Slice (alloc.vec.Vec I64)) (σ : Int) (c : Nat) :
      Finset (Nat × Nat) :=
    ((verticesOf edges).product (verticesOf edges)).filter (fun p =>
      p.1 < p.2 ∧ p.1 ≠ c ∧ p.2 ≠ c ∧ σ ∣ dist edges c p.1 ∧ σ ∣ dist edges c p.2 ∧
        PathEdgeDisjoint edges c p.1 p.2)

  def connectableTriples (edges : Slice (alloc.vec.Vec I64)) (σ : Int) :
      Finset (Nat × Nat × Nat) :=
    ((verticesOf edges).product ((verticesOf edges).product (verticesOf edges))).filter
      (fun t => t.1 < t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
        σ ∣ dist edges t.2.2 t.1 ∧ σ ∣ dist edges t.2.2 t.2.1 ∧
        PathEdgeDisjoint edges t.2.2 t.1 t.2.1)

  def separatedPairs (edges : Slice (alloc.vec.Vec I64)) (c : Nat) : Finset (Nat × Nat) :=
    ((verticesOf edges).product (verticesOf edges)).filter (fun p =>
      p.1 < p.2 ∧ p.1 ≠ c ∧ p.2 ≠ c ∧ ¬ InComponentAfterDeleting edges c p.1 p.2)

  def neighborsOf (edges : Slice (alloc.vec.Vec I64)) (c : Nat) : Finset Nat :=
    (verticesOf edges).filter (fun u => Adj edges c u)

  def branchCount (edges : Slice (alloc.vec.Vec I64)) (σ : Int) (c u : Nat) : Nat :=
    ((verticesOf edges).filter (fun y =>
      y ≠ c ∧ Adj edges c u ∧ InComponentAfterDeleting edges c u y ∧
        σ ∣ dist edges c y)).card

  def branchPairSum (edges : Slice (alloc.vec.Vec I64)) (σ : Int) (c : Nat) : Nat :=
    ∑ u ∈ neighborsOf edges c, ∑ v ∈ neighborsOf edges c,
      if u < v then branchCount edges σ c u * branchCount edges σ c v else 0

  def divisDistCount (edges : Slice (alloc.vec.Vec I64)) (σ : Int) (c : Nat) : Nat :=
    ((verticesOf edges).filter (fun y => y ≠ c ∧ σ ∣ dist edges c y)).card

  def Precondition (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64) : Prop :=
    2 ≤ numVertices edges ∧ numVertices edges ≤ 1000 ∧ EdgesWellFormed edges ∧ IsTree edges ∧
      1 ≤ signalSpeed.val ∧ signalSpeed.val ≤ 1000000

  /-- Whenever the function returns a result r, for every integer c with 0 <= c < n, r[c] is the number of unordered pairs {a,b} of vertices such that 0 <= a < b < n, a != c, b != c, dist(c,a) is divisible by signalSpeed, dist(c,b) is divisible by signalSpeed, and the simple paths from c to a and from c to b have no edge in common. Here dist(x,y) is the sum of the weights of the edges on the unique simple path between x and y in the tree formed by edges.
    Preconditions: Let n = len(edges)+1. The input satisfies: 2 <= n <= 1000; len(edges) = n-1; every edges[i] has length 3; writing edges[i] = [a_i,b_i,w_i], we have 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 10^6; the undirected graph on vertices 0,...,n-1 with one edge {a_i,b_i} of weight w_i for each i is connected and acyclic (so it is a tree); and 1 <= signalSpeed <= 10^6. -/
  theorem spec_1 (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
      (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
      (hr : countPairs edges signalSpeed = ok r) :
      ∀ c, c < numVertices edges →
        arrGet r c = ((connectablePairs edges signalSpeed.val c).card : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
        (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
        (hr : countPairs edges signalSpeed = ok r), ∀ c, c < numVertices edges →
          arrGet r c = ((connectablePairs edges signalSpeed.val c).card : Int)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, overflow, or access an out-of-bounds index) for every input satisfying the preconditions.
    Preconditions: Let n = len(edges)+1. The input satisfies: 2 <= n <= 1000; len(edges) = n-1; every edges[i] has length 3; writing edges[i] = [a_i,b_i,w_i], we have 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 10^6; the undirected graph on vertices 0,...,n-1 with one edge {a_i,b_i} of weight w_i for each i is connected and acyclic (so it is a tree); and 1 <= signalSpeed <= 10^6. -/
  theorem spec_2 (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
      (hpre : Precondition edges signalSpeed) :
      ∃ r : alloc.vec.Vec I64, countPairs edges signalSpeed = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
        (hpre : Precondition edges signalSpeed), ∃ r : alloc.vec.Vec I64, countPairs edges signalSpeed = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(edges)+1.
    Preconditions: Let n = len(edges)+1. The input satisfies: 2 <= n <= 1000; len(edges) = n-1; every edges[i] has length 3; writing edges[i] = [a_i,b_i,w_i], we have 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 10^6; the undirected graph on vertices 0,...,n-1 with one edge {a_i,b_i} of weight w_i for each i is connected and acyclic (so it is a tree); and 1 <= signalSpeed <= 10^6. -/
  theorem spec_3 (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
      (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
      (hr : countPairs edges signalSpeed = ok r) :
      r.val.length = numVertices edges := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
        (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
        (hr : countPairs edges signalSpeed = ok r), r.val.length = numVertices edges) := by
    sorry

  /-- Whenever the function returns a result r, for every integer i with 0 <= i < len(r), 0 <= r[i].
    Preconditions: Let n = len(edges)+1. The input satisfies: 2 <= n <= 1000; len(edges) = n-1; every edges[i] has length 3; writing edges[i] = [a_i,b_i,w_i], we have 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 10^6; the undirected graph on vertices 0,...,n-1 with one edge {a_i,b_i} of weight w_i for each i is connected and acyclic (so it is a tree); and 1 <= signalSpeed <= 10^6. -/
  theorem spec_4 (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
      (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
      (hr : countPairs edges signalSpeed = ok r) :
      ∀ i, i < r.val.length → 0 ≤ arrGet r i := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
        (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
        (hr : countPairs edges signalSpeed = ok r), ∀ i, i < r.val.length → 0 ≤ arrGet r i) := by
    sorry

  /-- Whenever the function returns a result r, for every integer c with 0 <= c < n, r[c] <= ((n-1)*(n-2))/2. This upper bound is the number of unordered pairs of vertices distinct from c.
    Preconditions: Let n = len(edges)+1. The input satisfies: 2 <= n <= 1000; len(edges) = n-1; every edges[i] has length 3; writing edges[i] = [a_i,b_i,w_i], we have 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 10^6; the undirected graph on vertices 0,...,n-1 with one edge {a_i,b_i} of weight w_i for each i is connected and acyclic (so it is a tree); and 1 <= signalSpeed <= 10^6. -/
  theorem spec_5 (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
      (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
      (hr : countPairs edges signalSpeed = ok r) :
      ∀ c, c < numVertices edges →
        arrGet r c ≤ (((numVertices edges - 1) * (numVertices edges - 2)) / 2 : Nat) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
        (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
        (hr : countPairs edges signalSpeed = ok r), ∀ c, c < numVertices edges →
          arrGet r c ≤ (((numVertices edges - 1) * (numVertices edges - 2)) / 2 : Nat)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer c with 0 <= c < n, if c has at most one neighbor in the tree, then r[c] = 0.
    Preconditions: Let n = len(edges)+1. The input satisfies: 2 <= n <= 1000; len(edges) = n-1; every edges[i] has length 3; writing edges[i] = [a_i,b_i,w_i], we have 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 10^6; the undirected graph on vertices 0,...,n-1 with one edge {a_i,b_i} of weight w_i for each i is connected and acyclic (so it is a tree); and 1 <= signalSpeed <= 10^6. -/
  theorem spec_6 (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
      (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
      (hr : countPairs edges signalSpeed = ok r) :
      ∀ c, c < numVertices edges → (neighborsOf edges c).card ≤ 1 → arrGet r c = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
        (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
        (hr : countPairs edges signalSpeed = ok r), ∀ c, c < numVertices edges → (neighborsOf edges c).card ≤ 1 → arrGet r c = 0) := by
    sorry

  /-- Whenever the function returns a result r, for every integer c with 0 <= c < n, let A(c,u) be the number of vertices y such that y != c, the first edge on the path from c to y is the edge from c to its neighbor u, and dist(c,y) is divisible by signalSpeed. Then r[c] = sum over all unordered pairs {u,v} of distinct neighbors of c of A(c,u)*A(c,v).
    Preconditions: Let n = len(edges)+1. The input satisfies: 2 <= n <= 1000; len(edges) = n-1; every edges[i] has length 3; writing edges[i] = [a_i,b_i,w_i], we have 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 10^6; the undirected graph on vertices 0,...,n-1 with one edge {a_i,b_i} of weight w_i for each i is connected and acyclic (so it is a tree); and 1 <= signalSpeed <= 10^6. -/
  theorem spec_7 (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
      (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
      (hr : countPairs edges signalSpeed = ok r) :
      ∀ c, c < numVertices edges →
        arrGet r c = (branchPairSum edges signalSpeed.val c : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
        (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
        (hr : countPairs edges signalSpeed = ok r), ∀ c, c < numVertices edges →
          arrGet r c = (branchPairSum edges signalSpeed.val c : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer c with 0 <= c < n, r[c] > 0 if and only if there exist two distinct neighbors u and v of c such that the component containing u after deleting c contains a vertex a != c with dist(c,a) divisible by signalSpeed, and the component containing v after deleting c contains a vertex b != c with dist(c,b) divisible by signalSpeed.
    Preconditions: Let n = len(edges)+1. The input satisfies: 2 <= n <= 1000; len(edges) = n-1; every edges[i] has length 3; writing edges[i] = [a_i,b_i,w_i], we have 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 10^6; the undirected graph on vertices 0,...,n-1 with one edge {a_i,b_i} of weight w_i for each i is connected and acyclic (so it is a tree); and 1 <= signalSpeed <= 10^6. -/
  theorem spec_8 (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
      (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
      (hr : countPairs edges signalSpeed = ok r) :
      ∀ c, c < numVertices edges →
        0 < arrGet r c ↔
          ∃ u v, u ≠ v ∧ Adj edges c u ∧ Adj edges c v ∧
            (∃ a, a ≠ c ∧ InComponentAfterDeleting edges c u a ∧
              signalSpeed.val ∣ dist edges c a) ∧
            (∃ b, b ≠ c ∧ InComponentAfterDeleting edges c v b ∧
              signalSpeed.val ∣ dist edges c b) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
        (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
        (hr : countPairs edges signalSpeed = ok r), ∀ c, c < numVertices edges →
          0 < arrGet r c ↔
            ∃ u v, u ≠ v ∧ Adj edges c u ∧ Adj edges c v ∧
              (∃ a, a ≠ c ∧ InComponentAfterDeleting edges c u a ∧
                signalSpeed.val ∣ dist edges c a) ∧
              (∃ b, b ≠ c ∧ InComponentAfterDeleting edges c v b ∧
                signalSpeed.val ∣ dist edges c b)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer c with 0 <= c < n, let Q(c) be the number of vertices y != c with dist(c,y) divisible by signalSpeed. Then r[c] <= Q(c)*(Q(c)-1)/2.
    Preconditions: Let n = len(edges)+1. The input satisfies: 2 <= n <= 1000; len(edges) = n-1; every edges[i] has length 3; writing edges[i] = [a_i,b_i,w_i], we have 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 10^6; the undirected graph on vertices 0,...,n-1 with one edge {a_i,b_i} of weight w_i for each i is connected and acyclic (so it is a tree); and 1 <= signalSpeed <= 10^6. -/
  theorem spec_9 (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
      (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
      (hr : countPairs edges signalSpeed = ok r) :
      ∀ c, c < numVertices edges →
        arrGet r c ≤
          ((divisDistCount edges signalSpeed.val c * (divisDistCount edges signalSpeed.val c - 1)) / 2
            : Nat) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
        (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
        (hr : countPairs edges signalSpeed = ok r), ∀ c, c < numVertices edges →
          arrGet r c ≤
            ((divisDistCount edges signalSpeed.val c * (divisDistCount edges signalSpeed.val c - 1)) / 2
              : Nat)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer c with 0 <= c < n, if there are fewer than two vertices y != c with dist(c,y) divisible by signalSpeed, then r[c] = 0.
    Preconditions: Let n = len(edges)+1. The input satisfies: 2 <= n <= 1000; len(edges) = n-1; every edges[i] has length 3; writing edges[i] = [a_i,b_i,w_i], we have 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 10^6; the undirected graph on vertices 0,...,n-1 with one edge {a_i,b_i} of weight w_i for each i is connected and acyclic (so it is a tree); and 1 <= signalSpeed <= 10^6. -/
  theorem spec_10 (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
      (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
      (hr : countPairs edges signalSpeed = ok r) :
      ∀ c, c < numVertices edges → divisDistCount edges signalSpeed.val c < 2 → arrGet r c = 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
        (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
        (hr : countPairs edges signalSpeed = ok r), ∀ c, c < numVertices edges → divisDistCount edges signalSpeed.val c < 2 → arrGet r c = 0) := by
    sorry

  /-- Whenever the function returns a result r, if signalSpeed divides every edge weight w_i, then for every integer c with 0 <= c < n, r[c] is the number of unordered pairs {a,b} with 0 <= a < b < n, a != c, b != c, such that a and b lie in two different connected components of the tree after deleting c.
    Preconditions: Let n = len(edges)+1. The input satisfies: 2 <= n <= 1000; len(edges) = n-1; every edges[i] has length 3; writing edges[i] = [a_i,b_i,w_i], we have 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 10^6; the undirected graph on vertices 0,...,n-1 with one edge {a_i,b_i} of weight w_i for each i is connected and acyclic (so it is a tree); and 1 <= signalSpeed <= 10^6. -/
  theorem spec_11 (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
      (hpre : Precondition edges signalSpeed)
      (hdiv : ∀ row ∈ rows edges, signalSpeed.val ∣ rowW row) {r : alloc.vec.Vec I64}
      (hr : countPairs edges signalSpeed = ok r) :
      ∀ c, c < numVertices edges →
        arrGet r c = ((separatedPairs edges c).card : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
        (hpre : Precondition edges signalSpeed)
        (hdiv : ∀ row ∈ rows edges, signalSpeed.val ∣ rowW row) {r : alloc.vec.Vec I64}
        (hr : countPairs edges signalSpeed = ok r), ∀ c, c < numVertices edges →
          arrGet r c = ((separatedPairs edges c).card : Int)) := by
    sorry

  /-- Whenever the function returns a result r on (edges,signalSpeed) and a result r2 on (edges2,signalSpeed), we have r = r2.
    Preconditions: Let n = len(edges)+1. The input (edges,signalSpeed) satisfies: 2 <= n <= 1000; len(edges) = n-1; every edges[i] has length 3; writing edges[i] = [a_i,b_i,w_i], we have 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 10^6; the undirected graph on vertices 0,...,n-1 with one edge {a_i,b_i} of weight w_i for each i is connected and acyclic (so it is a tree); and 1 <= signalSpeed <= 10^6. Let edges2 be any permutation of the slice edges such that, with the same signalSpeed, edges2 also satisfies the same conditions. -/
  theorem spec_12 (edges edges2 : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
      (hpre : Precondition edges signalSpeed) (hpre2 : Precondition edges2 signalSpeed)
      (hperm : edges2.val.Perm edges.val) {r r2 : alloc.vec.Vec I64}
      (hr : countPairs edges signalSpeed = ok r)
      (hr2 : countPairs edges2 signalSpeed = ok r2) :
      r.val = r2.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (edges edges2 : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
        (hpre : Precondition edges signalSpeed) (hpre2 : Precondition edges2 signalSpeed)
        (hperm : edges2.val.Perm edges.val) {r r2 : alloc.vec.Vec I64}
        (hr : countPairs edges signalSpeed = ok r)
        (hr2 : countPairs edges2 signalSpeed = ok r2), r.val = r2.val) := by
    sorry

  /-- Whenever the function returns a result r, the sum of r[c] over all integers c with 0 <= c < n equals the number of triples (a,b,c) of integers such that 0 <= a < b < n, 0 <= c < n, a != c, b != c, dist(c,a) is divisible by signalSpeed, dist(c,b) is divisible by signalSpeed, and the simple paths from c to a and from c to b have no edge in common.
    Preconditions: Let n = len(edges)+1. The input satisfies: 2 <= n <= 1000; len(edges) = n-1; every edges[i] has length 3; writing edges[i] = [a_i,b_i,w_i], we have 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 10^6; the undirected graph on vertices 0,...,n-1 with one edge {a_i,b_i} of weight w_i for each i is connected and acyclic (so it is a tree); and 1 <= signalSpeed <= 10^6. -/
  theorem spec_13 (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
      (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
      (hr : countPairs edges signalSpeed = ok r) :
      (∑ c ∈ Finset.range (numVertices edges), arrGet r c) =
        ((connectableTriples edges signalSpeed.val).card : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (signalSpeed : I64)
        (hpre : Precondition edges signalSpeed) {r : alloc.vec.Vec I64}
        (hr : countPairs edges signalSpeed = ok r), (∑ c ∈ Finset.range (numVertices edges), arrGet r c) =
          ((connectableTriples edges signalSpeed.val).card : Int)) := by
    sorry

  /-- Whenever the function returns a result r on (edges,S) and a result r2 on (edges,T), for every integer c with 0 <= c < n, we have r2[c] <= r[c].
    Preconditions: Let n = len(edges)+1. The input (edges,signalSpeed) satisfies: 2 <= n <= 1000; len(edges) = n-1; every edges[i] has length 3; writing edges[i] = [a_i,b_i,w_i], we have 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 10^6; the undirected graph on vertices 0,...,n-1 with one edge {a_i,b_i} of weight w_i for each i is connected and acyclic; and 1 <= signalSpeed <= 10^6. Let S and T be integers with 1 <= S <= 10^6, 1 <= T <= 10^6, and S divides T. Let r be the result on (edges,S) and r2 the result on (edges,T). -/
  theorem spec_14 (edges : Slice (alloc.vec.Vec I64)) (S T : I64)
      (hpreS : Precondition edges S) (hpreT : Precondition edges T)
      (hdvd : S.val ∣ T.val) {r r2 : alloc.vec.Vec I64}
      (hr : countPairs edges S = ok r) (hr2 : countPairs edges T = ok r2) :
      ∀ c, c < numVertices edges → arrGet r2 c ≤ arrGet r c := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (S T : I64)
        (hpreS : Precondition edges S) (hpreT : Precondition edges T)
        (hdvd : S.val ∣ T.val) {r r2 : alloc.vec.Vec I64}
        (hr : countPairs edges S = ok r) (hr2 : countPairs edges T = ok r2), ∀ c, c < numVertices edges → arrGet r2 c ≤ arrGet r c) := by
    sorry

  end AegisSpec.CountPairsOfConnectableServers
