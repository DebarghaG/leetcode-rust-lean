import Aegis.ShortestPathWithHops.Code.Funs

/-!
# Specifications of `Aegis.ShortestPathWithHops.shortest_path_with_hops`

LeetCode problem `find-shortest-path-with-k-hops`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ShortestPathWithHops

namespace AegisSpec.ShortestPathWithHops

structure Edge where

  u : ℤ

  v : ℤ

  w : ℤ

def asEdge (e : alloc.vec.Vec Std.I64) : Option Edge :=
  match e.val with
  | [u, v, w] => some ⟨u.val, v.val, w.val⟩
  | _ => none

def RepresentsEdges (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge) : Prop :=
  edges.val.map asEdge = es.map some

def HasEdge (es : List Edge) (x y : ℤ) : Prop :=
  ∃ t ∈ es, (t.u = x ∧ t.v = y) ∨ (t.u = y ∧ t.v = x)

def edgeWeight (es : List Edge) (x y : ℤ) : ℤ :=
  match es with
  | [] => 0
  | t :: ts => if (t.u = x ∧ t.v = y) ∨ (t.u = y ∧ t.v = x) then t.w else edgeWeight ts x y

def SimplePath (es : List Edge) (s d : ℤ) (vs : List ℤ) : Prop :=
  2 ≤ vs.length ∧ vs.head? = some s ∧ vs.getLast? = some d ∧ vs.Nodup ∧
    ∀ p ∈ vs.zip vs.tail, HasEdge es p.1 p.2

def pathWeights (es : List Edge) (vs : List ℤ) : List ℤ :=
  (vs.zip vs.tail).map (fun p => edgeWeight es p.1 p.2)

def pathWeight (es : List Edge) (vs : List ℤ) : ℤ := (pathWeights es vs).sum

def insertDesc (x : ℤ) : List ℤ → List ℤ
  | [] => [x]
  | y :: ys => if x ≥ y then x :: y :: ys else y :: insertDesc x ys

def sortDesc : List ℤ → List ℤ
  | [] => []
  | x :: xs => insertDesc x (sortDesc xs)

def topKSum (ws : List ℤ) (k : ℕ) : ℤ := ((sortDesc ws).take k).sum

def SubWeights (rem ws : List ℤ) : Prop := ∃ rest : List ℤ, ws.Perm (rem ++ rest)

def IsHopsOptimum (es : List Edge) (s d : ℤ) (k : ℕ) (r : ℤ) : Prop :=
  (∃ vs : List ℤ, SimplePath es s d vs ∧
      pathWeight es vs - topKSum (pathWeights es vs) k = r) ∧
    ∀ vs : List ℤ, SimplePath es s d vs →
      r ≤ pathWeight es vs - topKSum (pathWeights es vs) k

def IsShortestDistance (es : List Edge) (s d : ℤ) (D : ℤ) : Prop :=
  (∃ vs : List ℤ, SimplePath es s d vs ∧ pathWeight es vs = D) ∧
    ∀ vs : List ℤ, SimplePath es s d vs → D ≤ pathWeight es vs

def GraphConstraints (n : ℤ) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge) : Prop :=
  2 ≤ n ∧ n ≤ 500 ∧
    RepresentsEdges edges es ∧
    (∀ t ∈ es,
      0 ≤ t.u ∧ t.u < n ∧ 0 ≤ t.v ∧ t.v < n ∧ t.u ≠ t.v ∧ 1 ≤ t.w ∧ t.w ≤ 1000000) ∧
    (∀ t₁ ∈ es, ∀ t₂ ∈ es,
      ((t₁.u = t₂.u ∧ t₁.v = t₂.v) ∨ (t₁.u = t₂.v ∧ t₁.v = t₂.u)) → t₁ = t₂) ∧
    (∀ x : ℤ, 0 ≤ x → x < n → Relation.ReflTransGen (HasEdge es) 0 x) ∧
    n - 1 ≤ (es.length : ℤ) ∧ (es.length : ℤ) ≤ min 10000 (n * (n - 1) / 2)

def EndpointsConstraints (n s d : ℤ) : Prop :=
  0 ≤ s ∧ s < n ∧ 0 ≤ d ∧ d < n ∧ s ≠ d

def HopsConstraints (n k : ℤ) : Prop :=
  0 ≤ k ∧ k ≤ n - 1

def IsBijectionOnRange (n : ℤ) (π : ℤ → ℤ) : Prop :=
  (∀ x : ℤ, 0 ≤ x → x < n → 0 ≤ π x ∧ π x < n) ∧
    ∀ x y : ℤ, 0 ≤ x → x < n → 0 ≤ y → y < n → π x = π y → x = y

def IsEdgeRenaming (π : ℤ → ℤ) (es es' : List Edge) : Prop :=
  es' = es.map (fun t => ⟨π t.u, π t.v, t.w⟩)

/-- Whenever the function returns a result r, r is equal to the minimum, over all simple paths P = (v0,...,vm) from s to d in the undirected graph represented by edges (so v0 = s, vm = d, the vi are pairwise distinct, and m >= 1), of the quantity sum_{i=1..m} w(v_{i-1},v_i) minus the sum of the min(k,m) largest numbers among the m edge weights w(v_0,v_1),...,w(v_{m-1},v_m). Here w(x,y) is the weight of the unique edge joining x and y.
  Preconditions: n, edges, s, d, k satisfy the problem constraints: 2 <= n <= 500; every entry of edges is a triple [u,v,w] with 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; no unordered pair {u,v} occurs in two different entries of edges; the undirected graph on nodes 0,...,n-1 with these edges is connected; n-1 <= len(edges) <= min(10^4, n*(n-1)/2); 0 <= s < n; 0 <= d < n; s != d; 0 <= k <= n-1. -/
theorem spec_1 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk : HopsConstraints n.val k.val) :
    ∀ r : Std.I64, shortest_path_with_hops n edges s d k = ok r →
      IsHopsOptimum es s.val d.val k.val.toNat r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk : HopsConstraints n.val k.val), ∀ r : Std.I64, shortest_path_with_hops n edges s d k = ok r →
      IsHopsOptimum es s.val d.val k.val.toNat r.val) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or get stuck) for every input satisfying the preconditions.
  Preconditions: n, edges, s, d, k satisfy the problem constraints: 2 <= n <= 500; every entry of edges is a triple [u,v,w] with 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; no unordered pair {u,v} occurs in two different entries of edges; the undirected graph on nodes 0,...,n-1 with these edges is connected; n-1 <= len(edges) <= min(10^4, n*(n-1)/2); 0 <= s < n; 0 <= d < n; s != d; 0 <= k <= n-1. -/
theorem spec_2 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk : HopsConstraints n.val k.val) :
    ∃ r : Std.I64, shortest_path_with_hops n edges s d k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk : HopsConstraints n.val k.val), ∃ r : Std.I64, shortest_path_with_hops n edges s d k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: n, edges, s, d, k satisfy the problem constraints: 2 <= n <= 500; every entry of edges is a triple [u,v,w] with 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; no unordered pair {u,v} occurs in two different entries of edges; the undirected graph on nodes 0,...,n-1 with these edges is connected; n-1 <= len(edges) <= min(10^4, n*(n-1)/2); 0 <= s < n; 0 <= d < n; s != d; 0 <= k <= n-1. -/
theorem spec_3 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk : HopsConstraints n.val k.val) :
    ∀ r : Std.I64, shortest_path_with_hops n edges s d k = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk : HopsConstraints n.val k.val), ∀ r : Std.I64, shortest_path_with_hops n edges s d k = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= D(s,d), where D(s,d) is the ordinary shortest-path distance from s to d in the original weighted graph, i.e. the minimum over all simple paths P from s to d of the sum of the original weights w(e) for e in P.
  Preconditions: n, edges, s, d, k satisfy the problem constraints: 2 <= n <= 500; every entry of edges is a triple [u,v,w] with 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; no unordered pair {u,v} occurs in two different entries of edges; the undirected graph on nodes 0,...,n-1 with these edges is connected; n-1 <= len(edges) <= min(10^4, n*(n-1)/2); 0 <= s < n; 0 <= d < n; s != d; 0 <= k <= n-1. -/
theorem spec_4 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk : HopsConstraints n.val k.val) :
    ∀ r : Std.I64, shortest_path_with_hops n edges s d k = ok r →
      ∀ D : ℤ, IsShortestDistance es s.val d.val D → r.val ≤ D := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk : HopsConstraints n.val k.val), ∀ r : Std.I64, shortest_path_with_hops n edges s d k = ok r →
      ∀ D : ℤ, IsShortestDistance es s.val d.val D → r.val ≤ D) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there exists a simple path from s to d with at most k edges (equivalently, the minimum number of edges in any s-d path is at most k).
  Preconditions: n, edges, s, d, k satisfy the problem constraints: 2 <= n <= 500; every entry of edges is a triple [u,v,w] with 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; no unordered pair {u,v} occurs in two different entries of edges; the undirected graph on nodes 0,...,n-1 with these edges is connected; n-1 <= len(edges) <= min(10^4, n*(n-1)/2); 0 <= s < n; 0 <= d < n; s != d; 0 <= k <= n-1. -/
theorem spec_5 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk : HopsConstraints n.val k.val) :
    ∀ r : Std.I64, shortest_path_with_hops n edges s d k = ok r →
      (r.val = 0 ↔
        ∃ vs : List ℤ, SimplePath es s.val d.val vs ∧ vs.length ≤ k.val.toNat + 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk : HopsConstraints n.val k.val), ∀ r : Std.I64, shortest_path_with_hops n edges s d k = ok r →
      (r.val = 0 ↔
        ∃ vs : List ℤ, SimplePath es s.val d.val vs ∧ vs.length ≤ k.val.toNat + 1)) := by
  sorry

/-- If r1 = shortest_path_with_hops(n,edges,s,d,k1) and r2 = shortest_path_with_hops(n,edges,s,d,k2) both return results, then r1 >= r2.
  Preconditions: n, edges, s, d satisfy the problem graph constraints: 2 <= n <= 500; every entry of edges is a triple [u,v,w] with 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; no unordered pair {u,v} occurs twice; the undirected graph on nodes 0,...,n-1 is connected; n-1 <= len(edges) <= min(10^4, n*(n-1)/2); 0 <= s < n; 0 <= d < n; s != d; and 0 <= k1 <= k2 <= n-1. -/
theorem spec_6 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d : Std.I64) (k1 k2 : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk1 : HopsConstraints n.val k1.val)
    (hk2 : HopsConstraints n.val k2.val) (hmono : k1.val ≤ k2.val) :
    ∀ r1 r2 : Std.I64, shortest_path_with_hops n edges s d k1 = ok r1 →
      shortest_path_with_hops n edges s d k2 = ok r2 → r2.val ≤ r1.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d : Std.I64) (k1 k2 : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk1 : HopsConstraints n.val k1.val)
    (hk2 : HopsConstraints n.val k2.val) (hmono : k1.val ≤ k2.val), ∀ r1 r2 : Std.I64, shortest_path_with_hops n edges s d k1 = ok r1 →
      shortest_path_with_hops n edges s d k2 = ok r2 → r2.val ≤ r1.val) := by
  sorry

/-- Whenever the function returns a result r on (n,edges,s,d,k), the call shortest_path_with_hops(n,edges,d,s,k) also returns a result and the two results are equal.
  Preconditions: n, edges, s, d, k satisfy the problem constraints: 2 <= n <= 500; every entry of edges is a triple [u,v,w] with 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; no unordered pair {u,v} occurs in two different entries of edges; the undirected graph on nodes 0,...,n-1 with these edges is connected; n-1 <= len(edges) <= min(10^4, n*(n-1)/2); 0 <= s < n; 0 <= d < n; s != d; 0 <= k <= n-1. -/
theorem spec_7 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk : HopsConstraints n.val k.val) :
    ∀ r : Std.I64, shortest_path_with_hops n edges s d k = ok r →
      ∃ r' : Std.I64, shortest_path_with_hops n edges d s k = ok r' ∧ r'.val = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk : HopsConstraints n.val k.val), ∀ r : Std.I64, shortest_path_with_hops n edges s d k = ok r →
      ∃ r' : Std.I64, shortest_path_with_hops n edges d s k = ok r' ∧ r'.val = r.val) := by
  sorry

/-- Whenever shortest_path_with_hops(n,edges,s,d,k) returns r and shortest_path_with_hops(n,edges',s,d,k) returns r', we have r = r'.
  Preconditions: n, edges, s, d, k satisfy the problem constraints: 2 <= n <= 500; every entry of edges is a triple [u,v,w] with 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; no unordered pair {u,v} occurs in two different entries of edges; the undirected graph on nodes 0,...,n-1 with these edges is connected; n-1 <= len(edges) <= min(10^4, n*(n-1)/2); 0 <= s < n; 0 <= d < n; s != d; 0 <= k <= n-1; and edges' is any permutation of the entries of edges. -/
theorem spec_8 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (edges' : Slice (alloc.vec.Vec Std.I64))
    (hgraph : GraphConstraints n.val edges es) (hends : EndpointsConstraints n.val s.val d.val)
    (hk : HopsConstraints n.val k.val) (hperm : edges'.val.Perm edges.val) :
    ∀ r r' : Std.I64, shortest_path_with_hops n edges s d k = ok r →
      shortest_path_with_hops n edges' s d k = ok r' → r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (edges' : Slice (alloc.vec.Vec Std.I64))
    (hgraph : GraphConstraints n.val edges es) (hends : EndpointsConstraints n.val s.val d.val)
    (hk : HopsConstraints n.val k.val) (hperm : edges'.val.Perm edges.val), ∀ r r' : Std.I64, shortest_path_with_hops n edges s d k = ok r →
      shortest_path_with_hops n edges' s d k = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, there exist a simple path P from s to d and a set Z of at most k edges of P such that r = sum of w(e) over all edges e of P that are not in Z. Here w(e) denotes the original weight of edge e.
  Preconditions: n, edges, s, d, k satisfy the problem constraints: 2 <= n <= 500; every entry of edges is a triple [u,v,w] with 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; no unordered pair {u,v} occurs in two different entries of edges; the undirected graph on nodes 0,...,n-1 with these edges is connected; n-1 <= len(edges) <= min(10^4, n*(n-1)/2); 0 <= s < n; 0 <= d < n; s != d; 0 <= k <= n-1. -/
theorem spec_9 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk : HopsConstraints n.val k.val) :
    ∀ r : Std.I64, shortest_path_with_hops n edges s d k = ok r →
      ∃ vs : List ℤ, SimplePath es s.val d.val vs ∧
        ∃ rem : List ℤ, SubWeights rem (pathWeights es vs) ∧
          rem.length ≤ k.val.toNat ∧ r.val = pathWeight es vs - rem.sum := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk : HopsConstraints n.val k.val), ∀ r : Std.I64, shortest_path_with_hops n edges s d k = ok r →
      ∃ vs : List ℤ, SimplePath es s.val d.val vs ∧
        ∃ rem : List ℤ, SubWeights rem (pathWeights es vs) ∧
          rem.length ≤ k.val.toNat ∧ r.val = pathWeight es vs - rem.sum) := by
  sorry

/-- Whenever the function returns a result r, for every simple path P from s to d and every set Z of at most k edges of P, r <= sum of w(e) over all edges e of P that are not in Z, where w(e) is the original weight of edge e.
  Preconditions: n, edges, s, d, k satisfy the problem constraints: 2 <= n <= 500; every entry of edges is a triple [u,v,w] with 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; no unordered pair {u,v} occurs in two different entries of edges; the undirected graph on nodes 0,...,n-1 with these edges is connected; n-1 <= len(edges) <= min(10^4, n*(n-1)/2); 0 <= s < n; 0 <= d < n; s != d; 0 <= k <= n-1. -/
theorem spec_10 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk : HopsConstraints n.val k.val) :
    ∀ r : Std.I64, shortest_path_with_hops n edges s d k = ok r →
      ∀ vs : List ℤ, SimplePath es s.val d.val vs →
        ∀ rem : List ℤ, SubWeights rem (pathWeights es vs) → rem.length ≤ k.val.toNat →
          r.val ≤ pathWeight es vs - rem.sum := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk : HopsConstraints n.val k.val), ∀ r : Std.I64, shortest_path_with_hops n edges s d k = ok r →
      ∀ vs : List ℤ, SimplePath es s.val d.val vs →
        ∀ rem : List ℤ, SubWeights rem (pathWeights es vs) → rem.length ≤ k.val.toNat →
          r.val ≤ pathWeight es vs - rem.sum) := by
  sorry

/-- Whenever shortest_path_with_hops(n,edges,s,d,k) returns r and shortest_path_with_hops(n,edges',s',d',k) returns r', we have r = r'.
  Preconditions: n, edges, s, d, k satisfy the problem constraints (as in spec_1), and π is a bijection on {0,...,n-1}; edges' is obtained from edges by replacing each [u,v,w] with [π(u),π(v),w]; s' = π(s); d' = π(d). -/
theorem spec_11 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (π : ℤ → ℤ) (edges' : Slice (alloc.vec.Vec Std.I64))
    (es' : List Edge) (s' d' : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk : HopsConstraints n.val k.val)
    (hπ : IsBijectionOnRange n.val π) (hrep' : RepresentsEdges edges' es')
    (hrelabel : IsEdgeRenaming π es es') (hs' : s'.val = π s.val) (hd' : d'.val = π d.val) :
    ∀ r r' : Std.I64, shortest_path_with_hops n edges s d k = ok r →
      shortest_path_with_hops n edges' s' d' k = ok r' → r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (es : List Edge)
    (s d k : Std.I64) (π : ℤ → ℤ) (edges' : Slice (alloc.vec.Vec Std.I64))
    (es' : List Edge) (s' d' : Std.I64) (hgraph : GraphConstraints n.val edges es)
    (hends : EndpointsConstraints n.val s.val d.val) (hk : HopsConstraints n.val k.val)
    (hπ : IsBijectionOnRange n.val π) (hrep' : RepresentsEdges edges' es')
    (hrelabel : IsEdgeRenaming π es es') (hs' : s'.val = π s.val) (hd' : d'.val = π d.val), ∀ r r' : Std.I64, shortest_path_with_hops n edges s d k = ok r →
      shortest_path_with_hops n edges' s' d' k = ok r' → r.val = r'.val) := by
  sorry

end AegisSpec.ShortestPathWithHops
