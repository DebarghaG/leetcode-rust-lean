import Aegis.CountPairs.Code.Funs

/-!
# Specifications of `Aegis.CountPairs.count_pairs`

LeetCode problem `count-unreachable-pairs-of-nodes-in-an-undirected-graph`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountPairs

noncomputable section

attribute [local instance] Classical.propDecidable

def edgePair? (e : alloc.vec.Vec Std.I64) : Option (Int × Int) :=
  match e.val with
  | [x, y] => some (x.val, y.val)
  | _ => none

def edgeAt (s : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Option (Int × Int) :=
  match s.val[i]? with
  | some e => edgePair? e
  | none => none

def edgeList (s : Slice (alloc.vec.Vec Std.I64)) : List (Int × Int) :=
  List.filterMap edgePair? s.val

def adj (E : List (Int × Int)) (u v : Int) : Prop :=
  (u, v) ∈ E ∨ (v, u) ∈ E

def reachable (E : List (Int × Int)) (u v : Int) : Prop :=
  Relation.ReflTransGen (adj E) u v

def totalPairs (n : Nat) : Int := ((n : Int) * ((n : Int) - 1)) / 2

def unreachablePairs (n : Nat) (E : List (Int × Int)) : Finset (Nat × Nat) :=
  Finset.filter (fun p : Nat × Nat => p.1 < p.2 ∧ ¬ reachable E (p.1 : Int) (p.2 : Int))
    (Finset.product (Finset.range n) (Finset.range n))

def unreachablePairCount (n : Nat) (E : List (Int × Int)) : Int :=
  ((unreachablePairs n E).card : Int)

def connectedPairs (n : Nat) (E : List (Int × Int)) : Finset (Nat × Nat) :=
  Finset.filter (fun p : Nat × Nat => p.1 < p.2 ∧ reachable E (p.1 : Int) (p.2 : Int))
    (Finset.product (Finset.range n) (Finset.range n))

def connectedPairCount (n : Nat) (E : List (Int × Int)) : Int :=
  ((connectedPairs n E).card : Int)

def isConnected (n : Nat) (E : List (Int × Int)) : Prop :=
  ∀ u, u < n → ∀ v, v < n → reachable E (u : Int) (v : Int)

def componentOf (n : Nat) (E : List (Int × Int)) (u : Nat) : Finset Nat :=
  Finset.filter (fun v : Nat => reachable E (u : Int) (v : Int)) (Finset.range n)

def components (n : Nat) (E : List (Int × Int)) : Finset (Finset Nat) :=
  Finset.image (fun u : Nat => componentOf n E u) (Finset.range n)

def compSize (n : Nat) (E : List (Int × Int)) (u : Nat) : Int :=
  ((componentOf n E u).card : Int)

def compRoots (n : Nat) (E : List (Int × Int)) : Finset Nat :=
  Finset.filter (fun u : Nat => ∀ v, v < n → reachable E (v : Int) (u : Int) → u ≤ v)
    (Finset.range n)

def compPairSum (n : Nat) (E : List (Int × Int)) : Int :=
  Finset.sum
    (Finset.filter (fun p : Nat × Nat => p.1 < p.2)
      (Finset.product (compRoots n E) (compRoots n E)))
    (fun p : Nat × Nat => compSize n E p.1 * compSize n E p.2)

def validEdge (n : Int) (s : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Prop :=
  ∃ a b : Int, edgeAt s i = some (a, b) ∧ 0 ≤ a ∧ a < n ∧ 0 ≤ b ∧ b < n ∧ a ≠ b

def validEdges (n : Int) (s : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∀ i, i < s.val.length → validEdge n s i

def edgesDistinct (s : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∀ (i j : Nat), i < j → j < s.val.length → ∀ a b a' b' : Int,
    edgeAt s i = some (a, b) → edgeAt s j = some (a', b') →
      ¬ ((a = a' ∧ b = b') ∨ (a = b' ∧ b = a'))

/-- Let G be the undirected graph with vertex set V = {0,1,...,n-1} and with one undirected edge between edges[i][0] and edges[i][1] for each i with 0 <= i < len(edges). Say two distinct vertices u and v are unreachable if there is no path in G from u to v. The function returns a result r, and the integer value of r equals the number of unordered pairs {u,v} of distinct vertices of V (equivalently, pairs with 0 <= u < v < n) such that u and v are unreachable.
  Preconditions: n is an I64 satisfying 1 <= n <= 100000. edges is a slice of Vec<I64> with len(edges) <= 200000. For every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]. For distinct i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are different. -/
theorem spec_1 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges) :
    ∃ r : Std.I64, Aegis.CountPairs.count_pairs n edges = ok r ∧
      r.val = unreachablePairCount n.val.toNat (edgeList edges) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges), ∃ r : Std.I64, Aegis.CountPairs.count_pairs n edges = ok r ∧
      r.val = unreachablePairCount n.val.toNat (edgeList edges)) := by
  sorry

/-- Under these preconditions, the call count_pairs(n, edges) returns a result r; it does not fail due to overflow, out-of-bounds indexing, or panic.
  Preconditions: n is an I64 satisfying 1 <= n <= 100000. edges is a slice of Vec<I64> with len(edges) <= 200000. For every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]. For distinct i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are different. -/
theorem spec_2 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges) :
    ∃ r : Std.I64, Aegis.CountPairs.count_pairs n edges = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges), ∃ r : Std.I64, Aegis.CountPairs.count_pairs n edges = ok r) := by
  sorry

/-- Whenever the call returns a result r, the integer value of r is nonnegative: 0 <= r.
  Preconditions: n is an I64 satisfying 1 <= n <= 100000. edges is a slice of Vec<I64> with len(edges) <= 200000. For every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]. For distinct i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are different. -/
theorem spec_3 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges)
    (r : Std.I64) (hr : Aegis.CountPairs.count_pairs n edges = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges)
    (r : Std.I64) (hr : Aegis.CountPairs.count_pairs n edges = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever the call returns a result r, the integer value of r satisfies r <= n*(n-1)/2, where the arithmetic is ordinary mathematical integer arithmetic.
  Preconditions: n is an I64 satisfying 1 <= n <= 100000. edges is a slice of Vec<I64> with len(edges) <= 200000. For every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]. For distinct i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are different. -/
theorem spec_4 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges)
    (r : Std.I64) (hr : Aegis.CountPairs.count_pairs n edges = ok r) :
    r.val ≤ totalPairs n.val.toNat := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges)
    (r : Std.I64) (hr : Aegis.CountPairs.count_pairs n edges = ok r), r.val ≤ totalPairs n.val.toNat) := by
  sorry

/-- The function returns a result r, and the integer value of r is n*(n-1)/2.
  Preconditions: n is an I64 satisfying 1 <= n <= 100000. edges is a slice of Vec<I64> with len(edges) = 0. -/
theorem spec_5 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hempty : edges.val.length = 0) :
    ∃ r : Std.I64, Aegis.CountPairs.count_pairs n edges = ok r ∧
      r.val = totalPairs n.val.toNat := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hempty : edges.val.length = 0), ∃ r : Std.I64, Aegis.CountPairs.count_pairs n edges = ok r ∧
      r.val = totalPairs n.val.toNat) := by
  sorry

/-- Let G be the undirected graph defined by n and edges. Whenever the call returns a result r, r = 0 if and only if G is connected, i.e. for every two vertices u,v in {0,...,n-1} there is a path in G from u to v (equivalently, G has exactly one connected component).
  Preconditions: n is an I64 satisfying 1 <= n <= 100000. edges is a slice of Vec<I64> with len(edges) <= 200000. For every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]. For distinct i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are different. -/
theorem spec_6 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges)
    (r : Std.I64) (hr : Aegis.CountPairs.count_pairs n edges = ok r) :
    (r.val = 0 ↔ isConnected n.val.toNat (edgeList edges)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges)
    (r : Std.I64) (hr : Aegis.CountPairs.count_pairs n edges = ok r), (r.val = 0 ↔ isConnected n.val.toNat (edgeList edges))) := by
  sorry

/-- Let C_1,...,C_m be the distinct connected components of the undirected graph G defined by n and edges, where a connected component is a maximal nonempty vertex set such that any two of its vertices are connected by a path. Let s_i = |C_i|. Whenever the call returns a result r, the integer value of r equals sum_{1 <= i < j <= m} s_i * s_j.
  Preconditions: n is an I64 satisfying 1 <= n <= 100000. edges is a slice of Vec<I64> with len(edges) <= 200000. For every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]. For distinct i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are different. -/
theorem spec_7 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges)
    (r : Std.I64) (hr : Aegis.CountPairs.count_pairs n edges = ok r) :
    r.val = compPairSum n.val.toNat (edgeList edges) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges)
    (r : Std.I64) (hr : Aegis.CountPairs.count_pairs n edges = ok r), r.val = compPairSum n.val.toNat (edgeList edges)) := by
  sorry

/-- Let G be the undirected graph defined by n and edges, and let R be the number of unordered pairs {u,v} with 0 <= u < v < n such that u and v are connected by a path in G. Whenever the call returns a result r, the integer values satisfy r + R = n*(n-1)/2.
  Preconditions: n is an I64 satisfying 1 <= n <= 100000. edges is a slice of Vec<I64> with len(edges) <= 200000. For every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]. For distinct i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are different. -/
theorem spec_8 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges)
    (r : Std.I64) (hr : Aegis.CountPairs.count_pairs n edges = ok r) :
    r.val + connectedPairCount n.val.toNat (edgeList edges) = totalPairs n.val.toNat := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges)
    (r : Std.I64) (hr : Aegis.CountPairs.count_pairs n edges = ok r), r.val + connectedPairCount n.val.toNat (edgeList edges) = totalPairs n.val.toNat) := by
  sorry

/-- The calls count_pairs(n, edges) and count_pairs(n, edges') both return results r and r', and the integer values satisfy r = r'.
  Preconditions: n is an I64 satisfying 1 <= n <= 100000. edges and edges' are slices of Vec<I64>, each satisfying the edge constraints for n: len(edges) <= 200000, len(edges') <= 200000, every edge has length 2, both endpoints are in [0,n-1], the two endpoints are different, and no unordered edge is repeated. Also len(edges') = len(edges), and for every i with 0 <= i < len(edges), edges'[i][0] = edges[i][1] and edges'[i][1] = edges[i][0]. -/
theorem spec_9 (n : Std.I64)
    (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hlen' : edges'.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges)
    (hvalid' : validEdges n.val edges')
    (hsimple' : edgesDistinct edges')
    (hsame_len : edges'.val.length = edges.val.length)
    (hrev : ∀ (i : Nat), i < edges.val.length → ∃ a b : Int,
      edgeAt edges i = some (a, b) ∧ edgeAt edges' i = some (b, a)) :
    ∃ r r' : Std.I64, Aegis.CountPairs.count_pairs n edges = ok r ∧
      Aegis.CountPairs.count_pairs n edges' = ok r' ∧ r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64)
    (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hlen' : edges'.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges)
    (hvalid' : validEdges n.val edges')
    (hsimple' : edgesDistinct edges')
    (hsame_len : edges'.val.length = edges.val.length)
    (hrev : ∀ (i : Nat), i < edges.val.length → ∃ a b : Int,
      edgeAt edges i = some (a, b) ∧ edgeAt edges' i = some (b, a)), ∃ r r' : Std.I64, Aegis.CountPairs.count_pairs n edges = ok r ∧
      Aegis.CountPairs.count_pairs n edges' = ok r' ∧ r.val = r'.val) := by
  sorry

/-- Let r be the result of count_pairs(n, edges) and let r' be the result of count_pairs(n, edges'). Both calls return results, and the integer values satisfy r' <= r.
  Preconditions: n is an I64 satisfying 1 <= n <= 100000. edges is a slice of Vec<I64> satisfying the edge constraints for n, and len(edges) < 200000. Let a and b satisfy 0 <= a < n, 0 <= b < n, a != b, and the unordered pair {a,b} is not already an edge in edges. Let edges' be the slice obtained by appending the one edge [a,b] to edges; edges' also satisfies all edge constraints for n. -/
theorem spec_10 (n : Std.I64)
    (edges edges' : Slice (alloc.vec.Vec Std.I64)) (a b : Int)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length < 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges)
    (ha_lo : 0 ≤ a) (ha_hi : a < n.val)
    (hb_lo : 0 ≤ b) (hb_hi : b < n.val) (hab : a ≠ b)
    (hnew : ∀ (i : Nat), i < edges.val.length → ∀ x y : Int,
      edgeAt edges i = some (x, y) → ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)))
    (hvalid' : validEdges n.val edges')
    (hsimple' : edgesDistinct edges')
    (happ_len : edges'.val.length = edges.val.length + 1)
    (happ_prefix : ∀ (i : Nat), i < edges.val.length → edgeAt edges' i = edgeAt edges i)
    (happ_last : edgeAt edges' edges.val.length = some (a, b)) :
    ∃ r r' : Std.I64, Aegis.CountPairs.count_pairs n edges = ok r ∧
      Aegis.CountPairs.count_pairs n edges' = ok r' ∧ r'.val ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64)
    (edges edges' : Slice (alloc.vec.Vec Std.I64)) (a b : Int)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length < 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges)
    (ha_lo : 0 ≤ a) (ha_hi : a < n.val)
    (hb_lo : 0 ≤ b) (hb_hi : b < n.val) (hab : a ≠ b)
    (hnew : ∀ (i : Nat), i < edges.val.length → ∀ x y : Int,
      edgeAt edges i = some (x, y) → ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)))
    (hvalid' : validEdges n.val edges')
    (hsimple' : edgesDistinct edges')
    (happ_len : edges'.val.length = edges.val.length + 1)
    (happ_prefix : ∀ (i : Nat), i < edges.val.length → edgeAt edges' i = edgeAt edges i)
    (happ_last : edgeAt edges' edges.val.length = some (a, b)), ∃ r r' : Std.I64, Aegis.CountPairs.count_pairs n edges = ok r ∧
      Aegis.CountPairs.count_pairs n edges' = ok r' ∧ r'.val ≤ r.val) := by
  sorry

/-- Let G be the undirected graph defined by n and edges. Whenever the call returns a result r, for every two distinct connected components C and D of G, the integer value of r is at least |C| * |D|.
  Preconditions: n is an I64 satisfying 1 <= n <= 100000. edges is a slice of Vec<I64> with len(edges) <= 200000. For every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]. For distinct i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are different. -/
theorem spec_11 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges)
    (r : Std.I64) (hr : Aegis.CountPairs.count_pairs n edges = ok r) :
    ∀ C ∈ components n.val.toNat (edgeList edges),
      ∀ D ∈ components n.val.toNat (edgeList edges), C ≠ D →
        (C.card : Int) * (D.card : Int) ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges)
    (r : Std.I64) (hr : Aegis.CountPairs.count_pairs n edges = ok r), ∀ C ∈ components n.val.toNat (edgeList edges),
      ∀ D ∈ components n.val.toNat (edgeList edges), C ≠ D →
        (C.card : Int) * (D.card : Int) ≤ r.val) := by
  sorry

/-- Let G be the undirected graph defined by n and edges. For each vertex u in {0,...,n-1}, let comp_size(u) be the number of vertices in the connected component of G containing u. Whenever the call returns a result r, sum_{u=0}^{n-1} (n - comp_size(u)) = 2 * r, with ordinary mathematical integer arithmetic.
  Preconditions: n is an I64 satisfying 1 <= n <= 100000. edges is a slice of Vec<I64> with len(edges) <= 200000. For every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]. For distinct i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are different. -/
theorem spec_12 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges)
    (r : Std.I64) (hr : Aegis.CountPairs.count_pairs n edges = ok r) :
    Finset.sum (Finset.range n.val.toNat)
        (fun u : Nat => n.val - compSize n.val.toNat (edgeList edges) u) = 2 * r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hlen : edges.val.length ≤ 200000)
    (hvalid : validEdges n.val edges)
    (hsimple : edgesDistinct edges)
    (r : Std.I64) (hr : Aegis.CountPairs.count_pairs n edges = ok r), Finset.sum (Finset.range n.val.toNat)
        (fun u : Nat => n.val - compSize n.val.toNat (edgeList edges) u) = 2 * r.val) := by
  sorry

end

end AegisSpec.CountPairs
