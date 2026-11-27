import Aegis.CountPaths.Code.Funs

/-!
# Specifications of `Aegis.CountPaths.count_paths`

LeetCode problem `count-valid-paths-in-a-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountPaths

def edgeLabels (e : alloc.vec.Vec Std.I64) : List Int := e.val.map (fun x => x.val)

def edgeAt? (edges : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Option (Int × Int) :=
  match edges.val[i]? with
  | some e =>
    match edgeLabels e with
    | [u, v] => some (u, v)
    | _ => none
  | none => none

def IsPrimeLabel (x : Int) : Prop := 2 ≤ x ∧ ∀ d : Int, 2 ≤ d → d < x → ¬ d ∣ x

def InLabelRange (n x : Int) : Prop := 1 ≤ x ∧ x ≤ n

def Adj (edges : Slice (alloc.vec.Vec Std.I64)) (u v : Int) : Prop :=
  ∃ e ∈ edges.val, edgeLabels e = [u, v] ∨ edgeLabels e = [v, u]

def IsWalk (R : Int → Int → Prop) : List Int → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => R x y ∧ IsWalk R (y :: rest)

def Reach (edges : Slice (alloc.vec.Vec Std.I64)) (u v : Int) : Prop :=
  ∃ s : List Int, s ≠ [] ∧ IsWalk (Adj edges) s ∧ s.head? = some u ∧ s.getLast? = some v

def stepKey (x y : Int) : Int × Int := if x ≤ y then (x, y) else (y, x)

def edgeKeys (s : List Int) : List (Int × Int) :=
  (s.zip s.tail).map (fun p : Int × Int => stepKey p.1 p.2)

def HasCycle (edges : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∃ s : List Int,
    3 ≤ s.length ∧ IsWalk (Adj edges) s ∧ s.head? = s.getLast? ∧ s.dropLast.Nodup ∧
      (edgeKeys s).Nodup

def OnPath (edges : Slice (alloc.vec.Vec Std.I64)) (a b x : Int) : Prop :=
  ∃ s : List Int,
    s ≠ [] ∧ s.Nodup ∧ IsWalk (Adj edges) s ∧ s.head? = some a ∧ s.getLast? = some b ∧
      x ∈ s

def PathHasUniquePrime (edges : Slice (alloc.vec.Vec Std.I64)) (a b p : Int) : Prop :=
  OnPath edges a b p ∧ IsPrimeLabel p ∧
    ∀ q : Int, OnPath edges a b q → IsPrimeLabel q → q = p

def PathHasExactlyOnePrime (edges : Slice (alloc.vec.Vec Std.I64)) (a b : Int) : Prop :=
  ∃ p : Int, PathHasUniquePrime edges a b p

structure IsTreeInput (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) : Prop where

  n_lower : 1 ≤ n.val

  n_upper : n.val ≤ 100000

  edges_length : edges.val.length = (n.val - 1).toNat

  edges_pairs : ∀ i : Nat, i < edges.val.length →
    ∃ u v : Int,
      edgeAt? edges i = some (u, v) ∧ InLabelRange n.val u ∧ InLabelRange n.val v ∧ u ≠ v

  connected : ∀ a b : Int, InLabelRange n.val a → InLabelRange n.val b → Reach edges a b

  acyclic : ¬ HasCycle edges

noncomputable def labelFinset (n : Int) : Finset Int :=
  (Finset.range n.toNat).image (fun k : Nat => (k : Int) + 1)

noncomputable def unorderedLabelPairs (n : Int) : Finset (Int × Int) := by
  classical
  exact ((labelFinset n).product (labelFinset n)).filter
    (fun ab : Int × Int => ab.1 < ab.2)

noncomputable def orderedLabelPairs (n : Int) : Finset (Int × Int) := by
  classical
  exact ((labelFinset n).product (labelFinset n)).filter
    (fun ab : Int × Int => ab.1 ≠ ab.2)

noncomputable def validPairCount (n : Int) (edges : Slice (alloc.vec.Vec Std.I64)) : Nat := by
  classical
  exact ((unorderedLabelPairs n).filter
    (fun ab : Int × Int => PathHasExactlyOnePrime edges ab.1 ab.2)).card

noncomputable def validOrderedPairCount (n : Int) (edges : Slice (alloc.vec.Vec Std.I64)) : Nat := by
  classical
  exact ((orderedLabelPairs n).filter
    (fun ab : Int × Int => PathHasExactlyOnePrime edges ab.1 ab.2)).card

noncomputable def primeWitnessCount (n : Int) (edges : Slice (alloc.vec.Vec Std.I64))
    (p : Int) : Nat := by
  classical
  exact ((unorderedLabelPairs n).filter
    (fun ab : Int × Int => PathHasUniquePrime edges ab.1 ab.2 p)).card

noncomputable def primeLabels (n : Int) : Finset Int := by
  classical
  exact (labelFinset n).filter (fun x : Int => IsPrimeLabel x)

noncomputable def onePrimeEdgeCount (edges : Slice (alloc.vec.Vec Std.I64)) : Nat := by
  classical
  exact ((Finset.range edges.val.length).filter
    (fun i : Nat =>
      match edgeAt? edges i with
      | some (u, v) =>
        (IsPrimeLabel u ∧ ¬ IsPrimeLabel v) ∨ (¬ IsPrimeLabel u ∧ IsPrimeLabel v)
      | none => False)).card

def ForestAdj (edges : Slice (alloc.vec.Vec Std.I64)) (u v : Int) : Prop :=
  ¬ IsPrimeLabel u ∧ ¬ IsPrimeLabel v ∧ Adj edges u v

def ForestReach (edges : Slice (alloc.vec.Vec Std.I64)) (u v : Int) : Prop :=
  ∃ s : List Int,
    s ≠ [] ∧ IsWalk (ForestAdj edges) s ∧ s.head? = some u ∧ s.getLast? = some v

noncomputable def forestComponent (n : Int) (edges : Slice (alloc.vec.Vec Std.I64))
    (x : Int) : Finset Int := by
  classical
  exact (labelFinset n).filter (fun y : Int => ForestReach edges x y)

noncomputable def forestComponents (n : Int) (edges : Slice (alloc.vec.Vec Std.I64)) :
    Finset (Finset Int) := by
  classical
  exact ((labelFinset n).filter (fun v : Int => ¬ IsPrimeLabel v)).image
    (fun v : Int => forestComponent n edges v)

noncomputable def neighborComponents (n : Int) (edges : Slice (alloc.vec.Vec Std.I64))
    (p : Int) : Finset (Finset Int) := by
  classical
  exact ((labelFinset n).filter (fun v : Int => ¬ IsPrimeLabel v ∧ Adj edges p v)).image
    (fun v : Int => forestComponent n edges v)

noncomputable def primeShapeCount (n : Int) (edges : Slice (alloc.vec.Vec Std.I64))
    (p : Int) : Nat :=
  let comps := neighborComponents n edges p
  comps.sum (fun C => C.card) + (comps.offDiag.sum (fun CD => CD.1.card * CD.2.card)) / 2

noncomputable def forestComponentPairSum (n : Int) (edges : Slice (alloc.vec.Vec Std.I64)) : Nat := by
  classical
  exact (forestComponents n edges).sum (fun C => C.card * (C.card - 1) / 2)

/-- Whenever the function returns a result r, r equals the number of unordered pairs {a,b} of distinct labels with 1 <= a < b <= n such that Path(a,b) contains exactly one prime label. Equivalently, r is the number of valid paths, where a valid path is an unordered pair of distinct nodes {a,b} whose unique connecting path has exactly one prime among its node labels; endpoints are included, and {a,b} and {b,a} are the same path counted once.
  Preconditions: n is an integer with 1 <= n <= 100000. edges is a slice of length n-1. For every i with 0 <= i < len(edges), edges[i] has length 2, and if edges[i][0] = u and edges[i][1] = v then 1 <= u <= n, 1 <= v <= n, and u != v. The undirected graph with vertex set {1,...,n} and an edge between u and v for each entry [u,v] or [v,u] in edges is connected and acyclic, so it is a tree with n-1 edges. A label x in {1,...,n} is prime iff x >= 2 and no integer d with 2 <= d < x divides x. For distinct a,b in {1,...,n}, Path(a,b) denotes the set of node labels on the unique simple path from a to b in this tree, including both endpoints. -/
theorem spec_1 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges) (r : Std.I64) (hr : Aegis.CountPaths.count_paths n edges = ok r) :
    r.val = (validPairCount n.val edges : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges) (r : Std.I64) (hr : Aegis.CountPaths.count_paths n edges = ok r), r.val = (validPairCount n.val edges : Int)) := by
  sorry

/-- Under the preconditions, the function returns a result r and does not fail: no arithmetic overflow, out-of-bounds access, panic, or other failure occurs.
  Preconditions: n is an integer with 1 <= n <= 100000. edges is a slice of length n-1. For every i with 0 <= i < len(edges), edges[i] has length 2, and if edges[i][0] = u and edges[i][1] = v then 1 <= u <= n, 1 <= v <= n, and u != v. The undirected graph with vertex set {1,...,n} and an edge between u and v for each entry [u,v] or [v,u] in edges is connected and acyclic, so it is a tree with n-1 edges. A label x in {1,...,n} is prime iff x >= 2 and no integer d with 2 <= d < x divides x. For distinct a,b in {1,...,n}, Path(a,b) denotes the set of node labels on the unique simple path from a to b in this tree, including both endpoints. -/
theorem spec_2 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges) :
    ∃ r : Std.I64, Aegis.CountPaths.count_paths n edges = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges), ∃ r : Std.I64, Aegis.CountPaths.count_paths n edges = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= n*(n-1)/2. The upper bound is the total number of unordered pairs of distinct nodes.
  Preconditions: n is an integer with 1 <= n <= 100000. edges is a slice of length n-1. For every i with 0 <= i < len(edges), edges[i] has length 2, and if edges[i][0] = u and edges[i][1] = v then 1 <= u <= n, 1 <= v <= n, and u != v. The undirected graph with vertex set {1,...,n} and an edge between u and v for each entry [u,v] or [v,u] in edges is connected and acyclic, so it is a tree with n-1 edges. A label x in {1,...,n} is prime iff x >= 2 and no integer d with 2 <= d < x divides x. For distinct a,b in {1,...,n}, Path(a,b) denotes the set of node labels on the unique simple path from a to b in this tree, including both endpoints. -/
theorem spec_3 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges) (r : Std.I64) (hr : Aegis.CountPaths.count_paths n edges = ok r) :
    0 ≤ r.val ∧ r.val ≤ n.val * (n.val - 1) / 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges) (r : Std.I64) (hr : Aegis.CountPaths.count_paths n edges = ok r), 0 ≤ r.val ∧ r.val ≤ n.val * (n.val - 1) / 2) := by
  sorry

/-- Let E be the number of indices i with 0 <= i < len(edges) such that exactly one of edges[i][0] and edges[i][1] is prime. Whenever the function returns a result r, r >= E.
  Preconditions: n is an integer with 1 <= n <= 100000. edges is a slice of length n-1. For every i with 0 <= i < len(edges), edges[i] has length 2, and if edges[i][0] = u and edges[i][1] = v then 1 <= u <= n, 1 <= v <= n, and u != v. The undirected graph with vertex set {1,...,n} and an edge between u and v for each entry [u,v] or [v,u] in edges is connected and acyclic, so it is a tree with n-1 edges. A label x in {1,...,n} is prime iff x >= 2 and no integer d with 2 <= d < x divides x. For distinct a,b in {1,...,n}, Path(a,b) denotes the set of node labels on the unique simple path from a to b in this tree, including both endpoints. -/
theorem spec_4 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges) (r : Std.I64) (hr : Aegis.CountPaths.count_paths n edges = ok r) :
    (onePrimeEdgeCount edges : Int) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges) (r : Std.I64) (hr : Aegis.CountPaths.count_paths n edges = ok r), (onePrimeEdgeCount edges : Int) ≤ r.val) := by
  sorry

/-- Let O be the number of ordered pairs (a,b) with 1 <= a <= n, 1 <= b <= n, and a != b, such that Path(a,b) contains exactly one prime label. Whenever the function returns a result r, 2*r = O.
  Preconditions: n is an integer with 1 <= n <= 100000. edges is a slice of length n-1. For every i with 0 <= i < len(edges), edges[i] has length 2, and if edges[i][0] = u and edges[i][1] = v then 1 <= u <= n, 1 <= v <= n, and u != v. The undirected graph with vertex set {1,...,n} and an edge between u and v for each entry [u,v] or [v,u] in edges is connected and acyclic, so it is a tree with n-1 edges. A label x in {1,...,n} is prime iff x >= 2 and no integer d with 2 <= d < x divides x. For distinct a,b in {1,...,n}, Path(a,b) denotes the set of node labels on the unique simple path from a to b in this tree, including both endpoints. -/
theorem spec_5 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges) (r : Std.I64) (hr : Aegis.CountPaths.count_paths n edges = ok r) :
    2 * r.val = (validOrderedPairCount n.val edges : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges) (r : Std.I64) (hr : Aegis.CountPaths.count_paths n edges = ok r), 2 * r.val = (validOrderedPairCount n.val edges : Int)) := by
  sorry

/-- For each prime label p in {1,...,n}, let V(p) be the number of unordered pairs {a,b} of distinct labels such that Path(a,b) contains p and contains no prime label other than p. Whenever the function returns a result r, r = sum over all prime p in {1,...,n} of V(p).
  Preconditions: n is an integer with 1 <= n <= 100000. edges is a slice of length n-1. For every i with 0 <= i < len(edges), edges[i] has length 2, and if edges[i][0] = u and edges[i][1] = v then 1 <= u <= n, 1 <= v <= n, and u != v. The undirected graph with vertex set {1,...,n} and an edge between u and v for each entry [u,v] or [v,u] in edges is connected and acyclic, so it is a tree with n-1 edges. A label x in {1,...,n} is prime iff x >= 2 and no integer d with 2 <= d < x divides x. For distinct a,b in {1,...,n}, Path(a,b) denotes the set of node labels on the unique simple path from a to b in this tree, including both endpoints. -/
theorem spec_6 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges) (r : Std.I64) (hr : Aegis.CountPaths.count_paths n edges = ok r) :
    r.val = (primeLabels n.val).sum (fun p => (primeWitnessCount n.val edges p : Int)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges) (r : Std.I64) (hr : Aegis.CountPaths.count_paths n edges = ok r), r.val = (primeLabels n.val).sum (fun p => (primeWitnessCount n.val edges p : Int))) := by
  sorry

/-- Fix a prime label p in {1,...,n}. Delete from the tree all nodes whose labels are prime, including p. This leaves a forest on the non-prime labels. Let C(p) be the set of connected components of this forest that contain at least one neighbor of p in the original tree. For a component C in C(p), let s(C) be the number of nodes in C. Then the number V(p) from the prime-decomposition specification is exactly sum over C in C(p) of s(C) plus sum over unordered pairs {C,D} of distinct components in C(p) of s(C)*s(D). Consequently, whenever the function returns a result r, r equals the sum of these quantities over all prime p in {1,...,n}.
  Preconditions: n is an integer with 1 <= n <= 100000. edges is a slice of length n-1. For every i with 0 <= i < len(edges), edges[i] has length 2, and if edges[i][0] = u and edges[i][1] = v then 1 <= u <= n, 1 <= v <= n, and u != v. The undirected graph with vertex set {1,...,n} and an edge between u and v for each entry [u,v] or [v,u] in edges is connected and acyclic, so it is a tree with n-1 edges. A label x in {1,...,n} is prime iff x >= 2 and no integer d with 2 <= d < x divides x. For distinct a,b in {1,...,n}, Path(a,b) denotes the set of node labels on the unique simple path from a to b in this tree, including both endpoints. -/
theorem spec_7 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges) (p : Int) (hp_mem : InLabelRange n.val p) (hp : IsPrimeLabel p)
    (r : Std.I64) (hr : Aegis.CountPaths.count_paths n edges = ok r) :
    primeWitnessCount n.val edges p = primeShapeCount n.val edges p ∧
      r.val = (primeLabels n.val).sum (fun q => (primeShapeCount n.val edges q : Int)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges) (p : Int) (hp_mem : InLabelRange n.val p) (hp : IsPrimeLabel p)
    (r : Std.I64) (hr : Aegis.CountPaths.count_paths n edges = ok r), primeWitnessCount n.val edges p = primeShapeCount n.val edges p ∧
      r.val = (primeLabels n.val).sum (fun q => (primeShapeCount n.val edges q : Int))) := by
  sorry

/-- Whenever the function returns a result r, r > 0 if and only if there exist distinct labels a,b in {1,...,n} such that Path(a,b) contains exactly one prime label.
  Preconditions: n is an integer with 1 <= n <= 100000. edges is a slice of length n-1. For every i with 0 <= i < len(edges), edges[i] has length 2, and if edges[i][0] = u and edges[i][1] = v then 1 <= u <= n, 1 <= v <= n, and u != v. The undirected graph with vertex set {1,...,n} and an edge between u and v for each entry [u,v] or [v,u] in edges is connected and acyclic, so it is a tree with n-1 edges. A label x in {1,...,n} is prime iff x >= 2 and no integer d with 2 <= d < x divides x. For distinct a,b in {1,...,n}, Path(a,b) denotes the set of node labels on the unique simple path from a to b in this tree, including both endpoints. -/
theorem spec_8 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges) (r : Std.I64) (hr : Aegis.CountPaths.count_paths n edges = ok r) :
    0 < r.val ↔
      ∃ a b : Int, InLabelRange n.val a ∧ InLabelRange n.val b ∧ a ≠ b ∧
        PathHasExactlyOnePrime edges a b := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges) (r : Std.I64) (hr : Aegis.CountPaths.count_paths n edges = ok r), 0 < r.val ↔
      ∃ a b : Int, InLabelRange n.val a ∧ InLabelRange n.val b ∧ a ≠ b ∧
        PathHasExactlyOnePrime edges a b) := by
  sorry

/-- If count_paths(n, edges) returns r and count_paths(n, edges2) returns r2, then r = r2. In particular, permuting the entries of edges or swapping the two coordinates inside any entry does not change the result.
  Preconditions: n is an integer with 1 <= n <= 100000. edges is a slice of length n-1. For every i with 0 <= i < len(edges), edges[i] has length 2, and if edges[i][0] = u and edges[i][1] = v then 1 <= u <= n, 1 <= v <= n, and u != v. The undirected graph with vertex set {1,...,n} and an edge between u and v for each entry [u,v] or [v,u] in edges is connected and acyclic, so it is a tree with n-1 edges. A label x in {1,...,n} is prime iff x >= 2 and no integer d with 2 <= d < x divides x. For distinct a,b in {1,...,n}, Path(a,b) denotes the set of node labels on the unique simple path from a to b in this tree, including both endpoints. Let edges2 be another slice of length n-1 satisfying the same conditions, and assume that for every pair of labels u,v, [u,v] occurs as an entry of edges in either order if and only if it occurs as an entry of edges2 in either order. Thus edges and edges2 represent the same undirected tree. -/
theorem spec_9 (n : Std.I64) (edges edges2 : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges) (h2 : IsTreeInput n edges2)
    (hsame : ∀ u v : Int, InLabelRange n.val u → InLabelRange n.val v →
      (Adj edges u v ↔ Adj edges2 u v))
    (r r2 : Std.I64) (hr : Aegis.CountPaths.count_paths n edges = ok r)
    (hr2 : Aegis.CountPaths.count_paths n edges2 = ok r2) : r = r2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (edges edges2 : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges) (h2 : IsTreeInput n edges2)
    (hsame : ∀ u v : Int, InLabelRange n.val u → InLabelRange n.val v →
      (Adj edges u v ↔ Adj edges2 u v))
    (r r2 : Std.I64) (hr : Aegis.CountPaths.count_paths n edges = ok r)
    (hr2 : Aegis.CountPaths.count_paths n edges2 = ok r2), r = r2) := by
  sorry

/-- Let the forest obtained by deleting all prime-labeled nodes have connected components on the non-prime labels, with sizes s1,...,sk. Whenever the function returns a result r, r <= n*(n-1)/2 - sum_{j=1..k} s_j*(s_j-1)/2.
  Preconditions: n is an integer with 1 <= n <= 100000. edges is a slice of length n-1. For every i with 0 <= i < len(edges), edges[i] has length 2, and if edges[i][0] = u and edges[i][1] = v then 1 <= u <= n, 1 <= v <= n, and u != v. The undirected graph with vertex set {1,...,n} and an edge between u and v for each entry [u,v] or [v,u] in edges is connected and acyclic, so it is a tree with n-1 edges. A label x in {1,...,n} is prime iff x >= 2 and no integer d with 2 <= d < x divides x. For distinct a,b in {1,...,n}, Path(a,b) denotes the set of node labels on the unique simple path from a to b in this tree, including both endpoints. -/
theorem spec_10 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges) (r : Std.I64) (hr : Aegis.CountPaths.count_paths n edges = ok r) :
    r.val ≤ n.val * (n.val - 1) / 2 - (forestComponentPairSum n.val edges : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h : IsTreeInput n edges) (r : Std.I64) (hr : Aegis.CountPaths.count_paths n edges = ok r), r.val ≤ n.val * (n.val - 1) / 2 - (forestComponentPairSum n.val edges : Int)) := by
  sorry

end AegisSpec.CountPaths
