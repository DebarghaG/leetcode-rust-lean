import Aegis.MaxXor.Code.Funs

/-!
# Specifications of `Aegis.MaxXor.max_xor`

LeetCode problem `maximum-xor-of-two-non-overlapping-subtrees`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxXor

open Aegis.MaxXor

def xorInt (a b : Int) : Int := ((a.toNat ^^^ b.toNat : Nat) : Int)

def orInt (a b : Int) : Int := ((a.toNat ||| b.toNat : Nat) : Int)

def edgeList (edges : Slice (alloc.vec.Vec Std.I64)) : List (Nat × Nat) :=
  edges.val.map fun v => ((v.val.getD 0 (0#i64)).val.toNat, (v.val.getD 1 (0#i64)).val.toNat)

def Adj (E : List (Nat × Nat)) (a b : Nat) : Prop := (a, b) ∈ E ∨ (b, a) ∈ E

inductive Path (E : List (Nat × Nat)) : Nat → Nat → List Nat → Prop where
  | nil (a : Nat) : Path E a a [a]
  | cons {a b c : Nat} {p : List Nat} :
      Adj E a b → Path E b c p → a ∉ p → Path E a c (a :: p)

def OnPath (E : List (Nat × Nat)) (v u : Nat) : Prop :=
  ∃ p : List Nat, Path E 0 u p ∧ v ∈ p

def normEdge (e : Nat × Nat) : Nat × Nat := (min e.1 e.2, max e.1 e.2)

def IsTree (E : List (Nat × Nat)) (n : Nat) : Prop :=
  (∀ e ∈ E, e.1 < n ∧ e.2 < n) ∧
    (∀ e ∈ E, e.1 ≠ e.2) ∧
    (E.map normEdge).Nodup ∧
    (∀ u v, u < n → v < n → ∃ p : List Nat, Path E u v p) ∧
    (∀ a p, Path E a a p → p = [a])

structure WellFormed (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) : Prop where

  h_n_lower : 2 ≤ n.val

  h_n_upper : n.val ≤ 50000

  h_edges_len : (edges.val.length : Int) = n.val - 1

  h_values_len : (values.val.length : Int) = n.val

  h_edges : ∀ v ∈ edges.val, v.val.length = 2 ∧ ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val < n.val

  h_values : ∀ x ∈ values.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9

  h_tree : IsTree (edgeList edges) n.val.toNat

def value (values : Slice Std.I64) (i : Nat) : Int := (values.val.getD i (0#i64)).val

noncomputable def S (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (v : Nat) : Int := by
  classical
  exact (Finset.range n.val.toNat).sum
    (fun u => if OnPath (edgeList edges) v u then value values u else 0)

noncomputable def maxS (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) : Int :=
  (List.range n.val.toNat).foldr (fun v acc => max (S n edges values v) acc) 0

noncomputable def orS (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) : Int :=
  (List.range n.val.toNat).foldr (fun v acc => orInt (S n edges values v) acc) 0

def IsLeastPowAbove (M : Int) (K : Nat) : Prop :=
  M < (2 : Int) ^ K ∧ ∀ K' : Nat, M < (2 : Int) ^ K' → K ≤ K'

def SubtreeDisjoint (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Prop :=
  ∀ u, u < n.val.toNat →
    ¬ (OnPath (edgeList edges) i u ∧ OnPath (edgeList edges) j u)

def Admissible (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Prop :=
  i < j ∧ j < n.val.toNat ∧ SubtreeDisjoint n edges i j

def Child (edges : Slice (alloc.vec.Vec Std.I64)) (v c : Nat) : Prop :=
  Adj (edgeList edges) v c ∧ OnPath (edgeList edges) v c

def IsChain (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∀ v, v < n.val.toNat → ∀ c₁ c₂, Child edges v c₁ → Child edges v c₂ → c₁ = c₂

def IsStar (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∀ v, 1 ≤ v → v < n.val.toNat → Adj (edgeList edges) 0 v

def SameUndirectedTree (edges edges' : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ((edgeList edges).map normEdge).Perm ((edgeList edges').map normEdge)

/-- Let S(v) be the sum of values[u] over all nodes u such that v lies on the unique path from root 0 to u. Call a pair (i,j) admissible when 0 <= i < j < n and the subtrees of i and j are disjoint. Whenever max_xor(n, edges, values) returns a result r, the following hold: (1) for every admissible pair (i,j), r >= S(i) XOR S(j); (2) if at least one admissible pair exists, then some admissible pair (i,j) satisfies r = S(i) XOR S(j); (3) if no admissible pair exists, then r = 0.
  Preconditions: 2 <= n <= 50000; len(edges) = n - 1; len(values) = n; each edges[k] is a vector of length 2, say [a,b], with 0 <= a,b < n; each values[i] satisfies 1 <= values[i] <= 10^9; and the undirected graph with vertices 0,...,n-1 and the edges in edges is a valid tree (connected and acyclic, with no self-loops or duplicate edges). -/
theorem spec_1 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values) {r : Std.I64}
    (hr : max_xor n edges values = ok r) :
    (∀ i j, Admissible n edges i j →
        xorInt (S n edges values i) (S n edges values j) ≤ r.val) ∧
      ((∃ i j, Admissible n edges i j) →
        ∃ i j, Admissible n edges i j ∧
          r.val = xorInt (S n edges values i) (S n edges values j)) ∧
      ((¬ ∃ i j, Admissible n edges i j) → r.val = 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values) {r : Std.I64}
    (hr : max_xor n edges values = ok r), (∀ i j, Admissible n edges i j →
        xorInt (S n edges values i) (S n edges values j) ≤ r.val) ∧
      ((∃ i j, Admissible n edges i j) →
        ∃ i j, Admissible n edges i j ∧
          r.val = xorInt (S n edges values i) (S n edges values j)) ∧
      ((¬ ∃ i j, Admissible n edges i j) → r.val = 0)) := by
  sorry

/-- The call max_xor(n, edges, values) returns a result; it does not fail.
  Preconditions: 2 <= n <= 50000; len(edges) = n - 1; len(values) = n; each edges[k] is a vector of length 2, say [a,b], with 0 <= a,b < n; each values[i] satisfies 1 <= values[i] <= 10^9; and the undirected graph with vertices 0,...,n-1 and the edges in edges is a valid tree (connected and acyclic, with no self-loops or duplicate edges). -/
theorem spec_2 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values) :
    ∃ r : Std.I64, max_xor n edges values = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values), ∃ r : Std.I64, max_xor n edges values = ok r) := by
  sorry

/-- Let S(v) be the sum of values[u] over all u such that v lies on the unique path from root 0 to u, and let M = max_{0 <= v < n} S(v). Let K be the least nonnegative integer such that M < 2^K. Whenever max_xor(n, edges, values) returns a result r, 0 <= r < 2^K.
  Preconditions: 2 <= n <= 50000; len(edges) = n - 1; len(values) = n; each edges[k] is a vector of length 2, say [a,b], with 0 <= a,b < n; each values[i] satisfies 1 <= values[i] <= 10^9; and the undirected graph with vertices 0,...,n-1 and the edges in edges is a valid tree (connected and acyclic, with no self-loops or duplicate edges). -/
theorem spec_3 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values) (K : Nat)
    (hK : IsLeastPowAbove (maxS n edges values) K) {r : Std.I64}
    (hr : max_xor n edges values = ok r) :
    0 ≤ r.val ∧ r.val < (2 : Int) ^ K := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values) (K : Nat)
    (hK : IsLeastPowAbove (maxS n edges values) K) {r : Std.I64}
    (hr : max_xor n edges values = ok r), 0 ≤ r.val ∧ r.val < (2 : Int) ^ K) := by
  sorry

/-- Let S(v) be the sum of values[u] over all u such that v lies on the unique path from root 0 to u. Call a pair (i,j) admissible when 0 <= i < j < n and the subtrees of i and j are disjoint. Whenever max_xor(n, edges, values) returns a result r, r = 0 if and only if either no admissible pair exists, or for every admissible pair (i,j) we have S(i) = S(j).
  Preconditions: 2 <= n <= 50000; len(edges) = n - 1; len(values) = n; each edges[k] is a vector of length 2, say [a,b], with 0 <= a,b < n; each values[i] satisfies 1 <= values[i] <= 10^9; and the undirected graph with vertices 0,...,n-1 and the edges in edges is a valid tree (connected and acyclic, with no self-loops or duplicate edges). -/
theorem spec_4 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values) {r : Std.I64}
    (hr : max_xor n edges values = ok r) :
    (r.val = 0 ↔
      ((¬ ∃ i j, Admissible n edges i j) ∨
        (∀ i j, Admissible n edges i j → S n edges values i = S n edges values j))) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values) {r : Std.I64}
    (hr : max_xor n edges values = ok r), (r.val = 0 ↔
      ((¬ ∃ i j, Admissible n edges i j) ∨
        (∀ i j, Admissible n edges i j → S n edges values i = S n edges values j)))) := by
  sorry

/-- Let S(v) be the sum of values[u] over all u such that v lies on the unique path from root 0 to u. Whenever max_xor(n, edges, values) returns a result r, r is the maximum of S(i) XOR S(j) over all pairs 1 <= i < j < n whose subtrees are disjoint, with the convention that this maximum is 0 if there is no such pair.
  Preconditions: 2 <= n <= 50000; len(edges) = n - 1; len(values) = n; each edges[k] is a vector of length 2, say [a,b], with 0 <= a,b < n; each values[i] satisfies 1 <= values[i] <= 10^9; and the undirected graph with vertices 0,...,n-1 and the edges in edges is a valid tree (connected and acyclic, with no self-loops or duplicate edges). -/
theorem spec_5 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values) {r : Std.I64}
    (hr : max_xor n edges values = ok r) :
    (∀ i j, 1 ≤ i → i < j → j < n.val.toNat → SubtreeDisjoint n edges i j →
        xorInt (S n edges values i) (S n edges values j) ≤ r.val) ∧
      ((∃ i j, 1 ≤ i ∧ i < j ∧ j < n.val.toNat ∧ SubtreeDisjoint n edges i j) →
        ∃ i j, 1 ≤ i ∧ i < j ∧ j < n.val.toNat ∧ SubtreeDisjoint n edges i j ∧
          r.val = xorInt (S n edges values i) (S n edges values j)) ∧
      ((¬ ∃ i j, 1 ≤ i ∧ i < j ∧ j < n.val.toNat ∧ SubtreeDisjoint n edges i j) →
        r.val = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values) {r : Std.I64}
    (hr : max_xor n edges values = ok r), (∀ i j, 1 ≤ i → i < j → j < n.val.toNat → SubtreeDisjoint n edges i j →
        xorInt (S n edges values i) (S n edges values j) ≤ r.val) ∧
      ((∃ i j, 1 ≤ i ∧ i < j ∧ j < n.val.toNat ∧ SubtreeDisjoint n edges i j) →
        ∃ i j, 1 ≤ i ∧ i < j ∧ j < n.val.toNat ∧ SubtreeDisjoint n edges i j ∧
          r.val = xorInt (S n edges values i) (S n edges values j)) ∧
      ((¬ ∃ i j, 1 ≤ i ∧ i < j ∧ j < n.val.toNat ∧ SubtreeDisjoint n edges i j) →
        r.val = 0)) := by
  sorry

/-- Whenever max_xor(n, edges, values) returns a result r, if the rooted tree (root 0) is a chain, meaning every node has at most one child where a child is a neighbor farther from 0, then r = 0.
  Preconditions: 2 <= n <= 50000; len(edges) = n - 1; len(values) = n; each edges[k] is a vector of length 2, say [a,b], with 0 <= a,b < n; each values[i] satisfies 1 <= values[i] <= 10^9; and the undirected graph with vertices 0,...,n-1 and the edges in edges is a valid tree (connected and acyclic, with no self-loops or duplicate edges). -/
theorem spec_6 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values) {r : Std.I64}
    (hr : max_xor n edges values = ok r) (hchain : IsChain n edges) :
    r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values) {r : Std.I64}
    (hr : max_xor n edges values = ok r) (hchain : IsChain n edges), r.val = 0) := by
  sorry

/-- Whenever max_xor(n, edges, values) returns a result r, if every node 1,...,n-1 is adjacent to node 0, so the tree is a star centered at 0, then r is the maximum of values[i] XOR values[j] over all 1 <= i < j < n, with the convention that this maximum is 0 when n = 2 because there are no two leaves.
  Preconditions: 2 <= n <= 50000; len(edges) = n - 1; len(values) = n; each edges[k] is a vector of length 2, say [a,b], with 0 <= a,b < n; each values[i] satisfies 1 <= values[i] <= 10^9; and the undirected graph with vertices 0,...,n-1 and the edges in edges is a valid tree (connected and acyclic, with no self-loops or duplicate edges). -/
theorem spec_7 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values) {r : Std.I64}
    (hr : max_xor n edges values = ok r) (hstar : IsStar n edges) :
    (∀ i j, 1 ≤ i → i < j → j < n.val.toNat →
        xorInt (value values i) (value values j) ≤ r.val) ∧
      ((∃ i j, 1 ≤ i ∧ i < j ∧ j < n.val.toNat) →
        ∃ i j, 1 ≤ i ∧ i < j ∧ j < n.val.toNat ∧
          r.val = xorInt (value values i) (value values j)) ∧
      ((¬ ∃ i j, 1 ≤ i ∧ i < j ∧ j < n.val.toNat) → r.val = 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values) {r : Std.I64}
    (hr : max_xor n edges values = ok r) (hstar : IsStar n edges), (∀ i j, 1 ≤ i → i < j → j < n.val.toNat →
        xorInt (value values i) (value values j) ≤ r.val) ∧
      ((∃ i j, 1 ≤ i ∧ i < j ∧ j < n.val.toNat) →
        ∃ i j, 1 ≤ i ∧ i < j ∧ j < n.val.toNat ∧
          r.val = xorInt (value values i) (value values j)) ∧
      ((¬ ∃ i j, 1 ≤ i ∧ i < j ∧ j < n.val.toNat) → r.val = 0)) := by
  sorry

/-- Whenever max_xor(n, edges, values) returns r and max_xor(n, edges', values) returns r', we have r = r'.
  Preconditions: 2 <= n <= 50000; len(edges) = n - 1; len(values) = n; each edges[k] is a vector of length 2, say [a,b], with 0 <= a,b < n; each values[i] satisfies 1 <= values[i] <= 10^9; and the undirected graph with vertices 0,...,n-1 and the edges in edges is a valid tree (connected and acyclic, with no self-loops or duplicate edges). Also edges' is any slice of length n-1 obtained from edges by permuting its entries and independently swapping the two endpoints of any entries, so edges and edges' describe the same undirected tree, and (n, edges', values) also satisfies the same constraints. -/
theorem spec_8 (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values)
    (hwf' : WellFormed n edges' values) (hsame : SameUndirectedTree edges edges')
    {r r' : Std.I64} (hr : max_xor n edges values = ok r)
    (hr' : max_xor n edges' values = ok r') :
    r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values)
    (hwf' : WellFormed n edges' values) (hsame : SameUndirectedTree edges edges')
    {r r' : Std.I64} (hr : max_xor n edges values = ok r)
    (hr' : max_xor n edges' values = ok r'), r = r') := by
  sorry

/-- Let S(v) be the sum of values[u] over all u such that v lies on the unique path from root 0 to u, and let O be the bitwise OR of all S(v) for 0 <= v < n. Whenever max_xor(n, edges, values) returns a result r, r <= O.
  Preconditions: 2 <= n <= 50000; len(edges) = n - 1; len(values) = n; each edges[k] is a vector of length 2, say [a,b], with 0 <= a,b < n; each values[i] satisfies 1 <= values[i] <= 10^9; and the undirected graph with vertices 0,...,n-1 and the edges in edges is a valid tree (connected and acyclic, with no self-loops or duplicate edges). -/
theorem spec_9 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values) {r : Std.I64}
    (hr : max_xor n edges values = ok r) :
    r.val ≤ orS n edges values := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values) {r : Std.I64}
    (hr : max_xor n edges values = ok r), r.val ≤ orS n edges values) := by
  sorry

/-- Let S(v) be the sum of values[u] over all u such that v lies on the unique path from root 0 to u. Call a pair (i,j) admissible when 0 <= i < j < n and the subtrees of i and j are disjoint. Whenever max_xor(n, edges, values) returns a result r, if there exists an admissible pair (i,j) with S(i) != S(j), then r > 0.
  Preconditions: 2 <= n <= 50000; len(edges) = n - 1; len(values) = n; each edges[k] is a vector of length 2, say [a,b], with 0 <= a,b < n; each values[i] satisfies 1 <= values[i] <= 10^9; and the undirected graph with vertices 0,...,n-1 and the edges in edges is a valid tree (connected and acyclic, with no self-loops or duplicate edges). -/
theorem spec_10 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values) {r : Std.I64}
    (hr : max_xor n edges values = ok r)
    (h : ∃ i j, Admissible n edges i j ∧ S n edges values i ≠ S n edges values j) :
    0 < r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (hwf : WellFormed n edges values) {r : Std.I64}
    (hr : max_xor n edges values = ok r)
    (h : ∃ i j, Admissible n edges i j ∧ S n edges values i ≠ S n edges values j), 0 < r.val) := by
  sorry

end AegisSpec.MaxXor
