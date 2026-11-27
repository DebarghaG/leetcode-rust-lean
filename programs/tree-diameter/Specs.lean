import Aegis.TreeDiameter.Code.Funs

/-!
# Specifications of `Aegis.TreeDiameter.tree_diameter`

LeetCode problem `tree-diameter`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.TreeDiameter

def intVals (e : alloc.vec.Vec I64) : List Int := e.val.map (fun x => x.val)

def edgePairs (edges : Slice (alloc.vec.Vec I64)) : List (Int × Int) :=
  edges.val.filterMap (fun e =>
    match intVals e with
    | [a, b] => some (a, b)
    | _ => none)

def HasEdge (edges : Slice (alloc.vec.Vec I64)) (u v : Nat) : Prop :=
  ((u : Int), (v : Int)) ∈ edgePairs edges ∨ ((v : Int), (u : Int)) ∈ edgePairs edges

def Steps (R : Nat → Nat → Prop) : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => R a b ∧ Steps R (b :: rest)

def IsSimplePath (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (vs : List Nat) : Prop :=
  (∀ v ∈ vs, v < n) ∧ vs.Nodup ∧ Steps (HasEdge edges) vs

def IsCycle (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (vs : List Nat) : Prop :=
  3 ≤ vs.length ∧ IsSimplePath edges n vs ∧
    ∃ u v : Nat, vs.head? = some u ∧ vs.getLast? = some v ∧ HasEdge edges u v

def ConnectedGraph (edges : Slice (alloc.vec.Vec I64)) (n : Nat) : Prop :=
  ∀ u v : Nat, u < n → v < n →
    ∃ vs : List Nat,
      vs.head? = some u ∧ vs.getLast? = some v ∧ (∀ w ∈ vs, w < n) ∧ Steps (HasEdge edges) vs

def AcyclicGraph (edges : Slice (alloc.vec.Vec I64)) (n : Nat) : Prop :=
  ¬ ∃ vs : List Nat, IsCycle edges n vs

def IsTree (edges : Slice (alloc.vec.Vec I64)) (n : Nat) : Prop :=
  ConnectedGraph edges n ∧ AcyclicGraph edges n

def NoRepeatedEdges (edges : Slice (alloc.vec.Vec I64)) : Prop :=
  ∀ (i j : Nat) (ei ej : alloc.vec.Vec I64) (a b c d : Int),
    edges.val[i]? = some ei → edges.val[j]? = some ej →
    intVals ei = [a, b] → intVals ej = [c, d] →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) → i = j

def IsTreeInput (edges : Slice (alloc.vec.Vec I64)) (n : Nat) : Prop :=
  edges.val.length + 1 = n ∧ 1 ≤ n ∧ n ≤ 10 ^ 4 ∧
    (∀ (i : Nat) (e : alloc.vec.Vec I64), edges.val[i]? = some e →
      ∃ a b : Int,
        intVals e = [a, b] ∧ 0 ≤ a ∧ a < (n : Int) ∧ 0 ≤ b ∧ b < (n : Int) ∧ a ≠ b) ∧
    NoRepeatedEdges edges ∧ IsTree edges n

def Degree (edges : Slice (alloc.vec.Vec I64)) (v : Nat) : Nat :=
  (edgePairs edges).countP (fun p => p.1 == (v : Int) || p.2 == (v : Int))

def PathLenFromTo (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (u v : Nat) (k : Int) : Prop :=
  ∃ vs : List Nat,
    IsSimplePath edges n vs ∧ vs.head? = some u ∧ vs.getLast? = some v ∧
      (vs.length : Int) = k + 1

def IsDist (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (u v : Nat) (k : Int) : Prop :=
  PathLenFromTo edges n u v k ∧ ∀ k' : Int, PathLenFromTo edges n u v k' → k' = k

def IsDiameter (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (k : Int) : Prop :=
  0 ≤ k ∧
    (∃ vs : List Nat, IsSimplePath edges n vs ∧ (vs.length : Int) = k + 1) ∧
    ∀ (j : Int) (vs : List Nat), IsSimplePath edges n vs → (vs.length : Int) = j + 1 → j ≤ k

/-- Let n = len(edges)+1. The function returns a result r, and r is the diameter of G: the largest integer k >= 0 for which there exists a sequence of vertices v_0, v_1, ..., v_k such that each v_j is in [0,n), the vertices v_0,...,v_k are pairwise distinct, and for every j with 0 <= j < k the unordered pair {v_j, v_{j+1}} is one of the input edges. For k=0 this is a single vertex and has length 0.
  Preconditions: Let n = len(edges)+1. For every i with 0 <= i < len(edges), edges[i] has length 2, its entries edges[i][0] and edges[i][1] are integers with 0 <= edges[i][0] < n and 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]. The undirected graph G with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) } is a simple tree: it is connected and acyclic. Also 1 <= n <= 10^4. -/
theorem spec_1 (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n) :
    ∃ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r ∧ IsDiameter edges n r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n), ∃ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r ∧ IsDiameter edges n r.val) := by
  sorry

/-- For every input satisfying the preconditions, tree_diameter(edges) returns a result r; it does not overflow, panic, or otherwise fail.
  Preconditions: Let n = len(edges)+1. For every i with 0 <= i < len(edges), edges[i] has length 2, its entries edges[i][0] and edges[i][1] are integers with 0 <= edges[i][0] < n and 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]. The undirected graph G with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) } is a simple tree: it is connected and acyclic. Also 1 <= n <= 10^4. -/
theorem spec_2 (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n) :
    ∃ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n), ∃ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r) := by
  sorry

/-- Whenever tree_diameter(edges) returns a result r, 0 <= r <= len(edges). Equivalently, 0 <= r <= n-1.
  Preconditions: Let n = len(edges)+1. For every i with 0 <= i < len(edges), edges[i] has length 2, its entries edges[i][0] and edges[i][1] are integers with 0 <= edges[i][0] < n and 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]. The undirected graph G with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) } is a simple tree: it is connected and acyclic. Also 1 <= n <= 10^4. -/
theorem spec_3 (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n) :
    ∀ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r →
      0 ≤ r.val ∧ r.val ≤ (edges.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n), ∀ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r →
      0 ≤ r.val ∧ r.val ≤ (edges.val.length : Int)) := by
  sorry

/-- Whenever tree_diameter(edges) returns a result r, r >= 0 and there exist vertices v_0,...,v_r, pairwise distinct and all in [0,n), such that for every j with 0 <= j < r the unordered pair {v_j, v_{j+1}} is an input edge. Thus a path of length r is realized in G.
  Preconditions: Let n = len(edges)+1. For every i with 0 <= i < len(edges), edges[i] has length 2, its entries edges[i][0] and edges[i][1] are integers with 0 <= edges[i][0] < n and 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]. The undirected graph G with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) } is a simple tree: it is connected and acyclic. Also 1 <= n <= 10^4. -/
theorem spec_4 (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n) :
    ∀ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r →
      0 ≤ r.val ∧
        ∃ vs : List Nat, IsSimplePath edges n vs ∧ (vs.length : Int) = r.val + 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n), ∀ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r →
      0 ≤ r.val ∧
        ∃ vs : List Nat, IsSimplePath edges n vs ∧ (vs.length : Int) = r.val + 1) := by
  sorry

/-- Whenever tree_diameter(edges) returns a result r, for every integer k >= 0 and every sequence v_0,...,v_k of pairwise distinct vertices in [0,n) such that each consecutive unordered pair {v_j, v_{j+1}} with 0 <= j < k is an input edge, we have k <= r. Thus no simple path in G has more than r edges.
  Preconditions: Let n = len(edges)+1. For every i with 0 <= i < len(edges), edges[i] has length 2, its entries edges[i][0] and edges[i][1] are integers with 0 <= edges[i][0] < n and 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]. The undirected graph G with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) } is a simple tree: it is connected and acyclic. Also 1 <= n <= 10^4. -/
theorem spec_5 (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n) :
    ∀ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r →
      ∀ (k : Nat) (vs : List Nat), IsSimplePath edges n vs → vs.length = k + 1 →
        (k : Int) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n), ∀ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r →
      ∀ (k : Nat) (vs : List Nat), IsSimplePath edges n vs → vs.length = k + 1 →
        (k : Int) ≤ r.val) := by
  sorry

/-- Whenever tree_diameter(edges) returns a result r, r = 0 if and only if len(edges) = 0 (equivalently, n = 1).
  Preconditions: Let n = len(edges)+1. For every i with 0 <= i < len(edges), edges[i] has length 2, its entries edges[i][0] and edges[i][1] are integers with 0 <= edges[i][0] < n and 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]. The undirected graph G with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) } is a simple tree: it is connected and acyclic. Also 1 <= n <= 10^4. -/
theorem spec_6 (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n) :
    ∀ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r →
      (r.val = 0 ↔ edges.val.length = 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n), ∀ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r →
      (r.val = 0 ↔ edges.val.length = 0)) := by
  sorry

/-- Whenever tree_diameter(edges) returns a result r, if every vertex v in [0,n) has degree at most 2 in G, where the degree is the number of input edges incident to v, then r = len(edges).
  Preconditions: Let n = len(edges)+1. For every i with 0 <= i < len(edges), edges[i] has length 2, its entries edges[i][0] and edges[i][1] are integers with 0 <= edges[i][0] < n and 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]. The undirected graph G with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) } is a simple tree: it is connected and acyclic. Also 1 <= n <= 10^4. -/
theorem spec_7 (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n) :
    ∀ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r →
      (∀ v : Nat, v < n → Degree edges v ≤ 2) → r.val = (edges.val.length : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n), ∀ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r →
      (∀ v : Nat, v < n → Degree edges v ≤ 2) → r.val = (edges.val.length : Int)) := by
  sorry

/-- Whenever tree_diameter(edges) returns a result r, if n >= 3 and there exists a vertex c in [0,n) such that for every vertex v in [0,n) with v != c the unordered pair {c,v} is an input edge, then r = 2.
  Preconditions: Let n = len(edges)+1. For every i with 0 <= i < len(edges), edges[i] has length 2, its entries edges[i][0] and edges[i][1] are integers with 0 <= edges[i][0] < n and 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]. The undirected graph G with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) } is a simple tree: it is connected and acyclic. Also 1 <= n <= 10^4. -/
theorem spec_8 (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n) :
    ∀ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r → 3 ≤ n →
      (∃ c : Nat, c < n ∧ ∀ v : Nat, v < n → v ≠ c → HasEdge edges c v) → r.val = 2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n), ∀ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r → 3 ≤ n →
      (∃ c : Nat, c < n ∧ ∀ v : Nat, v < n → v ≠ c → HasEdge edges c v) → r.val = 2) := by
  sorry

/-- Whenever tree_diameter(edges) returns r and tree_diameter(edges') returns r', we have r = r'. Thus the result depends only on the undirected graph, not on the order of the edge list or on the orientation of individual edges.
  Preconditions: Let n = len(edges)+1 = len(edges')+1. Both edges and edges' satisfy the same tree preconditions: each edge vector has length 2, entries are in [0,n), the two entries differ, and the undirected graph represented by each is a simple tree on vertices 0,...,n-1. Additionally, the two slices represent the same undirected graph: for every unordered pair {u,v} of distinct vertices in [0,n), {u,v} occurs as an input edge of edges if and only if it occurs as an input edge of edges'. -/
theorem spec_9 (edges edges' : Slice (alloc.vec.Vec I64)) (n : Nat)
    (h : IsTreeInput edges n) (h' : IsTreeInput edges' n)
    (hsame : ∀ u v : Nat, u < n → v < n → u ≠ v → (HasEdge edges u v ↔ HasEdge edges' u v)) :
    ∀ r r' : I64, Aegis.TreeDiameter.tree_diameter edges = ok r →
      Aegis.TreeDiameter.tree_diameter edges' = ok r' → r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (edges edges' : Slice (alloc.vec.Vec I64)) (n : Nat)
    (h : IsTreeInput edges n) (h' : IsTreeInput edges' n)
    (hsame : ∀ u v : Nat, u < n → v < n → u ≠ v → (HasEdge edges u v ↔ HasEdge edges' u v)), ∀ r r' : I64, Aegis.TreeDiameter.tree_diameter edges = ok r →
      Aegis.TreeDiameter.tree_diameter edges' = ok r' → r = r') := by
  sorry

/-- Whenever tree_diameter(edges) returns r and tree_diameter(edges') returns r', we have r = r'. Thus the diameter is invariant under relabeling of the tree vertices.
  Preconditions: Let n = len(edges)+1. The slice edges satisfies the tree preconditions: each edge vector has length 2, entries are in [0,n), the two entries differ, and the undirected graph G represented by edges is a simple tree on vertices 0,...,n-1. Let f be a bijection from {0,1,...,n-1} to itself, and let edges' be a slice with len(edges') = len(edges) such that edges'[i] = [f(edges[i][0]), f(edges[i][1])] for every i with 0 <= i < len(edges). -/
theorem spec_10 (edges edges' : Slice (alloc.vec.Vec I64)) (n : Nat) (f : Nat → Nat)
    (h : IsTreeInput edges n)
    (hbij : ∀ u : Nat, u < n → f u < n)
    (hinj : ∀ u v : Nat, u < n → v < n → f u = f v → u = v)
    (hlen : edges'.val.length = edges.val.length)
    (hedges' : ∀ (i : Nat) (e e' : alloc.vec.Vec I64),
      edges.val[i]? = some e → edges'.val[i]? = some e' →
        intVals e' = (intVals e).map (fun a => (f a.toNat : Int))) :
    ∀ r r' : I64, Aegis.TreeDiameter.tree_diameter edges = ok r →
      Aegis.TreeDiameter.tree_diameter edges' = ok r' → r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (edges edges' : Slice (alloc.vec.Vec I64)) (n : Nat) (f : Nat → Nat)
    (h : IsTreeInput edges n)
    (hbij : ∀ u : Nat, u < n → f u < n)
    (hinj : ∀ u v : Nat, u < n → v < n → f u = f v → u = v)
    (hlen : edges'.val.length = edges.val.length)
    (hedges' : ∀ (i : Nat) (e e' : alloc.vec.Vec I64),
      edges.val[i]? = some e → edges'.val[i]? = some e' →
        intVals e' = (intVals e).map (fun a => (f a.toNat : Int))), ∀ r r' : I64, Aegis.TreeDiameter.tree_diameter edges = ok r →
      Aegis.TreeDiameter.tree_diameter edges' = ok r' → r = r') := by
  sorry

/-- Whenever tree_diameter(edges) returns a result r, if n >= 2 then there exist two distinct vertices u and v in [0,n), each of degree 1 in G (incident to exactly one input edge), such that the unique simple path between u and v in G has exactly r edges.
  Preconditions: Let n = len(edges)+1. For every i with 0 <= i < len(edges), edges[i] has length 2, its entries edges[i][0] and edges[i][1] are integers with 0 <= edges[i][0] < n and 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]. The undirected graph G with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) } is a simple tree: it is connected and acyclic. Also 1 <= n <= 10^4. -/
theorem spec_11 (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n) :
    ∀ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r → 2 ≤ n →
      ∃ u v : Nat, u < n ∧ v < n ∧ u ≠ v ∧ Degree edges u = 1 ∧ Degree edges v = 1 ∧
        IsDist edges n u v r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n), ∀ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r → 2 ≤ n →
      ∃ u v : Nat, u < n ∧ v < n ∧ u ≠ v ∧ Degree edges u = 1 ∧ Degree edges v = 1 ∧
        IsDist edges n u v r.val) := by
  sorry

/-- Whenever tree_diameter(edges) returns a result r, define d(u,v), for u and v in [0,n), to be the number of edges on the unique simple path from u to v in G, with d(v,v)=0. Then r = max_{v in [0,n)} max_{u in [0,n)} d(v,u).
  Preconditions: Let n = len(edges)+1. For every i with 0 <= i < len(edges), edges[i] has length 2, its entries edges[i][0] and edges[i][1] are integers with 0 <= edges[i][0] < n and 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]. The undirected graph G with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) } is a simple tree: it is connected and acyclic. Also 1 <= n <= 10^4. -/
theorem spec_12 (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n) :
    ∀ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r →
      (∀ (u v : Nat) (k : Int), u < n → v < n → IsDist edges n u v k → k ≤ r.val) ∧
        (∃ (u v : Nat) (k : Int), u < n ∧ v < n ∧ IsDist edges n u v k ∧ k = r.val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (h : IsTreeInput edges n), ∀ r : I64, Aegis.TreeDiameter.tree_diameter edges = ok r →
      (∀ (u v : Nat) (k : Int), u < n → v < n → IsDist edges n u v k → k ≤ r.val) ∧
        (∃ (u v : Nat) (k : Int), u < n ∧ v < n ∧ IsDist edges n u v k ∧ k = r.val)) := by
  sorry

end AegisSpec.TreeDiameter
