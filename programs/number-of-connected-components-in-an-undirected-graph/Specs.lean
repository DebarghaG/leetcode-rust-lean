import Aegis.CountComponents.Code.Funs

/-!
# Specifications of `Aegis.CountComponents.count_components`

LeetCode problem `number-of-connected-components-in-an-undirected-graph`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountComponents
open Classical

namespace AegisSpec.CountComponents

def edgeAt? (edges : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : Option (ℤ × ℤ) :=
  match edges.val[i]? with
  | some v =>
    match v.val with
    | [x, y] => some (x.val, y.val)
    | _ => none
  | none => none

def IsEdgeOf (edges : Slice (alloc.vec.Vec Std.I64)) (u v : ℤ) : Prop :=
  ∃ i, i < edges.val.length ∧ edgeAt? edges i = some (min u v, max u v)

def Connected (edges : Slice (alloc.vec.Vec Std.I64)) : ℤ → ℤ → Prop :=
  Relation.ReflTransGen (fun u v => IsEdgeOf edges u v)

def Incident (edges : Slice (alloc.vec.Vec Std.I64)) (v : ℤ) : Prop :=
  ∃ u : ℤ, IsEdgeOf edges u v

def IsComponentRep (n : ℤ) (edges : Slice (alloc.vec.Vec Std.I64)) (v : ℤ) : Prop :=
  0 ≤ v ∧ v < n ∧ ∀ u : ℤ, 0 ≤ u → u < n → Connected edges u v → v ≤ u

noncomputable def numComponents (n : ℤ) (edges : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
  ((Finset.range n.toNat).filter (fun k : ℕ => IsComponentRep n edges (k : ℤ))).card

noncomputable def isolatedCount (n : ℤ) (edges : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
  ((Finset.range n.toNat).filter (fun k : ℕ => ¬ Incident edges (k : ℤ))).card

def IsVertexPerm (n : ℤ) (pi : ℤ → ℤ) : Prop :=
  (∀ v : ℤ, 0 ≤ v → v < n → 0 ≤ pi v ∧ pi v < n) ∧
  (∀ v u : ℤ, 0 ≤ v → v < n → 0 ≤ u → u < n → pi v = pi u → v = u) ∧
  (∀ u : ℤ, 0 ≤ u → u < n → ∃ v : ℤ, 0 ≤ v ∧ v < n ∧ pi v = u)

def IsIndexPerm (len : ℕ) (f : ℕ → ℕ) : Prop :=
  (∀ j, j < len → f j < len) ∧
  (∀ i j, i < len → j < len → f i = f j → i = j) ∧
  (∀ i, i < len → ∃ j, j < len ∧ f j = i)

def cycSucc {k : ℕ} (j : Fin k) : Fin k :=
  ⟨(j.val + 1) % k, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt)⟩

def IsSimpleCycle (edges : Slice (alloc.vec.Vec Std.I64)) (k : ℕ) (v : Fin k → ℤ) : Prop :=
  3 ≤ k ∧ Function.Injective v ∧ ∀ j : Fin k, IsEdgeOf edges (v j) (v (cycSucc j))

def HasCycle (edges : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∃ (k : ℕ) (v : Fin k → ℤ), IsSimpleCycle edges k v

/-- Whenever count_components n edges returns Result.ok r, r is the number of connected components of the undirected graph G whose vertex set is {0,1,...,n-1} and whose edge set consists exactly of the unordered pairs {edges[i][0], edges[i][1]} for 0 <= i < len(edges). Equivalently, define u ~ v for vertices u and v to mean that u = v or there is a finite sequence of vertices u = w0, w1, ..., wk = v with k >= 0 such that for every j with 0 <= j < k the unordered pair {wj, wj+1} is one of the listed edge pairs; then r is the number of equivalence classes of ~.
  Preconditions: 1 <= n <= 2000 and 1 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and there are no repeated edges: for all i and j with 0 <= i < j < len(edges), not (edges[i][0] = edges[j][0] and edges[i][1] = edges[j][1]). -/
theorem spec_1 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j) :
    count_components n edges = ok r → r.val = (numComponents n.val edges : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j), count_components n edges = ok r → r.val = (numComponents n.val edges : ℤ)) := by
  sorry

/-- For every n and edges satisfying the preconditions, count_components n edges returns a result: there exists an integer r such that the call evaluates to Result.ok r. In particular, on all stated valid inputs the function does not fail, panic, overflow, or access memory out of bounds.
  Preconditions: 1 <= n <= 2000 and 1 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and there are no repeated edges: for all i and j with 0 <= i < j < len(edges), not (edges[i][0] = edges[j][0] and edges[i][1] = edges[j][1]). -/
theorem spec_2 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j) :
    ∃ r : Std.I64, count_components n edges = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j), ∃ r : Std.I64, count_components n edges = ok r) := by
  sorry

/-- Whenever count_components n edges returns Result.ok r, 1 <= r <= n.
  Preconditions: 1 <= n <= 2000 and 1 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and there are no repeated edges: for all i and j with 0 <= i < j < len(edges), not (edges[i][0] = edges[j][0] and edges[i][1] = edges[j][1]). -/
theorem spec_3 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j) :
    count_components n edges = ok r → 1 ≤ r.val ∧ r.val ≤ n.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j), count_components n edges = ok r → 1 ≤ r.val ∧ r.val ≤ n.val) := by
  sorry

/-- Whenever count_components n edges returns Result.ok r, r >= 1 and r >= n - len(edges); equivalently, r >= max(1, n - len(edges)).
  Preconditions: 1 <= n <= 2000 and 1 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and there are no repeated edges: for all i and j with 0 <= i < j < len(edges), not (edges[i][0] = edges[j][0] and edges[i][1] = edges[j][1]). -/
theorem spec_4 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j) :
    count_components n edges = ok r →
      1 ≤ r.val ∧ n.val - (edges.val.length : ℤ) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j), count_components n edges = ok r →
      1 ≤ r.val ∧ n.val - (edges.val.length : ℤ) ≤ r.val) := by
  sorry

/-- Whenever count_components n edges returns Result.ok r, r = 1 if and only if every two vertices u and v with 0 <= u < v < n are connected in G by a path using the listed undirected edges; equivalently, r = 1 exactly when the graph has a single connected component containing all n vertices.
  Preconditions: 1 <= n <= 2000 and 1 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and there are no repeated edges: for all i and j with 0 <= i < j < len(edges), not (edges[i][0] = edges[j][0] and edges[i][1] = edges[j][1]). -/
theorem spec_5 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j) :
    count_components n edges = ok r →
      (r.val = 1 ↔ ∀ u v : ℤ, 0 ≤ u → u < v → v < n.val → Connected edges u v) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j), count_components n edges = ok r →
      (r.val = 1 ↔ ∀ u v : ℤ, 0 ≤ u → u < v → v < n.val → Connected edges u v)) := by
  sorry

/-- Whenever count_components n edges returns Result.ok r, r = n - len(edges).
  Preconditions: 1 <= n <= 2000 and 1 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and there are no repeated edges: for all i and j with 0 <= i < j < len(edges), not (edges[i][0] = edges[j][0] and edges[i][1] = edges[j][1]). Additionally, the graph G is acyclic: there is no integer k >= 3 and no k distinct vertices v0, v1, ..., v_{k-1} such that all unordered pairs {v0,v1}, {v1,v2}, ..., {v_{k-2},v_{k-1}}, {v_{k-1},v0} occur among the listed edge pairs. -/
theorem spec_6 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j)
    (hacyc : ¬ HasCycle edges) :
    count_components n edges = ok r → r.val = n.val - (edges.val.length : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j)
    (hacyc : ¬ HasCycle edges), count_components n edges = ok r → r.val = n.val - (edges.val.length : ℤ)) := by
  sorry

/-- Whenever count_components n edges returns Result.ok r and count_components n edges' returns Result.ok r', we have r' = r.
  Preconditions: 1 <= n <= 2000 and 1 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and there are no repeated edges: for all i and j with 0 <= i < j < len(edges), not (edges[i][0] = edges[j][0] and edges[i][1] = edges[j][1]). Also, 0 <= a < b < n, len(edges) < 5000, vertices a and b are connected in G by a path using the listed undirected edges, and the unordered pair {a,b} is not one of the listed edge pairs. Let edges' be the slice obtained by appending one vector [a,b] to edges. -/
theorem spec_7 (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (a b r r' : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ x y : ℤ, edgeAt? edges i = some (x, y) ∧ 0 ≤ x ∧ x ≤ y ∧ y < n.val ∧ x ≠ y)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j)
    (ha : 0 ≤ a.val) (hab : a.val < b.val) (hb : b.val < n.val)
    (hlen : edges.val.length < 5000)
    (hconn : Connected edges a.val b.val)
    (hnot : ¬ IsEdgeOf edges a.val b.val)
    (happ : ∃ v : alloc.vec.Vec Std.I64, v.val = [a, b] ∧ edges'.val = edges.val ++ [v]) :
    count_components n edges = ok r →
      count_components n edges' = ok r' → r'.val = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (a b r r' : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ x y : ℤ, edgeAt? edges i = some (x, y) ∧ 0 ≤ x ∧ x ≤ y ∧ y < n.val ∧ x ≠ y)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j)
    (ha : 0 ≤ a.val) (hab : a.val < b.val) (hb : b.val < n.val)
    (hlen : edges.val.length < 5000)
    (hconn : Connected edges a.val b.val)
    (hnot : ¬ IsEdgeOf edges a.val b.val)
    (happ : ∃ v : alloc.vec.Vec Std.I64, v.val = [a, b] ∧ edges'.val = edges.val ++ [v]), count_components n edges = ok r →
      count_components n edges' = ok r' → r'.val = r.val) := by
  sorry

/-- Whenever count_components n edges returns Result.ok r and count_components n edges' returns Result.ok r', we have r' = r - 1.
  Preconditions: 1 <= n <= 2000 and 1 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and there are no repeated edges: for all i and j with 0 <= i < j < len(edges), not (edges[i][0] = edges[j][0] and edges[i][1] = edges[j][1]). Also, 0 <= a < b < n, len(edges) < 5000, and vertices a and b are not connected in G by any path using the listed undirected edges. Let edges' be the slice obtained by appending one vector [a,b] to edges. -/
theorem spec_8 (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (a b r r' : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ x y : ℤ, edgeAt? edges i = some (x, y) ∧ 0 ≤ x ∧ x ≤ y ∧ y < n.val ∧ x ≠ y)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j)
    (ha : 0 ≤ a.val) (hab : a.val < b.val) (hb : b.val < n.val)
    (hlen : edges.val.length < 5000)
    (hnotconn : ¬ Connected edges a.val b.val)
    (happ : ∃ v : alloc.vec.Vec Std.I64, v.val = [a, b] ∧ edges'.val = edges.val ++ [v]) :
    count_components n edges = ok r →
      count_components n edges' = ok r' → r'.val = r.val - 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (a b r r' : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ x y : ℤ, edgeAt? edges i = some (x, y) ∧ 0 ≤ x ∧ x ≤ y ∧ y < n.val ∧ x ≠ y)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j)
    (ha : 0 ≤ a.val) (hab : a.val < b.val) (hb : b.val < n.val)
    (hlen : edges.val.length < 5000)
    (hnotconn : ¬ Connected edges a.val b.val)
    (happ : ∃ v : alloc.vec.Vec Std.I64, v.val = [a, b] ∧ edges'.val = edges.val ++ [v]), count_components n edges = ok r →
      count_components n edges' = ok r' → r'.val = r.val - 1) := by
  sorry

/-- Let edges' be any slice with len(edges') = len(edges) such that there exists a bijection f from {0,...,len(edges)-1} to itself with edges'[j] = edges[f(j)] for every j with 0 <= j < len(edges). Whenever count_components n edges returns Result.ok r and count_components n edges' returns Result.ok r', we have r' = r.
  Preconditions: 1 <= n <= 2000 and 1 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and there are no repeated edges: for all i and j with 0 <= i < j < len(edges), not (edges[i][0] = edges[j][0] and edges[i][1] = edges[j][1]). -/
theorem spec_9 (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64)) (r r' : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j)
    (hlen : edges'.val.length = edges.val.length)
    (hperm : ∃ f : ℕ → ℕ, IsIndexPerm edges.val.length f ∧
      ∀ j, j < edges'.val.length → edges'.val[j]? = edges.val[f j]?) :
    count_components n edges = ok r →
      count_components n edges' = ok r' → r'.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64)) (r r' : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j)
    (hlen : edges'.val.length = edges.val.length)
    (hperm : ∃ f : ℕ → ℕ, IsIndexPerm edges.val.length f ∧
      ∀ j, j < edges'.val.length → edges'.val[j]? = edges.val[f j]?), count_components n edges = ok r →
      count_components n edges' = ok r' → r'.val = r.val) := by
  sorry

/-- Let pi be any bijection from {0,1,...,n-1} to itself. Form edges' by replacing, for each i, the edge vector [a,b] = [edges[i][0], edges[i][1]] with [min(pi(a),pi(b)), max(pi(a),pi(b))] at the same index i. Whenever count_components n edges returns Result.ok r and count_components n edges' returns Result.ok r', we have r' = r.
  Preconditions: 1 <= n <= 2000 and 1 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and there are no repeated edges: for all i and j with 0 <= i < j < len(edges), not (edges[i][0] = edges[j][0] and edges[i][1] = edges[j][1]). -/
theorem spec_10 (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (pi : ℤ → ℤ) (r r' : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j)
    (hpi : IsVertexPerm n.val pi)
    (hlen : edges'.val.length = edges.val.length)
    (hmap : ∀ i, i < edges.val.length → ∀ a b : ℤ, edgeAt? edges i = some (a, b) →
      edgeAt? edges' i = some (min (pi a) (pi b), max (pi a) (pi b))) :
    count_components n edges = ok r →
      count_components n edges' = ok r' → r'.val = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (pi : ℤ → ℤ) (r r' : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j)
    (hpi : IsVertexPerm n.val pi)
    (hlen : edges'.val.length = edges.val.length)
    (hmap : ∀ i, i < edges.val.length → ∀ a b : ℤ, edgeAt? edges i = some (a, b) →
      edgeAt? edges' i = some (min (pi a) (pi b), max (pi a) (pi b))), count_components n edges = ok r →
      count_components n edges' = ok r' → r'.val = r.val) := by
  sorry

/-- Let I be the number of vertices v with 0 <= v < n such that for every i with 0 <= i < len(edges), v != edges[i][0] and v != edges[i][1]. Whenever count_components n edges returns Result.ok r, r >= I + 1.
  Preconditions: 1 <= n <= 2000 and 1 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and there are no repeated edges: for all i and j with 0 <= i < j < len(edges), not (edges[i][0] = edges[j][0] and edges[i][1] = edges[j][1]). -/
theorem spec_11 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j) :
    count_components n edges = ok r →
      (isolatedCount n.val edges : ℤ) + 1 ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j), count_components n edges = ok r →
      (isolatedCount n.val edges : ℤ) + 1 ≤ r.val) := by
  sorry

/-- Let I be the number of vertices v with 0 <= v < n such that for every i with 0 <= i < len(edges), v != edges[i][0] and v != edges[i][1]. Whenever count_components n edges returns Result.ok r, r <= I + floor((n - I)/2), where floor denotes the greatest integer not exceeding (n-I)/2.
  Preconditions: 1 <= n <= 2000 and 1 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and there are no repeated edges: for all i and j with 0 <= i < j < len(edges), not (edges[i][0] = edges[j][0] and edges[i][1] = edges[j][1]). -/
theorem spec_12 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j) :
    count_components n edges = ok r →
      r.val ≤ ((isolatedCount n.val edges + (n.val.toNat - isolatedCount n.val edges) / 2 : ℕ)
        : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2000)
    (he1 : 1 ≤ edges.val.length) (he2 : edges.val.length ≤ 5000)
    (hshape : ∀ i, i < edges.val.length →
      ∃ a b : ℤ, edgeAt? edges i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b < n.val ∧ a ≠ b)
    (hnorep : ∀ i j, i < j → j < edges.val.length → edgeAt? edges i ≠ edgeAt? edges j), count_components n edges = ok r →
      r.val ≤ ((isolatedCount n.val edges + (n.val.toNat - isolatedCount n.val edges) / 2 : ℕ)
        : ℤ)) := by
  sorry

end AegisSpec.CountComponents
