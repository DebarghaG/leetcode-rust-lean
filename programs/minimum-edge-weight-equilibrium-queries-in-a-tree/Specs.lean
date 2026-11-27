import Aegis.MinOperationsQueries.Code.Funs

/-!
# Specifications of `Aegis.MinOperationsQueries.min_operations_queries`

LeetCode problem `minimum-edge-weight-equilibrium-queries-in-a-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Classical
open Aegis.MinOperationsQueries

namespace AegisSpec.MinOperationsQueries

noncomputable section

abbrev IntVec := alloc.vec.Vec I64

structure Edge where

  u : ℤ

  v : ℤ

  w : ℤ

def Joins (e : Edge) (x y : ℤ) : Prop :=
  (e.u = x ∧ e.v = y) ∨ (e.u = y ∧ e.v = x)

def findEdge? (g : List Edge) (x y : ℤ) : Option Edge :=
  g.find? fun e => (e.u == x && e.v == y) || (e.u == y && e.v == x)

def toEdges (edges : List IntVec) : List Edge :=
  edges.map fun e =>
    ⟨(e.val.getD 0 0#i64).val, (e.val.getD 1 0#i64).val, (e.val.getD 2 0#i64).val⟩

def queryAt (queries : Slice IntVec) (j : ℕ) : Option (ℤ × ℤ) :=
  match queries.val[j]? with
  | none => none
  | some q =>
    match q.val with
    | [a, b] => some (a.val, b.val)
    | _ => none

def ansAt (r : IntVec) (j : ℕ) : Option ℤ := (r.val[j]?).map fun x => x.val

def Adj (g : List Edge) (x y : ℤ) : Prop := ∃ e ∈ g, Joins e x y

def Reach (g : List Edge) (x y : ℤ) : Prop := Relation.ReflTransGen (Adj g) x y

def IsWalk (g : List Edge) (vs : List ℤ) : Prop :=
  ∀ q ∈ vs.zip vs.tail, Adj g q.1 q.2

def IsSimplePath (g : List Edge) (a b : ℤ) (vs : List ℤ) : Prop :=
  vs.head? = some a ∧ vs.getLast? = some b ∧ vs.Nodup ∧ IsWalk g vs

def IsTree (n : ℤ) (g : List Edge) : Prop :=
  (∀ e ∈ g, e.u ≠ e.v) ∧
    (∀ a b : ℤ, 0 ≤ a → a < n → 0 ≤ b → b < n → ∃ vs : List ℤ, IsSimplePath g a b vs) ∧
    (∀ (a b : ℤ) (vs ws : List ℤ), IsSimplePath g a b vs → IsSimplePath g a b ws → vs = ws)

def pathWeightsOf (g : List Edge) (vs : List ℤ) : List ℤ :=
  (vs.zip vs.tail).filterMap fun q => (findEdge? g q.1 q.2).map fun e => e.w

def someSimplePath (g : List Edge) (a b : ℤ) : List ℤ :=
  if h : ∃ vs, IsSimplePath g a b vs then Classical.choose h else []

def pathWeightsList (g : List Edge) (a b : ℤ) : List ℤ :=
  pathWeightsOf g (someSimplePath g a b)

def E (edges : Slice IntVec) (a b : ℤ) : List ℤ := pathWeightsList (toEdges edges.val) a b

def cnt (edges : Slice IntVec) (a b w : ℤ) : ℕ := (E edges a b).count w

def maxCnt (edges : Slice IntVec) (a b : ℤ) : ℕ :=
  ((List.range 26).map fun i => cnt edges a b ((i : ℤ) + 1)).foldr max 0

def numDistinct (edges : Slice IntVec) (a b : ℤ) : ℕ := (E edges a b).dedup.length

def SubMultiset (l₁ l₂ : List ℤ) : Prop := ∀ w : ℤ, l₁.count w ≤ l₂.count w

def EdgesWellFormed (n : ℤ) (edges : Slice IntVec) : Prop :=
  ∀ e ∈ edges.val, ∃ u v w : I64,
    e.val = [u, v, w] ∧
      0 ≤ u.val ∧ u.val < n ∧ 0 ≤ v.val ∧ v.val < n ∧ 1 ≤ w.val ∧ w.val ≤ 26

def QueriesWellFormed (n : ℤ) (queries : Slice IntVec) : Prop :=
  ∀ q ∈ queries.val, ∃ a b : I64, q.val = [a, b] ∧ 0 ≤ a.val ∧ a.val < n ∧ 0 ≤ b.val ∧ b.val < n

/-- Whenever min_operations_queries returns a result r, for every index j with 0 <= j < len(queries), writing queries[j] = [a_j, b_j], we have r[j] = |E(a_j,b_j)| - max_{1 <= w <= 26} cnt(a_j,b_j,w), where E(a,b) is the multiset of weights of the edges on the unique simple path from a to b in the given tree (E(a,a) is empty), and cnt(a,b,w) is the number of occurrences of weight w in E(a,b). Equivalently, r[j] is the minimum number of edge-weight changes needed so that all edges on the path from a_j to b_j have one common weight.
  Preconditions: n is an integer with 1 <= n; len(edges) = n - 1; each edges[i] has length 3, and if edges[i] = [u_i, v_i, w_i] then 0 <= u_i, v_i < n and 1 <= w_i <= 26; the undirected graph on vertices 0..n-1 with these edges is a tree. Also len(queries) = m with m >= 1; each queries[j] has length 2, and if queries[j] = [a_j, b_j] then 0 <= a_j, b_j < n. -/
theorem spec_1 (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r) :
    ∀ (j : ℕ), j < queries.val.length → ∀ (a b x : ℤ),
      queryAt queries j = some (a, b) → ansAt r j = some x →
      x = ((E edges a b).length : ℤ) - (maxCnt edges a b : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r), ∀ (j : ℕ), j < queries.val.length → ∀ (a b x : ℤ),
      queryAt queries j = some (a, b) → ansAt r j = some x →
      x = ((E edges a b).length : ℤ) - (maxCnt edges a b : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, min_operations_queries returns a result r; it does not fail through arithmetic overflow, out-of-bounds indexing, or panic.
  Preconditions: n is an integer with 1 <= n; len(edges) = n - 1; each edges[i] has length 3, and if edges[i] = [u_i, v_i, w_i] then 0 <= u_i, v_i < n and 1 <= w_i <= 26; the undirected graph on vertices 0..n-1 with these edges is a tree. Also len(queries) = m with m >= 1; each queries[j] has length 2, and if queries[j] = [a_j, b_j] then 0 <= a_j, b_j < n. -/
theorem spec_2 (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries) :
    ∃ r : IntVec, min_operations_queries n edges queries = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries), ∃ r : IntVec, min_operations_queries n edges queries = ok r) := by
  sorry

/-- Whenever min_operations_queries returns a result r, len(r) = len(queries).
  Preconditions: n is an integer with 1 <= n; len(edges) = n - 1; each edges[i] has length 3, and if edges[i] = [u_i, v_i, w_i] then 0 <= u_i, v_i < n and 1 <= w_i <= 26; the undirected graph on vertices 0..n-1 with these edges is a tree. Also len(queries) = m with m >= 1; each queries[j] has length 2, and if queries[j] = [a_j, b_j] then 0 <= a_j, b_j < n. -/
theorem spec_3 (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r) :
    r.val.length = queries.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r), r.val.length = queries.val.length) := by
  sorry

/-- Whenever min_operations_queries returns a result r, for every j with 0 <= j < len(queries), writing queries[j] = [a_j, b_j], 0 <= r[j] <= |E(a_j,b_j)| <= n - 1, where E(a,b) is the multiset of weights of edges on the unique simple path from a to b (empty if a = b).
  Preconditions: n is an integer with 1 <= n; len(edges) = n - 1; each edges[i] has length 3, and if edges[i] = [u_i, v_i, w_i] then 0 <= u_i, v_i < n and 1 <= w_i <= 26; the undirected graph on vertices 0..n-1 with these edges is a tree. Also len(queries) = m with m >= 1; each queries[j] has length 2, and if queries[j] = [a_j, b_j] then 0 <= a_j, b_j < n. -/
theorem spec_4 (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r) :
    ∀ (j : ℕ), j < queries.val.length → ∀ (a b x : ℤ),
      queryAt queries j = some (a, b) → ansAt r j = some x →
      0 ≤ x ∧ x ≤ ((E edges a b).length : ℤ) ∧ ((E edges a b).length : ℤ) ≤ n.val - 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r), ∀ (j : ℕ), j < queries.val.length → ∀ (a b x : ℤ),
      queryAt queries j = some (a, b) → ansAt r j = some x →
      0 ≤ x ∧ x ≤ ((E edges a b).length : ℤ) ∧ ((E edges a b).length : ℤ) ≤ n.val - 1) := by
  sorry

/-- Whenever min_operations_queries returns a result r, for every j with 0 <= j < len(queries), r[j] = 0 if and only if the set of weights occurring on the unique simple path from a_j to b_j has size at most 1.
  Preconditions: n is an integer with 1 <= n; len(edges) = n - 1; each edges[i] has length 3, and if edges[i] = [u_i, v_i, w_i] then 0 <= u_i, v_i < n and 1 <= w_i <= 26; the undirected graph on vertices 0..n-1 with these edges is a tree. Also len(queries) = m with m >= 1; each queries[j] has length 2, and if queries[j] = [a_j, b_j] then 0 <= a_j, b_j < n. -/
theorem spec_5 (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r) :
    ∀ (j : ℕ), j < queries.val.length → ∀ (a b x : ℤ),
      queryAt queries j = some (a, b) → ansAt r j = some x →
      (x = 0 ↔ numDistinct edges a b ≤ 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r), ∀ (j : ℕ), j < queries.val.length → ∀ (a b x : ℤ),
      queryAt queries j = some (a, b) → ansAt r j = some x →
      (x = 0 ↔ numDistinct edges a b ≤ 1)) := by
  sorry

/-- Whenever min_operations_queries returns a result r, for all j,k with 0 <= j,k < len(queries), writing queries[j] = [a_j,b_j] and queries[k] = [a_k,b_k], if a_j = b_k and b_j = a_k, then r[j] = r[k].
  Preconditions: n is an integer with 1 <= n; len(edges) = n - 1; each edges[i] has length 3, and if edges[i] = [u_i, v_i, w_i] then 0 <= u_i, v_i < n and 1 <= w_i <= 26; the undirected graph on vertices 0..n-1 with these edges is a tree. Also len(queries) = m with m >= 1; each queries[j] has length 2, and if queries[j] = [a_j, b_j] then 0 <= a_j, b_j < n. -/
theorem spec_6 (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r) :
    ∀ (j k : ℕ), j < queries.val.length → k < queries.val.length →
      ∀ (aj bj ak bk x y : ℤ),
        queryAt queries j = some (aj, bj) → queryAt queries k = some (ak, bk) →
        ansAt r j = some x → ansAt r k = some y →
        aj = bk → bj = ak → x = y := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r), ∀ (j k : ℕ), j < queries.val.length → k < queries.val.length →
      ∀ (aj bj ak bk x y : ℤ),
        queryAt queries j = some (aj, bj) → queryAt queries k = some (ak, bk) →
        ansAt r j = some x → ansAt r k = some y →
        aj = bk → bj = ak → x = y) := by
  sorry

/-- Whenever min_operations_queries returns a result r, for all j,k with 0 <= j,k < len(queries), if queries[j] = queries[k], then r[j] = r[k].
  Preconditions: n is an integer with 1 <= n; len(edges) = n - 1; each edges[i] has length 3, and if edges[i] = [u_i, v_i, w_i] then 0 <= u_i, v_i < n and 1 <= w_i <= 26; the undirected graph on vertices 0..n-1 with these edges is a tree. Also len(queries) = m with m >= 1; each queries[j] has length 2, and if queries[j] = [a_j, b_j] then 0 <= a_j, b_j < n. -/
theorem spec_7 (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r) :
    ∀ (j k : ℕ), j < queries.val.length → k < queries.val.length →
      queries.val[j]? = queries.val[k]? →
      ∀ (x y : ℤ), ansAt r j = some x → ansAt r k = some y → x = y := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r), ∀ (j k : ℕ), j < queries.val.length → k < queries.val.length →
      queries.val[j]? = queries.val[k]? →
      ∀ (x y : ℤ), ansAt r j = some x → ansAt r k = some y → x = y) := by
  sorry

/-- Whenever min_operations_queries returns a result r, for every j with 0 <= j < len(queries), if a_j != b_j and d_j is the number of distinct weights occurring on the unique simple path from a_j to b_j, then r[j] >= d_j - 1.
  Preconditions: n is an integer with 1 <= n; len(edges) = n - 1; each edges[i] has length 3, and if edges[i] = [u_i, v_i, w_i] then 0 <= u_i, v_i < n and 1 <= w_i <= 26; the undirected graph on vertices 0..n-1 with these edges is a tree. Also len(queries) = m with m >= 1; each queries[j] has length 2, and if queries[j] = [a_j, b_j] then 0 <= a_j, b_j < n. -/
theorem spec_8 (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r) :
    ∀ (j : ℕ), j < queries.val.length → ∀ (a b x : ℤ),
      queryAt queries j = some (a, b) → ansAt r j = some x →
      a ≠ b → (numDistinct edges a b : ℤ) - 1 ≤ x := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r), ∀ (j : ℕ), j < queries.val.length → ∀ (a b x : ℤ),
      queryAt queries j = some (a, b) → ansAt r j = some x →
      a ≠ b → (numDistinct edges a b : ℤ) - 1 ≤ x) := by
  sorry

/-- Whenever min_operations_queries returns a result r, for every j with 0 <= j < len(queries), if a_j != b_j and all edges on the unique simple path from a_j to b_j have pairwise distinct weights, then r[j] = |E(a_j,b_j)| - 1, where E(a,b) is the edge-weight multiset of the path.
  Preconditions: n is an integer with 1 <= n; len(edges) = n - 1; each edges[i] has length 3, and if edges[i] = [u_i, v_i, w_i] then 0 <= u_i, v_i < n and 1 <= w_i <= 26; the undirected graph on vertices 0..n-1 with these edges is a tree. Also len(queries) = m with m >= 1; each queries[j] has length 2, and if queries[j] = [a_j, b_j] then 0 <= a_j, b_j < n. -/
theorem spec_9 (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r) :
    ∀ (j : ℕ), j < queries.val.length → ∀ (a b x : ℤ),
      queryAt queries j = some (a, b) → ansAt r j = some x →
      a ≠ b → (E edges a b).Nodup → x = ((E edges a b).length : ℤ) - 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r), ∀ (j : ℕ), j < queries.val.length → ∀ (a b x : ℤ),
      queryAt queries j = some (a, b) → ansAt r j = some x →
      a ≠ b → (E edges a b).Nodup → x = ((E edges a b).length : ℤ) - 1) := by
  sorry

/-- Whenever min_operations_queries returns a result r, for every j with 0 <= j < len(queries), if the unique simple path from a_j to b_j consists of exactly two edges with weights p and q, then r[j] = 0 if p = q, and r[j] = 1 if p != q.
  Preconditions: n is an integer with 1 <= n; len(edges) = n - 1; each edges[i] has length 3, and if edges[i] = [u_i, v_i, w_i] then 0 <= u_i, v_i < n and 1 <= w_i <= 26; the undirected graph on vertices 0..n-1 with these edges is a tree. Also len(queries) = m with m >= 1; each queries[j] has length 2, and if queries[j] = [a_j, b_j] then 0 <= a_j, b_j < n. -/
theorem spec_10 (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r) :
    ∀ (j : ℕ), j < queries.val.length → ∀ (a b x p q : ℤ),
      queryAt queries j = some (a, b) → ansAt r j = some x → E edges a b = [p, q] →
      ((p = q → x = 0) ∧ (p ≠ q → x = 1)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r), ∀ (j : ℕ), j < queries.val.length → ∀ (a b x p q : ℤ),
      queryAt queries j = some (a, b) → ansAt r j = some x → E edges a b = [p, q] →
      ((p = q → x = 0) ∧ (p ≠ q → x = 1))) := by
  sorry

/-- Whenever min_operations_queries returns a result r, for every j with 0 <= j < len(queries), there exists a weight c in {1,...,26} such that r[j] equals the number of edges on the unique simple path from a_j to b_j whose weight is not c.
  Preconditions: n is an integer with 1 <= n; len(edges) = n - 1; each edges[i] has length 3, and if edges[i] = [u_i, v_i, w_i] then 0 <= u_i, v_i < n and 1 <= w_i <= 26; the undirected graph on vertices 0..n-1 with these edges is a tree. Also len(queries) = m with m >= 1; each queries[j] has length 2, and if queries[j] = [a_j, b_j] then 0 <= a_j, b_j < n. -/
theorem spec_11 (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r) :
    ∀ (j : ℕ), j < queries.val.length → ∀ (a b x : ℤ),
      queryAt queries j = some (a, b) → ansAt r j = some x →
      ∃ c : ℤ, 1 ≤ c ∧ c ≤ 26 ∧ x = (((E edges a b).filter fun w => decide (w ≠ c)).length : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r), ∀ (j : ℕ), j < queries.val.length → ∀ (a b x : ℤ),
      queryAt queries j = some (a, b) → ansAt r j = some x →
      ∃ c : ℤ, 1 ≤ c ∧ c ≤ 26 ∧ x = (((E edges a b).filter fun w => decide (w ≠ c)).length : ℤ)) := by
  sorry

/-- Whenever min_operations_queries returns a result r, for every j with 0 <= j < len(queries), if a_j != b_j and k = |E(a_j,b_j)|, where E(a,b) is the edge-weight multiset of the unique simple path from a to b, then r[j] <= k - 1.
  Preconditions: n is an integer with 1 <= n; len(edges) = n - 1; each edges[i] has length 3, and if edges[i] = [u_i, v_i, w_i] then 0 <= u_i, v_i < n and 1 <= w_i <= 26; the undirected graph on vertices 0..n-1 with these edges is a tree. Also len(queries) = m with m >= 1; each queries[j] has length 2, and if queries[j] = [a_j, b_j] then 0 <= a_j, b_j < n. -/
theorem spec_12 (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r) :
    ∀ (j : ℕ), j < queries.val.length → ∀ (a b x : ℤ),
      queryAt queries j = some (a, b) → ansAt r j = some x →
      a ≠ b → x ≤ ((E edges a b).length : ℤ) - 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r), ∀ (j : ℕ), j < queries.val.length → ∀ (a b x : ℤ),
      queryAt queries j = some (a, b) → ansAt r j = some x →
      a ≠ b → x ≤ ((E edges a b).length : ℤ) - 1) := by
  sorry

/-- Whenever min_operations_queries returns a result r, for all j,k with 0 <= j,k < len(queries), if E(a_j,b_j) is a sub-multiset of E(a_k,b_k), then r[j] <= r[k], where E(a,b) is the multiset of weights of edges on the unique simple path from a to b.
  Preconditions: n is an integer with 1 <= n; len(edges) = n - 1; each edges[i] has length 3, and if edges[i] = [u_i, v_i, w_i] then 0 <= u_i, v_i < n and 1 <= w_i <= 26; the undirected graph on vertices 0..n-1 with these edges is a tree. Also len(queries) = m with m >= 1; each queries[j] has length 2, and if queries[j] = [a_j, b_j] then 0 <= a_j, b_j < n. -/
theorem spec_13 (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r) :
    ∀ (j k : ℕ), j < queries.val.length → k < queries.val.length →
      ∀ (aj bj ak bk x y : ℤ),
        queryAt queries j = some (aj, bj) → queryAt queries k = some (ak, bk) →
        ansAt r j = some x → ansAt r k = some y →
        SubMultiset (E edges aj bj) (E edges ak bk) → x ≤ y := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : I64) (edges queries : Slice IntVec) (m : ℕ)
    (hn : 1 ≤ n.val) (hlen : (edges.val.length : ℤ) = n.val - 1)
    (hedges : EdgesWellFormed n.val edges) (htree : IsTree n.val (toEdges edges.val))
    (hqlen : queries.val.length = m) (hm : 1 ≤ m)
    (hqueries : QueriesWellFormed n.val queries)
    (r : IntVec) (hres : min_operations_queries n edges queries = ok r), ∀ (j k : ℕ), j < queries.val.length → k < queries.val.length →
      ∀ (aj bj ak bk x y : ℤ),
        queryAt queries j = some (aj, bj) → queryAt queries k = some (ak, bk) →
        ansAt r j = some x → ansAt r k = some y →
        SubMultiset (E edges aj bj) (E edges ak bk) → x ≤ y) := by
  sorry

end

end AegisSpec.MinOperationsQueries
