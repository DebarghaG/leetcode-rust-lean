import Aegis.AllPathsSourceTarget.Code.Funs

/-!
# Specifications of `Aegis.AllPathsSourceTarget.all_paths_source_target`

LeetCode problem `all-paths-from-source-to-target`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.AllPathsSourceTarget

open Aegis.AllPathsSourceTarget

def adj (graph : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
  graph.val.map (fun vs => vs.val.map (fun v => v.val))

def outPath (out : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (a : Nat) : List ℤ :=
  match out.val[a]? with
  | none => []
  | some vs => vs.val.map (fun v => v.val)

def Edge (g : List (List ℤ)) (u v : ℤ) : Prop :=
  ∃ (i : Nat) (hi : i < g.length), u = (i : ℤ) ∧ v ∈ g[i]

def Reaches (g : List (List ℤ)) (u v : ℤ) : Prop :=
  Relation.ReflTransGen (Edge g) u v

def Acyclic (g : List (List ℤ)) : Prop :=
  ∀ u : ℤ, ¬ Relation.TransGen (Edge g) u u

def IsPath (g : List (List ℤ)) (p : List ℤ) : Prop :=
  p.head? = some 0 ∧
  p.getLast? = some ((g.length : ℤ) - 1) ∧
  (∀ (k : Nat) (hk : k < p.length), 0 ≤ p[k]'hk ∧ p[k]'hk < (g.length : ℤ)) ∧
  (∀ (k : Nat) (h : k + 1 < p.length),
    Edge g (p[k]'(Nat.lt_of_succ_lt h)) (p[k+1]'h))

/-- Whenever the function returns a result r, r is exactly the collection of all paths from node 0 to node n-1 in graph, with each path listed once and in arbitrary order. A sequence p is such a path when len(p) >= 1, p[0] = 0, p[len(p)-1] = n-1, every p[k] with 0 <= k < len(p) satisfies 0 <= p[k] < n, and for every k with 0 <= k < len(p)-1, p[k+1] is one of the entries of graph[p[k]]. Exactly means: (1) every element r[a] with 0 <= a < len(r) is such a path; (2) every such path p equals r[a] for some a with 0 <= a < len(r), with the same length and the same entries at every index; and (3) no two distinct indices a,b with 0 <= a < b < len(r) give equal sequences r[a] and r[b]. No condition is imposed on the order of the elements of r.
  Preconditions: Let n = len(graph). Assume: 2 <= n <= 15; for every i with 0 <= i < n and every entry v of graph[i], 0 <= v < n and v != i; for every i with 0 <= i < n, the entries of graph[i] are pairwise distinct; the directed graph on nodes 0,...,n-1 with an edge i -> graph[i][j] for each 0 <= i < n and 0 <= j < len(graph[i]) is acyclic (equivalently, no nonempty directed cycle exists). -/
theorem spec_1 (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r) :
    (∀ a, a < r.val.length → IsPath (adj graph) (outPath r a)) ∧
    (∀ p, IsPath (adj graph) p → ∃ a, a < r.val.length ∧ outPath r a = p) ∧
    (∀ a b, a < b → b < r.val.length → outPath r a ≠ outPath r b) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r), (∀ a, a < r.val.length → IsPath (adj graph) (outPath r a)) ∧
    (∀ p, IsPath (adj graph) p → ∃ a, a < r.val.length ∧ outPath r a = p) ∧
    (∀ a b, a < b → b < r.val.length → outPath r a ≠ outPath r b)) := by
  sorry

/-- Under the preconditions, the function returns a result r and does not fail: no arithmetic overflow, out-of-bounds access, or panic occurs.
  Preconditions: Let n = len(graph). Assume: 2 <= n <= 15; for every i with 0 <= i < n and every entry v of graph[i], 0 <= v < n and v != i; for every i with 0 <= i < n, the entries of graph[i] are pairwise distinct; the directed graph on nodes 0,...,n-1 with an edge i -> graph[i][j] for each 0 <= i < n and 0 <= j < len(graph[i]) is acyclic (equivalently, no nonempty directed cycle exists). -/
theorem spec_2 (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph)) :
    ∃ r, all_paths_source_target graph = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph)), ∃ r, all_paths_source_target graph = ok r) := by
  sorry

/-- Whenever the function returns a result r, every returned path starts at the source: for every a with 0 <= a < len(r), len(r[a]) >= 1 and r[a][0] = 0.
  Preconditions: Let n = len(graph). Assume: 2 <= n <= 15; for every i with 0 <= i < n and every entry v of graph[i], 0 <= v < n and v != i; for every i with 0 <= i < n, the entries of graph[i] are pairwise distinct; the directed graph on nodes 0,...,n-1 with an edge i -> graph[i][j] for each 0 <= i < n and 0 <= j < len(graph[i]) is acyclic (equivalently, no nonempty directed cycle exists). -/
theorem spec_3 (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r) :
    ∀ a, a < r.val.length → 1 ≤ (outPath r a).length ∧ (outPath r a).head? = some 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r), ∀ a, a < r.val.length → 1 ≤ (outPath r a).length ∧ (outPath r a).head? = some 0) := by
  sorry

/-- Whenever the function returns a result r, every returned path ends at the target: for every a with 0 <= a < len(r), len(r[a]) >= 1 and r[a][len(r[a])-1] = n-1.
  Preconditions: Let n = len(graph). Assume: 2 <= n <= 15; for every i with 0 <= i < n and every entry v of graph[i], 0 <= v < n and v != i; for every i with 0 <= i < n, the entries of graph[i] are pairwise distinct; the directed graph on nodes 0,...,n-1 with an edge i -> graph[i][j] for each 0 <= i < n and 0 <= j < len(graph[i]) is acyclic (equivalently, no nonempty directed cycle exists). -/
theorem spec_4 (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r) :
    ∀ a, a < r.val.length →
      1 ≤ (outPath r a).length ∧
        (outPath r a).getLast? = some (((adj graph).length : ℤ) - 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r), ∀ a, a < r.val.length →
      1 ≤ (outPath r a).length ∧
        (outPath r a).getLast? = some (((adj graph).length : ℤ) - 1)) := by
  sorry

/-- Whenever the function returns a result r, every consecutive pair in every returned path is a directed edge: for every a with 0 <= a < len(r) and every k with 0 <= k < len(r[a])-1, r[a][k] is in the range [0,n-1] and r[a][k+1] is one of the entries of graph[r[a][k]] (that is, there exists j with 0 <= j < len(graph[r[a][k]]) such that graph[r[a][k]][j] = r[a][k+1]).
  Preconditions: Let n = len(graph). Assume: 2 <= n <= 15; for every i with 0 <= i < n and every entry v of graph[i], 0 <= v < n and v != i; for every i with 0 <= i < n, the entries of graph[i] are pairwise distinct; the directed graph on nodes 0,...,n-1 with an edge i -> graph[i][j] for each 0 <= i < n and 0 <= j < len(graph[i]) is acyclic (equivalently, no nonempty directed cycle exists). -/
theorem spec_5 (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r) :
    ∀ a, a < r.val.length → ∀ (k : Nat) (h : k + 1 < (outPath r a).length),
      0 ≤ (outPath r a)[k]'(Nat.lt_of_succ_lt h) ∧
        (outPath r a)[k]'(Nat.lt_of_succ_lt h) < ((adj graph).length : ℤ) ∧
        Edge (adj graph) ((outPath r a)[k]'(Nat.lt_of_succ_lt h)) ((outPath r a)[k+1]'h) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r), ∀ a, a < r.val.length → ∀ (k : Nat) (h : k + 1 < (outPath r a).length),
      0 ≤ (outPath r a)[k]'(Nat.lt_of_succ_lt h) ∧
        (outPath r a)[k]'(Nat.lt_of_succ_lt h) < ((adj graph).length : ℤ) ∧
        Edge (adj graph) ((outPath r a)[k]'(Nat.lt_of_succ_lt h)) ((outPath r a)[k+1]'h)) := by
  sorry

/-- Whenever the function returns a result r, every node label in every returned path is a valid node: for every a with 0 <= a < len(r) and every k with 0 <= k < len(r[a]), 0 <= r[a][k] < n.
  Preconditions: Let n = len(graph). Assume: 2 <= n <= 15; for every i with 0 <= i < n and every entry v of graph[i], 0 <= v < n and v != i; for every i with 0 <= i < n, the entries of graph[i] are pairwise distinct; the directed graph on nodes 0,...,n-1 with an edge i -> graph[i][j] for each 0 <= i < n and 0 <= j < len(graph[i]) is acyclic (equivalently, no nonempty directed cycle exists). -/
theorem spec_6 (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r) :
    ∀ a, a < r.val.length → ∀ (k : Nat) (h : k < (outPath r a).length),
      0 ≤ (outPath r a)[k]'h ∧ (outPath r a)[k]'h < ((adj graph).length : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r), ∀ a, a < r.val.length → ∀ (k : Nat) (h : k < (outPath r a).length),
      0 ≤ (outPath r a)[k]'h ∧ (outPath r a)[k]'h < ((adj graph).length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, every returned path has at least two nodes: for every a with 0 <= a < len(r), len(r[a]) >= 2.
  Preconditions: Let n = len(graph). Assume: 2 <= n <= 15; for every i with 0 <= i < n and every entry v of graph[i], 0 <= v < n and v != i; for every i with 0 <= i < n, the entries of graph[i] are pairwise distinct; the directed graph on nodes 0,...,n-1 with an edge i -> graph[i][j] for each 0 <= i < n and 0 <= j < len(graph[i]) is acyclic (equivalently, no nonempty directed cycle exists). -/
theorem spec_7 (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r) :
    ∀ a, a < r.val.length → 2 ≤ (outPath r a).length := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r), ∀ a, a < r.val.length → 2 ≤ (outPath r a).length) := by
  sorry

/-- Whenever the function returns a result r, every returned path has at most n nodes: for every a with 0 <= a < len(r), len(r[a]) <= n.
  Preconditions: Let n = len(graph). Assume: 2 <= n <= 15; for every i with 0 <= i < n and every entry v of graph[i], 0 <= v < n and v != i; for every i with 0 <= i < n, the entries of graph[i] are pairwise distinct; the directed graph on nodes 0,...,n-1 with an edge i -> graph[i][j] for each 0 <= i < n and 0 <= j < len(graph[i]) is acyclic (equivalently, no nonempty directed cycle exists). -/
theorem spec_8 (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r) :
    ∀ a, a < r.val.length → (outPath r a).length ≤ (adj graph).length := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r), ∀ a, a < r.val.length → (outPath r a).length ≤ (adj graph).length) := by
  sorry

/-- Whenever the function returns a result r, every returned path is simple: for every a with 0 <= a < len(r) and all k,l with 0 <= k < l < len(r[a]), r[a][k] != r[a][l].
  Preconditions: Let n = len(graph). Assume: 2 <= n <= 15; for every i with 0 <= i < n and every entry v of graph[i], 0 <= v < n and v != i; for every i with 0 <= i < n, the entries of graph[i] are pairwise distinct; the directed graph on nodes 0,...,n-1 with an edge i -> graph[i][j] for each 0 <= i < n and 0 <= j < len(graph[i]) is acyclic (equivalently, no nonempty directed cycle exists). -/
theorem spec_9 (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r) :
    ∀ a, a < r.val.length → ∀ (k l : Nat) (hk : k < l) (hl : l < (outPath r a).length),
      (outPath r a)[k]'(Nat.lt_trans hk hl) ≠ (outPath r a)[l]'hl := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r), ∀ a, a < r.val.length → ∀ (k l : Nat) (hk : k < l) (hl : l < (outPath r a).length),
      (outPath r a)[k]'(Nat.lt_trans hk hl) ≠ (outPath r a)[l]'hl) := by
  sorry

/-- Whenever the function returns a result r, the result contains no duplicate paths: for all a,b with 0 <= a < b < len(r), the sequences r[a] and r[b] are not equal, meaning either len(r[a]) != len(r[b]) or there exists k with 0 <= k < len(r[a]) such that r[a][k] != r[b][k].
  Preconditions: Let n = len(graph). Assume: 2 <= n <= 15; for every i with 0 <= i < n and every entry v of graph[i], 0 <= v < n and v != i; for every i with 0 <= i < n, the entries of graph[i] are pairwise distinct; the directed graph on nodes 0,...,n-1 with an edge i -> graph[i][j] for each 0 <= i < n and 0 <= j < len(graph[i]) is acyclic (equivalently, no nonempty directed cycle exists). -/
theorem spec_10 (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r) :
    ∀ a b, a < b → b < r.val.length → outPath r a ≠ outPath r b := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r), ∀ a b, a < b → b < r.val.length → outPath r a ≠ outPath r b) := by
  sorry

/-- Whenever the function returns a result r, every path from 0 to n-1 occurs in r. Here a sequence p is a path from 0 to n-1 when len(p) >= 1, p[0] = 0, p[len(p)-1] = n-1, every p[k] with 0 <= k < len(p) satisfies 0 <= p[k] < n, and every p[k+1] with 0 <= k < len(p)-1 is one of the entries of graph[p[k]]. For every such p, there exists an index a with 0 <= a < len(r) such that len(r[a]) = len(p) and r[a][k] = p[k] for all 0 <= k < len(p).
  Preconditions: Let n = len(graph). Assume: 2 <= n <= 15; for every i with 0 <= i < n and every entry v of graph[i], 0 <= v < n and v != i; for every i with 0 <= i < n, the entries of graph[i] are pairwise distinct; the directed graph on nodes 0,...,n-1 with an edge i -> graph[i][j] for each 0 <= i < n and 0 <= j < len(graph[i]) is acyclic (equivalently, no nonempty directed cycle exists). -/
theorem spec_11 (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r) :
    ∀ p, IsPath (adj graph) p → ∃ a, a < r.val.length ∧ outPath r a = p := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r), ∀ p, IsPath (adj graph) p → ∃ a, a < r.val.length ∧ outPath r a = p) := by
  sorry

/-- Whenever the function returns a result r, len(r) = 0 if and only if there does not exist a sequence p such that len(p) >= 1, p[0] = 0, p[len(p)-1] = n-1, every p[k] with 0 <= k < len(p) satisfies 0 <= p[k] < n, and every p[k+1] with 0 <= k < len(p)-1 is one of the entries of graph[p[k]].
  Preconditions: Let n = len(graph). Assume: 2 <= n <= 15; for every i with 0 <= i < n and every entry v of graph[i], 0 <= v < n and v != i; for every i with 0 <= i < n, the entries of graph[i] are pairwise distinct; the directed graph on nodes 0,...,n-1 with an edge i -> graph[i][j] for each 0 <= i < n and 0 <= j < len(graph[i]) is acyclic (equivalently, no nonempty directed cycle exists). -/
theorem spec_12 (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r) :
    r.val.length = 0 ↔ ¬ ∃ p, IsPath (adj graph) p := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64))
    (h_n2 : 2 ≤ (adj graph).length) (h_n15 : (adj graph).length ≤ 15)
    (h_range : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i],
      0 ≤ v ∧ v < ((adj graph).length : ℤ))
    (h_self : ∀ (i : Nat) (hi : i < (adj graph).length), ∀ v ∈ (adj graph)[i], v ≠ (i : ℤ))
    (h_nodup : ∀ (i : Nat) (hi : i < (adj graph).length), ((adj graph)[i]).Nodup)
    (h_acyc : Acyclic (adj graph))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : all_paths_source_target graph = ok r), r.val.length = 0 ↔ ¬ ∃ p, IsPath (adj graph) p) := by
  sorry

end AegisSpec.AllPathsSourceTarget
