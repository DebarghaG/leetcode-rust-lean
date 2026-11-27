import Aegis.MinTrioDegree.Code.Funs

/-!
# Specifications of `Aegis.MinTrioDegree.min_trio_degree`

LeetCode problem `minimum-degree-of-a-connected-trio-in-a-graph`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinTrioDegree (min_trio_degree)

namespace AegisSpec.MinTrioDegree

def entryInts (edges : Slice (alloc.vec.Vec I64)) (i : Nat) : Option (List Int) :=
  (edges.val[i]?).map fun r => r.val.map fun x => x.val

def IsEdge (edges : Slice (alloc.vec.Vec I64)) (u v : Int) : Prop :=
  ∃ i, i < edges.val.length ∧ (entryInts edges i = some [u, v] ∨ entryInts edges i = some [v, u])

def IsTrio (edges : Slice (alloc.vec.Vec I64)) (n : Int) (T : Finset Int) : Prop :=
  T.card = 3 ∧ (∀ x ∈ T, 1 ≤ x ∧ x ≤ n) ∧
    (∀ u ∈ T, ∀ v ∈ T, u ≠ v → IsEdge edges u v)

def CrossCount (edges : Slice (alloc.vec.Vec I64)) (T : Finset Int) : Nat :=
  (List.range edges.val.length).countP fun i =>
    match entryInts edges i with
    | some [u, v] => decide (u ∈ T) != decide (v ∈ T)
    | _ => false

def Degree (edges : Slice (alloc.vec.Vec I64)) (v : Int) : Nat :=
  (List.range edges.val.length).countP fun i =>
    match entryInts edges i with
    | some [u, w] => decide (v = u ∨ v = w)
    | _ => false

/-- Whenever the function returns a result r: let a trio be a 3-element subset T of {1,...,n} such that for every two distinct u,v in T the unordered pair {u,v} occurs among the entries of edges, and for such T let d(T) be the number of indices i with 0 <= i < len(edges) for which exactly one of edges[i][0], edges[i][1] belongs to T. If at least one trio exists, then 0 <= r and r = min { d(T) : T is a trio }. If no trio exists, then r = -1.
  Preconditions: n is an integer with 2 <= n <= 400. edges is a list with len(edges) >= 1. For every i with 0 <= i < len(edges), edges[i] is a list of length 2 whose entries satisfy 1 <= edges[i][0] <= n, 1 <= edges[i][1] <= n, and edges[i][0] != edges[i][1]. For every 0 <= i < j < len(edges), the unordered pair {edges[i][0], edges[i][1]} is different from {edges[j][0], edges[j][1]} (no repeated undirected edge). -/
theorem spec_1
    (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 400)
    (hne : 1 ≤ edges.val.length)
    (hshape : ∀ i, i < edges.val.length →
      ∃ u v : Int, entryInts edges i = some [u, v] ∧
        1 ≤ u ∧ u ≤ n.val ∧ 1 ≤ v ∧ v ≤ n.val ∧ u ≠ v)
    (hdistinct : ∀ i j, i < j → j < edges.val.length →
      ∀ u v u' v' : Int, entryInts edges i = some [u, v] →
        entryInts edges j = some [u', v'] → ({u, v} : Finset Int) ≠ {u', v'})
    (r : I64) (hr : min_trio_degree n edges = ok r) :
    ((∃ T, IsTrio edges n.val T) →
        (0 ≤ r.val ∧
          (∃ T, IsTrio edges n.val T ∧ (CrossCount edges T : Int) = r.val) ∧
          ∀ T, IsTrio edges n.val T → r.val ≤ (CrossCount edges T : Int)))
      ∧ ((¬ ∃ T, IsTrio edges n.val T) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 400)
    (hne : 1 ≤ edges.val.length)
    (hshape : ∀ i, i < edges.val.length →
      ∃ u v : Int, entryInts edges i = some [u, v] ∧
        1 ≤ u ∧ u ≤ n.val ∧ 1 ≤ v ∧ v ≤ n.val ∧ u ≠ v)
    (hdistinct : ∀ i j, i < j → j < edges.val.length →
      ∀ u v u' v' : Int, entryInts edges i = some [u, v] →
        entryInts edges j = some [u', v'] → ({u, v} : Finset Int) ≠ {u', v'})
    (r : I64) (hr : min_trio_degree n edges = ok r), ((∃ T, IsTrio edges n.val T) →
        (0 ≤ r.val ∧
          (∃ T, IsTrio edges n.val T ∧ (CrossCount edges T : Int) = r.val) ∧
          ∀ T, IsTrio edges n.val T → r.val ≤ (CrossCount edges T : Int)))
      ∧ ((¬ ∃ T, IsTrio edges n.val T) → r.val = -1)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, overflow, or access memory out of bounds) for every input satisfying the preconditions.
  Preconditions: n is an integer with 2 <= n <= 400. edges is a list with len(edges) >= 1. For every i with 0 <= i < len(edges), edges[i] is a list of length 2 whose entries satisfy 1 <= edges[i][0] <= n, 1 <= edges[i][1] <= n, and edges[i][0] != edges[i][1]. For every 0 <= i < j < len(edges), the unordered pair {edges[i][0], edges[i][1]} is different from {edges[j][0], edges[j][1]}. -/
theorem spec_2
    (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 400)
    (hne : 1 ≤ edges.val.length)
    (hshape : ∀ i, i < edges.val.length →
      ∃ u v : Int, entryInts edges i = some [u, v] ∧
        1 ≤ u ∧ u ≤ n.val ∧ 1 ≤ v ∧ v ≤ n.val ∧ u ≠ v)
    (hdistinct : ∀ i j, i < j → j < edges.val.length →
      ∀ u v u' v' : Int, entryInts edges i = some [u, v] →
        entryInts edges j = some [u', v'] → ({u, v} : Finset Int) ≠ {u', v'}) :
    ∃ r, min_trio_degree n edges = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 400)
    (hne : 1 ≤ edges.val.length)
    (hshape : ∀ i, i < edges.val.length →
      ∃ u v : Int, entryInts edges i = some [u, v] ∧
        1 ≤ u ∧ u ≤ n.val ∧ 1 ≤ v ∧ v ≤ n.val ∧ u ≠ v)
    (hdistinct : ∀ i j, i < j → j < edges.val.length →
      ∀ u v u' v' : Int, entryInts edges i = some [u, v] →
        entryInts edges j = some [u', v'] → ({u, v} : Finset Int) ≠ {u', v'}), ∃ r, min_trio_degree n edges = ok r) := by
  sorry

/-- Whenever the function returns a result r, r != -1 if and only if there exists a 3-element subset T of {1,...,n} such that for every two distinct u,v in T the unordered pair {u,v} occurs among the entries of edges.
  Preconditions: n is an integer with 2 <= n <= 400. edges is a list with len(edges) >= 1. For every i with 0 <= i < len(edges), edges[i] is a list of length 2 whose entries satisfy 1 <= edges[i][0] <= n, 1 <= edges[i][1] <= n, and edges[i][0] != edges[i][1]. For every 0 <= i < j < len(edges), the unordered pair {edges[i][0], edges[i][1]} is different from {edges[j][0], edges[j][1]}. -/
theorem spec_3
    (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 400)
    (hne : 1 ≤ edges.val.length)
    (hshape : ∀ i, i < edges.val.length →
      ∃ u v : Int, entryInts edges i = some [u, v] ∧
        1 ≤ u ∧ u ≤ n.val ∧ 1 ≤ v ∧ v ≤ n.val ∧ u ≠ v)
    (hdistinct : ∀ i j, i < j → j < edges.val.length →
      ∀ u v u' v' : Int, entryInts edges i = some [u, v] →
        entryInts edges j = some [u', v'] → ({u, v} : Finset Int) ≠ {u', v'})
    (r : I64) (hr : min_trio_degree n edges = ok r) :
    (r.val ≠ -1 ↔ ∃ T, IsTrio edges n.val T) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 400)
    (hne : 1 ≤ edges.val.length)
    (hshape : ∀ i, i < edges.val.length →
      ∃ u v : Int, entryInts edges i = some [u, v] ∧
        1 ≤ u ∧ u ≤ n.val ∧ 1 ≤ v ∧ v ≤ n.val ∧ u ≠ v)
    (hdistinct : ∀ i j, i < j → j < edges.val.length →
      ∀ u v u' v' : Int, entryInts edges i = some [u, v] →
        entryInts edges j = some [u', v'] → ({u, v} : Finset Int) ≠ {u', v'})
    (r : I64) (hr : min_trio_degree n edges = ok r), (r.val ≠ -1 ↔ ∃ T, IsTrio edges n.val T)) := by
  sorry

/-- Whenever the function returns a result r: r >= -1; and if r != -1 then 0 <= r <= len(edges) and r <= 3*(n-3).
  Preconditions: n is an integer with 2 <= n <= 400. edges is a list with len(edges) >= 1. For every i with 0 <= i < len(edges), edges[i] is a list of length 2 whose entries satisfy 1 <= edges[i][0] <= n, 1 <= edges[i][1] <= n, and edges[i][0] != edges[i][1]. For every 0 <= i < j < len(edges), the unordered pair {edges[i][0], edges[i][1]} is different from {edges[j][0], edges[j][1]}. -/
theorem spec_4
    (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 400)
    (hne : 1 ≤ edges.val.length)
    (hshape : ∀ i, i < edges.val.length →
      ∃ u v : Int, entryInts edges i = some [u, v] ∧
        1 ≤ u ∧ u ≤ n.val ∧ 1 ≤ v ∧ v ≤ n.val ∧ u ≠ v)
    (hdistinct : ∀ i j, i < j → j < edges.val.length →
      ∀ u v u' v' : Int, entryInts edges i = some [u, v] →
        entryInts edges j = some [u', v'] → ({u, v} : Finset Int) ≠ {u', v'})
    (r : I64) (hr : min_trio_degree n edges = ok r) :
    -1 ≤ r.val ∧
      (r.val ≠ -1 →
        0 ≤ r.val ∧ r.val ≤ (edges.val.length : Int) ∧ r.val ≤ 3 * (n.val - 3)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 400)
    (hne : 1 ≤ edges.val.length)
    (hshape : ∀ i, i < edges.val.length →
      ∃ u v : Int, entryInts edges i = some [u, v] ∧
        1 ≤ u ∧ u ≤ n.val ∧ 1 ≤ v ∧ v ≤ n.val ∧ u ≠ v)
    (hdistinct : ∀ i j, i < j → j < edges.val.length →
      ∀ u v u' v' : Int, entryInts edges i = some [u, v] →
        entryInts edges j = some [u', v'] → ({u, v} : Finset Int) ≠ {u', v'})
    (r : I64) (hr : min_trio_degree n edges = ok r), -1 ≤ r.val ∧
      (r.val ≠ -1 →
        0 ≤ r.val ∧ r.val ≤ (edges.val.length : Int) ∧ r.val ≤ 3 * (n.val - 3))) := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exists a 3-element subset T of {1,...,n} such that (i) for every two distinct u,v in T the unordered pair {u,v} occurs among the entries of edges, and (ii) r equals the number of indices i with 0 <= i < len(edges) for which exactly one of edges[i][0], edges[i][1] belongs to T.
  Preconditions: n is an integer with 2 <= n <= 400. edges is a list with len(edges) >= 1. For every i with 0 <= i < len(edges), edges[i] is a list of length 2 whose entries satisfy 1 <= edges[i][0] <= n, 1 <= edges[i][1] <= n, and edges[i][0] != edges[i][1]. For every 0 <= i < j < len(edges), the unordered pair {edges[i][0], edges[i][1]} is different from {edges[j][0], edges[j][1]}. -/
theorem spec_5
    (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 400)
    (hne : 1 ≤ edges.val.length)
    (hshape : ∀ i, i < edges.val.length →
      ∃ u v : Int, entryInts edges i = some [u, v] ∧
        1 ≤ u ∧ u ≤ n.val ∧ 1 ≤ v ∧ v ≤ n.val ∧ u ≠ v)
    (hdistinct : ∀ i j, i < j → j < edges.val.length →
      ∀ u v u' v' : Int, entryInts edges i = some [u, v] →
        entryInts edges j = some [u', v'] → ({u, v} : Finset Int) ≠ {u', v'})
    (r : I64) (hr : min_trio_degree n edges = ok r) :
    r.val ≠ -1 → ∃ T, IsTrio edges n.val T ∧ (CrossCount edges T : Int) = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 400)
    (hne : 1 ≤ edges.val.length)
    (hshape : ∀ i, i < edges.val.length →
      ∃ u v : Int, entryInts edges i = some [u, v] ∧
        1 ≤ u ∧ u ≤ n.val ∧ 1 ≤ v ∧ v ≤ n.val ∧ u ≠ v)
    (hdistinct : ∀ i j, i < j → j < edges.val.length →
      ∀ u v u' v' : Int, entryInts edges i = some [u, v] →
        entryInts edges j = some [u', v'] → ({u, v} : Finset Int) ≠ {u', v'})
    (r : I64) (hr : min_trio_degree n edges = ok r), r.val ≠ -1 → ∃ T, IsTrio edges n.val T ∧ (CrossCount edges T : Int) = r.val) := by
  sorry

/-- Whenever the function returns a result r with r != -1, for every 3-element subset T of {1,...,n} such that every two distinct elements of T form an edge of edges, the number of indices i with 0 <= i < len(edges) for which exactly one of edges[i][0], edges[i][1] belongs to T is at least r.
  Preconditions: n is an integer with 2 <= n <= 400. edges is a list with len(edges) >= 1. For every i with 0 <= i < len(edges), edges[i] is a list of length 2 whose entries satisfy 1 <= edges[i][0] <= n, 1 <= edges[i][1] <= n, and edges[i][0] != edges[i][1]. For every 0 <= i < j < len(edges), the unordered pair {edges[i][0], edges[i][1]} is different from {edges[j][0], edges[j][1]}. -/
theorem spec_6
    (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 400)
    (hne : 1 ≤ edges.val.length)
    (hshape : ∀ i, i < edges.val.length →
      ∃ u v : Int, entryInts edges i = some [u, v] ∧
        1 ≤ u ∧ u ≤ n.val ∧ 1 ≤ v ∧ v ≤ n.val ∧ u ≠ v)
    (hdistinct : ∀ i j, i < j → j < edges.val.length →
      ∀ u v u' v' : Int, entryInts edges i = some [u, v] →
        entryInts edges j = some [u', v'] → ({u, v} : Finset Int) ≠ {u', v'})
    (r : I64) (hr : min_trio_degree n edges = ok r) :
    r.val ≠ -1 → ∀ T, IsTrio edges n.val T → r.val ≤ (CrossCount edges T : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 400)
    (hne : 1 ≤ edges.val.length)
    (hshape : ∀ i, i < edges.val.length →
      ∃ u v : Int, entryInts edges i = some [u, v] ∧
        1 ≤ u ∧ u ≤ n.val ∧ 1 ≤ v ∧ v ≤ n.val ∧ u ≠ v)
    (hdistinct : ∀ i j, i < j → j < edges.val.length →
      ∀ u v u' v' : Int, entryInts edges i = some [u, v] →
        entryInts edges j = some [u', v'] → ({u, v} : Finset Int) ≠ {u', v'})
    (r : I64) (hr : min_trio_degree n edges = ok r), r.val ≠ -1 → ∀ T, IsTrio edges n.val T → r.val ≤ (CrossCount edges T : Int)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, define deg(v) for v in {1,...,n} as the number of indices i with 0 <= i < len(edges) such that v = edges[i][0] or v = edges[i][1]. Then r = min { deg(a)+deg(b)+deg(c)-6 : 1 <= a < b < c <= n and each of {a,b}, {a,c}, {b,c} is an edge of edges }.
  Preconditions: n is an integer with 2 <= n <= 400. edges is a list with len(edges) >= 1. For every i with 0 <= i < len(edges), edges[i] is a list of length 2 whose entries satisfy 1 <= edges[i][0] <= n, 1 <= edges[i][1] <= n, and edges[i][0] != edges[i][1]. For every 0 <= i < j < len(edges), the unordered pair {edges[i][0], edges[i][1]} is different from {edges[j][0], edges[j][1]}. -/
theorem spec_7
    (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 400)
    (hne : 1 ≤ edges.val.length)
    (hshape : ∀ i, i < edges.val.length →
      ∃ u v : Int, entryInts edges i = some [u, v] ∧
        1 ≤ u ∧ u ≤ n.val ∧ 1 ≤ v ∧ v ≤ n.val ∧ u ≠ v)
    (hdistinct : ∀ i j, i < j → j < edges.val.length →
      ∀ u v u' v' : Int, entryInts edges i = some [u, v] →
        entryInts edges j = some [u', v'] → ({u, v} : Finset Int) ≠ {u', v'})
    (r : I64) (hr : min_trio_degree n edges = ok r) :
    r.val ≠ -1 →
      ((∃ a b c : Int, 1 ≤ a ∧ a < b ∧ b < c ∧ c ≤ n.val ∧
          IsEdge edges a b ∧ IsEdge edges a c ∧ IsEdge edges b c ∧
          r.val = (Degree edges a : Int) + (Degree edges b : Int) + (Degree edges c : Int) - 6)
        ∧ (∀ a b c : Int, 1 ≤ a → a < b → b < c → c ≤ n.val →
            IsEdge edges a b → IsEdge edges a c → IsEdge edges b c →
            r.val ≤
              (Degree edges a : Int) + (Degree edges b : Int) + (Degree edges c : Int) - 6)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 400)
    (hne : 1 ≤ edges.val.length)
    (hshape : ∀ i, i < edges.val.length →
      ∃ u v : Int, entryInts edges i = some [u, v] ∧
        1 ≤ u ∧ u ≤ n.val ∧ 1 ≤ v ∧ v ≤ n.val ∧ u ≠ v)
    (hdistinct : ∀ i j, i < j → j < edges.val.length →
      ∀ u v u' v' : Int, entryInts edges i = some [u, v] →
        entryInts edges j = some [u', v'] → ({u, v} : Finset Int) ≠ {u', v'})
    (r : I64) (hr : min_trio_degree n edges = ok r), r.val ≠ -1 →
      ((∃ a b c : Int, 1 ≤ a ∧ a < b ∧ b < c ∧ c ≤ n.val ∧
          IsEdge edges a b ∧ IsEdge edges a c ∧ IsEdge edges b c ∧
          r.val = (Degree edges a : Int) + (Degree edges b : Int) + (Degree edges c : Int) - 6)
        ∧ (∀ a b c : Int, 1 ≤ a → a < b → b < c → c ≤ n.val →
            IsEdge edges a b → IsEdge edges a c → IsEdge edges b c →
            r.val ≤
              (Degree edges a : Int) + (Degree edges b : Int) + (Degree edges c : Int) - 6))) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there exists a 3-element subset T of {1,...,n} such that every two distinct elements of T form an edge of edges and no index i with 0 <= i < len(edges) has exactly one of edges[i][0], edges[i][1] in T.
  Preconditions: n is an integer with 2 <= n <= 400. edges is a list with len(edges) >= 1. For every i with 0 <= i < len(edges), edges[i] is a list of length 2 whose entries satisfy 1 <= edges[i][0] <= n, 1 <= edges[i][1] <= n, and edges[i][0] != edges[i][1]. For every 0 <= i < j < len(edges), the unordered pair {edges[i][0], edges[i][1]} is different from {edges[j][0], edges[j][1]}. -/
theorem spec_8
    (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 400)
    (hne : 1 ≤ edges.val.length)
    (hshape : ∀ i, i < edges.val.length →
      ∃ u v : Int, entryInts edges i = some [u, v] ∧
        1 ≤ u ∧ u ≤ n.val ∧ 1 ≤ v ∧ v ≤ n.val ∧ u ≠ v)
    (hdistinct : ∀ i j, i < j → j < edges.val.length →
      ∀ u v u' v' : Int, entryInts edges i = some [u, v] →
        entryInts edges j = some [u', v'] → ({u, v} : Finset Int) ≠ {u', v'})
    (r : I64) (hr : min_trio_degree n edges = ok r) :
    (r.val = 0 ↔ ∃ T, IsTrio edges n.val T ∧ CrossCount edges T = 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 400)
    (hne : 1 ≤ edges.val.length)
    (hshape : ∀ i, i < edges.val.length →
      ∃ u v : Int, entryInts edges i = some [u, v] ∧
        1 ≤ u ∧ u ≤ n.val ∧ 1 ≤ v ∧ v ≤ n.val ∧ u ≠ v)
    (hdistinct : ∀ i j, i < j → j < edges.val.length →
      ∀ u v u' v' : Int, entryInts edges i = some [u, v] →
        entryInts edges j = some [u', v'] → ({u, v} : Finset Int) ≠ {u', v'})
    (r : I64) (hr : min_trio_degree n edges = ok r), (r.val = 0 ↔ ∃ T, IsTrio edges n.val T ∧ CrossCount edges T = 0)) := by
  sorry

/-- Whenever the graph is complete, meaning n >= 3 and for every 1 <= u < v <= n the unordered pair {u,v} occurs among the entries of edges, and the function returns a result r, then r = 3*(n-3).
  Preconditions: n is an integer with 2 <= n <= 400. edges is a list with len(edges) >= 1. For every i with 0 <= i < len(edges), edges[i] is a list of length 2 whose entries satisfy 1 <= edges[i][0] <= n, 1 <= edges[i][1] <= n, and edges[i][0] != edges[i][1]. For every 0 <= i < j < len(edges), the unordered pair {edges[i][0], edges[i][1]} is different from {edges[j][0], edges[j][1]}. -/
theorem spec_9
    (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 400)
    (hne : 1 ≤ edges.val.length)
    (hshape : ∀ i, i < edges.val.length →
      ∃ u v : Int, entryInts edges i = some [u, v] ∧
        1 ≤ u ∧ u ≤ n.val ∧ 1 ≤ v ∧ v ≤ n.val ∧ u ≠ v)
    (hdistinct : ∀ i j, i < j → j < edges.val.length →
      ∀ u v u' v' : Int, entryInts edges i = some [u, v] →
        entryInts edges j = some [u', v'] → ({u, v} : Finset Int) ≠ {u', v'})
    (hcomplete : 3 ≤ n.val)
    (hcomp : ∀ u v : Int, 1 ≤ u → u < v → v ≤ n.val → IsEdge edges u v)
    (r : I64) (hr : min_trio_degree n edges = ok r) :
    r.val = 3 * (n.val - 3) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64))
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 400)
    (hne : 1 ≤ edges.val.length)
    (hshape : ∀ i, i < edges.val.length →
      ∃ u v : Int, entryInts edges i = some [u, v] ∧
        1 ≤ u ∧ u ≤ n.val ∧ 1 ≤ v ∧ v ≤ n.val ∧ u ≠ v)
    (hdistinct : ∀ i j, i < j → j < edges.val.length →
      ∀ u v u' v' : Int, entryInts edges i = some [u, v] →
        entryInts edges j = some [u', v'] → ({u, v} : Finset Int) ≠ {u', v'})
    (hcomplete : 3 ≤ n.val)
    (hcomp : ∀ u v : Int, 1 ≤ u → u < v → v ≤ n.val → IsEdge edges u v)
    (r : I64) (hr : min_trio_degree n edges = ok r), r.val = 3 * (n.val - 3)) := by
  sorry

end AegisSpec.MinTrioDegree
