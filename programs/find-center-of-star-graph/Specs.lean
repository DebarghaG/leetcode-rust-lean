import Aegis.FindCenter.Code.Funs

/-!
# Specifications of `Aegis.FindCenter.find_center`

LeetCode problem `find-center-of-star-graph`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.FindCenter (find_center)

namespace AegisSpec.FindCenter

def vecInts (e : alloc.vec.Vec Std.I64) : List Int :=
  e.val.map (fun x => x.val)

def edgeList (edges : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  edges.val.map vecInts

def ep0 (e : List Int) : Int := e[0]!

def ep1 (e : List Int) : Int := e[1]!

def Joins (e : List Int) (u v : Int) : Prop :=
  ({ep0 e, ep1 e} : Set Int) = {u, v}

def endpointCount (es : List (List Int)) (v : Int) : Nat :=
  (es.map (fun e => if v ∈ e then 1 else 0)).sum

def IsCenter (es : List (List Int)) (n c : Int) : Prop :=
  1 ≤ c ∧ c ≤ n ∧
    (∀ e ∈ es, c ∈ e) ∧
    (∀ v : Int, 1 ≤ v → v ≤ n → v ≠ c →
      ∃! i : Nat, i < es.length ∧ Joins (es[i]!) c v)

def IsStarGraphOn (es : List (List Int)) (n : Int) : Prop :=
  3 ≤ n ∧ n ≤ 100000 ∧ (es.length : Int) + 1 = n ∧
    (∀ e ∈ es, e.length = 2) ∧
    (∀ e ∈ es, ∀ x ∈ e, 1 ≤ x ∧ x ≤ n) ∧
    (∀ e ∈ es, e.Nodup) ∧
    ∃ c : Int, IsCenter es n c

def IsStarGraph (es : List (List Int)) : Prop :=
  ∃ n : Int, IsStarGraphOn es n

/-- The function returns a result r and for every i with 0 <= i < len(edges), either edges[i][0] = r or edges[i][1] = r.
  Preconditions: edges is a valid star graph: there exists an integer n with 3 <= n <= 100000 such that len(edges) = n - 1, every edges[i] has length 2, every entry of every edge is in the range 1..n, the two entries of each edge are unequal, and there is a node c in 1..n such that every edge has c as one endpoint and the other endpoints are exactly the n-1 nodes of {1,...,n} other than c, each such node occurring exactly once. -/
theorem spec_1 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n) :
    ∃ r : Std.I64, find_center edges = ok r ∧
      ∀ i : Nat, i < (edgeList edges).length →
        ep0 ((edgeList edges)[i]!) = r.val ∨ ep1 ((edgeList edges)[i]!) = r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n), ∃ r : Std.I64, find_center edges = ok r ∧
      ∀ i : Nat, i < (edgeList edges).length →
        ep0 ((edgeList edges)[i]!) = r.val ∨ ep1 ((edgeList edges)[i]!) = r.val) := by
  sorry

/-- The function returns a result r for every input satisfying the precondition (it does not fail, panic, or overflow).
  Preconditions: edges is a valid star graph: there exists an integer n with 3 <= n <= 100000 such that len(edges) = n - 1, every edges[i] has length 2, every entry of every edge is in the range 1..n, the two entries of each edge are unequal, and there is a node c in 1..n such that every edge has c as one endpoint and the other endpoints are exactly the n-1 nodes of {1,...,n} other than c, each such node occurring exactly once. -/
theorem spec_2 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n) :
    ∃ r : Std.I64, find_center edges = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n), ∃ r : Std.I64, find_center edges = ok r) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r <= len(edges) + 1 (equivalently, 1 <= r <= n).
  Preconditions: edges is a valid star graph: there exists an integer n with 3 <= n <= 100000 such that len(edges) = n - 1, every edges[i] has length 2, every entry of every edge is in the range 1..n, the two entries of each edge are unequal, and there is a node c in 1..n such that every edge has c as one endpoint and the other endpoints are exactly the n-1 nodes of {1,...,n} other than c, each such node occurring exactly once. -/
theorem spec_3 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n) :
    ∀ r : Std.I64, find_center edges = ok r →
      1 ≤ r.val ∧ r.val ≤ ((edgeList edges).length : Int) + 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n), ∀ r : Std.I64, find_center edges = ok r →
      1 ≤ r.val ∧ r.val ≤ ((edgeList edges).length : Int) + 1) := by
  sorry

/-- Whenever the function returns a result r, for every node v with 1 <= v <= n and v != r, there is exactly one index i with 0 <= i < len(edges) such that edges[i][0] = v or edges[i][1] = v.
  Preconditions: edges is a valid star graph: there exists an integer n with 3 <= n <= 100000 such that len(edges) = n - 1, every edges[i] has length 2, every entry of every edge is in the range 1..n, the two entries of each edge are unequal, and there is a node c in 1..n such that every edge has c as one endpoint and the other endpoints are exactly the n-1 nodes of {1,...,n} other than c, each such node occurring exactly once. -/
theorem spec_4 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n) :
    ∀ r : Std.I64, find_center edges = ok r →
      ∀ v : Int, 1 ≤ v → v ≤ n → v ≠ r.val →
        ∃! i : Nat, i < (edgeList edges).length ∧ v ∈ (edgeList edges)[i]! := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n), ∀ r : Std.I64, find_center edges = ok r →
      ∀ v : Int, 1 ≤ v → v ≤ n → v ≠ r.val →
        ∃! i : Nat, i < (edgeList edges).length ∧ v ∈ (edgeList edges)[i]!) := by
  sorry

/-- Whenever the function returns a result r, for every node v with 1 <= v <= n and v != r, there exists an index i with 0 <= i < len(edges) such that the edge edges[i] has endpoints r and v, i.e., {edges[i][0], edges[i][1]} = {r, v}.
  Preconditions: edges is a valid star graph: there exists an integer n with 3 <= n <= 100000 such that len(edges) = n - 1, every edges[i] has length 2, every entry of every edge is in the range 1..n, the two entries of each edge are unequal, and there is a node c in 1..n such that every edge has c as one endpoint and the other endpoints are exactly the n-1 nodes of {1,...,n} other than c, each such node occurring exactly once. -/
theorem spec_5 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n) :
    ∀ r : Std.I64, find_center edges = ok r →
      ∀ v : Int, 1 ≤ v → v ≤ n → v ≠ r.val →
        ∃ i : Nat, i < (edgeList edges).length ∧
          ({ep0 ((edgeList edges)[i]!), ep1 ((edgeList edges)[i]!)} : Set Int) = {r.val, v} := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n), ∀ r : Std.I64, find_center edges = ok r →
      ∀ v : Int, 1 ≤ v → v ≤ n → v ≠ r.val →
        ∃ i : Nat, i < (edgeList edges).length ∧
          ({ep0 ((edgeList edges)[i]!), ep1 ((edgeList edges)[i]!)} : Set Int) = {r.val, v}) := by
  sorry

/-- Whenever the function returns a result r, for every i and j with 0 <= i < j < len(edges), the two edges edges[i] and edges[j] have exactly one common endpoint, and that common endpoint is r.
  Preconditions: edges is a valid star graph: there exists an integer n with 3 <= n <= 100000 such that len(edges) = n - 1, every edges[i] has length 2, every entry of every edge is in the range 1..n, the two entries of each edge are unequal, and there is a node c in 1..n such that every edge has c as one endpoint and the other endpoints are exactly the n-1 nodes of {1,...,n} other than c, each such node occurring exactly once. -/
theorem spec_6 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n) :
    ∀ r : Std.I64, find_center edges = ok r →
      ∀ i j : Nat, i < j → j < (edgeList edges).length →
        ({u : Int | u ∈ (edgeList edges)[i]! ∧ u ∈ (edgeList edges)[j]!} : Set Int) = {r.val} := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n), ∀ r : Std.I64, find_center edges = ok r →
      ∀ i j : Nat, i < j → j < (edgeList edges).length →
        ({u : Int | u ∈ (edgeList edges)[i]! ∧ u ∈ (edgeList edges)[j]!} : Set Int) = {r.val}) := by
  sorry

/-- Whenever the function returns a result r, the set of nodes v with 1 <= v <= n that are an endpoint of every edge edges[i] (0 <= i < len(edges)) is exactly {r}.
  Preconditions: edges is a valid star graph: there exists an integer n with 3 <= n <= 100000 such that len(edges) = n - 1, every edges[i] has length 2, every entry of every edge is in the range 1..n, the two entries of each edge are unequal, and there is a node c in 1..n such that every edge has c as one endpoint and the other endpoints are exactly the n-1 nodes of {1,...,n} other than c, each such node occurring exactly once. -/
theorem spec_7 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n) :
    ∀ r : Std.I64, find_center edges = ok r →
      ({v : Int | 1 ≤ v ∧ v ≤ n ∧
          ∀ i : Nat, i < (edgeList edges).length → v ∈ (edgeList edges)[i]!} : Set Int)
        = {r.val} := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n), ∀ r : Std.I64, find_center edges = ok r →
      ({v : Int | 1 ≤ v ∧ v ≤ n ∧
          ∀ i : Nat, i < (edgeList edges).length → v ∈ (edgeList edges)[i]!} : Set Int)
        = {r.val}) := by
  sorry

/-- Whenever the function returns a result r, the number of indices i with 0 <= i < len(edges) for which r is an endpoint of edges[i] is strictly greater than the number of such indices for every other node v with 1 <= v <= n and v != r.
  Preconditions: edges is a valid star graph: there exists an integer n with 3 <= n <= 100000 such that len(edges) = n - 1, every edges[i] has length 2, every entry of every edge is in the range 1..n, the two entries of each edge are unequal, and there is a node c in 1..n such that every edge has c as one endpoint and the other endpoints are exactly the n-1 nodes of {1,...,n} other than c, each such node occurring exactly once. -/
theorem spec_8 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n) :
    ∀ r : Std.I64, find_center edges = ok r →
      ∀ v : Int, 1 ≤ v → v ≤ n → v ≠ r.val →
        endpointCount (edgeList edges) v < endpointCount (edgeList edges) r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n), ∀ r : Std.I64, find_center edges = ok r →
      ∀ v : Int, 1 ≤ v → v ≤ n → v ≠ r.val →
        endpointCount (edgeList edges) v < endpointCount (edgeList edges) r.val) := by
  sorry

/-- If find_center(edges) returns r and find_center(edges') returns r', then r = r'.
  Preconditions: edges is a valid star graph with the star-graph precondition above. edges' has the same length as edges, and for every i with 0 <= i < len(edges), edges'[i][0] = edges[i][1] and edges'[i][1] = edges[i][0]. (Thus edges' is also a valid star graph on the same n nodes.) -/
theorem spec_9 (edges edges' : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n)
    (hlen : (edgeList edges').length = (edgeList edges).length)
    (hswap : ∀ i : Nat, i < (edgeList edges).length →
      ep0 ((edgeList edges')[i]!) = ep1 ((edgeList edges)[i]!) ∧
      ep1 ((edgeList edges')[i]!) = ep0 ((edgeList edges)[i]!)) :
    ∀ r r' : Std.I64, find_center edges = ok r → find_center edges' = ok r' → r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (edges edges' : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n)
    (hlen : (edgeList edges').length = (edgeList edges).length)
    (hswap : ∀ i : Nat, i < (edgeList edges).length →
      ep0 ((edgeList edges')[i]!) = ep1 ((edgeList edges)[i]!) ∧
      ep1 ((edgeList edges')[i]!) = ep0 ((edgeList edges)[i]!)), ∀ r r' : Std.I64, find_center edges = ok r → find_center edges' = ok r' → r = r') := by
  sorry

/-- Whenever the function returns a result r, for every node v with 1 <= v <= n, the number of indices i with 0 <= i < len(edges) for which v is an endpoint of edges[i] is greater than 1 if and only if v = r.
  Preconditions: edges is a valid star graph: there exists an integer n with 3 <= n <= 100000 such that len(edges) = n - 1, every edges[i] has length 2, every entry of every edge is in the range 1..n, the two entries of each edge are unequal, and there is a node c in 1..n such that every edge has c as one endpoint and the other endpoints are exactly the n-1 nodes of {1,...,n} other than c, each such node occurring exactly once. -/
theorem spec_10 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n) :
    ∀ r : Std.I64, find_center edges = ok r →
      ∀ v : Int, 1 ≤ v → v ≤ n →
        (1 < endpointCount (edgeList edges) v ↔ v = r.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Int)
    (hstar : IsStarGraphOn (edgeList edges) n), ∀ r : Std.I64, find_center edges = ok r →
      ∀ v : Int, 1 ≤ v → v ≤ n →
        (1 < endpointCount (edgeList edges) v ↔ v = r.val)) := by
  sorry

end AegisSpec.FindCenter
