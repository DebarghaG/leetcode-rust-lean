import Aegis.ShortestDistanceAfterQueries.Code.Funs

/-!
# Specifications of `Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries`

LeetCode problem `shortest-distance-after-road-addition-queries-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ShortestDistanceAfterQueries

  def queryPair (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Option (Int × Int) :=
    match (queries.val[i]?).map (fun q => q.val) with
    | some [u, v] => some (u, v)
    | _ => none

  def gapSum (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    ((List.range (i + 1)).map (fun t =>
      match queryPair queries t with
      | some (u, v) => v - u - 1
      | none => 0)).sum

  def AdjacentChain (R : Int → Int → Prop) : List Int → Prop
    | [] => True
    | [_] => True
    | a :: b :: t => R a b ∧ AdjacentChain R (b :: t)

  def IsEdge (n : Int) (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) (u v : Int) : Prop :=
    (0 ≤ u ∧ u + 1 < n ∧ v = u + 1) ∨
      (∃ (t : Nat) (u' v' : Int),
        t ≤ i ∧ queryPair queries t = some (u', v') ∧ u = u' ∧ v = v')

  def IsWalk (n : Int) (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) (p : List Int) : Prop :=
    p.head? = some 0 ∧ p.getLast? = some (n - 1) ∧
      AdjacentChain (fun u v => IsEdge n queries i u v) p

  def IsShortestDistance (n : Int) (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat)
      (d : Int) : Prop :=
    (∃ p : List Int, IsWalk n queries i p ∧ (p.length : Int) = d + 1) ∧
      ∀ p : List Int, IsWalk n queries i p → d ≤ (p.length : Int) - 1

  def PairwiseDisjointUpTo (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Prop :=
    ∀ (a b : Nat) (u v u' v' : Int),
      a < b → b ≤ i →
        queryPair queries a = some (u, v) → queryPair queries b = some (u', v') →
          v ≤ u' ∨ v' ≤ u

  /-- Whenever the function returns a result r, len(r) = len(queries) and, for every i with 0 <= i < len(queries), r[i] is the length (number of roads traversed) of a shortest directed path from city 0 to city n - 1 in the directed graph G_i with vertices 0, ..., n - 1 and edges {j -> j + 1 | 0 <= j < n - 1} together with {queries[t][0] -> queries[t][1] | 0 <= t <= i}. Shortest means that no directed path from 0 to n - 1 in G_i has smaller length.
    Preconditions: 3 <= n <= 500; 1 <= len(queries) <= 500; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < queries[i][1] < n, and 1 < queries[i][1] - queries[i][0]; and for all i, j with 0 <= i < j < len(queries), the pair (queries[i][0], queries[i][1]) is different from (queries[j][0], queries[j][1]). -/
  theorem spec_1 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
      (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
      (hq_len_two : ∀ (i : Nat), i < queries.val.length →
        ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
      (hq_shape : ∀ (i : Nat), i < queries.val.length →
        ∃ (u v : Int),
          queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
      (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
        i < j → j < queries.val.length →
          queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
            (u, v) ≠ (u', v')) :
      ∀ (r : alloc.vec.Vec Std.I64),
        Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
          r.val.length = queries.val.length ∧
            ∀ (i : Nat), i < queries.val.length → ∀ (d : Std.I64),
              r.val[i]? = some d → IsShortestDistance n.val queries i d.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
        (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
        (hq_len_two : ∀ (i : Nat), i < queries.val.length →
          ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
        (hq_shape : ∀ (i : Nat), i < queries.val.length →
          ∃ (u v : Int),
            queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
        (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
          i < j → j < queries.val.length →
            queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
              (u, v) ≠ (u', v')), ∀ (r : alloc.vec.Vec Std.I64),
          Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
            r.val.length = queries.val.length ∧
              ∀ (i : Nat), i < queries.val.length → ∀ (d : Std.I64),
                r.val[i]? = some d → IsShortestDistance n.val queries i d.val) := by
    sorry

  /-- The function returns a result r and does not fail for every input satisfying the preconditions.
    Preconditions: 3 <= n <= 500; 1 <= len(queries) <= 500; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < queries[i][1] < n, and 1 < queries[i][1] - queries[i][0]; and for all i, j with 0 <= i < j < len(queries), the pair (queries[i][0], queries[i][1]) is different from (queries[j][0], queries[j][1]). -/
  theorem spec_2 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
      (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
      (hq_len_two : ∀ (i : Nat), i < queries.val.length →
        ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
      (hq_shape : ∀ (i : Nat), i < queries.val.length →
        ∃ (u v : Int),
          queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
      (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
        i < j → j < queries.val.length →
          queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
            (u, v) ≠ (u', v')) :
      ∃ (r : alloc.vec.Vec Std.I64),
        Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
        (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
        (hq_len_two : ∀ (i : Nat), i < queries.val.length →
          ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
        (hq_shape : ∀ (i : Nat), i < queries.val.length →
          ∃ (u v : Int),
            queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
        (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
          i < j → j < queries.val.length →
            queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
              (u, v) ≠ (u', v')), ∃ (r : alloc.vec.Vec Std.I64),
          Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(queries).
    Preconditions: 3 <= n <= 500; 1 <= len(queries) <= 500; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < queries[i][1] < n, and 1 < queries[i][1] - queries[i][0]; and for all i, j with 0 <= i < j < len(queries), the pair (queries[i][0], queries[i][1]) is different from (queries[j][0], queries[j][1]). -/
  theorem spec_3 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
      (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
      (hq_len_two : ∀ (i : Nat), i < queries.val.length →
        ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
      (hq_shape : ∀ (i : Nat), i < queries.val.length →
        ∃ (u v : Int),
          queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
      (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
        i < j → j < queries.val.length →
          queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
            (u, v) ≠ (u', v')) :
      ∀ (r : alloc.vec.Vec Std.I64),
        Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
          r.val.length = queries.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
        (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
        (hq_len_two : ∀ (i : Nat), i < queries.val.length →
          ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
        (hq_shape : ∀ (i : Nat), i < queries.val.length →
          ∃ (u v : Int),
            queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
        (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
          i < j → j < queries.val.length →
            queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
              (u, v) ≠ (u', v')), ∀ (r : alloc.vec.Vec Std.I64),
          Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
            r.val.length = queries.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), 1 <= r[i] <= n - 2.
    Preconditions: 3 <= n <= 500; 1 <= len(queries) <= 500; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < queries[i][1] < n, and 1 < queries[i][1] - queries[i][0]; and for all i, j with 0 <= i < j < len(queries), the pair (queries[i][0], queries[i][1]) is different from (queries[j][0], queries[j][1]). -/
  theorem spec_4 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
      (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
      (hq_len_two : ∀ (i : Nat), i < queries.val.length →
        ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
      (hq_shape : ∀ (i : Nat), i < queries.val.length →
        ∃ (u v : Int),
          queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
      (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
        i < j → j < queries.val.length →
          queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
            (u, v) ≠ (u', v')) :
      ∀ (r : alloc.vec.Vec Std.I64),
        Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
          ∀ (i : Nat), i < queries.val.length → ∀ (d : Std.I64),
            r.val[i]? = some d → 1 ≤ d.val ∧ d.val ≤ n.val - 2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
        (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
        (hq_len_two : ∀ (i : Nat), i < queries.val.length →
          ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
        (hq_shape : ∀ (i : Nat), i < queries.val.length →
          ∃ (u v : Int),
            queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
        (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
          i < j → j < queries.val.length →
            queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
              (u, v) ≠ (u', v')), ∀ (r : alloc.vec.Vec Std.I64),
          Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
            ∀ (i : Nat), i < queries.val.length → ∀ (d : Std.I64),
              r.val[i]? = some d → 1 ≤ d.val ∧ d.val ≤ n.val - 2) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries) - 1, r[i + 1] <= r[i].
    Preconditions: 3 <= n <= 500; 1 <= len(queries) <= 500; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < queries[i][1] < n, and 1 < queries[i][1] - queries[i][0]; and for all i, j with 0 <= i < j < len(queries), the pair (queries[i][0], queries[i][1]) is different from (queries[j][0], queries[j][1]). -/
  theorem spec_5 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
      (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
      (hq_len_two : ∀ (i : Nat), i < queries.val.length →
        ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
      (hq_shape : ∀ (i : Nat), i < queries.val.length →
        ∃ (u v : Int),
          queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
      (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
        i < j → j < queries.val.length →
          queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
            (u, v) ≠ (u', v')) :
      ∀ (r : alloc.vec.Vec Std.I64),
        Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
          ∀ (i : Nat), i + 1 < queries.val.length → ∀ (d d' : Std.I64),
            r.val[i]? = some d → r.val[i + 1]? = some d' → d'.val ≤ d.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
        (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
        (hq_len_two : ∀ (i : Nat), i < queries.val.length →
          ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
        (hq_shape : ∀ (i : Nat), i < queries.val.length →
          ∃ (u v : Int),
            queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
        (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
          i < j → j < queries.val.length →
            queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
              (u, v) ≠ (u', v')), ∀ (r : alloc.vec.Vec Std.I64),
          Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
            ∀ (i : Nat), i + 1 < queries.val.length → ∀ (d d' : Std.I64),
              r.val[i]? = some d → r.val[i + 1]? = some d' → d'.val ≤ d.val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 1 <= i < len(queries), r[i - 1] - r[i] <= queries[i][1] - queries[i][0] - 1.
    Preconditions: 3 <= n <= 500; 1 <= len(queries) <= 500; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < queries[i][1] < n, and 1 < queries[i][1] - queries[i][0]; and for all i, j with 0 <= i < j < len(queries), the pair (queries[i][0], queries[i][1]) is different from (queries[j][0], queries[j][1]). -/
  theorem spec_6 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
      (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
      (hq_len_two : ∀ (i : Nat), i < queries.val.length →
        ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
      (hq_shape : ∀ (i : Nat), i < queries.val.length →
        ∃ (u v : Int),
          queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
      (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
        i < j → j < queries.val.length →
          queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
            (u, v) ≠ (u', v')) :
      ∀ (r : alloc.vec.Vec Std.I64),
        Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
          ∀ (i : Nat), 1 ≤ i → i < queries.val.length →
            ∀ (d d' : Std.I64) (u v : Int),
              r.val[i - 1]? = some d → r.val[i]? = some d' →
                queryPair queries i = some (u, v) → d.val - d'.val ≤ v - u - 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
        (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
        (hq_len_two : ∀ (i : Nat), i < queries.val.length →
          ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
        (hq_shape : ∀ (i : Nat), i < queries.val.length →
          ∃ (u v : Int),
            queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
        (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
          i < j → j < queries.val.length →
            queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
              (u, v) ≠ (u', v')), ∀ (r : alloc.vec.Vec Std.I64),
          Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
            ∀ (i : Nat), 1 ≤ i → i < queries.val.length →
              ∀ (d d' : Std.I64) (u v : Int),
                r.val[i - 1]? = some d → r.val[i]? = some d' →
                  queryPair queries i = some (u, v) → d.val - d'.val ≤ v - u - 1) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), r[i] = 1 if and only if there exists t with 0 <= t <= i such that queries[t][0] = 0 and queries[t][1] = n - 1.
    Preconditions: 3 <= n <= 500; 1 <= len(queries) <= 500; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < queries[i][1] < n, and 1 < queries[i][1] - queries[i][0]; and for all i, j with 0 <= i < j < len(queries), the pair (queries[i][0], queries[i][1]) is different from (queries[j][0], queries[j][1]). -/
  theorem spec_7 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
      (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
      (hq_len_two : ∀ (i : Nat), i < queries.val.length →
        ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
      (hq_shape : ∀ (i : Nat), i < queries.val.length →
        ∃ (u v : Int),
          queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
      (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
        i < j → j < queries.val.length →
          queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
            (u, v) ≠ (u', v')) :
      ∀ (r : alloc.vec.Vec Std.I64),
        Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
          ∀ (i : Nat), i < queries.val.length → ∀ (d : Std.I64),
            r.val[i]? = some d →
              (d.val = 1 ↔ ∃ (t : Nat), t ≤ i ∧ queryPair queries t = some (0, n.val - 1)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
        (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
        (hq_len_two : ∀ (i : Nat), i < queries.val.length →
          ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
        (hq_shape : ∀ (i : Nat), i < queries.val.length →
          ∃ (u v : Int),
            queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
        (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
          i < j → j < queries.val.length →
            queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
              (u, v) ≠ (u', v')), ∀ (r : alloc.vec.Vec Std.I64),
          Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
            ∀ (i : Nat), i < queries.val.length → ∀ (d : Std.I64),
              r.val[i]? = some d →
                (d.val = 1 ↔ ∃ (t : Nat), t ≤ i ∧ queryPair queries t = some (0, n.val - 1))) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries) and every t with 0 <= t <= i, r[i] <= n - (queries[t][1] - queries[t][0]).
    Preconditions: 3 <= n <= 500; 1 <= len(queries) <= 500; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < queries[i][1] < n, and 1 < queries[i][1] - queries[i][0]; and for all i, j with 0 <= i < j < len(queries), the pair (queries[i][0], queries[i][1]) is different from (queries[j][0], queries[j][1]). -/
  theorem spec_8 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
      (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
      (hq_len_two : ∀ (i : Nat), i < queries.val.length →
        ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
      (hq_shape : ∀ (i : Nat), i < queries.val.length →
        ∃ (u v : Int),
          queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
      (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
        i < j → j < queries.val.length →
          queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
            (u, v) ≠ (u', v')) :
      ∀ (r : alloc.vec.Vec Std.I64),
        Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
          ∀ (i : Nat), i < queries.val.length →
            ∀ (t : Nat), t ≤ i → ∀ (u v : Int),
              queryPair queries t = some (u, v) → ∀ (d : Std.I64),
                r.val[i]? = some d → d.val ≤ n.val - (v - u) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
        (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
        (hq_len_two : ∀ (i : Nat), i < queries.val.length →
          ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
        (hq_shape : ∀ (i : Nat), i < queries.val.length →
          ∃ (u v : Int),
            queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
        (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
          i < j → j < queries.val.length →
            queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
              (u, v) ≠ (u', v')), ∀ (r : alloc.vec.Vec Std.I64),
          Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
            ∀ (i : Nat), i < queries.val.length →
              ∀ (t : Nat), t ≤ i → ∀ (u v : Int),
                queryPair queries t = some (u, v) → ∀ (d : Std.I64),
                  r.val[i]? = some d → d.val ≤ n.val - (v - u)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), r[i] >= n - 1 - sum_{t=0}^{i} (queries[t][1] - queries[t][0] - 1).
    Preconditions: 3 <= n <= 500; 1 <= len(queries) <= 500; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < queries[i][1] < n, and 1 < queries[i][1] - queries[i][0]; and for all i, j with 0 <= i < j < len(queries), the pair (queries[i][0], queries[i][1]) is different from (queries[j][0], queries[j][1]). -/
  theorem spec_9 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
      (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
      (hq_len_two : ∀ (i : Nat), i < queries.val.length →
        ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
      (hq_shape : ∀ (i : Nat), i < queries.val.length →
        ∃ (u v : Int),
          queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
      (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
        i < j → j < queries.val.length →
          queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
            (u, v) ≠ (u', v')) :
      ∀ (r : alloc.vec.Vec Std.I64),
        Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
          ∀ (i : Nat), i < queries.val.length → ∀ (d : Std.I64),
            r.val[i]? = some d → n.val - 1 - gapSum queries i ≤ d.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
        (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
        (hq_len_two : ∀ (i : Nat), i < queries.val.length →
          ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
        (hq_shape : ∀ (i : Nat), i < queries.val.length →
          ∃ (u v : Int),
            queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
        (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
          i < j → j < queries.val.length →
            queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
              (u, v) ≠ (u', v')), ∀ (r : alloc.vec.Vec Std.I64),
          Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
            ∀ (i : Nat), i < queries.val.length → ∀ (d : Std.I64),
              r.val[i]? = some d → n.val - 1 - gapSum queries i ≤ d.val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), if the intervals [queries[t][0], queries[t][1]] for 0 <= t <= i are pairwise disjoint, meaning that for every pair a, b with 0 <= a < b <= i either queries[a][1] <= queries[b][0] or queries[b][1] <= queries[a][0], then r[i] = n - 1 - sum_{t=0}^{i} (queries[t][1] - queries[t][0] - 1).
    Preconditions: 3 <= n <= 500; 1 <= len(queries) <= 500; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < queries[i][1] < n, and 1 < queries[i][1] - queries[i][0]; and for all i, j with 0 <= i < j < len(queries), the pair (queries[i][0], queries[i][1]) is different from (queries[j][0], queries[j][1]). -/
  theorem spec_10 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
      (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
      (hq_len_two : ∀ (i : Nat), i < queries.val.length →
        ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
      (hq_shape : ∀ (i : Nat), i < queries.val.length →
        ∃ (u v : Int),
          queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
      (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
        i < j → j < queries.val.length →
          queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
            (u, v) ≠ (u', v')) :
      ∀ (r : alloc.vec.Vec Std.I64),
        Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
          ∀ (i : Nat), i < queries.val.length → PairwiseDisjointUpTo queries i →
            ∀ (d : Std.I64), r.val[i]? = some d → d.val = n.val - 1 - gapSum queries i := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
        (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
        (hq_len_two : ∀ (i : Nat), i < queries.val.length →
          ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
        (hq_shape : ∀ (i : Nat), i < queries.val.length →
          ∃ (u v : Int),
            queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
        (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
          i < j → j < queries.val.length →
            queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
              (u, v) ≠ (u', v')), ∀ (r : alloc.vec.Vec Std.I64),
          Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
            ∀ (i : Nat), i < queries.val.length → PairwiseDisjointUpTo queries i →
              ∀ (d : Std.I64), r.val[i]? = some d → d.val = n.val - 1 - gapSum queries i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), if there is no t with 0 <= t <= i and queries[t][0] = 0, then r[i] >= 2.
    Preconditions: 3 <= n <= 500; 1 <= len(queries) <= 500; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < queries[i][1] < n, and 1 < queries[i][1] - queries[i][0]; and for all i, j with 0 <= i < j < len(queries), the pair (queries[i][0], queries[i][1]) is different from (queries[j][0], queries[j][1]). -/
  theorem spec_11 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
      (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
      (hq_len_two : ∀ (i : Nat), i < queries.val.length →
        ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
      (hq_shape : ∀ (i : Nat), i < queries.val.length →
        ∃ (u v : Int),
          queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
      (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
        i < j → j < queries.val.length →
          queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
            (u, v) ≠ (u', v')) :
      ∀ (r : alloc.vec.Vec Std.I64),
        Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
          ∀ (i : Nat), i < queries.val.length →
            (¬ ∃ (t : Nat) (v : Int), t ≤ i ∧ queryPair queries t = some (0, v)) →
              ∀ (d : Std.I64), r.val[i]? = some d → 2 ≤ d.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
        (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
        (hq_len_two : ∀ (i : Nat), i < queries.val.length →
          ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
        (hq_shape : ∀ (i : Nat), i < queries.val.length →
          ∃ (u v : Int),
            queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
        (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
          i < j → j < queries.val.length →
            queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
              (u, v) ≠ (u', v')), ∀ (r : alloc.vec.Vec Std.I64),
          Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
            ∀ (i : Nat), i < queries.val.length →
              (¬ ∃ (t : Nat) (v : Int), t ≤ i ∧ queryPair queries t = some (0, v)) →
                ∀ (d : Std.I64), r.val[i]? = some d → 2 ≤ d.val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), if there is no t with 0 <= t <= i and queries[t][1] = n - 1, then r[i] >= 2.
    Preconditions: 3 <= n <= 500; 1 <= len(queries) <= 500; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < queries[i][1] < n, and 1 < queries[i][1] - queries[i][0]; and for all i, j with 0 <= i < j < len(queries), the pair (queries[i][0], queries[i][1]) is different from (queries[j][0], queries[j][1]). -/
  theorem spec_12 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
      (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
      (hq_len_two : ∀ (i : Nat), i < queries.val.length →
        ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
      (hq_shape : ∀ (i : Nat), i < queries.val.length →
        ∃ (u v : Int),
          queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
      (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
        i < j → j < queries.val.length →
          queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
            (u, v) ≠ (u', v')) :
      ∀ (r : alloc.vec.Vec Std.I64),
        Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
          ∀ (i : Nat), i < queries.val.length →
            (¬ ∃ (t : Nat) (u : Int), t ≤ i ∧ queryPair queries t = some (u, n.val - 1)) →
              ∀ (d : Std.I64), r.val[i]? = some d → 2 ≤ d.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lower : 3 ≤ n.val) (hn_upper : n.val ≤ 500)
        (hq_length : 1 ≤ queries.val.length) (hq_length_upper : queries.val.length ≤ 500)
        (hq_len_two : ∀ (i : Nat), i < queries.val.length →
          ∃ (q : alloc.vec.Vec Std.I64), queries.val[i]? = some q ∧ q.val.length = 2)
        (hq_shape : ∀ (i : Nat), i < queries.val.length →
          ∃ (u v : Int),
            queryPair queries i = some (u, v) ∧ 0 ≤ u ∧ u < v ∧ v < n.val ∧ 1 < v - u)
        (hq_distinct : ∀ (i j : Nat) (u v u' v' : Int),
          i < j → j < queries.val.length →
            queryPair queries i = some (u, v) → queryPair queries j = some (u', v') →
              (u, v) ≠ (u', v')), ∀ (r : alloc.vec.Vec Std.I64),
          Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries n queries = ok r →
            ∀ (i : Nat), i < queries.val.length →
              (¬ ∃ (t : Nat) (u : Int), t ≤ i ∧ queryPair queries t = some (u, n.val - 1)) →
                ∀ (d : Std.I64), r.val[i]? = some d → 2 ≤ d.val) := by
    sorry

  end AegisSpec.ShortestDistanceAfterQueries
