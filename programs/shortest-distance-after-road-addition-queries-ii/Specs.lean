import Aegis.ShortestDistanceAfterQueries.Code.Funs

/-!
# Specifications of `Aegis.ShortestDistanceAfterQueries.shortest_distance_after_queries`

LeetCode problem `shortest-distance-after-road-addition-queries-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.ShortestDistanceAfterQueries

  namespace AegisSpec.ShortestDistanceAfterQueries

  def queryInts (queries : Slice (alloc.vec.Vec I64)) : List (List ℤ) :=
    queries.val.map (fun q => q.val.map (fun x => x.val))

  def entry (r : alloc.vec.Vec I64) (i : ℕ) : ℤ :=
    match r.val[i]? with
    | some x => x.val
    | none => 0

  def GEdge (n : ℤ) (qs : List (List ℤ)) (i : ℕ) (x y : ℤ) : Prop :=
    (0 ≤ x ∧ x < n - 1 ∧ y = x + 1) ∨ (∃ j : ℕ, j ≤ i ∧ qs[j]? = some [x, y])

  inductive WPath (n : ℤ) (E : ℤ → ℤ → Prop) : ℤ → ℤ → ℕ → Prop where
    | nil (a : ℤ) (ha0 : 0 ≤ a) (han : a < n) : WPath n E a a 0
    | cons {a b c : ℤ} {k : ℕ} (ha0 : 0 ≤ a) (han : a < n) (hab : E a b)
        (hbc : WPath n E b c k) : WPath n E a c (k + 1)

  def MinPathLen (n : ℤ) (E : ℤ → ℤ → Prop) (a b : ℤ) (k : ℕ) : Prop :=
    WPath n E a b k ∧ ∀ k' : ℕ, WPath n E a b k' → k ≤ k'

  def spanOf (q : List ℤ) : ℤ := q.getD 1 0 - q.getD 0 0

  def maxSpan (qs : List (List ℤ)) (i : ℕ) : ℤ :=
    (qs.take (i + 1)).foldr (fun q acc => max (spanOf q) acc) 0

  def Mspan (qs : List (List ℤ)) (i : ℕ) : ℤ := max 1 (maxSpan qs i)

  /-- Whenever the function returns a result r, len(r) = len(queries), and for every i with 0 <= i < len(queries), r[i] is the minimum number of edges in a directed path from 0 to n-1 in the directed graph G_i whose vertices are {0,...,n-1} and whose edges are (x, x+1) for every 0 <= x < n-1 together with (queries[j][0], queries[j][1]) for every 0 <= j <= i. A path's length is its number of edges; the minimum exists because the initial chain 0->1->...->n-1 is always an edge path of length n-1.
    Preconditions: n >= 3; n <= 100000; len(queries) >= 1; len(queries) <= 100000; every queries[j] has length 2; writing queries[j] = [u_j, v_j], 0 <= u_j < v_j < n; no road [u,v] occurs twice among the queries; and there are no indices i != j with u_i < u_j < v_i < v_j. -/
  theorem spec_1 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
      (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
      (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
      (hrange : ∀ (j : ℕ) (u v : ℤ),
        (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
      (hnodup : (queryInts queries).Nodup)
      (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
        (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
        ¬ (u < u' ∧ u' < v ∧ v < v')) :
      ∀ r : alloc.vec.Vec I64,
        shortest_distance_after_queries n queries = ok r →
          r.val.length = queries.val.length ∧
            ∀ (i : ℕ), i < queries.val.length →
              ∃ k : ℕ, entry r i = (k : ℤ) ∧
                MinPathLen n.val (GEdge n.val (queryInts queries) i) 0 (n.val - 1) k := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
        (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
        (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
        (hrange : ∀ (j : ℕ) (u v : ℤ),
          (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
        (hnodup : (queryInts queries).Nodup)
        (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
          (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
          ¬ (u < u' ∧ u' < v ∧ v < v')), ∀ r : alloc.vec.Vec I64,
          shortest_distance_after_queries n queries = ok r →
            r.val.length = queries.val.length ∧
              ∀ (i : ℕ), i < queries.val.length →
                ∃ k : ℕ, entry r i = (k : ℤ) ∧
                  MinPathLen n.val (GEdge n.val (queryInts queries) i) 0 (n.val - 1) k) := by
    sorry

  /-- For every input satisfying the preconditions, the function call returns a result r (it does not panic, fail, overflow, or go out of bounds).
    Preconditions: n >= 3; n <= 100000; len(queries) >= 1; len(queries) <= 100000; every queries[j] has length 2; writing queries[j] = [u_j, v_j], 0 <= u_j < v_j < n; no road [u,v] occurs twice among the queries; and there are no indices i != j with u_i < u_j < v_i < v_j. -/
  theorem spec_2 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
      (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
      (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
      (hrange : ∀ (j : ℕ) (u v : ℤ),
        (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
      (hnodup : (queryInts queries).Nodup)
      (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
        (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
        ¬ (u < u' ∧ u' < v ∧ v < v')) :
      ∃ r : alloc.vec.Vec I64, shortest_distance_after_queries n queries = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
        (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
        (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
        (hrange : ∀ (j : ℕ) (u v : ℤ),
          (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
        (hnodup : (queryInts queries).Nodup)
        (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
          (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
          ¬ (u < u' ∧ u' < v ∧ v < v')), ∃ r : alloc.vec.Vec I64, shortest_distance_after_queries n queries = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), 1 <= r[i] <= n-1.
    Preconditions: n >= 3; n <= 100000; len(queries) >= 1; len(queries) <= 100000; every queries[j] has length 2; writing queries[j] = [u_j, v_j], 0 <= u_j < v_j < n; no road [u,v] occurs twice among the queries; and there are no indices i != j with u_i < u_j < v_i < v_j. -/
  theorem spec_3 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
      (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
      (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
      (hrange : ∀ (j : ℕ) (u v : ℤ),
        (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
      (hnodup : (queryInts queries).Nodup)
      (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
        (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
        ¬ (u < u' ∧ u' < v ∧ v < v')) :
      ∀ r : alloc.vec.Vec I64,
        shortest_distance_after_queries n queries = ok r →
          ∀ (i : ℕ), i < queries.val.length → 1 ≤ entry r i ∧ entry r i ≤ n.val - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
        (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
        (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
        (hrange : ∀ (j : ℕ) (u v : ℤ),
          (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
        (hnodup : (queryInts queries).Nodup)
        (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
          (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
          ¬ (u < u' ∧ u' < v ∧ v < v')), ∀ r : alloc.vec.Vec I64,
          shortest_distance_after_queries n queries = ok r →
            ∀ (i : ℕ), i < queries.val.length → 1 ≤ entry r i ∧ entry r i ≤ n.val - 1) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 1 <= i < len(queries), r[i] <= r[i-1].
    Preconditions: n >= 3; n <= 100000; len(queries) >= 1; len(queries) <= 100000; every queries[j] has length 2; writing queries[j] = [u_j, v_j], 0 <= u_j < v_j < n; no road [u,v] occurs twice among the queries; and there are no indices i != j with u_i < u_j < v_i < v_j. -/
  theorem spec_4 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
      (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
      (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
      (hrange : ∀ (j : ℕ) (u v : ℤ),
        (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
      (hnodup : (queryInts queries).Nodup)
      (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
        (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
        ¬ (u < u' ∧ u' < v ∧ v < v')) :
      ∀ r : alloc.vec.Vec I64,
        shortest_distance_after_queries n queries = ok r →
          ∀ (i : ℕ), 1 ≤ i → i < queries.val.length → entry r i ≤ entry r (i - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
        (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
        (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
        (hrange : ∀ (j : ℕ) (u v : ℤ),
          (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
        (hnodup : (queryInts queries).Nodup)
        (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
          (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
          ¬ (u < u' ∧ u' < v ∧ v < v')), ∀ r : alloc.vec.Vec I64,
          shortest_distance_after_queries n queries = ok r →
            ∀ (i : ℕ), 1 ≤ i → i < queries.val.length → entry r i ≤ entry r (i - 1)) := by
    sorry

  /-- Whenever the function returns a result r and queries[0] = [u, v], it holds that r[0] = n - (v - u).
    Preconditions: n >= 3; n <= 100000; len(queries) >= 1; len(queries) <= 100000; every queries[j] has length 2; writing queries[j] = [u_j, v_j], 0 <= u_j < v_j < n; no road [u,v] occurs twice among the queries; and there are no indices i != j with u_i < u_j < v_i < v_j. -/
  theorem spec_5 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
      (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
      (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
      (hrange : ∀ (j : ℕ) (u v : ℤ),
        (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
      (hnodup : (queryInts queries).Nodup)
      (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
        (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
        ¬ (u < u' ∧ u' < v ∧ v < v')) :
      ∀ r : alloc.vec.Vec I64,
        shortest_distance_after_queries n queries = ok r →
          ∀ (u v : ℤ), (queryInts queries)[0]? = some [u, v] → entry r 0 = n.val - (v - u) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
        (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
        (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
        (hrange : ∀ (j : ℕ) (u v : ℤ),
          (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
        (hnodup : (queryInts queries).Nodup)
        (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
          (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
          ¬ (u < u' ∧ u' < v ∧ v < v')), ∀ r : alloc.vec.Vec I64,
          shortest_distance_after_queries n queries = ok r →
            ∀ (u v : ℤ), (queryInts queries)[0]? = some [u, v] → entry r 0 = n.val - (v - u)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), r[i] = 1 if and only if there exists j with 0 <= j <= i such that queries[j][0] = 0 and queries[j][1] = n-1.
    Preconditions: n >= 3; n <= 100000; len(queries) >= 1; len(queries) <= 100000; every queries[j] has length 2; writing queries[j] = [u_j, v_j], 0 <= u_j < v_j < n; no road [u,v] occurs twice among the queries; and there are no indices i != j with u_i < u_j < v_i < v_j. -/
  theorem spec_6 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
      (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
      (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
      (hrange : ∀ (j : ℕ) (u v : ℤ),
        (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
      (hnodup : (queryInts queries).Nodup)
      (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
        (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
        ¬ (u < u' ∧ u' < v ∧ v < v')) :
      ∀ r : alloc.vec.Vec I64,
        shortest_distance_after_queries n queries = ok r →
          ∀ (i : ℕ), i < queries.val.length →
            (entry r i = 1 ↔
              ∃ j : ℕ, j ≤ i ∧ (queryInts queries)[j]? = some [0, n.val - 1]) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
        (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
        (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
        (hrange : ∀ (j : ℕ) (u v : ℤ),
          (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
        (hnodup : (queryInts queries).Nodup)
        (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
          (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
          ¬ (u < u' ∧ u' < v ∧ v < v')), ∀ r : alloc.vec.Vec I64,
          shortest_distance_after_queries n queries = ok r →
            ∀ (i : ℕ), i < queries.val.length →
              (entry r i = 1 ↔
                ∃ j : ℕ, j ≤ i ∧ (queryInts queries)[j]? = some [0, n.val - 1])) := by
    sorry

  /-- Whenever the two calls return results r and r', it holds that r[i] = r'[i] for every 0 <= i < k.
    Preconditions: n >= 3; n <= 100000; both (n, queries) and (n, queries') satisfy: len >= 1, every query is [u,v] with 0 <= u < v < n, no repeated roads, and no indices i != j with u_i < u_j < v_i < v_j; and k is an integer with 0 <= k <= min(len(queries), len(queries')) such that queries[j] = queries'[j] for every 0 <= j < k. -/
  theorem spec_7 (n : I64) (queries queries' : Slice (alloc.vec.Vec I64)) (k : ℕ)
      (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
      (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
      (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
      (hrange : ∀ (j : ℕ) (u v : ℤ),
        (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
      (hnodup : (queryInts queries).Nodup)
      (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
        (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
        ¬ (u < u' ∧ u' < v ∧ v < v'))
      (hq1' : 1 ≤ queries'.val.length) (hq100' : queries'.val.length ≤ 100000)
      (hlen' : ∀ (j : ℕ) (q : List ℤ), (queryInts queries')[j]? = some q → q.length = 2)
      (hrange' : ∀ (j : ℕ) (u v : ℤ),
        (queryInts queries')[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
      (hnodup' : (queryInts queries').Nodup)
      (hnocross' : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
        (queryInts queries')[i]? = some [u, v] → (queryInts queries')[j]? = some [u', v'] →
        ¬ (u < u' ∧ u' < v ∧ v < v'))
      (hk : k ≤ min queries.val.length queries'.val.length)
      (hagree : ∀ j : ℕ, j < k → (queryInts queries)[j]? = (queryInts queries')[j]?) :
      ∀ r r' : alloc.vec.Vec I64,
        shortest_distance_after_queries n queries = ok r →
          shortest_distance_after_queries n queries' = ok r' →
            ∀ (i : ℕ), i < k → entry r i = entry r' i := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : I64) (queries queries' : Slice (alloc.vec.Vec I64)) (k : ℕ)
        (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
        (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
        (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
        (hrange : ∀ (j : ℕ) (u v : ℤ),
          (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
        (hnodup : (queryInts queries).Nodup)
        (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
          (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
          ¬ (u < u' ∧ u' < v ∧ v < v'))
        (hq1' : 1 ≤ queries'.val.length) (hq100' : queries'.val.length ≤ 100000)
        (hlen' : ∀ (j : ℕ) (q : List ℤ), (queryInts queries')[j]? = some q → q.length = 2)
        (hrange' : ∀ (j : ℕ) (u v : ℤ),
          (queryInts queries')[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
        (hnodup' : (queryInts queries').Nodup)
        (hnocross' : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
          (queryInts queries')[i]? = some [u, v] → (queryInts queries')[j]? = some [u', v'] →
          ¬ (u < u' ∧ u' < v ∧ v < v'))
        (hk : k ≤ min queries.val.length queries'.val.length)
        (hagree : ∀ j : ℕ, j < k → (queryInts queries)[j]? = (queryInts queries')[j]?), ∀ r r' : alloc.vec.Vec I64,
          shortest_distance_after_queries n queries = ok r →
            shortest_distance_after_queries n queries' = ok r' →
              ∀ (i : ℕ), i < k → entry r i = entry r' i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries) there exists a sequence x_0, x_1, ..., x_{r[i]} of integers such that x_0 = 0, x_{r[i]} = n-1, 0 <= x_t < n for every t, and for every 0 <= t < r[i], either x_{t+1} = x_t + 1 or there exists j with 0 <= j <= i and (x_t, x_{t+1}) = (queries[j][0], queries[j][1]).
    Preconditions: n >= 3; n <= 100000; len(queries) >= 1; len(queries) <= 100000; every queries[j] has length 2; writing queries[j] = [u_j, v_j], 0 <= u_j < v_j < n; no road [u,v] occurs twice among the queries; and there are no indices i != j with u_i < u_j < v_i < v_j. -/
  theorem spec_8 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
      (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
      (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
      (hrange : ∀ (j : ℕ) (u v : ℤ),
        (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
      (hnodup : (queryInts queries).Nodup)
      (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
        (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
        ¬ (u < u' ∧ u' < v ∧ v < v')) :
      ∀ r : alloc.vec.Vec I64,
        shortest_distance_after_queries n queries = ok r →
          ∀ (i : ℕ), i < queries.val.length →
            ∃ k : ℕ, entry r i = (k : ℤ) ∧
              WPath n.val (GEdge n.val (queryInts queries) i) 0 (n.val - 1) k := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
        (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
        (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
        (hrange : ∀ (j : ℕ) (u v : ℤ),
          (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
        (hnodup : (queryInts queries).Nodup)
        (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
          (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
          ¬ (u < u' ∧ u' < v ∧ v < v')), ∀ r : alloc.vec.Vec I64,
          shortest_distance_after_queries n queries = ok r →
            ∀ (i : ℕ), i < queries.val.length →
              ∃ k : ℕ, entry r i = (k : ℤ) ∧
                WPath n.val (GEdge n.val (queryInts queries) i) 0 (n.val - 1) k) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries) and every directed path from 0 to n-1 in the graph with edges (x, x+1) for 0 <= x < n-1 and (queries[j][0], queries[j][1]) for 0 <= j <= i, the number of edges in that path is at least r[i].
    Preconditions: n >= 3; n <= 100000; len(queries) >= 1; len(queries) <= 100000; every queries[j] has length 2; writing queries[j] = [u_j, v_j], 0 <= u_j < v_j < n; no road [u,v] occurs twice among the queries; and there are no indices i != j with u_i < u_j < v_i < v_j. -/
  theorem spec_9 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
      (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
      (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
      (hrange : ∀ (j : ℕ) (u v : ℤ),
        (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
      (hnodup : (queryInts queries).Nodup)
      (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
        (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
        ¬ (u < u' ∧ u' < v ∧ v < v')) :
      ∀ r : alloc.vec.Vec I64,
        shortest_distance_after_queries n queries = ok r →
          ∀ (i : ℕ), i < queries.val.length →
            ∀ k : ℕ, WPath n.val (GEdge n.val (queryInts queries) i) 0 (n.val - 1) k →
              entry r i ≤ (k : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
        (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
        (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
        (hrange : ∀ (j : ℕ) (u v : ℤ),
          (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
        (hnodup : (queryInts queries).Nodup)
        (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
          (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
          ¬ (u < u' ∧ u' < v ∧ v < v')), ∀ r : alloc.vec.Vec I64,
          shortest_distance_after_queries n queries = ok r →
            ∀ (i : ℕ), i < queries.val.length →
              ∀ k : ℕ, WPath n.val (GEdge n.val (queryInts queries) i) 0 (n.val - 1) k →
                entry r i ≤ (k : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), r[i] <= n - max_{0 <= j <= i} (queries[j][1] - queries[j][0]).
    Preconditions: n >= 3; n <= 100000; len(queries) >= 1; len(queries) <= 100000; every queries[j] has length 2; writing queries[j] = [u_j, v_j], 0 <= u_j < v_j < n; no road [u,v] occurs twice among the queries; and there are no indices i != j with u_i < u_j < v_i < v_j. -/
  theorem spec_10 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
      (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
      (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
      (hrange : ∀ (j : ℕ) (u v : ℤ),
        (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
      (hnodup : (queryInts queries).Nodup)
      (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
        (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
        ¬ (u < u' ∧ u' < v ∧ v < v')) :
      ∀ r : alloc.vec.Vec I64,
        shortest_distance_after_queries n queries = ok r →
          ∀ (i : ℕ), i < queries.val.length →
            entry r i ≤ n.val - maxSpan (queryInts queries) i := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
        (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
        (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
        (hrange : ∀ (j : ℕ) (u v : ℤ),
          (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
        (hnodup : (queryInts queries).Nodup)
        (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
          (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
          ¬ (u < u' ∧ u' < v ∧ v < v')), ∀ r : alloc.vec.Vec I64,
          shortest_distance_after_queries n queries = ok r →
            ∀ (i : ℕ), i < queries.val.length →
              entry r i ≤ n.val - maxSpan (queryInts queries) i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 1 <= i < len(queries), if there exists j < i such that queries[j][0] <= queries[i][0] < queries[i][1] <= queries[j][1], then r[i] = r[i-1].
    Preconditions: n >= 3; n <= 100000; len(queries) >= 1; len(queries) <= 100000; every queries[j] has length 2; writing queries[j] = [u_j, v_j], 0 <= u_j < v_j < n; no road [u,v] occurs twice among the queries; and there are no indices i != j with u_i < u_j < v_i < v_j. -/
  theorem spec_11 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
      (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
      (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
      (hrange : ∀ (j : ℕ) (u v : ℤ),
        (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
      (hnodup : (queryInts queries).Nodup)
      (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
        (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
        ¬ (u < u' ∧ u' < v ∧ v < v')) :
      ∀ r : alloc.vec.Vec I64,
        shortest_distance_after_queries n queries = ok r →
          ∀ (i : ℕ), 1 ≤ i → i < queries.val.length →
            (∃ (j : ℕ) (uj vj ui vi : ℤ), j < i ∧
              (queryInts queries)[j]? = some [uj, vj] ∧
              (queryInts queries)[i]? = some [ui, vi] ∧
              uj ≤ ui ∧ ui < vi ∧ vi ≤ vj) →
            entry r i = entry r (i - 1) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
        (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
        (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
        (hrange : ∀ (j : ℕ) (u v : ℤ),
          (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
        (hnodup : (queryInts queries).Nodup)
        (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
          (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
          ¬ (u < u' ∧ u' < v ∧ v < v')), ∀ r : alloc.vec.Vec I64,
          shortest_distance_after_queries n queries = ok r →
            ∀ (i : ℕ), 1 ≤ i → i < queries.val.length →
              (∃ (j : ℕ) (uj vj ui vi : ℤ), j < i ∧
                (queryInts queries)[j]? = some [uj, vj] ∧
                (queryInts queries)[i]? = some [ui, vi] ∧
                uj ≤ ui ∧ ui < vi ∧ vi ≤ vj) →
              entry r i = entry r (i - 1)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), if M_i = max(1, max_{0 <= j <= i} (queries[j][1] - queries[j][0])), then r[i] >= (n - 1 + M_i - 1) / M_i (integer ceiling division).
    Preconditions: n >= 3; n <= 100000; len(queries) >= 1; len(queries) <= 100000; every queries[j] has length 2; writing queries[j] = [u_j, v_j], 0 <= u_j < v_j < n; no road [u,v] occurs twice among the queries; and there are no indices i != j with u_i < u_j < v_i < v_j. -/
  theorem spec_12 (n : I64) (queries : Slice (alloc.vec.Vec I64))
      (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
      (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
      (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
      (hrange : ∀ (j : ℕ) (u v : ℤ),
        (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
      (hnodup : (queryInts queries).Nodup)
      (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
        (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
        ¬ (u < u' ∧ u' < v ∧ v < v')) :
      ∀ r : alloc.vec.Vec I64,
        shortest_distance_after_queries n queries = ok r →
          ∀ (i : ℕ), i < queries.val.length →
            (n.val - 1 + Mspan (queryInts queries) i - 1) / Mspan (queryInts queries) i ≤
              entry r i := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : I64) (queries : Slice (alloc.vec.Vec I64))
        (hn3 : 3 ≤ n.val) (hn100 : n.val ≤ 100000)
        (hq1 : 1 ≤ queries.val.length) (hq100 : queries.val.length ≤ 100000)
        (hlen : ∀ (j : ℕ) (q : List ℤ), (queryInts queries)[j]? = some q → q.length = 2)
        (hrange : ∀ (j : ℕ) (u v : ℤ),
          (queryInts queries)[j]? = some [u, v] → 0 ≤ u ∧ u < v ∧ v < n.val)
        (hnodup : (queryInts queries).Nodup)
        (hnocross : ∀ (i j : ℕ) (u v u' v' : ℤ), i ≠ j →
          (queryInts queries)[i]? = some [u, v] → (queryInts queries)[j]? = some [u', v'] →
          ¬ (u < u' ∧ u' < v ∧ v < v')), ∀ r : alloc.vec.Vec I64,
          shortest_distance_after_queries n queries = ok r →
            ∀ (i : ℕ), i < queries.val.length →
              (n.val - 1 + Mspan (queryInts queries) i - 1) / Mspan (queryInts queries) i ≤
                entry r i) := by
    sorry

  end AegisSpec.ShortestDistanceAfterQueries
