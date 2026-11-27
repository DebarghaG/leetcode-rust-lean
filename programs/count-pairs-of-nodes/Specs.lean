import Aegis.CountPairs.Code.Funs

/-!
# Specifications of `Aegis.CountPairs.count_pairs`

LeetCode problem `count-pairs-of-nodes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
  open Aegis.CountPairs

  set_option maxHeartbeats 1000000

  namespace AegisSpec.CountPairs

  def sliceEntry (s : Slice Std.I64) (i : ℕ) : Option ℤ := (s.val[i]?).map IScalar.val

  def vecEntry (v : alloc.vec.Vec Std.I64) (i : ℕ) : Option ℤ := (v.val[i]?).map IScalar.val

  def edgeAt (edges : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : Option (ℤ × ℤ) :=
    (edges.val[i]?).bind fun e =>
      match e.val with
      | [a, b] => some (a.val, b.val)
      | _ => none

  def query (queries : Slice Std.I64) (i : ℕ) : ℤ := (sliceEntry queries i).getD 0

  def incident (edges : Slice (alloc.vec.Vec Std.I64)) (a b : ℤ) : ℕ :=
    (List.range edges.val.length).countP fun k =>
      match edgeAt edges k with
      | some (x, y) => decide (x = a ∨ y = a ∨ x = b ∨ y = b)
      | none => false

  def pairList (n : ℕ) : List (ℤ × ℤ) :=
    (List.range n).flatMap fun b => (List.range b).map fun a => ((a : ℤ) + 1, (b : ℤ) + 1)

  def incidentCounts (n : ℕ) (edges : Slice (alloc.vec.Vec Std.I64)) : List ℕ :=
    (pairList n).map fun p => incident edges p.1 p.2

  def listMin : List ℕ → ℕ
    | [] => 0
    | x :: xs => xs.foldr min x

  def listMax : List ℕ → ℕ
    | [] => 0
    | x :: xs => xs.foldr max x

  def minIncident (n : ℕ) (edges : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
    listMin (incidentCounts n edges)

  def maxIncident (n : ℕ) (edges : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
    listMax (incidentCounts n edges)

  def countPairsAbove (n : ℕ) (edges : Slice (alloc.vec.Vec Std.I64)) (q : ℤ) : ℕ :=
    (incidentCounts n edges).countP fun c => decide (q < (c : ℤ))

  def vertices (n : Std.I64) : ℕ := n.val.toNat

  def totalPairs (n : Std.I64) : ℕ := vertices n * (vertices n - 1) / 2

  def edgeMult (edges : Slice (alloc.vec.Vec Std.I64)) (a b : ℤ) : ℕ :=
    edges.val.countP fun e =>
      match e.val with
      | [x, y] => decide (x.val = a ∧ y.val = b)
      | _ => false

  def NRange (n : Std.I64) : Prop := 2 ≤ n.val ∧ n.val ≤ 20000

  def EdgesWF (n : ℤ) (edges : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    1 ≤ edges.val.length ∧ edges.val.length ≤ 100000 ∧
      ∀ e ∈ edges.val,
        ∃ a b : Std.I64, e.val = [a, b] ∧ 1 ≤ a.val ∧ a.val ≤ n ∧ 1 ≤ b.val ∧
          b.val ≤ n ∧ a.val ≠ b.val

  def QueriesWF (m : ℕ) (queries : Slice Std.I64) : Prop :=
    1 ≤ queries.val.length ∧ queries.val.length ≤ 20 ∧
      ∀ q ∈ queries.val, 0 ≤ q.val ∧ q.val < (m : ℤ)

  /-- Define, for 1 <= a < b <= n, incident(a,b) = |{ k : 0 <= k < len(edges) and (edges[k][0] = a or edges[k][1] = a or edges[k][0] = b or edges[k][1] = b) }|. Whenever count_pairs(n, edges, queries) returns a result r, r has length len(queries), and for every j with 0 <= j < len(queries), r[j] = |{ (a,b) : 1 <= a < b <= n and incident(a,b) > queries[j] }|.
    Preconditions: n is an integer with 2 <= n <= 20000. edges is a slice of vectors with 1 <= len(edges) <= 100000; every element edges[k] has length 2, edges[k][0] and edges[k][1] are in {1,...,n}, and edges[k][0] != edges[k][1]. queries is a slice with 1 <= len(queries) <= 20; for every j with 0 <= j < len(queries), 0 <= queries[j] < len(edges). -/
  theorem spec_1 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
      (hq : QueriesWF edges.val.length queries) :
      ∀ r : alloc.vec.Vec Std.I64,
        count_pairs n edges queries = ok r →
          r.val.length = queries.val.length ∧
            ∀ j, j < queries.val.length →
              vecEntry r j =
                some (countPairsAbove (vertices n) edges (query queries j) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
        (hq : QueriesWF edges.val.length queries), ∀ r : alloc.vec.Vec Std.I64,
          count_pairs n edges queries = ok r →
            r.val.length = queries.val.length ∧
              ∀ j, j < queries.val.length →
                vecEntry r j =
                  some (countPairsAbove (vertices n) edges (query queries j) : ℤ)) := by
    sorry

  /-- Whenever count_pairs(n, edges, queries) returns a result r, len(r) = len(queries).
    Preconditions: n is an integer with 2 <= n <= 20000. edges is a slice of vectors with 1 <= len(edges) <= 100000; every element edges[k] has length 2, edges[k][0] and edges[k][1] are in {1,...,n}, and edges[k][0] != edges[k][1]. queries is a slice with 1 <= len(queries) <= 20; for every j with 0 <= j < len(queries), 0 <= queries[j] < len(edges). -/
  theorem spec_2 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
      (hq : QueriesWF edges.val.length queries) :
      ∀ r : alloc.vec.Vec Std.I64,
        count_pairs n edges queries = ok r → r.val.length = queries.val.length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
        (hq : QueriesWF edges.val.length queries), ∀ r : alloc.vec.Vec Std.I64,
          count_pairs n edges queries = ok r → r.val.length = queries.val.length) := by
    sorry

  /-- count_pairs(n, edges, queries) returns a result r; it does not fail, panic, or overflow on any input satisfying the preconditions.
    Preconditions: n is an integer with 2 <= n <= 20000. edges is a slice of vectors with 1 <= len(edges) <= 100000; every element edges[k] has length 2, edges[k][0] and edges[k][1] are in {1,...,n}, and edges[k][0] != edges[k][1]. queries is a slice with 1 <= len(queries) <= 20; for every j with 0 <= j < len(queries), 0 <= queries[j] < len(edges). -/
  theorem spec_3 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
      (hq : QueriesWF edges.val.length queries) :
      ∃ r : alloc.vec.Vec Std.I64, count_pairs n edges queries = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
        (hq : QueriesWF edges.val.length queries), ∃ r : alloc.vec.Vec Std.I64, count_pairs n edges queries = ok r) := by
    sorry

  /-- Whenever count_pairs(n, edges, queries) returns a result r, for every j with 0 <= j < len(queries), 0 <= r[j] <= n*(n-1)/2.
    Preconditions: n is an integer with 2 <= n <= 20000. edges is a slice of vectors with 1 <= len(edges) <= 100000; every element edges[k] has length 2, edges[k][0] and edges[k][1] are in {1,...,n}, and edges[k][0] != edges[k][1]. queries is a slice with 1 <= len(queries) <= 20; for every j with 0 <= j < len(queries), 0 <= queries[j] < len(edges). -/
  theorem spec_4 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
      (hq : QueriesWF edges.val.length queries) :
      ∀ r : alloc.vec.Vec Std.I64,
        count_pairs n edges queries = ok r →
          ∀ j, j < queries.val.length →
            ∃ x : ℤ, vecEntry r j = some x ∧ 0 ≤ x ∧ x ≤ (totalPairs n : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
        (hq : QueriesWF edges.val.length queries), ∀ r : alloc.vec.Vec Std.I64,
          count_pairs n edges queries = ok r →
            ∀ j, j < queries.val.length →
              ∃ x : ℤ, vecEntry r j = some x ∧ 0 ≤ x ∧ x ≤ (totalPairs n : ℤ)) := by
    sorry

  /-- Whenever count_pairs(n, edges, queries) returns a result r, for all i,k with 0 <= i < len(queries) and 0 <= k < len(queries), if queries[i] <= queries[k] then r[i] >= r[k].
    Preconditions: n is an integer with 2 <= n <= 20000. edges is a slice of vectors with 1 <= len(edges) <= 100000; every element edges[k] has length 2, edges[k][0] and edges[k][1] are in {1,...,n}, and edges[k][0] != edges[k][1]. queries is a slice with 1 <= len(queries) <= 20; for every j with 0 <= j < len(queries), 0 <= queries[j] < len(edges). -/
  theorem spec_5 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
      (hq : QueriesWF edges.val.length queries) :
      ∀ r : alloc.vec.Vec Std.I64,
        count_pairs n edges queries = ok r →
          ∀ i k, i < queries.val.length → k < queries.val.length →
            query queries i ≤ query queries k →
              ∃ x y : ℤ, vecEntry r i = some x ∧ vecEntry r k = some y ∧ y ≤ x := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
        (hq : QueriesWF edges.val.length queries), ∀ r : alloc.vec.Vec Std.I64,
          count_pairs n edges queries = ok r →
            ∀ i k, i < queries.val.length → k < queries.val.length →
              query queries i ≤ query queries k →
                ∃ x y : ℤ, vecEntry r i = some x ∧ vecEntry r k = some y ∧ y ≤ x) := by
    sorry

  /-- For every j with 0 <= j < len(queries1) and 0 <= j < len(queries2), if queries1[j] = queries2[j], then whenever count_pairs(n, edges, queries1) returns r1 and count_pairs(n, edges, queries2) returns r2, r1[j] = r2[j].
    Preconditions: n is an integer with 2 <= n <= 20000. edges is a slice of vectors with 1 <= len(edges) <= 100000; every element edges[k] has length 2, edges[k][0] and edges[k][1] are in {1,...,n}, and edges[k][0] != edges[k][1]. queries1 and queries2 are slices with 1 <= len <= 20; for every valid j, 0 <= queries1[j] < len(edges) and 0 <= queries2[j] < len(edges). -/
  theorem spec_6 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (queries1 queries2 : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
      (hq1 : QueriesWF edges.val.length queries1)
      (hq2 : QueriesWF edges.val.length queries2) :
      ∀ j, j < queries1.val.length → j < queries2.val.length →
        query queries1 j = query queries2 j →
          ∀ r1 r2 : alloc.vec.Vec Std.I64,
            count_pairs n edges queries1 = ok r1 →
              count_pairs n edges queries2 = ok r2 → vecEntry r1 j = vecEntry r2 j := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (queries1 queries2 : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
        (hq1 : QueriesWF edges.val.length queries1)
        (hq2 : QueriesWF edges.val.length queries2), ∀ j, j < queries1.val.length → j < queries2.val.length →
          query queries1 j = query queries2 j →
            ∀ r1 r2 : alloc.vec.Vec Std.I64,
              count_pairs n edges queries1 = ok r1 →
                count_pairs n edges queries2 = ok r2 → vecEntry r1 j = vecEntry r2 j) := by
    sorry

  /-- Let incident(a,b) = |{ k : 0 <= k < len(edges) and (edges[k][0] = a or edges[k][1] = a or edges[k][0] = b or edges[k][1] = b) }| for 1 <= a < b <= n, and let minIncident = min { incident(a,b) : 1 <= a < b <= n }. Whenever count_pairs(n, edges, queries) returns a result r, for every j with 0 <= j < len(queries), if queries[j] < minIncident then r[j] = n*(n-1)/2.
    Preconditions: n is an integer with 2 <= n <= 20000. edges is a slice of vectors with 1 <= len(edges) <= 100000; every element edges[k] has length 2, edges[k][0] and edges[k][1] are in {1,...,n}, and edges[k][0] != edges[k][1]. queries is a slice with 1 <= len(queries) <= 20; for every j with 0 <= j < len(queries), 0 <= queries[j] < len(edges). -/
  theorem spec_7 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
      (hq : QueriesWF edges.val.length queries) :
      ∀ r : alloc.vec.Vec Std.I64,
        count_pairs n edges queries = ok r →
          ∀ j, j < queries.val.length →
            query queries j < (minIncident (vertices n) edges : ℤ) →
              vecEntry r j = some (totalPairs n : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
        (hq : QueriesWF edges.val.length queries), ∀ r : alloc.vec.Vec Std.I64,
          count_pairs n edges queries = ok r →
            ∀ j, j < queries.val.length →
              query queries j < (minIncident (vertices n) edges : ℤ) →
                vecEntry r j = some (totalPairs n : ℤ)) := by
    sorry

  /-- Let incident(a,b) = |{ k : 0 <= k < len(edges) and (edges[k][0] = a or edges[k][1] = a or edges[k][0] = b or edges[k][1] = b) }| for 1 <= a < b <= n, and let maxIncident = max { incident(a,b) : 1 <= a < b <= n }. Whenever count_pairs(n, edges, queries) returns a result r, for every j with 0 <= j < len(queries), if queries[j] >= maxIncident then r[j] = 0.
    Preconditions: n is an integer with 2 <= n <= 20000. edges is a slice of vectors with 1 <= len(edges) <= 100000; every element edges[k] has length 2, edges[k][0] and edges[k][1] are in {1,...,n}, and edges[k][0] != edges[k][1]. queries is a slice with 1 <= len(queries) <= 20; for every j with 0 <= j < len(queries), 0 <= queries[j] < len(edges). -/
  theorem spec_8 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
      (hq : QueriesWF edges.val.length queries) :
      ∀ r : alloc.vec.Vec Std.I64,
        count_pairs n edges queries = ok r →
          ∀ j, j < queries.val.length →
            (maxIncident (vertices n) edges : ℤ) ≤ query queries j →
              vecEntry r j = some (0 : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
        (hq : QueriesWF edges.val.length queries), ∀ r : alloc.vec.Vec Std.I64,
          count_pairs n edges queries = ok r →
            ∀ j, j < queries.val.length →
              (maxIncident (vertices n) edges : ℤ) ≤ query queries j →
                vecEntry r j = some (0 : ℤ)) := by
    sorry

  /-- Let incident(a,b) = |{ k : 0 <= k < len(edges) and (edges[k][0] = a or edges[k][1] = a or edges[k][0] = b or edges[k][1] = b) }| for 1 <= a < b <= n. Whenever count_pairs(n, edges, queries) returns a result r, for every j with 0 <= j < len(queries), if r[j] > 0 then there exist integers a,b with 1 <= a < b <= n such that incident(a,b) > queries[j].
    Preconditions: n is an integer with 2 <= n <= 20000. edges is a slice of vectors with 1 <= len(edges) <= 100000; every element edges[k] has length 2, edges[k][0] and edges[k][1] are in {1,...,n}, and edges[k][0] != edges[k][1]. queries is a slice with 1 <= len(queries) <= 20; for every j with 0 <= j < len(queries), 0 <= queries[j] < len(edges). -/
  theorem spec_9 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
      (hq : QueriesWF edges.val.length queries) :
      ∀ r : alloc.vec.Vec Std.I64,
        count_pairs n edges queries = ok r →
          ∀ j, j < queries.val.length →
            (∃ x : ℤ, vecEntry r j = some x ∧ 0 < x) →
              ∃ a b : ℤ,
                1 ≤ a ∧ a < b ∧ b ≤ n.val ∧ query queries j < (incident edges a b : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
        (hq : QueriesWF edges.val.length queries), ∀ r : alloc.vec.Vec Std.I64,
          count_pairs n edges queries = ok r →
            ∀ j, j < queries.val.length →
              (∃ x : ℤ, vecEntry r j = some x ∧ 0 < x) →
                ∃ a b : ℤ,
                  1 ≤ a ∧ a < b ∧ b ≤ n.val ∧ query queries j < (incident edges a b : ℤ)) := by
    sorry

  /-- Let incident(a,b) = |{ k : 0 <= k < len(edges) and (edges[k][0] = a or edges[k][1] = a or edges[k][0] = b or edges[k][1] = b) }| for 1 <= a < b <= n. Whenever count_pairs(n, edges, queries) returns a result r, for every j with 0 <= j < len(queries), if r[j] < n*(n-1)/2 then there exist integers a,b with 1 <= a < b <= n such that incident(a,b) <= queries[j].
    Preconditions: n is an integer with 2 <= n <= 20000. edges is a slice of vectors with 1 <= len(edges) <= 100000; every element edges[k] has length 2, edges[k][0] and edges[k][1] are in {1,...,n}, and edges[k][0] != edges[k][1]. queries is a slice with 1 <= len(queries) <= 20; for every j with 0 <= j < len(queries), 0 <= queries[j] < len(edges). -/
  theorem spec_10 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
      (hq : QueriesWF edges.val.length queries) :
      ∀ r : alloc.vec.Vec Std.I64,
        count_pairs n edges queries = ok r →
          ∀ j, j < queries.val.length →
            (∃ x : ℤ, vecEntry r j = some x ∧ x < (totalPairs n : ℤ)) →
              ∃ a b : ℤ,
                1 ≤ a ∧ a < b ∧ b ≤ n.val ∧ (incident edges a b : ℤ) ≤ query queries j := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
        (hq : QueriesWF edges.val.length queries), ∀ r : alloc.vec.Vec Std.I64,
          count_pairs n edges queries = ok r →
            ∀ j, j < queries.val.length →
              (∃ x : ℤ, vecEntry r j = some x ∧ x < (totalPairs n : ℤ)) →
                ∃ a b : ℤ,
                  1 ≤ a ∧ a < b ∧ b ≤ n.val ∧ (incident edges a b : ℤ) ≤ query queries j) := by
    sorry

  /-- Let incident(a,b) = |{ k : 0 <= k < len(edges) and (edges[k][0] = a or edges[k][1] = a or edges[k][0] = b or edges[k][1] = b) }| for 1 <= a < b <= n. Whenever count_pairs(n, edges, queries) returns a result r, for every j with 0 <= j < len(queries), r[j] = n*(n-1)/2 if and only if for every pair a,b with 1 <= a < b <= n, incident(a,b) > queries[j].
    Preconditions: n is an integer with 2 <= n <= 20000. edges is a slice of vectors with 1 <= len(edges) <= 100000; every element edges[k] has length 2, edges[k][0] and edges[k][1] are in {1,...,n}, and edges[k][0] != edges[k][1]. queries is a slice with 1 <= len(queries) <= 20; for every j with 0 <= j < len(queries), 0 <= queries[j] < len(edges). -/
  theorem spec_11 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
      (hq : QueriesWF edges.val.length queries) :
      ∀ r : alloc.vec.Vec Std.I64,
        count_pairs n edges queries = ok r →
          ∀ j, j < queries.val.length →
            (vecEntry r j = some (totalPairs n : ℤ) ↔
              ∀ a b : ℤ,
                1 ≤ a → a < b → b ≤ n.val → query queries j < (incident edges a b : ℤ)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
        (hq : QueriesWF edges.val.length queries), ∀ r : alloc.vec.Vec Std.I64,
          count_pairs n edges queries = ok r →
            ∀ j, j < queries.val.length →
              (vecEntry r j = some (totalPairs n : ℤ) ↔
                ∀ a b : ℤ,
                  1 ≤ a → a < b → b ≤ n.val → query queries j < (incident edges a b : ℤ))) := by
    sorry

  /-- Let incident(a,b) = |{ k : 0 <= k < len(edges) and (edges[k][0] = a or edges[k][1] = a or edges[k][0] = b or edges[k][1] = b) }| for 1 <= a < b <= n. Whenever count_pairs(n, edges, queries) returns a result r, for every j with 0 <= j < len(queries), r[j] = 0 if and only if for every pair a,b with 1 <= a < b <= n, incident(a,b) <= queries[j].
    Preconditions: n is an integer with 2 <= n <= 20000. edges is a slice of vectors with 1 <= len(edges) <= 100000; every element edges[k] has length 2, edges[k][0] and edges[k][1] are in {1,...,n}, and edges[k][0] != edges[k][1]. queries is a slice with 1 <= len(queries) <= 20; for every j with 0 <= j < len(queries), 0 <= queries[j] < len(edges). -/
  theorem spec_12 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
      (hq : QueriesWF edges.val.length queries) :
      ∀ r : alloc.vec.Vec Std.I64,
        count_pairs n edges queries = ok r →
          ∀ j, j < queries.val.length →
            (vecEntry r j = some (0 : ℤ) ↔
              ∀ a b : ℤ,
                1 ≤ a → a < b → b ≤ n.val → (incident edges a b : ℤ) ≤ query queries j) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
        (hq : QueriesWF edges.val.length queries), ∀ r : alloc.vec.Vec Std.I64,
          count_pairs n edges queries = ok r →
            ∀ j, j < queries.val.length →
              (vecEntry r j = some (0 : ℤ) ↔
                ∀ a b : ℤ,
                  1 ≤ a → a < b → b ≤ n.val → (incident edges a b : ℤ) ≤ query queries j)) := by
    sorry

  /-- Whenever count_pairs(n, edges1, queries) returns r1 and count_pairs(n, edges2, queries) returns r2, r1 = r2.
    Preconditions: n is an integer with 2 <= n <= 20000. edges1 and edges2 are slices of vectors, each satisfying 1 <= len <= 100000, every element has length 2, both entries are in {1,...,n}, and the two entries are distinct. Assume len(edges1) = len(edges2) and edges2 is a permutation of edges1: there is a bijection p from {0,...,len(edges1)-1} to itself such that edges2[k] = edges1[p(k)] for every k. queries is a slice with 1 <= len(queries) <= 20 and 0 <= queries[j] < len(edges1) for every j. -/
  theorem spec_13 (n : Std.I64) (edges1 edges2 : Slice (alloc.vec.Vec Std.I64))
      (queries : Slice Std.I64) (hn : NRange n) (h1 : EdgesWF n.val edges1)
      (h2 : EdgesWF n.val edges2) (hlen : edges1.val.length = edges2.val.length)
      (p : ℕ → ℕ)
      (hp_mem : ∀ k, k < edges1.val.length → p k < edges1.val.length)
      (hp_inj : ∀ k l, k < edges1.val.length → l < edges1.val.length → p k = p l → k = l)
      (hp : ∀ k, k < edges1.val.length → edges2.val[k]? = edges1.val[p k]?)
      (hq : QueriesWF edges1.val.length queries) :
      ∀ r1 r2 : alloc.vec.Vec Std.I64,
        count_pairs n edges1 queries = ok r1 →
          count_pairs n edges2 queries = ok r2 → r1 = r2 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Std.I64) (edges1 edges2 : Slice (alloc.vec.Vec Std.I64))
        (queries : Slice Std.I64) (hn : NRange n) (h1 : EdgesWF n.val edges1)
        (h2 : EdgesWF n.val edges2) (hlen : edges1.val.length = edges2.val.length)
        (p : ℕ → ℕ)
        (hp_mem : ∀ k, k < edges1.val.length → p k < edges1.val.length)
        (hp_inj : ∀ k l, k < edges1.val.length → l < edges1.val.length → p k = p l → k = l)
        (hp : ∀ k, k < edges1.val.length → edges2.val[k]? = edges1.val[p k]?)
        (hq : QueriesWF edges1.val.length queries), ∀ r1 r2 : alloc.vec.Vec Std.I64,
          count_pairs n edges1 queries = ok r1 →
            count_pairs n edges2 queries = ok r2 → r1 = r2) := by
    sorry

  /-- Whenever count_pairs(n, edges, queries) returns r and count_pairs(n, edges_rev, queries) returns r_rev, r = r_rev.
    Preconditions: n is an integer with 2 <= n <= 20000. edges and edges_rev are slices of vectors, each satisfying 1 <= len <= 100000, every element has length 2, both entries are in {1,...,n}, and the two entries are distinct. Assume len(edges) = len(edges_rev) and for every k with 0 <= k < len(edges), edges_rev[k] has length 2 and edges_rev[k][0] = edges[k][1] and edges_rev[k][1] = edges[k][0]. queries is a slice with 1 <= len(queries) <= 20 and 0 <= queries[j] < len(edges) for every j. -/
  theorem spec_14 (n : Std.I64) (edges edges_rev : Slice (alloc.vec.Vec Std.I64))
      (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
      (he_rev : EdgesWF n.val edges_rev)
      (hlen : edges.val.length = edges_rev.val.length)
      (hrev : ∀ k, k < edges.val.length →
        edgeAt edges_rev k = (edgeAt edges k).map fun q => (q.2, q.1))
      (hq : QueriesWF edges.val.length queries) :
      ∀ r r_rev : alloc.vec.Vec Std.I64,
        count_pairs n edges queries = ok r →
          count_pairs n edges_rev queries = ok r_rev → r = r_rev := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : Std.I64) (edges edges_rev : Slice (alloc.vec.Vec Std.I64))
        (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
        (he_rev : EdgesWF n.val edges_rev)
        (hlen : edges.val.length = edges_rev.val.length)
        (hrev : ∀ k, k < edges.val.length →
          edgeAt edges_rev k = (edgeAt edges k).map fun q => (q.2, q.1))
        (hq : QueriesWF edges.val.length queries), ∀ r r_rev : alloc.vec.Vec Std.I64,
          count_pairs n edges queries = ok r →
            count_pairs n edges_rev queries = ok r_rev → r = r_rev) := by
    sorry

  /-- Whenever count_pairs(n, edges, queries) returns a result r and count_pairs(n, edges_sigma, queries) returns a result r_sigma, r = r_sigma.
    Preconditions: n is an integer with 2 <= n <= 20000. edges is a slice of vectors with 1 <= len(edges) <= 100000; every element edges[k] has length 2, edges[k][0] and edges[k][1] are in {1,...,n}, and edges[k][0] != edges[k][1]. Let sigma be a bijection from {1,...,n} to itself, and let edges_sigma be the slice with len(edges_sigma) = len(edges) and edges_sigma[k][0] = sigma(edges[k][0]), edges_sigma[k][1] = sigma(edges[k][1]) for every k. queries is a slice with 1 <= len(queries) <= 20; for every j with 0 <= j < len(queries), 0 <= queries[j] < len(edges). -/
  theorem spec_15 (n : Std.I64) (edges edges_sigma : Slice (alloc.vec.Vec Std.I64))
      (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
      (sigma : ℤ → ℤ)
      (hsigma_image : ∀ v : ℤ, 1 ≤ v → v ≤ n.val → 1 ≤ sigma v ∧ sigma v ≤ n.val)
      (hsigma_inj : ∀ v w : ℤ, 1 ≤ v → v ≤ n.val → 1 ≤ w → w ≤ n.val →
        sigma v = sigma w → v = w)
      (hlen : edges_sigma.val.length = edges.val.length)
      (hedges_sigma : ∀ k, k < edges.val.length →
        edgeAt edges_sigma k = (edgeAt edges k).map fun q => (sigma q.1, sigma q.2))
      (hq : QueriesWF edges.val.length queries) :
      ∀ r r_sigma : alloc.vec.Vec Std.I64,
        count_pairs n edges queries = ok r →
          count_pairs n edges_sigma queries = ok r_sigma → r = r_sigma := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (n : Std.I64) (edges edges_sigma : Slice (alloc.vec.Vec Std.I64))
        (queries : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
        (sigma : ℤ → ℤ)
        (hsigma_image : ∀ v : ℤ, 1 ≤ v → v ≤ n.val → 1 ≤ sigma v ∧ sigma v ≤ n.val)
        (hsigma_inj : ∀ v w : ℤ, 1 ≤ v → v ≤ n.val → 1 ≤ w → w ≤ n.val →
          sigma v = sigma w → v = w)
        (hlen : edges_sigma.val.length = edges.val.length)
        (hedges_sigma : ∀ k, k < edges.val.length →
          edgeAt edges_sigma k = (edgeAt edges k).map fun q => (sigma q.1, sigma q.2))
        (hq : QueriesWF edges.val.length queries), ∀ r r_sigma : alloc.vec.Vec Std.I64,
          count_pairs n edges queries = ok r →
            count_pairs n edges_sigma queries = ok r_sigma → r = r_sigma) := by
    sorry

  /-- Whenever count_pairs(n, edges, queries1) returns a result r1 and count_pairs(n, edges, queries2) returns a result r2, for every k with 0 <= k < len(queries2), r2[k] = r1[pi(k)].
    Preconditions: n is an integer with 2 <= n <= 20000. edges is a slice of vectors with 1 <= len(edges) <= 100000; every element edges[k] has length 2, edges[k][0] and edges[k][1] are in {1,...,n}, and edges[k][0] != edges[k][1]. queries1 and queries2 are slices with 1 <= len(queries1) <= 20 and 1 <= len(queries2) <= 20; for every valid index j, 0 <= queries1[j] < len(edges) and 0 <= queries2[j] < len(edges). Assume len(queries1) = len(queries2) and there is a bijection pi from {0,...,len(queries1)-1} to itself such that queries2[k] = queries1[pi(k)] for every k. -/
  theorem spec_16 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (queries1 queries2 : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
      (hq1 : QueriesWF edges.val.length queries1)
      (hq2 : QueriesWF edges.val.length queries2)
      (hlen : queries1.val.length = queries2.val.length) (pi : ℕ → ℕ)
      (hpi_mem : ∀ k, k < queries1.val.length → pi k < queries1.val.length)
      (hpi_inj : ∀ k l, k < queries1.val.length → l < queries1.val.length →
        pi k = pi l → k = l)
      (hpi : ∀ k, k < queries1.val.length → sliceEntry queries2 k = sliceEntry queries1 (pi k)) :
      ∀ r1 r2 : alloc.vec.Vec Std.I64,
        count_pairs n edges queries1 = ok r1 →
          count_pairs n edges queries2 = ok r2 →
            ∀ k, k < queries2.val.length → vecEntry r2 k = vecEntry r1 (pi k) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (queries1 queries2 : Slice Std.I64) (hn : NRange n) (he : EdgesWF n.val edges)
        (hq1 : QueriesWF edges.val.length queries1)
        (hq2 : QueriesWF edges.val.length queries2)
        (hlen : queries1.val.length = queries2.val.length) (pi : ℕ → ℕ)
        (hpi_mem : ∀ k, k < queries1.val.length → pi k < queries1.val.length)
        (hpi_inj : ∀ k l, k < queries1.val.length → l < queries1.val.length →
          pi k = pi l → k = l)
        (hpi : ∀ k, k < queries1.val.length → sliceEntry queries2 k = sliceEntry queries1 (pi k)), ∀ r1 r2 : alloc.vec.Vec Std.I64,
          count_pairs n edges queries1 = ok r1 →
            count_pairs n edges queries2 = ok r2 →
              ∀ k, k < queries2.val.length → vecEntry r2 k = vecEntry r1 (pi k)) := by
    sorry

  /-- Whenever count_pairs(n, edges1, queries) returns a result r1 and count_pairs(n, edges2, queries) returns a result r2, for every j with 0 <= j < len(queries), r1[j] <= r2[j].
    Preconditions: n is an integer with 2 <= n <= 20000. edges1 and edges2 are slices of vectors, each with 1 <= len <= 100000; every element has length 2, both entries are in {1,...,n}, and the two entries are distinct. For every vector e, let count1(e) = |{ k : 0 <= k < len(edges1) and edges1[k] = e }| and count2(e) = |{ k : 0 <= k < len(edges2) and edges2[k] = e }|; assume count1(e) <= count2(e) for every e. queries is a slice with 1 <= len(queries) <= 20; for every j with 0 <= j < len(queries), 0 <= queries[j] < len(edges1) and 0 <= queries[j] < len(edges2). -/
  theorem spec_17 (n : Std.I64) (edges1 edges2 : Slice (alloc.vec.Vec Std.I64))
      (queries : Slice Std.I64) (hn : NRange n) (h1 : EdgesWF n.val edges1)
      (h2 : EdgesWF n.val edges2)
      (hmult : ∀ a b : ℤ, edgeMult edges1 a b ≤ edgeMult edges2 a b)
      (hq1 : QueriesWF edges1.val.length queries)
      (hq2 : QueriesWF edges2.val.length queries) :
      ∀ r1 r2 : alloc.vec.Vec Std.I64,
        count_pairs n edges1 queries = ok r1 →
          count_pairs n edges2 queries = ok r2 →
            ∀ j, j < queries.val.length →
              ∃ x y : ℤ, vecEntry r1 j = some x ∧ vecEntry r2 j = some y ∧ x ≤ y := by
    sorry

  theorem spec_17_neg :
      ¬ (∀ (n : Std.I64) (edges1 edges2 : Slice (alloc.vec.Vec Std.I64))
        (queries : Slice Std.I64) (hn : NRange n) (h1 : EdgesWF n.val edges1)
        (h2 : EdgesWF n.val edges2)
        (hmult : ∀ a b : ℤ, edgeMult edges1 a b ≤ edgeMult edges2 a b)
        (hq1 : QueriesWF edges1.val.length queries)
        (hq2 : QueriesWF edges2.val.length queries), ∀ r1 r2 : alloc.vec.Vec Std.I64,
          count_pairs n edges1 queries = ok r1 →
            count_pairs n edges2 queries = ok r2 →
              ∀ j, j < queries.val.length →
                ∃ x y : ℤ, vecEntry r1 j = some x ∧ vecEntry r2 j = some y ∧ x ≤ y) := by
    sorry

  end AegisSpec.CountPairs
