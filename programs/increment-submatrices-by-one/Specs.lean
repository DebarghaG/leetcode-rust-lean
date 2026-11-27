import Aegis.RangeAddQueries.Code.Funs

/-!
# Specifications of `Aegis.RangeAddQueries.range_add_queries`

LeetCode problem `increment-submatrices-by-one`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.RangeAddQueries

namespace AegisSpec.RangeAddQueries

def cell (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (x y : Nat) : Int :=
  match r.val[x]? with
  | none => 0
  | some row =>
    match row.val[y]? with
    | none => 0
    | some v => v.val

def rowLen (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (x : Nat) : Nat :=
  match r.val[x]? with
  | none => 0
  | some row => row.val.length

def qcoord (queries : Slice (alloc.vec.Vec Std.I64)) (k j : Nat) : Int :=
  match queries.val[k]? with
  | none => 0
  | some q =>
    match q.val[j]? with
    | none => 0
    | some v => v.val

def covers (queries : Slice (alloc.vec.Vec Std.I64)) (k x y : Nat) : Prop :=
  qcoord queries k 0 ≤ (x : Int) ∧ (x : Int) ≤ qcoord queries k 2 ∧
    qcoord queries k 1 ≤ (y : Int) ∧ (y : Int) ≤ qcoord queries k 3

instance coversDecidable (queries : Slice (alloc.vec.Vec Std.I64)) (k x y : Nat) :
    Decidable (covers queries k x y) :=
  inferInstanceAs (Decidable (qcoord queries k 0 ≤ (x : Int) ∧ (x : Int) ≤ qcoord queries k 2 ∧
    qcoord queries k 1 ≤ (y : Int) ∧ (y : Int) ≤ qcoord queries k 3))

def coverCount (queries : Slice (alloc.vec.Vec Std.I64)) (x y : Nat) : Nat :=
  ((Finset.range queries.val.length).filter (fun k => covers queries k x y)).card

def queryArea (queries : Slice (alloc.vec.Vec Std.I64)) (k : Nat) : Int :=
  (qcoord queries k 2 - qcoord queries k 0 + 1) * (qcoord queries k 3 - qcoord queries k 1 + 1)

def queryHeight (queries : Slice (alloc.vec.Vec Std.I64)) (k : Nat) : Int :=
  qcoord queries k 2 - qcoord queries k 0 + 1

def queryWidth (queries : Slice (alloc.vec.Vec Std.I64)) (k : Nat) : Int :=
  qcoord queries k 3 - qcoord queries k 1 + 1

def Precondition (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  1 ≤ n.val ∧ n.val ≤ 500 ∧
    1 ≤ queries.val.length ∧ queries.val.length ≤ 10000 ∧
    (∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val)

/-- The function returns a result r such that len(r) = n and, for every x with 0 <= x < n, len(r[x]) = n; moreover, for every x,y with 0 <= x < n and 0 <= y < n, r[x][y] is the number of indices k with 0 <= k < len(queries) for which queries[k][0] <= x <= queries[k][2] and queries[k][1] <= y <= queries[k][3]. Equivalently, r is exactly the n by n matrix obtained from the all-zero matrix by adding 1, for each k, to every cell in the inclusive rectangle [queries[k][0]..queries[k][2]] times [queries[k][1]..queries[k][3]].
  Preconditions: n is an integer with 1 <= n <= 500. queries is a slice with 1 <= len(queries) <= 10000. For every k with 0 <= k < len(queries), len(queries[k]) = 4, and if queries[k] = [row1_k, col1_k, row2_k, col2_k], then 0 <= row1_k <= row2_k < n and 0 <= col1_k <= col2_k < n. All coordinates are 0-based row and column indices. -/
theorem spec_1 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      range_add_queries n queries = ok r ∧
        r.val.length = n.val.toNat ∧
        (∀ x : Nat, x < n.val.toNat → rowLen r x = n.val.toNat) ∧
        (∀ x : Nat, x < n.val.toNat → ∀ y : Nat, y < n.val.toNat →
          cell r x y = (coverCount queries x y : Int)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      range_add_queries n queries = ok r ∧
        r.val.length = n.val.toNat ∧
        (∀ x : Nat, x < n.val.toNat → rowLen r x = n.val.toNat) ∧
        (∀ x : Nat, x < n.val.toNat → ∀ y : Nat, y < n.val.toNat →
          cell r x y = (coverCount queries x y : Int))) := by
  sorry

/-- Whenever the inputs satisfy the preconditions, the function returns a result r; it does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: n is an integer with 1 <= n <= 500. queries is a slice with 1 <= len(queries) <= 10000. For every k with 0 <= k < len(queries), len(queries[k]) = 4, and if queries[k] = [row1_k, col1_k, row2_k, col2_k], then 0 <= row1_k <= row2_k < n and 0 <= col1_k <= col2_k < n. -/
theorem spec_2 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r) := by
  sorry

/-- Whenever the function returns a result r, r has exactly n rows and every row has exactly n entries: len(r) = n and, for every i with 0 <= i < n, len(r[i]) = n.
  Preconditions: n is an integer with 1 <= n <= 500. queries is a slice with 1 <= len(queries) <= 10000. For every k with 0 <= k < len(queries), len(queries[k]) = 4, and if queries[k] = [row1_k, col1_k, row2_k, col2_k], then 0 <= row1_k <= row2_k < n and 0 <= col1_k <= col2_k < n. -/
theorem spec_3 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      r.val.length = n.val.toNat ∧
        (∀ x : Nat, x < n.val.toNat → rowLen r x = n.val.toNat) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      r.val.length = n.val.toNat ∧
        (∀ x : Nat, x < n.val.toNat → rowLen r x = n.val.toNat)) := by
  sorry

/-- Whenever the function returns a result r, for every x,y with 0 <= x < n and 0 <= y < n, 0 <= r[x][y].
  Preconditions: n is an integer with 1 <= n <= 500. queries is a slice with 1 <= len(queries) <= 10000. For every k with 0 <= k < len(queries), len(queries[k]) = 4, and if queries[k] = [row1_k, col1_k, row2_k, col2_k], then 0 <= row1_k <= row2_k < n and 0 <= col1_k <= col2_k < n. -/
theorem spec_4 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      ∀ x : Nat, x < n.val.toNat → ∀ y : Nat, y < n.val.toNat → 0 ≤ cell r x y := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      ∀ x : Nat, x < n.val.toNat → ∀ y : Nat, y < n.val.toNat → 0 ≤ cell r x y) := by
  sorry

/-- Whenever the function returns a result r, for every x,y with 0 <= x < n and 0 <= y < n, r[x][y] <= len(queries).
  Preconditions: n is an integer with 1 <= n <= 500. queries is a slice with 1 <= len(queries) <= 10000. For every k with 0 <= k < len(queries), len(queries[k]) = 4, and if queries[k] = [row1_k, col1_k, row2_k, col2_k], then 0 <= row1_k <= row2_k < n and 0 <= col1_k <= col2_k < n. -/
theorem spec_5 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      ∀ x : Nat, x < n.val.toNat → ∀ y : Nat, y < n.val.toNat →
        cell r x y ≤ (queries.val.length : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      ∀ x : Nat, x < n.val.toNat → ∀ y : Nat, y < n.val.toNat →
        cell r x y ≤ (queries.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, the sum of all entries of r equals the total area covered by all queries: Σ_{x=0}^{n-1} Σ_{y=0}^{n-1} r[x][y] = Σ_{k=0}^{len(queries)-1} (queries[k][2] - queries[k][0] + 1) * (queries[k][3] - queries[k][1] + 1).
  Preconditions: n is an integer with 1 <= n <= 500. queries is a slice with 1 <= len(queries) <= 10000. For every k with 0 <= k < len(queries), len(queries[k]) = 4, and if queries[k] = [row1_k, col1_k, row2_k, col2_k], then 0 <= row1_k <= row2_k < n and 0 <= col1_k <= col2_k < n. -/
theorem spec_6 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      (∑ x ∈ Finset.range n.val.toNat, ∑ y ∈ Finset.range n.val.toNat, cell r x y)
        = ∑ k ∈ Finset.range queries.val.length, queryArea queries k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      (∑ x ∈ Finset.range n.val.toNat, ∑ y ∈ Finset.range n.val.toNat, cell r x y)
        = ∑ k ∈ Finset.range queries.val.length, queryArea queries k) := by
  sorry

/-- Whenever the function returns a result r, for every x with 0 <= x < n, Σ_{y=0}^{n-1} r[x][y] = Σ_{k: 0 <= k < len(queries) and queries[k][0] <= x <= queries[k][2]} (queries[k][3] - queries[k][1] + 1).
  Preconditions: n is an integer with 1 <= n <= 500. queries is a slice with 1 <= len(queries) <= 10000. For every k with 0 <= k < len(queries), len(queries[k]) = 4, and if queries[k] = [row1_k, col1_k, row2_k, col2_k], then 0 <= row1_k <= row2_k < n and 0 <= col1_k <= col2_k < n. -/
theorem spec_7 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      ∀ x : Nat, x < n.val.toNat →
        (∑ y ∈ Finset.range n.val.toNat, cell r x y)
          = ∑ k ∈ (Finset.range queries.val.length).filter
              (fun k => qcoord queries k 0 ≤ (x : Int) ∧ (x : Int) ≤ qcoord queries k 2),
              queryWidth queries k := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      ∀ x : Nat, x < n.val.toNat →
        (∑ y ∈ Finset.range n.val.toNat, cell r x y)
          = ∑ k ∈ (Finset.range queries.val.length).filter
              (fun k => qcoord queries k 0 ≤ (x : Int) ∧ (x : Int) ≤ qcoord queries k 2),
              queryWidth queries k) := by
  sorry

/-- Whenever the function returns a result r, for every y with 0 <= y < n, Σ_{x=0}^{n-1} r[x][y] = Σ_{k: 0 <= k < len(queries) and queries[k][1] <= y <= queries[k][3]} (queries[k][2] - queries[k][0] + 1).
  Preconditions: n is an integer with 1 <= n <= 500. queries is a slice with 1 <= len(queries) <= 10000. For every k with 0 <= k < len(queries), len(queries[k]) = 4, and if queries[k] = [row1_k, col1_k, row2_k, col2_k], then 0 <= row1_k <= row2_k < n and 0 <= col1_k <= col2_k < n. -/
theorem spec_8 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      ∀ y : Nat, y < n.val.toNat →
        (∑ x ∈ Finset.range n.val.toNat, cell r x y)
          = ∑ k ∈ (Finset.range queries.val.length).filter
              (fun k => qcoord queries k 1 ≤ (y : Int) ∧ (y : Int) ≤ qcoord queries k 3),
              queryHeight queries k := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      ∀ y : Nat, y < n.val.toNat →
        (∑ x ∈ Finset.range n.val.toNat, cell r x y)
          = ∑ k ∈ (Finset.range queries.val.length).filter
              (fun k => qcoord queries k 1 ≤ (y : Int) ∧ (y : Int) ≤ qcoord queries k 3),
              queryHeight queries k) := by
  sorry

/-- Whenever the function returns a result r, for every x,y with 0 <= x < n and 0 <= y < n, if there is no k with 0 <= k < len(queries) such that queries[k][0] <= x <= queries[k][2] and queries[k][1] <= y <= queries[k][3], then r[x][y] = 0.
  Preconditions: n is an integer with 1 <= n <= 500. queries is a slice with 1 <= len(queries) <= 10000. For every k with 0 <= k < len(queries), len(queries[k]) = 4, and if queries[k] = [row1_k, col1_k, row2_k, col2_k], then 0 <= row1_k <= row2_k < n and 0 <= col1_k <= col2_k < n. -/
theorem spec_9 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      ∀ x : Nat, x < n.val.toNat → ∀ y : Nat, y < n.val.toNat →
        (¬ ∃ k : Nat, k < queries.val.length ∧ covers queries k x y) → cell r x y = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      ∀ x : Nat, x < n.val.toNat → ∀ y : Nat, y < n.val.toNat →
        (¬ ∃ k : Nat, k < queries.val.length ∧ covers queries k x y) → cell r x y = 0) := by
  sorry

/-- Whenever the function returns a result r, for every x,y with 0 <= x < n and 0 <= y < n, if for every k with 0 <= k < len(queries) we have queries[k][0] <= x <= queries[k][2] and queries[k][1] <= y <= queries[k][3], then r[x][y] = len(queries).
  Preconditions: n is an integer with 1 <= n <= 500. queries is a slice with 1 <= len(queries) <= 10000. For every k with 0 <= k < len(queries), len(queries[k]) = 4, and if queries[k] = [row1_k, col1_k, row2_k, col2_k], then 0 <= row1_k <= row2_k < n and 0 <= col1_k <= col2_k < n. -/
theorem spec_10 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      ∀ x : Nat, x < n.val.toNat → ∀ y : Nat, y < n.val.toNat →
        (∀ k : Nat, k < queries.val.length → covers queries k x y) →
          cell r x y = (queries.val.length : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      ∀ x : Nat, x < n.val.toNat → ∀ y : Nat, y < n.val.toNat →
        (∀ k : Nat, k < queries.val.length → covers queries k x y) →
          cell r x y = (queries.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every x,y with 0 <= x < n and 0 <= y < n, if r[x][y] > 0 then there exists k with 0 <= k < len(queries) such that queries[k][0] <= x <= queries[k][2] and queries[k][1] <= y <= queries[k][3].
  Preconditions: n is an integer with 1 <= n <= 500. queries is a slice with 1 <= len(queries) <= 10000. For every k with 0 <= k < len(queries), len(queries[k]) = 4, and if queries[k] = [row1_k, col1_k, row2_k, col2_k], then 0 <= row1_k <= row2_k < n and 0 <= col1_k <= col2_k < n. -/
theorem spec_11 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      ∀ x : Nat, x < n.val.toNat → ∀ y : Nat, y < n.val.toNat →
        0 < cell r x y → ∃ k : Nat, k < queries.val.length ∧ covers queries k x y := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      ∀ x : Nat, x < n.val.toNat → ∀ y : Nat, y < n.val.toNat →
        0 < cell r x y → ∃ k : Nat, k < queries.val.length ∧ covers queries k x y) := by
  sorry

/-- Whenever the function returns a result r, for all x1,y1,x2,y2 with 0 <= x1,y1,x2,y2 < n, if for every k with 0 <= k < len(queries), the condition (queries[k][0] <= x1 <= queries[k][2] and queries[k][1] <= y1 <= queries[k][3]) implies the condition (queries[k][0] <= x2 <= queries[k][2] and queries[k][1] <= y2 <= queries[k][3]), then r[x1][y1] <= r[x2][y2].
  Preconditions: n is an integer with 1 <= n <= 500. queries is a slice with 1 <= len(queries) <= 10000. For every k with 0 <= k < len(queries), len(queries[k]) = 4, and if queries[k] = [row1_k, col1_k, row2_k, col2_k], then 0 <= row1_k <= row2_k < n and 0 <= col1_k <= col2_k < n. -/
theorem spec_12 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      ∀ x1 : Nat, x1 < n.val.toNat → ∀ y1 : Nat, y1 < n.val.toNat →
      ∀ x2 : Nat, x2 < n.val.toNat → ∀ y2 : Nat, y2 < n.val.toNat →
        (∀ k : Nat, k < queries.val.length →
          (covers queries k x1 y1 → covers queries k x2 y2)) →
          cell r x1 y1 ≤ cell r x2 y2 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      ∀ x1 : Nat, x1 < n.val.toNat → ∀ y1 : Nat, y1 < n.val.toNat →
      ∀ x2 : Nat, x2 < n.val.toNat → ∀ y2 : Nat, y2 < n.val.toNat →
        (∀ k : Nat, k < queries.val.length →
          (covers queries k x1 y1 → covers queries k x2 y2)) →
          cell r x1 y1 ≤ cell r x2 y2) := by
  sorry

/-- Whenever the function returns a result r, for all x1,y1,x2,y2 with 0 <= x1,y1,x2,y2 < n, if for every k with 0 <= k < len(queries), the two conditions (queries[k][0] <= x1 <= queries[k][2] and queries[k][1] <= y1 <= queries[k][3]) and (queries[k][0] <= x2 <= queries[k][2] and queries[k][1] <= y2 <= queries[k][3]) are equivalent, then r[x1][y1] = r[x2][y2].
  Preconditions: n is an integer with 1 <= n <= 500. queries is a slice with 1 <= len(queries) <= 10000. For every k with 0 <= k < len(queries), len(queries[k]) = 4, and if queries[k] = [row1_k, col1_k, row2_k, col2_k], then 0 <= row1_k <= row2_k < n and 0 <= col1_k <= col2_k < n. -/
theorem spec_13 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      ∀ x1 : Nat, x1 < n.val.toNat → ∀ y1 : Nat, y1 < n.val.toNat →
      ∀ x2 : Nat, x2 < n.val.toNat → ∀ y2 : Nat, y2 < n.val.toNat →
        (∀ k : Nat, k < queries.val.length →
          (covers queries k x1 y1 ↔ covers queries k x2 y2)) →
          cell r x1 y1 = cell r x2 y2 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 500)
    (hqueries_lower : 1 ≤ queries.val.length) (hqueries_upper : queries.val.length ≤ 10000)
    (hqueries : ∀ k : Nat, k < queries.val.length →
      ∃ row1 col1 row2 col2 : Int,
        (queries.val[k]?).map (fun q => q.val.map (fun v => v.val))
            = some [row1, col1, row2, col2] ∧
          0 ≤ row1 ∧ row1 ≤ row2 ∧ row2 < n.val ∧
          0 ≤ col1 ∧ col1 ≤ col2 ∧ col2 < n.val), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), range_add_queries n queries = ok r →
      ∀ x1 : Nat, x1 < n.val.toNat → ∀ y1 : Nat, y1 < n.val.toNat →
      ∀ x2 : Nat, x2 < n.val.toNat → ∀ y2 : Nat, y2 < n.val.toNat →
        (∀ k : Nat, k < queries.val.length →
          (covers queries k x1 y1 ↔ covers queries k x2 y2)) →
          cell r x1 y1 = cell r x2 y2) := by
  sorry

end AegisSpec.RangeAddQueries
