import Aegis.QueryResults.Code.Funs

/-!
# Specifications of `Aegis.QueryResults.query_results`

LeetCode problem `find-the-number-of-distinct-colors-among-the-balls`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.QueryResults

namespace AegisSpec.QueryResults

attribute [local instance] Classical.propDecidable

def ival (s : Std.I64) : Int := s.val

def qpairs (queries : Slice (alloc.vec.Vec Std.I64)) : List (Int × Int) :=
  queries.val.map (fun v => (((v.val[0]?).map ival).getD 0, ((v.val[1]?).map ival).getD 0))

def qLen (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Nat :=
  ((queries.val[i]?).map (fun v => v.val.length)).getD 0

def qBall (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
  (((qpairs queries)[i]?).map (fun p => p.1)).getD 0

def qColor (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
  (((qpairs queries)[i]?).map (fun p => p.2)).getD 0

def resAt (r : alloc.vec.Vec Std.I64) (i : Nat) : Int :=
  ((r.val[i]?).map ival).getD 0

def colorAfter (qs : List (Int × Int)) (x : Int) (k : Nat) : Option Int :=
  (((qs.take k).filter (fun p => p.1 = x)).getLast?).map (fun p => p.2)

def coloredAfter (qs : List (Int × Int)) (x : Int) (k : Nat) : Prop :=
  ∃ c, colorAfter qs x k = some c

def distinctColors (qs : List (Int × Int)) (limit : Int) (k : Nat) : Nat :=
  (((List.range (limit.toNat + 1)).filterMap (fun b => colorAfter qs (b : Int) k)).dedup).length

def distinctColorVals (qs : List (Int × Int)) (k : Nat) : Nat :=
  (((qs.take k).map (fun p => p.2)).dedup).length

def distinctBallVals (qs : List (Int × Int)) (k : Nat) : Nat :=
  (((qs.take k).map (fun p => p.1)).dedup).length

/-- Whenever query_results(limit, queries) returns a result r, len(r) = n, and for every i with 0 <= i < n, r[i] equals the number of distinct colors c for which there exists a ball label x with 0 <= x <= limit whose color after the first i+1 queries is c. For a prefix of j+1 queries with 0 <= j < n, the color of ball x after that prefix is defined as follows: if some query index k with 0 <= k <= j has queries[k][0] = x, take the largest such k; then ball x has color queries[k][1]; if no such k exists, ball x is uncolored. Uncolored balls do not contribute a color.
  Preconditions: limit is an I64 with 1 <= limit <= 10^9; queries is a slice of Vec I64; let n = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, len(queries[i]) = 2, 0 <= queries[i][0] <= limit, and 1 <= queries[i][1] <= 10^9. -/
theorem spec_1 (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9) :
    ∀ r, query_results limit queries = ok r →
      r.val.length = queries.val.length ∧
        ∀ i, i < queries.val.length →
          resAt r i = (distinctColors (qpairs queries) limit.val (i + 1) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9), ∀ r, query_results limit queries = ok r →
      r.val.length = queries.val.length ∧
        ∀ i, i < queries.val.length →
          resAt r i = (distinctColors (qpairs queries) limit.val (i + 1) : Int)) := by
  sorry

/-- query_results(limit, queries) returns a result r; it does not fail, overflow, read out of bounds, or panic.
  Preconditions: limit is an I64 with 1 <= limit <= 10^9; queries is a slice of Vec I64; let n = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, len(queries[i]) = 2, 0 <= queries[i][0] <= limit, and 1 <= queries[i][1] <= 10^9. -/
theorem spec_2 (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9) :
    ∃ r, query_results limit queries = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9), ∃ r, query_results limit queries = ok r) := by
  sorry

/-- Whenever query_results(limit, queries) returns a result r, for every i with 0 <= i < n, 1 <= r[i] <= i+1.
  Preconditions: limit is an I64 with 1 <= limit <= 10^9; queries is a slice of Vec I64; let n = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, len(queries[i]) = 2, 0 <= queries[i][0] <= limit, and 1 <= queries[i][1] <= 10^9. -/
theorem spec_3 (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9) :
    ∀ r, query_results limit queries = ok r →
      ∀ i, i < queries.val.length →
        1 ≤ resAt r i ∧ resAt r i ≤ (i : Int) + 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9), ∀ r, query_results limit queries = ok r →
      ∀ i, i < queries.val.length →
        1 ≤ resAt r i ∧ resAt r i ≤ (i : Int) + 1) := by
  sorry

/-- Whenever query_results(limit, queries) returns a result r, for every i with 0 <= i < n, if queries[j][0] = queries[0][0] for every j with 0 <= j <= i, then r[i] = 1.
  Preconditions: limit is an I64 with 1 <= limit <= 10^9; queries is a slice of Vec I64; let n = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, len(queries[i]) = 2, 0 <= queries[i][0] <= limit, and 1 <= queries[i][1] <= 10^9. -/
theorem spec_4 (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9) :
    ∀ r, query_results limit queries = ok r →
      ∀ i, i < queries.val.length →
        (∀ j, j ≤ i → qBall queries j = qBall queries 0) → resAt r i = 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9), ∀ r, query_results limit queries = ok r →
      ∀ i, i < queries.val.length →
        (∀ j, j ≤ i → qBall queries j = qBall queries 0) → resAt r i = 1) := by
  sorry

/-- Whenever query_results(limit, queries) returns a result r, for every i with 0 <= i < n, if queries[j][1] = queries[0][1] for every j with 0 <= j <= i, then r[i] = 1.
  Preconditions: limit is an I64 with 1 <= limit <= 10^9; queries is a slice of Vec I64; let n = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, len(queries[i]) = 2, 0 <= queries[i][0] <= limit, and 1 <= queries[i][1] <= 10^9. -/
theorem spec_5 (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9) :
    ∀ r, query_results limit queries = ok r →
      ∀ i, i < queries.val.length →
        (∀ j, j ≤ i → qColor queries j = qColor queries 0) → resAt r i = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9), ∀ r, query_results limit queries = ok r →
      ∀ i, i < queries.val.length →
        (∀ j, j ≤ i → qColor queries j = qColor queries 0) → resAt r i = 1) := by
  sorry

/-- Whenever query_results(limit, queries) returns a result r, for every i with 0 <= i < n, r[i] <= |{ queries[j][1] | 0 <= j <= i }|, i.e. r[i] is at most the number of distinct colors appearing as the second component in the first i+1 queries.
  Preconditions: limit is an I64 with 1 <= limit <= 10^9; queries is a slice of Vec I64; let n = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, len(queries[i]) = 2, 0 <= queries[i][0] <= limit, and 1 <= queries[i][1] <= 10^9. -/
theorem spec_6 (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9) :
    ∀ r, query_results limit queries = ok r →
      ∀ i, i < queries.val.length →
        resAt r i ≤ (distinctColorVals (qpairs queries) (i + 1) : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9), ∀ r, query_results limit queries = ok r →
      ∀ i, i < queries.val.length →
        resAt r i ≤ (distinctColorVals (qpairs queries) (i + 1) : Int)) := by
  sorry

/-- Whenever query_results(limit, queries) returns a result r, for every i with 0 <= i < n, r[i] <= |{ queries[j][0] | 0 <= j <= i }|, i.e. r[i] is at most the number of distinct ball labels mentioned in the first i+1 queries.
  Preconditions: limit is an I64 with 1 <= limit <= 10^9; queries is a slice of Vec I64; let n = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, len(queries[i]) = 2, 0 <= queries[i][0] <= limit, and 1 <= queries[i][1] <= 10^9. -/
theorem spec_7 (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9) :
    ∀ r, query_results limit queries = ok r →
      ∀ i, i < queries.val.length →
        resAt r i ≤ (distinctBallVals (qpairs queries) (i + 1) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9), ∀ r, query_results limit queries = ok r →
      ∀ i, i < queries.val.length →
        resAt r i ≤ (distinctBallVals (qpairs queries) (i + 1) : Int)) := by
  sorry

/-- Whenever query_results(limit, queries) returns a result r, for every i with 1 <= i < n, -1 <= r[i] - r[i-1] <= 1.
  Preconditions: limit is an I64 with 1 <= limit <= 10^9; queries is a slice of Vec I64; let n = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, len(queries[i]) = 2, 0 <= queries[i][0] <= limit, and 1 <= queries[i][1] <= 10^9. -/
theorem spec_8 (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9) :
    ∀ r, query_results limit queries = ok r →
      ∀ i, 1 ≤ i → i < queries.val.length →
        -1 ≤ resAt r i - resAt r (i - 1) ∧ resAt r i - resAt r (i - 1) ≤ 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9), ∀ r, query_results limit queries = ok r →
      ∀ i, 1 ≤ i → i < queries.val.length →
        -1 ≤ resAt r i - resAt r (i - 1) ∧ resAt r i - resAt r (i - 1) ≤ 1) := by
  sorry

/-- Whenever query_results(limit, queries) returns a result r, for every i with 1 <= i < n, let x = queries[i][0] and y = queries[i][1]. Consider the state after the first i queries, i.e. the prefix ending at index i-1. Define old_unique to be true iff ball x has a color c in that state with c != y and no ball z with z != x has color c in that state. Define new_absent to be true iff no ball z with 0 <= z <= limit has color y in that state. Then r[i] = r[i-1] + (1 if new_absent else 0) - (1 if old_unique else 0).
  Preconditions: limit is an I64 with 1 <= limit <= 10^9; queries is a slice of Vec I64; let n = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, len(queries[i]) = 2, 0 <= queries[i][0] <= limit, and 1 <= queries[i][1] <= 10^9. -/
theorem spec_9 (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9) :
    ∀ r, query_results limit queries = ok r →
      ∀ i, 1 ≤ i → i < queries.val.length →
        resAt r i =
          resAt r (i - 1)
            + (if ∀ z, 0 ≤ z → z ≤ limit.val →
                  colorAfter (qpairs queries) z i ≠ some (qColor queries i)
               then (1 : Int) else 0)
            - (if ∃ c, colorAfter (qpairs queries) (qBall queries i) i = some c ∧
                       c ≠ qColor queries i ∧
                       (∀ z, z ≠ qBall queries i →
                          colorAfter (qpairs queries) z i ≠ some c)
               then (1 : Int) else 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9), ∀ r, query_results limit queries = ok r →
      ∀ i, 1 ≤ i → i < queries.val.length →
        resAt r i =
          resAt r (i - 1)
            + (if ∀ z, 0 ≤ z → z ≤ limit.val →
                  colorAfter (qpairs queries) z i ≠ some (qColor queries i)
               then (1 : Int) else 0)
            - (if ∃ c, colorAfter (qpairs queries) (qBall queries i) i = some c ∧
                       c ≠ qColor queries i ∧
                       (∀ z, z ≠ qBall queries i →
                          colorAfter (qpairs queries) z i ≠ some c)
               then (1 : Int) else 0)) := by
  sorry

/-- Whenever query_results(limit, queries) returns a result r, for any I64 limit' with 1 <= limit' <= 10^9 and 0 <= queries[j][0] <= limit' for all 0 <= j < n, if query_results(limit', queries) returns r', then r' = r.
  Preconditions: limit is an I64 with 1 <= limit <= 10^9; queries is a slice of Vec I64; let n = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, len(queries[i]) = 2, 0 <= queries[i][0] <= limit, and 1 <= queries[i][1] <= 10^9. -/
theorem spec_10 (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9) :
    ∀ r, query_results limit queries = ok r →
      ∀ (limit' : Std.I64), 1 ≤ limit'.val → limit'.val ≤ 10 ^ 9 →
        (∀ j, j < queries.val.length → 0 ≤ qBall queries j ∧ qBall queries j ≤ limit'.val) →
          ∀ r', query_results limit' queries = ok r' → r'.val = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9), ∀ r, query_results limit queries = ok r →
      ∀ (limit' : Std.I64), 1 ≤ limit'.val → limit'.val ≤ 10 ^ 9 →
        (∀ j, j < queries.val.length → 0 ≤ qBall queries j ∧ qBall queries j ≤ limit'.val) →
          ∀ r', query_results limit' queries = ok r' → r'.val = r.val) := by
  sorry

/-- Let C = { queries[j][1] | 0 <= j < n }. Suppose f is a function from C to I64 that is injective on C and satisfies 1 <= f(c) <= 10^9 for every c in C. Let queries' be a slice of Vec I64 with len(queries') = n such that for every j with 0 <= j < n, len(queries'[j]) = 2, queries'[j][0] = queries[j][0], and queries'[j][1] = f(queries[j][1]). Whenever query_results(limit, queries) returns r and query_results(limit, queries') returns r', we have r' = r.
  Preconditions: limit is an I64 with 1 <= limit <= 10^9; queries is a slice of Vec I64; let n = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, len(queries[i]) = 2, 0 <= queries[i][0] <= limit, and 1 <= queries[i][1] <= 10^9. -/
theorem spec_11 (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9)
    (f : Int → Int)
    (h_f_inj : ∀ c₁, (∃ j, j < queries.val.length ∧ qColor queries j = c₁) →
      ∀ c₂, (∃ j, j < queries.val.length ∧ qColor queries j = c₂) →
        f c₁ = f c₂ → c₁ = c₂)
    (h_f_lo : ∀ c, (∃ j, j < queries.val.length ∧ qColor queries j = c) → 1 ≤ f c)
    (h_f_hi : ∀ c, (∃ j, j < queries.val.length ∧ qColor queries j = c) → f c ≤ 10 ^ 9)
    (queries' : Slice (alloc.vec.Vec Std.I64))
    (h_q'_len : queries'.val.length = queries.val.length)
    (h_q'_inner : ∀ j, j < queries.val.length → qLen queries' j = 2)
    (h_q'_ball : ∀ j, j < queries.val.length → qBall queries' j = qBall queries j)
    (h_q'_color : ∀ j, j < queries.val.length →
      qColor queries' j = f (qColor queries j)) :
    ∀ r r', query_results limit queries = ok r → query_results limit queries' = ok r' →
      r'.val = r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9)
    (f : Int → Int)
    (h_f_inj : ∀ c₁, (∃ j, j < queries.val.length ∧ qColor queries j = c₁) →
      ∀ c₂, (∃ j, j < queries.val.length ∧ qColor queries j = c₂) →
        f c₁ = f c₂ → c₁ = c₂)
    (h_f_lo : ∀ c, (∃ j, j < queries.val.length ∧ qColor queries j = c) → 1 ≤ f c)
    (h_f_hi : ∀ c, (∃ j, j < queries.val.length ∧ qColor queries j = c) → f c ≤ 10 ^ 9)
    (queries' : Slice (alloc.vec.Vec Std.I64))
    (h_q'_len : queries'.val.length = queries.val.length)
    (h_q'_inner : ∀ j, j < queries.val.length → qLen queries' j = 2)
    (h_q'_ball : ∀ j, j < queries.val.length → qBall queries' j = qBall queries j)
    (h_q'_color : ∀ j, j < queries.val.length →
      qColor queries' j = f (qColor queries j)), ∀ r r', query_results limit queries = ok r → query_results limit queries' = ok r' →
      r'.val = r.val) := by
  sorry

/-- Whenever query_results(limit, queries) returns a result r, for every i with 0 <= i < n, there exists a set X of exactly r[i] ball labels in [0, limit] such that every ball in X is colored after the first i+1 queries and the colors of the balls in X are pairwise distinct; and every set Y of ball labels in [0, limit] such that every ball in Y is colored after the first i+1 queries and the colors of the balls in Y are pairwise distinct has |Y| <= r[i].
  Preconditions: limit is an I64 with 1 <= limit <= 10^9; queries is a slice of Vec I64; let n = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, len(queries[i]) = 2, 0 <= queries[i][0] <= limit, and 1 <= queries[i][1] <= 10^9. -/
theorem spec_12 (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9) :
    ∀ r, query_results limit queries = ok r →
      ∀ i, i < queries.val.length →
        ∃ X : Finset Int,
          (X.card : Int) = resAt r i ∧
            (∀ x ∈ X, 0 ≤ x ∧ x ≤ limit.val) ∧
            (∀ x ∈ X, coloredAfter (qpairs queries) x (i + 1)) ∧
            (∀ x ∈ X, ∀ y ∈ X, x ≠ y →
              colorAfter (qpairs queries) x (i + 1) ≠
                colorAfter (qpairs queries) y (i + 1)) ∧
            ∀ Y : Finset Int,
              (∀ y ∈ Y, 0 ≤ y ∧ y ≤ limit.val) →
                (∀ y ∈ Y, coloredAfter (qpairs queries) y (i + 1)) →
                  (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z →
                    colorAfter (qpairs queries) y (i + 1) ≠
                      colorAfter (qpairs queries) z (i + 1)) →
                    (Y.card : Int) ≤ resAt r i := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9), ∀ r, query_results limit queries = ok r →
      ∀ i, i < queries.val.length →
        ∃ X : Finset Int,
          (X.card : Int) = resAt r i ∧
            (∀ x ∈ X, 0 ≤ x ∧ x ≤ limit.val) ∧
            (∀ x ∈ X, coloredAfter (qpairs queries) x (i + 1)) ∧
            (∀ x ∈ X, ∀ y ∈ X, x ≠ y →
              colorAfter (qpairs queries) x (i + 1) ≠
                colorAfter (qpairs queries) y (i + 1)) ∧
            ∀ Y : Finset Int,
              (∀ y ∈ Y, 0 ≤ y ∧ y ≤ limit.val) →
                (∀ y ∈ Y, coloredAfter (qpairs queries) y (i + 1)) →
                  (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z →
                    colorAfter (qpairs queries) y (i + 1) ≠
                      colorAfter (qpairs queries) z (i + 1)) →
                    (Y.card : Int) ≤ resAt r i) := by
  sorry

/-- Whenever query_results(limit, queries) returns a result r, for every i with 0 <= i < n, if queries[j][0] != queries[k][0] for all 0 <= k < j <= i, then r[i] = |{ queries[j][1] | 0 <= j <= i }|, i.e. r[i] equals the number of distinct colors among the first i+1 queries.
  Preconditions: limit is an I64 with 1 <= limit <= 10^9; queries is a slice of Vec I64; let n = len(queries); 1 <= n <= 10^5; for every i with 0 <= i < n, len(queries[i]) = 2, 0 <= queries[i][0] <= limit, and 1 <= queries[i][1] <= 10^9. -/
theorem spec_13 (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9) :
    ∀ r, query_results limit queries = ok r →
      ∀ i, i < queries.val.length →
        (∀ j k, k < j → j ≤ i → qBall queries j ≠ qBall queries k) →
          resAt r i = (distinctColorVals (qpairs queries) (i + 1) : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (limit : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (h_lim_lo : 1 ≤ limit.val) (h_lim_hi : limit.val ≤ 10 ^ 9)
    (h_n_lo : 1 ≤ queries.val.length) (h_n_hi : queries.val.length ≤ 10 ^ 5)
    (h_len : ∀ i, i < queries.val.length → qLen queries i = 2)
    (h_ball_lo : ∀ i, i < queries.val.length → 0 ≤ qBall queries i)
    (h_ball_hi : ∀ i, i < queries.val.length → qBall queries i ≤ limit.val)
    (h_col_lo : ∀ i, i < queries.val.length → 1 ≤ qColor queries i)
    (h_col_hi : ∀ i, i < queries.val.length → qColor queries i ≤ 10 ^ 9), ∀ r, query_results limit queries = ok r →
      ∀ i, i < queries.val.length →
        (∀ j k, k < j → j ≤ i → qBall queries j ≠ qBall queries k) →
          resAt r i = (distinctColorVals (qpairs queries) (i + 1) : Int)) := by
  sorry

end AegisSpec.QueryResults
