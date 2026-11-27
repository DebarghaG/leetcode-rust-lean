import Aegis.CountServers.Code.Funs

/-!
# Specifications of `Aegis.CountServers.count_servers`

LeetCode problem `count-zero-request-servers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountServers

noncomputable section

def Hit (logs : Slice (alloc.vec.Vec Std.I64)) (lo hi s : ℤ) : Prop :=
  ∃ (v : alloc.vec.Vec Std.I64) (a b : Std.I64),
    v ∈ logs.val ∧ v.val = [a, b] ∧ a.val = s ∧ lo ≤ b.val ∧ b.val ≤ hi

def Occurs (logs : Slice (alloc.vec.Vec Std.I64)) (s : ℤ) : Prop :=
  ∃ (v : alloc.vec.Vec Std.I64) (a b : Std.I64),
    v ∈ logs.val ∧ v.val = [a, b] ∧ a.val = s

def AnyInWindow (logs : Slice (alloc.vec.Vec Std.I64)) (lo hi : ℤ) : Prop :=
  ∃ s : ℤ, Hit logs lo hi s

def numMissing (logs : Slice (alloc.vec.Vec Std.I64)) (n lo hi : ℤ) : ℕ :=
  Nat.card { s : ℤ // 1 ≤ s ∧ s ≤ n ∧ ¬ Hit logs lo hi s }

def numHit (logs : Slice (alloc.vec.Vec Std.I64)) (n lo hi : ℤ) : ℕ :=
  Nat.card { s : ℤ // 1 ≤ s ∧ s ≤ n ∧ Hit logs lo hi s }

def numUnused (logs : Slice (alloc.vec.Vec Std.I64)) (n : ℤ) : ℕ :=
  Nat.card { s : ℤ // 1 ≤ s ∧ s ≤ n ∧ ¬ Occurs logs s }

def outAt (r : alloc.vec.Vec Std.I64) (j : ℕ) : Option ℤ :=
  (r.val[j]?).map fun z => z.val

def LogsOK (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  1 ≤ logs.val.length ∧ logs.val.length ≤ 10 ^ 5 ∧
    ∀ (v : alloc.vec.Vec Std.I64) (a b : Std.I64),
      v ∈ logs.val → v.val = [a, b] →
        (1 : ℤ) ≤ a.val ∧ a.val ≤ n.val ∧ (1 : ℤ) ≤ b.val ∧ b.val ≤ (10 : ℤ) ^ 6

/-- Whenever count_servers(n, logs, x, queries) returns a result r, len(r) = len(queries) and for every j with 0 <= j < len(queries), r[j] is equal to the number of integers s with 1 <= s <= n such that there is no i with 0 <= i < len(logs), logs[i][0] = s, and queries[j] - x <= logs[i][1] <= queries[j].
  Preconditions: Assume the problem constraints: n and x are i64 values; logs is a slice of vectors of i64; queries is a slice of i64. 1 <= n <= 10^5. 1 <= len(logs) <= 10^5. For every i with 0 <= i < len(logs), len(logs[i]) = 2, 1 <= logs[i][0] <= n, and 1 <= logs[i][1] <= 10^6. 1 <= len(queries) <= 10^5. 1 <= x <= 10^5. For every j with 0 <= j < len(queries), x < queries[j] <= 10^6. -/
theorem spec_1
    (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r) :
    r.val.length = queries.val.length ∧
      ∀ (j : ℕ) (hj : j < queries.val.length),
        outAt r j =
          some (((numMissing logs n.val ((queries.val[j]).val - x.val)
            ((queries.val[j]).val) : ℕ) : ℤ)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r), r.val.length = queries.val.length ∧
      ∀ (j : ℕ) (hj : j < queries.val.length),
        outAt r j =
          some (((numMissing logs n.val ((queries.val[j]).val - x.val)
            ((queries.val[j]).val) : ℕ) : ℤ))) := by
  sorry

/-- For every input satisfying the preconditions, count_servers(n, logs, x, queries) returns a result r; evaluation does not panic, access out of bounds, or overflow.
  Preconditions: Assume the problem constraints: n and x are i64 values; logs is a slice of vectors of i64; queries is a slice of i64. 1 <= n <= 10^5. 1 <= len(logs) <= 10^5. For every i with 0 <= i < len(logs), len(logs[i]) = 2, 1 <= logs[i][0] <= n, and 1 <= logs[i][1] <= 10^6. 1 <= len(queries) <= 10^5. 1 <= x <= 10^5. For every j with 0 <= j < len(queries), x < queries[j] <= 10^6. -/
theorem spec_2
    (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6) :
    ∃ r : alloc.vec.Vec Std.I64, Aegis.CountServers.count_servers n logs x queries = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6), ∃ r : alloc.vec.Vec Std.I64, Aegis.CountServers.count_servers n logs x queries = ok r) := by
  sorry

/-- Whenever count_servers(n, logs, x, queries) returns a result r, len(r) = len(queries).
  Preconditions: Assume the problem constraints: n and x are i64 values; logs is a slice of vectors of i64; queries is a slice of i64. 1 <= n <= 10^5. 1 <= len(logs) <= 10^5. For every i with 0 <= i < len(logs), len(logs[i]) = 2, 1 <= logs[i][0] <= n, and 1 <= logs[i][1] <= 10^6. 1 <= len(queries) <= 10^5. 1 <= x <= 10^5. For every j with 0 <= j < len(queries), x < queries[j] <= 10^6. -/
theorem spec_3
    (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r) :
    r.val.length = queries.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r), r.val.length = queries.val.length) := by
  sorry

/-- Whenever count_servers(n, logs, x, queries) returns a result r, for every j with 0 <= j < len(queries), 0 <= r[j] <= n.
  Preconditions: Assume the problem constraints: n and x are i64 values; logs is a slice of vectors of i64; queries is a slice of i64. 1 <= n <= 10^5. 1 <= len(logs) <= 10^5. For every i with 0 <= i < len(logs), len(logs[i]) = 2, 1 <= logs[i][0] <= n, and 1 <= logs[i][1] <= 10^6. 1 <= len(queries) <= 10^5. 1 <= x <= 10^5. For every j with 0 <= j < len(queries), x < queries[j] <= 10^6. -/
theorem spec_4
    (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r) :
    ∀ (j : ℕ) (hj : j < queries.val.length),
      ∃ z : ℤ, outAt r j = some z ∧ 0 ≤ z ∧ z ≤ n.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r), ∀ (j : ℕ) (hj : j < queries.val.length),
      ∃ z : ℤ, outAt r j = some z ∧ 0 ≤ z ∧ z ≤ n.val) := by
  sorry

/-- Whenever count_servers(n, logs, x, queries) returns a result r, for every j with 0 <= j < len(queries), if there is no i with 0 <= i < len(logs) and queries[j] - x <= logs[i][1] <= queries[j], then r[j] = n.
  Preconditions: Assume the problem constraints: n and x are i64 values; logs is a slice of vectors of i64; queries is a slice of i64. 1 <= n <= 10^5. 1 <= len(logs) <= 10^5. For every i with 0 <= i < len(logs), len(logs[i]) = 2, 1 <= logs[i][0] <= n, and 1 <= logs[i][1] <= 10^6. 1 <= len(queries) <= 10^5. 1 <= x <= 10^5. For every j with 0 <= j < len(queries), x < queries[j] <= 10^6. -/
theorem spec_5
    (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r) :
    ∀ (j : ℕ) (hj : j < queries.val.length),
      ¬ AnyInWindow logs ((queries.val[j]).val - x.val) ((queries.val[j]).val) →
        outAt r j = some n.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r), ∀ (j : ℕ) (hj : j < queries.val.length),
      ¬ AnyInWindow logs ((queries.val[j]).val - x.val) ((queries.val[j]).val) →
        outAt r j = some n.val) := by
  sorry

/-- Whenever count_servers(n, logs, x, queries) returns a result r, for every j with 0 <= j < len(queries), if for every s with 1 <= s <= n there exists i with 0 <= i < len(logs), logs[i][0] = s, and queries[j] - x <= logs[i][1] <= queries[j], then r[j] = 0.
  Preconditions: Assume the problem constraints: n and x are i64 values; logs is a slice of vectors of i64; queries is a slice of i64. 1 <= n <= 10^5. 1 <= len(logs) <= 10^5. For every i with 0 <= i < len(logs), len(logs[i]) = 2, 1 <= logs[i][0] <= n, and 1 <= logs[i][1] <= 10^6. 1 <= len(queries) <= 10^5. 1 <= x <= 10^5. For every j with 0 <= j < len(queries), x < queries[j] <= 10^6. -/
theorem spec_6
    (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r) :
    ∀ (j : ℕ) (hj : j < queries.val.length),
      (∀ s : ℤ, 1 ≤ s → s ≤ n.val →
          Hit logs ((queries.val[j]).val - x.val) ((queries.val[j]).val) s) →
        outAt r j = some 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r), ∀ (j : ℕ) (hj : j < queries.val.length),
      (∀ s : ℤ, 1 ≤ s → s ≤ n.val →
          Hit logs ((queries.val[j]).val - x.val) ((queries.val[j]).val) s) →
        outAt r j = some 0) := by
  sorry

/-- Whenever count_servers(n, logs, x, queries) returns a result r, for every j with 0 <= j < len(queries), r[j] = n - d_j, where d_j is the number of integers s with 1 <= s <= n for which there exists i with 0 <= i < len(logs), logs[i][0] = s, and queries[j] - x <= logs[i][1] <= queries[j].
  Preconditions: Assume the problem constraints: n and x are i64 values; logs is a slice of vectors of i64; queries is a slice of i64. 1 <= n <= 10^5. 1 <= len(logs) <= 10^5. For every i with 0 <= i < len(logs), len(logs[i]) = 2, 1 <= logs[i][0] <= n, and 1 <= logs[i][1] <= 10^6. 1 <= len(queries) <= 10^5. 1 <= x <= 10^5. For every j with 0 <= j < len(queries), x < queries[j] <= 10^6. -/
theorem spec_7
    (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r) :
    ∀ (j : ℕ) (hj : j < queries.val.length),
      outAt r j =
        some (n.val - ((numHit logs n.val ((queries.val[j]).val - x.val)
          ((queries.val[j]).val) : ℕ) : ℤ)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r), ∀ (j : ℕ) (hj : j < queries.val.length),
      outAt r j =
        some (n.val - ((numHit logs n.val ((queries.val[j]).val - x.val)
          ((queries.val[j]).val) : ℕ) : ℤ))) := by
  sorry

/-- Whenever both count_servers(n, logs, x, queries) returns r and count_servers(n, logs', x, queries) returns r', we have len(r) = len(r') and for every j with 0 <= j < len(queries), r[j] = r'[j].
  Preconditions: Assume the problem constraints: n and x are i64 values; logs is a slice of vectors of i64; queries is a slice of i64. 1 <= n <= 10^5. 1 <= len(logs) <= 10^5. For every i with 0 <= i < len(logs), len(logs[i]) = 2, 1 <= logs[i][0] <= n, and 1 <= logs[i][1] <= 10^6. 1 <= len(queries) <= 10^5. 1 <= x <= 10^5. For every j with 0 <= j < len(queries), x < queries[j] <= 10^6. Let logs' be another slice of vectors of i64 satisfying the same constraints with respect to n and x, and such that logs' is a permutation of logs: len(logs') = len(logs) and there is a bijection pi on {0,...,len(logs)-1} with logs'[i] = logs[pi(i)] for every i. -/
theorem spec_8
    (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (logs' : Slice (alloc.vec.Vec Std.I64)) (hlogs' : LogsOK n logs')
    (hperm : List.Perm logs'.val logs.val)
    (r r' : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r)
    (hres' : Aegis.CountServers.count_servers n logs' x queries = ok r') :
    r.val.length = r'.val.length ∧
      ∀ (j : ℕ) (hj : j < queries.val.length), outAt r j = outAt r' j := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (logs' : Slice (alloc.vec.Vec Std.I64)) (hlogs' : LogsOK n logs')
    (hperm : List.Perm logs'.val logs.val)
    (r r' : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r)
    (hres' : Aegis.CountServers.count_servers n logs' x queries = ok r'), r.val.length = r'.val.length ∧
      ∀ (j : ℕ) (hj : j < queries.val.length), outAt r j = outAt r' j) := by
  sorry

/-- Whenever count_servers(n, logs, x, queries) returns a result r, for every j and k with 0 <= j < len(queries), 0 <= k < len(queries), and queries[j] = queries[k], we have r[j] = r[k].
  Preconditions: Assume the problem constraints: n and x are i64 values; logs is a slice of vectors of i64; queries is a slice of i64. 1 <= n <= 10^5. 1 <= len(logs) <= 10^5. For every i with 0 <= i < len(logs), len(logs[i]) = 2, 1 <= logs[i][0] <= n, and 1 <= logs[i][1] <= 10^6. 1 <= len(queries) <= 10^5. 1 <= x <= 10^5. For every j with 0 <= j < len(queries), x < queries[j] <= 10^6. -/
theorem spec_9
    (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r) :
    ∀ (j k : ℕ) (hj : j < queries.val.length) (hk : k < queries.val.length),
      (queries.val[j]).val = (queries.val[k]).val → outAt r j = outAt r k := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r), ∀ (j k : ℕ) (hj : j < queries.val.length) (hk : k < queries.val.length),
      (queries.val[j]).val = (queries.val[k]).val → outAt r j = outAt r k) := by
  sorry

/-- Whenever count_servers(n, logs, x, queries) returns r and count_servers(n', logs, x, queries) returns r', we have len(r) = len(r') and for every j with 0 <= j < len(queries), r'[j] = r[j] + (n' - n).
  Preconditions: Assume the problem constraints: n and x are i64 values; logs is a slice of vectors of i64; queries is a slice of i64. 1 <= n <= 10^5. 1 <= len(logs) <= 10^5. For every i with 0 <= i < len(logs), len(logs[i]) = 2, 1 <= logs[i][0] <= n, and 1 <= logs[i][1] <= 10^6. 1 <= len(queries) <= 10^5. 1 <= x <= 10^5. For every j with 0 <= j < len(queries), x < queries[j] <= 10^6. Let n' be an integer with n <= n' <= 10^5. -/
theorem spec_10
    (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (n' : Std.I64) (hn'_lo : n.val ≤ n'.val) (hn'_hi : n'.val ≤ (10 : ℤ) ^ 5)
    (r r' : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r)
    (hres' : Aegis.CountServers.count_servers n' logs x queries = ok r') :
    r.val.length = r'.val.length ∧
      ∀ (j : ℕ) (hj : j < queries.val.length),
        ∃ z : ℤ, outAt r j = some z ∧ outAt r' j = some (z + (n'.val - n.val)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (n' : Std.I64) (hn'_lo : n.val ≤ n'.val) (hn'_hi : n'.val ≤ (10 : ℤ) ^ 5)
    (r r' : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r)
    (hres' : Aegis.CountServers.count_servers n' logs x queries = ok r'), r.val.length = r'.val.length ∧
      ∀ (j : ℕ) (hj : j < queries.val.length),
        ∃ z : ℤ, outAt r j = some z ∧ outAt r' j = some (z + (n'.val - n.val))) := by
  sorry

/-- Whenever count_servers(n, logs, x, queries) returns a result r, let U be the set of integers s with 1 <= s <= n such that for every i with 0 <= i < len(logs), logs[i][0] != s. Then for every j with 0 <= j < len(queries), r[j] >= |U|.
  Preconditions: Assume the problem constraints: n and x are i64 values; logs is a slice of vectors of i64; queries is a slice of i64. 1 <= n <= 10^5. 1 <= len(logs) <= 10^5. For every i with 0 <= i < len(logs), len(logs[i]) = 2, 1 <= logs[i][0] <= n, and 1 <= logs[i][1] <= 10^6. 1 <= len(queries) <= 10^5. 1 <= x <= 10^5. For every j with 0 <= j < len(queries), x < queries[j] <= 10^6. -/
theorem spec_11
    (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r) :
    ∀ (j : ℕ) (hj : j < queries.val.length),
      ∃ z : ℤ, outAt r j = some z ∧ ((numUnused logs n.val : ℕ) : ℤ) ≤ z := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r), ∀ (j : ℕ) (hj : j < queries.val.length),
      ∃ z : ℤ, outAt r j = some z ∧ ((numUnused logs n.val : ℕ) : ℤ) ≤ z) := by
  sorry

/-- Whenever both count_servers(n, logs, x, queries) returns r and count_servers(n, logs', x, queries) returns r', we have r[j] = r'[j].
  Preconditions: Assume the problem constraints: n and x are i64 values; logs is a slice of vectors of i64; queries is a slice of i64. 1 <= n <= 10^5. 1 <= len(logs) <= 10^5. For every i with 0 <= i < len(logs), len(logs[i]) = 2, 1 <= logs[i][0] <= n, and 1 <= logs[i][1] <= 10^6. 1 <= len(queries) <= 10^5. 1 <= x <= 10^5. For every j with 0 <= j < len(queries), x < queries[j] <= 10^6. Fix an index j with 0 <= j < len(queries). Let logs' be another slice of vectors of i64 satisfying the same constraints with respect to n and x, such that for every s with 1 <= s <= n, there exists i with 0 <= i < len(logs), logs[i][0] = s, and queries[j] - x <= logs[i][1] <= queries[j] if and only if there exists i' with 0 <= i' < len(logs'), logs'[i'][0] = s, and queries[j] - x <= logs'[i'][1] <= queries[j]. -/
theorem spec_12
    (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (j : ℕ) (hj : j < queries.val.length)
    (logs' : Slice (alloc.vec.Vec Std.I64)) (hlogs' : LogsOK n logs')
    (hsame : ∀ s : ℤ, 1 ≤ s → s ≤ n.val →
      (Hit logs ((queries.val[j]).val - x.val) ((queries.val[j]).val) s ↔
        Hit logs' ((queries.val[j]).val - x.val) ((queries.val[j]).val) s))
    (r r' : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r)
    (hres' : Aegis.CountServers.count_servers n logs' x queries = ok r') :
    outAt r j = outAt r' j := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (j : ℕ) (hj : j < queries.val.length)
    (logs' : Slice (alloc.vec.Vec Std.I64)) (hlogs' : LogsOK n logs')
    (hsame : ∀ s : ℤ, 1 ≤ s → s ≤ n.val →
      (Hit logs ((queries.val[j]).val - x.val) ((queries.val[j]).val) s ↔
        Hit logs' ((queries.val[j]).val - x.val) ((queries.val[j]).val) s))
    (r r' : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r)
    (hres' : Aegis.CountServers.count_servers n logs' x queries = ok r'), outAt r j = outAt r' j) := by
  sorry

/-- Whenever count_servers(n, logs, x, queries) returns a result r, for every j with 0 <= j < len(queries), if there exists i with 0 <= i < len(logs) and (logs[i][1] = queries[j] - x or logs[i][1] = queries[j]), then r[j] <= n - 1.
  Preconditions: Assume the problem constraints: n and x are i64 values; logs is a slice of vectors of i64; queries is a slice of i64. 1 <= n <= 10^5. 1 <= len(logs) <= 10^5. For every i with 0 <= i < len(logs), len(logs[i]) = 2, 1 <= logs[i][0] <= n, and 1 <= logs[i][1] <= 10^6. 1 <= len(queries) <= 10^5. 1 <= x <= 10^5. For every j with 0 <= j < len(queries), x < queries[j] <= 10^6. -/
theorem spec_13
    (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r) :
    ∀ (j : ℕ) (hj : j < queries.val.length),
      (∃ (v : alloc.vec.Vec Std.I64) (a b : Std.I64),
          v ∈ logs.val ∧ v.val = [a, b] ∧
            (b.val = (queries.val[j]).val - x.val ∨ b.val = (queries.val[j]).val)) →
        ∃ z : ℤ, outAt r j = some z ∧ z ≤ n.val - 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r), ∀ (j : ℕ) (hj : j < queries.val.length),
      (∃ (v : alloc.vec.Vec Std.I64) (a b : Std.I64),
          v ∈ logs.val ∧ v.val = [a, b] ∧
            (b.val = (queries.val[j]).val - x.val ∨ b.val = (queries.val[j]).val)) →
        ∃ z : ℤ, outAt r j = some z ∧ z ≤ n.val - 1) := by
  sorry

/-- Whenever count_servers(n, logs, x, queries) returns a result r, for every j with 0 <= j < len(queries), if there exists s with 1 <= s <= n such that no i with 0 <= i < len(logs) has logs[i][0] = s and queries[j] - x <= logs[i][1] <= queries[j], then r[j] >= 1.
  Preconditions: Assume the problem constraints: n and x are i64 values; logs is a slice of vectors of i64; queries is a slice of i64. 1 <= n <= 10^5. 1 <= len(logs) <= 10^5. For every i with 0 <= i < len(logs), len(logs[i]) = 2, 1 <= logs[i][0] <= n, and 1 <= logs[i][1] <= 10^6. 1 <= len(queries) <= 10^5. 1 <= x <= 10^5. For every j with 0 <= j < len(queries), x < queries[j] <= 10^6. -/
theorem spec_14
    (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r) :
    ∀ (j : ℕ) (hj : j < queries.val.length),
      (∃ s : ℤ, 1 ≤ s ∧ s ≤ n.val ∧
          ¬ Hit logs ((queries.val[j]).val - x.val) ((queries.val[j]).val) s) →
        ∃ z : ℤ, outAt r j = some z ∧ 1 ≤ z := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64)) (x : Std.I64) (queries : Slice Std.I64)
    (hn_lo : (1 : ℤ) ≤ n.val) (hn_hi : n.val ≤ (10 : ℤ) ^ 5)
    (hlogs : LogsOK n logs)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 10 ^ 5)
    (hx_lo : (1 : ℤ) ≤ x.val) (hx_hi : x.val ≤ (10 : ℤ) ^ 5)
    (hqs : ∀ (j : ℕ) (hj : j < queries.val.length),
      x.val < (queries.val[j]).val ∧ (queries.val[j]).val ≤ (10 : ℤ) ^ 6)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.CountServers.count_servers n logs x queries = ok r), ∀ (j : ℕ) (hj : j < queries.val.length),
      (∃ s : ℤ, 1 ≤ s ∧ s ≤ n.val ∧
          ¬ Hit logs ((queries.val[j]).val - x.val) ((queries.val[j]).val) s) →
        ∃ z : ℤ, outAt r j = some z ∧ 1 ≤ z) := by
  sorry

end

end AegisSpec.CountServers
