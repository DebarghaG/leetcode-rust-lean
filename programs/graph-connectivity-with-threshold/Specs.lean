import Aegis.AreConnected.Code.Funs

/-!
# Specifications of `Aegis.AreConnected.are_connected`

LeetCode problem `graph-connectivity-with-threshold`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.AreConnected

namespace AegisSpec.AreConnected

def Adjacent (threshold : ℤ) (x y : ℤ) : Prop :=
  x ≠ y ∧ ∃ z : ℤ, threshold < z ∧ z ∣ x ∧ z ∣ y

def AdjChain (threshold : ℤ) : List ℤ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => Adjacent threshold a b ∧ AdjChain threshold (b :: rest)

def IsPath (threshold n : ℤ) (x y : ℤ) : Prop :=
  ∃ c : List ℤ, c ≠ [] ∧ c.head? = some x ∧ c.getLast? = some y ∧
    (∀ v ∈ c, 1 ≤ v ∧ v ≤ n) ∧ AdjChain threshold c

def IsSimplePath (threshold n : ℤ) (x y : ℤ) : Prop :=
  ∃ c : List ℤ, 2 ≤ c.length ∧ c.Nodup ∧ c.head? = some x ∧ c.getLast? = some y ∧
    (∀ v ∈ c, 1 ≤ v ∧ v ≤ n) ∧ AdjChain threshold c

def QueryAt (queries : List (alloc.vec.Vec Std.I64)) (i : ℕ) (x y : Std.I64) : Prop :=
  (queries[i]?).map alloc.vec.Vec.val = some [x, y]

def AnsTrue (r : alloc.vec.Vec Bool) (i : ℕ) : Prop := r.val[i]? = some true

def AnsFalse (r : alloc.vec.Vec Bool) (i : ℕ) : Prop := r.val[i]? = some false

/-- Whenever the function returns a result r, r is a Vec<bool> with len(r) = len(queries), and for every i with 0 <= i < len(queries), r[i] = true exactly when there is a path between queries[i][0] and queries[i][1] in the undirected graph on cities {1,...,n} where two distinct cities x and y are adjacent iff there exists an integer z such that z > threshold, z divides x, and z divides y. A path is a finite sequence c_0,...,c_k of cities in {1,...,n} with k >= 0, c_0 = queries[i][0], c_k = queries[i][1], and every consecutive pair c_j,c_{j+1} adjacent as just defined.
  Preconditions: n, threshold, and queries satisfy: 2 <= n <= 10^4; 0 <= threshold <= n; 1 <= len(queries) <= 10^5; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= n, 1 <= queries[i][1] <= n, and queries[i][0] != queries[i][1]. -/
theorem spec_1 (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val) :
    ∀ r, are_connected n threshold queries = ok r →
      r.val.length = queries.val.length ∧
        ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
          QueryAt queries.val i x y →
            (AnsTrue r i ↔ IsPath threshold.val n.val x.val y.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val), ∀ r, are_connected n threshold queries = ok r →
      r.val.length = queries.val.length ∧
        ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
          QueryAt queries.val i x y →
            (AnsTrue r i ↔ IsPath threshold.val n.val x.val y.val)) := by
  sorry

/-- For every n, threshold, and queries satisfying the preconditions, the function returns a result r and does not fail: it does not panic, overflow, go out of bounds, or divide by zero.
  Preconditions: n, threshold, and queries satisfy: 2 <= n <= 10^4; 0 <= threshold <= n; 1 <= len(queries) <= 10^5; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= n, 1 <= queries[i][1] <= n, and queries[i][0] != queries[i][1]. -/
theorem spec_2 (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val) :
    ∃ r, are_connected n threshold queries = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val), ∃ r, are_connected n threshold queries = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(queries).
  Preconditions: n, threshold, and queries satisfy: 2 <= n <= 10^4; 0 <= threshold <= n; 1 <= len(queries) <= 10^5; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= n, 1 <= queries[i][1] <= n, and queries[i][0] != queries[i][1]. -/
theorem spec_3 (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val) :
    ∀ r, are_connected n threshold queries = ok r →
      r.val.length = queries.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val), ∀ r, are_connected n threshold queries = ok r →
      r.val.length = queries.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every i,j with 0 <= i,j < len(queries), if queries[i][0] = queries[j][1] and queries[i][1] = queries[j][0], then r[i] = r[j].
  Preconditions: n, threshold, and queries satisfy: 2 <= n <= 10^4; 0 <= threshold <= n; 1 <= len(queries) <= 10^5; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= n, 1 <= queries[i][1] <= n, and queries[i][0] != queries[i][1]. -/
theorem spec_4 (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val) :
    ∀ r, are_connected n threshold queries = ok r →
      ∀ (i j : ℕ) (x y : Std.I64), i < queries.val.length → j < queries.val.length →
        QueryAt queries.val i x y → QueryAt queries.val j y x →
          r.val[i]? = r.val[j]? := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val), ∀ r, are_connected n threshold queries = ok r →
      ∀ (i j : ℕ) (x y : Std.I64), i < queries.val.length → j < queries.val.length →
        QueryAt queries.val i x y → QueryAt queries.val j y x →
          r.val[i]? = r.val[j]?) := by
  sorry

/-- Whenever the function returns a result r, for every i,j,k with 0 <= i,j,k < len(queries), if there exist a,b,c such that queries[i] = [a,b], queries[j] = [b,c], queries[k] = [a,c], r[i] = true, and r[j] = true, then r[k] = true.
  Preconditions: n, threshold, and queries satisfy: 2 <= n <= 10^4; 0 <= threshold <= n; 1 <= len(queries) <= 10^5; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= n, 1 <= queries[i][1] <= n, and queries[i][0] != queries[i][1]. -/
theorem spec_5 (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val) :
    ∀ r, are_connected n threshold queries = ok r →
      ∀ (i j k : ℕ) (a b c : Std.I64),
        i < queries.val.length → j < queries.val.length → k < queries.val.length →
          QueryAt queries.val i a b → QueryAt queries.val j b c →
            QueryAt queries.val k a c →
              AnsTrue r i → AnsTrue r j → AnsTrue r k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val), ∀ r, are_connected n threshold queries = ok r →
      ∀ (i j k : ℕ) (a b c : Std.I64),
        i < queries.val.length → j < queries.val.length → k < queries.val.length →
          QueryAt queries.val i a b → QueryAt queries.val j b c →
            QueryAt queries.val k a c →
              AnsTrue r i → AnsTrue r j → AnsTrue r k) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), if queries[i][0] <= threshold or queries[i][1] <= threshold, then r[i] = false.
  Preconditions: n, threshold, and queries satisfy: 2 <= n <= 10^4; 0 <= threshold <= n; 1 <= len(queries) <= 10^5; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= n, 1 <= queries[i][1] <= n, and queries[i][0] != queries[i][1]. -/
theorem spec_6 (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val) :
    ∀ r, are_connected n threshold queries = ok r →
      ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
        QueryAt queries.val i x y →
          (x.val ≤ threshold.val ∨ y.val ≤ threshold.val) → AnsFalse r i := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val), ∀ r, are_connected n threshold queries = ok r →
      ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
        QueryAt queries.val i x y →
          (x.val ≤ threshold.val ∨ y.val ≤ threshold.val) → AnsFalse r i) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), r[i] = true.
  Preconditions: n, threshold, and queries satisfy: 2 <= n <= 10^4; 0 <= threshold <= n; 1 <= len(queries) <= 10^5; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= n, 1 <= queries[i][1] <= n, and queries[i][0] != queries[i][1]; additionally threshold = 0. -/
theorem spec_7 (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val)
    (hthr_zero : threshold.val = 0) :
    ∀ r, are_connected n threshold queries = ok r →
      ∀ i, i < queries.val.length → AnsTrue r i := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val)
    (hthr_zero : threshold.val = 0), ∀ r, are_connected n threshold queries = ok r →
      ∀ i, i < queries.val.length → AnsTrue r i) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), r[i] = false.
  Preconditions: n, threshold, and queries satisfy: 2 <= n <= 10^4; 0 <= threshold <= n; 1 <= len(queries) <= 10^5; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= n, 1 <= queries[i][1] <= n, and queries[i][0] != queries[i][1]; additionally threshold >= floor(n/2). -/
theorem spec_8 (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val)
    (hthr_half : n.val / 2 ≤ threshold.val) :
    ∀ r, are_connected n threshold queries = ok r →
      ∀ i, i < queries.val.length → AnsFalse r i := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val)
    (hthr_half : n.val / 2 ≤ threshold.val), ∀ r, are_connected n threshold queries = ok r →
      ∀ i, i < queries.val.length → AnsFalse r i) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), if there exists an integer z such that z > threshold, z divides queries[i][0], and z divides queries[i][1], then r[i] = true.
  Preconditions: n, threshold, and queries satisfy: 2 <= n <= 10^4; 0 <= threshold <= n; 1 <= len(queries) <= 10^5; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= n, 1 <= queries[i][1] <= n, and queries[i][0] != queries[i][1]. -/
theorem spec_9 (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val) :
    ∀ r, are_connected n threshold queries = ok r →
      ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
        QueryAt queries.val i x y →
          (∃ z : ℤ, threshold.val < z ∧ z ∣ x.val ∧ z ∣ y.val) → AnsTrue r i := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val), ∀ r, are_connected n threshold queries = ok r →
      ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
        QueryAt queries.val i x y →
          (∃ z : ℤ, threshold.val < z ∧ z ∣ x.val ∧ z ∣ y.val) → AnsTrue r i) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), if r[i] = true, then there exists an integer k >= 0 and a sequence c_0,...,c_k of integers such that 1 <= c_j <= n for every 0 <= j <= k, c_0 = queries[i][0], c_k = queries[i][1], and for every 0 <= j < k, c_j != c_{j+1} and there exists an integer z > threshold dividing both c_j and c_{j+1}.
  Preconditions: n, threshold, and queries satisfy: 2 <= n <= 10^4; 0 <= threshold <= n; 1 <= len(queries) <= 10^5; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= n, 1 <= queries[i][1] <= n, and queries[i][0] != queries[i][1]. -/
theorem spec_10 (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val) :
    ∀ r, are_connected n threshold queries = ok r →
      ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
        QueryAt queries.val i x y → AnsTrue r i → IsPath threshold.val n.val x.val y.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val), ∀ r, are_connected n threshold queries = ok r →
      ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
        QueryAt queries.val i x y → AnsTrue r i → IsPath threshold.val n.val x.val y.val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), if r[i] = false, then there does not exist an integer k >= 0 and a sequence c_0,...,c_k of integers such that 1 <= c_j <= n for every 0 <= j <= k, c_0 = queries[i][0], c_k = queries[i][1], and for every 0 <= j < k, c_j != c_{j+1} and there exists an integer z > threshold dividing both c_j and c_{j+1}.
  Preconditions: n, threshold, and queries satisfy: 2 <= n <= 10^4; 0 <= threshold <= n; 1 <= len(queries) <= 10^5; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= n, 1 <= queries[i][1] <= n, and queries[i][0] != queries[i][1]. -/
theorem spec_11 (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val) :
    ∀ r, are_connected n threshold queries = ok r →
      ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
        QueryAt queries.val i x y → AnsFalse r i → ¬ IsPath threshold.val n.val x.val y.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val), ∀ r, are_connected n threshold queries = ok r →
      ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
        QueryAt queries.val i x y → AnsFalse r i → ¬ IsPath threshold.val n.val x.val y.val) := by
  sorry

/-- If both calls return results r1 and r2, then for every i with 0 <= i < len(Q), if r2[i] = true then r1[i] = true.
  Preconditions: For all integers n, t1, t2, and all query lists Q such that 2 <= n <= 10^4, 0 <= t1 <= t2 <= n, 1 <= len(Q) <= 10^5, and for every i with 0 <= i < len(Q), len(Q[i]) = 2, 1 <= Q[i][0] <= n, 1 <= Q[i][1] <= n, and Q[i][0] != Q[i][1]. Let r1 be the result of are_connected(n,t1,Q) and r2 be the result of are_connected(n,t2,Q). -/
theorem spec_12 (n t1 t2 : Std.I64) (Q : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (ht1_lo : 0 ≤ t1.val) (ht12 : t1.val ≤ t2.val) (ht2_hi : t2.val ≤ n.val)
    (hq_lo : 1 ≤ Q.val.length) (hq_hi : Q.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      Q.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < Q.val.length →
      QueryAt Q.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val) :
    ∀ r1 r2, are_connected n t1 Q = ok r1 → are_connected n t2 Q = ok r2 →
      ∀ (i : ℕ) (x y : Std.I64), i < Q.val.length → QueryAt Q.val i x y →
        AnsTrue r2 i → AnsTrue r1 i := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n t1 t2 : Std.I64) (Q : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (ht1_lo : 0 ≤ t1.val) (ht12 : t1.val ≤ t2.val) (ht2_hi : t2.val ≤ n.val)
    (hq_lo : 1 ≤ Q.val.length) (hq_hi : Q.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      Q.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < Q.val.length →
      QueryAt Q.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val), ∀ r1 r2, are_connected n t1 Q = ok r1 → are_connected n t2 Q = ok r2 →
      ∀ (i : ℕ) (x y : Std.I64), i < Q.val.length → QueryAt Q.val i x y →
        AnsTrue r2 i → AnsTrue r1 i) := by
  sorry

/-- If both calls return results r1 and r2, then for every i with 0 <= i < len(Q), if r1[i] = true then r2[i] = true.
  Preconditions: For all integers n1, n2, t, and all query lists Q such that 2 <= n1 <= n2 <= 10^4, 0 <= t <= n1, 1 <= len(Q) <= 10^5, and for every i with 0 <= i < len(Q), len(Q[i]) = 2, 1 <= Q[i][0] <= n1, 1 <= Q[i][1] <= n1, and Q[i][0] != Q[i][1]. Let r1 be the result of are_connected(n1,t,Q) and r2 be the result of are_connected(n2,t,Q). -/
theorem spec_13 (n1 n2 t : Std.I64) (Q : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n1.val) (hn12 : n1.val ≤ n2.val) (hn_hi : n2.val ≤ 10000)
    (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ n1.val)
    (hq_lo : 1 ≤ Q.val.length) (hq_hi : Q.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      Q.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < Q.val.length →
      QueryAt Q.val i x y →
        1 ≤ x.val ∧ x.val ≤ n1.val ∧ 1 ≤ y.val ∧ y.val ≤ n1.val ∧ x.val ≠ y.val) :
    ∀ r1 r2, are_connected n1 t Q = ok r1 → are_connected n2 t Q = ok r2 →
      ∀ (i : ℕ) (x y : Std.I64), i < Q.val.length → QueryAt Q.val i x y →
        AnsTrue r1 i → AnsTrue r2 i := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n1 n2 t : Std.I64) (Q : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n1.val) (hn12 : n1.val ≤ n2.val) (hn_hi : n2.val ≤ 10000)
    (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ n1.val)
    (hq_lo : 1 ≤ Q.val.length) (hq_hi : Q.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      Q.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < Q.val.length →
      QueryAt Q.val i x y →
        1 ≤ x.val ∧ x.val ≤ n1.val ∧ 1 ≤ y.val ∧ y.val ≤ n1.val ∧ x.val ≠ y.val), ∀ r1 r2, are_connected n1 t Q = ok r1 → are_connected n2 t Q = ok r2 →
      ∀ (i : ℕ) (x y : Std.I64), i < Q.val.length → QueryAt Q.val i x y →
        AnsTrue r1 i → AnsTrue r2 i) := by
  sorry

/-- If both calls return results r and r', then for every i,j with 0 <= i < len(Q) and 0 <= j < len(Q'), if Q[i][0] = Q'[j][0] and Q[i][1] = Q'[j][1], then r[i] = r'[j].
  Preconditions: For all integers n, t, and all query lists Q and Q' such that 2 <= n <= 10^4, 0 <= t <= n, both Q and Q' satisfy 1 <= len <= 10^5, every inner vector has length 2, all coordinates are in 1..n, and every pair has distinct endpoints. Let r be the result of are_connected(n,t,Q) and r' be the result of are_connected(n,t,Q'). -/
theorem spec_14 (n t : Std.I64) (Q Q' : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ n.val)
    (hq_lo : 1 ≤ Q.val.length) (hq_hi : Q.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      Q.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < Q.val.length →
      QueryAt Q.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val)
    (hq'_lo : 1 ≤ Q'.val.length) (hq'_hi : Q'.val.length ≤ 100000)
    (hq'_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      Q'.val[i]? = some q → q.val.length = 2)
    (hq'_ok : ∀ (i : ℕ) (x y : Std.I64), i < Q'.val.length →
      QueryAt Q'.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val) :
    ∀ r r', are_connected n t Q = ok r → are_connected n t Q' = ok r' →
      ∀ (i j : ℕ) (x y : Std.I64), i < Q.val.length → j < Q'.val.length →
        QueryAt Q.val i x y → QueryAt Q'.val j x y → r.val[i]? = r'.val[j]? := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n t : Std.I64) (Q Q' : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (ht_lo : 0 ≤ t.val) (ht_hi : t.val ≤ n.val)
    (hq_lo : 1 ≤ Q.val.length) (hq_hi : Q.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      Q.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < Q.val.length →
      QueryAt Q.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val)
    (hq'_lo : 1 ≤ Q'.val.length) (hq'_hi : Q'.val.length ≤ 100000)
    (hq'_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      Q'.val[i]? = some q → q.val.length = 2)
    (hq'_ok : ∀ (i : ℕ) (x y : Std.I64), i < Q'.val.length →
      QueryAt Q'.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val), ∀ r r', are_connected n t Q = ok r → are_connected n t Q' = ok r' →
      ∀ (i j : ℕ) (x y : Std.I64), i < Q.val.length → j < Q'.val.length →
        QueryAt Q.val i x y → QueryAt Q'.val j x y → r.val[i]? = r'.val[j]?) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), if r[i] = true, then there exists an integer k >= 1 and a sequence c_0,...,c_k of integers such that 1 <= c_j <= n for every 0 <= j <= k, c_0 = queries[i][0], c_k = queries[i][1], the cities c_0,...,c_k are pairwise distinct, and for every 0 <= j < k there exists an integer z > threshold dividing both c_j and c_{j+1}.
  Preconditions: n, threshold, and queries satisfy: 2 <= n <= 10^4; 0 <= threshold <= n; 1 <= len(queries) <= 10^5; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= n, 1 <= queries[i][1] <= n, and queries[i][0] != queries[i][1]. -/
theorem spec_15 (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val) :
    ∀ r, are_connected n threshold queries = ok r →
      ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length → QueryAt queries.val i x y →
        AnsTrue r i → IsSimplePath threshold.val n.val x.val y.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_hi : threshold.val ≤ n.val)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val), ∀ r, are_connected n threshold queries = ok r →
      ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length → QueryAt queries.val i x y →
        AnsTrue r i → IsSimplePath threshold.val n.val x.val y.val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), if (queries[i][0] = threshold+1 and queries[i][1] = 2*(threshold+1)) or (queries[i][0] = 2*(threshold+1) and queries[i][1] = threshold+1), then r[i] = true.
  Preconditions: n, threshold, and queries satisfy: 2 <= n <= 10^4; 0 <= threshold < floor(n/2); 1 <= len(queries) <= 10^5; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= n, 1 <= queries[i][1] <= n, and queries[i][0] != queries[i][1]. -/
theorem spec_16 (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_lt_half : threshold.val < n.val / 2)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val) :
    ∀ r, are_connected n threshold queries = ok r →
      ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length → QueryAt queries.val i x y →
        ((x.val = threshold.val + 1 ∧ y.val = 2 * (threshold.val + 1)) ∨
          (x.val = 2 * (threshold.val + 1) ∧ y.val = threshold.val + 1)) → AnsTrue r i := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (n threshold : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hthr_lo : 0 ≤ threshold.val) (hthr_lt_half : threshold.val < n.val / 2)
    (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
    (hq_len : ∀ (i : ℕ) (q : alloc.vec.Vec Std.I64),
      queries.val[i]? = some q → q.val.length = 2)
    (hq_ok : ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length →
      QueryAt queries.val i x y →
        1 ≤ x.val ∧ x.val ≤ n.val ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧ x.val ≠ y.val), ∀ r, are_connected n threshold queries = ok r →
      ∀ (i : ℕ) (x y : Std.I64), i < queries.val.length → QueryAt queries.val i x y →
        ((x.val = threshold.val + 1 ∧ y.val = 2 * (threshold.val + 1)) ∨
          (x.val = 2 * (threshold.val + 1) ∧ y.val = threshold.val + 1)) → AnsTrue r i) := by
  sorry

end AegisSpec.AreConnected
