import Aegis.ResultsArray.Code.Funs

/-!
# Specifications of `Aegis.ResultsArray.results_array`

LeetCode problem `k-th-nearest-obstacle-queries`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ResultsArray

def absInt (a : Int) : Int := if 0 ≤ a then a else -a

def distList : List Std.I64 → Int
  | x :: y :: _ => absInt x.val + absInt y.val
  | [x] => absInt x.val
  | [] => 0

def dist (q : alloc.vec.Vec Std.I64) : Int := distList q.val

def coord (queries : Slice (alloc.vec.Vec Std.I64)) (j c : ℕ) : Int :=
  ((queries.val[j]!).val[c]!).val

def distAt (queries : Slice (alloc.vec.Vec Std.I64)) (j : ℕ) : Int :=
  absInt (coord queries j 0) + absInt (coord queries j 1)

def distsUpTo (queries : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : List Int :=
  (List.range (i + 1)).map (distAt queries)

def countLtUpTo (queries : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) (d : Int) : ℕ :=
  (distsUpTo queries i).countP (fun x => decide (x < d))

def countLeUpTo (queries : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) (d : Int) : ℕ :=
  (distsUpTo queries i).countP (fun x => decide (x ≤ d))

def minUpTo (queries : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : Int :=
  ((distsUpTo queries i).min?).getD 0

def maxUpTo (queries : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : Int :=
  ((distsUpTo queries i).max?).getD 0

def kthSmallest (l : List Int) (k : ℕ) : Option Int := (l.mergeSort (· ≤ ·))[k - 1]?

def resAt (r : alloc.vec.Vec Std.I64) (i : ℕ) : Int := (r.val[i]!).val

/-- The function returns a result r (it does not fail), and len(r) = len(queries). For every i with 0 <= i < len(queries), if i+1 < k then r[i] = -1; if i+1 >= k then r[i] is the k-th smallest element of the multiset {dist(queries[j]) | 0 <= j <= i}, counting equal distances with multiplicity. Equivalently, if the distances of queries[0], ..., queries[i] sorted nondecreasing are d_0 <= ... <= d_i with 0-based indexing, then r[i] = d_{k-1}.
  Preconditions: len(queries) >= 1 and len(queries) <= 200000; every queries[j] is a vector of length exactly 2; for every j and c in {0,1}, -1000000000 <= queries[j][c] <= 1000000000; all coordinate pairs (queries[j][0], queries[j][1]) for 0 <= j < len(queries) are distinct; 1 <= k <= 100000. For a two-element query q, write dist(q) = |q[0]| + |q[1]|, where |a| = a if a >= 0 and |a| = -a if a < 0. -/
theorem spec_1
    (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000) :
    ∃ r, Aegis.ResultsArray.results_array queries k = ok r ∧
      r.length = queries.length ∧
      (∀ i, i < queries.length → i + 1 < k.val.toNat → resAt r i = -1) ∧
      (∀ i, i < queries.length → k.val.toNat ≤ i + 1 →
        kthSmallest (distsUpTo queries i) k.val.toNat = some (resAt r i)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000), ∃ r, Aegis.ResultsArray.results_array queries k = ok r ∧
      r.length = queries.length ∧
      (∀ i, i < queries.length → i + 1 < k.val.toNat → resAt r i = -1) ∧
      (∀ i, i < queries.length → k.val.toNat ≤ i + 1 →
        kthSmallest (distsUpTo queries i) k.val.toNat = some (resAt r i))) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(queries). Thus for every i with 0 <= i < len(queries) there is exactly one result r[i] corresponding to queries[i], and there are no extra entries.
  Preconditions: len(queries) >= 1 and len(queries) <= 200000; every queries[j] is a vector of length exactly 2; for every j and c in {0,1}, -1000000000 <= queries[j][c] <= 1000000000; all coordinate pairs (queries[j][0], queries[j][1]) for 0 <= j < len(queries) are distinct; 1 <= k <= 100000. -/
theorem spec_2
    (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000) :
    ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      r.length = queries.length ∧ (∀ i, i < queries.length → ∃ v, r.val[i]? = some v) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000), ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      r.length = queries.length ∧ (∀ i, i < queries.length → ∃ v, r.val[i]? = some v)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not panic, fail an out-of-bounds check, or overflow a 64-bit integer.
  Preconditions: len(queries) >= 1 and len(queries) <= 200000; every queries[j] is a vector of length exactly 2; for every j and c in {0,1}, -1000000000 <= queries[j][c] <= 1000000000; all coordinate pairs (queries[j][0], queries[j][1]) for 0 <= j < len(queries) are distinct; 1 <= k <= 100000. -/
theorem spec_3
    (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000) :
    ∃ r, Aegis.ResultsArray.results_array queries k = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000), ∃ r, Aegis.ResultsArray.results_array queries k = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries) and i+1 >= k, setting d = r[i], we have d != -1, the number of indices j with 0 <= j <= i and dist(queries[j]) < d is at most k-1, and the number of indices j with 0 <= j <= i and dist(queries[j]) <= d is at least k.
  Preconditions: len(queries) >= 1 and len(queries) <= 200000; every queries[j] is a vector of length exactly 2; for every j and c in {0,1}, -1000000000 <= queries[j][c] <= 1000000000; all coordinate pairs (queries[j][0], queries[j][1]) for 0 <= j < len(queries) are distinct; 1 <= k <= 100000. For a two-element query q, write dist(q) = |q[0]| + |q[1]|, where |a| = a if a >= 0 and |a| = -a if a < 0. -/
theorem spec_4
    (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000) :
    ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      ∀ i, i < queries.length → k.val.toNat ≤ i + 1 →
        resAt r i ≠ -1 ∧
        countLtUpTo queries i (resAt r i) ≤ k.val.toNat - 1 ∧
        k.val.toNat ≤ countLeUpTo queries i (resAt r i) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000), ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      ∀ i, i < queries.length → k.val.toNat ≤ i + 1 →
        resAt r i ≠ -1 ∧
        countLtUpTo queries i (resAt r i) ≤ k.val.toNat - 1 ∧
        k.val.toNat ≤ countLeUpTo queries i (resAt r i)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries) and i+1 >= k, r[i] is the least integer d such that at least k of the distances dist(queries[j]) for 0 <= j <= i satisfy dist(queries[j]) <= d.
  Preconditions: len(queries) >= 1 and len(queries) <= 200000; every queries[j] is a vector of length exactly 2; for every j and c in {0,1}, -1000000000 <= queries[j][c] <= 1000000000; all coordinate pairs (queries[j][0], queries[j][1]) for 0 <= j < len(queries) are distinct; 1 <= k <= 100000. For a two-element query q, write dist(q) = |q[0]| + |q[1]|, where |a| = a if a >= 0 and |a| = -a if a < 0. -/
theorem spec_5
    (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000) :
    ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      ∀ i, i < queries.length → k.val.toNat ≤ i + 1 →
        k.val.toNat ≤ countLeUpTo queries i (resAt r i) ∧
        (∀ d, d < resAt r i → countLeUpTo queries i d < k.val.toNat) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000), ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      ∀ i, i < queries.length → k.val.toNat ≤ i + 1 →
        k.val.toNat ≤ countLeUpTo queries i (resAt r i) ∧
        (∀ d, d < resAt r i → countLeUpTo queries i d < k.val.toNat)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), r[i] = -1 if and only if i+1 < k.
  Preconditions: len(queries) >= 1 and len(queries) <= 200000; every queries[j] is a vector of length exactly 2; for every j and c in {0,1}, -1000000000 <= queries[j][c] <= 1000000000; all coordinate pairs (queries[j][0], queries[j][1]) for 0 <= j < len(queries) are distinct; 1 <= k <= 100000. -/
theorem spec_6
    (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000) :
    ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      ∀ i, i < queries.length → (resAt r i = -1 ↔ i + 1 < k.val.toNat) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000), ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      ∀ i, i < queries.length → (resAt r i = -1 ↔ i + 1 < k.val.toNat)) := by
  sorry

/-- Whenever the function returns a result r, if k <= len(queries), then r[k-1] = max({dist(queries[j]) | 0 <= j < k}).
  Preconditions: len(queries) >= 1 and len(queries) <= 200000; every queries[j] is a vector of length exactly 2; for every j and c in {0,1}, -1000000000 <= queries[j][c] <= 1000000000; all coordinate pairs (queries[j][0], queries[j][1]) for 0 <= j < len(queries) are distinct; 1 <= k <= 100000. For a two-element query q, write dist(q) = |q[0]| + |q[1]|, where |a| = a if a >= 0 and |a| = -a if a < 0. -/
theorem spec_7
    (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000) :
    ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      k.val ≤ (queries.length : ℤ) →
        resAt r (k.val.toNat - 1) = maxUpTo queries (k.val.toNat - 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000), ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      k.val ≤ (queries.length : ℤ) →
        resAt r (k.val.toNat - 1) = maxUpTo queries (k.val.toNat - 1)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries) and i+1 >= k, there exists an index j with 0 <= j <= i such that r[i] = dist(queries[j]).
  Preconditions: len(queries) >= 1 and len(queries) <= 200000; every queries[j] is a vector of length exactly 2; for every j and c in {0,1}, -1000000000 <= queries[j][c] <= 1000000000; all coordinate pairs (queries[j][0], queries[j][1]) for 0 <= j < len(queries) are distinct; 1 <= k <= 100000. For a two-element query q, write dist(q) = |q[0]| + |q[1]|, where |a| = a if a >= 0 and |a| = -a if a < 0. -/
theorem spec_8
    (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000) :
    ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      ∀ i, i < queries.length → k.val.toNat ≤ i + 1 →
        ∃ j, j ≤ i ∧ j < queries.length ∧ resAt r i = distAt queries j := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000), ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      ∀ i, i < queries.length → k.val.toNat ≤ i + 1 →
        ∃ j, j ≤ i ∧ j < queries.length ∧ resAt r i = distAt queries j) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), if r[i] != -1 then 0 <= r[i] <= 2000000000.
  Preconditions: len(queries) >= 1 and len(queries) <= 200000; every queries[j] is a vector of length exactly 2; for every j and c in {0,1}, -1000000000 <= queries[j][c] <= 1000000000; all coordinate pairs (queries[j][0], queries[j][1]) for 0 <= j < len(queries) are distinct; 1 <= k <= 100000. -/
theorem spec_9
    (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000) :
    ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      ∀ i, i < queries.length → resAt r i ≠ -1 →
        0 ≤ resAt r i ∧ resAt r i ≤ 2000000000 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000), ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      ∀ i, i < queries.length → resAt r i ≠ -1 →
        0 ≤ resAt r i ∧ resAt r i ≤ 2000000000) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries) and i+1 >= k, min({dist(queries[j]) | 0 <= j <= i}) <= r[i] <= max({dist(queries[j]) | 0 <= j <= i}).
  Preconditions: len(queries) >= 1 and len(queries) <= 200000; every queries[j] is a vector of length exactly 2; for every j and c in {0,1}, -1000000000 <= queries[j][c] <= 1000000000; all coordinate pairs (queries[j][0], queries[j][1]) for 0 <= j < len(queries) are distinct; 1 <= k <= 100000. For a two-element query q, write dist(q) = |q[0]| + |q[1]|, where |a| = a if a >= 0 and |a| = -a if a < 0. -/
theorem spec_10
    (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000) :
    ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      ∀ i, i < queries.length → k.val.toNat ≤ i + 1 →
        minUpTo queries i ≤ resAt r i ∧ resAt r i ≤ maxUpTo queries i := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000), ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      ∀ i, i < queries.length → k.val.toNat ≤ i + 1 →
        minUpTo queries i ≤ resAt r i ∧ resAt r i ≤ maxUpTo queries i) := by
  sorry

/-- Whenever the function returns a result r, for all i and j with 0 <= i < j < len(queries) and i+1 >= k, we have r[j] <= r[i].
  Preconditions: len(queries) >= 1 and len(queries) <= 200000; every queries[j] is a vector of length exactly 2; for every j and c in {0,1}, -1000000000 <= queries[j][c] <= 1000000000; all coordinate pairs (queries[j][0], queries[j][1]) for 0 <= j < len(queries) are distinct; 1 <= k <= 100000. -/
theorem spec_11
    (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000) :
    ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      ∀ i j, i < j → j < queries.length → k.val.toNat ≤ i + 1 → resAt r j ≤ resAt r i := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000), ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      ∀ i j, i < j → j < queries.length → k.val.toNat ≤ i + 1 → resAt r j ≤ resAt r i) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries)-1 and i+1 >= k, if dist(queries[i+1]) >= r[i], then r[i+1] = r[i].
  Preconditions: len(queries) >= 1 and len(queries) <= 200000; every queries[j] is a vector of length exactly 2; for every j and c in {0,1}, -1000000000 <= queries[j][c] <= 1000000000; all coordinate pairs (queries[j][0], queries[j][1]) for 0 <= j < len(queries) are distinct; 1 <= k <= 100000. For a two-element query q, write dist(q) = |q[0]| + |q[1]|, where |a| = a if a >= 0 and |a| = -a if a < 0. -/
theorem spec_12
    (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000) :
    ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      ∀ i, i + 1 < queries.length → k.val.toNat ≤ i + 1 →
        distAt queries (i + 1) ≥ resAt r i → resAt r (i + 1) = resAt r i := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000), ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      ∀ i, i + 1 < queries.length → k.val.toNat ≤ i + 1 →
        distAt queries (i + 1) ≥ resAt r i → resAt r (i + 1) = resAt r i) := by
  sorry

/-- Whenever the function returns a result r, if k = 1, then for every i with 0 <= i < len(queries), r[i] = min({dist(queries[j]) | 0 <= j <= i}).
  Preconditions: len(queries) >= 1 and len(queries) <= 200000; every queries[j] is a vector of length exactly 2; for every j and c in {0,1}, -1000000000 <= queries[j][c] <= 1000000000; all coordinate pairs (queries[j][0], queries[j][1]) for 0 <= j < len(queries) are distinct; 1 <= k <= 100000. For a two-element query q, write dist(q) = |q[0]| + |q[1]|, where |a| = a if a >= 0 and |a| = -a if a < 0. -/
theorem spec_13
    (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000) :
    ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      k.val = 1 → ∀ i, i < queries.length → resAt r i = minUpTo queries i := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlen_pos : 1 ≤ queries.length)
    (hlen_le : queries.length ≤ 200000)
    (hq_len : ∀ j, j < queries.length → (queries.val[j]!).val.length = 2)
    (hq_bounds : ∀ j c, j < queries.length → c < 2 →
      -1000000000 ≤ coord queries j c ∧ coord queries j c ≤ 1000000000)
    (hq_distinct : ∀ j₁ j₂, j₁ < queries.length → j₂ < queries.length → j₁ ≠ j₂ →
      (coord queries j₁ 0, coord queries j₁ 1) ≠ (coord queries j₂ 0, coord queries j₂ 1))
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ 100000), ∀ r, Aegis.ResultsArray.results_array queries k = ok r →
      k.val = 1 → ∀ i, i < queries.length → resAt r i = minUpTo queries i) := by
  sorry

end AegisSpec.ResultsArray
