import Aegis.MatrixSumQueries.Code.Funs

/-!
# Specifications of `Aegis.MatrixSumQueries.matrix_sum_queries`

LeetCode problem `sum-of-matrix-after-queries`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MatrixSumQueries

def queryField (Q : List (alloc.vec.Vec Std.I64)) (i k : ℕ) : Option ℤ :=
  match Q[i]? with
  | none => none
  | some q => (q[k]?).map fun x => x.val

def queryFieldVal (Q : List (alloc.vec.Vec Std.I64)) (i k : ℕ) : ℤ :=
  (queryField Q i k).getD 0

def queryVal (Q : List (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
  queryFieldVal Q i 2

def queryValInt (Q : List (alloc.vec.Vec Std.I64)) (i : ℤ) : ℤ :=
  if 0 ≤ i then queryVal Q i.toNat else 0

def lastIndex (Q : List (alloc.vec.Vec Std.I64)) (typ idx : ℤ) : ℤ :=
  List.foldr max (-1)
    ((List.range Q.length).filterMap fun i =>
      if queryField Q i 0 = some typ ∧ queryField Q i 1 = some idx then some (i : ℤ) else none)

def lastRowValue (Q : List (alloc.vec.Vec Std.I64)) (r : ℕ) : ℤ :=
  queryValInt Q (lastIndex Q 0 (r : ℤ))

def finalCell (Q : List (alloc.vec.Vec Std.I64)) (r c : ℕ) : ℤ :=
  let a := lastIndex Q 0 (r : ℤ)
  let b := lastIndex Q 1 (c : ℤ)
  if a = -1 ∧ b = -1 then 0 else queryValInt Q (max a b)

def totalSum (Q : List (alloc.vec.Vec Std.I64)) (n : ℕ) : ℤ :=
  ((List.range n).map fun r => ((List.range n).map fun c => finalCell Q r c).sum).sum

def maxValue (Q : List (alloc.vec.Vec Std.I64)) : ℤ :=
  List.foldr max 0 ((List.range Q.length).map fun i => queryVal Q i)

def lastQueryVal (Q : List (alloc.vec.Vec Std.I64)) : ℤ :=
  queryVal Q (Q.length - 1)

def i64Of (x : ℤ) : Std.I64 := ⟨BitVec.ofInt 64 x⟩

def withValue (q : alloc.vec.Vec Std.I64) (v : Std.I64) : alloc.vec.Vec Std.I64 :=
  q.set 2#usize v

def setQueryValue (queries : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) (v : Std.I64) :
    Slice (alloc.vec.Vec Std.I64) :=
  queries.setAtNat i (withValue (queries.val.getD i default) v)

def isLastOfPair (Q : List (alloc.vec.Vec Std.I64)) (i : ℕ) : Bool :=
  (List.range Q.length).all fun j =>
    decide (i < j → ¬(queryField Q j 0 = queryField Q i 0 ∧ queryField Q j 1 = queryField Q i 1))

def keepLastOfPair (Q : List (alloc.vec.Vec Std.I64)) : List (alloc.vec.Vec Std.I64) :=
  (List.range Q.length).filterMap fun i => if isLastOfPair Q i then Q[i]? else none

def keepLastOfPairSlice (queries : Slice (alloc.vec.Vec Std.I64)) :
    Slice (alloc.vec.Vec Std.I64) :=
  Slice.from (keepLastOfPair queries.val) (by
    have h := Aeneas.Std.Slice.length_ineq queries
    have h2 : (keepLastOfPair queries.val).length ≤ queries.val.length := by
      have := List.length_filterMap_le
        (fun i => if isLastOfPair queries.val i then queries.val[i]? else none)
        (List.range queries.val.length)
      simpa [keepLastOfPair, List.length_range] using this
    exact le_trans h2 h)

def flipQuery (q : alloc.vec.Vec Std.I64) : alloc.vec.Vec Std.I64 :=
  q.set 0#usize (i64Of (1 - queryFieldVal [q] 0 0))

def flipQueries (queries : Slice (alloc.vec.Vec Std.I64)) : Slice (alloc.vec.Vec Std.I64) :=
  Slice.from (queries.val.map flipQuery) (by
    rw [List.length_map]
    exact Aeneas.Std.Slice.length_ineq queries)

def scaleQuery (k : ℤ) (q : alloc.vec.Vec Std.I64) : alloc.vec.Vec Std.I64 :=
  q.set 2#usize (i64Of (k * queryFieldVal [q] 0 2))

def scaleQueries (k : ℤ) (queries : Slice (alloc.vec.Vec Std.I64)) :
    Slice (alloc.vec.Vec Std.I64) :=
  Slice.from (queries.val.map (scaleQuery k)) (by
    rw [List.length_map]
    exact Aeneas.Std.Slice.length_ineq queries)

/-- The function returns a result res and res = sum_{r=0}^{n-1} sum_{c=0}^{n-1} final(r,c), where for each cell (r,c), final(r,c) is defined as follows. Let a_r be the largest index i with 0 <= i < len(queries) such that t_i = 0 and idx_i = r, or -1 if no such i exists. Let b_c be the largest index i with 0 <= i < len(queries) such that t_i = 1 and idx_i = c, or -1 if no such i exists. If a_r = -1 and b_c = -1, then final(r,c) = 0. Otherwise final(r,c) = v_{max(a_r, b_c)}.
  Preconditions: n is an integer with 1 <= n <= 10^4. queries is a slice of vectors, each of length 3, with len(queries) between 1 and 5*10^4. For every i with 0 <= i < len(queries), writing queries[i] = [t_i, idx_i, v_i], we have t_i ∈ {0,1}, 0 <= idx_i < n, and 0 <= v_i <= 10^5. All values are i64. -/
theorem spec_1 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000) :
    ∃ res : Std.I64, Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok res ∧
      res.val = totalSum queries.val n.val.toNat := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000), ∃ res : Std.I64, Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok res ∧
      res.val = totalSum queries.val n.val.toNat) := by
  sorry

/-- The function returns a result res (it does not fail, overflow, or panic).
  Preconditions: n is an integer with 1 <= n <= 10^4. queries is a slice of vectors, each of length 3, with len(queries) between 1 and 5*10^4. For every i with 0 <= i < len(queries), writing queries[i] = [t_i, idx_i, v_i], we have t_i ∈ {0,1}, 0 <= idx_i < n, and 0 <= v_i <= 10^5. All values are i64. -/
theorem spec_2 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000) :
    ∃ res : Std.I64, Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok res := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000), ∃ res : Std.I64, Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok res) := by
  sorry

/-- The function returns a result res and res >= 0.
  Preconditions: n is an integer with 1 <= n <= 10^4. queries is a slice of vectors, each of length 3, with len(queries) between 1 and 5*10^4. For every i with 0 <= i < len(queries), writing queries[i] = [t_i, idx_i, v_i], we have t_i ∈ {0,1}, 0 <= idx_i < n, and 0 <= v_i <= 10^5. All values are i64. -/
theorem spec_3 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000) :
    ∃ res : Std.I64, Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok res ∧
      0 ≤ res.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000), ∃ res : Std.I64, Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok res ∧
      0 ≤ res.val) := by
  sorry

/-- The function returns a result res and res <= n * n * M, where M = max_{0 <= i < len(queries)} v_i (the maximum value appearing in any query).
  Preconditions: n is an integer with 1 <= n <= 10^4. queries is a slice of vectors, each of length 3, with len(queries) between 1 and 5*10^4. For every i with 0 <= i < len(queries), writing queries[i] = [t_i, idx_i, v_i], we have t_i ∈ {0,1}, 0 <= idx_i < n, and 0 <= v_i <= 10^5. All values are i64. -/
theorem spec_4 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000) :
    ∃ res : Std.I64, Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok res ∧
      res.val ≤ n.val * n.val * maxValue queries.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000), ∃ res : Std.I64, Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok res ∧
      res.val ≤ n.val * n.val * maxValue queries.val) := by
  sorry

/-- The function returns a result res and res = v_{len(queries)-1} (the val of the last query).
  Preconditions: n is an integer with 1 <= n <= 10^4 and n = 1. queries is a slice of vectors, each of length 3, with len(queries) between 1 and 5*10^4. For every i with 0 <= i < len(queries), writing queries[i] = [t_i, idx_i, v_i], we have t_i ∈ {0,1}, 0 <= idx_i < n, and 0 <= v_i <= 10^5. All values are i64. -/
theorem spec_5 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (hn1 : n.val = 1)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000) :
    ∃ res : Std.I64, Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok res ∧
      res.val = lastQueryVal queries.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (hn1 : n.val = 1)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000), ∃ res : Std.I64, Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok res ∧
      res.val = lastQueryVal queries.val) := by
  sorry

/-- The function returns a result res and res = n * v_0.
  Preconditions: n is an integer with 1 <= n <= 10^4. queries is a slice of vectors, each of length 3, with len(queries) = 1. For i=0, writing queries[0] = [t_0, idx_0, v_0], we have t_0 ∈ {0,1}, 0 <= idx_0 < n, and 0 <= v_0 <= 10^5. All values are i64. -/
theorem spec_6 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (hlen1 : queries.val.length = 1)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000) :
    ∃ res : Std.I64, Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok res ∧
      res.val = n.val * queryVal queries.val 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000) (hlen1 : queries.val.length = 1)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000), ∃ res : Std.I64, Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok res ∧
      res.val = n.val * queryVal queries.val 0) := by
  sorry

/-- The function returns a result res and res >= n * v_{len(queries)-1}.
  Preconditions: n is an integer with 1 <= n <= 10^4. queries is a slice of vectors, each of length 3, with len(queries) between 1 and 5*10^4. For every i with 0 <= i < len(queries), writing queries[i] = [t_i, idx_i, v_i], we have t_i ∈ {0,1}, 0 <= idx_i < n, and 0 <= v_i <= 10^5. All values are i64. -/
theorem spec_7 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000) :
    ∃ res : Std.I64, Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok res ∧
      n.val * lastQueryVal queries.val ≤ res.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000), ∃ res : Std.I64, Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok res ∧
      n.val * lastQueryVal queries.val ≤ res.val) := by
  sorry

/-- Let S = { i | 0 <= i < len(queries) and for all j with i < j < len(queries), it is not the case that (t_j = t_i and idx_j = idx_i) }. Let Q' be the subsequence of queries consisting of queries[i] for i in S, in increasing order of i. Then matrix_sum_queries(n, queries) = matrix_sum_queries(n, Q').
  Preconditions: n is an integer with 1 <= n <= 10^4. queries is a slice of vectors, each of length 3, with len(queries) between 1 and 5*10^4. For every i with 0 <= i < len(queries), writing queries[i] = [t_i, idx_i, v_i], we have t_i ∈ {0,1}, 0 <= idx_i < n, and 0 <= v_i <= 10^5. All values are i64. -/
theorem spec_8 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000) :
    Aegis.MatrixSumQueries.matrix_sum_queries n (keepLastOfPairSlice queries) =
      Aegis.MatrixSumQueries.matrix_sum_queries n queries := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000), Aegis.MatrixSumQueries.matrix_sum_queries n (keepLastOfPairSlice queries) =
      Aegis.MatrixSumQueries.matrix_sum_queries n queries) := by
  sorry

/-- For any index i with 0 <= i < len(queries), if there exists j with i < j < len(queries) such that t_j = t_i and idx_j = idx_i, then for any integer v' with 0 <= v' <= 10^5, let Q' be the sequence obtained from queries by replacing v_i with v'. Then matrix_sum_queries(n, Q') = matrix_sum_queries(n, queries).
  Preconditions: n is an integer with 1 <= n <= 10^4. queries is a slice of vectors, each of length 3, with len(queries) between 1 and 5*10^4. For every i with 0 <= i < len(queries), writing queries[i] = [t_i, idx_i, v_i], we have t_i ∈ {0,1}, 0 <= idx_i < n, and 0 <= v_i <= 10^5. All values are i64. -/
theorem spec_9 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000)
    (i : ℕ) (hi : i < queries.val.length)
    (hdup : ∃ j : ℕ, i < j ∧ j < queries.val.length ∧
      queryField queries.val j 0 = queryField queries.val i 0 ∧
      queryField queries.val j 1 = queryField queries.val i 1)
    (v' : Std.I64) (hv' : 0 ≤ v'.val ∧ v'.val ≤ 100000) :
    Aegis.MatrixSumQueries.matrix_sum_queries n (setQueryValue queries i v') =
      Aegis.MatrixSumQueries.matrix_sum_queries n queries := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000)
    (i : ℕ) (hi : i < queries.val.length)
    (hdup : ∃ j : ℕ, i < j ∧ j < queries.val.length ∧
      queryField queries.val j 0 = queryField queries.val i 0 ∧
      queryField queries.val j 1 = queryField queries.val i 1)
    (v' : Std.I64) (hv' : 0 ≤ v'.val ∧ v'.val ≤ 100000), Aegis.MatrixSumQueries.matrix_sum_queries n (setQueryValue queries i v') =
      Aegis.MatrixSumQueries.matrix_sum_queries n queries) := by
  sorry

/-- Let Q' be the sequence defined by Q'[i] = [1 - t_i, idx_i, v_i] for all i. Then matrix_sum_queries(n, Q') = matrix_sum_queries(n, queries).
  Preconditions: n is an integer with 1 <= n <= 10^4. queries is a slice of vectors, each of length 3, with len(queries) between 1 and 5*10^4. For every i with 0 <= i < len(queries), writing queries[i] = [t_i, idx_i, v_i], we have t_i ∈ {0,1}, 0 <= idx_i < n, and 0 <= v_i <= 10^5. All values are i64. -/
theorem spec_10 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000) :
    Aegis.MatrixSumQueries.matrix_sum_queries n (flipQueries queries) =
      Aegis.MatrixSumQueries.matrix_sum_queries n queries := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000), Aegis.MatrixSumQueries.matrix_sum_queries n (flipQueries queries) =
      Aegis.MatrixSumQueries.matrix_sum_queries n queries) := by
  sorry

/-- Let res = matrix_sum_queries(n, queries). For any integer k >= 0 such that k * v_i <= 10^5 for all i and k * res <= 2^63 - 1, let Q' be the sequence obtained by replacing every v_i with k * v_i. Then matrix_sum_queries(n, Q') = k * res.
  Preconditions: n is an integer with 1 <= n <= 10^4. queries is a slice of vectors, each of length 3, with len(queries) between 1 and 5*10^4. For every i with 0 <= i < len(queries), writing queries[i] = [t_i, idx_i, v_i], we have t_i ∈ {0,1}, 0 <= idx_i < n, and 0 <= v_i <= 10^5. All values are i64. -/
theorem spec_11 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000)
    (res : Std.I64) (hres : Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok res)
    (k : ℤ) (hk : 0 ≤ k)
    (hkval : ∀ i : ℕ, i < queries.val.length → k * queryVal queries.val i ≤ 100000)
    (hkres : k * res.val ≤ 9223372036854775807) :
    ∃ res' : Std.I64,
      Aegis.MatrixSumQueries.matrix_sum_queries n (scaleQueries k queries) = ok res' ∧
        res'.val = k * res.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000)
    (res : Std.I64) (hres : Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok res)
    (k : ℤ) (hk : 0 ≤ k)
    (hkval : ∀ i : ℕ, i < queries.val.length → k * queryVal queries.val i ≤ 100000)
    (hkres : k * res.val ≤ 9223372036854775807), ∃ res' : Std.I64,
      Aegis.MatrixSumQueries.matrix_sum_queries n (scaleQueries k queries) = ok res' ∧
        res'.val = k * res.val) := by
  sorry

/-- For any index i with 0 <= i < len(queries) and any integer v' with v_i <= v' <= 10^5, let Q' be the sequence obtained from queries by replacing v_i with v'. Then matrix_sum_queries(n, Q') >= matrix_sum_queries(n, queries).
  Preconditions: n is an integer with 1 <= n <= 10^4. queries is a slice of vectors, each of length 3, with len(queries) between 1 and 5*10^4. For every i with 0 <= i < len(queries), writing queries[i] = [t_i, idx_i, v_i], we have t_i ∈ {0,1}, 0 <= idx_i < n, and 0 <= v_i <= 10^5. All values are i64. -/
theorem spec_12 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000)
    (i : ℕ) (hi : i < queries.val.length)
    (vi : Std.I64) (hvi : queryField queries.val i 2 = some vi.val)
    (v' : Std.I64) (hv' : vi.val ≤ v'.val ∧ v'.val ≤ 100000) :
    ∀ (r r' : Std.I64), Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok r →
      Aegis.MatrixSumQueries.matrix_sum_queries n (setQueryValue queries i v') = ok r' →
        r.val ≤ r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000)
    (i : ℕ) (hi : i < queries.val.length)
    (vi : Std.I64) (hvi : queryField queries.val i 2 = some vi.val)
    (v' : Std.I64) (hv' : vi.val ≤ v'.val ∧ v'.val ≤ 100000), ∀ (r r' : Std.I64), Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok r →
      Aegis.MatrixSumQueries.matrix_sum_queries n (setQueryValue queries i v') = ok r' →
        r.val ≤ r'.val) := by
  sorry

/-- The function returns a result res and res = n * sum_{r=0}^{n-1} L(r), where for each row r, L(r) = v_{i} for the largest index i with idx_i = r (if such i exists), and L(r) = 0 if no query has idx_i = r.
  Preconditions: n is an integer with 1 <= n <= 10^4. queries is a slice of vectors, each of length 3, with len(queries) between 1 and 5*10^4. For every i with 0 <= i < len(queries), writing queries[i] = [t_i, idx_i, v_i], we have t_i ∈ {0,1}, 0 <= idx_i < n, and 0 <= v_i <= 10^5. All values are i64. Additionally, every query has type 0: for all i, t_i = 0. -/
theorem spec_13 (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000)
    (hall : ∀ i : ℕ, i < queries.val.length → queryField queries.val i 0 = some 0) :
    ∃ res : Std.I64, Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok res ∧
      res.val = n.val * ((List.range n.val.toNat).map fun r => lastRowValue queries.val r).sum := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
    (hlen : 1 ≤ queries.val.length ∧ queries.val.length ≤ 50000)
    (hq : ∀ i : ℕ, i < queries.val.length →
      ∃ (q : alloc.vec.Vec Std.I64) (t idx v : Std.I64),
        queries.val[i]? = some q ∧ q.val = [t, idx, v] ∧ (t.val = 0 ∨ t.val = 1) ∧
          0 ≤ idx.val ∧ idx.val < n.val ∧ 0 ≤ v.val ∧ v.val ≤ 100000)
    (hall : ∀ i : ℕ, i < queries.val.length → queryField queries.val i 0 = some 0), ∃ res : Std.I64, Aegis.MatrixSumQueries.matrix_sum_queries n queries = ok res ∧
      res.val = n.val * ((List.range n.val.toNat).map fun r => lastRowValue queries.val r).sum) := by
  sorry

end AegisSpec.MatrixSumQueries
