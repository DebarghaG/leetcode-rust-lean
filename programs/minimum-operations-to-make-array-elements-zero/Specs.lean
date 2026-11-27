import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-operations-to-make-array-elements-zero`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinOperations

namespace AegisSpec.MinOperations

noncomputable def d (x : ℤ) : ℤ := by
  classical
  exact if h : ∃ k : ℕ, 0 < k ∧ x < (4 : ℤ) ^ k then (Nat.find h : ℤ) else 1

def ceilHalf (n : ℤ) : ℤ := (n + 1) / 2

noncomputable def S (l r : ℤ) : ℤ :=
  Finset.sum (Finset.range (Int.toNat (r - l + 1))) (fun i => d (l + (i : ℤ)))

noncomputable def m (l r : ℤ) : ℤ := max (d r) (ceilHalf (S l r))

def queryL (v : alloc.vec.Vec Std.I64) : ℤ := (v.val.map (fun x => x.val)).getD 0 0

def queryR (v : alloc.vec.Vec Std.I64) : ℤ := (v.val.map (fun x => x.val)).getD 1 0

def ValidQuery (v : alloc.vec.Vec Std.I64) : Prop :=
  v.val.length = 2 ∧ 1 ≤ queryL v ∧ queryL v < queryR v ∧ queryR v ≤ 1000000000

def ValidQueries (qs : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  1 ≤ qs.val.length ∧ qs.val.length ≤ 100000 ∧ ∀ v ∈ qs.val, ValidQuery v

noncomputable def totalM (qs : List (alloc.vec.Vec Std.I64)) : ℤ :=
  (qs.map (fun v => m (queryL v) (queryR v))).sum

noncomputable def totalS (qs : List (alloc.vec.Vec Std.I64)) : ℤ :=
  (qs.map (fun v => S (queryL v) (queryR v))).sum

noncomputable def totalCeil (qs : List (alloc.vec.Vec Std.I64)) : ℤ :=
  (qs.map (fun v => ceilHalf (queryR v - queryL v + 1))).sum

noncomputable def totalLen (qs : List (alloc.vec.Vec Std.I64)) : ℤ :=
  (qs.map (fun v => queryR v - queryL v + 1)).sum

def sliceOfList (qs : List (alloc.vec.Vec Std.I64)) (h : qs.length ≤ Usize.max) :
    Slice (alloc.vec.Vec Std.I64) :=
  ⟨qs.length, Aeneas.Data.ListN.ListN.fromList qs, h⟩

def queryVec (l r : Std.I64) : alloc.vec.Vec Std.I64 :=
  ⟨⟨2, Aeneas.Data.ListN.ListN.fromList [l, r],
      le_trans (by norm_num) Aeneas.Std.Usize.cMax_bound_concrete.1⟩⟩

def specQuery : Slice (alloc.vec.Vec Std.I64) :=
  sliceOfList [queryVec (1#i64) (1000000000#i64)]
    (le_trans (by norm_num) Aeneas.Std.Usize.cMax_bound_concrete.1)

def ReplacedR (q q' : List (alloc.vec.Vec Std.I64)) (l r₁ r₂ : ℤ) : Prop :=
  ∃ (pre post : List (alloc.vec.Vec Std.I64)) (v₁ v₂ : alloc.vec.Vec Std.I64),
    q = pre ++ v₁ :: post ∧ q' = pre ++ v₂ :: post ∧
    queryL v₁ = l ∧ queryR v₁ = r₁ ∧ queryL v₂ = l ∧ queryR v₂ = r₂

def ReplacedL (q q' : List (alloc.vec.Vec Std.I64)) (l₁ l₂ r : ℤ) : Prop :=
  ∃ (pre post : List (alloc.vec.Vec Std.I64)) (v₁ v₂ : alloc.vec.Vec Std.I64),
    q = pre ++ v₁ :: post ∧ q' = pre ++ v₂ :: post ∧
    queryL v₁ = l₁ ∧ queryR v₁ = r ∧ queryL v₂ = l₂ ∧ queryR v₂ = r

noncomputable def LegalSeq (l r : ℤ) (k : ℕ) : Prop :=
  ∃ a : Fin k → Fin (Int.toNat (r - l + 1)) → ℕ,
    (∀ t i, a t i ≤ 1) ∧
    (∀ t, Finset.univ.sum (fun i => a t i) ≤ 2) ∧
    (∀ i, Finset.univ.sum (fun t => a t i) = Int.toNat (d (l + (i : ℤ))))

/-- Whenever the function returns a result v, v = sum_{i=0}^{len(queries)-1} m(l_i, r_i), where for x >= 1, d(x) is the least positive integer k such that x < 4^k; S(l,r) = sum_{x=l}^{r} d(x); and m(l,r) = max(d(r), ceil(S(l,r)/2)).
  Preconditions: queries is a slice of vectors of 64-bit integers satisfying the problem constraints: 1 <= len(queries) <= 100000; for every i with 0 <= i < len(queries), len(queries[i]) = 2; writing l_i = queries[i][0] and r_i = queries[i][1], we have 1 <= l_i < r_i <= 1000000000. All I64 entries are interpreted as mathematical integers. -/
theorem spec_1 (queries : Slice (alloc.vec.Vec Std.I64)) (v : Std.I64)
    (hvalid : ValidQueries queries)
    (hres : min_operations queries = ok v) :
    v.val = totalM queries.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (v : Std.I64)
    (hvalid : ValidQueries queries)
    (hres : min_operations queries = ok v), v.val = totalM queries.val) := by
  sorry

/-- For every queries satisfying the preconditions, the function returns Result.ok v for some 64-bit integer v; it does not fail by panic, out-of-bounds access, or arithmetic overflow.
  Preconditions: queries satisfies the problem constraints: 1 <= len(queries) <= 100000; every queries[i] has length 2; writing l_i = queries[i][0], r_i = queries[i][1], we have 1 <= l_i < r_i <= 1000000000. -/
theorem spec_2 (queries : Slice (alloc.vec.Vec Std.I64))
    (hvalid : ValidQueries queries) :
    ∃ v : Std.I64, min_operations queries = ok v := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64))
    (hvalid : ValidQueries queries), ∃ v : Std.I64, min_operations queries = ok v) := by
  sorry

/-- Whenever the function returns v, v >= sum_{i=0}^{len(queries)-1} ceil((r_i - l_i + 1)/2). In particular, v >= len(queries).
  Preconditions: queries satisfies the problem constraints: 1 <= len(queries) <= 100000; every queries[i] has length 2; l_i = queries[i][0], r_i = queries[i][1] with 1 <= l_i < r_i <= 1000000000. -/
theorem spec_3 (queries : Slice (alloc.vec.Vec Std.I64)) (v : Std.I64)
    (hvalid : ValidQueries queries)
    (hres : min_operations queries = ok v) :
    totalCeil queries.val ≤ v.val ∧ (queries.val.length : ℤ) ≤ v.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (v : Std.I64)
    (hvalid : ValidQueries queries)
    (hres : min_operations queries = ok v), totalCeil queries.val ≤ v.val ∧ (queries.val.length : ℤ) ≤ v.val) := by
  sorry

/-- Let d(x) be the least positive k with x < 4^k and S(l,r) = sum_{x=l}^{r} d(x). Whenever the function returns v, v <= sum_{i=0}^{len(queries)-1} S(l_i,r_i), and therefore v <= 15 * sum_{i=0}^{len(queries)-1} (r_i - l_i + 1) <= 1500000000000000.
  Preconditions: queries satisfies the problem constraints: 1 <= len(queries) <= 100000; every queries[i] has length 2; l_i = queries[i][0], r_i = queries[i][1] with 1 <= l_i < r_i <= 1000000000. -/
theorem spec_4 (queries : Slice (alloc.vec.Vec Std.I64)) (v : Std.I64)
    (hvalid : ValidQueries queries)
    (hres : min_operations queries = ok v) :
    v.val ≤ totalS queries.val ∧
      totalS queries.val ≤ 15 * totalLen queries.val ∧
      15 * totalLen queries.val ≤ 1500000000000000 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (v : Std.I64)
    (hvalid : ValidQueries queries)
    (hres : min_operations queries = ok v), v.val ≤ totalS queries.val ∧
      totalS queries.val ≤ 15 * totalLen queries.val ∧
      15 * totalLen queries.val ≤ 1500000000000000) := by
  sorry

/-- Let d(x) be the least positive k with x < 4^k and S(l,r) = sum_{x=l}^{r} d(x). If 2*d(r) >= S(l,r), then whenever the function returns v, v = d(r).
  Preconditions: queries satisfies the problem constraints and has exactly one query; write that query as [l,r] with 1 <= l < r <= 1000000000. -/
theorem spec_5 (queries : Slice (alloc.vec.Vec Std.I64)) (q : alloc.vec.Vec Std.I64)
    (v : Std.I64)
    (hvalid : ValidQueries queries) (hq : queries.val = [q])
    (h : 2 * d (queryR q) ≥ S (queryL q) (queryR q))
    (hres : min_operations queries = ok v) :
    v.val = d (queryR q) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (q : alloc.vec.Vec Std.I64)
    (v : Std.I64)
    (hvalid : ValidQueries queries) (hq : queries.val = [q])
    (h : 2 * d (queryR q) ≥ S (queryL q) (queryR q))
    (hres : min_operations queries = ok v), v.val = d (queryR q)) := by
  sorry

/-- Let d(x) be the least positive k with x < 4^k and S(l,r) = sum_{x=l}^{r} d(x). If 2*d(r) < S(l,r), then whenever the function returns v, v = ceil(S(l,r)/2).
  Preconditions: queries satisfies the problem constraints and has exactly one query; write that query as [l,r] with 1 <= l < r <= 1000000000. -/
theorem spec_6 (queries : Slice (alloc.vec.Vec Std.I64)) (q : alloc.vec.Vec Std.I64)
    (v : Std.I64)
    (hvalid : ValidQueries queries) (hq : queries.val = [q])
    (h : 2 * d (queryR q) < S (queryL q) (queryR q))
    (hres : min_operations queries = ok v) :
    v.val = ceilHalf (S (queryL q) (queryR q)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (q : alloc.vec.Vec Std.I64)
    (v : Std.I64)
    (hvalid : ValidQueries queries) (hq : queries.val = [q])
    (h : 2 * d (queryR q) < S (queryL q) (queryR q))
    (hres : min_operations queries = ok v), v.val = ceilHalf (S (queryL q) (queryR q))) := by
  sorry

/-- Let d(x) be the least positive k with x < 4^k, S(l,r) = sum_{x=l}^{r} d(x), and m(l,r) = max(d(r), ceil(S(l,r)/2)). For fixed l, m(l,r) is nondecreasing in r. Consequently, whenever both calls return, the value returned for q' is greater than or equal to the value returned for q.
  Preconditions: q and q' are query lists satisfying the problem constraints. The list q' is obtained from q by replacing one query [l,r1] with [l,r2], where 1 <= l < r1 <= r2 <= 1000000000; all other entries are unchanged. -/
theorem spec_7 (q q' : Slice (alloc.vec.Vec Std.I64)) (v v' : Std.I64)
    (l r₁ r₂ : ℤ)
    (hvalid : ValidQueries q) (hvalid' : ValidQueries q')
    (hrep : ReplacedR q.val q'.val l r₁ r₂)
    (hr : r₁ ≤ r₂)
    (hres : min_operations q = ok v) (hres' : min_operations q' = ok v') :
    (∀ r r' : ℤ, r ≤ r' → m l r ≤ m l r') ∧ v.val ≤ v'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (q q' : Slice (alloc.vec.Vec Std.I64)) (v v' : Std.I64)
    (l r₁ r₂ : ℤ)
    (hvalid : ValidQueries q) (hvalid' : ValidQueries q')
    (hrep : ReplacedR q.val q'.val l r₁ r₂)
    (hr : r₁ ≤ r₂)
    (hres : min_operations q = ok v) (hres' : min_operations q' = ok v'), (∀ r r' : ℤ, r ≤ r' → m l r ≤ m l r') ∧ v.val ≤ v'.val) := by
  sorry

/-- Let d(x) be the least positive k with x < 4^k, S(l,r) = sum_{x=l}^{r} d(x), and m(l,r) = max(d(r), ceil(S(l,r)/2)). For fixed r, m(l,r) is nonincreasing in l. Consequently, whenever both calls return, the value returned for q' is less than or equal to the value returned for q.
  Preconditions: q and q' are query lists satisfying the problem constraints. The list q' is obtained from q by replacing one query [l1,r] with [l2,r], where 1 <= l1 <= l2 < r <= 1000000000; all other entries are unchanged. -/
theorem spec_8 (q q' : Slice (alloc.vec.Vec Std.I64)) (v v' : Std.I64)
    (l₁ l₂ r : ℤ)
    (hvalid : ValidQueries q) (hvalid' : ValidQueries q')
    (hrep : ReplacedL q.val q'.val l₁ l₂ r)
    (hl : l₁ ≤ l₂)
    (hres : min_operations q = ok v) (hres' : min_operations q' = ok v') :
    (∀ l l' : ℤ, l ≤ l' → m l' r ≤ m l r) ∧ v'.val ≤ v.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (q q' : Slice (alloc.vec.Vec Std.I64)) (v v' : Std.I64)
    (l₁ l₂ r : ℤ)
    (hvalid : ValidQueries q) (hvalid' : ValidQueries q')
    (hrep : ReplacedL q.val q'.val l₁ l₂ r)
    (hl : l₁ ≤ l₂)
    (hres : min_operations q = ok v) (hres' : min_operations q' = ok v'), (∀ l l' : ℤ, l ≤ l' → m l' r ≤ m l r) ∧ v'.val ≤ v.val) := by
  sorry

/-- Whenever the calls on q1, q2, and q1++q2 return v1, v2, and v3 respectively, we have v3 = v1 + v2.
  Preconditions: q1 and q2 are nonempty query lists satisfying the problem constraints, and their concatenation q1++q2 also has length at most 100000 with every query entry valid. -/
theorem spec_9 (q₁ q₂ q₃ : Slice (alloc.vec.Vec Std.I64)) (v₁ v₂ v₃ : Std.I64)
    (hvalid₁ : ValidQueries q₁) (hvalid₂ : ValidQueries q₂)
    (hcat : q₃.val = q₁.val ++ q₂.val)
    (hlen : q₃.val.length ≤ 100000)
    (hentries : ∀ v ∈ q₃.val, ValidQuery v)
    (hres₁ : min_operations q₁ = ok v₁)
    (hres₂ : min_operations q₂ = ok v₂)
    (hres₃ : min_operations q₃ = ok v₃) :
    v₃.val = v₁.val + v₂.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (q₁ q₂ q₃ : Slice (alloc.vec.Vec Std.I64)) (v₁ v₂ v₃ : Std.I64)
    (hvalid₁ : ValidQueries q₁) (hvalid₂ : ValidQueries q₂)
    (hcat : q₃.val = q₁.val ++ q₂.val)
    (hlen : q₃.val.length ≤ 100000)
    (hentries : ∀ v ∈ q₃.val, ValidQuery v)
    (hres₁ : min_operations q₁ = ok v₁)
    (hres₂ : min_operations q₂ = ok v₂)
    (hres₃ : min_operations q₃ = ok v₃), v₃.val = v₁.val + v₂.val) := by
  sorry

/-- Whenever both calls return, the value returned for q' equals the value returned for queries.
  Preconditions: queries satisfies the problem constraints; q' is any permutation of the entries of queries. -/
theorem spec_10 (queries q' : Slice (alloc.vec.Vec Std.I64)) (v v' : Std.I64)
    (hvalid : ValidQueries queries) (hvalid' : ValidQueries q')
    (hperm : List.Perm q'.val queries.val)
    (hres : min_operations queries = ok v) (hres' : min_operations q' = ok v') :
    v'.val = v.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (queries q' : Slice (alloc.vec.Vec Std.I64)) (v v' : Std.I64)
    (hvalid : ValidQueries queries) (hvalid' : ValidQueries q')
    (hperm : List.Perm q'.val queries.val)
    (hres : min_operations queries = ok v) (hres' : min_operations q' = ok v'), v'.val = v.val) := by
  sorry

/-- The returned value is at least n. The lower bound n is attained: if every query is [1,2], then the function returns n.
  Preconditions: queries satisfies the problem constraints and has n = len(queries) queries. -/
theorem spec_11 (queries : Slice (alloc.vec.Vec Std.I64)) (v : Std.I64)
    (hvalid : ValidQueries queries)
    (hres : min_operations queries = ok v) :
    (queries.val.length : ℤ) ≤ v.val ∧
      (∀ (n : ℕ) (hn₁ : 1 ≤ n) (hn : n ≤ 100000),
        ∃ w : Std.I64,
          min_operations (sliceOfList (List.replicate n (queryVec (1#i64) (2#i64)))
            (by
              have h100 : (100000 : ℕ) ≤ Aeneas.Std.Usize.max :=
                le_trans (by norm_num) Aeneas.Std.Usize.cMax_bound_concrete.1
              simpa using le_trans hn h100)) = ok w ∧
          w.val = (n : ℤ)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (v : Std.I64)
    (hvalid : ValidQueries queries)
    (hres : min_operations queries = ok v), (queries.val.length : ℤ) ≤ v.val ∧
      (∀ (n : ℕ) (hn₁ : 1 ≤ n) (hn : n ≤ 100000),
        ∃ w : Std.I64,
          min_operations (sliceOfList (List.replicate n (queryVec (1#i64) (2#i64)))
            (by
              have h100 : (100000 : ℕ) ≤ Aeneas.Std.Usize.max :=
                le_trans (by norm_num) Aeneas.Std.Usize.cMax_bound_concrete.1
              simpa using le_trans hn h100)) = ok w ∧
          w.val = (n : ℤ))) := by
  sorry

/-- The returned value is at most 7321043037. This bound is attained by the single query [1,1000000000].
  Preconditions: queries satisfies the problem constraints and has exactly one query. -/
theorem spec_12 (queries : Slice (alloc.vec.Vec Std.I64)) (v : Std.I64)
    (hvalid : ValidQueries queries) (hone : queries.val.length = 1)
    (hres : min_operations queries = ok v) :
    v.val ≤ 7321043037 ∧
      (∃ w : Std.I64, min_operations specQuery = ok w ∧ w.val = 7321043037) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (v : Std.I64)
    (hvalid : ValidQueries queries) (hone : queries.val.length = 1)
    (hres : min_operations queries = ok v), v.val ≤ 7321043037 ∧
      (∃ w : Std.I64, min_operations specQuery = ok w ∧ w.val = 7321043037)) := by
  sorry

/-- For every query [l,r] in the input, define d(x) as the least positive k with x < 4^k, S(l,r) = sum_{x=l}^{r} d(x), and m(l,r) = max(d(r), ceil(S(l,r)/2)). Then m(l,r) is a true minimum: there exists a legal sequence of exactly m(l,r) operations reducing the array l,l+1,...,r to all zeros, and no legal sequence of fewer operations does so. Whenever the function returns a value, that value is the sum of these m(l,r).
  Preconditions: queries satisfies the problem constraints: 1 <= len(queries) <= 100000; every queries[i] has length 2; l_i = queries[i][0], r_i = queries[i][1] with 1 <= l_i < r_i <= 1000000000. -/
theorem spec_13 (queries : Slice (alloc.vec.Vec Std.I64)) (v : Std.I64)
    (hvalid : ValidQueries queries)
    (hres : min_operations queries = ok v) :
    (∀ q ∈ queries.val,
        LegalSeq (queryL q) (queryR q) (m (queryL q) (queryR q)).toNat ∧
        ∀ k : ℕ, LegalSeq (queryL q) (queryR q) k →
          (m (queryL q) (queryR q)).toNat ≤ k) ∧
      v.val = totalM queries.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (v : Std.I64)
    (hvalid : ValidQueries queries)
    (hres : min_operations queries = ok v), (∀ q ∈ queries.val,
        LegalSeq (queryL q) (queryR q) (m (queryL q) (queryR q)).toNat ∧
        ∀ k : ℕ, LegalSeq (queryL q) (queryR q) k →
          (m (queryL q) (queryR q)).toNat ≤ k) ∧
      v.val = totalM queries.val) := by
  sorry

/-- Let d(x) be the least positive k with x < 4^k and S(l,r) = sum_{x=l}^{r} d(x). Whenever the function returns v, 2*v >= sum_{i=0}^{len(queries)-1} S(l_i,r_i).
  Preconditions: queries satisfies the problem constraints: 1 <= len(queries) <= 100000; every queries[i] has length 2; l_i = queries[i][0], r_i = queries[i][1] with 1 <= l_i < r_i <= 1000000000. -/
theorem spec_14 (queries : Slice (alloc.vec.Vec Std.I64)) (v : Std.I64)
    (hvalid : ValidQueries queries)
    (hres : min_operations queries = ok v) :
    2 * v.val ≥ totalS queries.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (v : Std.I64)
    (hvalid : ValidQueries queries)
    (hres : min_operations queries = ok v), 2 * v.val ≥ totalS queries.val) := by
  sorry

end AegisSpec.MinOperations
