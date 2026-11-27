import Aegis.CountOfPeaks.Code.Funs

/-!
# Specifications of `Aegis.CountOfPeaks.count_of_peaks`

LeetCode problem `peaks-in-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountOfPeaks

def numsOf (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def outOf (ans : Aeneas.Std.alloc.vec.Vec Std.I64) : List ℤ := ans.val.map (fun x => x.val)

def queriesOf (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64)) : List (List ℤ) :=
  queries.val.map (fun q => q.val.map (fun x => x.val))

def queryAt (qs : List (List ℤ)) (t : ℕ) : List ℤ := qs.getD t []

def isType1 (q : List ℤ) : Bool := q.getD 0 0 == 1

def type1Indices (qs : List (List ℤ)) : List ℕ :=
  (List.range qs.length).filter (fun t => isType1 (queryAt qs t))

def applyQuery (a : List ℤ) (q : List ℤ) : List ℤ :=
  if q.getD 0 0 = 2 then a.set (q.getD 1 0).toNat (q.getD 2 0) else a

def state (a : List ℤ) (qs : List (List ℤ)) (t : ℕ) : List ℤ :=
  (qs.take t).foldl applyQuery a

@[reducible] def PeakAt (a : List ℤ) (k : ℕ) : Prop :=
  1 ≤ k ∧ k + 1 < a.length ∧ a.getD (k - 1) 0 < a.getD k 0 ∧ a.getD (k + 1) 0 < a.getD k 0

def peakCount (a : List ℤ) (ql qr : ℤ) : ℕ :=
  ((Finset.Ico (ql + 1).toNat qr.toNat).filter (fun k => PeakAt a k)).card

def answerAt (a : List ℤ) (qs : List (List ℤ)) (t : ℕ) : ℤ :=
  let q := queryAt qs t
  if q.getD 0 0 = 1 then ((peakCount (state a qs t) (q.getD 1 0) (q.getD 2 0) : ℕ) : ℤ) else 0

def Pre (nums : Slice Std.I64) (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64)) : Prop :=
  let a := numsOf nums
  let qs := queriesOf queries
  let n : ℤ := (a.length : ℤ)
  3 ≤ a.length ∧ a.length ≤ 10 ^ 5 ∧ 1 ≤ qs.length ∧ qs.length ≤ 10 ^ 5 ∧
    (∀ k : ℕ, k < a.length → 1 ≤ a.getD k 0 ∧ a.getD k 0 ≤ 10 ^ 5) ∧
    ∀ i : ℕ,
      i < qs.length →
        (queryAt qs i).length = 3 ∧
          ((queryAt qs i).getD 0 0 = 1 ∨ (queryAt qs i).getD 0 0 = 2) ∧
          ((queryAt qs i).getD 0 0 = 1 →
            0 ≤ (queryAt qs i).getD 1 0 ∧
              (queryAt qs i).getD 1 0 ≤ (queryAt qs i).getD 2 0 ∧
              (queryAt qs i).getD 2 0 ≤ n - 1) ∧
          ((queryAt qs i).getD 0 0 = 2 →
            0 ≤ (queryAt qs i).getD 1 0 ∧
              (queryAt qs i).getD 1 0 ≤ n - 1 ∧
              1 ≤ (queryAt qs i).getD 2 0 ∧ (queryAt qs i).getD 2 0 ≤ 10 ^ 5)

/-- Whenever the function returns a result ans, the following holds. Let A^0 = nums, and for t = 0,...,m-1 let A^{t+1} be A^t if queries[t][0] = 1, and otherwise let A^{t+1} be the array obtained from A^t by setting position queries[t][1] to queries[t][2] and leaving all other positions unchanged. Then len(ans) equals the number of t with 0 <= t < m and queries[t][0] = 1. For each p with 0 <= p < len(ans), let t be the p-th index (0-based, in increasing order) such that queries[t][0] = 1, and write queries[t] = [1, ql, qr]. Then ans[p] is exactly the number of integers k with ql < k < qr and A^t[k] > A^t[k-1] and A^t[k] > A^t[k+1].
  Preconditions: Let n = len(nums) and m = len(queries). All indices are 0-based. 3 <= n <= 10^5. 1 <= m <= 10^5. For every k with 0 <= k < n, 1 <= nums[k] <= 10^5. For every i with 0 <= i < m: len(queries[i]) = 3; queries[i][0] is 1 or 2; if queries[i][0] = 1 then 0 <= queries[i][1] <= queries[i][2] <= n-1; if queries[i][0] = 2 then 0 <= queries[i][1] <= n-1 and 1 <= queries[i][2] <= 10^5. -/
theorem spec_1
    (nums : Slice Std.I64) (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64))
    (ans : Aeneas.Std.alloc.vec.Vec Std.I64) (hpre : Pre nums queries)
    (h : Aegis.CountOfPeaks.count_of_peaks nums queries = ok ans) :
    let a := numsOf nums
    let qs := queriesOf queries
    (outOf ans).length = (type1Indices qs).length ∧
      (∀ (p t : ℕ),
        (type1Indices qs)[p]? = some t → (outOf ans)[p]? = some (answerAt a qs t)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64))
    (ans : Aeneas.Std.alloc.vec.Vec Std.I64) (hpre : Pre nums queries)
    (h : Aegis.CountOfPeaks.count_of_peaks nums queries = ok ans), let a := numsOf nums
    let qs := queriesOf queries
    (outOf ans).length = (type1Indices qs).length ∧
      (∀ (p t : ℕ),
        (type1Indices qs)[p]? = some t → (outOf ans)[p]? = some (answerAt a qs t))) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
  Preconditions: Let n = len(nums) and m = len(queries). All indices are 0-based. 3 <= n <= 10^5. 1 <= m <= 10^5. For every k with 0 <= k < n, 1 <= nums[k] <= 10^5. For every i with 0 <= i < m: len(queries[i]) = 3; queries[i][0] is 1 or 2; if queries[i][0] = 1 then 0 <= queries[i][1] <= queries[i][2] <= n-1; if queries[i][0] = 2 then 0 <= queries[i][1] <= n-1 and 1 <= queries[i][2] <= 10^5. -/
theorem spec_2
    (nums : Slice Std.I64) (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64))
    (hpre : Pre nums queries) :
    ∃ r : Aeneas.Std.alloc.vec.Vec Std.I64,
      Aegis.CountOfPeaks.count_of_peaks nums queries = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64))
    (hpre : Pre nums queries), ∃ r : Aeneas.Std.alloc.vec.Vec Std.I64,
      Aegis.CountOfPeaks.count_of_peaks nums queries = ok r) := by
  sorry

/-- Whenever the function returns r, len(r) is exactly the number of type-1 queries (indices t with queries[t][0] = 1), and for every p with 0 <= p < len(r), the p-th element of r is the answer to the p-th type-1 query in the order the type-1 queries occur in queries (0-based).
  Preconditions: Let n = len(nums) and m = len(queries). All indices are 0-based. 3 <= n <= 10^5. 1 <= m <= 10^5. For every k with 0 <= k < n, 1 <= nums[k] <= 10^5. For every i with 0 <= i < m: len(queries[i]) = 3; queries[i][0] is 1 or 2; if queries[i][0] = 1 then 0 <= queries[i][1] <= queries[i][2] <= n-1; if queries[i][0] = 2 then 0 <= queries[i][1] <= n-1 and 1 <= queries[i][2] <= 10^5. -/
theorem spec_3
    (nums : Slice Std.I64) (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64))
    (r : Aeneas.Std.alloc.vec.Vec Std.I64) (hpre : Pre nums queries)
    (h : Aegis.CountOfPeaks.count_of_peaks nums queries = ok r) :
    let a := numsOf nums
    let qs := queriesOf queries
    (outOf r).length = (type1Indices qs).length ∧
      (∀ (p t : ℕ),
        (type1Indices qs)[p]? = some t → (outOf r)[p]? = some (answerAt a qs t)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64))
    (r : Aeneas.Std.alloc.vec.Vec Std.I64) (hpre : Pre nums queries)
    (h : Aegis.CountOfPeaks.count_of_peaks nums queries = ok r), let a := numsOf nums
    let qs := queriesOf queries
    (outOf r).length = (type1Indices qs).length ∧
      (∀ (p t : ℕ),
        (type1Indices qs)[p]? = some t → (outOf r)[p]? = some (answerAt a qs t))) := by
  sorry

/-- Whenever the function returns ans, for every type-1 query at index t with queries[t] = [1, ql, qr] and corresponding output value y (so y = ans[p] where t is the p-th type-1 query index), we have 0 <= y <= floor((qr-ql)/2), where floor is integer division rounding down.
  Preconditions: Let n = len(nums) and m = len(queries). All indices are 0-based. 3 <= n <= 10^5. 1 <= m <= 10^5. For every k with 0 <= k < n, 1 <= nums[k] <= 10^5. For every i with 0 <= i < m: len(queries[i]) = 3; queries[i][0] is 1 or 2; if queries[i][0] = 1 then 0 <= queries[i][1] <= queries[i][2] <= n-1; if queries[i][0] = 2 then 0 <= queries[i][1] <= n-1 and 1 <= queries[i][2] <= 10^5. -/
theorem spec_4
    (nums : Slice Std.I64) (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64))
    (ans : Aeneas.Std.alloc.vec.Vec Std.I64) (hpre : Pre nums queries)
    (h : Aegis.CountOfPeaks.count_of_peaks nums queries = ok ans) :
    let qs := queriesOf queries
    ∀ (p t : ℕ) (ql qr y : ℤ),
      queryAt qs t = [1, ql, qr] →
        (type1Indices qs)[p]? = some t →
          (outOf ans)[p]? = some y → 0 ≤ y ∧ y ≤ (qr - ql) / 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64))
    (ans : Aeneas.Std.alloc.vec.Vec Std.I64) (hpre : Pre nums queries)
    (h : Aegis.CountOfPeaks.count_of_peaks nums queries = ok ans), let qs := queriesOf queries
    ∀ (p t : ℕ) (ql qr y : ℤ),
      queryAt qs t = [1, ql, qr] →
        (type1Indices qs)[p]? = some t →
          (outOf ans)[p]? = some y → 0 ≤ y ∧ y ≤ (qr - ql) / 2) := by
  sorry

/-- Whenever the function returns ans, for every type-1 query at index t with queries[t] = [1, ql, qr] and corresponding output value y, where A^t is the array state just before query t (starting from nums and applying the preceding type-2 assignments in order), y > 0 if and only if there exists an integer k with ql < k < qr such that A^t[k] > A^t[k-1] and A^t[k] > A^t[k+1].
  Preconditions: Let n = len(nums) and m = len(queries). All indices are 0-based. 3 <= n <= 10^5. 1 <= m <= 10^5. For every k with 0 <= k < n, 1 <= nums[k] <= 10^5. For every i with 0 <= i < m: len(queries[i]) = 3; queries[i][0] is 1 or 2; if queries[i][0] = 1 then 0 <= queries[i][1] <= queries[i][2] <= n-1; if queries[i][0] = 2 then 0 <= queries[i][1] <= n-1 and 1 <= queries[i][2] <= 10^5. -/
theorem spec_5
    (nums : Slice Std.I64) (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64))
    (ans : Aeneas.Std.alloc.vec.Vec Std.I64) (hpre : Pre nums queries)
    (h : Aegis.CountOfPeaks.count_of_peaks nums queries = ok ans) :
    let a := numsOf nums
    let qs := queriesOf queries
    ∀ (p t : ℕ) (ql qr y : ℤ),
      queryAt qs t = [1, ql, qr] →
        (type1Indices qs)[p]? = some t →
          (outOf ans)[p]? = some y →
            0 < y ↔ ∃ k : ℕ, ql < (k : ℤ) ∧ (k : ℤ) < qr ∧ PeakAt (state a qs t) k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64))
    (ans : Aeneas.Std.alloc.vec.Vec Std.I64) (hpre : Pre nums queries)
    (h : Aegis.CountOfPeaks.count_of_peaks nums queries = ok ans), let a := numsOf nums
    let qs := queriesOf queries
    ∀ (p t : ℕ) (ql qr y : ℤ),
      queryAt qs t = [1, ql, qr] →
        (type1Indices qs)[p]? = some t →
          (outOf ans)[p]? = some y →
            0 < y ↔ ∃ k : ℕ, ql < (k : ℤ) ∧ (k : ℤ) < qr ∧ PeakAt (state a qs t) k) := by
  sorry

/-- Whenever the function returns ans, let t1 < t2 be two type-1 query indices with queries[t1] = [1, ql, qr] and queries[t2] = [1, ql, qr]. If every query index u with t1 < u < t2 satisfies queries[u][0] = 1 (so there is no update between them), then the output values corresponding to t1 and t2 in ans are equal.
  Preconditions: Let n = len(nums) and m = len(queries). All indices are 0-based. 3 <= n <= 10^5. 1 <= m <= 10^5. For every k with 0 <= k < n, 1 <= nums[k] <= 10^5. For every i with 0 <= i < m: len(queries[i]) = 3; queries[i][0] is 1 or 2; if queries[i][0] = 1 then 0 <= queries[i][1] <= queries[i][2] <= n-1; if queries[i][0] = 2 then 0 <= queries[i][1] <= n-1 and 1 <= queries[i][2] <= 10^5. -/
theorem spec_6
    (nums : Slice Std.I64) (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64))
    (ans : Aeneas.Std.alloc.vec.Vec Std.I64) (hpre : Pre nums queries)
    (h : Aegis.CountOfPeaks.count_of_peaks nums queries = ok ans) :
    let qs := queriesOf queries
    ∀ (p₁ p₂ t₁ t₂ : ℕ) (ql qr y₁ y₂ : ℤ),
      t₁ < t₂ →
        queryAt qs t₁ = [1, ql, qr] →
          queryAt qs t₂ = [1, ql, qr] →
            (type1Indices qs)[p₁]? = some t₁ →
              (type1Indices qs)[p₂]? = some t₂ →
                (∀ u : ℕ, t₁ < u → u < t₂ → isType1 (queryAt qs u) = true) →
                  (outOf ans)[p₁]? = some y₁ →
                    (outOf ans)[p₂]? = some y₂ → y₁ = y₂ := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64))
    (ans : Aeneas.Std.alloc.vec.Vec Std.I64) (hpre : Pre nums queries)
    (h : Aegis.CountOfPeaks.count_of_peaks nums queries = ok ans), let qs := queriesOf queries
    ∀ (p₁ p₂ t₁ t₂ : ℕ) (ql qr y₁ y₂ : ℤ),
      t₁ < t₂ →
        queryAt qs t₁ = [1, ql, qr] →
          queryAt qs t₂ = [1, ql, qr] →
            (type1Indices qs)[p₁]? = some t₁ →
              (type1Indices qs)[p₂]? = some t₂ →
                (∀ u : ℕ, t₁ < u → u < t₂ → isType1 (queryAt qs u) = true) →
                  (outOf ans)[p₁]? = some y₁ →
                    (outOf ans)[p₂]? = some y₂ → y₁ = y₂) := by
  sorry

/-- Whenever the function returns r, let t be any index with queries[t] = [2,idx,val] such that in the state A^t just before query t we have A^t[idx] = val. Then for every type-1 query at an index t' > t, its answer in r is the same as the answer it would have if query t were omitted and all other queries were processed in the same order.
  Preconditions: Let n = len(nums) and m = len(queries). All indices are 0-based. 3 <= n <= 10^5. 1 <= m <= 10^5. For every k with 0 <= k < n, 1 <= nums[k] <= 10^5. For every i with 0 <= i < m: len(queries[i]) = 3; queries[i][0] is 1 or 2; if queries[i][0] = 1 then 0 <= queries[i][1] <= queries[i][2] <= n-1; if queries[i][0] = 2 then 0 <= queries[i][1] <= n-1 and 1 <= queries[i][2] <= 10^5. -/
theorem spec_7
    (nums : Slice Std.I64) (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64))
    (ans : Aeneas.Std.alloc.vec.Vec Std.I64) (hpre : Pre nums queries)
    (h : Aegis.CountOfPeaks.count_of_peaks nums queries = ok ans) :
    let a := numsOf nums
    let qs := queriesOf queries
    ∀ (p t t' : ℕ) (idx val y : ℤ),
      queryAt qs t = [2, idx, val] →
        (state a qs t)[idx.toNat]? = some val →
          t < t' →
            (type1Indices qs)[p]? = some t' →
              (outOf ans)[p]? = some y →
                y = answerAt a (qs.eraseIdx t) (t' - 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64))
    (ans : Aeneas.Std.alloc.vec.Vec Std.I64) (hpre : Pre nums queries)
    (h : Aegis.CountOfPeaks.count_of_peaks nums queries = ok ans), let a := numsOf nums
    let qs := queriesOf queries
    ∀ (p t t' : ℕ) (idx val y : ℤ),
      queryAt qs t = [2, idx, val] →
        (state a qs t)[idx.toNat]? = some val →
          t < t' →
            (type1Indices qs)[p]? = some t' →
              (outOf ans)[p]? = some y →
                y = answerAt a (qs.eraseIdx t) (t' - 1)) := by
  sorry

/-- Whenever the function returns ans, for every type-1 query at index t with queries[t] = [1, ql, qr] and corresponding output value y, where A^t is the array state just before query t (starting from nums and applying the preceding type-2 assignments in order), y depends only on the values A^t[ql], A^t[ql+1], ..., A^t[qr]. More precisely, if B is any array of length n such that B[i] = A^t[i] for every i with ql <= i <= qr, then the number of k with ql < k < qr, B[k] > B[k-1], and B[k] > B[k+1] is also y.
  Preconditions: Let n = len(nums) and m = len(queries). All indices are 0-based. 3 <= n <= 10^5. 1 <= m <= 10^5. For every k with 0 <= k < n, 1 <= nums[k] <= 10^5. For every i with 0 <= i < m: len(queries[i]) = 3; queries[i][0] is 1 or 2; if queries[i][0] = 1 then 0 <= queries[i][1] <= queries[i][2] <= n-1; if queries[i][0] = 2 then 0 <= queries[i][1] <= n-1 and 1 <= queries[i][2] <= 10^5. -/
theorem spec_8
    (nums : Slice Std.I64) (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64))
    (ans : Aeneas.Std.alloc.vec.Vec Std.I64) (hpre : Pre nums queries)
    (h : Aegis.CountOfPeaks.count_of_peaks nums queries = ok ans) :
    let a := numsOf nums
    let qs := queriesOf queries
    ∀ (p t : ℕ) (ql qr y : ℤ) (B : List ℤ),
      queryAt qs t = [1, ql, qr] →
        (type1Indices qs)[p]? = some t →
          (outOf ans)[p]? = some y →
            B.length = a.length →
              (∀ i : ℕ, ql ≤ (i : ℤ) → (i : ℤ) ≤ qr → B[i]? = (state a qs t)[i]?) →
                ((peakCount B ql qr : ℕ) : ℤ) = y := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64))
    (ans : Aeneas.Std.alloc.vec.Vec Std.I64) (hpre : Pre nums queries)
    (h : Aegis.CountOfPeaks.count_of_peaks nums queries = ok ans), let a := numsOf nums
    let qs := queriesOf queries
    ∀ (p t : ℕ) (ql qr y : ℤ) (B : List ℤ),
      queryAt qs t = [1, ql, qr] →
        (type1Indices qs)[p]? = some t →
          (outOf ans)[p]? = some y →
            B.length = a.length →
              (∀ i : ℕ, ql ≤ (i : ℤ) → (i : ℤ) ≤ qr → B[i]? = (state a qs t)[i]?) →
                ((peakCount B ql qr : ℕ) : ℤ) = y) := by
  sorry

/-- Whenever the function returns r, let t1 and t2 be two type-1 query indices such that no type-2 query index u satisfies min(t1,t2) < u < max(t1,t2) (so both queries use the same array state). Let their ranges be [l1,r1] and [l2,r2]. If l1 <= l2 <= r2 <= r1, then the output value for the query with range [l2,r2] is at most the output value for the query with range [l1,r1].
  Preconditions: Let n = len(nums) and m = len(queries). All indices are 0-based. 3 <= n <= 10^5. 1 <= m <= 10^5. For every k with 0 <= k < n, 1 <= nums[k] <= 10^5. For every i with 0 <= i < m: len(queries[i]) = 3; queries[i][0] is 1 or 2; if queries[i][0] = 1 then 0 <= queries[i][1] <= queries[i][2] <= n-1; if queries[i][0] = 2 then 0 <= queries[i][1] <= n-1 and 1 <= queries[i][2] <= 10^5. -/
theorem spec_9
    (nums : Slice Std.I64) (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64))
    (ans : Aeneas.Std.alloc.vec.Vec Std.I64) (hpre : Pre nums queries)
    (h : Aegis.CountOfPeaks.count_of_peaks nums queries = ok ans) :
    let qs := queriesOf queries
    ∀ (p₁ p₂ t₁ t₂ : ℕ) (ql₁ qr₁ ql₂ qr₂ y₁ y₂ : ℤ),
      queryAt qs t₁ = [1, ql₁, qr₁] →
        queryAt qs t₂ = [1, ql₂, qr₂] →
          (type1Indices qs)[p₁]? = some t₁ →
            (type1Indices qs)[p₂]? = some t₂ →
              (∀ u : ℕ, min t₁ t₂ < u → u < max t₁ t₂ → isType1 (queryAt qs u) = false) →
                ql₁ ≤ ql₂ → ql₂ ≤ qr₂ → qr₂ ≤ qr₁ →
                  (outOf ans)[p₁]? = some y₁ →
                    (outOf ans)[p₂]? = some y₂ → y₂ ≤ y₁ := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (queries : Slice (Aeneas.Std.alloc.vec.Vec Std.I64))
    (ans : Aeneas.Std.alloc.vec.Vec Std.I64) (hpre : Pre nums queries)
    (h : Aegis.CountOfPeaks.count_of_peaks nums queries = ok ans), let qs := queriesOf queries
    ∀ (p₁ p₂ t₁ t₂ : ℕ) (ql₁ qr₁ ql₂ qr₂ y₁ y₂ : ℤ),
      queryAt qs t₁ = [1, ql₁, qr₁] →
        queryAt qs t₂ = [1, ql₂, qr₂] →
          (type1Indices qs)[p₁]? = some t₁ →
            (type1Indices qs)[p₂]? = some t₂ →
              (∀ u : ℕ, min t₁ t₂ < u → u < max t₁ t₂ → isType1 (queryAt qs u) = false) →
                ql₁ ≤ ql₂ → ql₂ ≤ qr₂ → qr₂ ≤ qr₁ →
                  (outOf ans)[p₁]? = some y₁ →
                    (outOf ans)[p₂]? = some y₂ → y₂ ≤ y₁) := by
  sorry

end AegisSpec.CountOfPeaks
