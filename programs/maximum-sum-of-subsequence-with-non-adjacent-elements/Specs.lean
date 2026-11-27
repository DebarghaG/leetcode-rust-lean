import Aegis.MaximumSumSubsequence.Code.Funs

/-!
# Specifications of `Aegis.MaximumSumSubsequence.maximum_sum_subsequence`

LeetCode problem `maximum-sum-of-subsequence-with-non-adjacent-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaximumSumSubsequence

namespace AegisSpec.MaximumSumSubsequence

def numsInts (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

def queryInts (v : alloc.vec.Vec I64) : List ℤ := v.val.map (fun x => x.val)

def qPos (v : alloc.vec.Vec I64) : ℕ := ((queryInts v).getD 0 0).toNat

def qVal (v : alloc.vec.Vec I64) : ℤ := (queryInts v).getD 1 0

def queryPairs (queries : Slice (alloc.vec.Vec I64)) : List (ℕ × ℤ) :=
  queries.val.map (fun v => (qPos v, qVal v))

def G : List ℤ → ℤ
  | [] => 0
  | [x] => max 0 x
  | x :: y :: rest => max (G (y :: rest)) (x + G rest)

def totalG (a : List ℤ) (qs : List (ℕ × ℤ)) : ℤ :=
  match qs with
  | [] => 0
  | (p, x) :: qs' => G (a.set p x) + totalG (a.set p x) qs'

def finalState (a : List ℤ) : List (ℕ × ℤ) → List ℤ
  | [] => a
  | (p, x) :: qs => finalState (a.set p x) qs

def runQueries (a : List ℤ) : List (ℕ × ℤ) → List (List ℤ)
  | [] => [a]
  | (p, x) :: qs => a :: runQueries (a.set p x) qs

def nthState (a : List ℤ) (qs : List (ℕ × ℤ)) (t : ℕ) : List ℤ :=
  (runQueries a qs).getD t []

def WritesCurrent (a : List ℤ) : List (ℕ × ℤ) → Prop
  | [] => True
  | (p, x) :: qs => x = a.getD p 0 ∧ WritesCurrent (a.set p x) qs

def headTwoMax (a : List ℤ) : ℤ := max 0 (max (a.getD 0 0) (a.getD 1 0))

def totalHeadTwo (a : List ℤ) (qs : List (ℕ × ℤ)) : ℤ :=
  match qs with
  | [] => 0
  | (p, x) :: qs' => headTwoMax (a.set p x) + totalHeadTwo (a.set p x) qs'

def NonAdjacent (S : Finset ℕ) : Prop := ∀ i, i ∈ S → i + 1 ∉ S

def sumOver (a : List ℤ) (S : Finset ℕ) : ℤ := S.sum (fun i => a.getD i 0)

def IsMaxNonAdjacent (a : List ℤ) (S : Finset ℕ) : Prop :=
  (∀ i ∈ S, i < a.length) ∧ NonAdjacent S ∧ sumOver a S = G a ∧
    ∀ S' : Finset ℕ,
      (∀ i ∈ S', i < a.length) → NonAdjacent S' → sumOver a S' ≤ sumOver a S

def firstPos (queries : Slice (alloc.vec.Vec I64)) : ℕ :=
  ((queryPairs queries).getD 0 (0, 0)).1

def Pre (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64)) : Prop :=
  1 ≤ nums.val.length ∧ nums.val.length ≤ 50000 ∧
  1 ≤ queries.val.length ∧ queries.val.length ≤ 50000 ∧
  (∀ v ∈ nums.val, -100000 ≤ v.val ∧ v.val ≤ 100000) ∧
  (∀ v ∈ queries.val, v.val.length = 2) ∧
  (∀ v ∈ queries.val,
    0 ≤ (queryInts v).getD 0 0 ∧ (queryInts v).getD 0 0 < (nums.val.length : ℤ)) ∧
  (∀ v ∈ queries.val,
    -100000 ≤ (queryInts v).getD 1 0 ∧ (queryInts v).getD 1 0 ≤ 100000)

/-- Let A_0 be nums. For t = 0,...,q-1, let A_{t+1} be the length-n array obtained from A_t by replacing coordinate p_t with x_t. For any length-n integer array a, let G(a) be the maximum of ∑_{i∈S} a[i] over all subsets S ⊆ {0,...,n-1} such that no i with 0 ≤ i < n-1 has both i∈S and i+1∈S; the empty subset is allowed. Then the function returns a result r and r = (∑_{t=0}^{q-1} G(A_{t+1})) mod 1000000007, where modulo denotes the least nonnegative remainder.
  Preconditions: Let n = len(nums) and q = len(queries). 1 ≤ n ≤ 50000, 1 ≤ q ≤ 50000. For every i with 0 ≤ i < n, -100000 ≤ nums[i] ≤ 100000. Each queries[t] has length 2; writing p_t = queries[t][0] and x_t = queries[t][1], we have 0 ≤ p_t < n and -100000 ≤ x_t ≤ 100000. -/
theorem spec_1
    (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries) :
    ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r ∧
      r.val = totalG (numsInts nums) (queryPairs queries) % 1000000007 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries), ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r ∧
      r.val = totalG (numsInts nums) (queryPairs queries) % 1000000007) := by
  sorry

/-- The function returns a result r; in particular, under these preconditions it does not fail due to overflow, out-of-bounds access, or panic.
  Preconditions: Let n = len(nums) and q = len(queries). 1 ≤ n ≤ 50000, 1 ≤ q ≤ 50000. For every i with 0 ≤ i < n, -100000 ≤ nums[i] ≤ 100000. Each queries[t] has length 2; writing p_t = queries[t][0] and x_t = queries[t][1], we have 0 ≤ p_t < n and -100000 ≤ x_t ≤ 100000. -/
theorem spec_2
    (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries) :
    ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries), ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r) := by
  sorry

/-- The function returns a result r satisfying 0 ≤ r ≤ 1000000006.
  Preconditions: Let n = len(nums) and q = len(queries). 1 ≤ n ≤ 50000, 1 ≤ q ≤ 50000. For every i with 0 ≤ i < n, -100000 ≤ nums[i] ≤ 100000. Each queries[t] has length 2; writing p_t = queries[t][0] and x_t = queries[t][1], we have 0 ≤ p_t < n and -100000 ≤ x_t ≤ 100000. -/
theorem spec_3
    (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries) :
    ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r ∧
      0 ≤ r.val ∧ r.val ≤ 1000000006 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries), ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r ∧
      0 ≤ r.val ∧ r.val ≤ 1000000006) := by
  sorry

/-- Let x_t = queries[t][1] for t = 0,...,q-1. The function returns r = (∑_{t=0}^{q-1} max(0, x_t)) mod 1000000007.
  Preconditions: Let n = len(nums) and q = len(queries). 1 ≤ n ≤ 50000, 1 ≤ q ≤ 50000. For every i with 0 ≤ i < n, -100000 ≤ nums[i] ≤ 100000. Each queries[t] has length 2; writing p_t = queries[t][0] and x_t = queries[t][1], we have 0 ≤ p_t < n and -100000 ≤ x_t ≤ 100000. Additionally, n = 1. -/
theorem spec_4
    (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries) (hn : nums.val.length = 1) :
    ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r ∧
      r.val = (queries.val.map (fun v => max 0 (qVal v))).sum % 1000000007 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries) (hn : nums.val.length = 1), ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r ∧
      r.val = (queries.val.map (fun v => max 0 (qVal v))).sum % 1000000007) := by
  sorry

/-- Let A_0 = nums, and for t = 0,...,q-1 let A_{t+1} be A_t with coordinate p_t replaced by x_t. Then the function returns r = (∑_{t=0}^{q-1} max(0, A_{t+1}[0], A_{t+1}[1])) mod 1000000007.
  Preconditions: Let n = len(nums) and q = len(queries). 1 ≤ n ≤ 50000, 1 ≤ q ≤ 50000. For every i with 0 ≤ i < n, -100000 ≤ nums[i] ≤ 100000. Each queries[t] has length 2; writing p_t = queries[t][0] and x_t = queries[t][1], we have 0 ≤ p_t < n and -100000 ≤ x_t ≤ 100000. Additionally, n = 2. -/
theorem spec_5
    (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries) (hn : nums.val.length = 2) :
    ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r ∧
      r.val = totalHeadTwo (numsInts nums) (queryPairs queries) % 1000000007 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries) (hn : nums.val.length = 2), ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r ∧
      r.val = totalHeadTwo (numsInts nums) (queryPairs queries) % 1000000007) := by
  sorry

/-- The function returns r = 0.
  Preconditions: Let n = len(nums) and q = len(queries). 1 ≤ n ≤ 50000, 1 ≤ q ≤ 50000. For every i with 0 ≤ i < n, -100000 ≤ nums[i] ≤ 100000. Each queries[t] has length 2; writing p_t = queries[t][0] and x_t = queries[t][1], we have 0 ≤ p_t < n and -100000 ≤ x_t ≤ 100000. Additionally, nums[i] ≤ 0 for every i with 0 ≤ i < n, and x_t ≤ 0 for every t with 0 ≤ t < q. -/
theorem spec_6
    (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries)
    (hnums : ∀ v ∈ nums.val, v.val ≤ 0)
    (hqueries : ∀ v ∈ queries.val, qVal v ≤ 0) :
    ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r ∧
      r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries)
    (hnums : ∀ v ∈ nums.val, v.val ≤ 0)
    (hqueries : ∀ v ∈ queries.val, qVal v ≤ 0), ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r ∧
      r.val = 0) := by
  sorry

/-- Let G(nums) be the maximum sum of all subsets of indices of nums with no two consecutive indices selected, with the empty subset allowed. Then the function returns r = (q * G(nums)) mod 1000000007.
  Preconditions: Let n = len(nums) and q = len(queries). 1 ≤ n ≤ 50000, 1 ≤ q ≤ 50000. For every i with 0 ≤ i < n, -100000 ≤ nums[i] ≤ 100000. Each queries[t] has length 2; writing p_t = queries[t][0] and x_t = queries[t][1], we have 0 ≤ p_t < n and -100000 ≤ x_t ≤ 100000. Let A_0 = nums and A_{t+1} be A_t with coordinate p_t replaced by x_t. Additionally, for every t with 0 ≤ t < q, x_t = A_t[p_t], so each query writes the value already present at its position. -/
theorem spec_7
    (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries)
    (hwrites : WritesCurrent (numsInts nums) (queryPairs queries)) :
    ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r ∧
      r.val = ((queries.val.length : ℤ) * G (numsInts nums)) % 1000000007 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries)
    (hwrites : WritesCurrent (numsInts nums) (queryPairs queries)), ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r ∧
      r.val = ((queries.val.length : ℤ) * G (numsInts nums)) % 1000000007) := by
  sorry

/-- For each t, let B_t be the array equal to nums except that B_t[p] = x_t. Let G be the maximum non-adjacent subsequence sum, with the empty subset allowed. Then the function returns r = (∑_{t=0}^{q-1} G(B_t)) mod 1000000007.
  Preconditions: Let n = len(nums) and q = len(queries). 1 ≤ n ≤ 50000, 1 ≤ q ≤ 50000. For every i with 0 ≤ i < n, -100000 ≤ nums[i] ≤ 100000. Each queries[t] has length 2; writing p_t = queries[t][0] and x_t = queries[t][1], we have 0 ≤ p_t < n and -100000 ≤ x_t ≤ 100000. Additionally, there exists p with 0 ≤ p < n such that p_t = p for every t with 0 ≤ t < q. -/
theorem spec_8
    (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries)
    (p : ℕ) (hp : p < nums.val.length)
    (hall : ∀ u ∈ queryPairs queries, u.1 = p) :
    ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r ∧
      r.val = (queries.val.map (fun v => G ((numsInts nums).set p (qVal v)))).sum
        % 1000000007 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries)
    (p : ℕ) (hp : p < nums.val.length)
    (hall : ∀ u ∈ queryPairs queries, u.1 = p), ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r ∧
      r.val = (queries.val.map (fun v => G ((numsInts nums).set p (qVal v)))).sum
        % 1000000007) := by
  sorry

/-- If r is the result returned for (nums, queries) and r' is the result returned for (nums', queries), then r = r'.
  Preconditions: Let q = len(queries), let nums and nums' be two arrays with the same length n, where 1 ≤ n ≤ 50000 and 1 ≤ q ≤ 50000. Both inputs satisfy: all entries lie in [-100000,100000], each query has length 2, each query position is in [0,n), and each query value is in [-100000,100000]. Let p = queries[0][0]. Assume nums'[i] = nums[i] for every i with 0 ≤ i < n and i ≠ p; nums'[p] may differ from nums[p]. -/
theorem spec_9
    (nums nums' : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries) (hpre' : Pre nums' queries)
    (hlen : nums'.val.length = nums.val.length)
    (hagree : ∀ i, i < nums.val.length → i ≠ firstPos queries →
      (numsInts nums').getD i 0 = (numsInts nums).getD i 0) :
    ∀ r r',
      Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r →
      Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums' queries = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries) (hpre' : Pre nums' queries)
    (hlen : nums'.val.length = nums.val.length)
    (hagree : ∀ i, i < nums.val.length → i ≠ firstPos queries →
      (numsInts nums').getD i 0 = (numsInts nums).getD i 0), ∀ r r',
      Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r →
      Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums' queries = ok r' →
      r.val = r'.val) := by
  sorry

/-- Let A_0 = nums and A_{t+1} be A_t with coordinate p_t replaced by x_t for 0 ≤ t < q. Let B be A_q with coordinate p replaced by x. If r is the result for (nums, queries) and r' is the result for (nums, queries'), then r' = (r + G(B)) mod 1000000007, where G(B) is the maximum non-adjacent subsequence sum of B with the empty subset allowed.
  Preconditions: Let n = len(nums) and q = len(queries). 1 ≤ n ≤ 50000, 1 ≤ q ≤ 50000. For every i with 0 ≤ i < n, -100000 ≤ nums[i] ≤ 100000. Each queries[t] has length 2; writing p_t = queries[t][0] and x_t = queries[t][1], we have 0 ≤ p_t < n and -100000 ≤ x_t ≤ 100000. Let p be an integer with 0 ≤ p < n and let x be an integer with -100000 ≤ x ≤ 100000. Let queries' be queries with the additional final query [p,x]. -/
theorem spec_10
    (nums : Slice I64) (queries queries' : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries) (hpre' : Pre nums queries')
    (p : ℕ) (hp : p < nums.val.length)
    (x : ℤ) (hx_lo : -100000 ≤ x) (hx_hi : x ≤ 100000)
    (happend : queryPairs queries' = queryPairs queries ++ [(p, x)]) :
    ∀ r r',
      Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r →
      Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries' = ok r' →
      r'.val = (r.val + G ((finalState (numsInts nums) (queryPairs queries)).set p x))
        % 1000000007 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (queries queries' : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries) (hpre' : Pre nums queries')
    (p : ℕ) (hp : p < nums.val.length)
    (x : ℤ) (hx_lo : -100000 ≤ x) (hx_hi : x ≤ 100000)
    (happend : queryPairs queries' = queryPairs queries ++ [(p, x)]), ∀ r r',
      Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r →
      Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries' = ok r' →
      r'.val = (r.val + G ((finalState (numsInts nums) (queryPairs queries)).set p x))
        % 1000000007) := by
  sorry

/-- Let A_0 = nums and A_{t+1} be A_t with coordinate p_t replaced by x_t. For every t with 0 ≤ t < q, there exists a subset S_t ⊆ {0,...,n-1} with no i such that both i and i+1 are in S_t, satisfying: (1) G(A_{t+1}) = ∑_{i∈S_t} A_{t+1}[i], where G is the maximum non-adjacent subsequence sum with the empty subset allowed; and (2) for every subset S ⊆ {0,...,n-1} with no two consecutive indices, ∑_{i∈S} A_{t+1}[i] ≤ ∑_{i∈S_t} A_{t+1}[i]. If r is the returned result, then r ≡ ∑_{t=0}^{q-1} ∑_{i∈S_t} A_{t+1}[i] (mod 1000000007).
  Preconditions: Let n = len(nums) and q = len(queries). 1 ≤ n ≤ 50000, 1 ≤ q ≤ 50000. For every i with 0 ≤ i < n, -100000 ≤ nums[i] ≤ 100000. Each queries[t] has length 2; writing p_t = queries[t][0] and x_t = queries[t][1], we have 0 ≤ p_t < n and -100000 ≤ x_t ≤ 100000. -/
theorem spec_11
    (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries) :
    (∀ t, t < (queryPairs queries).length →
      ∃ S : Finset ℕ,
        IsMaxNonAdjacent
          (nthState (numsInts nums) (queryPairs queries) (t + 1)) S) ∧
    ∀ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r →
      ∃ S : ℕ → Finset ℕ,
        (∀ t, t < (queryPairs queries).length →
          IsMaxNonAdjacent
            (nthState (numsInts nums) (queryPairs queries) (t + 1)) (S t)) ∧
        r.val ≡
          ((List.range (queryPairs queries).length).map
            (fun t => sumOver
              (nthState (numsInts nums) (queryPairs queries) (t + 1)) (S t))).sum
          [ZMOD 1000000007] := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries), (∀ t, t < (queryPairs queries).length →
      ∃ S : Finset ℕ,
        IsMaxNonAdjacent
          (nthState (numsInts nums) (queryPairs queries) (t + 1)) S) ∧
    ∀ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r →
      ∃ S : ℕ → Finset ℕ,
        (∀ t, t < (queryPairs queries).length →
          IsMaxNonAdjacent
            (nthState (numsInts nums) (queryPairs queries) (t + 1)) (S t)) ∧
        r.val ≡
          ((List.range (queryPairs queries).length).map
            (fun t => sumOver
              (nthState (numsInts nums) (queryPairs queries) (t + 1)) (S t))).sum
          [ZMOD 1000000007]) := by
  sorry

/-- Let A_0 = nums and A_{t+1} be A_t with coordinate p_t replaced by x_t. For every t with 0 ≤ t < q, the maximum non-adjacent subsequence sum G(A_{t+1}), with the empty subset allowed, satisfies 0 ≤ G(A_{t+1}) ≤ 2500000000. Consequently, the non-modular total T = ∑_{t=0}^{q-1} G(A_{t+1}) satisfies 0 ≤ T ≤ 125000000000000, and the returned value r is the least nonnegative residue of T modulo 1000000007.
  Preconditions: Let n = len(nums) and q = len(queries). 1 ≤ n ≤ 50000, 1 ≤ q ≤ 50000. For every i with 0 ≤ i < n, -100000 ≤ nums[i] ≤ 100000. Each queries[t] has length 2; writing p_t = queries[t][0] and x_t = queries[t][1], we have 0 ≤ p_t < n and -100000 ≤ x_t ≤ 100000. -/
theorem spec_12
    (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries) :
    ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r ∧
      (∀ t, t < (queryPairs queries).length →
        0 ≤ G (nthState (numsInts nums) (queryPairs queries) (t + 1)) ∧
        G (nthState (numsInts nums) (queryPairs queries) (t + 1)) ≤ 2500000000) ∧
      0 ≤ totalG (numsInts nums) (queryPairs queries) ∧
      totalG (numsInts nums) (queryPairs queries) ≤ 125000000000000 ∧
      r.val = totalG (numsInts nums) (queryPairs queries) % 1000000007 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries), ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r ∧
      (∀ t, t < (queryPairs queries).length →
        0 ≤ G (nthState (numsInts nums) (queryPairs queries) (t + 1)) ∧
        G (nthState (numsInts nums) (queryPairs queries) (t + 1)) ≤ 2500000000) ∧
      0 ≤ totalG (numsInts nums) (queryPairs queries) ∧
      totalG (numsInts nums) (queryPairs queries) ≤ 125000000000000 ∧
      r.val = totalG (numsInts nums) (queryPairs queries) % 1000000007) := by
  sorry

/-- Let A_0 = nums and A_{t+1} be A_t with coordinate p_t replaced by x_t. For every t with 0 ≤ t < q, G(A_{t+1}) ≥ max(0, x_t), where G is the maximum non-adjacent subsequence sum with the empty subset allowed. Consequently, the non-modular total T = ∑_{t=0}^{q-1} G(A_{t+1}) satisfies T ≥ ∑_{t=0}^{q-1} max(0, x_t), and the returned value r is the least nonnegative residue of T modulo 1000000007.
  Preconditions: Let n = len(nums) and q = len(queries). 1 ≤ n ≤ 50000, 1 ≤ q ≤ 50000. For every i with 0 ≤ i < n, -100000 ≤ nums[i] ≤ 100000. Each queries[t] has length 2; writing p_t = queries[t][0] and x_t = queries[t][1], we have 0 ≤ p_t < n and -100000 ≤ x_t ≤ 100000. -/
theorem spec_13
    (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries) :
    ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r ∧
      (∀ t, t < (queryPairs queries).length →
        max 0 ((queryPairs queries).getD t (0, 0)).2 ≤
          G (nthState (numsInts nums) (queryPairs queries) (t + 1))) ∧
      (queries.val.map (fun v => max 0 (qVal v))).sum ≤
        totalG (numsInts nums) (queryPairs queries) ∧
      r.val = totalG (numsInts nums) (queryPairs queries) % 1000000007 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hpre : Pre nums queries), ∃ r, Aegis.MaximumSumSubsequence.maximum_sum_subsequence nums queries = ok r ∧
      (∀ t, t < (queryPairs queries).length →
        max 0 ((queryPairs queries).getD t (0, 0)).2 ≤
          G (nthState (numsInts nums) (queryPairs queries) (t + 1))) ∧
      (queries.val.map (fun v => max 0 (qVal v))).sum ≤
        totalG (numsInts nums) (queryPairs queries) ∧
      r.val = totalG (numsInts nums) (queryPairs queries) % 1000000007) := by
  sorry

end AegisSpec.MaximumSumSubsequence
