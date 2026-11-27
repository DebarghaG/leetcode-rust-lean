import Aegis.MaximumSubarrayXor.Code.Funs

/-!
# Specifications of `Aegis.MaximumSubarrayXor.maximum_subarray_xor`

LeetCode problem `maximum-xor-score-subarray-queries`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumSubarrayXor

  def xorZ (a b : ℤ) : ℤ := (a.toNat ^^^ b.toNat : ℕ)

  def bitSet (z : ℤ) (b : ℕ) : Prop := z.toNat.testBit b = true

  def intsOfSlice (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def intsOfVec (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map (fun x => x.val)

  def queryEntries (queries : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    queries.val.map (fun v => intsOfVec v)

  def queryEntry (queries : Slice (alloc.vec.Vec Std.I64)) (j : ℕ) : List ℤ :=
    (queryEntries queries).getD j []

  def queryLo (queries : Slice (alloc.vec.Vec Std.I64)) (j : ℕ) : ℤ :=
    (queryEntry queries j).getD 0 0

  def queryHi (queries : Slice (alloc.vec.Vec Std.I64)) (j : ℕ) : ℤ :=
    (queryEntry queries j).getD 1 0

  def ansAt (ans : alloc.vec.Vec Std.I64) (j : ℕ) : ℤ := (intsOfVec ans).getD j 0

  def ilget (a : List ℤ) (i : ℤ) : ℤ := a.getD i.toNat 0

  def xorStep (l : List ℤ) : List ℤ :=
    (l.zip (l.drop 1)).map (fun p => xorZ p.1 p.2)

  def xorReduceAux : ℕ → List ℤ → ℤ
    | 0, _ => 0
    | _ + 1, [] => 0
    | _ + 1, [x] => x
    | k + 1, l => xorReduceAux k (xorStep l)

  def xorReduce (l : List ℤ) : ℤ := xorReduceAux l.length l

  def xorScore (a : List ℤ) (s t : ℕ) : ℤ := xorReduce ((a.drop s).take (t + 1 - s))

  def xorScoreBinom (a : List ℤ) (s t : ℕ) : ℤ :=
    ((List.range (t + 1 - s)).filter (fun k => Nat.choose (t - s) k % 2 = 1)).foldr
      (fun k acc => xorZ (a.getD (s + k) 0) acc) 0

  def listMax : List ℤ → ℤ
    | [] => 0
    | x :: xs => xs.foldr max x

  def subarrayScores (a : List ℤ) (l r : ℕ) : List ℤ :=
    (List.range (r + 1 - l)).flatMap (fun i =>
      (List.range (r + 1 - l - i)).map (fun k => xorScore a (l + i) (l + i + k)))

  def intervalMax (a : List ℤ) (l r : ℕ) : ℤ := listMax (subarrayScores a l r)

  def izIntervalMax (a : List ℤ) (l r : ℤ) : ℤ := intervalMax a l.toNat r.toNat

  def intervalValues (a : List ℤ) (l r : ℕ) : List ℤ :=
    (List.range (r + 1 - l)).map (fun k => a.getD (l + k) 0)

  def intervalValueMax (a : List ℤ) (l r : ℕ) : ℤ := listMax (intervalValues a l r)

  def izIntervalValueMax (a : List ℤ) (l r : ℤ) : ℤ :=
    intervalValueMax a l.toNat r.toNat

  def ValidNums (nums : Slice Std.I64) : Prop :=
    1 ≤ nums.val.length ∧ nums.val.length ≤ 2000 ∧
      ∀ i, i < nums.val.length →
        0 ≤ ilget (intsOfSlice nums) (i : ℤ) ∧ ilget (intsOfSlice nums) (i : ℤ) < 2 ^ 63

  def ValidQueries (nums : Slice Std.I64)
      (queries : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    1 ≤ queries.val.length ∧ queries.val.length ≤ 100000 ∧
      ∀ j, j < queries.val.length →
        (queryEntry queries j).length = 2 ∧
        0 ≤ queryLo queries j ∧ queryLo queries j ≤ queryHi queries j ∧
        queryHi queries j < (nums.val.length : ℤ)

  def ValidInput (nums : Slice Std.I64)
      (queries : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ValidNums nums ∧ ValidQueries nums queries

  def IsPerm (pi : ℕ → ℕ) (q : ℕ) : Prop :=
    (∀ j, j < q → pi j < q) ∧ (∀ i j, i < q → j < q → pi i = pi j → i = j)

  /-- Whenever the function returns a result ans, len(ans) = q and for every j with 0 <= j < q, letting l_j = queries[j][0] and r_j = queries[j][1], ans[j] = max { X(s,t) | l_j <= s <= t <= r_j }, where X(s,t) is the final single value obtained from nums[s..t] by repeatedly replacing a sequence b[0..m-1] with (b[0] XOR b[1], ..., b[m-2] XOR b[m-1]) while m > 1. Equivalently, X(s,t) is the XOR of nums[s+k] over all k in 0..t-s for which the binomial coefficient C(t-s,k) is odd.
    Preconditions: Let n = len(nums) and q = len(queries). Assume n >= 1, q >= 1, n <= 2000, q <= 100000, every nums[i] with 0 <= i < n is a nonnegative 64-bit integer, and for every j with 0 <= j < q, len(queries[j]) = 2 with 0 <= queries[j][0] <= queries[j][1] < n. -/
  theorem spec_1 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans) :
      ans.val.length = queries.val.length ∧
        ∀ j, j < queries.val.length →
          ansAt ans j = izIntervalMax (intsOfSlice nums) (queryLo queries j)
            (queryHi queries j) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans), ans.val.length = queries.val.length ∧
          ∀ j, j < queries.val.length →
            ansAt ans j = izIntervalMax (intsOfSlice nums) (queryLo queries j)
              (queryHi queries j)) := by
    sorry

  /-- For every nums and queries satisfying the preconditions, the function returns a result ans; it does not fail because of arithmetic overflow, out-of-bounds indexing, or a panic.
    Preconditions: Let n = len(nums) and q = len(queries). Assume n >= 1, q >= 1, n <= 2000, q <= 100000, every nums[i] with 0 <= i < n is a nonnegative 64-bit integer, and for every j with 0 <= j < q, len(queries[j]) = 2 with 0 <= queries[j][0] <= queries[j][1] < n. -/
  theorem spec_2 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput nums queries) :
      ∃ ans, Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput nums queries), ∃ ans, Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans) := by
    sorry

  /-- Whenever the function returns ans, len(ans) = len(queries), and the entries are indexed 0..q-1 in the same order as queries, so ans[j] is the answer corresponding to queries[j].
    Preconditions: Let n = len(nums) and q = len(queries). Assume n >= 1, q >= 1, n <= 2000, q <= 100000, every nums[i] with 0 <= i < n is a nonnegative 64-bit integer, and for every j with 0 <= j < q, len(queries[j]) = 2 with 0 <= queries[j][0] <= queries[j][1] < n. -/
  theorem spec_3 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans) :
      ans.val.length = queries.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans), ans.val.length = queries.val.length) := by
    sorry

  /-- Whenever the function returns ans, for every j with 0 <= j < q, ans[j] >= 0.
    Preconditions: Let n = len(nums) and q = len(queries). Assume n >= 1, q >= 1, n <= 2000, q <= 100000, every nums[i] with 0 <= i < n is a nonnegative 64-bit integer, and for every j with 0 <= j < q, len(queries[j]) = 2 with 0 <= queries[j][0] <= queries[j][1] < n. -/
  theorem spec_4 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans) :
      ∀ j, j < queries.val.length → 0 ≤ ansAt ans j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans), ∀ j, j < queries.val.length → 0 ≤ ansAt ans j) := by
    sorry

  /-- Whenever the function returns ans, for every j with 0 <= j < q and every bit position b with 0 <= b < 63, if bit b of ans[j] is 1, then there exists an index t with queries[j][0] <= t <= queries[j][1] such that bit b of nums[t] is 1. Equivalently, ans[j] is a bitwise submask of the bitwise OR of nums[queries[j][0]], ..., nums[queries[j][1]].
    Preconditions: Let n = len(nums) and q = len(queries). Assume n >= 1, q >= 1, n <= 2000, q <= 100000, every nums[i] with 0 <= i < n is a nonnegative 64-bit integer, and for every j with 0 <= j < q, len(queries[j]) = 2 with 0 <= queries[j][0] <= queries[j][1] < n. -/
  theorem spec_5 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans) :
      ∀ j, j < queries.val.length → ∀ b : ℕ, b < 63 →
        bitSet (ansAt ans j) b →
          ∃ t : ℤ, queryLo queries j ≤ t ∧ t ≤ queryHi queries j ∧
            bitSet (ilget (intsOfSlice nums) t) b := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans), ∀ j, j < queries.val.length → ∀ b : ℕ, b < 63 →
          bitSet (ansAt ans j) b →
            ∃ t : ℤ, queryLo queries j ≤ t ∧ t ≤ queryHi queries j ∧
              bitSet (ilget (intsOfSlice nums) t) b) := by
    sorry

  /-- Whenever the function returns ans, for every j with 0 <= j < q, ans[j] >= max { nums[t] | queries[j][0] <= t <= queries[j][1] }.
    Preconditions: Let n = len(nums) and q = len(queries). Assume n >= 1, q >= 1, n <= 2000, q <= 100000, every nums[i] with 0 <= i < n is a nonnegative 64-bit integer, and for every j with 0 <= j < q, len(queries[j]) = 2 with 0 <= queries[j][0] <= queries[j][1] < n. -/
  theorem spec_6 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans) :
      ∀ j, j < queries.val.length →
        izIntervalValueMax (intsOfSlice nums) (queryLo queries j) (queryHi queries j) ≤
          ansAt ans j := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans), ∀ j, j < queries.val.length →
          izIntervalValueMax (intsOfSlice nums) (queryLo queries j) (queryHi queries j) ≤
            ansAt ans j) := by
    sorry

  /-- Whenever the function returns ans, for every j with 0 <= j < q and every t with queries[j][0] <= t < queries[j][1], ans[j] >= (nums[t] XOR nums[t+1]).
    Preconditions: Let n = len(nums) and q = len(queries). Assume n >= 1, q >= 1, n <= 2000, q <= 100000, every nums[i] with 0 <= i < n is a nonnegative 64-bit integer, and for every j with 0 <= j < q, len(queries[j]) = 2 with 0 <= queries[j][0] <= queries[j][1] < n. -/
  theorem spec_7 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans) :
      ∀ j, j < queries.val.length → ∀ t : ℤ,
        queryLo queries j ≤ t → t < queryHi queries j →
          xorZ (ilget (intsOfSlice nums) t) (ilget (intsOfSlice nums) (t + 1)) ≤
            ansAt ans j := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans), ∀ j, j < queries.val.length → ∀ t : ℤ,
          queryLo queries j ≤ t → t < queryHi queries j →
            xorZ (ilget (intsOfSlice nums) t) (ilget (intsOfSlice nums) (t + 1)) ≤
              ansAt ans j) := by
    sorry

  /-- Whenever the function returns ans, for every j with 0 <= j < q, ans[j] is at least the XOR score of the entire queried interval nums[queries[j][0]..queries[j][1]], where the XOR score is defined by the repeated simultaneous XOR-and-remove-last operation.
    Preconditions: Let n = len(nums) and q = len(queries). Assume n >= 1, q >= 1, n <= 2000, q <= 100000, every nums[i] with 0 <= i < n is a nonnegative 64-bit integer, and for every j with 0 <= j < q, len(queries[j]) = 2 with 0 <= queries[j][0] <= queries[j][1] < n. -/
  theorem spec_8 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans) :
      ∀ j, j < queries.val.length →
        xorScore (intsOfSlice nums) (queryLo queries j).toNat (queryHi queries j).toNat ≤
          ansAt ans j := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans), ∀ j, j < queries.val.length →
          xorScore (intsOfSlice nums) (queryLo queries j).toNat (queryHi queries j).toNat ≤
            ansAt ans j) := by
    sorry

  /-- Whenever the function returns ans, for every j with 0 <= j < q there exist indices s,t with queries[j][0] <= s <= t <= queries[j][1] such that the XOR score of nums[s..t] equals ans[j].
    Preconditions: Let n = len(nums) and q = len(queries). Assume n >= 1, q >= 1, n <= 2000, q <= 100000, every nums[i] with 0 <= i < n is a nonnegative 64-bit integer, and for every j with 0 <= j < q, len(queries[j]) = 2 with 0 <= queries[j][0] <= queries[j][1] < n. -/
  theorem spec_9 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans) :
      ∀ j, j < queries.val.length →
        ∃ s t : ℕ, (queryLo queries j).toNat ≤ s ∧ s ≤ t ∧
          t ≤ (queryHi queries j).toNat ∧ xorScore (intsOfSlice nums) s t = ansAt ans j := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans), ∀ j, j < queries.val.length →
          ∃ s t : ℕ, (queryLo queries j).toNat ≤ s ∧ s ≤ t ∧
            t ≤ (queryHi queries j).toNat ∧ xorScore (intsOfSlice nums) s t = ansAt ans j) := by
    sorry

  /-- Whenever the function returns ans, for every j with 0 <= j < q, if queries[j][0] = queries[j][1], then ans[j] = nums[queries[j][0]].
    Preconditions: Let n = len(nums) and q = len(queries). Assume n >= 1, q >= 1, n <= 2000, q <= 100000, every nums[i] with 0 <= i < n is a nonnegative 64-bit integer, and for every j with 0 <= j < q, len(queries[j]) = 2 with 0 <= queries[j][0] <= queries[j][1] < n. -/
  theorem spec_10 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans) :
      ∀ j, j < queries.val.length → queryLo queries j = queryHi queries j →
        ansAt ans j = ilget (intsOfSlice nums) (queryLo queries j) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans), ∀ j, j < queries.val.length → queryLo queries j = queryHi queries j →
          ansAt ans j = ilget (intsOfSlice nums) (queryLo queries j)) := by
    sorry

  /-- Whenever the function returns ans, for every i,j with 0 <= i < q and 0 <= j < q, if queries[j][0] <= queries[i][0] <= queries[i][1] <= queries[j][1], then ans[i] <= ans[j].
    Preconditions: Let n = len(nums) and q = len(queries). Assume n >= 1, q >= 1, n <= 2000, q <= 100000, every nums[i] with 0 <= i < n is a nonnegative 64-bit integer, and for every j with 0 <= j < q, len(queries[j]) = 2 with 0 <= queries[j][0] <= queries[j][1] < n. -/
  theorem spec_11 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans) :
      ∀ i j, i < queries.val.length → j < queries.val.length →
        queryLo queries j ≤ queryLo queries i → queryHi queries i ≤ queryHi queries j →
          ansAt ans i ≤ ansAt ans j := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans), ∀ i j, i < queries.val.length → j < queries.val.length →
          queryLo queries j ≤ queryLo queries i → queryHi queries i ≤ queryHi queries j →
            ansAt ans i ≤ ansAt ans j) := by
    sorry

  /-- Whenever the function returns ans for (nums, queries) and returns ans' for (nums, queries'), then for every index j that is valid for both lists, if queries[j] = queries'[j] (same two endpoints), then ans[j] = ans'[j].
    Preconditions: Let n = len(nums). Assume n >= 1, n <= 2000 and every nums[i] with 0 <= i < n is a nonnegative 64-bit integer. Let queries and queries' be two query lists, each of length at least 1 and at most 100000, such that for every entry [l,r] in either list, len([l,r]) = 2 and 0 <= l <= r < n. -/
  theorem spec_12 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (queries' : Slice (alloc.vec.Vec Std.I64))
      (hn : ValidNums nums) (hq : ValidQueries nums queries)
      (hq' : ValidQueries nums queries') (ans ans' : alloc.vec.Vec Std.I64)
      (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans)
      (hans' : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries' = ok ans') :
      ∀ j, j < queries.val.length → j < queries'.val.length →
        queryLo queries j = queryLo queries' j → queryHi queries j = queryHi queries' j →
          ansAt ans j = ansAt ans' j := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (queries' : Slice (alloc.vec.Vec Std.I64))
        (hn : ValidNums nums) (hq : ValidQueries nums queries)
        (hq' : ValidQueries nums queries') (ans ans' : alloc.vec.Vec Std.I64)
        (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans)
        (hans' : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries' = ok ans'), ∀ j, j < queries.val.length → j < queries'.val.length →
          queryLo queries j = queryLo queries' j → queryHi queries j = queryHi queries' j →
            ansAt ans j = ansAt ans' j) := by
    sorry

  /-- Whenever the function returns ans for (nums, queries) and returns ans' for (nums, queries'), for every j with 0 <= j < q, ans'[pi(j)] = ans[j].
    Preconditions: Let n = len(nums) and q = len(queries). Assume n >= 1, q >= 1, n <= 2000, q <= 100000, every nums[i] with 0 <= i < n is a nonnegative 64-bit integer, and every query is a valid pair 0 <= l <= r < n. Let pi be a permutation of {0,...,q-1}, and let queries' be the valid query list of length q with queries'[pi(j)] = queries[j] for all 0 <= j < q. -/
  theorem spec_13 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (queries' : Slice (alloc.vec.Vec Std.I64)) (pi : ℕ → ℕ)
      (hn : ValidNums nums) (hq : ValidQueries nums queries)
      (hq' : ValidQueries nums queries') (hpi : IsPerm pi queries.val.length)
      (hlen : queries'.val.length = queries.val.length)
      (hperm : ∀ j, j < queries.val.length →
        queryLo queries' (pi j) = queryLo queries j ∧
          queryHi queries' (pi j) = queryHi queries j)
      (ans ans' : alloc.vec.Vec Std.I64)
      (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans)
      (hans' : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries' = ok ans') :
      ∀ j, j < queries.val.length → ansAt ans' (pi j) = ansAt ans j := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (queries' : Slice (alloc.vec.Vec Std.I64)) (pi : ℕ → ℕ)
        (hn : ValidNums nums) (hq : ValidQueries nums queries)
        (hq' : ValidQueries nums queries') (hpi : IsPerm pi queries.val.length)
        (hlen : queries'.val.length = queries.val.length)
        (hperm : ∀ j, j < queries.val.length →
          queryLo queries' (pi j) = queryLo queries j ∧
            queryHi queries' (pi j) = queryHi queries j)
        (ans ans' : alloc.vec.Vec Std.I64)
        (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans)
        (hans' : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries' = ok ans'), ∀ j, j < queries.val.length → ansAt ans' (pi j) = ansAt ans j) := by
    sorry

  /-- Whenever the function returns ans, for every j with 0 <= j < q, if there is an integer x such that nums[t] = x for every t with queries[j][0] <= t <= queries[j][1], then ans[j] = x.
    Preconditions: Let n = len(nums) and q = len(queries). Assume n >= 1, q >= 1, n <= 2000, q <= 100000, every nums[i] with 0 <= i < n is a nonnegative 64-bit integer, and for every j with 0 <= j < q, len(queries[j]) = 2 with 0 <= queries[j][0] <= queries[j][1] < n. -/
  theorem spec_14 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans) :
      ∀ j, j < queries.val.length → ∀ x : ℤ,
        (∀ t : ℤ, queryLo queries j ≤ t → t ≤ queryHi queries j →
          ilget (intsOfSlice nums) t = x) →
          ansAt ans j = x := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans), ∀ j, j < queries.val.length → ∀ x : ℤ,
          (∀ t : ℤ, queryLo queries j ≤ t → t ≤ queryHi queries j →
            ilget (intsOfSlice nums) t = x) →
            ansAt ans j = x) := by
    sorry

  /-- Whenever the function returns ans, for every j with 0 <= j < q, if queries[j][1] = queries[j][0] + 1, then ans[j] = max(nums[queries[j][0]], nums[queries[j][1]], nums[queries[j][0]] XOR nums[queries[j][1]]).
    Preconditions: Let n = len(nums) and q = len(queries). Assume n >= 1, q >= 1, n <= 2000, q <= 100000, every nums[i] with 0 <= i < n is a nonnegative 64-bit integer, and for every j with 0 <= j < q, len(queries[j]) = 2 with 0 <= queries[j][0] <= queries[j][1] < n. -/
  theorem spec_15 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
      (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans) :
      ∀ j, j < queries.val.length → queryHi queries j = queryLo queries j + 1 →
        ansAt ans j =
          max (max (ilget (intsOfSlice nums) (queryLo queries j))
                (ilget (intsOfSlice nums) (queryHi queries j)))
            (xorZ (ilget (intsOfSlice nums) (queryLo queries j))
              (ilget (intsOfSlice nums) (queryHi queries j))) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
        (hans : Aegis.MaximumSubarrayXor.maximum_subarray_xor nums queries = ok ans), ∀ j, j < queries.val.length → queryHi queries j = queryLo queries j + 1 →
          ansAt ans j =
            max (max (ilget (intsOfSlice nums) (queryLo queries j))
                  (ilget (intsOfSlice nums) (queryHi queries j)))
              (xorZ (ilget (intsOfSlice nums) (queryLo queries j))
                (ilget (intsOfSlice nums) (queryHi queries j)))) := by
    sorry

  end AegisSpec.MaximumSubarrayXor
