import Aegis.AnswerQueries.Code.Funs

/-!
# Specifications of `Aegis.AnswerQueries.answer_queries`

LeetCode problem `longest-subsequence-with-limited-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.AnswerQueries

  namespace AegisSpec.AnswerQueries

  def valList (l : List I64) : List Int := l.map (fun x => x.val)

  def IsSortedVersion (a l : List Int) : Prop :=
    a.length = l.length ∧ a.Perm l ∧ a.Pairwise (fun x y => x ≤ y)

  def prefixSum (a : List Int) (k : Nat) : Int := (a.take k).sum

  def IsMaxPrefix (a : List Int) (n : Nat) (q : Int) (k : Int) : Prop :=
    0 ≤ k ∧ k ≤ (n : Int) ∧ prefixSum a k.toNat ≤ q ∧
      (∀ k' : Int, 0 ≤ k' → k' ≤ (n : Int) → prefixSum a k'.toNat ≤ q → k' ≤ k)

  def IsMinOf (l : List Int) (mu : Int) : Prop :=
    (∀ x ∈ l, mu ≤ x) ∧ (∃ x ∈ l, x = mu)

  def floorDiv (a b : Int) : Int := a / b

  /-- Let a be the nondecreasing sorted version of nums, so len(a)=n and a is a permutation of nums. The function returns a result r with len(r)=m, and for every i with 0 <= i < m, r[i] is the largest integer k satisfying 0 <= k <= n and sum_{t=0}^{k-1} a[t] <= queries[i], where the empty sum for k=0 is 0. Equivalently, r[i] is the maximum possible size of a subsequence of nums whose sum is at most queries[i].
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 1000, 1 <= m <= 1000, and 1 <= nums[j] <= 1000000 for every 0 <= j < n, and 1 <= queries[i] <= 1000000 for every 0 <= i < m. -/
  theorem spec_1
      (nums queries : Slice I64) (a : List Int)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (ha : IsSortedVersion a (valList nums.val)) :
      ∃ r : alloc.vec.Vec I64,
        answer_queries nums queries = ok r ∧
        r.val.length = queries.val.length ∧
        ∀ (i : Nat) (hi : i < queries.val.length) (hi' : i < r.val.length),
          IsMaxPrefix a nums.val.length (queries.val[i]'hi).val (r.val[i]'hi').val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums queries : Slice I64) (a : List Int)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (ha : IsSortedVersion a (valList nums.val)), ∃ r : alloc.vec.Vec I64,
          answer_queries nums queries = ok r ∧
          r.val.length = queries.val.length ∧
          ∀ (i : Nat) (hi : i < queries.val.length) (hi' : i < r.val.length),
            IsMaxPrefix a nums.val.length (queries.val[i]'hi).val (r.val[i]'hi').val) := by
    sorry

  /-- Whenever the function returns a result r, the length of r is m: len(r) = len(queries).
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 1000, 1 <= m <= 1000, and 1 <= nums[j] <= 1000000 for every 0 <= j < n, and 1 <= queries[i] <= 1000000 for every 0 <= i < m. -/
  theorem spec_2
      (nums queries : Slice I64) (r : alloc.vec.Vec I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hr : answer_queries nums queries = ok r) :
      r.val.length = queries.val.length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums queries : Slice I64) (r : alloc.vec.Vec I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hr : answer_queries nums queries = ok r), r.val.length = queries.val.length) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = m, for every i with 0 <= i < m we have 0 <= r[i] <= len(nums).
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 1000, 1 <= m <= 1000, and 1 <= nums[j] <= 1000000 for every 0 <= j < n, and 1 <= queries[i] <= 1000000 for every 0 <= i < m. -/
  theorem spec_3
      (nums queries : Slice I64) (r : alloc.vec.Vec I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hr : answer_queries nums queries = ok r)
      (hlen : r.val.length = queries.val.length) :
      ∀ (i : Nat) (hi : i < queries.val.length),
        0 ≤ (r.val[i]'(Nat.lt_of_lt_of_eq hi hlen.symm)).val ∧
          (r.val[i]'(Nat.lt_of_lt_of_eq hi hlen.symm)).val ≤ (nums.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums queries : Slice I64) (r : alloc.vec.Vec I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hr : answer_queries nums queries = ok r)
        (hlen : r.val.length = queries.val.length), ∀ (i : Nat) (hi : i < queries.val.length),
          0 ≤ (r.val[i]'(Nat.lt_of_lt_of_eq hi hlen.symm)).val ∧
            (r.val[i]'(Nat.lt_of_lt_of_eq hi hlen.symm)).val ≤ (nums.val.length : Int)) := by
    sorry

  /-- The function returns a result r; in particular, it does not fail, panic, or overflow on any input satisfying the preconditions.
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 1000, 1 <= m <= 1000, and 1 <= nums[j] <= 1000000 for every 0 <= j < n, and 1 <= queries[i] <= 1000000 for every 0 <= i < m. -/
  theorem spec_4
      (nums queries : Slice I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000) :
      ∃ r : alloc.vec.Vec I64, answer_queries nums queries = ok r := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums queries : Slice I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000), ∃ r : alloc.vec.Vec I64, answer_queries nums queries = ok r) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = m, let a be the nondecreasing sorted version of nums, so len(a) = n and a is a permutation of nums. For every i with 0 <= i < m and every integer k with 0 <= k <= n, if r[i] = k then sum_{t=0}^{k-1} a[t] <= queries[i], where the empty sum for k = 0 is 0.
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 1000, 1 <= m <= 1000, and 1 <= nums[j] <= 1000000 for every 0 <= j < n, and 1 <= queries[i] <= 1000000 for every 0 <= i < m. -/
  theorem spec_5
      (nums queries : Slice I64) (a : List Int) (r : alloc.vec.Vec I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (ha : IsSortedVersion a (valList nums.val))
      (hr : answer_queries nums queries = ok r)
      (hlen : r.val.length = queries.val.length) :
      ∀ (i : Nat) (hi : i < queries.val.length) (hi' : i < r.val.length) (k : Int),
        0 ≤ k → k ≤ (nums.val.length : Int) → (r.val[i]'hi').val = k →
          prefixSum a k.toNat ≤ (queries.val[i]'hi).val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums queries : Slice I64) (a : List Int) (r : alloc.vec.Vec I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (ha : IsSortedVersion a (valList nums.val))
        (hr : answer_queries nums queries = ok r)
        (hlen : r.val.length = queries.val.length), ∀ (i : Nat) (hi : i < queries.val.length) (hi' : i < r.val.length) (k : Int),
          0 ≤ k → k ≤ (nums.val.length : Int) → (r.val[i]'hi').val = k →
            prefixSum a k.toNat ≤ (queries.val[i]'hi).val) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = m, let a be the nondecreasing sorted version of nums. For every i with 0 <= i < m and every integer k with 0 <= k < n, if r[i] = k then sum_{t=0}^{k} a[t] > queries[i].
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 1000, 1 <= m <= 1000, and 1 <= nums[j] <= 1000000 for every 0 <= j < n, and 1 <= queries[i] <= 1000000 for every 0 <= i < m. -/
  theorem spec_6
      (nums queries : Slice I64) (a : List Int) (r : alloc.vec.Vec I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (ha : IsSortedVersion a (valList nums.val))
      (hr : answer_queries nums queries = ok r)
      (hlen : r.val.length = queries.val.length) :
      ∀ (i : Nat) (hi : i < queries.val.length) (hi' : i < r.val.length) (k : Int),
        0 ≤ k → k < (nums.val.length : Int) → (r.val[i]'hi').val = k →
          (queries.val[i]'hi).val < prefixSum a (k.toNat + 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums queries : Slice I64) (a : List Int) (r : alloc.vec.Vec I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (ha : IsSortedVersion a (valList nums.val))
        (hr : answer_queries nums queries = ok r)
        (hlen : r.val.length = queries.val.length), ∀ (i : Nat) (hi : i < queries.val.length) (hi' : i < r.val.length) (k : Int),
          0 ≤ k → k < (nums.val.length : Int) → (r.val[i]'hi').val = k →
            (queries.val[i]'hi).val < prefixSum a (k.toNat + 1)) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = m, for every i with 0 <= i < m we have r[i] = 0 if and only if queries[i] < min_{0 <= j < n} nums[j].
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 1000, 1 <= m <= 1000, and 1 <= nums[j] <= 1000000 for every 0 <= j < n, and 1 <= queries[i] <= 1000000 for every 0 <= i < m. -/
  theorem spec_7
      (nums queries : Slice I64) (r : alloc.vec.Vec I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hr : answer_queries nums queries = ok r)
      (hlen : r.val.length = queries.val.length) :
      ∀ (i : Nat) (hi : i < queries.val.length) (hi' : i < r.val.length) (mu : Int),
        IsMinOf (valList nums.val) mu →
          ((r.val[i]'hi').val = 0 ↔ (queries.val[i]'hi).val < mu) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums queries : Slice I64) (r : alloc.vec.Vec I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hr : answer_queries nums queries = ok r)
        (hlen : r.val.length = queries.val.length), ∀ (i : Nat) (hi : i < queries.val.length) (hi' : i < r.val.length) (mu : Int),
          IsMinOf (valList nums.val) mu →
            ((r.val[i]'hi').val = 0 ↔ (queries.val[i]'hi).val < mu)) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = m, for every i with 0 <= i < m we have r[i] = len(nums) if and only if sum_{j=0}^{n-1} nums[j] <= queries[i].
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 1000, 1 <= m <= 1000, and 1 <= nums[j] <= 1000000 for every 0 <= j < n, and 1 <= queries[i] <= 1000000 for every 0 <= i < m. -/
  theorem spec_8
      (nums queries : Slice I64) (r : alloc.vec.Vec I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hr : answer_queries nums queries = ok r)
      (hlen : r.val.length = queries.val.length) :
      ∀ (i : Nat) (hi : i < queries.val.length) (hi' : i < r.val.length),
        ((r.val[i]'hi').val = (nums.val.length : Int) ↔
          (valList nums.val).sum ≤ (queries.val[i]'hi).val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums queries : Slice I64) (r : alloc.vec.Vec I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hr : answer_queries nums queries = ok r)
        (hlen : r.val.length = queries.val.length), ∀ (i : Nat) (hi : i < queries.val.length) (hi' : i < r.val.length),
          ((r.val[i]'hi').val = (nums.val.length : Int) ↔
            (valList nums.val).sum ≤ (queries.val[i]'hi).val)) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = m, for all i and j with 0 <= i < m and 0 <= j < m, if queries[i] <= queries[j] then r[i] <= r[j].
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 1000, 1 <= m <= 1000, and 1 <= nums[j] <= 1000000 for every 0 <= j < n, and 1 <= queries[i] <= 1000000 for every 0 <= i < m. -/
  theorem spec_9
      (nums queries : Slice I64) (r : alloc.vec.Vec I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hr : answer_queries nums queries = ok r)
      (hlen : r.val.length = queries.val.length) :
      ∀ (i j : Nat) (hi : i < queries.val.length) (hj : j < queries.val.length)
        (hi' : i < r.val.length) (hj' : j < r.val.length),
        (queries.val[i]'hi).val ≤ (queries.val[j]'hj).val →
          (r.val[i]'hi').val ≤ (r.val[j]'hj').val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums queries : Slice I64) (r : alloc.vec.Vec I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hr : answer_queries nums queries = ok r)
        (hlen : r.val.length = queries.val.length), ∀ (i j : Nat) (hi : i < queries.val.length) (hj : j < queries.val.length)
          (hi' : i < r.val.length) (hj' : j < r.val.length),
          (queries.val[i]'hi).val ≤ (queries.val[j]'hj).val →
            (r.val[i]'hi').val ≤ (r.val[j]'hj').val) := by
    sorry

  /-- For every list nums' of integers with len(nums') = n that is a permutation of nums, if the function returns r on (nums, queries) and returns r' on (nums', queries), then len(r) = len(r') = m and r'[i] = r[i] for every i with 0 <= i < m.
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 1000, 1 <= m <= 1000, and 1 <= nums[j] <= 1000000 for every 0 <= j < n, and 1 <= queries[i] <= 1000000 for every 0 <= i < m. -/
  theorem spec_10
      (nums nums' queries : Slice I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hperm : (valList nums'.val).Perm (valList nums.val))
      (r r' : alloc.vec.Vec I64)
      (hr : answer_queries nums queries = ok r)
      (hr' : answer_queries nums' queries = ok r') :
      r.val.length = queries.val.length ∧ r'.val.length = queries.val.length ∧
        ∀ (i : Nat) (hi : i < queries.val.length) (hi1 : i < r.val.length)
          (hi2 : i < r'.val.length),
          (r'.val[i]'hi2).val = (r.val[i]'hi1).val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' queries : Slice I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hperm : (valList nums'.val).Perm (valList nums.val))
        (r r' : alloc.vec.Vec I64)
        (hr : answer_queries nums queries = ok r)
        (hr' : answer_queries nums' queries = ok r'), r.val.length = queries.val.length ∧ r'.val.length = queries.val.length ∧
          ∀ (i : Nat) (hi : i < queries.val.length) (hi1 : i < r.val.length)
            (hi2 : i < r'.val.length),
            (r'.val[i]'hi2).val = (r.val[i]'hi1).val) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = m, for every i with 0 <= i < m, r[i] <= the number of indices j with 0 <= j < n and nums[j] <= queries[i].
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 1000, 1 <= m <= 1000, and 1 <= nums[j] <= 1000000 for every 0 <= j < n, and 1 <= queries[i] <= 1000000 for every 0 <= i < m. -/
  theorem spec_11
      (nums queries : Slice I64) (r : alloc.vec.Vec I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hr : answer_queries nums queries = ok r)
      (hlen : r.val.length = queries.val.length) :
      ∀ (i : Nat) (hi : i < queries.val.length) (hi' : i < r.val.length),
        (r.val[i]'hi').val ≤
          (((valList nums.val).filter (fun x => x ≤ (queries.val[i]'hi).val)).length : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums queries : Slice I64) (r : alloc.vec.Vec I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hr : answer_queries nums queries = ok r)
        (hlen : r.val.length = queries.val.length), ∀ (i : Nat) (hi : i < queries.val.length) (hi' : i < r.val.length),
          (r.val[i]'hi').val ≤
            (((valList nums.val).filter (fun x => x ≤ (queries.val[i]'hi).val)).length : Int)) := by
    sorry

  /-- Whenever the function returns a result r on (nums, queries) with len(r) = m, for every list queries' with len(queries') = m and 1 <= queries'[j] <= 1000000 for every 0 <= j < m, and for every i with 0 <= i < m, if queries'[i] = queries[i], then for any result r' returned by the function on (nums, queries'), r'[i] = r[i].
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 1000, 1 <= m <= 1000, and 1 <= nums[j] <= 1000000 for every 0 <= j < n, and 1 <= queries[i] <= 1000000 for every 0 <= i < m. -/
  theorem spec_12
      (nums queries : Slice I64) (r : alloc.vec.Vec I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hr : answer_queries nums queries = ok r)
      (hlen : r.val.length = queries.val.length) :
      ∀ (queries' : Slice I64) (hq'len : queries'.val.length = queries.val.length)
        (hq'bounds : ∀ x ∈ queries'.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (i : Nat) (hi : i < queries.val.length)
        (hqi : (queries'.val[i]'(Nat.lt_of_lt_of_eq hi hq'len.symm)).val =
          (queries.val[i]'hi).val)
        (r' : alloc.vec.Vec I64) (hr' : answer_queries nums queries' = ok r')
        (hr'len : r'.val.length = queries.val.length),
        (r'.val[i]'(Nat.lt_of_lt_of_eq hi hr'len.symm)).val =
          (r.val[i]'(Nat.lt_of_lt_of_eq hi hlen.symm)).val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums queries : Slice I64) (r : alloc.vec.Vec I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hr : answer_queries nums queries = ok r)
        (hlen : r.val.length = queries.val.length), ∀ (queries' : Slice I64) (hq'len : queries'.val.length = queries.val.length)
          (hq'bounds : ∀ x ∈ queries'.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
          (i : Nat) (hi : i < queries.val.length)
          (hqi : (queries'.val[i]'(Nat.lt_of_lt_of_eq hi hq'len.symm)).val =
            (queries.val[i]'hi).val)
          (r' : alloc.vec.Vec I64) (hr' : answer_queries nums queries' = ok r')
          (hr'len : r'.val.length = queries.val.length),
          (r'.val[i]'(Nat.lt_of_lt_of_eq hi hr'len.symm)).val =
            (r.val[i]'(Nat.lt_of_lt_of_eq hi hlen.symm)).val) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = m, let mu = min_{0 <= j < n} nums[j]. For every i with 0 <= i < m, r[i] <= floor(queries[i] / mu).
    Preconditions: Let n = len(nums) and m = len(queries). Assume 1 <= n <= 1000, 1 <= m <= 1000, and 1 <= nums[j] <= 1000000 for every 0 <= j < n, and 1 <= queries[i] <= 1000000 for every 0 <= i < m. -/
  theorem spec_13
      (nums queries : Slice I64) (r : alloc.vec.Vec I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
      (hr : answer_queries nums queries = ok r)
      (hlen : r.val.length = queries.val.length) :
      ∀ (i : Nat) (hi : i < queries.val.length) (hi' : i < r.val.length) (mu : Int),
        IsMinOf (valList nums.val) mu →
          (r.val[i]'hi').val ≤ floorDiv (queries.val[i]'hi).val mu := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums queries : Slice I64) (r : alloc.vec.Vec I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hm1 : 1 ≤ queries.val.length) (hm2 : queries.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hqueries : ∀ x ∈ queries.val, 1 ≤ x.val ∧ x.val ≤ 1000000)
        (hr : answer_queries nums queries = ok r)
        (hlen : r.val.length = queries.val.length), ∀ (i : Nat) (hi : i < queries.val.length) (hi' : i < r.val.length) (mu : Int),
          IsMinOf (valList nums.val) mu →
            (r.val[i]'hi').val ≤ floorDiv (queries.val[i]'hi).val mu) := by
    sorry

  end AegisSpec.AnswerQueries
