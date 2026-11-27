import Aegis.MaximumSumQueries.Code.Funs

/-!
# Specifications of `Aegis.MaximumSumQueries.maximum_sum_queries`

LeetCode problem `maximum-sum-queries`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumSumQueries

  def entry (l : List Std.I64) (i : ℕ) : ℤ :=
    ((l[i]?).map (fun x => x.val)).getD 0

  def queryAt (qs : List (alloc.vec.Vec Std.I64)) (i : ℕ) : List Std.I64 :=
    match qs[i]? with
    | some q => q.val
    | none => []

  def qx (qs : List (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ := entry (queryAt qs i) 0

  def qy (qs : List (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ := entry (queryAt qs i) 1

  def IsMaxSumOver (nums1 nums2 : List Std.I64) (n : ℕ) (x y v : ℤ) : Prop :=
    (¬ ∃ j, j < n ∧ x ≤ entry nums1 j ∧ y ≤ entry nums2 j) ∧ v = -1 ∨
      ∃ j, j < n ∧ x ≤ entry nums1 j ∧ y ≤ entry nums2 j ∧
        v = entry nums1 j + entry nums2 j ∧
        ∀ j', j' < n → x ≤ entry nums1 j' → y ≤ entry nums2 j' →
          entry nums1 j' + entry nums2 j' ≤ v

  /-- Whenever the function returns a result r, len(r) = m, and for every i with 0 <= i < m, writing x = queries[i][0], y = queries[i][1], and S_i = { j | 0 <= j < n and nums1[j] >= x and nums2[j] >= y }, we have: if S_i is empty then r[i] = -1; otherwise r[i] = max { nums1[j] + nums2[j] | j in S_i }.
    Preconditions: n = len(nums1) = len(nums2), 1 <= n <= 100000; for every j with 0 <= j < n, 1 <= nums1[j] <= 1000000000 and 1 <= nums2[j] <= 1000000000; m = len(queries), 1 <= m <= 100000; for every i with 0 <= i < m, len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= 1000000000. -/
  theorem spec_1
      (nums1 nums2 : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (n m : ℕ)
      (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hnpos : 1 ≤ n) (hnle : n ≤ 100000)
      (hb1 : ∀ (j : ℕ), j < n → 1 ≤ entry nums1.val j ∧ entry nums1.val j ≤ 1000000000)
      (hb2 : ∀ (j : ℕ), j < n → 1 ≤ entry nums2.val j ∧ entry nums2.val j ≤ 1000000000)
      (hm1 : queries.val.length = m) (hmpos : 1 ≤ m) (hmle : m ≤ 100000)
      (hq : ∀ (i : ℕ), i < m → (queryAt queries.val i).length = 2 ∧
          1 ≤ qx queries.val i ∧ qx queries.val i ≤ 1000000000 ∧
          1 ≤ qy queries.val i ∧ qy queries.val i ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.MaximumSumQueries.maximum_sum_queries nums1 nums2 queries = ok r) :
      r.val.length = m ∧
        ∀ (i : ℕ), i < m →
          IsMaxSumOver nums1.val nums2.val n (qx queries.val i) (qy queries.val i)
            (entry r.val i) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (n m : ℕ)
        (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hnpos : 1 ≤ n) (hnle : n ≤ 100000)
        (hb1 : ∀ (j : ℕ), j < n → 1 ≤ entry nums1.val j ∧ entry nums1.val j ≤ 1000000000)
        (hb2 : ∀ (j : ℕ), j < n → 1 ≤ entry nums2.val j ∧ entry nums2.val j ≤ 1000000000)
        (hm1 : queries.val.length = m) (hmpos : 1 ≤ m) (hmle : m ≤ 100000)
        (hq : ∀ (i : ℕ), i < m → (queryAt queries.val i).length = 2 ∧
            1 ≤ qx queries.val i ∧ qx queries.val i ≤ 1000000000 ∧
            1 ≤ qy queries.val i ∧ qy queries.val i ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.MaximumSumQueries.maximum_sum_queries nums1 nums2 queries = ok r), r.val.length = m ∧
          ∀ (i : ℕ), i < m →
            IsMaxSumOver nums1.val nums2.val n (qx queries.val i) (qy queries.val i)
              (entry r.val i)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: n = len(nums1) = len(nums2), 1 <= n <= 100000; for every j with 0 <= j < n, 1 <= nums1[j] <= 1000000000 and 1 <= nums2[j] <= 1000000000; m = len(queries), 1 <= m <= 100000; for every i with 0 <= i < m, len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= 1000000000. -/
  theorem spec_2
      (nums1 nums2 : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (n m : ℕ)
      (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hnpos : 1 ≤ n) (hnle : n ≤ 100000)
      (hb1 : ∀ (j : ℕ), j < n → 1 ≤ entry nums1.val j ∧ entry nums1.val j ≤ 1000000000)
      (hb2 : ∀ (j : ℕ), j < n → 1 ≤ entry nums2.val j ∧ entry nums2.val j ≤ 1000000000)
      (hm1 : queries.val.length = m) (hmpos : 1 ≤ m) (hmle : m ≤ 100000)
      (hq : ∀ (i : ℕ), i < m → (queryAt queries.val i).length = 2 ∧
          1 ≤ qx queries.val i ∧ qx queries.val i ≤ 1000000000 ∧
          1 ≤ qy queries.val i ∧ qy queries.val i ≤ 1000000000) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.MaximumSumQueries.maximum_sum_queries nums1 nums2 queries = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (n m : ℕ)
        (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hnpos : 1 ≤ n) (hnle : n ≤ 100000)
        (hb1 : ∀ (j : ℕ), j < n → 1 ≤ entry nums1.val j ∧ entry nums1.val j ≤ 1000000000)
        (hb2 : ∀ (j : ℕ), j < n → 1 ≤ entry nums2.val j ∧ entry nums2.val j ≤ 1000000000)
        (hm1 : queries.val.length = m) (hmpos : 1 ≤ m) (hmle : m ≤ 100000)
        (hq : ∀ (i : ℕ), i < m → (queryAt queries.val i).length = 2 ∧
            1 ≤ qx queries.val i ∧ qx queries.val i ≤ 1000000000 ∧
            1 ≤ qy queries.val i ∧ qy queries.val i ≤ 1000000000), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.MaximumSumQueries.maximum_sum_queries nums1 nums2 queries = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for any two query indices i and k with 0 <= i < m and 0 <= k < m, if queries[i][0] <= queries[k][0] and queries[i][1] <= queries[k][1], then: if r[k] != -1 then r[i] != -1 and r[i] >= r[k].
    Preconditions: n = len(nums1) = len(nums2), 1 <= n <= 100000; for every j with 0 <= j < n, 1 <= nums1[j] <= 1000000000 and 1 <= nums2[j] <= 1000000000; m = len(queries), 1 <= m <= 100000; for every i with 0 <= i < m, len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= 1000000000. -/
  theorem spec_3
      (nums1 nums2 : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (n m : ℕ)
      (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hnpos : 1 ≤ n) (hnle : n ≤ 100000)
      (hb1 : ∀ (j : ℕ), j < n → 1 ≤ entry nums1.val j ∧ entry nums1.val j ≤ 1000000000)
      (hb2 : ∀ (j : ℕ), j < n → 1 ≤ entry nums2.val j ∧ entry nums2.val j ≤ 1000000000)
      (hm1 : queries.val.length = m) (hmpos : 1 ≤ m) (hmle : m ≤ 100000)
      (hq : ∀ (i : ℕ), i < m → (queryAt queries.val i).length = 2 ∧
          1 ≤ qx queries.val i ∧ qx queries.val i ≤ 1000000000 ∧
          1 ≤ qy queries.val i ∧ qy queries.val i ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.MaximumSumQueries.maximum_sum_queries nums1 nums2 queries = ok r) :
      ∀ (i k : ℕ), i < m → k < m →
        qx queries.val i ≤ qx queries.val k →
        qy queries.val i ≤ qy queries.val k →
        entry r.val k ≠ -1 → entry r.val i ≠ -1 ∧ entry r.val k ≤ entry r.val i := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (n m : ℕ)
        (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hnpos : 1 ≤ n) (hnle : n ≤ 100000)
        (hb1 : ∀ (j : ℕ), j < n → 1 ≤ entry nums1.val j ∧ entry nums1.val j ≤ 1000000000)
        (hb2 : ∀ (j : ℕ), j < n → 1 ≤ entry nums2.val j ∧ entry nums2.val j ≤ 1000000000)
        (hm1 : queries.val.length = m) (hmpos : 1 ≤ m) (hmle : m ≤ 100000)
        (hq : ∀ (i : ℕ), i < m → (queryAt queries.val i).length = 2 ∧
            1 ≤ qx queries.val i ∧ qx queries.val i ≤ 1000000000 ∧
            1 ≤ qy queries.val i ∧ qy queries.val i ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.MaximumSumQueries.maximum_sum_queries nums1 nums2 queries = ok r), ∀ (i k : ℕ), i < m → k < m →
          qx queries.val i ≤ qx queries.val k →
          qy queries.val i ≤ qy queries.val k →
          entry r.val k ≠ -1 → entry r.val i ≠ -1 ∧ entry r.val k ≤ entry r.val i) := by
    sorry

  /-- Whenever the function returns a result r on nums1, nums2, queries, for any arrays nums1' and nums2' of length n for which there exists a permutation p of {0, ..., n-1} such that nums1'[i] = nums1[p(i)] and nums2'[i] = nums2[p(i)] for every i with 0 <= i < n, the function called on nums1', nums2', queries returns the same result r.
    Preconditions: n = len(nums1) = len(nums2), 1 <= n <= 100000; for every j with 0 <= j < n, 1 <= nums1[j] <= 1000000000 and 1 <= nums2[j] <= 1000000000; m = len(queries), 1 <= m <= 100000; for every i with 0 <= i < m, len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= 1000000000. -/
  theorem spec_4
      (nums1 nums2 : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (n m : ℕ)
      (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hnpos : 1 ≤ n) (hnle : n ≤ 100000)
      (hb1 : ∀ (j : ℕ), j < n → 1 ≤ entry nums1.val j ∧ entry nums1.val j ≤ 1000000000)
      (hb2 : ∀ (j : ℕ), j < n → 1 ≤ entry nums2.val j ∧ entry nums2.val j ≤ 1000000000)
      (hm1 : queries.val.length = m) (hmpos : 1 ≤ m) (hmle : m ≤ 100000)
      (hq : ∀ (i : ℕ), i < m → (queryAt queries.val i).length = 2 ∧
          1 ≤ qx queries.val i ∧ qx queries.val i ≤ 1000000000 ∧
          1 ≤ qy queries.val i ∧ qy queries.val i ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.MaximumSumQueries.maximum_sum_queries nums1 nums2 queries = ok r)
      (nums1' nums2' : Slice Std.I64)
      (hn1' : nums1'.val.length = n) (hn2' : nums2'.val.length = n)
      (hp : ∃ p : Equiv.Perm (Fin n), ∀ (i : ℕ) (hi : i < n),
          entry nums1'.val i = entry nums1.val (p ⟨i, hi⟩).val ∧
          entry nums2'.val i = entry nums2.val (p ⟨i, hi⟩).val) :
      Aegis.MaximumSumQueries.maximum_sum_queries nums1' nums2' queries = ok r := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (n m : ℕ)
        (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hnpos : 1 ≤ n) (hnle : n ≤ 100000)
        (hb1 : ∀ (j : ℕ), j < n → 1 ≤ entry nums1.val j ∧ entry nums1.val j ≤ 1000000000)
        (hb2 : ∀ (j : ℕ), j < n → 1 ≤ entry nums2.val j ∧ entry nums2.val j ≤ 1000000000)
        (hm1 : queries.val.length = m) (hmpos : 1 ≤ m) (hmle : m ≤ 100000)
        (hq : ∀ (i : ℕ), i < m → (queryAt queries.val i).length = 2 ∧
            1 ≤ qx queries.val i ∧ qx queries.val i ≤ 1000000000 ∧
            1 ≤ qy queries.val i ∧ qy queries.val i ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.MaximumSumQueries.maximum_sum_queries nums1 nums2 queries = ok r)
        (nums1' nums2' : Slice Std.I64)
        (hn1' : nums1'.val.length = n) (hn2' : nums2'.val.length = n)
        (hp : ∃ p : Equiv.Perm (Fin n), ∀ (i : ℕ) (hi : i < n),
            entry nums1'.val i = entry nums1.val (p ⟨i, hi⟩).val ∧
            entry nums2'.val i = entry nums2.val (p ⟨i, hi⟩).val), Aegis.MaximumSumQueries.maximum_sum_queries nums1' nums2' queries = ok r) := by
    sorry

  /-- Whenever the function returns a result r on nums1, nums2, queries, for any permutation pi of {0, ..., m-1}, let queries' be the slice of length m with queries'[i] = queries[pi(i)] for every i with 0 <= i < m. If r' is the result of the function on nums1, nums2, queries', then len(r') = m and r'[i] = r[pi(i)] for every i with 0 <= i < m.
    Preconditions: n = len(nums1) = len(nums2), 1 <= n <= 100000; for every j with 0 <= j < n, 1 <= nums1[j] <= 1000000000 and 1 <= nums2[j] <= 1000000000; m = len(queries), 1 <= m <= 100000; for every i with 0 <= i < m, len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= 1000000000. -/
  theorem spec_5
      (nums1 nums2 : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (n m : ℕ)
      (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
      (hnpos : 1 ≤ n) (hnle : n ≤ 100000)
      (hb1 : ∀ (j : ℕ), j < n → 1 ≤ entry nums1.val j ∧ entry nums1.val j ≤ 1000000000)
      (hb2 : ∀ (j : ℕ), j < n → 1 ≤ entry nums2.val j ∧ entry nums2.val j ≤ 1000000000)
      (hm1 : queries.val.length = m) (hmpos : 1 ≤ m) (hmle : m ≤ 100000)
      (hq : ∀ (i : ℕ), i < m → (queryAt queries.val i).length = 2 ∧
          1 ≤ qx queries.val i ∧ qx queries.val i ≤ 1000000000 ∧
          1 ≤ qy queries.val i ∧ qy queries.val i ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64)
      (hr : Aegis.MaximumSumQueries.maximum_sum_queries nums1 nums2 queries = ok r)
      (pi : Equiv.Perm (Fin m))
      (queries' : Slice (alloc.vec.Vec Std.I64))
      (hqm : queries'.val.length = m)
      (hqp : ∀ (i : ℕ) (hi : i < m),
        queries'.val[i]? = queries.val[(pi ⟨i, hi⟩).val]?)
      (r' : alloc.vec.Vec Std.I64)
      (hr' : Aegis.MaximumSumQueries.maximum_sum_queries nums1 nums2 queries' = ok r') :
      r'.val.length = m ∧
        ∀ (i : ℕ) (hi : i < m), entry r'.val i = entry r.val (pi ⟨i, hi⟩).val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (n m : ℕ)
        (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
        (hnpos : 1 ≤ n) (hnle : n ≤ 100000)
        (hb1 : ∀ (j : ℕ), j < n → 1 ≤ entry nums1.val j ∧ entry nums1.val j ≤ 1000000000)
        (hb2 : ∀ (j : ℕ), j < n → 1 ≤ entry nums2.val j ∧ entry nums2.val j ≤ 1000000000)
        (hm1 : queries.val.length = m) (hmpos : 1 ≤ m) (hmle : m ≤ 100000)
        (hq : ∀ (i : ℕ), i < m → (queryAt queries.val i).length = 2 ∧
            1 ≤ qx queries.val i ∧ qx queries.val i ≤ 1000000000 ∧
            1 ≤ qy queries.val i ∧ qy queries.val i ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64)
        (hr : Aegis.MaximumSumQueries.maximum_sum_queries nums1 nums2 queries = ok r)
        (pi : Equiv.Perm (Fin m))
        (queries' : Slice (alloc.vec.Vec Std.I64))
        (hqm : queries'.val.length = m)
        (hqp : ∀ (i : ℕ) (hi : i < m),
          queries'.val[i]? = queries.val[(pi ⟨i, hi⟩).val]?)
        (r' : alloc.vec.Vec Std.I64)
        (hr' : Aegis.MaximumSumQueries.maximum_sum_queries nums1 nums2 queries' = ok r'), r'.val.length = m ∧
          ∀ (i : ℕ) (hi : i < m), entry r'.val i = entry r.val (pi ⟨i, hi⟩).val) := by
    sorry

  end AegisSpec.MaximumSumQueries
