import Aegis.SumEvenAfterQueries.Code.Funs

/-!
# Specifications of `Aegis.SumEvenAfterQueries.sum_even_after_queries`

LeetCode problem `sum-of-even-numbers-after-queries`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SumEvenAfterQueries

  open Classical

  attribute [local instance] Classical.propDecidable

  def IsEven (x : ℤ) : Prop := ∃ t : ℤ, x = 2 * t

  def IsOdd (x : ℤ) : Prop := ¬ IsEven x

  def sliceInts (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

  def vecInts (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map (fun x => x.val)

  def queryInts (queries : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    queries.val.map vecInts

  def nlen (nums : Slice Std.I64) : ℕ := (sliceInts nums).length

  def numAt (nums : Slice Std.I64) (j : ℕ) : ℤ := (sliceInts nums).getD j 0

  def qlen (queries : Slice (alloc.vec.Vec Std.I64)) : ℕ := (queryInts queries).length

  def querySize (queries : Slice (alloc.vec.Vec Std.I64)) (k : ℕ) : ℕ :=
    ((queryInts queries).getD k []).length

  def queryVal (queries : Slice (alloc.vec.Vec Std.I64)) (k : ℕ) : ℤ :=
    ((queryInts queries).getD k []).getD 0 0

  def queryIdx (queries : Slice (alloc.vec.Vec Std.I64)) (k : ℕ) : ℤ :=
    ((queryInts queries).getD k []).getD 1 0

  def queryPair (queries : Slice (alloc.vec.Vec Std.I64)) (k : ℕ) : ℤ × ℕ :=
    (queryVal queries k, (queryIdx queries k).toNat)

  def queryPairs (queries : Slice (alloc.vec.Vec Std.I64)) : List (ℤ × ℕ) :=
    (List.range (qlen queries)).map (queryPair queries)

  def updateAt (a : List ℤ) (i : ℕ) (d : ℤ) : List ℤ := a.set i (a.getD i 0 + d)

  def stateAfter (nums : List ℤ) (qs : List (ℤ × ℕ)) (k : ℕ) : List ℤ :=
    (qs.take k).foldl (fun a q => updateAt a q.2 q.1) nums

  noncomputable def evenSum (l : List ℤ) : ℤ :=
    (l.map (fun x => if IsEven x then x else 0)).sum

  def totalDelta (qs : List (ℤ × ℕ)) (j : ℕ) : ℤ :=
    (qs.map (fun q => if q.2 = j then q.1 else 0)).sum

  def AllEven (l : List ℤ) : Prop := ∀ x, x ∈ l → IsEven x

  def AllOdd (l : List ℤ) : Prop := ∀ x, x ∈ l → IsOdd x

  /-- The function returns a result r and, with m = len(queries) and n = len(nums), len(r) = m and for every i with 0 <= i < m, r[i] = Σ_{j=0}^{n-1} (if A^(i+1)[j] is even then A^(i+1)[j] else 0), where A^(0) = nums, for 0 <= k < m the array A^(k+1) of length n is defined by A^(k+1)[j] = A^(k)[j] + (if j = queries[k][1] then queries[k][0] else 0) for every 0 <= j < n, and an integer x is even iff x = 2*t for some integer t.
    Preconditions: len(nums) >= 1; len(nums) <= 10000; len(queries) >= 1; len(queries) <= 10000; for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000; for every k with 0 <= k < len(queries), len(queries[k]) = 2; for every k with 0 <= k < len(queries), -10000 <= queries[k][0] <= 10000; for every k with 0 <= k < len(queries), 0 <= queries[k][1] < len(nums) -/
  theorem spec_1 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
      (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
      (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
      (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
      (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
      (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
        queryIdx queries k < (nlen nums : ℤ)) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r ∧
        (vecInts r).length = qlen queries ∧
        ∀ i, i < qlen queries →
          (vecInts r).getD i 0
            = evenSum (stateAfter (sliceInts nums) (queryPairs queries) (i + 1)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
        (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
        (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
        (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
        (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
        (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
          queryIdx queries k < (nlen nums : ℤ)), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r ∧
          (vecInts r).length = qlen queries ∧
          ∀ i, i < qlen queries →
            (vecInts r).getD i 0
              = evenSum (stateAfter (sliceInts nums) (queryPairs queries) (i + 1))) := by
    sorry

  /-- The function returns a result r; under the preconditions it does not fail (no overflow, out-of-bounds access, or panic).
    Preconditions: len(nums) >= 1; len(nums) <= 10000; len(queries) >= 1; len(queries) <= 10000; for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000; for every k with 0 <= k < len(queries), len(queries[k]) = 2; for every k with 0 <= k < len(queries), -10000 <= queries[k][0] <= 10000; for every k with 0 <= k < len(queries), 0 <= queries[k][1] < len(nums) -/
  theorem spec_2 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
      (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
      (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
      (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
      (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
      (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
        queryIdx queries k < (nlen nums : ℤ)) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
        (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
        (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
        (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
        (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
        (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
          queryIdx queries k < (nlen nums : ℤ)), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(queries).
    Preconditions: len(nums) >= 1; len(nums) <= 10000; len(queries) >= 1; len(queries) <= 10000; for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000; for every k with 0 <= k < len(queries), len(queries[k]) = 2; for every k with 0 <= k < len(queries), -10000 <= queries[k][0] <= 10000; for every k with 0 <= k < len(queries), 0 <= queries[k][1] < len(nums) -/
  theorem spec_3 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
      (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
      (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
      (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
      (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
      (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
        queryIdx queries k < (nlen nums : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
        (vecInts r).length = qlen queries := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
        (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
        (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
        (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
        (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
        (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
          queryIdx queries k < (nlen nums : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
          (vecInts r).length = qlen queries) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = len(queries), define for every j with 0 <= j < len(nums) the total increment S_j = Σ_{k=0}^{len(queries)-1} (if queries[k][1] = j then queries[k][0] else 0). Then r[len(queries)-1] = Σ_{j=0}^{len(nums)-1} (if nums[j] + S_j is even then nums[j] + S_j else 0), where an integer x is even iff x = 2*t for some integer t.
    Preconditions: len(nums) >= 1; len(nums) <= 10000; len(queries) >= 1; len(queries) <= 10000; for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000; for every k with 0 <= k < len(queries), len(queries[k]) = 2; for every k with 0 <= k < len(queries), -10000 <= queries[k][0] <= 10000; for every k with 0 <= k < len(queries), 0 <= queries[k][1] < len(nums) -/
  theorem spec_4 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
      (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
      (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
      (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
      (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
      (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
        queryIdx queries k < (nlen nums : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
        (vecInts r).length = qlen queries →
        (vecInts r).getD (qlen queries - 1) 0
          = evenSum ((List.range (nlen nums)).map
              (fun j => numAt nums j + totalDelta (queryPairs queries) j)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
        (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
        (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
        (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
        (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
        (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
          queryIdx queries k < (nlen nums : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
          (vecInts r).length = qlen queries →
          (vecInts r).getD (qlen queries - 1) 0
            = evenSum ((List.range (nlen nums)).map
                (fun j => numAt nums j + totalDelta (queryPairs queries) j))) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = len(queries), let A^(0) = nums and for 0 <= k < len(queries) let A^(k+1) be obtained from A^(k) by adding queries[k][0] to position queries[k][1]. Let E_0 = Σ_{j=0}^{len(nums)-1} (if A^(0)[j] is even then A^(0)[j] else 0). For every i with 0 <= i < len(queries), put b = A^(i)[queries[i][1]] and c = b + queries[i][0]. Then r[i] = (if i = 0 then E_0 else r[i-1]) + (if c is even then c else 0) - (if b is even then b else 0), where an integer x is even iff x = 2*t for some integer t.
    Preconditions: len(nums) >= 1; len(nums) <= 10000; len(queries) >= 1; len(queries) <= 10000; for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000; for every k with 0 <= k < len(queries), len(queries[k]) = 2; for every k with 0 <= k < len(queries), -10000 <= queries[k][0] <= 10000; for every k with 0 <= k < len(queries), 0 <= queries[k][1] < len(nums) -/
  theorem spec_5 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
      (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
      (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
      (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
      (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
      (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
        queryIdx queries k < (nlen nums : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
        (vecInts r).length = qlen queries →
        ∀ i, i < qlen queries →
          let b := (stateAfter (sliceInts nums) (queryPairs queries) i).getD
            (queryPair queries i).2 0
          let c := b + (queryPair queries i).1
          (vecInts r).getD i 0
            = (if i = 0 then evenSum (sliceInts nums) else (vecInts r).getD (i - 1) 0)
              + (if IsEven c then c else 0) - (if IsEven b then b else 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
        (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
        (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
        (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
        (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
        (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
          queryIdx queries k < (nlen nums : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
          (vecInts r).length = qlen queries →
          ∀ i, i < qlen queries →
            let b := (stateAfter (sliceInts nums) (queryPairs queries) i).getD
              (queryPair queries i).2 0
            let c := b + (queryPair queries i).1
            (vecInts r).getD i 0
              = (if i = 0 then evenSum (sliceInts nums) else (vecInts r).getD (i - 1) 0)
                + (if IsEven c then c else 0) - (if IsEven b then b else 0)) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = len(queries), for every i with 0 <= i < len(queries), r[i] is even (there exists an integer t with r[i] = 2*t).
    Preconditions: len(nums) >= 1; len(nums) <= 10000; len(queries) >= 1; len(queries) <= 10000; for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000; for every k with 0 <= k < len(queries), len(queries[k]) = 2; for every k with 0 <= k < len(queries), -10000 <= queries[k][0] <= 10000; for every k with 0 <= k < len(queries), 0 <= queries[k][1] < len(nums) -/
  theorem spec_6 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
      (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
      (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
      (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
      (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
      (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
        queryIdx queries k < (nlen nums : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
        (vecInts r).length = qlen queries →
        ∀ i, i < qlen queries → IsEven ((vecInts r).getD i 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
        (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
        (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
        (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
        (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
        (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
          queryIdx queries k < (nlen nums : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
          (vecInts r).length = qlen queries →
          ∀ i, i < qlen queries → IsEven ((vecInts r).getD i 0)) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = len(queries), for every i with 0 <= i < len(queries) such that queries[i][0] = 0: if i = 0 then r[0] = Σ_{j=0}^{len(nums)-1} (if nums[j] is even then nums[j] else 0), and if i > 0 then r[i] = r[i-1]. Here an integer x is even iff x = 2*t for some integer t.
    Preconditions: len(nums) >= 1; len(nums) <= 10000; len(queries) >= 1; len(queries) <= 10000; for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000; for every k with 0 <= k < len(queries), len(queries[k]) = 2; for every k with 0 <= k < len(queries), -10000 <= queries[k][0] <= 10000; for every k with 0 <= k < len(queries), 0 <= queries[k][1] < len(nums) -/
  theorem spec_7 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
      (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
      (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
      (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
      (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
      (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
        queryIdx queries k < (nlen nums : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
        (vecInts r).length = qlen queries →
        ∀ i, i < qlen queries → queryVal queries i = 0 →
          (if i = 0 then (vecInts r).getD 0 0 = evenSum (sliceInts nums)
           else (vecInts r).getD i 0 = (vecInts r).getD (i - 1) 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
        (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
        (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
        (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
        (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
        (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
          queryIdx queries k < (nlen nums : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
          (vecInts r).length = qlen queries →
          ∀ i, i < qlen queries → queryVal queries i = 0 →
            (if i = 0 then (vecInts r).getD 0 0 = evenSum (sliceInts nums)
             else (vecInts r).getD i 0 = (vecInts r).getD (i - 1) 0)) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = len(queries), let A^(0) = nums and for 0 <= k < len(queries) let A^(k+1) be obtained from A^(k) by adding queries[k][0] to position queries[k][1]. For every i with 0 <= i < len(queries), if every entry of A^(i+1) is odd (not even), then r[i] = 0. An integer x is even iff x = 2*t for some integer t.
    Preconditions: len(nums) >= 1; len(nums) <= 10000; len(queries) >= 1; len(queries) <= 10000; for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000; for every k with 0 <= k < len(queries), len(queries[k]) = 2; for every k with 0 <= k < len(queries), -10000 <= queries[k][0] <= 10000; for every k with 0 <= k < len(queries), 0 <= queries[k][1] < len(nums) -/
  theorem spec_8 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
      (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
      (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
      (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
      (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
      (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
        queryIdx queries k < (nlen nums : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
        (vecInts r).length = qlen queries →
        ∀ i, i < qlen queries →
          AllOdd (stateAfter (sliceInts nums) (queryPairs queries) (i + 1)) →
          (vecInts r).getD i 0 = 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
        (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
        (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
        (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
        (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
        (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
          queryIdx queries k < (nlen nums : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
          (vecInts r).length = qlen queries →
          ∀ i, i < qlen queries →
            AllOdd (stateAfter (sliceInts nums) (queryPairs queries) (i + 1)) →
            (vecInts r).getD i 0 = 0) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = len(queries), let A^(0) = nums and for 0 <= k < len(queries) let A^(k+1) be obtained from A^(k) by adding queries[k][0] to position queries[k][1]. For every i with 0 <= i < len(queries), if every entry of A^(i+1) is even, then r[i] = Σ_{j=0}^{len(nums)-1} A^(i+1)[j], where an integer x is even iff x = 2*t for some integer t.
    Preconditions: len(nums) >= 1; len(nums) <= 10000; len(queries) >= 1; len(queries) <= 10000; for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000; for every k with 0 <= k < len(queries), len(queries[k]) = 2; for every k with 0 <= k < len(queries), -10000 <= queries[k][0] <= 10000; for every k with 0 <= k < len(queries), 0 <= queries[k][1] < len(nums) -/
  theorem spec_9 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
      (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
      (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
      (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
      (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
      (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
        queryIdx queries k < (nlen nums : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
        (vecInts r).length = qlen queries →
        ∀ i, i < qlen queries →
          AllEven (stateAfter (sliceInts nums) (queryPairs queries) (i + 1)) →
          (vecInts r).getD i 0
            = (stateAfter (sliceInts nums) (queryPairs queries) (i + 1)).sum := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
        (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
        (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
        (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
        (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
        (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
          queryIdx queries k < (nlen nums : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
          (vecInts r).length = qlen queries →
          ∀ i, i < qlen queries →
            AllEven (stateAfter (sliceInts nums) (queryPairs queries) (i + 1)) →
            (vecInts r).getD i 0
              = (stateAfter (sliceInts nums) (queryPairs queries) (i + 1)).sum) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = len(queries), for every i with 0 <= i < len(queries), r[i] = (Σ_{j=0}^{len(nums)-1} nums[j]) + Σ_{k=0}^{i} queries[k][0].
    Preconditions: len(nums) >= 1; len(nums) <= 10000; len(queries) >= 1; len(queries) <= 10000; for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000; for every k with 0 <= k < len(queries), len(queries[k]) = 2; for every k with 0 <= k < len(queries), -10000 <= queries[k][0] <= 10000; for every k with 0 <= k < len(queries), 0 <= queries[k][1] < len(nums); for every j with 0 <= j < len(nums), nums[j] is even (nums[j] = 2*t for some integer t); for every k with 0 <= k < len(queries), queries[k][0] is even (queries[k][0] = 2*t for some integer t) -/
  theorem spec_10 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
      (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
      (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
      (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
      (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
      (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
        queryIdx queries k < (nlen nums : ℤ))
      (h_nums_even : ∀ j, j < nlen nums → IsEven (numAt nums j))
      (h_qs_val_even : ∀ k, k < qlen queries → IsEven (queryVal queries k)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
        (vecInts r).length = qlen queries →
        ∀ i, i < qlen queries →
          (vecInts r).getD i 0
            = (sliceInts nums).sum
              + ((List.range (i + 1)).map (fun k => queryVal queries k)).sum := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
        (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
        (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
        (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
        (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
        (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
          queryIdx queries k < (nlen nums : ℤ))
        (h_nums_even : ∀ j, j < nlen nums → IsEven (numAt nums j))
        (h_qs_val_even : ∀ k, k < qlen queries → IsEven (queryVal queries k)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
          (vecInts r).length = qlen queries →
          ∀ i, i < qlen queries →
            (vecInts r).getD i 0
              = (sliceInts nums).sum
                + ((List.range (i + 1)).map (fun k => queryVal queries k)).sum) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = len(queries), for every i with 0 <= i < len(queries), let x = nums[0] + Σ_{k=0}^{i} queries[k][0]. Then r[i] = x if x is even, and r[i] = 0 if x is odd (an integer y is even iff y = 2*t for some integer t).
    Preconditions: len(nums) >= 1; len(nums) <= 10000; len(queries) >= 1; len(queries) <= 10000; for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000; for every k with 0 <= k < len(queries), len(queries[k]) = 2; for every k with 0 <= k < len(queries), -10000 <= queries[k][0] <= 10000; for every k with 0 <= k < len(queries), 0 <= queries[k][1] < len(nums); len(nums) = 1 -/
  theorem spec_11 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
      (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
      (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
      (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
      (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
      (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
        queryIdx queries k < (nlen nums : ℤ))
      (h_nums_len : nlen nums = 1) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
        (vecInts r).length = qlen queries →
        ∀ i, i < qlen queries →
          let x := (sliceInts nums).getD 0 0
            + ((List.range (i + 1)).map (fun k => queryVal queries k)).sum
          (vecInts r).getD i 0 = (if IsEven x then x else 0) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
        (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
        (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
        (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
        (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
        (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
          queryIdx queries k < (nlen nums : ℤ))
        (h_nums_len : nlen nums = 1), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
          (vecInts r).length = qlen queries →
          ∀ i, i < qlen queries →
            let x := (sliceInts nums).getD 0 0
              + ((List.range (i + 1)).map (fun k => queryVal queries k)).sum
            (vecInts r).getD i 0 = (if IsEven x then x else 0)) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = len(queries), for every i with 0 <= i < len(queries), |r[i]| <= len(nums) * (10000 + len(queries) * 10000).
    Preconditions: len(nums) >= 1; len(nums) <= 10000; len(queries) >= 1; len(queries) <= 10000; for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000; for every k with 0 <= k < len(queries), len(queries[k]) = 2; for every k with 0 <= k < len(queries), -10000 <= queries[k][0] <= 10000; for every k with 0 <= k < len(queries), 0 <= queries[k][1] < len(nums) -/
  theorem spec_12 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
      (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
      (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
      (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
      (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
      (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
        queryIdx queries k < (nlen nums : ℤ)) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
        (vecInts r).length = qlen queries →
        ∀ i, i < qlen queries →
          |(vecInts r).getD i 0| ≤ (nlen nums : ℤ) * (10000 + (qlen queries : ℤ) * 10000) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_nums_len_ge : 1 ≤ nlen nums) (h_nums_len_le : nlen nums ≤ 10000)
        (h_qs_len_ge : 1 ≤ qlen queries) (h_qs_len_le : qlen queries ≤ 10000)
        (h_nums_bound : ∀ j, j < nlen nums → -10000 ≤ numAt nums j ∧ numAt nums j ≤ 10000)
        (h_qs_size : ∀ k, k < qlen queries → querySize queries k = 2)
        (h_qs_val : ∀ k, k < qlen queries → -10000 ≤ queryVal queries k ∧ queryVal queries k ≤ 10000)
        (h_qs_idx : ∀ k, k < qlen queries → 0 ≤ queryIdx queries k ∧
          queryIdx queries k < (nlen nums : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.SumEvenAfterQueries.sum_even_after_queries nums queries = ok r →
          (vecInts r).length = qlen queries →
          ∀ i, i < qlen queries →
            |(vecInts r).getD i 0| ≤ (nlen nums : ℤ) * (10000 + (qlen queries : ℤ) * 10000)) := by
    sorry

  end AegisSpec.SumEvenAfterQueries
