import Aegis.XorQueries.Code.Funs

/-!
# Specifications of `Aegis.XorQueries.xor_queries`

LeetCode problem `xor-queries-of-a-subarray`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.XorQueries

def bxor (a b : Int) : Int := (BitVec.ofInt 64 a ^^^ BitVec.ofInt 64 b).toInt

def xorRange (arr : Slice Std.I64) (lo hi : Nat) : Int :=
  (List.range (hi + 1 - lo)).foldl (fun acc d => bxor acc ((arr.val[lo + d]!).val)) 0

/-- Whenever the function returns a result r, len(r) = len(queries), and for every i with 0 <= i < len(queries), writing l = queries[i][0] and m = queries[i][1], we have r[i] = arr[l] XOR arr[l+1] XOR ... XOR arr[m], i.e. r[i] is the bitwise XOR of all arr[j] with l <= j <= m. This range is non-empty because l <= m.
  Preconditions: len(arr) >= 1 and len(queries) >= 1; len(arr) <= 30000 and len(queries) <= 30000; for every k with 0 <= k < len(arr), 1 <= arr[k] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2 and 0 <= queries[i][0] <= queries[i][1] < len(arr). -/
theorem spec_1
    (arr : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (harr_pos : 1 ≤ arr.val.length)
    (hqueries_pos : 1 ≤ queries.val.length)
    (harr_le : arr.val.length ≤ 30000)
    (hqueries_le : queries.val.length ≤ 30000)
    (harr_bounds : ∀ k, k < arr.val.length →
      1 ≤ (arr.val[k]!).val ∧ (arr.val[k]!).val ≤ 1000000000)
    (hquery_bounds : ∀ i, i < queries.val.length →
      (queries.val[i]!).val.length = 2 ∧
      0 ≤ ((queries.val[i]!).val[0]!).val ∧
      ((queries.val[i]!).val[0]!).val ≤ ((queries.val[i]!).val[1]!).val ∧
      ((queries.val[i]!).val[1]!).val < (arr.val.length : Int)) :
    ∀ r, Aegis.XorQueries.xor_queries arr queries = ok r →
      r.val.length = queries.val.length ∧
      ∀ i, i < queries.val.length →
        (r.val[i]!).val =
          xorRange arr (((queries.val[i]!).val[0]!).val.toNat)
            (((queries.val[i]!).val[1]!).val.toNat) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (harr_pos : 1 ≤ arr.val.length)
    (hqueries_pos : 1 ≤ queries.val.length)
    (harr_le : arr.val.length ≤ 30000)
    (hqueries_le : queries.val.length ≤ 30000)
    (harr_bounds : ∀ k, k < arr.val.length →
      1 ≤ (arr.val[k]!).val ∧ (arr.val[k]!).val ≤ 1000000000)
    (hquery_bounds : ∀ i, i < queries.val.length →
      (queries.val[i]!).val.length = 2 ∧
      0 ≤ ((queries.val[i]!).val[0]!).val ∧
      ((queries.val[i]!).val[0]!).val ≤ ((queries.val[i]!).val[1]!).val ∧
      ((queries.val[i]!).val[1]!).val < (arr.val.length : Int)), ∀ r, Aegis.XorQueries.xor_queries arr queries = ok r →
      r.val.length = queries.val.length ∧
      ∀ i, i < queries.val.length →
        (r.val[i]!).val =
          xorRange arr (((queries.val[i]!).val[0]!).val.toNat)
            (((queries.val[i]!).val[1]!).val.toNat)) := by
  sorry

/-- The function returns a result r (it does not panic, fail an arithmetic overflow check, or access arr or any query vector out of bounds).
  Preconditions: len(arr) >= 1 and len(queries) >= 1; len(arr) <= 30000 and len(queries) <= 30000; for every k with 0 <= k < len(arr), 1 <= arr[k] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2 and 0 <= queries[i][0] <= queries[i][1] < len(arr). -/
theorem spec_2
    (arr : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (harr_pos : 1 ≤ arr.val.length)
    (hqueries_pos : 1 ≤ queries.val.length)
    (harr_le : arr.val.length ≤ 30000)
    (hqueries_le : queries.val.length ≤ 30000)
    (harr_bounds : ∀ k, k < arr.val.length →
      1 ≤ (arr.val[k]!).val ∧ (arr.val[k]!).val ≤ 1000000000)
    (hquery_bounds : ∀ i, i < queries.val.length →
      (queries.val[i]!).val.length = 2 ∧
      0 ≤ ((queries.val[i]!).val[0]!).val ∧
      ((queries.val[i]!).val[0]!).val ≤ ((queries.val[i]!).val[1]!).val ∧
      ((queries.val[i]!).val[1]!).val < (arr.val.length : Int)) :
    ∃ r, Aegis.XorQueries.xor_queries arr queries = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (harr_pos : 1 ≤ arr.val.length)
    (hqueries_pos : 1 ≤ queries.val.length)
    (harr_le : arr.val.length ≤ 30000)
    (hqueries_le : queries.val.length ≤ 30000)
    (harr_bounds : ∀ k, k < arr.val.length →
      1 ≤ (arr.val[k]!).val ∧ (arr.val[k]!).val ≤ 1000000000)
    (hquery_bounds : ∀ i, i < queries.val.length →
      (queries.val[i]!).val.length = 2 ∧
      0 ≤ ((queries.val[i]!).val[0]!).val ∧
      ((queries.val[i]!).val[0]!).val ≤ ((queries.val[i]!).val[1]!).val ∧
      ((queries.val[i]!).val[1]!).val < (arr.val.length : Int)), ∃ r, Aegis.XorQueries.xor_queries arr queries = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), 0 <= r[i] < 2^30.
  Preconditions: len(arr) >= 1 and len(queries) >= 1; len(arr) <= 30000 and len(queries) <= 30000; for every k with 0 <= k < len(arr), 1 <= arr[k] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2 and 0 <= queries[i][0] <= queries[i][1] < len(arr). -/
theorem spec_3
    (arr : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (harr_pos : 1 ≤ arr.val.length)
    (hqueries_pos : 1 ≤ queries.val.length)
    (harr_le : arr.val.length ≤ 30000)
    (hqueries_le : queries.val.length ≤ 30000)
    (harr_bounds : ∀ k, k < arr.val.length →
      1 ≤ (arr.val[k]!).val ∧ (arr.val[k]!).val ≤ 1000000000)
    (hquery_bounds : ∀ i, i < queries.val.length →
      (queries.val[i]!).val.length = 2 ∧
      0 ≤ ((queries.val[i]!).val[0]!).val ∧
      ((queries.val[i]!).val[0]!).val ≤ ((queries.val[i]!).val[1]!).val ∧
      ((queries.val[i]!).val[1]!).val < (arr.val.length : Int)) :
    ∀ r, Aegis.XorQueries.xor_queries arr queries = ok r →
      ∀ i, i < queries.val.length →
        0 ≤ (r.val[i]!).val ∧ (r.val[i]!).val < (2 : Int) ^ 30 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (harr_pos : 1 ≤ arr.val.length)
    (hqueries_pos : 1 ≤ queries.val.length)
    (harr_le : arr.val.length ≤ 30000)
    (hqueries_le : queries.val.length ≤ 30000)
    (harr_bounds : ∀ k, k < arr.val.length →
      1 ≤ (arr.val[k]!).val ∧ (arr.val[k]!).val ≤ 1000000000)
    (hquery_bounds : ∀ i, i < queries.val.length →
      (queries.val[i]!).val.length = 2 ∧
      0 ≤ ((queries.val[i]!).val[0]!).val ∧
      ((queries.val[i]!).val[0]!).val ≤ ((queries.val[i]!).val[1]!).val ∧
      ((queries.val[i]!).val[1]!).val < (arr.val.length : Int)), ∀ r, Aegis.XorQueries.xor_queries arr queries = ok r →
      ∀ i, i < queries.val.length →
        0 ≤ (r.val[i]!).val ∧ (r.val[i]!).val < (2 : Int) ^ 30) := by
  sorry

/-- Whenever the function returns a result r, for all i and j with 0 <= i < len(queries) and 0 <= j < len(queries), if queries[i][0] = queries[j][0] and queries[i][1] < queries[j][1], then r[i] XOR r[j] = arr[queries[i][1]+1] XOR arr[queries[i][1]+2] XOR ... XOR arr[queries[j][1]].
  Preconditions: len(arr) >= 1 and len(queries) >= 1; len(arr) <= 30000 and len(queries) <= 30000; for every k with 0 <= k < len(arr), 1 <= arr[k] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2 and 0 <= queries[i][0] <= queries[i][1] < len(arr). -/
theorem spec_4
    (arr : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (harr_pos : 1 ≤ arr.val.length)
    (hqueries_pos : 1 ≤ queries.val.length)
    (harr_le : arr.val.length ≤ 30000)
    (hqueries_le : queries.val.length ≤ 30000)
    (harr_bounds : ∀ k, k < arr.val.length →
      1 ≤ (arr.val[k]!).val ∧ (arr.val[k]!).val ≤ 1000000000)
    (hquery_bounds : ∀ i, i < queries.val.length →
      (queries.val[i]!).val.length = 2 ∧
      0 ≤ ((queries.val[i]!).val[0]!).val ∧
      ((queries.val[i]!).val[0]!).val ≤ ((queries.val[i]!).val[1]!).val ∧
      ((queries.val[i]!).val[1]!).val < (arr.val.length : Int)) :
    ∀ r, Aegis.XorQueries.xor_queries arr queries = ok r →
      ∀ i j, i < queries.val.length → j < queries.val.length →
        ((queries.val[i]!).val[0]!).val = ((queries.val[j]!).val[0]!).val →
        ((queries.val[i]!).val[1]!).val < ((queries.val[j]!).val[1]!).val →
        bxor (r.val[i]!).val (r.val[j]!).val =
          xorRange arr (((queries.val[i]!).val[1]!).val.toNat + 1)
            (((queries.val[j]!).val[1]!).val.toNat) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (harr_pos : 1 ≤ arr.val.length)
    (hqueries_pos : 1 ≤ queries.val.length)
    (harr_le : arr.val.length ≤ 30000)
    (hqueries_le : queries.val.length ≤ 30000)
    (harr_bounds : ∀ k, k < arr.val.length →
      1 ≤ (arr.val[k]!).val ∧ (arr.val[k]!).val ≤ 1000000000)
    (hquery_bounds : ∀ i, i < queries.val.length →
      (queries.val[i]!).val.length = 2 ∧
      0 ≤ ((queries.val[i]!).val[0]!).val ∧
      ((queries.val[i]!).val[0]!).val ≤ ((queries.val[i]!).val[1]!).val ∧
      ((queries.val[i]!).val[1]!).val < (arr.val.length : Int)), ∀ r, Aegis.XorQueries.xor_queries arr queries = ok r →
      ∀ i j, i < queries.val.length → j < queries.val.length →
        ((queries.val[i]!).val[0]!).val = ((queries.val[j]!).val[0]!).val →
        ((queries.val[i]!).val[1]!).val < ((queries.val[j]!).val[1]!).val →
        bxor (r.val[i]!).val (r.val[j]!).val =
          xorRange arr (((queries.val[i]!).val[1]!).val.toNat + 1)
            (((queries.val[j]!).val[1]!).val.toNat)) := by
  sorry

/-- Whenever the function returns a result r, for all i, j, and k with 0 <= i < len(queries), 0 <= j < len(queries), and 0 <= k < len(queries), if there exist l, m, and n such that 0 <= l <= m < n < len(arr), queries[i][0] = l, queries[i][1] = m, queries[j][0] = m+1, queries[j][1] = n, queries[k][0] = l, and queries[k][1] = n, then r[k] = r[i] XOR r[j].
  Preconditions: len(arr) >= 1 and len(queries) >= 1; len(arr) <= 30000 and len(queries) <= 30000; for every k with 0 <= k < len(arr), 1 <= arr[k] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2 and 0 <= queries[i][0] <= queries[i][1] < len(arr). -/
theorem spec_5
    (arr : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (harr_pos : 1 ≤ arr.val.length)
    (hqueries_pos : 1 ≤ queries.val.length)
    (harr_le : arr.val.length ≤ 30000)
    (hqueries_le : queries.val.length ≤ 30000)
    (harr_bounds : ∀ k, k < arr.val.length →
      1 ≤ (arr.val[k]!).val ∧ (arr.val[k]!).val ≤ 1000000000)
    (hquery_bounds : ∀ i, i < queries.val.length →
      (queries.val[i]!).val.length = 2 ∧
      0 ≤ ((queries.val[i]!).val[0]!).val ∧
      ((queries.val[i]!).val[0]!).val ≤ ((queries.val[i]!).val[1]!).val ∧
      ((queries.val[i]!).val[1]!).val < (arr.val.length : Int)) :
    ∀ r, Aegis.XorQueries.xor_queries arr queries = ok r →
      ∀ i j k, i < queries.val.length → j < queries.val.length →
        k < queries.val.length →
        (∃ l m n : Nat,
          l ≤ m ∧ m < n ∧ n < arr.val.length ∧
          ((queries.val[i]!).val[0]!).val = (l : Int) ∧
          ((queries.val[i]!).val[1]!).val = (m : Int) ∧
          ((queries.val[j]!).val[0]!).val = (m : Int) + 1 ∧
          ((queries.val[j]!).val[1]!).val = (n : Int) ∧
          ((queries.val[k]!).val[0]!).val = (l : Int) ∧
          ((queries.val[k]!).val[1]!).val = (n : Int)) →
        (r.val[k]!).val = bxor (r.val[i]!).val (r.val[j]!).val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
    (harr_pos : 1 ≤ arr.val.length)
    (hqueries_pos : 1 ≤ queries.val.length)
    (harr_le : arr.val.length ≤ 30000)
    (hqueries_le : queries.val.length ≤ 30000)
    (harr_bounds : ∀ k, k < arr.val.length →
      1 ≤ (arr.val[k]!).val ∧ (arr.val[k]!).val ≤ 1000000000)
    (hquery_bounds : ∀ i, i < queries.val.length →
      (queries.val[i]!).val.length = 2 ∧
      0 ≤ ((queries.val[i]!).val[0]!).val ∧
      ((queries.val[i]!).val[0]!).val ≤ ((queries.val[i]!).val[1]!).val ∧
      ((queries.val[i]!).val[1]!).val < (arr.val.length : Int)), ∀ r, Aegis.XorQueries.xor_queries arr queries = ok r →
      ∀ i j k, i < queries.val.length → j < queries.val.length →
        k < queries.val.length →
        (∃ l m n : Nat,
          l ≤ m ∧ m < n ∧ n < arr.val.length ∧
          ((queries.val[i]!).val[0]!).val = (l : Int) ∧
          ((queries.val[i]!).val[1]!).val = (m : Int) ∧
          ((queries.val[j]!).val[0]!).val = (m : Int) + 1 ∧
          ((queries.val[j]!).val[1]!).val = (n : Int) ∧
          ((queries.val[k]!).val[0]!).val = (l : Int) ∧
          ((queries.val[k]!).val[1]!).val = (n : Int)) →
        (r.val[k]!).val = bxor (r.val[i]!).val (r.val[j]!).val) := by
  sorry

/-- Whenever the function returns r on (arr, queries) and r_prime on (arr, queries_prime), for every i with 0 <= i < len(queries), if queries[i] = queries_prime[i], then r[i] = r_prime[i].
  Preconditions: Both (arr, queries) and (arr, queries_prime) are valid inputs: len(arr) >= 1; len(queries) >= 1 and len(queries_prime) >= 1; len(arr) <= 30000 and len(queries) <= 30000 and len(queries_prime) <= 30000; for every k with 0 <= k < len(arr), 1 <= arr[k] <= 1000000000; every query vector in either list has length 2 and endpoints satisfying 0 <= left <= right < len(arr); also len(queries) = len(queries_prime). -/
theorem spec_6
    (arr : Slice Std.I64)
    (queries : Slice (alloc.vec.Vec Std.I64))
    (queries_prime : Slice (alloc.vec.Vec Std.I64))
    (harr_pos : 1 ≤ arr.val.length)
    (hqueries_pos : 1 ≤ queries.val.length)
    (hqueries_prime_pos : 1 ≤ queries_prime.val.length)
    (harr_le : arr.val.length ≤ 30000)
    (hqueries_le : queries.val.length ≤ 30000)
    (hqueries_prime_le : queries_prime.val.length ≤ 30000)
    (harr_bounds : ∀ k, k < arr.val.length →
      1 ≤ (arr.val[k]!).val ∧ (arr.val[k]!).val ≤ 1000000000)
    (hquery_bounds : ∀ i, i < queries.val.length →
      (queries.val[i]!).val.length = 2 ∧
      0 ≤ ((queries.val[i]!).val[0]!).val ∧
      ((queries.val[i]!).val[0]!).val ≤ ((queries.val[i]!).val[1]!).val ∧
      ((queries.val[i]!).val[1]!).val < (arr.val.length : Int))
    (hquery_prime_bounds : ∀ i, i < queries_prime.val.length →
      (queries_prime.val[i]!).val.length = 2 ∧
      0 ≤ ((queries_prime.val[i]!).val[0]!).val ∧
      ((queries_prime.val[i]!).val[0]!).val ≤
        ((queries_prime.val[i]!).val[1]!).val ∧
      ((queries_prime.val[i]!).val[1]!).val < (arr.val.length : Int))
    (hlen : queries.val.length = queries_prime.val.length) :
    ∀ r r', Aegis.XorQueries.xor_queries arr queries = ok r →
      Aegis.XorQueries.xor_queries arr queries_prime = ok r' →
      ∀ i, i < queries.val.length →
        queries.val[i]! = queries_prime.val[i]! → (r.val[i]!).val = (r'.val[i]!).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (queries : Slice (alloc.vec.Vec Std.I64))
    (queries_prime : Slice (alloc.vec.Vec Std.I64))
    (harr_pos : 1 ≤ arr.val.length)
    (hqueries_pos : 1 ≤ queries.val.length)
    (hqueries_prime_pos : 1 ≤ queries_prime.val.length)
    (harr_le : arr.val.length ≤ 30000)
    (hqueries_le : queries.val.length ≤ 30000)
    (hqueries_prime_le : queries_prime.val.length ≤ 30000)
    (harr_bounds : ∀ k, k < arr.val.length →
      1 ≤ (arr.val[k]!).val ∧ (arr.val[k]!).val ≤ 1000000000)
    (hquery_bounds : ∀ i, i < queries.val.length →
      (queries.val[i]!).val.length = 2 ∧
      0 ≤ ((queries.val[i]!).val[0]!).val ∧
      ((queries.val[i]!).val[0]!).val ≤ ((queries.val[i]!).val[1]!).val ∧
      ((queries.val[i]!).val[1]!).val < (arr.val.length : Int))
    (hquery_prime_bounds : ∀ i, i < queries_prime.val.length →
      (queries_prime.val[i]!).val.length = 2 ∧
      0 ≤ ((queries_prime.val[i]!).val[0]!).val ∧
      ((queries_prime.val[i]!).val[0]!).val ≤
        ((queries_prime.val[i]!).val[1]!).val ∧
      ((queries_prime.val[i]!).val[1]!).val < (arr.val.length : Int))
    (hlen : queries.val.length = queries_prime.val.length), ∀ r r', Aegis.XorQueries.xor_queries arr queries = ok r →
      Aegis.XorQueries.xor_queries arr queries_prime = ok r' →
      ∀ i, i < queries.val.length →
        queries.val[i]! = queries_prime.val[i]! → (r.val[i]!).val = (r'.val[i]!).val) := by
  sorry

/-- Whenever the function returns r on (arr, queries) and r_prime on (arr_prime, queries), for every i with 0 <= i < len(queries), if arr[j] = arr_prime[j] for every j with queries[i][0] <= j <= queries[i][1], then r[i] = r_prime[i].
  Preconditions: Both (arr, queries) and (arr_prime, queries) are valid inputs: len(arr) >= 1 and len(arr_prime) >= 1; len(queries) >= 1; len(arr) <= 30000 and len(arr_prime) <= 30000 and len(queries) <= 30000; for every k with 0 <= k < len(arr), 1 <= arr[k] <= 1000000000; for every k with 0 <= k < len(arr_prime), 1 <= arr_prime[k] <= 1000000000; every query vector has length 2 and endpoints satisfying 0 <= left <= right < len(arr) and 0 <= left <= right < len(arr_prime); also len(arr) = len(arr_prime). -/
theorem spec_7
    (arr : Slice Std.I64) (arr_prime : Slice Std.I64)
    (queries : Slice (alloc.vec.Vec Std.I64))
    (harr_pos : 1 ≤ arr.val.length)
    (harr_prime_pos : 1 ≤ arr_prime.val.length)
    (hqueries_pos : 1 ≤ queries.val.length)
    (harr_le : arr.val.length ≤ 30000)
    (harr_prime_le : arr_prime.val.length ≤ 30000)
    (hqueries_le : queries.val.length ≤ 30000)
    (harr_bounds : ∀ k, k < arr.val.length →
      1 ≤ (arr.val[k]!).val ∧ (arr.val[k]!).val ≤ 1000000000)
    (harr_prime_bounds : ∀ k, k < arr_prime.val.length →
      1 ≤ (arr_prime.val[k]!).val ∧ (arr_prime.val[k]!).val ≤ 1000000000)
    (hquery_bounds : ∀ i, i < queries.val.length →
      (queries.val[i]!).val.length = 2 ∧
      0 ≤ ((queries.val[i]!).val[0]!).val ∧
      ((queries.val[i]!).val[0]!).val ≤ ((queries.val[i]!).val[1]!).val ∧
      ((queries.val[i]!).val[1]!).val < (arr.val.length : Int) ∧
      ((queries.val[i]!).val[1]!).val < (arr_prime.val.length : Int))
    (hlen : arr.val.length = arr_prime.val.length) :
    ∀ r r', Aegis.XorQueries.xor_queries arr queries = ok r →
      Aegis.XorQueries.xor_queries arr_prime queries = ok r' →
      ∀ i, i < queries.val.length →
        (∀ j : Nat, ((queries.val[i]!).val[0]!).val ≤ (j : Int) →
          (j : Int) ≤ ((queries.val[i]!).val[1]!).val →
          (arr.val[j]!).val = (arr_prime.val[j]!).val) →
        (r.val[i]!).val = (r'.val[i]!).val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice Std.I64) (arr_prime : Slice Std.I64)
    (queries : Slice (alloc.vec.Vec Std.I64))
    (harr_pos : 1 ≤ arr.val.length)
    (harr_prime_pos : 1 ≤ arr_prime.val.length)
    (hqueries_pos : 1 ≤ queries.val.length)
    (harr_le : arr.val.length ≤ 30000)
    (harr_prime_le : arr_prime.val.length ≤ 30000)
    (hqueries_le : queries.val.length ≤ 30000)
    (harr_bounds : ∀ k, k < arr.val.length →
      1 ≤ (arr.val[k]!).val ∧ (arr.val[k]!).val ≤ 1000000000)
    (harr_prime_bounds : ∀ k, k < arr_prime.val.length →
      1 ≤ (arr_prime.val[k]!).val ∧ (arr_prime.val[k]!).val ≤ 1000000000)
    (hquery_bounds : ∀ i, i < queries.val.length →
      (queries.val[i]!).val.length = 2 ∧
      0 ≤ ((queries.val[i]!).val[0]!).val ∧
      ((queries.val[i]!).val[0]!).val ≤ ((queries.val[i]!).val[1]!).val ∧
      ((queries.val[i]!).val[1]!).val < (arr.val.length : Int) ∧
      ((queries.val[i]!).val[1]!).val < (arr_prime.val.length : Int))
    (hlen : arr.val.length = arr_prime.val.length), ∀ r r', Aegis.XorQueries.xor_queries arr queries = ok r →
      Aegis.XorQueries.xor_queries arr_prime queries = ok r' →
      ∀ i, i < queries.val.length →
        (∀ j : Nat, ((queries.val[i]!).val[0]!).val ≤ (j : Int) →
          (j : Int) ≤ ((queries.val[i]!).val[1]!).val →
          (arr.val[j]!).val = (arr_prime.val[j]!).val) →
        (r.val[i]!).val = (r'.val[i]!).val) := by
  sorry

end AegisSpec.XorQueries
