import Aegis.MaxChunksToSorted.Code.Funs

/-!
# Specifications of `Aegis.MaxChunksToSorted.max_chunks_to_sorted`

LeetCode problem `max-chunks-to-make-sorted-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxChunksToSorted

def value (arr : Slice Std.I64) (i : ℕ) : ℤ := ((arr.val[i]?).map (·.val)).getD 0

def values (arr : Slice Std.I64) : List ℤ := arr.val.map (·.val)

def rangeMax (arr : Slice Std.I64) (lo hi : ℕ) : ℤ :=
  (((List.range hi).drop lo).map (value arr)).max?.getD 0

def rangeMin (arr : Slice Std.I64) (lo hi : ℕ) : ℤ :=
  (((List.range hi).drop lo).map (value arr)).min?.getD 0

def sortedList (l : List ℤ) : List ℤ := l.mergeSort (· ≤ ·)

def wholeSort (arr : Slice Std.I64) : List ℤ := sortedList (values arr)

def IsPartition (n k : ℕ) (b : Fin (k + 1) → ℕ) : Prop :=
  b ⟨0, Nat.succ_pos k⟩ = 0 ∧ b ⟨k, Nat.lt_succ_self k⟩ = n ∧ StrictMono b

def blockVals (arr : Slice Std.I64) (k : ℕ) (b : Fin (k + 1) → ℕ) (j : Fin k) : List ℤ :=
  (values arr).drop (b j.castSucc) |>.take (b j.succ - b j.castSucc)

def chunkSortConcat (arr : Slice Std.I64) (k : ℕ) (b : Fin (k + 1) → ℕ) : List ℤ :=
  (List.finRange k).flatMap (fun j => sortedList (blockVals arr k b j))

def IsValidPartition (arr : Slice Std.I64) (k : ℕ) (b : Fin (k + 1) → ℕ) : Prop :=
  IsPartition arr.val.length k b ∧ chunkSortConcat arr k b = wholeSort arr

abbrev IsSplitPoint (arr : Slice Std.I64) (m : ℕ) : Prop :=
  rangeMax arr 0 m ≤ rangeMin arr m arr.val.length

def cutCount (arr : Slice Std.I64) : ℕ :=
  ((List.range (arr.val.length - 1)).filter (fun i => decide (IsSplitPoint arr (i + 1)))).length

def ascentCount (arr : Slice Std.I64) : ℕ :=
  ((List.range (arr.val.length - 1)).filter
    (fun i => decide (value arr i ≤ value arr (i + 1)))).length

def IsNondecreasing (arr : Slice Std.I64) : Prop :=
  (values arr).Pairwise (· ≤ ·)

def IsShift (arr arr' : Slice Std.I64) (c : ℤ) : Prop :=
  arr'.val.length = arr.val.length ∧ ∀ i, i < arr.val.length → value arr' i = value arr i + c

/-- The function returns a result r and, interpreting r as an integer, r is the largest k such that there exist indices 0 = b_0 < b_1 < ... < b_k = n for which the concatenation, for j = 0,...,k-1, of the nondecreasing sorts of the nonempty blocks arr[b_j],...,arr[b_{j+1}-1] equals the nondecreasing sort of the whole array arr.
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 2000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000000. -/
theorem spec_1 (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000) :
    ∃ r : Std.I64,
      Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r ∧
        (∃ (k : ℕ) (b : Fin (k + 1) → ℕ),
          r.val = (k : ℤ) ∧ IsValidPartition arr k b) ∧
        (∀ (k : ℕ) (b : Fin (k + 1) → ℕ),
          IsValidPartition arr k b → (k : ℤ) ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000), ∃ r : Std.I64,
      Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r ∧
        (∃ (k : ℕ) (b : Fin (k + 1) → ℕ),
          r.val = (k : ℤ) ∧ IsValidPartition arr k b) ∧
        (∀ (k : ℕ) (b : Fin (k + 1) → ℕ),
          IsValidPartition arr k b → (k : ℤ) ≤ r.val)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail (no overflow, out-of-bounds access, or panic).
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 2000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000000. -/
theorem spec_2 (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000) :
    ∃ r : Std.I64, Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000), ∃ r : Std.I64, Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r) := by
  sorry

/-- Whenever the function returns a result r, interpreting r as an integer, 1 <= r <= n.
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 2000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000000. -/
theorem spec_3 (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    {r : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r) :
    1 ≤ r.val ∧ r.val ≤ (arr.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    {r : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r), 1 ≤ r.val ∧ r.val ≤ (arr.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, there exist indices 0 = b_0 < b_1 < ... < b_r = n (with r interpreted as a nonnegative integer) such that the concatenation of the nondecreasing sorts of the blocks arr[b_j],...,arr[b_{j+1}-1] for j = 0,...,r-1 equals the nondecreasing sort of arr.
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 2000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000000. -/
theorem spec_4 (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    {r : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r) :
    ∃ (k : ℕ) (b : Fin (k + 1) → ℕ), r.val = (k : ℤ) ∧ IsValidPartition arr k b := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    {r : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r), ∃ (k : ℕ) (b : Fin (k + 1) → ℕ), r.val = (k : ℤ) ∧ IsValidPartition arr k b) := by
  sorry

/-- Whenever the function returns a result r, for every k >= 0 and every sequence 0 = b_0 < b_1 < ... < b_k = n, if the concatenation of the nondecreasing sorts of the blocks arr[b_j],...,arr[b_{j+1}-1] for j = 0,...,k-1 equals the nondecreasing sort of arr, then k <= r (with r interpreted as an integer).
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 2000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000000. -/
theorem spec_5 (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    {r : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r) :
    ∀ (k : ℕ) (b : Fin (k + 1) → ℕ),
      IsValidPartition arr k b → (k : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    {r : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r), ∀ (k : ℕ) (b : Fin (k + 1) → ℕ),
      IsValidPartition arr k b → (k : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, let C be the number of indices i with 0 <= i < n-1 such that max{arr[j] | 0 <= j <= i} <= min{arr[j] | i < j < n}. Then r = 1 + C (with r interpreted as an integer). For n = 1, C = 0.
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 2000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000000. -/
theorem spec_6 (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    {r : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r) :
    r.val = 1 + (cutCount arr : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    {r : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r), r.val = 1 + (cutCount arr : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = n if and only if arr is nondecreasing, i.e. arr[0] <= arr[1] <= ... <= arr[n-1].
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 2000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000000. -/
theorem spec_7 (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    {r : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r) :
    r.val = (arr.val.length : ℤ) ↔ IsNondecreasing arr := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    {r : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r), r.val = (arr.val.length : ℤ) ↔ IsNondecreasing arr) := by
  sorry

/-- Whenever the function returns a result r, r = 1.
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 2000, for every i with 0 <= i < n, 0 <= arr[i] <= 100000000, and additionally n >= 2 and arr[0] > arr[n-1]. -/
theorem spec_8 (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    (hn_two : 2 ≤ arr.val.length)
    (hgt : value arr (arr.val.length - 1) < value arr 0)
    {r : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r) :
    r.val = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    (hn_two : 2 ≤ arr.val.length)
    (hgt : value arr (arr.val.length - 1) < value arr 0)
    {r : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r), r.val = 1) := by
  sorry

/-- Let r be the result returned on arr and r' the result returned on arr'. Then r = r' (both interpreted as integers).
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 2000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000000. Let c be any integer such that 0 <= arr[i] + c <= 100000000 for every i, and let arr' be the length-n slice with arr'[i] = arr[i] + c; arr' also satisfies the problem constraints. -/
theorem spec_9 (arr arr' : Slice Std.I64) (c : ℤ)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    (hc : ∀ i, i < arr.val.length →
      0 ≤ value arr i + c ∧ value arr i + c ≤ 100000000)
    (hshift : IsShift arr arr' c)
    (hn'_pos : 1 ≤ arr'.val.length) (hn'_max : arr'.val.length ≤ 2000)
    (hbound' : ∀ i, i < arr'.val.length →
      0 ≤ value arr' i ∧ value arr' i ≤ 100000000)
    {r r' : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r)
    (hr' : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr arr' : Slice Std.I64) (c : ℤ)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    (hc : ∀ i, i < arr.val.length →
      0 ≤ value arr i + c ∧ value arr i + c ≤ 100000000)
    (hshift : IsShift arr arr' c)
    (hn'_pos : 1 ≤ arr'.val.length) (hn'_max : arr'.val.length ≤ 2000)
    (hbound' : ∀ i, i < arr'.val.length →
      0 ≤ value arr' i ∧ value arr' i ≤ 100000000)
    {r r' : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r)
    (hr' : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr' = ok r'), r.val = r'.val) := by
  sorry

/-- Let r be the result returned on arr and r' the result returned on arr'. Then r' = r + 1 (both interpreted as integers).
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 2000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000000. Let x be an integer with max(arr) <= x <= 100000000, and suppose n+1 <= 2000. Let arr' be the length-(n+1) slice with arr'[i] = arr[i] for i < n and arr'[n] = x; arr' also satisfies the problem constraints. -/
theorem spec_10 (arr arr' : Slice Std.I64) (x : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    (hx_le : x.val ≤ 100000000)
    (hx_ge : ∀ i, i < arr.val.length → value arr i ≤ x.val)
    (hn_succ : arr.val.length + 1 ≤ 2000)
    (happend : arr'.val = arr.val ++ [x])
    (hn'_pos : 1 ≤ arr'.val.length) (hn'_max : arr'.val.length ≤ 2000)
    (hbound' : ∀ i, i < arr'.val.length →
      0 ≤ value arr' i ∧ value arr' i ≤ 100000000)
    {r r' : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r)
    (hr' : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr' = ok r') :
    r'.val = r.val + 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr arr' : Slice Std.I64) (x : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    (hx_le : x.val ≤ 100000000)
    (hx_ge : ∀ i, i < arr.val.length → value arr i ≤ x.val)
    (hn_succ : arr.val.length + 1 ≤ 2000)
    (happend : arr'.val = arr.val ++ [x])
    (hn'_pos : 1 ≤ arr'.val.length) (hn'_max : arr'.val.length ≤ 2000)
    (hbound' : ∀ i, i < arr'.val.length →
      0 ≤ value arr' i ∧ value arr' i ≤ 100000000)
    {r r' : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r)
    (hr' : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr' = ok r'), r'.val = r.val + 1) := by
  sorry

/-- Whenever the function returns a result r, let D be the number of indices i with 0 <= i < n-1 and arr[i] <= arr[i+1]. Then r <= 1 + D (with r interpreted as an integer).
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 2000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000000. -/
theorem spec_11 (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    {r : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r) :
    r.val ≤ 1 + (ascentCount arr : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    {r : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r), r.val ≤ 1 + (ascentCount arr : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, for every valid partition 0 = b_0 < b_1 < ... < b_r = n into exactly r chunks whose chunkwise nondecreasing sorts concatenate to the nondecreasing sort of arr, every internal boundary b_j with 1 <= j <= r-1 satisfies max{arr[t] | 0 <= t < b_j} <= min{arr[t] | b_j <= t < n}.
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 2000 and, for every i with 0 <= i < n, 0 <= arr[i] <= 100000000. -/
theorem spec_12 (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    {r : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r) :
    ∀ (k : ℕ) (b : Fin (k + 1) → ℕ),
      r.val = (k : ℤ) → IsValidPartition arr k b →
        ∀ j : Fin (k + 1), 1 ≤ j.val → j.val < k → IsSplitPoint arr (b j) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_max : arr.val.length ≤ 2000)
    (hbound : ∀ i, i < arr.val.length →
      0 ≤ value arr i ∧ value arr i ≤ 100000000)
    {r : Std.I64}
    (hr : Aegis.MaxChunksToSorted.max_chunks_to_sorted arr = ok r), ∀ (k : ℕ) (b : Fin (k + 1) → ℕ),
      r.val = (k : ℤ) → IsValidPartition arr k b →
        ∀ j : Fin (k + 1), 1 ≤ j.val → j.val < k → IsSplitPoint arr (b j)) := by
  sorry

end AegisSpec.MaxChunksToSorted
