import Aegis.MaxChunksToSorted.Code.Funs

/-!
# Specifications of `Aegis.MaxChunksToSorted.max_chunks_to_sorted`

LeetCode problem `max-chunks-to-make-sorted`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxChunksToSorted

namespace AegisSpec.MaxChunksToSorted

def vals (arr : Slice Std.I64) : List ℤ := arr.val.map (fun x => x.val)

def get (arr : Slice Std.I64) (i : ℕ) : ℤ := (vals arr).getD i 0

def rangeZ (n : ℕ) : List ℤ := (List.range n).map (fun k => (k : ℤ))

def insertZ (x : ℤ) : List ℤ → List ℤ
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertZ x ys

def sortZ : List ℤ → List ℤ
  | [] => []
  | x :: xs => insertZ x (sortZ xs)

def chunk (l : List ℤ) (c : ℕ → ℕ) (t : ℕ) : List ℤ :=
  (l.drop (c t)).take (c (t + 1) - c t)

def concatSorted (l : List ℤ) (c : ℕ → ℕ) : ℕ → List ℤ
  | 0 => []
  | t + 1 => concatSorted l c t ++ sortZ (chunk l c t)

def IsCutSet (n k : ℕ) (c : ℕ → ℕ) : Prop :=
  1 ≤ k ∧ c 0 = 0 ∧ c k = n ∧ ∀ t, t < k → c t < c (t + 1)

def IsValidSplit (l : List ℤ) (k : ℕ) (c : ℕ → ℕ) : Prop :=
  IsCutSet l.length k c ∧ concatSorted l c k = rangeZ l.length

def prefixMax (l : List ℤ) (i : ℕ) : ℤ := (l.take (i + 1)).foldr (fun a b => max a b) 0

def canonicalCuts (l : List ℤ) : List ℕ :=
  0 :: (((List.range (l.length - 1)).filter (fun i => prefixMax l i = (i : ℤ))).map
    (fun i => i + 1) ++ [l.length])

def canonicalCutsFun (l : List ℤ) : ℕ → ℕ := fun t => (canonicalCuts l).getD t l.length

def canonicalChunks (l : List ℤ) : ℕ := (canonicalCuts l).length - 1

def countPrefixMaxHits (arr : Slice Std.I64) : ℕ :=
  ((List.range arr.val.length).filter
    (fun i => prefixMax (vals arr) i = (i : ℤ))).length

/-- The function returns a result r (it does not fail), and r is the largest integer k >= 1 for which there exist cut indices 0 = c_0 < c_1 < ... < c_k = n such that, after sorting each contiguous segment arr[c_{j-1}], arr[c_{j-1}+1], ..., arr[c_j - 1] (for j = 1, ..., k) in nondecreasing order and concatenating the sorted segments in this order, the resulting sequence of length n is exactly 0, 1, ..., n-1.
  Preconditions: Let n = len(arr). 1 <= n <= 10; for every i with 0 <= i < n, 0 <= arr[i] < n; for every i, j with 0 <= i < j < n, arr[i] != arr[j]. -/
theorem spec_1 (arr : Slice Std.I64)
    (hpos : 1 ≤ arr.val.length) (hle : arr.val.length ≤ 10)
    (hrange : ∀ i, i < arr.val.length → 0 ≤ get arr i ∧ get arr i < (arr.val.length : ℤ))
    (hdistinct : ∀ i j, i < j → j < arr.val.length → get arr i ≠ get arr j) :
    ∃ r : Std.I64,
      max_chunks_to_sorted arr = ok r ∧
      1 ≤ r.val ∧
      (∃ k c, IsValidSplit (vals arr) k c ∧ (k : ℤ) = r.val) ∧
      (∀ k c, IsValidSplit (vals arr) k c → (k : ℤ) ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hpos : 1 ≤ arr.val.length) (hle : arr.val.length ≤ 10)
    (hrange : ∀ i, i < arr.val.length → 0 ≤ get arr i ∧ get arr i < (arr.val.length : ℤ))
    (hdistinct : ∀ i j, i < j → j < arr.val.length → get arr i ≠ get arr j), ∃ r : Std.I64,
      max_chunks_to_sorted arr = ok r ∧
      1 ≤ r.val ∧
      (∃ k c, IsValidSplit (vals arr) k c ∧ (k : ℤ) = r.val) ∧
      (∀ k c, IsValidSplit (vals arr) k c → (k : ℤ) ≤ r.val)) := by
  sorry

/-- The function returns a result r; in particular, for every input satisfying the preconditions it does not overflow, access out of bounds, or panic.
  Preconditions: Let n = len(arr). 1 <= n <= 10; for every i with 0 <= i < n, 0 <= arr[i] < n; for every i, j with 0 <= i < j < n, arr[i] != arr[j]. -/
theorem spec_2 (arr : Slice Std.I64)
    (hpos : 1 ≤ arr.val.length) (hle : arr.val.length ≤ 10)
    (hrange : ∀ i, i < arr.val.length → 0 ≤ get arr i ∧ get arr i < (arr.val.length : ℤ))
    (hdistinct : ∀ i j, i < j → j < arr.val.length → get arr i ≠ get arr j) :
    ∃ r : Std.I64, max_chunks_to_sorted arr = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hpos : 1 ≤ arr.val.length) (hle : arr.val.length ≤ 10)
    (hrange : ∀ i, i < arr.val.length → 0 ≤ get arr i ∧ get arr i < (arr.val.length : ℤ))
    (hdistinct : ∀ i j, i < j → j < arr.val.length → get arr i ≠ get arr j), ∃ r : Std.I64, max_chunks_to_sorted arr = ok r) := by
  sorry

/-- Whenever the function returns a result r, we have 1 <= r <= n.
  Preconditions: Let n = len(arr). 1 <= n <= 10; for every i with 0 <= i < n, 0 <= arr[i] < n; for every i, j with 0 <= i < j < n, arr[i] != arr[j]. -/
theorem spec_3 (arr : Slice Std.I64)
    (hpos : 1 ≤ arr.val.length) (hle : arr.val.length ≤ 10)
    (hrange : ∀ i, i < arr.val.length → 0 ≤ get arr i ∧ get arr i < (arr.val.length : ℤ))
    (hdistinct : ∀ i j, i < j → j < arr.val.length → get arr i ≠ get arr j) :
    ∀ r : Std.I64, max_chunks_to_sorted arr = ok r →
      1 ≤ r.val ∧ r.val ≤ (arr.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hpos : 1 ≤ arr.val.length) (hle : arr.val.length ≤ 10)
    (hrange : ∀ i, i < arr.val.length → 0 ≤ get arr i ∧ get arr i < (arr.val.length : ℤ))
    (hdistinct : ∀ i j, i < j → j < arr.val.length → get arr i ≠ get arr j), ∀ r : Std.I64, max_chunks_to_sorted arr = ok r →
      1 ≤ r.val ∧ r.val ≤ (arr.val.length : ℤ)) := by
  sorry

/-- The function returns r = n.
  Preconditions: Let n = len(arr). 1 <= n <= 10; for every i with 0 <= i < n, 0 <= arr[i] < n; for every i, j with 0 <= i < j < n, arr[i] != arr[j]; and for every i with 0 <= i < n, arr[i] = i. -/
theorem spec_4 (arr : Slice Std.I64)
    (hpos : 1 ≤ arr.val.length) (hle : arr.val.length ≤ 10)
    (hrange : ∀ i, i < arr.val.length → 0 ≤ get arr i ∧ get arr i < (arr.val.length : ℤ))
    (hdistinct : ∀ i j, i < j → j < arr.val.length → get arr i ≠ get arr j)
    (hident : ∀ i, i < arr.val.length → get arr i = (i : ℤ)) :
    ∃ r : Std.I64, max_chunks_to_sorted arr = ok r ∧ r.val = (arr.val.length : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hpos : 1 ≤ arr.val.length) (hle : arr.val.length ≤ 10)
    (hrange : ∀ i, i < arr.val.length → 0 ≤ get arr i ∧ get arr i < (arr.val.length : ℤ))
    (hdistinct : ∀ i j, i < j → j < arr.val.length → get arr i ≠ get arr j)
    (hident : ∀ i, i < arr.val.length → get arr i = (i : ℤ)), ∃ r : Std.I64, max_chunks_to_sorted arr = ok r ∧ r.val = (arr.val.length : ℤ)) := by
  sorry

/-- The function returns r = 1.
  Preconditions: Let n = len(arr). 1 <= n <= 10; for every i with 0 <= i < n, 0 <= arr[i] < n; for every i, j with 0 <= i < j < n, arr[i] != arr[j]; and for every i with 0 <= i < n, arr[i] = n - 1 - i. -/
theorem spec_5 (arr : Slice Std.I64)
    (hpos : 1 ≤ arr.val.length) (hle : arr.val.length ≤ 10)
    (hrange : ∀ i, i < arr.val.length → 0 ≤ get arr i ∧ get arr i < (arr.val.length : ℤ))
    (hdistinct : ∀ i j, i < j → j < arr.val.length → get arr i ≠ get arr j)
    (hrev : ∀ i, i < arr.val.length → get arr i = (arr.val.length : ℤ) - 1 - (i : ℤ)) :
    ∃ r : Std.I64, max_chunks_to_sorted arr = ok r ∧ r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hpos : 1 ≤ arr.val.length) (hle : arr.val.length ≤ 10)
    (hrange : ∀ i, i < arr.val.length → 0 ≤ get arr i ∧ get arr i < (arr.val.length : ℤ))
    (hdistinct : ∀ i j, i < j → j < arr.val.length → get arr i ≠ get arr j)
    (hrev : ∀ i, i < arr.val.length → get arr i = (arr.val.length : ℤ) - 1 - (i : ℤ)), ∃ r : Std.I64, max_chunks_to_sorted arr = ok r ∧ r.val = 1) := by
  sorry

/-- Whenever the function returns r, for every valid split of arr into k chunks (i.e., cut indices 0 = c_0 < ... < c_k = n such that sorting the segments arr[c_{t-1}..c_t-1] and concatenating gives 0,1,...,n-1), we have k <= r.
  Preconditions: Let n = len(arr). 1 <= n <= 10; for every i with 0 <= i < n, 0 <= arr[i] < n; for every i, j with 0 <= i < j < n, arr[i] != arr[j]. -/
theorem spec_6 (arr : Slice Std.I64)
    (hpos : 1 ≤ arr.val.length) (hle : arr.val.length ≤ 10)
    (hrange : ∀ i, i < arr.val.length → 0 ≤ get arr i ∧ get arr i < (arr.val.length : ℤ))
    (hdistinct : ∀ i j, i < j → j < arr.val.length → get arr i ≠ get arr j) :
    ∀ r : Std.I64, max_chunks_to_sorted arr = ok r →
      ∀ k c, IsValidSplit (vals arr) k c → (k : ℤ) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hpos : 1 ≤ arr.val.length) (hle : arr.val.length ≤ 10)
    (hrange : ∀ i, i < arr.val.length → 0 ≤ get arr i ∧ get arr i < (arr.val.length : ℤ))
    (hdistinct : ∀ i j, i < j → j < arr.val.length → get arr i ≠ get arr j), ∀ r : Std.I64, max_chunks_to_sorted arr = ok r →
      ∀ k c, IsValidSplit (vals arr) k c → (k : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns r, there exists a valid split of arr into exactly r chunks (using the definition of valid split by cut indices and sorting each contiguous segment).
  Preconditions: Let n = len(arr). 1 <= n <= 10; for every i with 0 <= i < n, 0 <= arr[i] < n; for every i, j with 0 <= i < j < n, arr[i] != arr[j]. -/
theorem spec_7 (arr : Slice Std.I64)
    (hpos : 1 ≤ arr.val.length) (hle : arr.val.length ≤ 10)
    (hrange : ∀ i, i < arr.val.length → 0 ≤ get arr i ∧ get arr i < (arr.val.length : ℤ))
    (hdistinct : ∀ i j, i < j → j < arr.val.length → get arr i ≠ get arr j) :
    ∀ r : Std.I64, max_chunks_to_sorted arr = ok r →
      ∃ k c, IsValidSplit (vals arr) k c ∧ (k : ℤ) = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hpos : 1 ≤ arr.val.length) (hle : arr.val.length ≤ 10)
    (hrange : ∀ i, i < arr.val.length → 0 ≤ get arr i ∧ get arr i < (arr.val.length : ℤ))
    (hdistinct : ∀ i j, i < j → j < arr.val.length → get arr i ≠ get arr j), ∀ r : Std.I64, max_chunks_to_sorted arr = ok r →
      ∃ k c, IsValidSplit (vals arr) k c ∧ (k : ℤ) = r.val) := by
  sorry

/-- Whenever the function returns r, the split whose cut indices are 0, n, and every integer i + 1 with 0 <= i < n - 1 and max{arr[0], ..., arr[i]} = i is a valid split with exactly r chunks.
  Preconditions: Let n = len(arr). 1 <= n <= 10; for every i with 0 <= i < n, 0 <= arr[i] < n; for every i, j with 0 <= i < j < n, arr[i] != arr[j]. -/
theorem spec_8 (arr : Slice Std.I64)
    (hpos : 1 ≤ arr.val.length) (hle : arr.val.length ≤ 10)
    (hrange : ∀ i, i < arr.val.length → 0 ≤ get arr i ∧ get arr i < (arr.val.length : ℤ))
    (hdistinct : ∀ i j, i < j → j < arr.val.length → get arr i ≠ get arr j) :
    ∀ r : Std.I64, max_chunks_to_sorted arr = ok r →
      IsValidSplit (vals arr) (canonicalChunks (vals arr)) (canonicalCutsFun (vals arr)) ∧
        (canonicalChunks (vals arr) : ℤ) = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hpos : 1 ≤ arr.val.length) (hle : arr.val.length ≤ 10)
    (hrange : ∀ i, i < arr.val.length → 0 ≤ get arr i ∧ get arr i < (arr.val.length : ℤ))
    (hdistinct : ∀ i j, i < j → j < arr.val.length → get arr i ≠ get arr j), ∀ r : Std.I64, max_chunks_to_sorted arr = ok r →
      IsValidSplit (vals arr) (canonicalChunks (vals arr)) (canonicalCutsFun (vals arr)) ∧
        (canonicalChunks (vals arr) : ℤ) = r.val) := by
  sorry

/-- Whenever the function returns r, r equals the number of integers i with 0 <= i < n such that max{arr[0], arr[1], ..., arr[i]} = i.
  Preconditions: Let n = len(arr). 1 <= n <= 10; for every i with 0 <= i < n, 0 <= arr[i] < n; for every i, j with 0 <= i < j < n, arr[i] != arr[j]. -/
theorem spec_9 (arr : Slice Std.I64)
    (hpos : 1 ≤ arr.val.length) (hle : arr.val.length ≤ 10)
    (hrange : ∀ i, i < arr.val.length → 0 ≤ get arr i ∧ get arr i < (arr.val.length : ℤ))
    (hdistinct : ∀ i j, i < j → j < arr.val.length → get arr i ≠ get arr j) :
    ∀ r : Std.I64, max_chunks_to_sorted arr = ok r →
      r.val = (countPrefixMaxHits arr : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hpos : 1 ≤ arr.val.length) (hle : arr.val.length ≤ 10)
    (hrange : ∀ i, i < arr.val.length → 0 ≤ get arr i ∧ get arr i < (arr.val.length : ℤ))
    (hdistinct : ∀ i j, i < j → j < arr.val.length → get arr i ≠ get arr j), ∀ r : Std.I64, max_chunks_to_sorted arr = ok r →
      r.val = (countPrefixMaxHits arr : ℤ)) := by
  sorry

end AegisSpec.MaxChunksToSorted
