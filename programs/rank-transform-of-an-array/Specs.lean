import Aegis.ArrayRankTransform.Code.Funs

/-!
# Specifications of `Aegis.ArrayRankTransform.array_rank_transform`

LeetCode problem `rank-transform-of-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.ArrayRankTransform

  namespace AegisSpec.ArrayRankTransform

  def valAt (l : List Std.I64) (i : Nat) : Int :=
    ((l[i]?).map (fun x => x.val)).getD 0

  def distinctValues (l : List Std.I64) : List Int :=
    (l.map (fun x => x.val)).dedup

  def numDistinct (l : List Std.I64) : Nat :=
    (distinctValues l).length

  def numDistinctBelow (l : List Std.I64) (x : Int) : Nat :=
    ((distinctValues l).filter (fun v => v < x)).length

  def OccursIn (l : List Std.I64) (v : Int) : Prop :=
    ∃ j, j < l.length ∧ valAt l j = v

  def IsMinAt (l : List Std.I64) (i : Nat) : Prop :=
    ∀ j, j < l.length → valAt l i ≤ valAt l j

  def IsMaxAt (l : List Std.I64) (i : Nat) : Prop :=
    ∀ j, j < l.length → valAt l j ≤ valAt l i

  def IsShift (l l' : List Std.I64) (c : Int) : Prop :=
    l'.length = l.length ∧ ∀ i, i < l.length → valAt l' i = valAt l i + c

  /-- Whenever the function returns a result r, len(r) = len(arr) and, for every i with 0 <= i < len(arr), r[i] = 1 + N_i, where N_i is the number of distinct integers v such that v occurs in arr (that is, there exists j with 0 <= j < len(arr) and arr[j] = v) and v < arr[i]. In words, r[i] is one plus the number of distinct values in arr that are strictly smaller than arr[i].
    Preconditions: 0 <= len(arr) <= 100000 and for every i with 0 <= i < len(arr), -1000000000 <= arr[i] <= 1000000000. -/
  theorem spec_1 (arr : Slice Std.I64)
      (hlen : arr.val.length ≤ 100000)
      (hbound : ∀ i, i < arr.val.length →
        -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
        r.val.length = arr.val.length ∧
          ∀ i, i < arr.val.length →
            valAt r.val i = 1 + (numDistinctBelow arr.val (valAt arr.val i) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : arr.val.length ≤ 100000)
        (hbound : ∀ i, i < arr.val.length →
          -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
          r.val.length = arr.val.length ∧
            ∀ i, i < arr.val.length →
              valAt r.val i = 1 + (numDistinctBelow arr.val (valAt arr.val i) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(arr).
    Preconditions: 0 <= len(arr) <= 100000 and for every i with 0 <= i < len(arr), -1000000000 <= arr[i] <= 1000000000. -/
  theorem spec_2 (arr : Slice Std.I64)
      (hlen : arr.val.length ≤ 100000)
      (hbound : ∀ i, i < arr.val.length →
        -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
        r.val.length = arr.val.length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : arr.val.length ≤ 100000)
        (hbound : ∀ i, i < arr.val.length →
          -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
          r.val.length = arr.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every i, j with 0 <= i < len(arr) and 0 <= j < len(arr), if arr[i] = arr[j] then r[i] = r[j].
    Preconditions: 0 <= len(arr) <= 100000 and for every i with 0 <= i < len(arr), -1000000000 <= arr[i] <= 1000000000. -/
  theorem spec_3 (arr : Slice Std.I64)
      (hlen : arr.val.length ≤ 100000)
      (hbound : ∀ i, i < arr.val.length →
        -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
        ∀ i j, i < arr.val.length → j < arr.val.length →
          valAt arr.val i = valAt arr.val j → valAt r.val i = valAt r.val j := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : arr.val.length ≤ 100000)
        (hbound : ∀ i, i < arr.val.length →
          -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
          ∀ i j, i < arr.val.length → j < arr.val.length →
            valAt arr.val i = valAt arr.val j → valAt r.val i = valAt r.val j) := by
    sorry

  /-- Whenever the function returns a result r, for every i, j with 0 <= i < len(arr) and 0 <= j < len(arr), if arr[i] != arr[j] then r[i] != r[j].
    Preconditions: 0 <= len(arr) <= 100000 and for every i with 0 <= i < len(arr), -1000000000 <= arr[i] <= 1000000000. -/
  theorem spec_4 (arr : Slice Std.I64)
      (hlen : arr.val.length ≤ 100000)
      (hbound : ∀ i, i < arr.val.length →
        -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
        ∀ i j, i < arr.val.length → j < arr.val.length →
          valAt arr.val i ≠ valAt arr.val j → valAt r.val i ≠ valAt r.val j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : arr.val.length ≤ 100000)
        (hbound : ∀ i, i < arr.val.length →
          -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
          ∀ i j, i < arr.val.length → j < arr.val.length →
            valAt arr.val i ≠ valAt arr.val j → valAt r.val i ≠ valAt r.val j) := by
    sorry

  /-- Whenever the function returns a result r, for every i, j with 0 <= i < len(arr) and 0 <= j < len(arr), if arr[i] < arr[j] then r[i] < r[j].
    Preconditions: 0 <= len(arr) <= 100000 and for every i with 0 <= i < len(arr), -1000000000 <= arr[i] <= 1000000000. -/
  theorem spec_5 (arr : Slice Std.I64)
      (hlen : arr.val.length ≤ 100000)
      (hbound : ∀ i, i < arr.val.length →
        -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
        ∀ i j, i < arr.val.length → j < arr.val.length →
          valAt arr.val i < valAt arr.val j → valAt r.val i < valAt r.val j := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : arr.val.length ≤ 100000)
        (hbound : ∀ i, i < arr.val.length →
          -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
          ∀ i j, i < arr.val.length → j < arr.val.length →
            valAt arr.val i < valAt arr.val j → valAt r.val i < valAt r.val j) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(arr), 1 <= r[i].
    Preconditions: 0 <= len(arr) <= 100000 and for every i with 0 <= i < len(arr), -1000000000 <= arr[i] <= 1000000000. -/
  theorem spec_6 (arr : Slice Std.I64)
      (hlen : arr.val.length ≤ 100000)
      (hbound : ∀ i, i < arr.val.length →
        -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
        ∀ i, i < arr.val.length → 1 ≤ valAt r.val i := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : arr.val.length ≤ 100000)
        (hbound : ∀ i, i < arr.val.length →
          -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
          ∀ i, i < arr.val.length → 1 ≤ valAt r.val i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(arr), r[i] <= d, where d is the number of distinct integers occurring in arr.
    Preconditions: 0 <= len(arr) <= 100000 and for every i with 0 <= i < len(arr), -1000000000 <= arr[i] <= 1000000000. -/
  theorem spec_7 (arr : Slice Std.I64)
      (hlen : arr.val.length ≤ 100000)
      (hbound : ∀ i, i < arr.val.length →
        -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
        ∀ i, i < arr.val.length → valAt r.val i ≤ (numDistinct arr.val : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : arr.val.length ≤ 100000)
        (hbound : ∀ i, i < arr.val.length →
          -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
          ∀ i, i < arr.val.length → valAt r.val i ≤ (numDistinct arr.val : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(arr), if arr[i] <= arr[j] for every j with 0 <= j < len(arr), then r[i] = 1.
    Preconditions: 0 <= len(arr) <= 100000 and for every i with 0 <= i < len(arr), -1000000000 <= arr[i] <= 1000000000. -/
  theorem spec_8 (arr : Slice Std.I64)
      (hlen : arr.val.length ≤ 100000)
      (hbound : ∀ i, i < arr.val.length →
        -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
        ∀ i, i < arr.val.length → IsMinAt arr.val i → valAt r.val i = 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : arr.val.length ≤ 100000)
        (hbound : ∀ i, i < arr.val.length →
          -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
          ∀ i, i < arr.val.length → IsMinAt arr.val i → valAt r.val i = 1) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(arr), if r[i] = 1 then arr[i] <= arr[j] for every j with 0 <= j < len(arr).
    Preconditions: 0 <= len(arr) <= 100000 and for every i with 0 <= i < len(arr), -1000000000 <= arr[i] <= 1000000000. -/
  theorem spec_9 (arr : Slice Std.I64)
      (hlen : arr.val.length ≤ 100000)
      (hbound : ∀ i, i < arr.val.length →
        -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
        ∀ i, i < arr.val.length → valAt r.val i = 1 → IsMinAt arr.val i := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : arr.val.length ≤ 100000)
        (hbound : ∀ i, i < arr.val.length →
          -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
          ∀ i, i < arr.val.length → valAt r.val i = 1 → IsMinAt arr.val i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(arr), if arr[i] >= arr[j] for every j with 0 <= j < len(arr), then r[i] = d, where d is the number of distinct integers occurring in arr.
    Preconditions: 0 <= len(arr) <= 100000 and for every i with 0 <= i < len(arr), -1000000000 <= arr[i] <= 1000000000. -/
  theorem spec_10 (arr : Slice Std.I64)
      (hlen : arr.val.length ≤ 100000)
      (hbound : ∀ i, i < arr.val.length →
        -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
        ∀ i, i < arr.val.length → IsMaxAt arr.val i →
          valAt r.val i = (numDistinct arr.val : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : arr.val.length ≤ 100000)
        (hbound : ∀ i, i < arr.val.length →
          -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
          ∀ i, i < arr.val.length → IsMaxAt arr.val i →
            valAt r.val i = (numDistinct arr.val : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(arr), if r[i] = d, where d is the number of distinct integers occurring in arr, then arr[i] >= arr[j] for every j with 0 <= j < len(arr).
    Preconditions: 0 <= len(arr) <= 100000 and for every i with 0 <= i < len(arr), -1000000000 <= arr[i] <= 1000000000. -/
  theorem spec_11 (arr : Slice Std.I64)
      (hlen : arr.val.length ≤ 100000)
      (hbound : ∀ i, i < arr.val.length →
        -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
        ∀ i, i < arr.val.length → valAt r.val i = (numDistinct arr.val : Int) →
          IsMaxAt arr.val i := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : arr.val.length ≤ 100000)
        (hbound : ∀ i, i < arr.val.length →
          -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
          ∀ i, i < arr.val.length → valAt r.val i = (numDistinct arr.val : Int) →
            IsMaxAt arr.val i) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k with 1 <= k <= d, there exists an index i with 0 <= i < len(arr) and r[i] = k, where d is the number of distinct integers occurring in arr.
    Preconditions: 0 <= len(arr) <= 100000 and for every i with 0 <= i < len(arr), -1000000000 <= arr[i] <= 1000000000. -/
  theorem spec_12 (arr : Slice Std.I64)
      (hlen : arr.val.length ≤ 100000)
      (hbound : ∀ i, i < arr.val.length →
        -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
        ∀ k : Int, 1 ≤ k → k ≤ (numDistinct arr.val : Int) →
          ∃ i, i < arr.val.length ∧ valAt r.val i = k := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : arr.val.length ≤ 100000)
        (hbound : ∀ i, i < arr.val.length →
          -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
          ∀ k : Int, 1 ≤ k → k ≤ (numDistinct arr.val : Int) →
            ∃ i, i < arr.val.length ∧ valAt r.val i = k) := by
    sorry

  /-- Let r be the result of the function on arr. For every integer c such that -1000000000 <= arr[i] + c <= 1000000000 for every i with 0 <= i < len(arr), let arr' be the array defined by arr'[i] = arr[i] + c. The function on arr' returns a result r' with len(r') = len(r) and r'[i] = r[i] for every i with 0 <= i < len(arr).
    Preconditions: 0 <= len(arr) <= 100000 and for every i with 0 <= i < len(arr), -1000000000 <= arr[i] <= 1000000000. -/
  theorem spec_13 (arr : Slice Std.I64)
      (hlen : arr.val.length ≤ 100000)
      (hbound : ∀ i, i < arr.val.length →
        -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
        ∀ c : Int,
          (∀ i, i < arr.val.length →
            -1000000000 ≤ valAt arr.val i + c ∧ valAt arr.val i + c ≤ 1000000000) →
          ∀ arr' : Slice Std.I64, IsShift arr.val arr'.val c →
            ∀ r' : alloc.vec.Vec Std.I64, array_rank_transform arr' = ok r' →
              r'.val.length = r.val.length ∧
                ∀ i, i < arr.val.length → valAt r'.val i = valAt r.val i := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : arr.val.length ≤ 100000)
        (hbound : ∀ i, i < arr.val.length →
          -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r →
          ∀ c : Int,
            (∀ i, i < arr.val.length →
              -1000000000 ≤ valAt arr.val i + c ∧ valAt arr.val i + c ≤ 1000000000) →
            ∀ arr' : Slice Std.I64, IsShift arr.val arr'.val c →
              ∀ r' : alloc.vec.Vec Std.I64, array_rank_transform arr' = ok r' →
                r'.val.length = r.val.length ∧
                  ∀ i, i < arr.val.length → valAt r'.val i = valAt r.val i) := by
    sorry

  /-- For every arr satisfying the preconditions, the function returns a result r; in particular it does not fail, panic, or overflow.
    Preconditions: 0 <= len(arr) <= 100000 and for every i with 0 <= i < len(arr), -1000000000 <= arr[i] <= 1000000000. -/
  theorem spec_14 (arr : Slice Std.I64)
      (hlen : arr.val.length ≤ 100000)
      (hbound : ∀ i, i < arr.val.length →
        -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000) :
      ∃ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : arr.val.length ≤ 100000)
        (hbound : ∀ i, i < arr.val.length →
          -1000000000 ≤ valAt arr.val i ∧ valAt arr.val i ≤ 1000000000), ∃ r : alloc.vec.Vec Std.I64, array_rank_transform arr = ok r) := by
    sorry

  end AegisSpec.ArrayRankTransform
