import Aegis.MaximumSum.Code.Funs

/-!
# Specifications of `Aegis.MaximumSum.maximum_sum`

LeetCode problem `maximum-subarray-sum-with-one-deletion`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumSum

def vals (arr : Slice Std.I64) : List Int := arr.val.map (fun x => x.val)

def elem (arr : Slice Std.I64) (i : Nat) : Int :=
  match arr.val[i]? with
  | some x => x.val
  | none => 0

def rangeSum (arr : Slice Std.I64) (l u : Nat) : Int :=
  (((vals arr).drop l).take (u - l + 1)).sum

def posSum (arr : Slice Std.I64) : Int := ((vals arr).filter (fun x => 0 < x)).sum

def totalSum (arr : Slice Std.I64) : Int := (vals arr).sum

def sumExcept (arr : Slice Std.I64) (k : Nat) : Int :=
  (((List.range arr.val.length).filter (fun i => i ≠ k)).map (fun i => elem arr i)).sum

def listMax : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl (fun acc y => max acc y) x

def maxElem (arr : Slice Std.I64) : Int := listMax (vals arr)

structure Choice where
  lo : Nat
  hi : Nat
  del : Option Nat

namespace Choice

def Valid (arr : Slice Std.I64) (c : Choice) : Prop :=
  c.lo ≤ c.hi ∧ c.hi < arr.val.length ∧
    match c.del with
    | none => True
    | some d => c.lo ≤ d ∧ d ≤ c.hi ∧ 2 ≤ c.hi - c.lo + 1

def value (arr : Slice Std.I64) (c : Choice) : Int :=
  rangeSum arr c.lo c.hi - match c.del with
    | none => 0
    | some d => elem arr d

end Choice

def IsBest (arr : Slice Std.I64) (r : Int) : Prop :=
  (∀ c : Choice, Choice.Valid arr c → Choice.value arr c ≤ r) ∧
    ∃ c : Choice, Choice.Valid arr c ∧ Choice.value arr c = r

/-- For every arr satisfying the preconditions, whenever maximum_sum(arr) returns a result r, r equals the maximum value among all valid choices, where a valid choice is either (a) a non-empty contiguous subarray arr[l..u] with 0 <= l <= u < len(arr), whose value is sum_{i=l}^{u} arr[i], or (b) a contiguous subarray arr[l..u] with 0 <= l <= u < len(arr) and u - l + 1 >= 2, together with a deleted index d with l <= d <= u, whose value is sum_{i=l}^{u} arr[i] - arr[d].
  Preconditions: len(arr) >= 1, len(arr) <= 100000, and -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr). -/
theorem spec_1 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r) :
    IsBest arr r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r), IsBest arr r.val) := by
  sorry

/-- For every arr satisfying the preconditions, maximum_sum(arr) returns a result (it does not fail, panic, or overflow).
  Preconditions: len(arr) >= 1, len(arr) <= 100000, and -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr). -/
theorem spec_2 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000) :
    ∃ r : Std.I64, Aegis.MaximumSum.maximum_sum arr = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000), ∃ r : Std.I64, Aegis.MaximumSum.maximum_sum arr = ok r) := by
  sorry

/-- For every arr satisfying the preconditions, whenever maximum_sum(arr) returns a result r, there exist l and u with 0 <= l <= u < len(arr) and either no deleted index or a deleted index d with l <= d <= u and u - l + 1 >= 2 such that r equals sum_{i=l}^{u} arr[i] when no index is deleted, and r equals sum_{i=l}^{u} arr[i] - arr[d] when d is deleted.
  Preconditions: len(arr) >= 1, len(arr) <= 100000, and -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr). -/
theorem spec_3 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r) :
    ∃ c : Choice, Choice.Valid arr c ∧ Choice.value arr c = r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r), ∃ c : Choice, Choice.Valid arr c ∧ Choice.value arr c = r.val) := by
  sorry

/-- For every arr satisfying the preconditions, whenever maximum_sum(arr) returns a result r, for every l and u with 0 <= l <= u < len(arr), and for every choice of either no deletion or a deleted index d with l <= d <= u and u - l + 1 >= 2, the value sum_{i=l}^{u} arr[i] (if no deletion) or sum_{i=l}^{u} arr[i] - arr[d] (if d is deleted) is at most r.
  Preconditions: len(arr) >= 1, len(arr) <= 100000, and -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr). -/
theorem spec_4 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r) :
    ∀ c : Choice, Choice.Valid arr c → Choice.value arr c ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r), ∀ c : Choice, Choice.Valid arr c → Choice.value arr c ≤ r.val) := by
  sorry

/-- For every arr satisfying the preconditions, whenever maximum_sum(arr) returns a result r, -10000 <= r <= 1000000000.
  Preconditions: len(arr) >= 1, len(arr) <= 100000, and -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr). -/
theorem spec_5 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r) :
    -10000 ≤ r.val ∧ r.val ≤ 1000000000 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r), -10000 ≤ r.val ∧ r.val ≤ 1000000000) := by
  sorry

/-- For every arr satisfying the preconditions, whenever maximum_sum(arr) returns a result r, for every index i with 0 <= i < len(arr), arr[i] <= r.
  Preconditions: len(arr) >= 1, len(arr) <= 100000, and -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr). -/
theorem spec_6 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r) :
    ∀ i, i < arr.val.length → elem arr i ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r), ∀ i, i < arr.val.length → elem arr i ≤ r.val) := by
  sorry

/-- For every arr satisfying the preconditions, whenever maximum_sum(arr) returns a result r, r <= sum_{0 <= i < len(arr), arr[i] > 0} arr[i].
  Preconditions: len(arr) >= 1, len(arr) <= 100000, and -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr). -/
theorem spec_7 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r) :
    r.val ≤ posSum arr := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r), r.val ≤ posSum arr) := by
  sorry

/-- For every arr satisfying the preconditions and len(arr) = 1, whenever maximum_sum(arr) returns a result r, r = arr[0].
  Preconditions: len(arr) >= 1, len(arr) <= 100000, -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr), and len(arr) = 1. -/
theorem spec_8 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (hlen1 : arr.val.length = 1)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r) :
    r.val = elem arr 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (hlen1 : arr.val.length = 1)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r), r.val = elem arr 0) := by
  sorry

/-- For every arr satisfying the preconditions and len(arr) = 2, whenever maximum_sum(arr) returns a result r, r = max(arr[0], arr[1], arr[0] + arr[1]).
  Preconditions: len(arr) >= 1, len(arr) <= 100000, -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr), and len(arr) = 2. -/
theorem spec_9 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (hlen2 : arr.val.length = 2)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r) :
    r.val = max (elem arr 0) (max (elem arr 1) (elem arr 0 + elem arr 1)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (hlen2 : arr.val.length = 2)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r), r.val = max (elem arr 0) (max (elem arr 1) (elem arr 0 + elem arr 1))) := by
  sorry

/-- For every arr satisfying the preconditions and with arr[i] <= 0 for every 0 <= i < len(arr), whenever maximum_sum(arr) returns a result r, r = max_{0 <= i < len(arr)} arr[i].
  Preconditions: len(arr) >= 1, len(arr) <= 100000, -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr), and arr[i] <= 0 for every 0 <= i < len(arr). -/
theorem spec_10 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (hnonpos : ∀ i, i < arr.val.length → elem arr i ≤ 0)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r) :
    r.val = maxElem arr := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (hnonpos : ∀ i, i < arr.val.length → elem arr i ≤ 0)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r), r.val = maxElem arr) := by
  sorry

/-- For every arr satisfying the preconditions and with arr[i] >= 0 for every 0 <= i < len(arr), whenever maximum_sum(arr) returns a result r, r = sum_{i=0}^{len(arr)-1} arr[i].
  Preconditions: len(arr) >= 1, len(arr) <= 100000, -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr), and arr[i] >= 0 for every 0 <= i < len(arr). -/
theorem spec_11 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (hnonneg : ∀ i, i < arr.val.length → 0 ≤ elem arr i)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r) :
    r.val = totalSum arr := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (hnonneg : ∀ i, i < arr.val.length → 0 ≤ elem arr i)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r), r.val = totalSum arr) := by
  sorry

/-- For every arr satisfying the preconditions and having exactly one negative entry at index k, whenever maximum_sum(arr) returns a result r, r = sum_{0 <= i < len(arr), i != k} arr[i].
  Preconditions: len(arr) >= 2, len(arr) <= 100000, -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr), and there is exactly one index k with 0 <= k < len(arr) and arr[k] < 0. -/
theorem spec_12 (arr : Slice Std.I64)
    (hlen : 2 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (huniq : ∃ k, (k < arr.val.length ∧ elem arr k < 0) ∧
      ∀ j, j < arr.val.length → elem arr j < 0 → j = k)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r) :
    ∀ k, k < arr.val.length → elem arr k < 0 → r.val = sumExcept arr k := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 2 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (huniq : ∃ k, (k < arr.val.length ∧ elem arr k < 0) ∧
      ∀ j, j < arr.val.length → elem arr j < 0 → j = k)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r), ∀ k, k < arr.val.length → elem arr k < 0 → r.val = sumExcept arr k) := by
  sorry

/-- For every arr satisfying the preconditions and having exactly one positive entry at index k, whenever maximum_sum(arr) returns a result r, r = arr[k].
  Preconditions: len(arr) >= 1, len(arr) <= 100000, -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr), and there is exactly one index k with 0 <= k < len(arr) and arr[k] > 0. -/
theorem spec_13 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (huniq : ∃ k, (k < arr.val.length ∧ 0 < elem arr k) ∧
      ∀ j, j < arr.val.length → 0 < elem arr j → j = k)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r) :
    ∀ k, k < arr.val.length → 0 < elem arr k → r.val = elem arr k := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (huniq : ∃ k, (k < arr.val.length ∧ 0 < elem arr k) ∧
      ∀ j, j < arr.val.length → 0 < elem arr j → j = k)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r), ∀ k, k < arr.val.length → 0 < elem arr k → r.val = elem arr k) := by
  sorry

/-- For every arr satisfying the preconditions, whenever maximum_sum(arr) returns a result r, there exist l and u with 0 <= l <= u < len(arr) and either no deleted index or a deleted index d with l <= d <= u and u - l + 1 >= 2 such that the corresponding value equals r, and either no deletion is used or arr[d] < 0.
  Preconditions: len(arr) >= 1, len(arr) <= 100000, and -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr). -/
theorem spec_14 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r) :
    ∃ c : Choice, Choice.Valid arr c ∧ Choice.value arr c = r.val ∧
      (c.del = none ∨ ∃ d, c.del = some d ∧ elem arr d < 0) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen' : arr.val.length ≤ 100000)
    (hbound : ∀ i, i < arr.val.length → -10000 ≤ elem arr i ∧ elem arr i ≤ 10000)
    (r : Std.I64) (hr : Aegis.MaximumSum.maximum_sum arr = ok r), ∃ c : Choice, Choice.Valid arr c ∧ Choice.value arr c = r.val ∧
      (c.del = none ∨ ∃ d, c.del = some d ∧ elem arr d < 0)) := by
  sorry

end AegisSpec.MaximumSum
