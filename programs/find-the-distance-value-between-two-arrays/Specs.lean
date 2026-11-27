import Aegis.FindTheDistanceValue.Code.Funs

/-!
# Specifications of `Aegis.FindTheDistanceValue.find_the_distance_value`

LeetCode problem `find-the-distance-value-between-two-arrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindTheDistanceValue

  def elemAt (s : Slice Std.I64) (i : Nat) : Int :=
    match s.val[i]? with
    | some x => x.val
    | none => 0

  def validAt (arr1 arr2 : Slice Std.I64) (d : Int) (i : Nat) : Bool :=
    arr2.val.all (fun y => decide (d < |elemAt arr1 i - y.val|))

  def countValid (arr1 arr2 : Slice Std.I64) (d : Int) : Nat :=
    ((List.range arr1.val.length).filter (fun i => validAt arr1 arr2 d i)).length

  def Occurs (x : Int) (s : Slice Std.I64) : Prop :=
    ∃ y ∈ s.val, y.val = x

  theorem elemAt_getElem (s : Slice Std.I64) (i : Nat) (h : i < s.val.length) :
      elemAt s i = (s.val[i]).val := by
    simp [elemAt, List.getElem?_eq_getElem h]

  theorem validAt_iff (arr1 arr2 : Slice Std.I64) (d : Int) (i : Nat) :
      (validAt arr1 arr2 d i = true) ↔
        ∀ y ∈ arr2.val, d < |elemAt arr1 i - y.val| := by
    simp [validAt, List.all_eq_true]

  /-- Whenever find_the_distance_value arr1 arr2 d returns a result r, r equals the number of indices i with 0 <= i < len(arr1) such that for every j with 0 <= j < len(arr2), |arr1[i] - arr2[j]| > d, where |x| is the usual absolute value of the integer x.
    Preconditions: len(arr1) >= 1, len(arr1) <= 500, len(arr2) >= 1, len(arr2) <= 500, for every i with 0 <= i < len(arr1), -1000 <= arr1[i] <= 1000, for every j with 0 <= j < len(arr2), -1000 <= arr2[j] <= 1000, and 0 <= d <= 100. -/
  theorem spec_1 (arr1 arr2 : Slice Std.I64) (d : Std.I64)
      (h1len : 1 ≤ arr1.val.length) (h1len' : arr1.val.length ≤ 500)
      (h2len : 1 ≤ arr2.val.length) (h2len' : arr2.val.length ≤ 500)
      (h1val : ∀ i, i < arr1.val.length → -1000 ≤ elemAt arr1 i ∧ elemAt arr1 i ≤ 1000)
      (h2val : ∀ j, j < arr2.val.length → -1000 ≤ elemAt arr2 j ∧ elemAt arr2 j ≤ 1000)
      (hd : 0 ≤ d.val ∧ d.val ≤ 100) :
      ∀ r, Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2 d = ok r →
        r.val = (countValid arr1 arr2 d.val : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr1 arr2 : Slice Std.I64) (d : Std.I64)
        (h1len : 1 ≤ arr1.val.length) (h1len' : arr1.val.length ≤ 500)
        (h2len : 1 ≤ arr2.val.length) (h2len' : arr2.val.length ≤ 500)
        (h1val : ∀ i, i < arr1.val.length → -1000 ≤ elemAt arr1 i ∧ elemAt arr1 i ≤ 1000)
        (h2val : ∀ j, j < arr2.val.length → -1000 ≤ elemAt arr2 j ∧ elemAt arr2 j ≤ 1000)
        (hd : 0 ≤ d.val ∧ d.val ≤ 100), ∀ r, Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2 d = ok r →
          r.val = (countValid arr1 arr2 d.val : Int)) := by
    sorry

  /-- For every arr1, arr2, and d satisfying the preconditions, find_the_distance_value arr1 arr2 d returns a result; it does not fail with overflow, out-of-bounds, or panic.
    Preconditions: len(arr1) >= 1, len(arr1) <= 500, len(arr2) >= 1, len(arr2) <= 500, for every i with 0 <= i < len(arr1), -1000 <= arr1[i] <= 1000, for every j with 0 <= j < len(arr2), -1000 <= arr2[j] <= 1000, and 0 <= d <= 100. -/
  theorem spec_2 (arr1 arr2 : Slice Std.I64) (d : Std.I64)
      (h1len : 1 ≤ arr1.val.length) (h1len' : arr1.val.length ≤ 500)
      (h2len : 1 ≤ arr2.val.length) (h2len' : arr2.val.length ≤ 500)
      (h1val : ∀ i, i < arr1.val.length → -1000 ≤ elemAt arr1 i ∧ elemAt arr1 i ≤ 1000)
      (h2val : ∀ j, j < arr2.val.length → -1000 ≤ elemAt arr2 j ∧ elemAt arr2 j ≤ 1000)
      (hd : 0 ≤ d.val ∧ d.val ≤ 100) :
      ∃ r, Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2 d = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr1 arr2 : Slice Std.I64) (d : Std.I64)
        (h1len : 1 ≤ arr1.val.length) (h1len' : arr1.val.length ≤ 500)
        (h2len : 1 ≤ arr2.val.length) (h2len' : arr2.val.length ≤ 500)
        (h1val : ∀ i, i < arr1.val.length → -1000 ≤ elemAt arr1 i ∧ elemAt arr1 i ≤ 1000)
        (h2val : ∀ j, j < arr2.val.length → -1000 ≤ elemAt arr2 j ∧ elemAt arr2 j ≤ 1000)
        (hd : 0 ≤ d.val ∧ d.val ≤ 100), ∃ r, Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2 d = ok r) := by
    sorry

  /-- If find_the_distance_value arr1 arr2 d1 returns a result r1 and find_the_distance_value arr1 arr2 d2 returns a result r2, then r1 >= r2.
    Preconditions: len(arr1) >= 1, len(arr1) <= 500, len(arr2) >= 1, len(arr2) <= 500, for every i with 0 <= i < len(arr1), -1000 <= arr1[i] <= 1000, for every j with 0 <= j < len(arr2), -1000 <= arr2[j] <= 1000, and 0 <= d1 <= d2 <= 100. -/
  theorem spec_3 (arr1 arr2 : Slice Std.I64) (d1 d2 : Std.I64)
      (h1len : 1 ≤ arr1.val.length) (h1len' : arr1.val.length ≤ 500)
      (h2len : 1 ≤ arr2.val.length) (h2len' : arr2.val.length ≤ 500)
      (h1val : ∀ i, i < arr1.val.length → -1000 ≤ elemAt arr1 i ∧ elemAt arr1 i ≤ 1000)
      (h2val : ∀ j, j < arr2.val.length → -1000 ≤ elemAt arr2 j ∧ elemAt arr2 j ≤ 1000)
      (hd : 0 ≤ d1.val ∧ d1.val ≤ d2.val ∧ d2.val ≤ 100) :
      ∀ r1 r2, Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2 d1 = ok r1 →
        Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2 d2 = ok r2 →
        r2.val ≤ r1.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr1 arr2 : Slice Std.I64) (d1 d2 : Std.I64)
        (h1len : 1 ≤ arr1.val.length) (h1len' : arr1.val.length ≤ 500)
        (h2len : 1 ≤ arr2.val.length) (h2len' : arr2.val.length ≤ 500)
        (h1val : ∀ i, i < arr1.val.length → -1000 ≤ elemAt arr1 i ∧ elemAt arr1 i ≤ 1000)
        (h2val : ∀ j, j < arr2.val.length → -1000 ≤ elemAt arr2 j ∧ elemAt arr2 j ≤ 1000)
        (hd : 0 ≤ d1.val ∧ d1.val ≤ d2.val ∧ d2.val ≤ 100), ∀ r1 r2, Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2 d1 = ok r1 →
          Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2 d2 = ok r2 →
          r2.val ≤ r1.val) := by
    sorry

  /-- If find_the_distance_value arr1 arr2 d returns a result r and find_the_distance_value arr1 arr2' d returns a result r', then r <= r'.
    Preconditions: len(arr1) >= 1, len(arr1) <= 500, len(arr2) >= 1, len(arr2) <= 500, for every i with 0 <= i < len(arr1), -1000 <= arr1[i] <= 1000, for every j with 0 <= j < len(arr2), -1000 <= arr2[j] <= 1000, 0 <= d <= 100, and arr2' is a slice of Std.I64 obtained from arr2 by deleting zero or more elements (so there are indices k_0 < k_1 < ... < k_{m-1} in [0, len(arr2)) with arr2'[t] = arr2[k_t] for every 0 <= t < len(arr2')), with len(arr2') >= 1 and len(arr2') <= 500. -/
  theorem spec_4 (arr1 arr2 arr2' : Slice Std.I64) (d : Std.I64)
      (h1len : 1 ≤ arr1.val.length) (h1len' : arr1.val.length ≤ 500)
      (h2len : 1 ≤ arr2.val.length) (h2len' : arr2.val.length ≤ 500)
      (h1val : ∀ i, i < arr1.val.length → -1000 ≤ elemAt arr1 i ∧ elemAt arr1 i ≤ 1000)
      (h2val : ∀ j, j < arr2.val.length → -1000 ≤ elemAt arr2 j ∧ elemAt arr2 j ≤ 1000)
      (hd : 0 ≤ d.val ∧ d.val ≤ 100)
      (hsub : arr2'.val.Sublist arr2.val)
      (h2'len : 1 ≤ arr2'.val.length) (h2'len' : arr2'.val.length ≤ 500) :
      ∀ r r', Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2 d = ok r →
        Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2' d = ok r' →
        r.val ≤ r'.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr1 arr2 arr2' : Slice Std.I64) (d : Std.I64)
        (h1len : 1 ≤ arr1.val.length) (h1len' : arr1.val.length ≤ 500)
        (h2len : 1 ≤ arr2.val.length) (h2len' : arr2.val.length ≤ 500)
        (h1val : ∀ i, i < arr1.val.length → -1000 ≤ elemAt arr1 i ∧ elemAt arr1 i ≤ 1000)
        (h2val : ∀ j, j < arr2.val.length → -1000 ≤ elemAt arr2 j ∧ elemAt arr2 j ≤ 1000)
        (hd : 0 ≤ d.val ∧ d.val ≤ 100)
        (hsub : arr2'.val.Sublist arr2.val)
        (h2'len : 1 ≤ arr2'.val.length) (h2'len' : arr2'.val.length ≤ 500), ∀ r r', Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2 d = ok r →
          Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2' d = ok r' →
          r.val ≤ r'.val) := by
    sorry

  /-- If find_the_distance_value arr1 arr2 d returns a result r and find_the_distance_value arr1' arr2 d returns a result r', then r' <= r.
    Preconditions: len(arr1) >= 1, len(arr1) <= 500, len(arr2) >= 1, len(arr2) <= 500, for every i with 0 <= i < len(arr1), -1000 <= arr1[i] <= 1000, for every j with 0 <= j < len(arr2), -1000 <= arr2[j] <= 1000, 0 <= d <= 100, and arr1' is a slice of Std.I64 obtained from arr1 by deleting zero or more elements (so there are indices k_0 < k_1 < ... < k_{m-1} in [0, len(arr1)) with arr1'[t] = arr1[k_t] for every 0 <= t < len(arr1')), with len(arr1') >= 1 and len(arr1') <= 500. -/
  theorem spec_5 (arr1 arr1' arr2 : Slice Std.I64) (d : Std.I64)
      (h1len : 1 ≤ arr1.val.length) (h1len' : arr1.val.length ≤ 500)
      (h2len : 1 ≤ arr2.val.length) (h2len' : arr2.val.length ≤ 500)
      (h1val : ∀ i, i < arr1.val.length → -1000 ≤ elemAt arr1 i ∧ elemAt arr1 i ≤ 1000)
      (h2val : ∀ j, j < arr2.val.length → -1000 ≤ elemAt arr2 j ∧ elemAt arr2 j ≤ 1000)
      (hd : 0 ≤ d.val ∧ d.val ≤ 100)
      (hsub : arr1'.val.Sublist arr1.val)
      (h1'len : 1 ≤ arr1'.val.length) (h1'len' : arr1'.val.length ≤ 500) :
      ∀ r r', Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2 d = ok r →
        Aegis.FindTheDistanceValue.find_the_distance_value arr1' arr2 d = ok r' →
        r'.val ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr1 arr1' arr2 : Slice Std.I64) (d : Std.I64)
        (h1len : 1 ≤ arr1.val.length) (h1len' : arr1.val.length ≤ 500)
        (h2len : 1 ≤ arr2.val.length) (h2len' : arr2.val.length ≤ 500)
        (h1val : ∀ i, i < arr1.val.length → -1000 ≤ elemAt arr1 i ∧ elemAt arr1 i ≤ 1000)
        (h2val : ∀ j, j < arr2.val.length → -1000 ≤ elemAt arr2 j ∧ elemAt arr2 j ≤ 1000)
        (hd : 0 ≤ d.val ∧ d.val ≤ 100)
        (hsub : arr1'.val.Sublist arr1.val)
        (h1'len : 1 ≤ arr1'.val.length) (h1'len' : arr1'.val.length ≤ 500), ∀ r r', Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2 d = ok r →
          Aegis.FindTheDistanceValue.find_the_distance_value arr1' arr2 d = ok r' →
          r'.val ≤ r.val) := by
    sorry

  /-- If find_the_distance_value arr1 arr2 d returns a result r and find_the_distance_value arr1' arr2 d returns a result r', then r = r'.
    Preconditions: len(arr1) >= 1, len(arr1) <= 500, len(arr2) >= 1, len(arr2) <= 500, for every i with 0 <= i < len(arr1), -1000 <= arr1[i] <= 1000, for every j with 0 <= j < len(arr2), -1000 <= arr2[j] <= 1000, 0 <= d <= 100, and arr1' is a permutation of arr1: len(arr1') = len(arr1) and the two lists have the same multiset of values. -/
  theorem spec_6 (arr1 arr1' arr2 : Slice Std.I64) (d : Std.I64)
      (h1len : 1 ≤ arr1.val.length) (h1len' : arr1.val.length ≤ 500)
      (h2len : 1 ≤ arr2.val.length) (h2len' : arr2.val.length ≤ 500)
      (h1val : ∀ i, i < arr1.val.length → -1000 ≤ elemAt arr1 i ∧ elemAt arr1 i ≤ 1000)
      (h2val : ∀ j, j < arr2.val.length → -1000 ≤ elemAt arr2 j ∧ elemAt arr2 j ≤ 1000)
      (hd : 0 ≤ d.val ∧ d.val ≤ 100)
      (hperm_len : arr1'.val.length = arr1.val.length)
      (hperm : arr1'.val.Perm arr1.val) :
      ∀ r r', Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2 d = ok r →
        Aegis.FindTheDistanceValue.find_the_distance_value arr1' arr2 d = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr1 arr1' arr2 : Slice Std.I64) (d : Std.I64)
        (h1len : 1 ≤ arr1.val.length) (h1len' : arr1.val.length ≤ 500)
        (h2len : 1 ≤ arr2.val.length) (h2len' : arr2.val.length ≤ 500)
        (h1val : ∀ i, i < arr1.val.length → -1000 ≤ elemAt arr1 i ∧ elemAt arr1 i ≤ 1000)
        (h2val : ∀ j, j < arr2.val.length → -1000 ≤ elemAt arr2 j ∧ elemAt arr2 j ≤ 1000)
        (hd : 0 ≤ d.val ∧ d.val ≤ 100)
        (hperm_len : arr1'.val.length = arr1.val.length)
        (hperm : arr1'.val.Perm arr1.val), ∀ r r', Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2 d = ok r →
          Aegis.FindTheDistanceValue.find_the_distance_value arr1' arr2 d = ok r' →
          r.val = r'.val) := by
    sorry

  /-- If find_the_distance_value arr1 arr2 d returns a result r and find_the_distance_value arr1 arr2' d returns a result r', then r = r'.
    Preconditions: len(arr1) >= 1, len(arr1) <= 500, len(arr2) >= 1, len(arr2) <= 500, for every i with 0 <= i < len(arr1), -1000 <= arr1[i] <= 1000, for every j with 0 <= j < len(arr2), -1000 <= arr2[j] <= 1000, 0 <= d <= 100, arr2' is a slice of Std.I64 with len(arr2') >= 1, len(arr2') <= 500, every element of arr2' is in [-1000, 1000], and for every integer x, x occurs in arr2' if and only if x occurs in arr2. -/
  theorem spec_7 (arr1 arr2 arr2' : Slice Std.I64) (d : Std.I64)
      (h1len : 1 ≤ arr1.val.length) (h1len' : arr1.val.length ≤ 500)
      (h2len : 1 ≤ arr2.val.length) (h2len' : arr2.val.length ≤ 500)
      (h1val : ∀ i, i < arr1.val.length → -1000 ≤ elemAt arr1 i ∧ elemAt arr1 i ≤ 1000)
      (h2val : ∀ j, j < arr2.val.length → -1000 ≤ elemAt arr2 j ∧ elemAt arr2 j ≤ 1000)
      (hd : 0 ≤ d.val ∧ d.val ≤ 100)
      (h2'len : 1 ≤ arr2'.val.length) (h2'len' : arr2'.val.length ≤ 500)
      (h2'val : ∀ j, j < arr2'.val.length →
        -1000 ≤ elemAt arr2' j ∧ elemAt arr2' j ≤ 1000)
      (hocc : ∀ x : Int, Occurs x arr2' ↔ Occurs x arr2) :
      ∀ r r', Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2 d = ok r →
        Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2' d = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr1 arr2 arr2' : Slice Std.I64) (d : Std.I64)
        (h1len : 1 ≤ arr1.val.length) (h1len' : arr1.val.length ≤ 500)
        (h2len : 1 ≤ arr2.val.length) (h2len' : arr2.val.length ≤ 500)
        (h1val : ∀ i, i < arr1.val.length → -1000 ≤ elemAt arr1 i ∧ elemAt arr1 i ≤ 1000)
        (h2val : ∀ j, j < arr2.val.length → -1000 ≤ elemAt arr2 j ∧ elemAt arr2 j ≤ 1000)
        (hd : 0 ≤ d.val ∧ d.val ≤ 100)
        (h2'len : 1 ≤ arr2'.val.length) (h2'len' : arr2'.val.length ≤ 500)
        (h2'val : ∀ j, j < arr2'.val.length →
          -1000 ≤ elemAt arr2' j ∧ elemAt arr2' j ≤ 1000)
        (hocc : ∀ x : Int, Occurs x arr2' ↔ Occurs x arr2), ∀ r r', Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2 d = ok r →
          Aegis.FindTheDistanceValue.find_the_distance_value arr1 arr2' d = ok r' →
          r.val = r'.val) := by
    sorry

  end AegisSpec.FindTheDistanceValue
