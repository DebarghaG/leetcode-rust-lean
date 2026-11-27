import Aegis.MaxAbsValExpr.Code.Funs

/-!
# Specifications of `Aegis.MaxAbsValExpr.max_abs_val_expr`

LeetCode problem `maximum-of-absolute-value-expression`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  set_option autoImplicit false

  namespace AegisSpec.MaxAbsValExpr

  def entry (arr : Slice Std.I64) (i : Nat) : Int :=
    match arr.val[i]? with
    | some x => x.val
    | none => 0

  def maxOver (n : Nat) (f : Nat → Int) : Int :=
    match List.range n with
    | [] => 0
    | i :: is => is.foldl (fun m j => max m (f j)) (f i)

  def minOver (n : Nat) (f : Nat → Int) : Int :=
    match List.range n with
    | [] => 0
    | i :: is => is.foldl (fun m j => min m (f j)) (f i)

  def maxEntry (arr : Slice Std.I64) : Int :=
    maxOver arr.val.length (entry arr)

  def minEntry (arr : Slice Std.I64) : Int :=
    minOver arr.val.length (entry arr)

  def signedRange (arr1 arr2 : Slice Std.I64) (s t : Int) : Int :=
    maxOver arr1.val.length (fun i => s * entry arr1 i + t * entry arr2 i + (i : Int)) -
      minOver arr1.val.length (fun i => s * entry arr1 i + t * entry arr2 i + (i : Int))

  /-- For every arr1 and arr2 satisfying the preconditions, max_abs_val_expr arr1 arr2 returns a result r (it does not fail), and r is the maximum of the set of all values |arr1[i] - arr1[j]| + |arr2[i] - arr2[j]| + |i - j| with 0 <= i < n and 0 <= j < n. Equivalently, every such expression is at most r, and some such expression is exactly r.
    Preconditions: Let n = len(arr1). The preconditions are: len(arr2) = n; 2 <= n <= 40000; for every i with 0 <= i < n, -1000000 <= arr1[i] <= 1000000 and -1000000 <= arr2[i] <= 1000000. -/
  theorem spec_1 (arr1 arr2 : Slice Std.I64)
      (h_len : arr2.val.length = arr1.val.length)
      (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
      (h_b1 : ∀ i (hi : i < arr1.val.length),
        -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
      (h_b2 : ∀ i (hi : i < arr2.val.length),
        -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000) :
      ∃ r : Std.I64,
        Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r ∧
          (∀ (i j : Nat) (hi : i < arr1.val.length) (hj : j < arr1.val.length),
            |(arr1.val[i]).val - (arr1.val[j]).val| +
                |(arr2.val[i]).val - (arr2.val[j]).val| + |(i : Int) - (j : Int)| ≤
              r.val) ∧
          (∃ (i j : Nat) (hi : i < arr1.val.length) (hj : j < arr1.val.length),
            |(arr1.val[i]).val - (arr1.val[j]).val| +
                |(arr2.val[i]).val - (arr2.val[j]).val| + |(i : Int) - (j : Int)| =
              r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr1 arr2 : Slice Std.I64)
        (h_len : arr2.val.length = arr1.val.length)
        (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
        (h_b1 : ∀ i (hi : i < arr1.val.length),
          -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
        (h_b2 : ∀ i (hi : i < arr2.val.length),
          -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000), ∃ r : Std.I64,
          Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r ∧
            (∀ (i j : Nat) (hi : i < arr1.val.length) (hj : j < arr1.val.length),
              |(arr1.val[i]).val - (arr1.val[j]).val| +
                  |(arr2.val[i]).val - (arr2.val[j]).val| + |(i : Int) - (j : Int)| ≤
                r.val) ∧
            (∃ (i j : Nat) (hi : i < arr1.val.length) (hj : j < arr1.val.length),
              |(arr1.val[i]).val - (arr1.val[j]).val| +
                  |(arr2.val[i]).val - (arr2.val[j]).val| + |(i : Int) - (j : Int)| =
                r.val)) := by
    sorry

  /-- Whenever max_abs_val_expr arr1 arr2 returns a result r, we have r >= n - 1.
    Preconditions: Let n = len(arr1). The preconditions are: len(arr2) = n; 2 <= n <= 40000; for every i with 0 <= i < n, -1000000 <= arr1[i] <= 1000000 and -1000000 <= arr2[i] <= 1000000. -/
  theorem spec_2 (arr1 arr2 : Slice Std.I64) (r : Std.I64)
      (h_len : arr2.val.length = arr1.val.length)
      (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
      (h_b1 : ∀ i (hi : i < arr1.val.length),
        -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
      (h_b2 : ∀ i (hi : i < arr2.val.length),
        -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000)
      (hr : Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r) :
      (arr1.val.length : Int) - 1 ≤ r.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr1 arr2 : Slice Std.I64) (r : Std.I64)
        (h_len : arr2.val.length = arr1.val.length)
        (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
        (h_b1 : ∀ i (hi : i < arr1.val.length),
          -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
        (h_b2 : ∀ i (hi : i < arr2.val.length),
          -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000)
        (hr : Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r), (arr1.val.length : Int) - 1 ≤ r.val) := by
    sorry

  /-- Whenever max_abs_val_expr arr1 arr2 returns a result r, we have r >= max(max1 - min1, max2 - min2), where max1 = max { arr1[i] | 0 <= i < n }, min1 = min { arr1[i] | 0 <= i < n }, max2 = max { arr2[i] | 0 <= i < n }, and min2 = min { arr2[i] | 0 <= i < n }.
    Preconditions: Let n = len(arr1). The preconditions are: len(arr2) = n; 2 <= n <= 40000; for every i with 0 <= i < n, -1000000 <= arr1[i] <= 1000000 and -1000000 <= arr2[i] <= 1000000. -/
  theorem spec_3 (arr1 arr2 : Slice Std.I64) (r : Std.I64)
      (h_len : arr2.val.length = arr1.val.length)
      (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
      (h_b1 : ∀ i (hi : i < arr1.val.length),
        -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
      (h_b2 : ∀ i (hi : i < arr2.val.length),
        -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000)
      (hr : Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r) :
      max (maxEntry arr1 - minEntry arr1) (maxEntry arr2 - minEntry arr2) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr1 arr2 : Slice Std.I64) (r : Std.I64)
        (h_len : arr2.val.length = arr1.val.length)
        (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
        (h_b1 : ∀ i (hi : i < arr1.val.length),
          -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
        (h_b2 : ∀ i (hi : i < arr2.val.length),
          -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000)
        (hr : Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r), max (maxEntry arr1 - minEntry arr1) (maxEntry arr2 - minEntry arr2) ≤ r.val) := by
    sorry

  /-- Whenever max_abs_val_expr arr1 arr2 returns a result r, we have r <= (max1 - min1) + (max2 - min2) + (n - 1), where max1 = max { arr1[i] | 0 <= i < n }, min1 = min { arr1[i] | 0 <= i < n }, max2 = max { arr2[i] | 0 <= i < n }, and min2 = min { arr2[i] | 0 <= i < n }.
    Preconditions: Let n = len(arr1). The preconditions are: len(arr2) = n; 2 <= n <= 40000; for every i with 0 <= i < n, -1000000 <= arr1[i] <= 1000000 and -1000000 <= arr2[i] <= 1000000. -/
  theorem spec_4 (arr1 arr2 : Slice Std.I64) (r : Std.I64)
      (h_len : arr2.val.length = arr1.val.length)
      (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
      (h_b1 : ∀ i (hi : i < arr1.val.length),
        -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
      (h_b2 : ∀ i (hi : i < arr2.val.length),
        -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000)
      (hr : Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r) :
      r.val ≤
        (maxEntry arr1 - minEntry arr1) + (maxEntry arr2 - minEntry arr2) +
          ((arr1.val.length : Int) - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr1 arr2 : Slice Std.I64) (r : Std.I64)
        (h_len : arr2.val.length = arr1.val.length)
        (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
        (h_b1 : ∀ i (hi : i < arr1.val.length),
          -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
        (h_b2 : ∀ i (hi : i < arr2.val.length),
          -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000)
        (hr : Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r), r.val ≤
          (maxEntry arr1 - minEntry arr1) + (maxEntry arr2 - minEntry arr2) +
            ((arr1.val.length : Int) - 1)) := by
    sorry

  /-- Whenever max_abs_val_expr arr1 arr2 returns a result r, there exist integers i and j with 0 <= i < j < n such that |arr1[i] - arr1[j]| + |arr2[i] - arr2[j]| + (j - i) = r.
    Preconditions: Let n = len(arr1). The preconditions are: len(arr2) = n; 2 <= n <= 40000; for every i with 0 <= i < n, -1000000 <= arr1[i] <= 1000000 and -1000000 <= arr2[i] <= 1000000. -/
  theorem spec_5 (arr1 arr2 : Slice Std.I64) (r : Std.I64)
      (h_len : arr2.val.length = arr1.val.length)
      (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
      (h_b1 : ∀ i (hi : i < arr1.val.length),
        -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
      (h_b2 : ∀ i (hi : i < arr2.val.length),
        -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000)
      (hr : Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r) :
      ∃ (i j : Nat) (hi : i < arr1.val.length) (hj : j < arr1.val.length),
        i < j ∧
          |(arr1.val[i]).val - (arr1.val[j]).val| +
              |(arr2.val[i]).val - (arr2.val[j]).val| + ((j : Int) - (i : Int)) =
            r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr1 arr2 : Slice Std.I64) (r : Std.I64)
        (h_len : arr2.val.length = arr1.val.length)
        (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
        (h_b1 : ∀ i (hi : i < arr1.val.length),
          -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
        (h_b2 : ∀ i (hi : i < arr2.val.length),
          -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000)
        (hr : Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r), ∃ (i j : Nat) (hi : i < arr1.val.length) (hj : j < arr1.val.length),
          i < j ∧
            |(arr1.val[i]).val - (arr1.val[j]).val| +
                |(arr2.val[i]).val - (arr2.val[j]).val| + ((j : Int) - (i : Int)) =
              r.val) := by
    sorry

  /-- Whenever max_abs_val_expr arr1 arr2 returns a result r and max_abs_val_expr arr2 arr1 returns a result s, we have r = s.
    Preconditions: Let n = len(arr1). The preconditions are: len(arr2) = n; 2 <= n <= 40000; for every i with 0 <= i < n, -1000000 <= arr1[i] <= 1000000 and -1000000 <= arr2[i] <= 1000000. -/
  theorem spec_6 (arr1 arr2 : Slice Std.I64) (r s : Std.I64)
      (h_len : arr2.val.length = arr1.val.length)
      (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
      (h_b1 : ∀ i (hi : i < arr1.val.length),
        -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
      (h_b2 : ∀ i (hi : i < arr2.val.length),
        -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000)
      (hr : Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r)
      (hs : Aegis.MaxAbsValExpr.max_abs_val_expr arr2 arr1 = ok s) :
      r.val = s.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr1 arr2 : Slice Std.I64) (r s : Std.I64)
        (h_len : arr2.val.length = arr1.val.length)
        (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
        (h_b1 : ∀ i (hi : i < arr1.val.length),
          -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
        (h_b2 : ∀ i (hi : i < arr2.val.length),
          -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000)
        (hr : Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r)
        (hs : Aegis.MaxAbsValExpr.max_abs_val_expr arr2 arr1 = ok s), r.val = s.val) := by
    sorry

  /-- For every pair of integers c and d such that -1000000 <= arr1[i] + c <= 1000000 and -1000000 <= arr2[i] + d <= 1000000 for all i with 0 <= i < n, define arr1'[i] = arr1[i] + c and arr2'[i] = arr2[i] + d. Whenever max_abs_val_expr arr1 arr2 returns r and max_abs_val_expr arr1' arr2' returns r', we have r = r'.
    Preconditions: Let n = len(arr1). The preconditions are: len(arr2) = n; 2 <= n <= 40000; for every i with 0 <= i < n, -1000000 <= arr1[i] <= 1000000 and -1000000 <= arr2[i] <= 1000000. -/
  theorem spec_7 (arr1 arr2 arr1' arr2' : Slice Std.I64) (c d : Int) (r r' : Std.I64)
      (h_len : arr2.val.length = arr1.val.length)
      (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
      (h_b1 : ∀ i (hi : i < arr1.val.length),
        -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
      (h_b2 : ∀ i (hi : i < arr2.val.length),
        -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000)
      (h_c1 : ∀ i (hi : i < arr1.val.length),
        -1000000 ≤ (arr1.val[i]).val + c ∧ (arr1.val[i]).val + c ≤ 1000000)
      (h_c2 : ∀ i (hi : i < arr2.val.length),
        -1000000 ≤ (arr2.val[i]).val + d ∧ (arr2.val[i]).val + d ≤ 1000000)
      (h_len1' : arr1'.val.length = arr1.val.length)
      (h_len2' : arr2'.val.length = arr2.val.length)
      (h_val1' : ∀ i (hi : i < arr1.val.length) (hi' : i < arr1'.val.length),
        (arr1'.val[i]).val = (arr1.val[i]).val + c)
      (h_val2' : ∀ i (hi : i < arr2.val.length) (hi' : i < arr2'.val.length),
        (arr2'.val[i]).val = (arr2.val[i]).val + d)
      (hr : Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r)
      (hr' : Aegis.MaxAbsValExpr.max_abs_val_expr arr1' arr2' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr1 arr2 arr1' arr2' : Slice Std.I64) (c d : Int) (r r' : Std.I64)
        (h_len : arr2.val.length = arr1.val.length)
        (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
        (h_b1 : ∀ i (hi : i < arr1.val.length),
          -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
        (h_b2 : ∀ i (hi : i < arr2.val.length),
          -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000)
        (h_c1 : ∀ i (hi : i < arr1.val.length),
          -1000000 ≤ (arr1.val[i]).val + c ∧ (arr1.val[i]).val + c ≤ 1000000)
        (h_c2 : ∀ i (hi : i < arr2.val.length),
          -1000000 ≤ (arr2.val[i]).val + d ∧ (arr2.val[i]).val + d ≤ 1000000)
        (h_len1' : arr1'.val.length = arr1.val.length)
        (h_len2' : arr2'.val.length = arr2.val.length)
        (h_val1' : ∀ i (hi : i < arr1.val.length) (hi' : i < arr1'.val.length),
          (arr1'.val[i]).val = (arr1.val[i]).val + c)
        (h_val2' : ∀ i (hi : i < arr2.val.length) (hi' : i < arr2'.val.length),
          (arr2'.val[i]).val = (arr2.val[i]).val + d)
        (hr : Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r)
        (hr' : Aegis.MaxAbsValExpr.max_abs_val_expr arr1' arr2' = ok r'), r.val = r'.val) := by
    sorry

  /-- Define arr1'[i] = -arr1[i] and arr2'[i] = -arr2[i] for every i with 0 <= i < n. Whenever max_abs_val_expr arr1 arr2 returns r and max_abs_val_expr arr1' arr2' returns r', we have r = r'.
    Preconditions: Let n = len(arr1). The preconditions are: len(arr2) = n; 2 <= n <= 40000; for every i with 0 <= i < n, -1000000 <= arr1[i] <= 1000000 and -1000000 <= arr2[i] <= 1000000. -/
  theorem spec_8 (arr1 arr2 arr1' arr2' : Slice Std.I64) (r r' : Std.I64)
      (h_len : arr2.val.length = arr1.val.length)
      (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
      (h_b1 : ∀ i (hi : i < arr1.val.length),
        -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
      (h_b2 : ∀ i (hi : i < arr2.val.length),
        -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000)
      (h_len1' : arr1'.val.length = arr1.val.length)
      (h_len2' : arr2'.val.length = arr2.val.length)
      (h_val1' : ∀ i (hi : i < arr1.val.length) (hi' : i < arr1'.val.length),
        (arr1'.val[i]).val = -((arr1.val[i]).val))
      (h_val2' : ∀ i (hi : i < arr2.val.length) (hi' : i < arr2'.val.length),
        (arr2'.val[i]).val = -((arr2.val[i]).val))
      (hr : Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r)
      (hr' : Aegis.MaxAbsValExpr.max_abs_val_expr arr1' arr2' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr1 arr2 arr1' arr2' : Slice Std.I64) (r r' : Std.I64)
        (h_len : arr2.val.length = arr1.val.length)
        (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
        (h_b1 : ∀ i (hi : i < arr1.val.length),
          -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
        (h_b2 : ∀ i (hi : i < arr2.val.length),
          -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000)
        (h_len1' : arr1'.val.length = arr1.val.length)
        (h_len2' : arr2'.val.length = arr2.val.length)
        (h_val1' : ∀ i (hi : i < arr1.val.length) (hi' : i < arr1'.val.length),
          (arr1'.val[i]).val = -((arr1.val[i]).val))
        (h_val2' : ∀ i (hi : i < arr2.val.length) (hi' : i < arr2'.val.length),
          (arr2'.val[i]).val = -((arr2.val[i]).val))
        (hr : Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r)
        (hr' : Aegis.MaxAbsValExpr.max_abs_val_expr arr1' arr2' = ok r'), r.val = r'.val) := by
    sorry

  /-- Define arr1'[i] = arr1[n - 1 - i] and arr2'[i] = arr2[n - 1 - i] for every i with 0 <= i < n. Whenever max_abs_val_expr arr1 arr2 returns r and max_abs_val_expr arr1' arr2' returns r', we have r = r'.
    Preconditions: Let n = len(arr1). The preconditions are: len(arr2) = n; 2 <= n <= 40000; for every i with 0 <= i < n, -1000000 <= arr1[i] <= 1000000 and -1000000 <= arr2[i] <= 1000000. -/
  theorem spec_9 (arr1 arr2 arr1' arr2' : Slice Std.I64) (r r' : Std.I64)
      (h_len : arr2.val.length = arr1.val.length)
      (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
      (h_b1 : ∀ i (hi : i < arr1.val.length),
        -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
      (h_b2 : ∀ i (hi : i < arr2.val.length),
        -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000)
      (h_val1' : arr1'.val = arr1.val.reverse)
      (h_val2' : arr2'.val = arr2.val.reverse)
      (hr : Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r)
      (hr' : Aegis.MaxAbsValExpr.max_abs_val_expr arr1' arr2' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr1 arr2 arr1' arr2' : Slice Std.I64) (r r' : Std.I64)
        (h_len : arr2.val.length = arr1.val.length)
        (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
        (h_b1 : ∀ i (hi : i < arr1.val.length),
          -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
        (h_b2 : ∀ i (hi : i < arr2.val.length),
          -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000)
        (h_val1' : arr1'.val = arr1.val.reverse)
        (h_val2' : arr2'.val = arr2.val.reverse)
        (hr : Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r)
        (hr' : Aegis.MaxAbsValExpr.max_abs_val_expr arr1' arr2' = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever max_abs_val_expr arr1 arr2 returns a result r, r is the maximum of the set of all values |arr1[i] - arr1[j]| + |arr2[i] - arr2[j]| + (j - i) with 0 <= i < j < n.
    Preconditions: Let n = len(arr1). The preconditions are: len(arr2) = n; 2 <= n <= 40000; for every i with 0 <= i < n, -1000000 <= arr1[i] <= 1000000 and -1000000 <= arr2[i] <= 1000000. -/
  theorem spec_10 (arr1 arr2 : Slice Std.I64) (r : Std.I64)
      (h_len : arr2.val.length = arr1.val.length)
      (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
      (h_b1 : ∀ i (hi : i < arr1.val.length),
        -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
      (h_b2 : ∀ i (hi : i < arr2.val.length),
        -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000)
      (hr : Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r) :
      (∀ (i j : Nat) (hi : i < arr1.val.length) (hj : j < arr1.val.length), i < j →
          |(arr1.val[i]).val - (arr1.val[j]).val| +
              |(arr2.val[i]).val - (arr2.val[j]).val| + ((j : Int) - (i : Int)) ≤
            r.val) ∧
        (∃ (i j : Nat) (hi : i < arr1.val.length) (hj : j < arr1.val.length),
          i < j ∧
            |(arr1.val[i]).val - (arr1.val[j]).val| +
                |(arr2.val[i]).val - (arr2.val[j]).val| + ((j : Int) - (i : Int)) =
              r.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr1 arr2 : Slice Std.I64) (r : Std.I64)
        (h_len : arr2.val.length = arr1.val.length)
        (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
        (h_b1 : ∀ i (hi : i < arr1.val.length),
          -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
        (h_b2 : ∀ i (hi : i < arr2.val.length),
          -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000)
        (hr : Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r), (∀ (i j : Nat) (hi : i < arr1.val.length) (hj : j < arr1.val.length), i < j →
            |(arr1.val[i]).val - (arr1.val[j]).val| +
                |(arr2.val[i]).val - (arr2.val[j]).val| + ((j : Int) - (i : Int)) ≤
              r.val) ∧
          (∃ (i j : Nat) (hi : i < arr1.val.length) (hj : j < arr1.val.length),
            i < j ∧
              |(arr1.val[i]).val - (arr1.val[j]).val| +
                  |(arr2.val[i]).val - (arr2.val[j]).val| + ((j : Int) - (i : Int)) =
                r.val)) := by
    sorry

  /-- For every arr1 and arr2 satisfying the preconditions, max_abs_val_expr arr1 arr2 returns a result r (it does not fail), and r = max over s in {1,-1} and t in {1,-1} of (max_{0 <= i < n} (s*arr1[i] + t*arr2[i] + i) - min_{0 <= i < n} (s*arr1[i] + t*arr2[i] + i)), with all arithmetic in mathematical integers. Equivalently, r is the maximum over the four sign choices of the range of the sequence s*arr1[i] + t*arr2[i] + i.
    Preconditions: Let n = len(arr1). The preconditions are: len(arr2) = n; 2 <= n <= 40000; for every i with 0 <= i < n, -1000000 <= arr1[i] <= 1000000 and -1000000 <= arr2[i] <= 1000000. -/
  theorem spec_11 (arr1 arr2 : Slice Std.I64)
      (h_len : arr2.val.length = arr1.val.length)
      (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
      (h_b1 : ∀ i (hi : i < arr1.val.length),
        -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
      (h_b2 : ∀ i (hi : i < arr2.val.length),
        -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000) :
      ∃ r : Std.I64,
        Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r ∧
          r.val =
            max (max (signedRange arr1 arr2 1 1) (signedRange arr1 arr2 1 (-1)))
              (max (signedRange arr1 arr2 (-1) 1) (signedRange arr1 arr2 (-1) (-1))) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr1 arr2 : Slice Std.I64)
        (h_len : arr2.val.length = arr1.val.length)
        (h_n : 2 ≤ arr1.val.length ∧ arr1.val.length ≤ 40000)
        (h_b1 : ∀ i (hi : i < arr1.val.length),
          -1000000 ≤ (arr1.val[i]).val ∧ (arr1.val[i]).val ≤ 1000000)
        (h_b2 : ∀ i (hi : i < arr2.val.length),
          -1000000 ≤ (arr2.val[i]).val ∧ (arr2.val[i]).val ≤ 1000000), ∃ r : Std.I64,
          Aegis.MaxAbsValExpr.max_abs_val_expr arr1 arr2 = ok r ∧
            r.val =
              max (max (signedRange arr1 arr2 1 1) (signedRange arr1 arr2 1 (-1)))
                (max (signedRange arr1 arr2 (-1) 1) (signedRange arr1 arr2 (-1) (-1)))) := by
    sorry

  end AegisSpec.MaxAbsValExpr
