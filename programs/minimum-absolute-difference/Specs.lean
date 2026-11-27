import Aegis.MinimumAbsDifference.Code.Funs

/-!
# Specifications of `Aegis.MinimumAbsDifference.minimum_abs_difference`

LeetCode problem `minimum-absolute-difference`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumAbsDifference

  def arrInts (arr : Slice Std.I64) : List ℤ := arr.val.map (fun x => x.val)

  def vecInts (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map (fun x => x.val)

  def arrAt (arr : Slice Std.I64) (i : ℕ) : ℤ := (arrInts arr).getD i 0

  def rowInts (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (k : ℕ) : List ℤ :=
    ((r.val[k]?).map vecInts).getD []

  def rowAt (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (k j : ℕ) : ℤ :=
    (rowInts r k).getD j 0

  def Occurs (arr : Slice Std.I64) (x : ℤ) : Prop := x ∈ arrInts arr

  def OccursTwice (arr : Slice Std.I64) (x : ℤ) : Prop :=
    ∃ i j : ℕ, i < j ∧ j < arr.val.length ∧ arrAt arr i = x ∧ arrAt arr j = x

  def listAbsDiffs (xs : List ℤ) : List ℤ :=
    (List.range xs.length).flatMap (fun i =>
      (List.range xs.length).flatMap (fun j =>
        if i < j then [((xs.getD i 0 - xs.getD j 0).natAbs : ℤ)] else []))

  def minAbsDiff (arr : Slice Std.I64) : ℤ := (listAbsDiffs (arrInts arr)).min?.getD 0

  /-- Let n = len(arr) and let d = min_{0 <= i < j < n} |arr[i] - arr[j]|. The function returns a result r such that r is exactly the list, in strictly ascending lexicographic order, of all pairs [a,b] for which: (1) a <= b; (2) a occurs in arr and b occurs in arr; (3) b - a = d; and (4) if a = b then a occurs at least twice in arr, i.e. there exist i < j with arr[i] = arr[j] = a. 'Exactly' means that for every such [a,b] there is exactly one index k with 0 <= k < len(r) and r[k] = [a,b], and every index k with 0 <= k < len(r) has len(r[k]) = 2 and r[k] equal to one of those pairs. 'Strictly ascending lexicographic order' means for every k with 0 <= k < len(r)-1, either r[k][0] < r[k+1][0], or r[k][0] = r[k+1][0] and r[k][1] < r[k+1][1].
    Preconditions: len(arr) >= 2 and len(arr) <= 100000; for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_1 (arr : Slice Std.I64)
      (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
      (h_range : ∀ i : ℕ, i < arr.val.length →
        -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r ∧

        (∀ a b : ℤ, a ≤ b → Occurs arr a → Occurs arr b →
          b - a = minAbsDiff arr → (a = b → OccursTwice arr a) →
          ∃! k : ℕ, k < r.val.length ∧ rowInts r k = [a, b]) ∧

        (∀ k : ℕ, k < r.val.length →
          (rowInts r k).length = 2 ∧
          ∃ a b : ℤ, a ≤ b ∧ Occurs arr a ∧ Occurs arr b ∧
            b - a = minAbsDiff arr ∧ (a = b → OccursTwice arr a) ∧
            rowInts r k = [a, b]) ∧

        (∀ k : ℕ, k + 1 < r.val.length →
          rowAt r k 0 < rowAt r (k + 1) 0 ∨
          (rowAt r k 0 = rowAt r (k + 1) 0 ∧ rowAt r k 1 < rowAt r (k + 1) 1)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
        (h_range : ∀ i : ℕ, i < arr.val.length →
          -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r ∧

          (∀ a b : ℤ, a ≤ b → Occurs arr a → Occurs arr b →
            b - a = minAbsDiff arr → (a = b → OccursTwice arr a) →
            ∃! k : ℕ, k < r.val.length ∧ rowInts r k = [a, b]) ∧

          (∀ k : ℕ, k < r.val.length →
            (rowInts r k).length = 2 ∧
            ∃ a b : ℤ, a ≤ b ∧ Occurs arr a ∧ Occurs arr b ∧
              b - a = minAbsDiff arr ∧ (a = b → OccursTwice arr a) ∧
              rowInts r k = [a, b]) ∧

          (∀ k : ℕ, k + 1 < r.val.length →
            rowAt r k 0 < rowAt r (k + 1) 0 ∨
            (rowAt r k 0 = rowAt r (k + 1) 0 ∧ rowAt r k 1 < rowAt r (k + 1) 1))) := by
    sorry

  /-- The function returns a result r; it does not fail.
    Preconditions: len(arr) >= 2 and len(arr) <= 100000; for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_2 (arr : Slice Std.I64)
      (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
      (h_range : ∀ i : ℕ, i < arr.val.length →
        -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
        (h_range : ∀ i : ℕ, i < arr.val.length →
          -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(r), the value r[k] is a list (vector) of length exactly 2.
    Preconditions: len(arr) >= 2 and len(arr) <= 100000; for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_3 (arr : Slice Std.I64)
      (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
      (h_range : ∀ i : ℕ, i < arr.val.length →
        -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
        ∀ k : ℕ, k < r.val.length → (rowInts r k).length = 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
        (h_range : ∀ i : ℕ, i < arr.val.length →
          -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
          ∀ k : ℕ, k < r.val.length → (rowInts r k).length = 2) := by
    sorry

  /-- Whenever the function returns a result r, r is in strictly ascending lexicographic order: for every k with 0 <= k < len(r)-1, either r[k][0] < r[k+1][0], or r[k][0] = r[k+1][0] and r[k][1] < r[k+1][1].
    Preconditions: len(arr) >= 2 and len(arr) <= 100000; for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_4 (arr : Slice Std.I64)
      (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
      (h_range : ∀ i : ℕ, i < arr.val.length →
        -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
        ∀ k : ℕ, k + 1 < r.val.length →
          rowAt r k 0 < rowAt r (k + 1) 0 ∨
          (rowAt r k 0 = rowAt r (k + 1) 0 ∧ rowAt r k 1 < rowAt r (k + 1) 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
        (h_range : ∀ i : ℕ, i < arr.val.length →
          -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
          ∀ k : ℕ, k + 1 < r.val.length →
            rowAt r k 0 < rowAt r (k + 1) 0 ∨
            (rowAt r k 0 = rowAt r (k + 1) 0 ∧ rowAt r k 1 < rowAt r (k + 1) 1)) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(r) and for j in {0,1}, the value r[k][j] occurs in arr: there exists i with 0 <= i < len(arr) and arr[i] = r[k][j].
    Preconditions: len(arr) >= 2 and len(arr) <= 100000; for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_5 (arr : Slice Std.I64)
      (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
      (h_range : ∀ i : ℕ, i < arr.val.length →
        -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
        ∀ k j : ℕ, k < r.val.length → j < 2 → Occurs arr (rowAt r k j) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
        (h_range : ∀ i : ℕ, i < arr.val.length →
          -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
          ∀ k j : ℕ, k < r.val.length → j < 2 → Occurs arr (rowAt r k j)) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(r) and for j in {0,1}, -1000000 <= r[k][j] <= 1000000.
    Preconditions: len(arr) >= 2 and len(arr) <= 100000; for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_6 (arr : Slice Std.I64)
      (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
      (h_range : ∀ i : ℕ, i < arr.val.length →
        -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
        ∀ k j : ℕ, k < r.val.length → j < 2 →
          -1000000 ≤ rowAt r k j ∧ rowAt r k j ≤ 1000000 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
        (h_range : ∀ i : ℕ, i < arr.val.length →
          -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
          ∀ k j : ℕ, k < r.val.length → j < 2 →
            -1000000 ≤ rowAt r k j ∧ rowAt r k j ≤ 1000000) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(r), r[k][0] <= r[k][1].
    Preconditions: len(arr) >= 2 and len(arr) <= 100000; for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_7 (arr : Slice Std.I64)
      (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
      (h_range : ∀ i : ℕ, i < arr.val.length →
        -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
        ∀ k : ℕ, k < r.val.length → rowAt r k 0 ≤ rowAt r k 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
        (h_range : ∀ i : ℕ, i < arr.val.length →
          -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
          ∀ k : ℕ, k < r.val.length → rowAt r k 0 ≤ rowAt r k 1) := by
    sorry

  /-- Let n = len(arr) and d = min_{0 <= i < j < n} |arr[i] - arr[j]|. Whenever the function returns a result r, for every k with 0 <= k < len(r), r[k][1] - r[k][0] = d.
    Preconditions: len(arr) >= 2 and len(arr) <= 100000; for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_8 (arr : Slice Std.I64)
      (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
      (h_range : ∀ i : ℕ, i < arr.val.length →
        -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
        ∀ k : ℕ, k < r.val.length → rowAt r k 1 - rowAt r k 0 = minAbsDiff arr := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
        (h_range : ∀ i : ℕ, i < arr.val.length →
          -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
          ∀ k : ℕ, k < r.val.length → rowAt r k 1 - rowAt r k 0 = minAbsDiff arr) := by
    sorry

  /-- Let n = len(arr) and d = min_{0 <= i < j < n} |arr[i] - arr[j]|. Whenever the function returns a result r, for every k with 0 <= k < len(r), if r[k][0] = r[k][1], then d = 0 and the value r[k][0] occurs at least twice in arr, i.e. there exist i < j with arr[i] = arr[j] = r[k][0].
    Preconditions: len(arr) >= 2 and len(arr) <= 100000; for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_9 (arr : Slice Std.I64)
      (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
      (h_range : ∀ i : ℕ, i < arr.val.length →
        -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
        ∀ k : ℕ, k < r.val.length → rowAt r k 0 = rowAt r k 1 →
          minAbsDiff arr = 0 ∧ OccursTwice arr (rowAt r k 0) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
        (h_range : ∀ i : ℕ, i < arr.val.length →
          -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
          ∀ k : ℕ, k < r.val.length → rowAt r k 0 = rowAt r k 1 →
            minAbsDiff arr = 0 ∧ OccursTwice arr (rowAt r k 0)) := by
    sorry

  /-- Let n = len(arr) and d = min_{0 <= i < j < n} |arr[i] - arr[j]|. Whenever the function returns a result r, for every pair of integers [a,b] such that a <= b, both a and b occur in arr, b - a = d, and (if a = b then a occurs at least twice in arr), there exists k with 0 <= k < len(r) and r[k] = [a,b].
    Preconditions: len(arr) >= 2 and len(arr) <= 100000; for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_10 (arr : Slice Std.I64)
      (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
      (h_range : ∀ i : ℕ, i < arr.val.length →
        -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
        ∀ a b : ℤ, a ≤ b → Occurs arr a → Occurs arr b →
          b - a = minAbsDiff arr → (a = b → OccursTwice arr a) →
          ∃ k : ℕ, k < r.val.length ∧ rowInts r k = [a, b] := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
        (h_range : ∀ i : ℕ, i < arr.val.length →
          -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
          ∀ a b : ℤ, a ≤ b → Occurs arr a → Occurs arr b →
            b - a = minAbsDiff arr → (a = b → OccursTwice arr a) →
            ∃ k : ℕ, k < r.val.length ∧ rowInts r k = [a, b]) := by
    sorry

  /-- Whenever the function returns a result r, no pair occurs twice in r: for all k and l with 0 <= k < l < len(r), r[k] != r[l].
    Preconditions: len(arr) >= 2 and len(arr) <= 100000; for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_11 (arr : Slice Std.I64)
      (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
      (h_range : ∀ i : ℕ, i < arr.val.length →
        -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
        ∀ k l : ℕ, k < l → l < r.val.length → rowInts r k ≠ rowInts r l := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
        (h_range : ∀ i : ℕ, i < arr.val.length →
          -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
          ∀ k l : ℕ, k < l → l < r.val.length → rowInts r k ≠ rowInts r l) := by
    sorry

  /-- Whenever the function returns a result r, len(r) >= 1.
    Preconditions: len(arr) >= 2 and len(arr) <= 100000; for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_12 (arr : Slice Std.I64)
      (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
      (h_range : ∀ i : ℕ, i < arr.val.length →
        -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
        1 ≤ r.val.length := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
        (h_range : ∀ i : ℕ, i < arr.val.length →
          -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
          1 ≤ r.val.length) := by
    sorry

  /-- Whenever the function returns a result r, len(r) <= len(arr) - 1.
    Preconditions: len(arr) >= 2 and len(arr) <= 100000; for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_13 (arr : Slice Std.I64)
      (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
      (h_range : ∀ i : ℕ, i < arr.val.length →
        -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
        r.val.length ≤ arr.val.length - 1 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
        (h_range : ∀ i : ℕ, i < arr.val.length →
          -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
          r.val.length ≤ arr.val.length - 1) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(r), if r[k][0] < r[k][1], then there is no index i with 0 <= i < len(arr) and r[k][0] < arr[i] < r[k][1].
    Preconditions: len(arr) >= 2 and len(arr) <= 100000; for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_14 (arr : Slice Std.I64)
      (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
      (h_range : ∀ i : ℕ, i < arr.val.length →
        -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
        ∀ k : ℕ, k < r.val.length → rowAt r k 0 < rowAt r k 1 →
          ¬ ∃ i : ℕ, i < arr.val.length ∧
            rowAt r k 0 < arrAt arr i ∧ arrAt arr i < rowAt r k 1 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 2 ≤ arr.val.length) (h_len_le : arr.val.length ≤ 100000)
        (h_range : ∀ i : ℕ, i < arr.val.length →
          -1000000 ≤ arrAt arr i ∧ arrAt arr i ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.MinimumAbsDifference.minimum_abs_difference arr = ok r →
          ∀ k : ℕ, k < r.val.length → rowAt r k 0 < rowAt r k 1 →
            ¬ ∃ i : ℕ, i < arr.val.length ∧
              rowAt r k 0 < arrAt arr i ∧ arrAt arr i < rowAt r k 1) := by
    sorry

  end AegisSpec.MinimumAbsDifference
