import Aegis.ValidMountainArray.Code.Funs

/-!
# Specifications of `Aegis.ValidMountainArray.valid_mountain_array`

LeetCode problem `valid-mountain-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ValidMountainArray

  def len (arr : Slice Std.I64) : Nat := arr.val.length

  def vals (arr : Slice Std.I64) : List Int := arr.val.map (fun x => x.val)

  def get (arr : Slice Std.I64) (i : Nat) : Int := (vals arr)[i]!

  def IsMountain (arr : Slice Std.I64) : Prop :=
    3 ≤ len arr ∧
      ∃ i, 0 < i ∧ i < len arr - 1 ∧
        (∀ j, j < i → get arr j < get arr (j + 1)) ∧
        (∀ j, i ≤ j → j < len arr - 1 → get arr j > get arr (j + 1))

  /-- The function returns a result r and does not fail. Let a mountain array mean an array with len(arr) >= 3 for which there exists an index i with 0 < i < len(arr)-1 such that (for every j with 0 <= j < i, arr[j] < arr[j+1]) and (for every j with i <= j < len(arr)-1, arr[j] > arr[j+1]). Then r = true if and only if arr is a mountain array; equivalently, r = false if and only if arr is not a mountain array.
    Preconditions: 1 <= len(arr) <= 10^4 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^4. -/
  theorem spec_1 (arr : Slice Std.I64)
      (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
      (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4) :
      ∃ r, Aegis.ValidMountainArray.valid_mountain_array arr = ok r ∧
        (r = true ↔ IsMountain arr) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
        (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4), ∃ r, Aegis.ValidMountainArray.valid_mountain_array arr = ok r ∧
          (r = true ↔ IsMountain arr)) := by
    sorry

  /-- The function returns a result r and does not fail for every arr satisfying the preconditions.
    Preconditions: 1 <= len(arr) <= 10^4 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^4. -/
  theorem spec_2 (arr : Slice Std.I64)
      (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
      (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4) :
      ∃ r, Aegis.ValidMountainArray.valid_mountain_array arr = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
        (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4), ∃ r, Aegis.ValidMountainArray.valid_mountain_array arr = ok r) := by
    sorry

  /-- Whenever the function returns a result r and len(arr) < 3, then r = false.
    Preconditions: 1 <= len(arr) <= 10^4 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^4. -/
  theorem spec_3 (arr : Slice Std.I64)
      (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
      (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
      (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
      (hlen : len arr < 3) :
      r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
        (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
        (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
        (hlen : len arr < 3), r = false) := by
    sorry

  /-- Whenever the function returns a result r and r = true, then len(arr) >= 3.
    Preconditions: 1 <= len(arr) <= 10^4 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^4. -/
  theorem spec_4 (arr : Slice Std.I64)
      (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
      (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
      (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
      (htrue : r = true) :
      3 ≤ len arr := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
        (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
        (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
        (htrue : r = true), 3 ≤ len arr) := by
    sorry

  /-- Whenever the function returns a result r and r = true, then len(arr) >= 2 and arr[0] < arr[1].
    Preconditions: 1 <= len(arr) <= 10^4 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^4. -/
  theorem spec_5 (arr : Slice Std.I64)
      (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
      (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
      (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
      (htrue : r = true) :
      2 ≤ len arr ∧ get arr 0 < get arr 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
        (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
        (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
        (htrue : r = true), 2 ≤ len arr ∧ get arr 0 < get arr 1) := by
    sorry

  /-- Whenever the function returns a result r and r = true, then len(arr) >= 2 and arr[len(arr)-2] > arr[len(arr)-1].
    Preconditions: 1 <= len(arr) <= 10^4 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^4. -/
  theorem spec_6 (arr : Slice Std.I64)
      (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
      (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
      (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
      (htrue : r = true) :
      2 ≤ len arr ∧ get arr (len arr - 2) > get arr (len arr - 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
        (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
        (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
        (htrue : r = true), 2 ≤ len arr ∧ get arr (len arr - 2) > get arr (len arr - 1)) := by
    sorry

  /-- Whenever the function returns a result r and there exists an index j with 0 <= j < len(arr)-1 such that arr[j] = arr[j+1], then r = false.
    Preconditions: 1 <= len(arr) <= 10^4 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^4. -/
  theorem spec_7 (arr : Slice Std.I64)
      (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
      (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
      (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
      (hdup : ∃ j, j < len arr - 1 ∧ get arr j = get arr (j + 1)) :
      r = false := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
        (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
        (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
        (hdup : ∃ j, j < len arr - 1 ∧ get arr j = get arr (j + 1)), r = false) := by
    sorry

  /-- Whenever the function returns a result r and for every j with 0 <= j < len(arr)-1 we have arr[j] < arr[j+1], then r = false.
    Preconditions: 1 <= len(arr) <= 10^4 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^4. -/
  theorem spec_8 (arr : Slice Std.I64)
      (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
      (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
      (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
      (hinc : ∀ j, j < len arr - 1 → get arr j < get arr (j + 1)) :
      r = false := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
        (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
        (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
        (hinc : ∀ j, j < len arr - 1 → get arr j < get arr (j + 1)), r = false) := by
    sorry

  /-- Whenever the function returns a result r and for every j with 0 <= j < len(arr)-1 we have arr[j] > arr[j+1], then r = false.
    Preconditions: 1 <= len(arr) <= 10^4 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^4. -/
  theorem spec_9 (arr : Slice Std.I64)
      (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
      (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
      (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
      (hdec : ∀ j, j < len arr - 1 → get arr j > get arr (j + 1)) :
      r = false := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
        (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
        (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
        (hdec : ∀ j, j < len arr - 1 → get arr j > get arr (j + 1)), r = false) := by
    sorry

  /-- Whenever the function returns a result r and len(arr) = 3, then r = true if and only if arr[0] < arr[1] and arr[1] > arr[2].
    Preconditions: 1 <= len(arr) <= 10^4 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^4. -/
  theorem spec_10 (arr : Slice Std.I64)
      (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
      (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
      (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
      (hlen : len arr = 3) :
      (r = true ↔ get arr 0 < get arr 1 ∧ get arr 1 > get arr 2) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
        (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
        (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
        (hlen : len arr = 3), (r = true ↔ get arr 0 < get arr 1 ∧ get arr 1 > get arr 2)) := by
    sorry

  /-- Whenever the function returns a result r and r = true, there exists an index i with 0 < i < len(arr)-1 such that for every k with 0 <= k < len(arr) and k != i, arr[i] > arr[k].
    Preconditions: 1 <= len(arr) <= 10^4 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^4. -/
  theorem spec_11 (arr : Slice Std.I64)
      (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
      (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
      (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
      (htrue : r = true) :
      ∃ i, 0 < i ∧ i < len arr - 1 ∧ ∀ k, k < len arr → k ≠ i → get arr i > get arr k := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
        (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
        (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
        (htrue : r = true), ∃ i, 0 < i ∧ i < len arr - 1 ∧ ∀ k, k < len arr → k ≠ i → get arr i > get arr k) := by
    sorry

  /-- Whenever the function returns a result r and r = true, there is exactly one index i with 0 < i < len(arr)-1 such that arr[i] > arr[i-1] and arr[i] > arr[i+1].
    Preconditions: 1 <= len(arr) <= 10^4 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^4. -/
  theorem spec_12 (arr : Slice Std.I64)
      (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
      (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
      (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
      (htrue : r = true) :
      ∃ i, 0 < i ∧ i < len arr - 1 ∧
        get arr i > get arr (i - 1) ∧ get arr i > get arr (i + 1) ∧
        ∀ i', 0 < i' → i' < len arr - 1 →
          get arr i' > get arr (i' - 1) → get arr i' > get arr (i' + 1) → i' = i := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
        (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
        (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
        (htrue : r = true), ∃ i, 0 < i ∧ i < len arr - 1 ∧
          get arr i > get arr (i - 1) ∧ get arr i > get arr (i + 1) ∧
          ∀ i', 0 < i' → i' < len arr - 1 →
            get arr i' > get arr (i' - 1) → get arr i' > get arr (i' + 1) → i' = i) := by
    sorry

  /-- Whenever the function returns a result r and there exists an index j with 0 < j < len(arr)-1 such that arr[j] < arr[j-1] and arr[j] < arr[j+1], then r = false.
    Preconditions: 1 <= len(arr) <= 10^4 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^4. -/
  theorem spec_13 (arr : Slice Std.I64)
      (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
      (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
      (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
      (hval : ∃ j, 0 < j ∧ j < len arr - 1 ∧
        get arr j < get arr (j - 1) ∧ get arr j < get arr (j + 1)) :
      r = false := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
        (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
        (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
        (hval : ∃ j, 0 < j ∧ j < len arr - 1 ∧
          get arr j < get arr (j - 1) ∧ get arr j < get arr (j + 1)), r = false) := by
    sorry

  /-- Whenever the function returns a result r and there is no index j with 0 < j < len(arr)-1 such that arr[j] > arr[j-1] and arr[j] > arr[j+1], then r = false.
    Preconditions: 1 <= len(arr) <= 10^4 and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^4. -/
  theorem spec_14 (arr : Slice Std.I64)
      (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
      (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
      (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
      (hnopeak : ¬ ∃ j, 0 < j ∧ j < len arr - 1 ∧
        get arr j > get arr (j - 1) ∧ get arr j > get arr (j + 1)) :
      r = false := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h1 : 1 ≤ len arr) (h2 : len arr ≤ 10 ^ 4)
        (h3 : ∀ i, i < len arr → 0 ≤ get arr i ∧ get arr i ≤ 10 ^ 4)
        (r : Bool) (hr : Aegis.ValidMountainArray.valid_mountain_array arr = ok r)
        (hnopeak : ¬ ∃ j, 0 < j ∧ j < len arr - 1 ∧
          get arr j > get arr (j - 1) ∧ get arr j > get arr (j + 1)), r = false) := by
    sorry

  end AegisSpec.ValidMountainArray
