import Aegis.FixedPoint.Code.Funs

/-!
# Specifications of `Aegis.FixedPoint.fixed_point`

LeetCode problem `fixed-point`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FixedPoint

def elem? (arr : Slice I64) (i : Nat) : Option Int :=
  (arr.val[i]?).map (fun x => x.val)

def IsFixedPointIndex (arr : Slice I64) (i : Nat) : Prop :=
  elem? arr i = some (i : Int)

def IsLeastFixedPointOrMinusOne (arr : Slice I64) (r : I64) : Prop :=
  (∃ i : Nat,
      IsFixedPointIndex arr i ∧ r.val = (i : Int) ∧
        ∀ j : Nat, IsFixedPointIndex arr j → i ≤ j) ∨
    (r.val = -1 ∧ ∀ j : Nat, ¬ IsFixedPointIndex arr j)

def BelowDiagonal (arr : Slice I64) (i : Nat) : Prop :=
  ∃ v : Int, elem? arr i = some v ∧ v < (i : Int)

def AboveDiagonal (arr : Slice I64) (i : Nat) : Prop :=
  ∃ v : Int, elem? arr i = some v ∧ (i : Int) ≤ v

def FirstEntryPositive (arr : Slice I64) : Prop :=
  ∃ v : Int, elem? arr 0 = some v ∧ 0 < v

def LastEntryBelowLastIndex (arr : Slice I64) : Prop :=
  ∃ v : Int, elem? arr (arr.val.length - 1) = some v ∧ v < (arr.val.length : Int) - 1

def StrictlyIncreasing (arr : Slice I64) : Prop :=
  arr.val.Pairwise (fun x y => x.val < y.val)

def ValueBounded (arr : Slice I64) : Prop :=
  ∀ x : I64, x ∈ arr.val → -(10 ^ 9) ≤ x.val ∧ x.val ≤ 10 ^ 9

/-- For every arr satisfying the preconditions, the function returns a result r, and r is determined as follows: if there exists an index i with 0 <= i < len(arr) and arr[i] = i, then r is the smallest such index i; otherwise r = -1.
  Preconditions: arr is a slice of 64-bit integers with len(arr) >= 1, len(arr) < 10^4, arr[0] < arr[1] < ... < arr[len(arr)-1] (strictly increasing, hence all elements distinct), and for every i with 0 <= i < len(arr), -10^9 <= arr[i] <= 10^9. -/
theorem spec_1 (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr) :
    ∃ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r ∧ IsLeastFixedPointOrMinusOne arr r := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr), ∃ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r ∧ IsLeastFixedPointOrMinusOne arr r) := by
  sorry

/-- For every arr satisfying the preconditions, the function returns a result (it does not fail, overflow, panic, or access memory out of bounds).
  Preconditions: arr is a slice of 64-bit integers with len(arr) >= 1, len(arr) < 10^4, arr[0] < arr[1] < ... < arr[len(arr)-1] (strictly increasing, hence all elements distinct), and for every i with 0 <= i < len(arr), -10^9 <= arr[i] <= 10^9. -/
theorem spec_2 (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr) :
    ∃ r : I64, Aegis.FixedPoint.fixed_point arr = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr), ∃ r : I64, Aegis.FixedPoint.fixed_point arr = ok r) := by
  sorry

/-- Whenever the function returns a result r and r != -1, we have 0 <= r < len(arr) and arr[r] = r.
  Preconditions: arr is a slice of 64-bit integers with len(arr) >= 1, len(arr) < 10^4, arr[0] < arr[1] < ... < arr[len(arr)-1] (strictly increasing, hence all elements distinct), and for every i with 0 <= i < len(arr), -10^9 <= arr[i] <= 10^9. -/
theorem spec_3 (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr) :
    ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r → r.val ≠ -1 →
        0 ≤ r.val ∧ r.val < (arr.val.length : Int) ∧
          ∃ i : Nat, r.val = (i : Int) ∧ IsFixedPointIndex arr i := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr), ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r → r.val ≠ -1 →
        0 ≤ r.val ∧ r.val < (arr.val.length : Int) ∧
          ∃ i : Nat, r.val = (i : Int) ∧ IsFixedPointIndex arr i) := by
  sorry

/-- Whenever the function returns a result r and r = -1, for every i with 0 <= i < len(arr), arr[i] != i.
  Preconditions: arr is a slice of 64-bit integers with len(arr) >= 1, len(arr) < 10^4, arr[0] < arr[1] < ... < arr[len(arr)-1] (strictly increasing, hence all elements distinct), and for every i with 0 <= i < len(arr), -10^9 <= arr[i] <= 10^9. -/
theorem spec_4 (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr) :
    ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r → r.val = -1 →
        ∀ i : Nat, ¬ IsFixedPointIndex arr i := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr), ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r → r.val = -1 →
        ∀ i : Nat, ¬ IsFixedPointIndex arr i) := by
  sorry

/-- Whenever the function returns a result r and r != -1, for every i with 0 <= i < r, arr[i] != i.
  Preconditions: arr is a slice of 64-bit integers with len(arr) >= 1, len(arr) < 10^4, arr[0] < arr[1] < ... < arr[len(arr)-1] (strictly increasing, hence all elements distinct), and for every i with 0 <= i < len(arr), -10^9 <= arr[i] <= 10^9. -/
theorem spec_5 (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr) :
    ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r → r.val ≠ -1 →
        ∀ i : Nat, (i : Int) < r.val → ¬ IsFixedPointIndex arr i := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr), ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r → r.val ≠ -1 →
        ∀ i : Nat, (i : Int) < r.val → ¬ IsFixedPointIndex arr i) := by
  sorry

/-- Whenever the function returns a result r, -1 <= r < len(arr).
  Preconditions: arr is a slice of 64-bit integers with len(arr) >= 1, len(arr) < 10^4, arr[0] < arr[1] < ... < arr[len(arr)-1] (strictly increasing, hence all elements distinct), and for every i with 0 <= i < len(arr), -10^9 <= arr[i] <= 10^9. -/
theorem spec_6 (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr) :
    ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r →
        -1 ≤ r.val ∧ r.val < (arr.val.length : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr), ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r →
        -1 ≤ r.val ∧ r.val < (arr.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r != -1 if and only if there exists i with 0 <= i < len(arr) and arr[i] = i.
  Preconditions: arr is a slice of 64-bit integers with len(arr) >= 1, len(arr) < 10^4, arr[0] < arr[1] < ... < arr[len(arr)-1] (strictly increasing, hence all elements distinct), and for every i with 0 <= i < len(arr), -10^9 <= arr[i] <= 10^9. -/
theorem spec_7 (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr) :
    ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r →
        (r.val ≠ -1 ↔ ∃ i : Nat, IsFixedPointIndex arr i) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr), ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r →
        (r.val ≠ -1 ↔ ∃ i : Nat, IsFixedPointIndex arr i)) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(arr) and arr[j] = j, we have r != -1 and r <= j.
  Preconditions: arr is a slice of 64-bit integers with len(arr) >= 1, len(arr) < 10^4, arr[0] < arr[1] < ... < arr[len(arr)-1] (strictly increasing, hence all elements distinct), and for every i with 0 <= i < len(arr), -10^9 <= arr[i] <= 10^9. -/
theorem spec_8 (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr) :
    ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r →
        ∀ j : Nat, IsFixedPointIndex arr j → r.val ≠ -1 ∧ r.val ≤ (j : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr), ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r →
        ∀ j : Nat, IsFixedPointIndex arr j → r.val ≠ -1 ∧ r.val ≤ (j : Int)) := by
  sorry

/-- Whenever the function returns a result r and arr[0] = 0, we have r = 0.
  Preconditions: arr is a slice of 64-bit integers with len(arr) >= 1, len(arr) < 10^4, arr[0] < arr[1] < ... < arr[len(arr)-1] (strictly increasing, hence all elements distinct), and for every i with 0 <= i < len(arr), -10^9 <= arr[i] <= 10^9. -/
theorem spec_9 (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr) :
    ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r → IsFixedPointIndex arr 0 → r.val = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr), ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r → IsFixedPointIndex arr 0 → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r and arr[len(arr)-1] < len(arr)-1, we have r = -1.
  Preconditions: arr is a slice of 64-bit integers with len(arr) >= 1, len(arr) < 10^4, arr[0] < arr[1] < ... < arr[len(arr)-1] (strictly increasing, hence all elements distinct), and for every i with 0 <= i < len(arr), -10^9 <= arr[i] <= 10^9. -/
theorem spec_10 (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr) :
    ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r → LastEntryBelowLastIndex arr → r.val = -1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr), ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r → LastEntryBelowLastIndex arr → r.val = -1) := by
  sorry

/-- Whenever the function returns a result r and len(arr) = 1, if arr[0] = 0 then r = 0, and if arr[0] != 0 then r = -1.
  Preconditions: arr is a slice of 64-bit integers with len(arr) >= 1, len(arr) < 10^4, arr[0] < arr[1] < ... < arr[len(arr)-1] (strictly increasing, hence all elements distinct), and for every i with 0 <= i < len(arr), -10^9 <= arr[i] <= 10^9. -/
theorem spec_11 (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr) :
    ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r → arr.val.length = 1 →
        (IsFixedPointIndex arr 0 → r.val = 0) ∧
          (¬ IsFixedPointIndex arr 0 → r.val = -1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr), ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r → arr.val.length = 1 →
        (IsFixedPointIndex arr 0 → r.val = 0) ∧
          (¬ IsFixedPointIndex arr 0 → r.val = -1)) := by
  sorry

/-- Whenever the function returns a result r and r != -1, for every i with 0 <= i < r, arr[i] < i, and for every i with r < i < len(arr), arr[i] >= i.
  Preconditions: arr is a slice of 64-bit integers with len(arr) >= 1, len(arr) < 10^4, arr[0] < arr[1] < ... < arr[len(arr)-1] (strictly increasing, hence all elements distinct), and for every i with 0 <= i < len(arr), -10^9 <= arr[i] <= 10^9. -/
theorem spec_12 (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr) :
    ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r → r.val ≠ -1 →
        (∀ i : Nat, (i : Int) < r.val → BelowDiagonal arr i) ∧
          (∀ i : Nat, r.val < (i : Int) → AboveDiagonal arr i) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr), ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r → r.val ≠ -1 →
        (∀ i : Nat, (i : Int) < r.val → BelowDiagonal arr i) ∧
          (∀ i : Nat, r.val < (i : Int) → AboveDiagonal arr i)) := by
  sorry

/-- Whenever the function returns a result r and arr[0] > 0, we have r = -1.
  Preconditions: arr is a slice of 64-bit integers with len(arr) >= 1, len(arr) < 10^4, arr[0] < arr[1] < ... < arr[len(arr)-1] (strictly increasing, hence all elements distinct), and for every i with 0 <= i < len(arr), -10^9 <= arr[i] <= 10^9. -/
theorem spec_13 (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr) :
    ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r → FirstEntryPositive arr → r.val = -1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (arr : Slice I64)
    (h_len_ge_one : 1 ≤ arr.val.length) (h_len_lt_max : arr.val.length < 10 ^ 4)
    (h_sorted : StrictlyIncreasing arr) (h_bounds : ValueBounded arr), ∀ r : I64,
      Aegis.FixedPoint.fixed_point arr = ok r → FirstEntryPositive arr → r.val = -1) := by
  sorry

end AegisSpec.FixedPoint
