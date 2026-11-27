import Aegis.MaxTurbulenceSize.Code.Funs

/-!
# Specifications of `Aegis.MaxTurbulenceSize.max_turbulence_size`

LeetCode problem `longest-turbulent-subarray`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxTurbulenceSize

  open Aegis.MaxTurbulenceSize

  def len (arr : Slice Std.I64) : Int := (arr.val.length : Int)

  def elem (arr : Slice Std.I64) (i : Int) : Int :=
    match arr.val[i.toNat]? with
    | some x => x.val
    | none => 0

  def Turbulent (arr : Slice Std.I64) (p q : Int) : Prop :=
    (∀ k : Int, p ≤ k → k < q → elem arr k ≠ elem arr (k + 1)) ∧
    (∀ k : Int, p ≤ k → k < q - 1 →
      (elem arr k < elem arr (k + 1) ∧ elem arr (k + 1) > elem arr (k + 2)) ∨
      (elem arr k > elem arr (k + 1) ∧ elem arr (k + 1) < elem arr (k + 2)))

  /-- The function returns a result r, and there exist integers i, j with 0 <= i <= j < len(arr) such that j - i + 1 = r and arr[i..j] is turbulent, and for every pair of integers i', j' with 0 <= i' <= j' < len(arr) such that arr[i'..j'] is turbulent, j' - i' + 1 <= r. Here arr[p..q] is turbulent if and only if for every k with p <= k < q, arr[k] != arr[k+1], and for every k with p <= k < q-1, either (arr[k] < arr[k+1] and arr[k+1] > arr[k+2]) or (arr[k] > arr[k+1] and arr[k+1] < arr[k+2]).
    Preconditions: len(arr) >= 1, len(arr) <= 40000, and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
  theorem spec_1 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
      (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
      ∃ r : Std.I64, max_turbulence_size arr = ok r ∧
        (∃ i j : Int, 0 ≤ i ∧ i ≤ j ∧ j < len arr ∧ j - i + 1 = r.val ∧ Turbulent arr i j) ∧
        (∀ i' j' : Int, 0 ≤ i' → i' ≤ j' → j' < len arr → Turbulent arr i' j' →
          j' - i' + 1 ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
        (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∃ r : Std.I64, max_turbulence_size arr = ok r ∧
          (∃ i j : Int, 0 ≤ i ∧ i ≤ j ∧ j < len arr ∧ j - i + 1 = r.val ∧ Turbulent arr i j) ∧
          (∀ i' j' : Int, 0 ≤ i' → i' ≤ j' → j' < len arr → Turbulent arr i' j' →
            j' - i' + 1 ≤ r.val)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, overflow, or go out of bounds).
    Preconditions: len(arr) >= 1, len(arr) <= 40000, and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
  theorem spec_2 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
      (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
      ∃ r : Std.I64, max_turbulence_size arr = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
        (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∃ r : Std.I64, max_turbulence_size arr = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= len(arr).
    Preconditions: len(arr) >= 1, len(arr) <= 40000, and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
  theorem spec_3 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
      (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
      ∀ r : Std.I64, max_turbulence_size arr = ok r → 1 ≤ r.val ∧ r.val ≤ len arr := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
        (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∀ r : Std.I64, max_turbulence_size arr = ok r → 1 ≤ r.val ∧ r.val ≤ len arr) := by
    sorry

  /-- Whenever the function returns a result r, there exist integers i, j with 0 <= i <= j < len(arr) such that j - i + 1 = r and arr[i..j] is turbulent, where arr[p..q] is turbulent iff for every k with p <= k < q, arr[k] != arr[k+1], and for every k with p <= k < q-1, either (arr[k] < arr[k+1] and arr[k+1] > arr[k+2]) or (arr[k] > arr[k+1] and arr[k+1] < arr[k+2]).
    Preconditions: len(arr) >= 1, len(arr) <= 40000, and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
  theorem spec_4 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
      (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
      ∀ r : Std.I64, max_turbulence_size arr = ok r →
        ∃ i j : Int, 0 ≤ i ∧ i ≤ j ∧ j < len arr ∧ j - i + 1 = r.val ∧ Turbulent arr i j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
        (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∀ r : Std.I64, max_turbulence_size arr = ok r →
          ∃ i j : Int, 0 ≤ i ∧ i ≤ j ∧ j < len arr ∧ j - i + 1 = r.val ∧ Turbulent arr i j) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of integers i, j with 0 <= i <= j < len(arr), if arr[i..j] is turbulent (defined as in spec_4) then j - i + 1 <= r.
    Preconditions: len(arr) >= 1, len(arr) <= 40000, and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
  theorem spec_5 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
      (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
      ∀ r : Std.I64, max_turbulence_size arr = ok r →
        ∀ i j : Int, 0 ≤ i → i ≤ j → j < len arr → Turbulent arr i j → j - i + 1 ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
        (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∀ r : Std.I64, max_turbulence_size arr = ok r →
          ∀ i j : Int, 0 ≤ i → i ≤ j → j < len arr → Turbulent arr i j → j - i + 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if for every i with 0 <= i < len(arr)-1, arr[i] = arr[i+1] (i.e., all elements of arr are equal).
    Preconditions: len(arr) >= 1, len(arr) <= 40000, and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
  theorem spec_6 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
      (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
      ∀ r : Std.I64, max_turbulence_size arr = ok r →
        (r.val = 1 ↔ ∀ i : Int, 0 ≤ i → i < len arr - 1 → elem arr i = elem arr (i + 1)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
        (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∀ r : Std.I64, max_turbulence_size arr = ok r →
          (r.val = 1 ↔ ∀ i : Int, 0 ≤ i → i < len arr - 1 → elem arr i = elem arr (i + 1))) := by
    sorry

  /-- Whenever the function returns a result r, r >= 2 if and only if there exists an integer i with 0 <= i < len(arr)-1 and arr[i] != arr[i+1].
    Preconditions: len(arr) >= 1, len(arr) <= 40000, and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
  theorem spec_7 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
      (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
      ∀ r : Std.I64, max_turbulence_size arr = ok r →
        (2 ≤ r.val ↔ ∃ i : Int, 0 ≤ i ∧ i < len arr - 1 ∧ elem arr i ≠ elem arr (i + 1)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
        (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∀ r : Std.I64, max_turbulence_size arr = ok r →
          (2 ≤ r.val ↔ ∃ i : Int, 0 ≤ i ∧ i < len arr - 1 ∧ elem arr i ≠ elem arr (i + 1))) := by
    sorry

  /-- Whenever the function returns a result r, r = min(len(arr), 2).
    Preconditions: len(arr) >= 1, len(arr) <= 40000, for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9, and either (for every i with 0 <= i < len(arr)-1, arr[i] < arr[i+1]) or (for every i with 0 <= i < len(arr)-1, arr[i] > arr[i+1]). -/
  theorem spec_8 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
      (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9)
      (hmono : (∀ i : Int, 0 ≤ i → i < len arr - 1 → elem arr i < elem arr (i + 1)) ∨
        (∀ i : Int, 0 ≤ i → i < len arr - 1 → elem arr i > elem arr (i + 1))) :
      ∀ r : Std.I64, max_turbulence_size arr = ok r → r.val = min (len arr) 2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
        (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9)
        (hmono : (∀ i : Int, 0 ≤ i → i < len arr - 1 → elem arr i < elem arr (i + 1)) ∨
          (∀ i : Int, 0 ≤ i → i < len arr - 1 → elem arr i > elem arr (i + 1))), ∀ r : Std.I64, max_turbulence_size arr = ok r → r.val = min (len arr) 2) := by
    sorry

  /-- Whenever the function returns a result r, r = len(arr) if and only if the whole array arr[0..len(arr)-1] is turbulent, where arr[p..q] is turbulent as defined in spec_4.
    Preconditions: len(arr) >= 1, len(arr) <= 40000, and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
  theorem spec_9 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
      (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
      ∀ r : Std.I64, max_turbulence_size arr = ok r →
        (r.val = len arr ↔ Turbulent arr 0 (len arr - 1)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
        (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∀ r : Std.I64, max_turbulence_size arr = ok r →
          (r.val = len arr ↔ Turbulent arr 0 (len arr - 1))) := by
    sorry

  /-- Whenever the function returns a result r, r >= 3 if and only if there exists an integer i with 0 <= i <= len(arr)-3 and either (arr[i] < arr[i+1] and arr[i+1] > arr[i+2]) or (arr[i] > arr[i+1] and arr[i+1] < arr[i+2]).
    Preconditions: len(arr) >= 1, len(arr) <= 40000, and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
  theorem spec_10 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
      (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
      ∀ r : Std.I64, max_turbulence_size arr = ok r →
        (3 ≤ r.val ↔ ∃ i : Int, 0 ≤ i ∧ i ≤ len arr - 3 ∧
          ((elem arr i < elem arr (i + 1) ∧ elem arr (i + 1) > elem arr (i + 2)) ∨
           (elem arr i > elem arr (i + 1) ∧ elem arr (i + 1) < elem arr (i + 2)))) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
        (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∀ r : Std.I64, max_turbulence_size arr = ok r →
          (3 ≤ r.val ↔ ∃ i : Int, 0 ≤ i ∧ i ≤ len arr - 3 ∧
            ((elem arr i < elem arr (i + 1) ∧ elem arr (i + 1) > elem arr (i + 2)) ∨
             (elem arr i > elem arr (i + 1) ∧ elem arr (i + 1) < elem arr (i + 2))))) := by
    sorry

  /-- For every nonzero integer c such that c * arr[i] is in the range -2^63 .. 2^63-1 for all i with 0 <= i < len(arr), if brr is defined by brr[i] = c * arr[i], then whenever the function returns a result r for arr, it also returns a result r' for brr and r = r'.
    Preconditions: len(arr) >= 1, len(arr) <= 40000, and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
  theorem spec_11 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
      (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
      ∀ c : Int, c ≠ 0 →
        (∀ i : Int, 0 ≤ i → i < len arr →
          -(2 ^ 63) ≤ c * elem arr i ∧ c * elem arr i ≤ 2 ^ 63 - 1) →
        ∀ brr : Slice Std.I64, brr.val.length = arr.val.length →
          (∀ i : Int, 0 ≤ i → i < len arr → elem brr i = c * elem arr i) →
          ∀ r : Std.I64, max_turbulence_size arr = ok r →
            ∃ r' : Std.I64, max_turbulence_size brr = ok r' ∧ r'.val = r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
        (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∀ c : Int, c ≠ 0 →
          (∀ i : Int, 0 ≤ i → i < len arr →
            -(2 ^ 63) ≤ c * elem arr i ∧ c * elem arr i ≤ 2 ^ 63 - 1) →
          ∀ brr : Slice Std.I64, brr.val.length = arr.val.length →
            (∀ i : Int, 0 ≤ i → i < len arr → elem brr i = c * elem arr i) →
            ∀ r : Std.I64, max_turbulence_size arr = ok r →
              ∃ r' : Std.I64, max_turbulence_size brr = ok r' ∧ r'.val = r.val) := by
    sorry

  /-- For every slice brr of Std.I64 with len(brr) = len(arr) such that for every i with 0 <= i < len(arr)-1, (arr[i] < arr[i+1] iff brr[i] < brr[i+1]) and (arr[i] = arr[i+1] iff brr[i] = brr[i+1]), whenever the function returns a result r for arr, it also returns a result r' for brr and r = r'.
    Preconditions: len(arr) >= 1, len(arr) <= 40000, and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
  theorem spec_12 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
      (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
      ∀ brr : Slice Std.I64, brr.val.length = arr.val.length →
        (∀ i : Int, 0 ≤ i → i < len arr - 1 →
          (elem arr i < elem arr (i + 1) ↔ elem brr i < elem brr (i + 1)) ∧
          (elem arr i = elem arr (i + 1) ↔ elem brr i = elem brr (i + 1))) →
        ∀ r : Std.I64, max_turbulence_size arr = ok r →
          ∃ r' : Std.I64, max_turbulence_size brr = ok r' ∧ r'.val = r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
        (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∀ brr : Slice Std.I64, brr.val.length = arr.val.length →
          (∀ i : Int, 0 ≤ i → i < len arr - 1 →
            (elem arr i < elem arr (i + 1) ↔ elem brr i < elem brr (i + 1)) ∧
            (elem arr i = elem arr (i + 1) ↔ elem brr i = elem brr (i + 1))) →
          ∀ r : Std.I64, max_turbulence_size arr = ok r →
            ∃ r' : Std.I64, max_turbulence_size brr = ok r' ∧ r'.val = r.val) := by
    sorry

  /-- Let brr be the array defined by brr[i] = arr[len(arr)-1-i] for 0 <= i < len(arr). Whenever the function returns a result r for arr, it also returns a result r' for brr and r = r'.
    Preconditions: len(arr) >= 1, len(arr) <= 40000, and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 10^9. -/
  theorem spec_13 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
      (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
      ∀ brr : Slice Std.I64, brr.val.length = arr.val.length →
        (∀ i : Int, 0 ≤ i → i < len arr → elem brr i = elem arr (len arr - 1 - i)) →
        ∀ r : Std.I64, max_turbulence_size arr = ok r →
          ∃ r' : Std.I64, max_turbulence_size brr = ok r' ∧ r'.val = r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ len arr) (hlen_hi : len arr ≤ 40000)
        (hbound : ∀ i : Int, 0 ≤ i → i < len arr → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∀ brr : Slice Std.I64, brr.val.length = arr.val.length →
          (∀ i : Int, 0 ≤ i → i < len arr → elem brr i = elem arr (len arr - 1 - i)) →
          ∀ r : Std.I64, max_turbulence_size arr = ok r →
            ∃ r' : Std.I64, max_turbulence_size brr = ok r' ∧ r'.val = r.val) := by
    sorry

  end AegisSpec.MaxTurbulenceSize
