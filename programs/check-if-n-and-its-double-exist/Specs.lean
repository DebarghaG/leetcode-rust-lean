import Aegis.CheckIfExist.Code.Funs

/-!
# Specifications of `Aegis.CheckIfExist.check_if_exist`

LeetCode problem `check-if-n-and-its-double-exist`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CheckIfExist

namespace AegisSpec.CheckIfExist

def contents (arr : Slice Std.I64) : List ℤ := arr.val.map (fun x => x.val)

def HasDoublePair (arr : Slice Std.I64) : Prop :=
  ∃ (i : Nat) (hi : i < arr.val.length) (j : Nat) (hj : j < arr.val.length),
    i ≠ j ∧ (arr.val[i]'hi).val = 2 * (arr.val[j]'hj).val

def IsPermIndex (n : Nat) (p : Nat → Nat) : Prop :=
  (∀ k, k < n → p k < n) ∧
    (∀ k₁ k₂, k₁ < n → k₂ < n → p k₁ = p k₂ → k₁ = k₂)

def permutedContents (arr : Slice Std.I64) (p : Nat → Nat)
    (hp : ∀ k, k < arr.val.length → p k < arr.val.length) : List ℤ :=
  List.ofFn (fun k : Fin arr.val.length => (arr.val[p k.1]'(hp k.1 k.2)).val)

/-- Whenever check_if_exist returns a result r, r = true if and only if there exist indices i and j such that 0 <= i < len(arr), 0 <= j < len(arr), i != j, and arr[i] = 2 * arr[j] as mathematical integers. If no such pair of indices exists, then r = false.
  Preconditions: len(arr) >= 2 and len(arr) <= 500 and for every k with 0 <= k < len(arr), -1000 <= arr[k] <= 1000. -/
theorem spec_1 (arr : Slice Std.I64)
    (hlen_lo : 2 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 500)
    (hbounds : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ (arr.val[k]'hk).val ∧ (arr.val[k]'hk).val ≤ 1000)
    (r : Bool) (hr : check_if_exist arr = ok r) :
    (r = true ↔ HasDoublePair arr) ∧ (¬ HasDoublePair arr → r = false) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_lo : 2 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 500)
    (hbounds : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ (arr.val[k]'hk).val ∧ (arr.val[k]'hk).val ≤ 1000)
    (r : Bool) (hr : check_if_exist arr = ok r), (r = true ↔ HasDoublePair arr) ∧ (¬ HasDoublePair arr → r = false)) := by
  sorry

/-- For every arr satisfying the preconditions, the call check_if_exist arr returns a Bool result r and does not fail, panic, go out of bounds, or overflow.
  Preconditions: len(arr) >= 2 and len(arr) <= 500 and for every k with 0 <= k < len(arr), -1000 <= arr[k] <= 1000. -/
theorem spec_2 (arr : Slice Std.I64)
    (hlen_lo : 2 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 500)
    (hbounds : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ (arr.val[k]'hk).val ∧ (arr.val[k]'hk).val ≤ 1000) :
    ∃ (r : Bool), check_if_exist arr = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_lo : 2 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 500)
    (hbounds : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ (arr.val[k]'hk).val ∧ (arr.val[k]'hk).val ≤ 1000), ∃ (r : Bool), check_if_exist arr = ok r) := by
  sorry

/-- Whenever check_if_exist returns true, there exist indices i and j such that 0 <= i < len(arr), 0 <= j < len(arr), i != j, arr[i] is even, arr[j] = arr[i] / 2 using exact integer division, and arr[i] = 2 * arr[j].
  Preconditions: len(arr) >= 2 and len(arr) <= 500 and for every k with 0 <= k < len(arr), -1000 <= arr[k] <= 1000. -/
theorem spec_3 (arr : Slice Std.I64)
    (hlen_lo : 2 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 500)
    (hbounds : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ (arr.val[k]'hk).val ∧ (arr.val[k]'hk).val ≤ 1000) :
    check_if_exist arr = ok true →
      ∃ (i : Nat) (hi : i < arr.val.length) (j : Nat) (hj : j < arr.val.length),
        i ≠ j ∧ 2 ∣ (arr.val[i]'hi).val ∧
          (arr.val[j]'hj).val = (arr.val[i]'hi).val / 2 ∧
          (arr.val[i]'hi).val = 2 * (arr.val[j]'hj).val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_lo : 2 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 500)
    (hbounds : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ (arr.val[k]'hk).val ∧ (arr.val[k]'hk).val ≤ 1000), check_if_exist arr = ok true →
      ∃ (i : Nat) (hi : i < arr.val.length) (j : Nat) (hj : j < arr.val.length),
        i ≠ j ∧ 2 ∣ (arr.val[i]'hi).val ∧
          (arr.val[j]'hj).val = (arr.val[i]'hi).val / 2 ∧
          (arr.val[i]'hi).val = 2 * (arr.val[j]'hj).val) := by
  sorry

/-- Whenever check_if_exist returns true, there exists an index j with 0 <= j < len(arr) such that -500 <= arr[j] <= 500 and there exists an index i with 0 <= i < len(arr), i != j, and arr[i] = 2 * arr[j].
  Preconditions: len(arr) >= 2 and len(arr) <= 500 and for every k with 0 <= k < len(arr), -1000 <= arr[k] <= 1000. -/
theorem spec_4 (arr : Slice Std.I64)
    (hlen_lo : 2 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 500)
    (hbounds : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ (arr.val[k]'hk).val ∧ (arr.val[k]'hk).val ≤ 1000) :
    check_if_exist arr = ok true →
      ∃ (j : Nat) (hj : j < arr.val.length),
        -500 ≤ (arr.val[j]'hj).val ∧ (arr.val[j]'hj).val ≤ 500 ∧
          ∃ (i : Nat) (hi : i < arr.val.length),
            i ≠ j ∧ (arr.val[i]'hi).val = 2 * (arr.val[j]'hj).val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_lo : 2 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 500)
    (hbounds : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ (arr.val[k]'hk).val ∧ (arr.val[k]'hk).val ≤ 1000), check_if_exist arr = ok true →
      ∃ (j : Nat) (hj : j < arr.val.length),
        -500 ≤ (arr.val[j]'hj).val ∧ (arr.val[j]'hj).val ≤ 500 ∧
          ∃ (i : Nat) (hi : i < arr.val.length),
            i ≠ j ∧ (arr.val[i]'hi).val = 2 * (arr.val[j]'hj).val) := by
  sorry

/-- For every bijection p from {0, ..., len(arr)-1} to itself, let arr_p be the slice of length len(arr) defined by arr_p[k] = arr[p(k)] for every k with 0 <= k < len(arr). Then check_if_exist arr_p returns the same Bool result as check_if_exist arr.
  Preconditions: len(arr) >= 2 and len(arr) <= 500 and for every k with 0 <= k < len(arr), -1000 <= arr[k] <= 1000. -/
theorem spec_5 (arr arrp : Slice Std.I64)
    (hlen_lo : 2 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 500)
    (hbounds : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ (arr.val[k]'hk).val ∧ (arr.val[k]'hk).val ≤ 1000)
    (p : Nat → Nat) (hp : IsPermIndex arr.val.length p)
    (harrp : contents arrp = permutedContents arr p hp.1) :
    ∀ (r : Bool), check_if_exist arr = ok r ↔ check_if_exist arrp = ok r := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr arrp : Slice Std.I64)
    (hlen_lo : 2 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 500)
    (hbounds : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ (arr.val[k]'hk).val ∧ (arr.val[k]'hk).val ≤ 1000)
    (p : Nat → Nat) (hp : IsPermIndex arr.val.length p)
    (harrp : contents arrp = permutedContents arr p hp.1), ∀ (r : Bool), check_if_exist arr = ok r ↔ check_if_exist arrp = ok r) := by
  sorry

/-- Let neg be the slice of length len(arr) defined by neg[k] = -arr[k] for every k with 0 <= k < len(arr). Then check_if_exist neg returns the same Bool result as check_if_exist arr.
  Preconditions: len(arr) >= 2 and len(arr) <= 500 and for every k with 0 <= k < len(arr), -1000 <= arr[k] <= 1000. -/
theorem spec_6 (arr neg : Slice Std.I64)
    (hlen_lo : 2 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 500)
    (hbounds : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ (arr.val[k]'hk).val ∧ (arr.val[k]'hk).val ≤ 1000)
    (hneg : contents neg = (contents arr).map (fun z => -z)) :
    ∀ (r : Bool), check_if_exist neg = ok r ↔ check_if_exist arr = ok r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr neg : Slice Std.I64)
    (hlen_lo : 2 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 500)
    (hbounds : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ (arr.val[k]'hk).val ∧ (arr.val[k]'hk).val ≤ 1000)
    (hneg : contents neg = (contents arr).map (fun z => -z)), ∀ (r : Bool), check_if_exist neg = ok r ↔ check_if_exist arr = ok r) := by
  sorry

/-- For every integer c with c >= 1 such that -1000 <= c * arr[k] <= 1000 for every k with 0 <= k < len(arr), let scaled_c be the slice defined by scaled_c[k] = c * arr[k]. Then check_if_exist scaled_c returns the same Bool result as check_if_exist arr.
  Preconditions: len(arr) >= 2 and len(arr) <= 500 and for every k with 0 <= k < len(arr), -1000 <= arr[k] <= 1000. -/
theorem spec_7 (arr scaled : Slice Std.I64) (c : ℤ)
    (hlen_lo : 2 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 500)
    (hbounds : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ (arr.val[k]'hk).val ∧ (arr.val[k]'hk).val ≤ 1000)
    (hc : 1 ≤ c)
    (hfactor : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ c * (arr.val[k]'hk).val ∧ c * (arr.val[k]'hk).val ≤ 1000)
    (hscaled : contents scaled = (contents arr).map (fun z => c * z)) :
    ∀ (r : Bool), check_if_exist scaled = ok r ↔ check_if_exist arr = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr scaled : Slice Std.I64) (c : ℤ)
    (hlen_lo : 2 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 500)
    (hbounds : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ (arr.val[k]'hk).val ∧ (arr.val[k]'hk).val ≤ 1000)
    (hc : 1 ≤ c)
    (hfactor : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ c * (arr.val[k]'hk).val ∧ c * (arr.val[k]'hk).val ≤ 1000)
    (hscaled : contents scaled = (contents arr).map (fun z => c * z)), ∀ (r : Bool), check_if_exist scaled = ok r ↔ check_if_exist arr = ok r) := by
  sorry

/-- For every integer x with -1000 <= x <= 1000, let arr' be the slice of length len(arr)+1 obtained by appending x to arr. If check_if_exist arr returns true, then check_if_exist arr' returns true.
  Preconditions: len(arr) >= 2, len(arr) < 500, and for every k with 0 <= k < len(arr), -1000 <= arr[k] <= 1000. -/
theorem spec_8 (arr arr' : Slice Std.I64) (x : Std.I64)
    (hlen_lo : 2 ≤ arr.val.length) (hlen_hi : arr.val.length < 500)
    (hbounds : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ (arr.val[k]'hk).val ∧ (arr.val[k]'hk).val ≤ 1000)
    (hx : -1000 ≤ x.val ∧ x.val ≤ 1000)
    (harr' : arr'.val = arr.val ++ [x]) :
    check_if_exist arr = ok true → check_if_exist arr' = ok true := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr arr' : Slice Std.I64) (x : Std.I64)
    (hlen_lo : 2 ≤ arr.val.length) (hlen_hi : arr.val.length < 500)
    (hbounds : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ (arr.val[k]'hk).val ∧ (arr.val[k]'hk).val ≤ 1000)
    (hx : -1000 ≤ x.val ∧ x.val ≤ 1000)
    (harr' : arr'.val = arr.val ++ [x]), check_if_exist arr = ok true → check_if_exist arr' = ok true) := by
  sorry

/-- For every index k with 0 <= k < len(arr), let arr_k be the slice of length len(arr)-1 obtained by deleting the element at position k. If check_if_exist arr returns false, then check_if_exist arr_k returns false.
  Preconditions: len(arr) >= 3 and len(arr) <= 500 and for every k with 0 <= k < len(arr), -1000 <= arr[k] <= 1000. -/
theorem spec_9 (arr arrk : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 500)
    (hbounds : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ (arr.val[k]'hk).val ∧ (arr.val[k]'hk).val ≤ 1000)
    (k : Nat) (hk : k < arr.val.length)
    (harrk : arrk.val = arr.val.take k ++ arr.val.drop (k + 1)) :
    check_if_exist arr = ok false → check_if_exist arrk = ok false := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr arrk : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 500)
    (hbounds : ∀ (k : Nat) (hk : k < arr.val.length),
      -1000 ≤ (arr.val[k]'hk).val ∧ (arr.val[k]'hk).val ≤ 1000)
    (k : Nat) (hk : k < arr.val.length)
    (harrk : arrk.val = arr.val.take k ++ arr.val.drop (k + 1)), check_if_exist arr = ok false → check_if_exist arrk = ok false) := by
  sorry

end AegisSpec.CheckIfExist
