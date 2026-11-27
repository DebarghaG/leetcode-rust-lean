import Aegis.ReplaceElements.Code.Funs

/-!
# Specifications of `Aegis.ReplaceElements.replace_elements`

LeetCode problem `replace-elements-with-greatest-element-on-right-side`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace AegisSpec.ReplaceElements

def intsOf (arr : Slice Std.I64) : List Int := arr.val.map fun x => x.val

def intsOfVec (r : alloc.vec.Vec Std.I64) : List Int := r.val.map fun x => x.val

def aget (arr : Slice Std.I64) (i : Nat) : Int := (intsOf arr).getD i 0

def vget (r : alloc.vec.Vec Std.I64) (i : Nat) : Int := (intsOfVec r).getD i 0

def IsMaxAtRight (arr : Slice Std.I64) (i : Nat) (m : Int) : Prop :=
  (∀ j, i < j → j < arr.val.length → m ≥ aget arr j) ∧
    ∃ j, i < j ∧ j < arr.val.length ∧ m = aget arr j

@[simp] theorem intsOf_length (arr : Slice Std.I64) :
    (intsOf arr).length = arr.val.length := by
  simp [intsOf]

@[simp] theorem intsOfVec_length (r : alloc.vec.Vec Std.I64) :
    (intsOfVec r).length = r.val.length := by
  simp [intsOfVec]

theorem aget_eq (arr : Slice Std.I64) {i : Nat} (h : i < arr.val.length) :
    aget arr i = (arr.val[i]).val := by
  simp [aget, intsOf, h]

theorem vget_eq (r : alloc.vec.Vec Std.I64) {i : Nat} (h : i < r.val.length) :
    vget r i = (r.val[i]).val := by
  simp [vget, intsOfVec, h]

/-- The function returns a result r such that len(r) = len(arr), and for every i with 0 <= i < len(arr): if i = len(arr)-1 then r[i] = -1; otherwise r[i] is the greatest (maximum) value among the elements of arr at indices j with i < j < len(arr). Equivalently, for i < len(arr)-1, r[i] >= arr[j] for every j with i < j < len(arr), and there exists k with i < k < len(arr) such that r[i] = arr[k].
  Preconditions: len(arr) >= 1, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
theorem spec_1 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.ReplaceElements.replace_elements arr = ok r ∧
        r.val.length = arr.val.length ∧
        (∀ i, i < arr.val.length →
          (i = arr.val.length - 1 → vget r i = -1) ∧
            (i < arr.val.length - 1 → IsMaxAtRight arr i (vget r i))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.ReplaceElements.replace_elements arr = ok r ∧
        r.val.length = arr.val.length ∧
        (∀ i, i < arr.val.length →
          (i = arr.val.length - 1 → vget r i = -1) ∧
            (i < arr.val.length - 1 → IsMaxAtRight arr i (vget r i)))) := by
  sorry

/-- The function returns a result r; it does not fail, panic, index out of bounds, or overflow any 64-bit integer arithmetic on any input satisfying the preconditions.
  Preconditions: len(arr) >= 1, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
theorem spec_2 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000) :
    ∃ r : alloc.vec.Vec Std.I64, Aegis.ReplaceElements.replace_elements arr = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000), ∃ r : alloc.vec.Vec Std.I64, Aegis.ReplaceElements.replace_elements arr = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(arr).
  Preconditions: len(arr) >= 1, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
theorem spec_3 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r) :
    r.val.length = arr.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r), r.val.length = arr.val.length) := by
  sorry

/-- Whenever the function returns a result r, r[len(arr)-1] = -1.
  Preconditions: len(arr) >= 1, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
theorem spec_4 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r) :
    vget r (arr.val.length - 1) = -1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r), vget r (arr.val.length - 1) = -1) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(arr)-1 and every j with i < j < len(arr), r[i] >= arr[j].
  Preconditions: len(arr) >= 1, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
theorem spec_5 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r) :
    ∀ i, i < arr.val.length - 1 → ∀ j, i < j → j < arr.val.length → vget r i ≥ aget arr j := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r), ∀ i, i < arr.val.length - 1 → ∀ j, i < j → j < arr.val.length → vget r i ≥ aget arr j) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(arr)-1 there exists j with i < j < len(arr) such that r[i] = arr[j].
  Preconditions: len(arr) >= 1, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
theorem spec_6 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r) :
    ∀ i, i < arr.val.length - 1 →
      ∃ j, i < j ∧ j < arr.val.length ∧ vget r i = aget arr j := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r), ∀ i, i < arr.val.length - 1 →
      ∃ j, i < j ∧ j < arr.val.length ∧ vget r i = aget arr j) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(arr)-1, r[i] = max(arr[i+1], r[i+1]), where max(x,y) denotes the larger of x and y.
  Preconditions: len(arr) >= 1, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
theorem spec_7 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r) :
    ∀ i, i < arr.val.length - 1 → vget r i = max (aget arr (i + 1)) (vget r (i + 1)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r), ∀ i, i < arr.val.length - 1 → vget r i = max (aget arr (i + 1)) (vget r (i + 1))) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(arr)-1, r[i] >= r[i+1].
  Preconditions: len(arr) >= 1, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
theorem spec_8 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r) :
    ∀ i, i < arr.val.length - 1 → vget r i ≥ vget r (i + 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r), ∀ i, i < arr.val.length - 1 → vget r i ≥ vget r (i + 1)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(arr)-1, 1 <= r[i] <= 100000.
  Preconditions: len(arr) >= 1, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
theorem spec_9 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r) :
    ∀ i, i < arr.val.length - 1 → 1 ≤ vget r i ∧ vget r i ≤ 100000 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r), ∀ i, i < arr.val.length - 1 → 1 ≤ vget r i ∧ vget r i ≤ 100000) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(arr)-1, r[i] = arr[i+1], and r[len(arr)-1] = -1.
  Preconditions: len(arr) >= 1, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and arr is non-increasing: for every i with 0 <= i < len(arr)-1, arr[i] >= arr[i+1]. -/
theorem spec_10 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (hmono : ∀ i, i < arr.val.length - 1 → aget arr i ≥ aget arr (i + 1))
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r) :
    (∀ i, i < arr.val.length - 1 → vget r i = aget arr (i + 1)) ∧
      vget r (arr.val.length - 1) = -1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (hmono : ∀ i, i < arr.val.length - 1 → aget arr i ≥ aget arr (i + 1))
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r), (∀ i, i < arr.val.length - 1 → vget r i = aget arr (i + 1)) ∧
      vget r (arr.val.length - 1) = -1) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(arr)-1, r[i] = arr[len(arr)-1], and r[len(arr)-1] = -1.
  Preconditions: len(arr) >= 1, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and arr is non-decreasing: for every i with 0 <= i < len(arr)-1, arr[i] <= arr[i+1]. -/
theorem spec_11 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (hmono : ∀ i, i < arr.val.length - 1 → aget arr i ≤ aget arr (i + 1))
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r) :
    (∀ i, i < arr.val.length - 1 → vget r i = aget arr (arr.val.length - 1)) ∧
      vget r (arr.val.length - 1) = -1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (hmono : ∀ i, i < arr.val.length - 1 → aget arr i ≤ aget arr (i + 1))
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r), (∀ i, i < arr.val.length - 1 → vget r i = aget arr (arr.val.length - 1)) ∧
      vget r (arr.val.length - 1) = -1) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), -1 <= r[i] <= 100000.
  Preconditions: len(arr) >= 1, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
theorem spec_12 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r) :
    ∀ i, i < r.val.length → -1 ≤ vget r i ∧ vget r i ≤ 100000 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hbounds : ∀ i, i < arr.val.length → 1 ≤ aget arr i ∧ aget arr i ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hret : Aegis.ReplaceElements.replace_elements arr = ok r), ∀ i, i < r.val.length → -1 ≤ vget r i ∧ vget r i ≤ 100000) := by
  sorry

end AegisSpec.ReplaceElements
