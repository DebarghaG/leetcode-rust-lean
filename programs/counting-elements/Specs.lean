import Aegis.CountElements.Code.Funs

/-!
# Specifications of `Aegis.CountElements.count_elements`

LeetCode problem `counting-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountElements

open Aegis.CountElements

def entriesInRange (arr : Slice Std.I64) (lo hi : Int) : Prop :=
  ∀ (i : Nat) (h : i < arr.val.length), lo ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ hi

def occ (arr : Slice Std.I64) (v : Int) : Nat :=
  (arr.val.filter (fun x => decide (x.val = v))).length

def present (arr : Slice Std.I64) (v : Int) : Bool :=
  arr.val.any (fun x => decide (x.val = v))

def countWithSuccessor (arr : Slice Std.I64) : Nat :=
  (arr.val.filter (fun x => present arr (x.val + 1))).length

def countAtMost (arr : Slice Std.I64) (c : Int) : Nat :=
  (arr.val.filter (fun x => decide (x.val ≤ c))).length

def sumWithSuccessor (arr : Slice Std.I64) : Nat :=
  ((List.range 1000).map
    (fun v => if present arr ((v : Int) + 1) then occ arr (v : Int) else 0)).sum

def IsAppend (arr arr' : Slice Std.I64) (x : Int) : Prop :=
  arr'.val.map (fun y => y.val) = arr.val.map (fun y => y.val) ++ [x]

/-- Whenever count_elements(arr) returns a result r, r equals the number of indices i with 0 ≤ i < len(arr) for which there exists an index j with 0 ≤ j < len(arr) and arr[j] = arr[i] + 1.
  Preconditions: 1 ≤ len(arr) ≤ 1000 and for every i with 0 ≤ i < len(arr), 0 ≤ arr[i] ≤ 1000. -/
theorem spec_1 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 1000)
    (hrange : entriesInRange arr 0 1000) :
    ∀ r : Std.I64, count_elements arr = ok r → r.val = (countWithSuccessor arr : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 1000)
    (hrange : entriesInRange arr 0 1000), ∀ r : Std.I64, count_elements arr = ok r → r.val = (countWithSuccessor arr : Int)) := by
  sorry

/-- The function returns a result (it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: 1 ≤ len(arr) ≤ 1000 and for every i with 0 ≤ i < len(arr), 0 ≤ arr[i] ≤ 1000. -/
theorem spec_2 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 1000)
    (hrange : entriesInRange arr 0 1000) :
    ∃ r : Std.I64, count_elements arr = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 1000)
    (hrange : entriesInRange arr 0 1000), ∃ r : Std.I64, count_elements arr = ok r) := by
  sorry

/-- Whenever count_elements(arr) returns a result r, 0 ≤ r ≤ len(arr).
  Preconditions: 1 ≤ len(arr) ≤ 1000 and for every i with 0 ≤ i < len(arr), 0 ≤ arr[i] ≤ 1000. -/
theorem spec_3 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 1000)
    (hrange : entriesInRange arr 0 1000) :
    ∀ r : Std.I64, count_elements arr = ok r → 0 ≤ r.val ∧ r.val ≤ (arr.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 1000)
    (hrange : entriesInRange arr 0 1000), ∀ r : Std.I64, count_elements arr = ok r → 0 ≤ r.val ∧ r.val ≤ (arr.val.length : Int)) := by
  sorry

/-- Whenever count_elements(arr) returns a result r, r = 0 if and only if for every index i with 0 ≤ i < len(arr) and every index j with 0 ≤ j < len(arr), arr[j] ≠ arr[i] + 1.
  Preconditions: 1 ≤ len(arr) ≤ 1000 and for every i with 0 ≤ i < len(arr), 0 ≤ arr[i] ≤ 1000. -/
theorem spec_4 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 1000)
    (hrange : entriesInRange arr 0 1000) :
    ∀ r : Std.I64, count_elements arr = ok r →
      (r.val = 0 ↔ ∀ (i : Nat) (hi : i < arr.val.length)
        (j : Nat) (hj : j < arr.val.length), (arr.val[j]).val ≠ (arr.val[i]).val + 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 1000)
    (hrange : entriesInRange arr 0 1000), ∀ r : Std.I64, count_elements arr = ok r →
      (r.val = 0 ↔ ∀ (i : Nat) (hi : i < arr.val.length)
        (j : Nat) (hj : j < arr.val.length), (arr.val[j]).val ≠ (arr.val[i]).val + 1)) := by
  sorry

/-- Whenever count_elements(arr) returns a result r, r = 0.
  Preconditions: 1 ≤ len(arr) ≤ 1000, len(arr) = 1, and for every i with 0 ≤ i < len(arr), 0 ≤ arr[i] ≤ 1000. -/
theorem spec_5 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen_one : arr.val.length = 1)
    (hlen_le : arr.val.length ≤ 1000)
    (hrange : entriesInRange arr 0 1000) :
    ∀ r : Std.I64, count_elements arr = ok r → r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen_one : arr.val.length = 1)
    (hlen_le : arr.val.length ≤ 1000)
    (hrange : entriesInRange arr 0 1000), ∀ r : Std.I64, count_elements arr = ok r → r.val = 0) := by
  sorry

/-- Whenever count_elements(arr) returns a result r, r = sum over v = 0 to 999 of occ(arr, v) if v + 1 is present in arr, and 0 otherwise, where occ(arr, v) is the number of indices k with 0 ≤ k < len(arr) and arr[k] = v, and v + 1 is present in arr when there exists j with 0 ≤ j < len(arr) and arr[j] = v + 1.
  Preconditions: 1 ≤ len(arr) ≤ 1000 and for every i with 0 ≤ i < len(arr), 0 ≤ arr[i] ≤ 1000. -/
theorem spec_6 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 1000)
    (hrange : entriesInRange arr 0 1000) :
    ∀ r : Std.I64, count_elements arr = ok r → r.val = (sumWithSuccessor arr : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 1000)
    (hrange : entriesInRange arr 0 1000), ∀ r : Std.I64, count_elements arr = ok r → r.val = (sumWithSuccessor arr : Int)) := by
  sorry

/-- Whenever count_elements(arr) returns a result r and count_elements(arr') returns a result r', we have r = r'.
  Preconditions: arr and arr' both satisfy the problem constraints (1 ≤ len(arr), len(arr') ≤ 1000 and all entries in [0, 1000]), and arr' is a permutation of arr, meaning that for every integer v, occ(arr, v) = occ(arr', v), where occ(arr, v) denotes the number of indices i with 0 ≤ i < len(arr) and arr[i] = v. -/
theorem spec_7 (arr arr' : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 1000)
    (hrange : entriesInRange arr 0 1000)
    (hlen' : 1 ≤ arr'.val.length) (hlen_le' : arr'.val.length ≤ 1000)
    (hrange' : entriesInRange arr' 0 1000)
    (hperm : ∀ v : Int, occ arr v = occ arr' v) :
    ∀ r r' : Std.I64, count_elements arr = ok r → count_elements arr' = ok r' →
      r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr arr' : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 1000)
    (hrange : entriesInRange arr 0 1000)
    (hlen' : 1 ≤ arr'.val.length) (hlen_le' : arr'.val.length ≤ 1000)
    (hrange' : entriesInRange arr' 0 1000)
    (hperm : ∀ v : Int, occ arr v = occ arr' v), ∀ r r' : Std.I64, count_elements arr = ok r → count_elements arr' = ok r' →
      r = r') := by
  sorry

/-- Whenever count_elements(arr) returns a result r and count_elements(arr') returns a result r', we have r ≤ r'.
  Preconditions: arr and arr' both satisfy the problem constraints, and for every integer v, occ(arr, v) ≤ occ(arr', v), where occ(arr, v) denotes the number of indices i with 0 ≤ i < len(arr) and arr[i] = v. -/
theorem spec_8 (arr arr' : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 1000)
    (hrange : entriesInRange arr 0 1000)
    (hlen' : 1 ≤ arr'.val.length) (hlen_le' : arr'.val.length ≤ 1000)
    (hrange' : entriesInRange arr' 0 1000)
    (hmono : ∀ v : Int, occ arr v ≤ occ arr' v) :
    ∀ r r' : Std.I64, count_elements arr = ok r → count_elements arr' = ok r' →
      r.val ≤ r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr arr' : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 1000)
    (hrange : entriesInRange arr 0 1000)
    (hlen' : 1 ≤ arr'.val.length) (hlen_le' : arr'.val.length ≤ 1000)
    (hrange' : entriesInRange arr' 0 1000)
    (hmono : ∀ v : Int, occ arr v ≤ occ arr' v), ∀ r r' : Std.I64, count_elements arr = ok r → count_elements arr' = ok r' →
      r.val ≤ r'.val) := by
  sorry

/-- Whenever count_elements(arr) returns a result r and count_elements(arr') returns a result r', we have r' = r + a + b, where present(arr, y) means there exists j with 0 ≤ j < len(arr) and arr[j] = y, occ(arr, y) means the number of indices k with 0 ≤ k < len(arr) and arr[k] = y, a = 1 if present(arr, x + 1) and a = 0 otherwise, and b = occ(arr, x - 1) if x is not present in arr and b = 0 otherwise.
  Preconditions: arr satisfies the problem constraints with 1 ≤ len(arr) ≤ 999, x is an integer with 0 ≤ x ≤ 1000, and arr' is the slice of length len(arr) + 1 obtained by appending x to arr, i.e. arr'[i] = arr[i] for 0 ≤ i < len(arr) and arr'[len(arr)] = x. -/
theorem spec_9 (arr arr' : Slice Std.I64) (x : Int)
    (hlen : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 999)
    (hrange : entriesInRange arr 0 1000)
    (hx_lo : 0 ≤ x) (hx_hi : x ≤ 1000)
    (happend : IsAppend arr arr' x) :
    ∀ r r' : Std.I64, count_elements arr = ok r → count_elements arr' = ok r' →
      r'.val = r.val + (if present arr (x + 1) then (1 : Int) else 0)
        + (if present arr x then 0 else (occ arr (x - 1) : Int)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr arr' : Slice Std.I64) (x : Int)
    (hlen : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 999)
    (hrange : entriesInRange arr 0 1000)
    (hx_lo : 0 ≤ x) (hx_hi : x ≤ 1000)
    (happend : IsAppend arr arr' x), ∀ r r' : Std.I64, count_elements arr = ok r → count_elements arr' = ok r' →
      r'.val = r.val + (if present arr (x + 1) then (1 : Int) else 0)
        + (if present arr x then 0 else (occ arr (x - 1) : Int))) := by
  sorry

/-- Whenever count_elements(arr) returns a result r, r ≤ the number of indices i with 0 ≤ i < len(arr) and arr[i] ≤ 999.
  Preconditions: 1 ≤ len(arr) ≤ 1000 and for every i with 0 ≤ i < len(arr), 0 ≤ arr[i] ≤ 1000. -/
theorem spec_10 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 1000)
    (hrange : entriesInRange arr 0 1000) :
    ∀ r : Std.I64, count_elements arr = ok r → r.val ≤ (countAtMost arr 999 : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 1000)
    (hrange : entriesInRange arr 0 1000), ∀ r : Std.I64, count_elements arr = ok r → r.val ≤ (countAtMost arr 999 : Int)) := by
  sorry

end AegisSpec.CountElements
