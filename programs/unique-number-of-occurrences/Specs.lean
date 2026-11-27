import Aegis.UniqueOccurrences.Code.Funs

/-!
# Specifications of `Aegis.UniqueOccurrences.unique_occurrences`

LeetCode problem `unique-number-of-occurrences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.UniqueOccurrences

namespace AegisSpec.UniqueOccurrences

def Occ (arr : Slice Std.I64) (v : ℤ) : ℕ :=
  arr.val.countP (fun x => decide (x.val = v))

def elem (arr : Slice Std.I64) (i : ℕ) (h : i < arr.val.length) : ℤ :=
  (arr.val.get ⟨i, h⟩).val

/-- Let Occ(v) be the number of indices i with 0 <= i < len(arr) and arr[i] = v. Whenever unique_occurrences(arr) returns a result r, r is true if and only if for every pair of integers x and y, if Occ(x) > 0, Occ(y) > 0, and x != y, then Occ(x) != Occ(y). Equivalently, among the distinct values that occur in arr, no two values have the same number of occurrences.
  Preconditions: arr is a slice of 64-bit integers satisfying 1 <= len(arr) <= 1000, and for every index i with 0 <= i < len(arr), -1000 <= arr[i] <= 1000. -/
theorem spec_1 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length ≤ 1000)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (r : Bool) (hr : unique_occurrences arr = Result.ok r) :
    (r = true ↔
      ∀ x y : ℤ, Occ arr x > 0 → Occ arr y > 0 → x ≠ y → Occ arr x ≠ Occ arr y) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length ≤ 1000)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (r : Bool) (hr : unique_occurrences arr = Result.ok r), (r = true ↔
      ∀ x y : ℤ, Occ arr x > 0 → Occ arr y > 0 → x ≠ y → Occ arr x ≠ Occ arr y)) := by
  sorry

/-- The function unique_occurrences(arr) returns a result r of type Bool; it does not fail, panic, index out of bounds, or overflow on any input satisfying the preconditions.
  Preconditions: arr is a slice of 64-bit integers satisfying 1 <= len(arr) <= 1000, and for every index i with 0 <= i < len(arr), -1000 <= arr[i] <= 1000. -/
theorem spec_2 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length ≤ 1000)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000) :
    ∃ r : Bool, unique_occurrences arr = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length ≤ 1000)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000), ∃ r : Bool, unique_occurrences arr = Result.ok r) := by
  sorry

/-- Whenever unique_occurrences(arr) returns a result r, r is true.
  Preconditions: arr satisfies 1 <= len(arr) <= 1000, all entries are in [-1000,1000], and there exists an integer v such that arr[i] = v for every i with 0 <= i < len(arr). -/
theorem spec_3 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length ≤ 1000)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (hv : ∃ v : ℤ, ∀ x ∈ arr.val, x.val = v)
    (r : Bool) (hr : unique_occurrences arr = Result.ok r) :
    r = true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length ≤ 1000)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (hv : ∃ v : ℤ, ∀ x ∈ arr.val, x.val = v)
    (r : Bool) (hr : unique_occurrences arr = Result.ok r), r = true) := by
  sorry

/-- Whenever unique_occurrences(arr) returns a result r, r is false.
  Preconditions: arr satisfies 1 <= len(arr) <= 1000, all entries are in [-1000,1000], len(arr) >= 2, and for every i and j with 0 <= i < j < len(arr), arr[i] != arr[j]. -/
theorem spec_4 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length ≤ 1000)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (hlen2 : 2 ≤ arr.val.length)
    (hdiff : ∀ (i j : ℕ) (hij : i < j) (hj : j < arr.val.length),
      arr.val.get ⟨i, by omega⟩ ≠ arr.val.get ⟨j, by omega⟩)
    (r : Bool) (hr : unique_occurrences arr = Result.ok r) :
    r = false := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length ≤ 1000)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (hlen2 : 2 ≤ arr.val.length)
    (hdiff : ∀ (i j : ℕ) (hij : i < j) (hj : j < arr.val.length),
      arr.val.get ⟨i, by omega⟩ ≠ arr.val.get ⟨j, by omega⟩)
    (r : Bool) (hr : unique_occurrences arr = Result.ok r), r = false) := by
  sorry

/-- Whenever unique_occurrences(arr) returns a result r, r is true exactly when arr[0] = arr[1], and r is false exactly when arr[0] != arr[1].
  Preconditions: arr satisfies 1 <= len(arr) <= 1000, all entries are in [-1000,1000], and len(arr) = 2. -/
theorem spec_5 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length ≤ 1000)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (hlen2 : arr.val.length = 2)
    (r : Bool) (hr : unique_occurrences arr = Result.ok r) :
    (r = true ↔ elem arr 0 (by omega) = elem arr 1 (by omega)) ∧
      (r = false ↔ elem arr 0 (by omega) ≠ elem arr 1 (by omega)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length ≤ 1000)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (hlen2 : arr.val.length = 2)
    (r : Bool) (hr : unique_occurrences arr = Result.ok r), (r = true ↔ elem arr 0 (by omega) = elem arr 1 (by omega)) ∧
      (r = false ↔ elem arr 0 (by omega) ≠ elem arr 1 (by omega))) := by
  sorry

/-- For the two distinct values x and y appearing in arr, whenever unique_occurrences(arr) returns a result r, r is true if and only if Occ(x) != Occ(y).
  Preconditions: arr satisfies 1 <= len(arr) <= 1000, all entries are in [-1000,1000], and there exist distinct integers x and y such that both x and y occur in arr and every element of arr is equal to x or to y. Let Occ(v) be the number of indices i with 0 <= i < len(arr) and arr[i] = v. -/
theorem spec_6 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length ≤ 1000)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (x y : ℤ) (hxy : x ≠ y)
    (hx : Occ arr x > 0) (hy : Occ arr y > 0)
    (honly : ∀ z ∈ arr.val, z.val = x ∨ z.val = y)
    (r : Bool) (hr : unique_occurrences arr = Result.ok r) :
    (r = true ↔ Occ arr x ≠ Occ arr y) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length ≤ 1000)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (x y : ℤ) (hxy : x ≠ y)
    (hx : Occ arr x > 0) (hy : Occ arr y > 0)
    (honly : ∀ z ∈ arr.val, z.val = x ∨ z.val = y)
    (r : Bool) (hr : unique_occurrences arr = Result.ok r), (r = true ↔ Occ arr x ≠ Occ arr y)) := by
  sorry

/-- Whenever unique_occurrences(arr1) returns a result r1 and unique_occurrences(arr2) returns a result r2, r1 = r2.
  Preconditions: arr1 and arr2 are slices of 64-bit integers, each satisfying 1 <= len <= 1000 with all entries in [-1000,1000], and for every integer v, the number of indices i with arr1[i] = v equals the number of indices j with arr2[j] = v. -/
theorem spec_7 (arr1 arr2 : Slice Std.I64)
    (hlen1 : 1 ≤ arr1.val.length ∧ arr1.val.length ≤ 1000)
    (hb1 : ∀ x ∈ arr1.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (hlen2 : 1 ≤ arr2.val.length ∧ arr2.val.length ≤ 1000)
    (hb2 : ∀ x ∈ arr2.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (hocc : ∀ v : ℤ, Occ arr1 v = Occ arr2 v)
    (r1 r2 : Bool)
    (hr1 : unique_occurrences arr1 = Result.ok r1)
    (hr2 : unique_occurrences arr2 = Result.ok r2) :
    r1 = r2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (hlen1 : 1 ≤ arr1.val.length ∧ arr1.val.length ≤ 1000)
    (hb1 : ∀ x ∈ arr1.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (hlen2 : 1 ≤ arr2.val.length ∧ arr2.val.length ≤ 1000)
    (hb2 : ∀ x ∈ arr2.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (hocc : ∀ v : ℤ, Occ arr1 v = Occ arr2 v)
    (r1 r2 : Bool)
    (hr1 : unique_occurrences arr1 = Result.ok r1)
    (hr2 : unique_occurrences arr2 = Result.ok r2), r1 = r2) := by
  sorry

/-- Whenever unique_occurrences(arr) returns a result r and unique_occurrences(arr2) returns a result r2, r = r2.
  Preconditions: arr satisfies 1 <= len(arr) <= 500 with all entries in [-1000,1000], and arr2 is the concatenation of arr with itself, so len(arr2) = 2*len(arr) and arr2 satisfies the problem constraints. -/
theorem spec_8 (arr arr2 : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length ≤ 500)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (harr2 : arr2.val = arr.val ++ arr.val)
    (r r2 : Bool)
    (hr : unique_occurrences arr = Result.ok r)
    (hr2 : unique_occurrences arr2 = Result.ok r2) :
    r = r2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr arr2 : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length ≤ 500)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (harr2 : arr2.val = arr.val ++ arr.val)
    (r r2 : Bool)
    (hr : unique_occurrences arr = Result.ok r)
    (hr2 : unique_occurrences arr2 = Result.ok r2), r = r2) := by
  sorry

/-- Whenever unique_occurrences(arr) returns a result r and r is false, there exist two distinct integers x and y such that Occ(x) > 0, Occ(y) > 0, and Occ(x) = Occ(y).
  Preconditions: arr satisfies 1 <= len(arr) <= 1000 with all entries in [-1000,1000]. Let Occ(v) be the number of indices i with 0 <= i < len(arr) and arr[i] = v. -/
theorem spec_9 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length ≤ 1000)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (r : Bool) (hr : unique_occurrences arr = Result.ok r) (hfalse : r = false) :
    ∃ x y : ℤ, x ≠ y ∧ Occ arr x > 0 ∧ Occ arr y > 0 ∧ Occ arr x = Occ arr y := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length ≤ 1000)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (r : Bool) (hr : unique_occurrences arr = Result.ok r) (hfalse : r = false), ∃ x y : ℤ, x ≠ y ∧ Occ arr x > 0 ∧ Occ arr y > 0 ∧ Occ arr x = Occ arr y) := by
  sorry

/-- Whenever unique_occurrences(arr) returns a result r and unique_occurrences(arr') returns a result r', if r is false then r' is false.
  Preconditions: arr satisfies 1 <= len(arr) < 1000 with all entries in [-1000,1000]. Let Occ(v) be the number of indices i with 0 <= i < len(arr) and arr[i] = v. Let z be an integer with -1000 <= z <= 1000 and Occ(z) = 0, and let arr' be the concatenation of arr and the one-element slice [z]. -/
theorem spec_10 (arr arr' : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length < 1000)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (z : Std.I64) (hz : -1000 ≤ z.val ∧ z.val ≤ 1000)
    (hzocc : Occ arr z.val = 0)
    (harr' : arr'.val = arr.val ++ [z])
    (r r' : Bool)
    (hr : unique_occurrences arr = Result.ok r)
    (hr' : unique_occurrences arr' = Result.ok r')
    (hfalse : r = false) :
    r' = false := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr arr' : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length < 1000)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (z : Std.I64) (hz : -1000 ≤ z.val ∧ z.val ≤ 1000)
    (hzocc : Occ arr z.val = 0)
    (harr' : arr'.val = arr.val ++ [z])
    (r r' : Bool)
    (hr : unique_occurrences arr = Result.ok r)
    (hr' : unique_occurrences arr' = Result.ok r')
    (hfalse : r = false), r' = false) := by
  sorry

/-- Whenever unique_occurrences(arr) returns a result r and unique_occurrences(arr') returns a result r', if r is true then r' is true if and only if there is no integer v with Occ(v) = 1.
  Preconditions: arr satisfies 1 <= len(arr) < 1000 with all entries in [-1000,1000]. Let Occ(v) be the number of indices i with 0 <= i < len(arr) and arr[i] = v. Let z be an integer with -1000 <= z <= 1000 and Occ(z) = 0, and let arr' be the concatenation of arr and the one-element slice [z]. -/
theorem spec_11 (arr arr' : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length < 1000)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (z : Std.I64) (hz : -1000 ≤ z.val ∧ z.val ≤ 1000)
    (hzocc : Occ arr z.val = 0)
    (harr' : arr'.val = arr.val ++ [z])
    (r r' : Bool)
    (hr : unique_occurrences arr = Result.ok r)
    (hr' : unique_occurrences arr' = Result.ok r')
    (htrue : r = true) :
    (r' = true ↔ ¬ ∃ v : ℤ, Occ arr v = 1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr arr' : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length ∧ arr.val.length < 1000)
    (hb : ∀ x ∈ arr.val, -1000 ≤ x.val ∧ x.val ≤ 1000)
    (z : Std.I64) (hz : -1000 ≤ z.val ∧ z.val ≤ 1000)
    (hzocc : Occ arr z.val = 0)
    (harr' : arr'.val = arr.val ++ [z])
    (r r' : Bool)
    (hr : unique_occurrences arr = Result.ok r)
    (hr' : unique_occurrences arr' = Result.ok r')
    (htrue : r = true), (r' = true ↔ ¬ ∃ v : ℤ, Occ arr v = 1)) := by
  sorry

end AegisSpec.UniqueOccurrences
