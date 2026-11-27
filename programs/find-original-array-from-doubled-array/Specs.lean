import Aegis.FindOriginalArray.Code.Funs

/-!
# Specifications of `Aegis.FindOriginalArray.find_original_array`

LeetCode problem `find-original-array-from-doubled-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.FindOriginalArray

namespace AegisSpec.FindOriginalArray

def vals (l : List Std.I64) : List Int := l.map (fun x => x.val)

def cnt (xs : List Int) (v : Int) : Nat := xs.countP (fun x => decide (x = v))

def dbl (xs : List Int) : List Int := xs.map (fun x => 2 * x)

def IsOriginal (changed O : List Int) : Prop :=
  changed.length = 2 * O.length ∧ ∀ v : Int, cnt changed v = cnt O v + cnt (dbl O) v

def IsDoubled (changed : List Int) : Prop := ∃ O : List Int, IsOriginal changed O

def minPos (xs : List Int) : Option Int := List.min? (xs.filter (fun x => decide (0 < x)))

def maxVal (xs : List Int) : Option Int := List.max? xs

/-- Whenever the function returns a result r, the following holds. For an array A, let count_A(v) be the number of indices i with 0 <= i < len(A) and A[i] = v. Call an array O a valid original for changed if len(changed) = 2 * len(O) and for every integer v, count_changed(v) = count_O(v) + (the number of indices i with 0 <= i < len(O) and 2 * O[i] = v). If there exists a valid original for changed, then r is a valid original for changed. Otherwise (no valid original exists), len(r) = 0.
  Preconditions: len(changed) >= 1, len(changed) <= 100000, and for every i with 0 <= i < len(changed), 0 <= changed[i] <= 100000. -/
theorem spec_1 (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      (IsDoubled (vals changed.val) → IsOriginal (vals changed.val) (vals r.val)) ∧
      (¬ IsDoubled (vals changed.val) → r.val.length = 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000), ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      (IsDoubled (vals changed.val) → IsOriginal (vals changed.val) (vals r.val)) ∧
      (¬ IsDoubled (vals changed.val) → r.val.length = 0)) := by
  sorry

/-- The function returns a result r (i.e., it does not fail) for every input satisfying the preconditions.
  Preconditions: len(changed) >= 1, len(changed) <= 100000, and for every i with 0 <= i < len(changed), 0 <= changed[i] <= 100000. -/
theorem spec_2 (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000) :
    ∃ r : alloc.vec.Vec Std.I64, find_original_array changed = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000), ∃ r : alloc.vec.Vec Std.I64, find_original_array changed = ok r) := by
  sorry

/-- Whenever the function returns a result r, either len(r) = 0 or len(changed) = 2 * len(r).
  Preconditions: len(changed) >= 1, len(changed) <= 100000, and for every i with 0 <= i < len(changed), 0 <= changed[i] <= 100000. -/
theorem spec_3 (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      r.val.length = 0 ∨ changed.length = 2 * r.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000), ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      r.val.length = 0 ∨ changed.length = 2 * r.val.length) := by
  sorry

/-- If len(changed) is odd, then whenever the function returns a result r, len(r) = 0.
  Preconditions: len(changed) >= 1, len(changed) <= 100000, for every i with 0 <= i < len(changed), 0 <= changed[i] <= 100000, and len(changed) is odd. -/
theorem spec_4 (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000)
    (hodd : Odd changed.length) :
    ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r → r.val.length = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000)
    (hodd : Odd changed.length), ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r → r.val.length = 0) := by
  sorry

/-- If the number of indices i with 0 <= i < len(changed) and changed[i] = 0 is odd, then whenever the function returns a result r, len(r) = 0.
  Preconditions: len(changed) >= 1, len(changed) <= 100000, for every i with 0 <= i < len(changed), 0 <= changed[i] <= 100000, and the number of indices i with 0 <= i < len(changed) and changed[i] = 0 is odd. -/
theorem spec_5 (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000)
    (hzero : Odd (cnt (vals changed.val) 0)) :
    ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r → r.val.length = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000)
    (hzero : Odd (cnt (vals changed.val) 0)), ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r → r.val.length = 0) := by
  sorry

/-- Whenever the function returns a result r, if len(r) > 0 then changed is a doubled array (i.e., there exists an array O satisfying len(changed) = 2 * len(O) and for every integer v, count_changed(v) = count_O(v) + (the number of indices i with 0 <= i < len(O) and 2 * O[i] = v)), where count_A(v) is the number of indices i with 0 <= i < len(A) and A[i] = v.
  Preconditions: len(changed) >= 1, len(changed) <= 100000, and for every i with 0 <= i < len(changed), 0 <= changed[i] <= 100000. -/
theorem spec_6 (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      0 < r.val.length → IsDoubled (vals changed.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000), ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      0 < r.val.length → IsDoubled (vals changed.val)) := by
  sorry

/-- If changed is a doubled array, then whenever the function returns a result r, len(r) > 0.
  Preconditions: len(changed) >= 1, len(changed) <= 100000, for every i with 0 <= i < len(changed), 0 <= changed[i] <= 100000, and changed is a doubled array, i.e., there exists an array O such that len(changed) = 2 * len(O) and for every integer v, count_changed(v) = count_O(v) + (the number of indices i with 0 <= i < len(O) and 2 * O[i] = v), where count_A(v) is the number of indices i with 0 <= i < len(A) and A[i] = v. -/
theorem spec_7 (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000)
    (hdoubled : IsDoubled (vals changed.val)) :
    ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r → 0 < r.val.length := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000)
    (hdoubled : IsDoubled (vals changed.val)), ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r → 0 < r.val.length) := by
  sorry

/-- Whenever the function returns a result r, if len(r) > 0 then for every integer v, the number of indices i with 0 <= i < len(changed) and changed[i] = v equals the number of indices i with 0 <= i < len(r) and r[i] = v plus the number of indices i with 0 <= i < len(r) and 2 * r[i] = v.
  Preconditions: len(changed) >= 1, len(changed) <= 100000, and for every i with 0 <= i < len(changed), 0 <= changed[i] <= 100000. -/
theorem spec_8 (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      0 < r.val.length →
      ∀ v : Int, cnt (vals changed.val) v = cnt (vals r.val) v + cnt (dbl (vals r.val)) v := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000), ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      0 < r.val.length →
      ∀ v : Int, cnt (vals changed.val) v = cnt (vals r.val) v + cnt (dbl (vals r.val)) v) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v is at most the number of indices i with 0 <= i < len(changed) and changed[i] = v.
  Preconditions: len(changed) >= 1, len(changed) <= 100000, and for every i with 0 <= i < len(changed), 0 <= changed[i] <= 100000. -/
theorem spec_9 (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      ∀ v : Int, cnt (vals r.val) v ≤ cnt (vals changed.val) v := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000), ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      ∀ v : Int, cnt (vals r.val) v ≤ cnt (vals changed.val) v) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v is at most the number of indices i with 0 <= i < len(changed) and changed[i] = 2 * v.
  Preconditions: len(changed) >= 1, len(changed) <= 100000, and for every i with 0 <= i < len(changed), 0 <= changed[i] <= 100000. -/
theorem spec_10 (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      ∀ v : Int, cnt (vals r.val) v ≤ cnt (vals changed.val) (2 * v) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000), ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      ∀ v : Int, cnt (vals r.val) v ≤ cnt (vals changed.val) (2 * v)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), 0 <= r[i] <= 50000.
  Preconditions: len(changed) >= 1, len(changed) <= 100000, and for every i with 0 <= i < len(changed), 0 <= changed[i] <= 100000. -/
theorem spec_11 (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      ∀ (i : Nat) (h : i < r.val.length),
        0 ≤ (r.val.get ⟨i, h⟩).val ∧ (r.val.get ⟨i, h⟩).val ≤ 50000 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000), ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      ∀ (i : Nat) (h : i < r.val.length),
        0 ≤ (r.val.get ⟨i, h⟩).val ∧ (r.val.get ⟨i, h⟩).val ≤ 50000) := by
  sorry

/-- Whenever the function returns a result r, if len(r) > 0 and there exists a positive element in changed, then the minimum positive value m of changed (i.e., m = min{ changed[i] | 0 <= i < len(changed) and changed[i] > 0 }) satisfies: there exists an index j with 0 <= j < len(r) and r[j] = m.
  Preconditions: len(changed) >= 1, len(changed) <= 100000, and for every i with 0 <= i < len(changed), 0 <= changed[i] <= 100000. -/
theorem spec_12 (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      0 < r.val.length →
      (∃ x : Int, x ∈ vals changed.val ∧ 0 < x) →
      ∃ m : Int, minPos (vals changed.val) = some m ∧
        ∃ (j : Nat) (hj : j < r.val.length), (r.val.get ⟨j, hj⟩).val = m := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000), ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      0 < r.val.length →
      (∃ x : Int, x ∈ vals changed.val ∧ 0 < x) →
      ∃ m : Int, minPos (vals changed.val) = some m ∧
        ∃ (j : Nat) (hj : j < r.val.length), (r.val.get ⟨j, hj⟩).val = m) := by
  sorry

/-- Whenever the function returns a result r, if len(r) > 0 and the maximum value M of changed is positive (i.e., M = max{ changed[i] | 0 <= i < len(changed) } > 0), then M is even and the number of indices i with 0 <= i < len(r) and r[i] = M/2 equals the number of indices i with 0 <= i < len(changed) and changed[i] = M.
  Preconditions: len(changed) >= 1, len(changed) <= 100000, and for every i with 0 <= i < len(changed), 0 <= changed[i] <= 100000. -/
theorem spec_13 (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      0 < r.val.length →
      ∀ M : Int, maxVal (vals changed.val) = some M → 0 < M →
        Even M ∧ cnt (vals r.val) (M / 2) = cnt (vals changed.val) M := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000), ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      0 < r.val.length →
      ∀ M : Int, maxVal (vals changed.val) = some M → 0 < M →
        Even M ∧ cnt (vals r.val) (M / 2) = cnt (vals changed.val) M) := by
  sorry

/-- Whenever the function returns a result r, if len(r) > 0 then the sum of the elements of changed equals three times the sum of the elements of r.
  Preconditions: len(changed) >= 1, len(changed) <= 100000, and for every i with 0 <= i < len(changed), 0 <= changed[i] <= 100000. -/
theorem spec_14 (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      0 < r.val.length → (vals changed.val).sum = 3 * (vals r.val).sum := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (changed : Slice Std.I64)
    (hlen_ge : 1 ≤ changed.length) (hlen_le : changed.length ≤ 100000)
    (hbounds : ∀ (i : Nat) (h : i < changed.val.length),
      0 ≤ (changed.val.get ⟨i, h⟩).val ∧ (changed.val.get ⟨i, h⟩).val ≤ 100000), ∀ (r : alloc.vec.Vec Std.I64), find_original_array changed = ok r →
      0 < r.val.length → (vals changed.val).sum = 3 * (vals r.val).sum) := by
  sorry

end AegisSpec.FindOriginalArray
