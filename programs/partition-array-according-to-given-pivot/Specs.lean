import Aegis.PivotArray.Code.Funs

/-!
# Specifications of `Aegis.PivotArray.pivot_array`

LeetCode problem `partition-array-according-to-given-pivot`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.PivotArray

def lessElems (l : List I64) (p : I64) : List I64 :=
  l.filter (fun x => decide (x.val < p.val))

def eqElems (l : List I64) (p : I64) : List I64 :=
  l.filter (fun x => decide (x.val = p.val))

def greaterElems (l : List I64) (p : I64) : List I64 :=
  l.filter (fun x => decide (p.val < x.val))

def countLT (l : List I64) (p : I64) : Nat := (lessElems l p).length

def countEQ (l : List I64) (p : I64) : Nat := (eqElems l p).length

def countGT (l : List I64) (p : I64) : Nat := (greaterElems l p).length

def countValue (l : List I64) (v : Int) : Nat :=
  l.filter (fun x => decide (x.val = v)) |>.length

def nthIndexWhere {α : Type} (P : α → Bool) : List α → Nat → Nat
  | [], _ => 0
  | x :: xs, 0 => if P x then 0 else (nthIndexWhere P xs 0) + 1
  | x :: xs, t + 1 => if P x then (nthIndexWhere P xs t) + 1 else (nthIndexWhere P xs (t + 1)) + 1

def nthIndexLT (l : List I64) (p : I64) (t : Nat) : Nat :=
  nthIndexWhere (fun x => decide (x.val < p.val)) l t

def nthIndexGT (l : List I64) (p : I64) (t : Nat) : Nat :=
  nthIndexWhere (fun x => decide (p.val < x.val)) l t

/-- Whenever the function returns a result r, the following holds. Let a be the number of indices i with 0 <= i < len(nums) and nums[i] < pivot, let e be the number of indices i with 0 <= i < len(nums) and nums[i] = pivot, and let c be the number of indices i with 0 <= i < len(nums) and nums[i] > pivot. Let l_0 < l_1 < ... < l_{a-1} be the indices i with 0 <= i < len(nums) and nums[i] < pivot, and let g_0 < g_1 < ... < g_{c-1} be the indices i with 0 <= i < len(nums) and nums[i] > pivot. Then len(r) = len(nums) = a + e + c, and for every t with 0 <= t < a, r[t] = nums[l_t], and for every t with 0 <= t < e, r[a + t] = pivot, and for every t with 0 <= t < c, r[a + e + t] = nums[g_t].
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^6 <= nums[i] <= 10^6; and there exists i with 0 <= i < len(nums) such that nums[i] = pivot. -/
theorem spec_1 (nums : Slice I64) (pivot : I64) (r : alloc.vec.Vec I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val)
    (h_returns : Aegis.PivotArray.pivot_array nums pivot = ok r) :
    r.val.length = nums.val.length ∧
    nums.val.length = countLT nums.val pivot + countEQ nums.val pivot + countGT nums.val pivot ∧
    (∀ (t : Nat), t < countLT nums.val pivot →
      r.val[t]? = nums.val[nthIndexLT nums.val pivot t]?) ∧
    (∀ (t : Nat), t < countEQ nums.val pivot →
      r.val[countLT nums.val pivot + t]? = some pivot) ∧
    (∀ (t : Nat), t < countGT nums.val pivot →
      r.val[countLT nums.val pivot + countEQ nums.val pivot + t]? =
        nums.val[nthIndexGT nums.val pivot t]?) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (pivot : I64) (r : alloc.vec.Vec I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val)
    (h_returns : Aegis.PivotArray.pivot_array nums pivot = ok r), r.val.length = nums.val.length ∧
    nums.val.length = countLT nums.val pivot + countEQ nums.val pivot + countGT nums.val pivot ∧
    (∀ (t : Nat), t < countLT nums.val pivot →
      r.val[t]? = nums.val[nthIndexLT nums.val pivot t]?) ∧
    (∀ (t : Nat), t < countEQ nums.val pivot →
      r.val[countLT nums.val pivot + t]? = some pivot) ∧
    (∀ (t : Nat), t < countGT nums.val pivot →
      r.val[countLT nums.val pivot + countEQ nums.val pivot + t]? =
        nums.val[nthIndexGT nums.val pivot t]?)) := by
  sorry

/-- Whenever the function returns a result r, for every integer value v, the number of indices i with 0 <= i < len(r) and r[i] = v equals the number of indices i with 0 <= i < len(nums) and nums[i] = v.
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^6 <= nums[i] <= 10^6; and there exists i with 0 <= i < len(nums) such that nums[i] = pivot. -/
theorem spec_2 (nums : Slice I64) (pivot : I64) (r : alloc.vec.Vec I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val)
    (h_returns : Aegis.PivotArray.pivot_array nums pivot = ok r) :
    ∀ (v : Int), countValue r.val v = countValue nums.val v := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (pivot : I64) (r : alloc.vec.Vec I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val)
    (h_returns : Aegis.PivotArray.pivot_array nums pivot = ok r), ∀ (v : Int), countValue r.val v = countValue nums.val v) := by
  sorry

/-- Whenever the function returns a result r, for all i and j with 0 <= i < j < len(r): if r[i] = pivot then r[j] >= pivot, and if r[i] > pivot then r[j] > pivot.
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^6 <= nums[i] <= 10^6; and there exists i with 0 <= i < len(nums) such that nums[i] = pivot. -/
theorem spec_3 (nums : Slice I64) (pivot : I64) (r : alloc.vec.Vec I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val)
    (h_returns : Aegis.PivotArray.pivot_array nums pivot = ok r) :
    ∀ (i j : Nat) (hij : i < j) (hj : j < r.val.length),
      ((r.val[i]'(Nat.lt_trans hij hj)).val = pivot.val →
        pivot.val ≤ (r.val[j]'hj).val) ∧
      (pivot.val < (r.val[i]'(Nat.lt_trans hij hj)).val →
        pivot.val < (r.val[j]'hj).val) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (pivot : I64) (r : alloc.vec.Vec I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val)
    (h_returns : Aegis.PivotArray.pivot_array nums pivot = ok r), ∀ (i j : Nat) (hij : i < j) (hj : j < r.val.length),
      ((r.val[i]'(Nat.lt_trans hij hj)).val = pivot.val →
        pivot.val ≤ (r.val[j]'hj).val) ∧
      (pivot.val < (r.val[i]'(Nat.lt_trans hij hj)).val →
        pivot.val < (r.val[j]'hj).val)) := by
  sorry

/-- Whenever the function returns a result r, let a be the number of indices i with 0 <= i < len(nums) and nums[i] < pivot, let e be the number of indices i with 0 <= i < len(nums) and nums[i] = pivot, and let n = len(nums). Then len(r) = n, for every i with 0 <= i < a, r[i] < pivot, and for every i with a + e <= i < n, r[i] > pivot.
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^6 <= nums[i] <= 10^6; and there exists i with 0 <= i < len(nums) such that nums[i] = pivot. -/
theorem spec_4 (nums : Slice I64) (pivot : I64) (r : alloc.vec.Vec I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val)
    (h_returns : Aegis.PivotArray.pivot_array nums pivot = ok r) :
    r.val.length = nums.val.length ∧
    (∀ (i : Nat), i < countLT nums.val pivot →
      ∀ (v : I64), r.val[i]? = some v → v.val < pivot.val) ∧
    (∀ (i : Nat), countLT nums.val pivot + countEQ nums.val pivot ≤ i →
      i < nums.val.length →
      ∀ (v : I64), r.val[i]? = some v → pivot.val < v.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (pivot : I64) (r : alloc.vec.Vec I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val)
    (h_returns : Aegis.PivotArray.pivot_array nums pivot = ok r), r.val.length = nums.val.length ∧
    (∀ (i : Nat), i < countLT nums.val pivot →
      ∀ (v : I64), r.val[i]? = some v → v.val < pivot.val) ∧
    (∀ (i : Nat), countLT nums.val pivot + countEQ nums.val pivot ≤ i →
      i < nums.val.length →
      ∀ (v : I64), r.val[i]? = some v → pivot.val < v.val)) := by
  sorry

/-- Whenever the function returns a result r, the list formed by the elements of r that are strictly less than pivot, in their order of occurrence in r, is equal to the list formed by the elements of nums that are strictly less than pivot, in their order of occurrence in nums.
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^6 <= nums[i] <= 10^6; and there exists i with 0 <= i < len(nums) such that nums[i] = pivot. -/
theorem spec_5 (nums : Slice I64) (pivot : I64) (r : alloc.vec.Vec I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val)
    (h_returns : Aegis.PivotArray.pivot_array nums pivot = ok r) :
    lessElems r.val pivot = lessElems nums.val pivot := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (pivot : I64) (r : alloc.vec.Vec I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val)
    (h_returns : Aegis.PivotArray.pivot_array nums pivot = ok r), lessElems r.val pivot = lessElems nums.val pivot) := by
  sorry

/-- Whenever the function returns a result r, the list formed by the elements of r that are strictly greater than pivot, in their order of occurrence in r, is equal to the list formed by the elements of nums that are strictly greater than pivot, in their order of occurrence in nums.
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^6 <= nums[i] <= 10^6; and there exists i with 0 <= i < len(nums) such that nums[i] = pivot. -/
theorem spec_6 (nums : Slice I64) (pivot : I64) (r : alloc.vec.Vec I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val)
    (h_returns : Aegis.PivotArray.pivot_array nums pivot = ok r) :
    greaterElems r.val pivot = greaterElems nums.val pivot := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (pivot : I64) (r : alloc.vec.Vec I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val)
    (h_returns : Aegis.PivotArray.pivot_array nums pivot = ok r), greaterElems r.val pivot = greaterElems nums.val pivot) := by
  sorry

/-- For every nums and pivot satisfying the preconditions, the function returns a result r; it neither panics nor overflows.
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^6 <= nums[i] <= 10^6; and there exists i with 0 <= i < len(nums) such that nums[i] = pivot. -/
theorem spec_7 (nums : Slice I64) (pivot : I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val) :
    ∃ (r : alloc.vec.Vec I64), Aegis.PivotArray.pivot_array nums pivot = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (pivot : I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val), ∃ (r : alloc.vec.Vec I64), Aegis.PivotArray.pivot_array nums pivot = ok r) := by
  sorry

/-- Whenever the function returns a result r, applying the function again to r with the same pivot yields a result r' such that len(r') = len(r) and for every i with 0 <= i < len(r), r'[i] = r[i].
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^6 <= nums[i] <= 10^6; and there exists i with 0 <= i < len(nums) such that nums[i] = pivot. -/
theorem spec_8 (nums : Slice I64) (pivot : I64) (r : alloc.vec.Vec I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val)
    (h_returns : Aegis.PivotArray.pivot_array nums pivot = ok r) :
    ∃ (r' : alloc.vec.Vec I64),
      Aegis.PivotArray.pivot_array r.slice pivot = ok r' ∧
      r'.val.length = r.val.length ∧
      (∀ (i : Nat), i < r.val.length → r'.val[i]? = r.val[i]?) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (pivot : I64) (r : alloc.vec.Vec I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val)
    (h_returns : Aegis.PivotArray.pivot_array nums pivot = ok r), ∃ (r' : alloc.vec.Vec I64),
      Aegis.PivotArray.pivot_array r.slice pivot = ok r' ∧
      r'.val.length = r.val.length ∧
      (∀ (i : Nat), i < r.val.length → r'.val[i]? = r.val[i]?)) := by
  sorry

/-- Whenever the function returns a result r, let a be the number of indices i with 0 <= i < len(nums) and nums[i] < pivot, and let e be the number of indices i with 0 <= i < len(nums) and nums[i] = pivot. Then len(r) = len(nums), and for every i with a <= i < a + e, r[i] = pivot.
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^6 <= nums[i] <= 10^6; and there exists i with 0 <= i < len(nums) such that nums[i] = pivot. -/
theorem spec_9 (nums : Slice I64) (pivot : I64) (r : alloc.vec.Vec I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val)
    (h_returns : Aegis.PivotArray.pivot_array nums pivot = ok r) :
    r.val.length = nums.val.length ∧
    (∀ (i : Nat), countLT nums.val pivot ≤ i →
      i < countLT nums.val pivot + countEQ nums.val pivot →
      ∀ (v : I64), r.val[i]? = some v → v = pivot) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (pivot : I64) (r : alloc.vec.Vec I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val)
    (h_returns : Aegis.PivotArray.pivot_array nums pivot = ok r), r.val.length = nums.val.length ∧
    (∀ (i : Nat), countLT nums.val pivot ≤ i →
      i < countLT nums.val pivot + countEQ nums.val pivot →
      ∀ (v : I64), r.val[i]? = some v → v = pivot)) := by
  sorry

/-- Whenever the function returns a result r, for every index i with 0 <= i < len(nums) and nums[i] < pivot, letting k be the number of indices j with 0 <= j < i and nums[j] < pivot, we have 0 <= k < len(r) and r[k] = nums[i].
  Preconditions: len(nums) >= 1; len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^6 <= nums[i] <= 10^6; and there exists i with 0 <= i < len(nums) such that nums[i] = pivot. -/
theorem spec_10 (nums : Slice I64) (pivot : I64) (r : alloc.vec.Vec I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val)
    (h_returns : Aegis.PivotArray.pivot_array nums pivot = ok r) :
    ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val < pivot.val →
      ∃ (hk : countLT (nums.val.take i) pivot < r.val.length),
        r.val[countLT (nums.val.take i) pivot]'hk = nums.val[i]'hi := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (pivot : I64) (r : alloc.vec.Vec I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
      -1000000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000)
    (h_pivot_occurs : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = pivot.val)
    (h_returns : Aegis.PivotArray.pivot_array nums pivot = ok r), ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val < pivot.val →
      ∃ (hk : countLT (nums.val.take i) pivot < r.val.length),
        r.val[countLT (nums.val.take i) pivot]'hk = nums.val[i]'hi) := by
  sorry

end AegisSpec.PivotArray
