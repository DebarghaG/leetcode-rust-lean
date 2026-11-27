import Aegis.GetDistances.Code.Funs

/-!
# Specifications of `Aegis.GetDistances.get_distances`

LeetCode problem `intervals-between-identical-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetDistances

def rev (arr : Slice I64) : Slice I64 where
  leng := arr.val.reverse.length
  list := Aeneas.Data.ListN.ListN.fromList arr.val.reverse
  bound := by
    rw [List.length_reverse]
    exact le_trans (le_of_eq (Aeneas.Data.ListN.ListN_length arr.list)) arr.bound

def distSum (arr : Slice I64) (i : ℕ) : ℤ :=
  ∑ j ∈ Finset.range arr.val.length,
    if (arr.val[j]!).val = (arr.val[i]!).val then |(i : ℤ) - (j : ℤ)| else 0

def pairDistSum (arr : Slice I64) : ℤ :=
  ∑ i ∈ Finset.range arr.val.length, ∑ j ∈ Finset.range arr.val.length,
    if i < j ∧ (arr.val[i]!).val = (arr.val[j]!).val then ((j : ℤ) - (i : ℤ)) else 0

/-- Whenever the function returns a result r, len(r) = len(arr) and for every i with 0 <= i < len(arr), r[i] = sum_{j=0}^{len(arr)-1} (if arr[j] = arr[i] then |i - j| else 0).
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000 -/
theorem spec_1 (arr : Slice I64)
    (hn1 : 1 ≤ arr.val.length) (hn2 : arr.val.length ≤ 100000)
    (hbound : ∀ (j : ℕ) (_ : j < arr.val.length),
      1 ≤ (arr.val[j]!).val ∧ (arr.val[j]!).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec I64), Aegis.GetDistances.get_distances arr = ok r →
      r.val.length = arr.val.length ∧
        ∀ (i : ℕ) (_ : i < arr.val.length), (r.val[i]!).val = distSum arr i := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice I64)
    (hn1 : 1 ≤ arr.val.length) (hn2 : arr.val.length ≤ 100000)
    (hbound : ∀ (j : ℕ) (_ : j < arr.val.length),
      1 ≤ (arr.val[j]!).val ∧ (arr.val[j]!).val ≤ 100000), ∀ (r : alloc.vec.Vec I64), Aegis.GetDistances.get_distances arr = ok r →
      r.val.length = arr.val.length ∧
        ∀ (i : ℕ) (_ : i < arr.val.length), (r.val[i]!).val = distSum arr i) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(arr), r[i] >= 0.
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000 -/
theorem spec_2 (arr : Slice I64)
    (hn1 : 1 ≤ arr.val.length) (hn2 : arr.val.length ≤ 100000)
    (hbound : ∀ (j : ℕ) (_ : j < arr.val.length),
      1 ≤ (arr.val[j]!).val ∧ (arr.val[j]!).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec I64), Aegis.GetDistances.get_distances arr = ok r →
      ∀ (i : ℕ) (_ : i < arr.val.length), 0 ≤ (r.val[i]!).val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice I64)
    (hn1 : 1 ≤ arr.val.length) (hn2 : arr.val.length ≤ 100000)
    (hbound : ∀ (j : ℕ) (_ : j < arr.val.length),
      1 ≤ (arr.val[j]!).val ∧ (arr.val[j]!).val ≤ 100000), ∀ (r : alloc.vec.Vec I64), Aegis.GetDistances.get_distances arr = ok r →
      ∀ (i : ℕ) (_ : i < arr.val.length), 0 ≤ (r.val[i]!).val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(arr), r[i] <= (len(arr) * (len(arr) - 1)) / 2.
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000 -/
theorem spec_3 (arr : Slice I64)
    (hn1 : 1 ≤ arr.val.length) (hn2 : arr.val.length ≤ 100000)
    (hbound : ∀ (j : ℕ) (_ : j < arr.val.length),
      1 ≤ (arr.val[j]!).val ∧ (arr.val[j]!).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec I64), Aegis.GetDistances.get_distances arr = ok r →
      ∀ (i : ℕ) (_ : i < arr.val.length),
        (r.val[i]!).val ≤ (((arr.val.length * (arr.val.length - 1)) / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice I64)
    (hn1 : 1 ≤ arr.val.length) (hn2 : arr.val.length ≤ 100000)
    (hbound : ∀ (j : ℕ) (_ : j < arr.val.length),
      1 ≤ (arr.val[j]!).val ∧ (arr.val[j]!).val ≤ 100000), ∀ (r : alloc.vec.Vec I64), Aegis.GetDistances.get_distances arr = ok r →
      ∀ (i : ℕ) (_ : i < arr.val.length),
        (r.val[i]!).val ≤ (((arr.val.length * (arr.val.length - 1)) / 2 : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(arr), r[i] = 0 if and only if for every j with 0 <= j < len(arr), arr[j] = arr[i] implies j = i.
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000 -/
theorem spec_4 (arr : Slice I64)
    (hn1 : 1 ≤ arr.val.length) (hn2 : arr.val.length ≤ 100000)
    (hbound : ∀ (j : ℕ) (_ : j < arr.val.length),
      1 ≤ (arr.val[j]!).val ∧ (arr.val[j]!).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec I64), Aegis.GetDistances.get_distances arr = ok r →
      ∀ (i : ℕ) (_ : i < arr.val.length),
        ((r.val[i]!).val = 0 ↔
          ∀ (j : ℕ) (_ : j < arr.val.length),
            (arr.val[j]!).val = (arr.val[i]!).val → j = i) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice I64)
    (hn1 : 1 ≤ arr.val.length) (hn2 : arr.val.length ≤ 100000)
    (hbound : ∀ (j : ℕ) (_ : j < arr.val.length),
      1 ≤ (arr.val[j]!).val ∧ (arr.val[j]!).val ≤ 100000), ∀ (r : alloc.vec.Vec I64), Aegis.GetDistances.get_distances arr = ok r →
      ∀ (i : ℕ) (_ : i < arr.val.length),
        ((r.val[i]!).val = 0 ↔
          ∀ (j : ℕ) (_ : j < arr.val.length),
            (arr.val[j]!).val = (arr.val[i]!).val → j = i)) := by
  sorry

/-- For every array arr' of the same length with all elements in [1, 100000] such that for every i, j with 0 <= i < len(arr) and 0 <= j < len(arr), arr[i] = arr[j] if and only if arr'[i] = arr'[j], whenever get_distances(arr) returns r and get_distances(arr') returns r', we have len(r) = len(r') and for every i with 0 <= i < len(arr), r[i] = r'[i].
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000 -/
theorem spec_5 (arr : Slice I64)
    (hn1 : 1 ≤ arr.val.length) (hn2 : arr.val.length ≤ 100000)
    (hbound : ∀ (j : ℕ) (_ : j < arr.val.length),
      1 ≤ (arr.val[j]!).val ∧ (arr.val[j]!).val ≤ 100000) :
    ∀ (arr' : Slice I64), arr'.val.length = arr.val.length →
      (∀ (j : ℕ) (_ : j < arr'.val.length),
        1 ≤ (arr'.val[j]!).val ∧ (arr'.val[j]!).val ≤ 100000) →
      (∀ (i j : ℕ) (_ : i < arr.val.length) (_ : j < arr.val.length),
        ((arr.val[i]!).val = (arr.val[j]!).val ↔
          (arr'.val[i]!).val = (arr'.val[j]!).val)) →
      ∀ (r r' : alloc.vec.Vec I64),
        Aegis.GetDistances.get_distances arr = ok r →
        Aegis.GetDistances.get_distances arr' = ok r' →
        r.val.length = r'.val.length ∧
          ∀ (i : ℕ) (_ : i < arr.val.length), (r.val[i]!).val = (r'.val[i]!).val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice I64)
    (hn1 : 1 ≤ arr.val.length) (hn2 : arr.val.length ≤ 100000)
    (hbound : ∀ (j : ℕ) (_ : j < arr.val.length),
      1 ≤ (arr.val[j]!).val ∧ (arr.val[j]!).val ≤ 100000), ∀ (arr' : Slice I64), arr'.val.length = arr.val.length →
      (∀ (j : ℕ) (_ : j < arr'.val.length),
        1 ≤ (arr'.val[j]!).val ∧ (arr'.val[j]!).val ≤ 100000) →
      (∀ (i j : ℕ) (_ : i < arr.val.length) (_ : j < arr.val.length),
        ((arr.val[i]!).val = (arr.val[j]!).val ↔
          (arr'.val[i]!).val = (arr'.val[j]!).val)) →
      ∀ (r r' : alloc.vec.Vec I64),
        Aegis.GetDistances.get_distances arr = ok r →
        Aegis.GetDistances.get_distances arr' = ok r' →
        r.val.length = r'.val.length ∧
          ∀ (i : ℕ) (_ : i < arr.val.length), (r.val[i]!).val = (r'.val[i]!).val) := by
  sorry

/-- Let rev(arr) be the array of length len(arr) with rev(arr)[i] = arr[len(arr)-1-i] for 0 <= i < len(arr). Whenever get_distances(arr) returns r and get_distances(rev(arr)) returns r', we have len(r) = len(r') and for every i with 0 <= i < len(arr), r'[i] = r[len(arr)-1-i].
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000 -/
theorem spec_6 (arr : Slice I64)
    (hn1 : 1 ≤ arr.val.length) (hn2 : arr.val.length ≤ 100000)
    (hbound : ∀ (j : ℕ) (_ : j < arr.val.length),
      1 ≤ (arr.val[j]!).val ∧ (arr.val[j]!).val ≤ 100000) :
    ∀ (r r' : alloc.vec.Vec I64),
      Aegis.GetDistances.get_distances arr = ok r →
      Aegis.GetDistances.get_distances (rev arr) = ok r' →
      r.val.length = r'.val.length ∧
        ∀ (i : ℕ) (_ : i < arr.val.length),
          (r'.val[i]!).val = (r.val[arr.val.length - 1 - i]!).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice I64)
    (hn1 : 1 ≤ arr.val.length) (hn2 : arr.val.length ≤ 100000)
    (hbound : ∀ (j : ℕ) (_ : j < arr.val.length),
      1 ≤ (arr.val[j]!).val ∧ (arr.val[j]!).val ≤ 100000), ∀ (r r' : alloc.vec.Vec I64),
      Aegis.GetDistances.get_distances arr = ok r →
      Aegis.GetDistances.get_distances (rev arr) = ok r' →
      r.val.length = r'.val.length ∧
        ∀ (i : ℕ) (_ : i < arr.val.length),
          (r'.val[i]!).val = (r.val[arr.val.length - 1 - i]!).val) := by
  sorry

/-- The function returns a result r (i.e., it does not fail).
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000 -/
theorem spec_7 (arr : Slice I64)
    (hn1 : 1 ≤ arr.val.length) (hn2 : arr.val.length ≤ 100000)
    (hbound : ∀ (j : ℕ) (_ : j < arr.val.length),
      1 ≤ (arr.val[j]!).val ∧ (arr.val[j]!).val ≤ 100000) :
    ∃ r : alloc.vec.Vec I64, Aegis.GetDistances.get_distances arr = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice I64)
    (hn1 : 1 ≤ arr.val.length) (hn2 : arr.val.length ≤ 100000)
    (hbound : ∀ (j : ℕ) (_ : j < arr.val.length),
      1 ≤ (arr.val[j]!).val ∧ (arr.val[j]!).val ≤ 100000), ∃ r : alloc.vec.Vec I64, Aegis.GetDistances.get_distances arr = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, the sum_{i=0}^{len(arr)-1} (if arr[i] = v then r[i] else 0) is even.
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000 -/
theorem spec_8 (arr : Slice I64)
    (hn1 : 1 ≤ arr.val.length) (hn2 : arr.val.length ≤ 100000)
    (hbound : ∀ (j : ℕ) (_ : j < arr.val.length),
      1 ≤ (arr.val[j]!).val ∧ (arr.val[j]!).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec I64), Aegis.GetDistances.get_distances arr = ok r →
      ∀ (v : ℤ),
        Even (∑ i ∈ Finset.range arr.val.length,
          if (arr.val[i]!).val = v then (r.val[i]!).val else 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice I64)
    (hn1 : 1 ≤ arr.val.length) (hn2 : arr.val.length ≤ 100000)
    (hbound : ∀ (j : ℕ) (_ : j < arr.val.length),
      1 ≤ (arr.val[j]!).val ∧ (arr.val[j]!).val ≤ 100000), ∀ (r : alloc.vec.Vec I64), Aegis.GetDistances.get_distances arr = ok r →
      ∀ (v : ℤ),
        Even (∑ i ∈ Finset.range arr.val.length,
          if (arr.val[i]!).val = v then (r.val[i]!).val else 0)) := by
  sorry

/-- Whenever the function returns a result r, sum_{i=0}^{len(arr)-1} r[i] = 2 * sum_{0 <= i < j < len(arr), arr[i] = arr[j]} (j - i).
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000 -/
theorem spec_9 (arr : Slice I64)
    (hn1 : 1 ≤ arr.val.length) (hn2 : arr.val.length ≤ 100000)
    (hbound : ∀ (j : ℕ) (_ : j < arr.val.length),
      1 ≤ (arr.val[j]!).val ∧ (arr.val[j]!).val ≤ 100000) :
    ∀ (r : alloc.vec.Vec I64), Aegis.GetDistances.get_distances arr = ok r →
      (∑ i ∈ Finset.range arr.val.length, (r.val[i]!).val) = 2 * pairDistSum arr := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice I64)
    (hn1 : 1 ≤ arr.val.length) (hn2 : arr.val.length ≤ 100000)
    (hbound : ∀ (j : ℕ) (_ : j < arr.val.length),
      1 ≤ (arr.val[j]!).val ∧ (arr.val[j]!).val ≤ 100000), ∀ (r : alloc.vec.Vec I64), Aegis.GetDistances.get_distances arr = ok r →
      (∑ i ∈ Finset.range arr.val.length, (r.val[i]!).val) = 2 * pairDistSum arr) := by
  sorry

end AegisSpec.GetDistances
