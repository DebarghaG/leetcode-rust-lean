import Aegis.FindLucky.Code.Funs

/-!
# Specifications of `Aegis.FindLucky.find_lucky`

LeetCode problem `find-lucky-integer-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindLucky

def freq (arr : Slice Std.I64) (v : Int) : Nat :=
  (arr.val.filter (fun x => x.val = v)).length

def IsMaxElem (arr : Slice Std.I64) (m : Int) : Prop :=
  (∀ x ∈ arr.val, x.val ≤ m) ∧ ∃ x ∈ arr.val, x.val = m

def SameFreq (arr arr' : Slice Std.I64) : Prop :=
  ∀ v : Int, freq arr' v = freq arr v

/-- Let freq(v) be the number of indices i with 0 <= i < len(arr) and arr[i] = v. The function returns a result r, and: r = -1 if and only if there is no integer v with 1 <= v and freq(v) = v; if r != -1 then freq(r) = r and for every integer v with 1 <= v and freq(v) = v, v <= r.
  Preconditions: 1 <= len(arr) <= 500; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 500. -/
theorem spec_1 (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500) :
    ∃ r, Aegis.FindLucky.find_lucky arr = ok r ∧
      (r.val = -1 ↔ ∀ v : Int, 1 ≤ v → (freq arr v : Int) ≠ v) ∧
      (r.val ≠ -1 → (freq arr r.val : Int) = r.val ∧
        ∀ v : Int, 1 ≤ v → (freq arr v : Int) = v → v ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500), ∃ r, Aegis.FindLucky.find_lucky arr = ok r ∧
      (r.val = -1 ↔ ∀ v : Int, 1 ≤ v → (freq arr v : Int) ≠ v) ∧
      (r.val ≠ -1 → (freq arr r.val : Int) = r.val ∧
        ∀ v : Int, 1 ≤ v → (freq arr v : Int) = v → v ≤ r.val)) := by
  sorry

/-- For every slice arr satisfying the preconditions, the function returns a result r; it does not fail due to overflow, out-of-bounds access, or panic.
  Preconditions: 1 <= len(arr) <= 500; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 500. -/
theorem spec_2 (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500) :
    ∃ r, Aegis.FindLucky.find_lucky arr = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500), ∃ r, Aegis.FindLucky.find_lucky arr = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 1 <= r <= len(arr).
  Preconditions: 1 <= len(arr) <= 500; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 500. -/
theorem spec_3 (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500) :
    ∀ r, Aegis.FindLucky.find_lucky arr = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ ((Slice.len arr).val : Int)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500), ∀ r, Aegis.FindLucky.find_lucky arr = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ ((Slice.len arr).val : Int))) := by
  sorry

/-- Whenever the function returns a result r with r != -1, freq(r) = r, where freq(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v.
  Preconditions: 1 <= len(arr) <= 500; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 500. -/
theorem spec_4 (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500) :
    ∀ r, Aegis.FindLucky.find_lucky arr = ok r → r.val ≠ -1 → (freq arr r.val : Int) = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500), ∀ r, Aegis.FindLucky.find_lucky arr = ok r → r.val ≠ -1 → (freq arr r.val : Int) = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer v with v >= 1 and v > r, freq(v) != v, where freq(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v.
  Preconditions: 1 <= len(arr) <= 500; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 500. -/
theorem spec_5 (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500) :
    ∀ r, Aegis.FindLucky.find_lucky arr = ok r →
      ∀ v : Int, 1 ≤ v → r.val < v → (freq arr v : Int) ≠ v := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500), ∀ r, Aegis.FindLucky.find_lucky arr = ok r →
      ∀ v : Int, 1 ≤ v → r.val < v → (freq arr v : Int) ≠ v) := by
  sorry

/-- If for every integer v with 1 <= v, freq(v) != v, then the function returns a result r with r = -1, where freq(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v.
  Preconditions: 1 <= len(arr) <= 500; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 500. -/
theorem spec_6 (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500) :
    (∀ v : Int, 1 ≤ v → (freq arr v : Int) ≠ v) →
      ∃ r, Aegis.FindLucky.find_lucky arr = ok r ∧ r.val = -1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500), (∀ v : Int, 1 ≤ v → (freq arr v : Int) ≠ v) →
      ∃ r, Aegis.FindLucky.find_lucky arr = ok r ∧ r.val = -1) := by
  sorry

/-- If there exists an integer v with 1 <= v and freq(v) = v, then the function returns a result r with r != -1, where freq(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v.
  Preconditions: 1 <= len(arr) <= 500; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 500. -/
theorem spec_7 (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500) :
    (∃ v : Int, 1 ≤ v ∧ (freq arr v : Int) = v) →
      ∃ r, Aegis.FindLucky.find_lucky arr = ok r ∧ r.val ≠ -1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500), (∃ v : Int, 1 ≤ v ∧ (freq arr v : Int) = v) →
      ∃ r, Aegis.FindLucky.find_lucky arr = ok r ∧ r.val ≠ -1) := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exists an index i with 0 <= i < len(arr) and arr[i] = r.
  Preconditions: 1 <= len(arr) <= 500; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 500. -/
theorem spec_8 (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500) :
    ∀ r, Aegis.FindLucky.find_lucky arr = ok r → r.val ≠ -1 →
      ∃ (i : Nat) (h : i < arr.val.length), (arr.val.get ⟨i, h⟩).val = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500), ∀ r, Aegis.FindLucky.find_lucky arr = ok r → r.val ≠ -1 →
      ∃ (i : Nat) (h : i < arr.val.length), (arr.val.get ⟨i, h⟩).val = r.val) := by
  sorry

/-- Whenever the function returns a result r with r != -1, r <= max(arr), where max(arr) is the largest element of arr (well-defined since len(arr) >= 1).
  Preconditions: 1 <= len(arr) <= 500; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 500. -/
theorem spec_9 (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500) :
    ∀ r, Aegis.FindLucky.find_lucky arr = ok r → r.val ≠ -1 →
      ∀ m : Int, IsMaxElem arr m → r.val ≤ m := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500), ∀ r, Aegis.FindLucky.find_lucky arr = ok r → r.val ≠ -1 →
      ∀ m : Int, IsMaxElem arr m → r.val ≤ m) := by
  sorry

/-- For every slice arr' with len(arr') = len(arr) and for every integer v, freq_{arr'}(v) = freq_arr(v) (where freq_X(v) is the number of indices i with 0 <= i < len(X) and X[i] = v), the function returns the same result on arr' as on arr: if the function returns r on arr, then it returns r on arr'.
  Preconditions: 1 <= len(arr) <= 500; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 500. Let arr' be any slice with len(arr') = len(arr) and with the same frequency function as arr, i.e. for every integer v the number of occurrences of v in arr' equals that in arr. -/
theorem spec_10 (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500) :
    ∀ arr' : Slice Std.I64, (Slice.len arr').val = (Slice.len arr).val → SameFreq arr arr' →
      ∀ r, Aegis.FindLucky.find_lucky arr = ok r → Aegis.FindLucky.find_lucky arr' = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ (Slice.len arr).val) (hlen_max : (Slice.len arr).val ≤ 500)
    (hrange : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 500), ∀ arr' : Slice Std.I64, (Slice.len arr').val = (Slice.len arr).val → SameFreq arr arr' →
      ∀ r, Aegis.FindLucky.find_lucky arr = ok r → Aegis.FindLucky.find_lucky arr' = ok r) := by
  sorry

end AegisSpec.FindLucky
