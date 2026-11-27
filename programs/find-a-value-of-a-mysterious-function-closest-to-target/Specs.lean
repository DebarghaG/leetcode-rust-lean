import Aegis.ClosestToTarget.Code.Funs

/-!
# Specifications of `Aegis.ClosestToTarget.closest_to_target`

LeetCode problem `find-a-value-of-a-mysterious-function-closest-to-target`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ClosestToTarget

open Aegis.ClosestToTarget (closest_to_target)

def bitAnd (a b : ℤ) : ℤ := ((BitVec.ofInt 64 a) &&& (BitVec.ofInt 64 b)).toInt

def andRange (xs : List Std.I64) (l u : ℕ) : ℤ :=
  ((xs.drop l).take (u + 1 - l)).foldl (fun acc x => bitAnd acc x.val) (-1)

def andValues (arr : Slice Std.I64) : Set ℤ :=
  {v | ∃ l u, l ≤ u ∧ u < arr.val.length ∧ v = andRange arr.val l u}

def distanceValues (arr : Slice Std.I64) (target : Std.I64) : Set ℤ :=
  {d | ∃ l u, l ≤ u ∧ u < arr.val.length ∧ d = |andRange arr.val l u - target.val|}

def entryValues (arr : Slice Std.I64) : Set ℤ :=
  {v | ∃ x ∈ arr.val, v = x.val}

/-- Let AND(l,u) = arr[l] & arr[l+1] & ... & arr[u] for 0 <= l <= u < len(arr), using bitwise AND on the nonnegative i64 values. Whenever the function returns a result r, r = min { |AND(l,u) - target| : 0 <= l <= u < len(arr) }.
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000, and 0 <= target <= 10000000. All indices are 0-based. -/
theorem spec_1
    (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000) :
    ∀ r, closest_to_target arr target = ok r → IsLeast (distanceValues arr target) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000), ∀ r, closest_to_target arr target = ok r → IsLeast (distanceValues arr target) r.val) := by
  sorry

/-- The function returns a result r; it does not fail (no out-of-bounds access and no i64 overflow).
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000, and 0 <= target <= 10000000. All indices are 0-based. -/
theorem spec_2
    (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000) :
    ∃ r, closest_to_target arr target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000), ∃ r, closest_to_target arr target = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000, and 0 <= target <= 10000000. All indices are 0-based. -/
theorem spec_3
    (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000) :
    ∀ r, closest_to_target arr target = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000), ∀ r, closest_to_target arr target = ok r → 0 ≤ r.val) := by
  sorry

/-- Let AND(l,u) = arr[l] & arr[l+1] & ... & arr[u] for 0 <= l <= u < len(arr), using bitwise AND. Whenever the function returns a result r, for every i with 0 <= i < len(arr), r <= |arr[i] - target|.
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000, and 0 <= target <= 10000000. All indices are 0-based. -/
theorem spec_4
    (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000) :
    ∀ r, closest_to_target arr target = ok r →
      ∀ (i : ℕ) (hi : i < arr.val.length),
        r.val ≤ |(arr.val.get ⟨i, hi⟩).val - target.val| := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000), ∀ r, closest_to_target arr target = ok r →
      ∀ (i : ℕ) (hi : i < arr.val.length),
        r.val ≤ |(arr.val.get ⟨i, hi⟩).val - target.val|) := by
  sorry

/-- Let AND(l,u) = arr[l] & arr[l+1] & ... & arr[u] for 0 <= l <= u < len(arr), using bitwise AND. Whenever the function returns a result r, there exist indices l and u with 0 <= l <= u < len(arr) such that r = |AND(l,u) - target|.
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000, and 0 <= target <= 10000000. All indices are 0-based. -/
theorem spec_5
    (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000) :
    ∀ r, closest_to_target arr target = ok r →
      ∃ l u, l ≤ u ∧ u < arr.val.length ∧ r.val = |andRange arr.val l u - target.val| := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000), ∀ r, closest_to_target arr target = ok r →
      ∃ l u, l ≤ u ∧ u < arr.val.length ∧ r.val = |andRange arr.val l u - target.val|) := by
  sorry

/-- Let AND(l,u) = arr[l] & arr[l+1] & ... & arr[u] for 0 <= l <= u < len(arr), using bitwise AND. Whenever the function returns a result r, for every l and u with 0 <= l <= u < len(arr), r <= |AND(l,u) - target|.
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000, and 0 <= target <= 10000000. All indices are 0-based. -/
theorem spec_6
    (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000) :
    ∀ r, closest_to_target arr target = ok r →
      ∀ l u, l ≤ u → u < arr.val.length →
        r.val ≤ |andRange arr.val l u - target.val| := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000), ∀ r, closest_to_target arr target = ok r →
      ∀ l u, l ≤ u → u < arr.val.length →
        r.val ≤ |andRange arr.val l u - target.val|) := by
  sorry

/-- Let AND(l,u) = arr[l] & arr[l+1] & ... & arr[u] for 0 <= l <= u < len(arr), using bitwise AND. Whenever the function returns a result r, r = 0 if and only if there exist l and u with 0 <= l <= u < len(arr) such that AND(l,u) = target.
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000, and 0 <= target <= 10000000. All indices are 0-based. -/
theorem spec_7
    (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000) :
    ∀ r, closest_to_target arr target = ok r →
      (r.val = 0 ↔ ∃ l u, l ≤ u ∧ u < arr.val.length ∧ andRange arr.val l u = target.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000), ∀ r, closest_to_target arr target = ok r →
      (r.val = 0 ↔ ∃ l u, l ≤ u ∧ u < arr.val.length ∧ andRange arr.val l u = target.val)) := by
  sorry

/-- Let AND(l,u) = arr[l] & arr[l+1] & ... & arr[u] for 0 <= l <= u < len(arr), using bitwise AND. If target = 0, then whenever the function returns a result r, r = min { AND(l,u) : 0 <= l <= u < len(arr) }.
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000, and 0 <= target <= 10000000. All indices are 0-based. -/
theorem spec_8
    (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000)
    (htarget0 : target.val = 0) :
    ∀ r, closest_to_target arr target = ok r → IsLeast (andValues arr) r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000)
    (htarget0 : target.val = 0), ∀ r, closest_to_target arr target = ok r → IsLeast (andValues arr) r.val) := by
  sorry

/-- If len(arr) = 1, then whenever the function returns a result r, r = |arr[0] - target|.
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000, and 0 <= target <= 10000000. All indices are 0-based. -/
theorem spec_9
    (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000)
    (hsingle : arr.val.length = 1) :
    ∀ r, closest_to_target arr target = ok r →
      r.val = |(arr.val.get ⟨0, by omega⟩).val - target.val| := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000)
    (hsingle : arr.val.length = 1), ∀ r, closest_to_target arr target = ok r →
      r.val = |(arr.val.get ⟨0, by omega⟩).val - target.val|) := by
  sorry

/-- If there exists an integer x such that arr[i] = x for every i with 0 <= i < len(arr), then whenever the function returns a result r, r = |x - target|.
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000, and 0 <= target <= 10000000. All indices are 0-based. -/
theorem spec_10
    (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000)
    (x : ℤ)
    (hconst : ∀ (i : ℕ) (hi : i < arr.val.length), (arr.val.get ⟨i, hi⟩).val = x) :
    ∀ r, closest_to_target arr target = ok r → r.val = |x - target.val| := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000)
    (x : ℤ)
    (hconst : ∀ (i : ℕ) (hi : i < arr.val.length), (arr.val.get ⟨i, hi⟩).val = x), ∀ r, closest_to_target arr target = ok r → r.val = |x - target.val|) := by
  sorry

/-- Let M = max { arr[i] : 0 <= i < len(arr) }. Whenever the function returns a result r, if target >= M, then r = target - M.
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000, and 0 <= target <= 10000000. All indices are 0-based. -/
theorem spec_11
    (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000)
    (M : ℤ) (hM : IsGreatest (entryValues arr) M) :
    ∀ r, closest_to_target arr target = ok r → M ≤ target.val → r.val = target.val - M := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000)
    (M : ℤ) (hM : IsGreatest (entryValues arr) M), ∀ r, closest_to_target arr target = ok r → M ≤ target.val → r.val = target.val - M) := by
  sorry

/-- Let AND(l,u) = arr[l] & arr[l+1] & ... & arr[u] for 0 <= l <= u < len(arr), using bitwise AND. Let V = { AND(l,u) : 0 <= l <= u < len(arr) } and let m = min V. Whenever the function returns a result r, if target <= v for every v in V, then r = m - target.
  Preconditions: len(arr) >= 1 and len(arr) <= 100000 and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000, and 0 <= target <= 10000000. All indices are 0-based. -/
theorem spec_12
    (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000)
    (m : ℤ) (hm : IsLeast (andValues arr) m) :
    ∀ r, closest_to_target arr target = ok r →
      (∀ v ∈ andValues arr, target.val ≤ v) → r.val = m - target.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr : Slice Std.I64) (target : Std.I64)
    (hpos : 1 ≤ arr.val.length)
    (hlen : arr.val.length ≤ 100000)
    (hval : ∀ (i : ℕ) (hi : i < arr.val.length),
      1 ≤ (arr.val.get ⟨i, hi⟩).val ∧ (arr.val.get ⟨i, hi⟩).val ≤ 1000000)
    (htarget : 0 ≤ target.val ∧ target.val ≤ 10000000)
    (m : ℤ) (hm : IsLeast (andValues arr) m), ∀ r, closest_to_target arr target = ok r →
      (∀ v ∈ andValues arr, target.val ≤ v) → r.val = m - target.val) := by
  sorry

end AegisSpec.ClosestToTarget
