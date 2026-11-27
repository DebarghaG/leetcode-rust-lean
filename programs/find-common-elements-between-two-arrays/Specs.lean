import Aegis.FindIntersectionValues.Code.Funs

/-!
# Specifications of `Aegis.FindIntersectionValues.find_intersection_values`

LeetCode problem `find-common-elements-between-two-arrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.FindIntersectionValues

namespace AegisSpec.FindIntersectionValues

def slen (nums : Slice Std.I64) : ℕ := nums.val.length

def entry (nums : Slice Std.I64) (i : ℕ) (h : i < nums.val.length) : ℤ := (nums.val[i]).val

def vecAt (r : alloc.vec.Vec Std.I64) (k : ℕ) : ℤ :=
  match r.val[k]? with
  | some x => x.val
  | none => 0

def Occurs (v : ℤ) (l : List Std.I64) : Prop := ∃ x ∈ l, x.val = v

instance (v : ℤ) (l : List Std.I64) : Decidable (Occurs v l) :=
  inferInstanceAs (Decidable (∃ x ∈ l, x.val = v))

def countOf (l : List Std.I64) (v : ℤ) : ℕ := (l.filter (fun x => x.val = v)).length

def countInOther (l1 l2 : List Std.I64) : ℕ :=
  (l1.filter (fun x => ∃ y ∈ l2, y.val = x.val)).length

def valuesOf (l : List Std.I64) : Finset ℤ := (l.map (fun x => x.val)).toFinset

def countSum (l1 l2 : List Std.I64) : ℤ :=
  Finset.sum (valuesOf l1 ∪ valuesOf l2)
    (fun v => (countOf l1 v : ℤ) * (if 0 < countOf l2 v then 1 else 0))

/-- Whenever find_intersection_values(nums1, nums2) returns a result r, len(r) = 2, r[0] is the cardinality of the set of indices i with 0 <= i < len(nums1) for which there exists j with 0 <= j < len(nums2) and nums2[j] = nums1[i], and r[1] is the cardinality of the set of indices j with 0 <= j < len(nums2) for which there exists i with 0 <= i < len(nums1) and nums1[i] = nums2[j].
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 100, len(nums2) <= 100, for every i with 0 <= i < len(nums1) we have 1 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2) we have 1 <= nums2[j] <= 100. -/
theorem spec_1 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100) :
    ∀ r, find_intersection_values nums1 nums2 = ok r →
      r.val.length = 2 ∧
        vecAt r 0 = (countInOther nums1.val nums2.val : ℤ) ∧
        vecAt r 1 = (countInOther nums2.val nums1.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100), ∀ r, find_intersection_values nums1 nums2 = ok r →
      r.val.length = 2 ∧
        vecAt r 0 = (countInOther nums1.val nums2.val : ℤ) ∧
        vecAt r 1 = (countInOther nums2.val nums1.val : ℤ)) := by
  sorry

/-- find_intersection_values(nums1, nums2) returns a result r (an Ok value); it does not fail, panic, or overflow.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 100, len(nums2) <= 100, for every i with 0 <= i < len(nums1) we have 1 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2) we have 1 <= nums2[j] <= 100. -/
theorem spec_2 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100) :
    ∃ r, find_intersection_values nums1 nums2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100), ∃ r, find_intersection_values nums1 nums2 = ok r) := by
  sorry

/-- Whenever find_intersection_values(nums1, nums2) returns a result r, 0 <= r[0] <= len(nums1).
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 100, len(nums2) <= 100, for every i with 0 <= i < len(nums1) we have 1 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2) we have 1 <= nums2[j] <= 100. -/
theorem spec_3 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100) :
    ∀ r, find_intersection_values nums1 nums2 = ok r →
      0 ≤ vecAt r 0 ∧ vecAt r 0 ≤ (slen nums1 : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100), ∀ r, find_intersection_values nums1 nums2 = ok r →
      0 ≤ vecAt r 0 ∧ vecAt r 0 ≤ (slen nums1 : ℤ)) := by
  sorry

/-- Whenever find_intersection_values(nums1, nums2) returns a result r, 0 <= r[1] <= len(nums2).
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 100, len(nums2) <= 100, for every i with 0 <= i < len(nums1) we have 1 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2) we have 1 <= nums2[j] <= 100. -/
theorem spec_4 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100) :
    ∀ r, find_intersection_values nums1 nums2 = ok r →
      0 ≤ vecAt r 1 ∧ vecAt r 1 ≤ (slen nums2 : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100), ∀ r, find_intersection_values nums1 nums2 = ok r →
      0 ≤ vecAt r 1 ∧ vecAt r 1 ≤ (slen nums2 : ℤ)) := by
  sorry

/-- Whenever find_intersection_values(nums1, nums2) returns a result r, if for every i with 0 <= i < len(nums1) and every j with 0 <= j < len(nums2) we have nums1[i] != nums2[j], then r[0] = 0 and r[1] = 0.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 100, len(nums2) <= 100, for every i with 0 <= i < len(nums1) we have 1 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2) we have 1 <= nums2[j] <= 100. -/
theorem spec_5 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100) :
    ∀ r, find_intersection_values nums1 nums2 = ok r →
      (∀ (i : ℕ) (hi : i < slen nums1) (j : ℕ) (hj : j < slen nums2),
        entry nums1 i hi ≠ entry nums2 j hj) →
      vecAt r 0 = 0 ∧ vecAt r 1 = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100), ∀ r, find_intersection_values nums1 nums2 = ok r →
      (∀ (i : ℕ) (hi : i < slen nums1) (j : ℕ) (hj : j < slen nums2),
        entry nums1 i hi ≠ entry nums2 j hj) →
      vecAt r 0 = 0 ∧ vecAt r 1 = 0) := by
  sorry

/-- Whenever find_intersection_values(nums1, nums2) returns a result r, if for every i with 0 <= i < len(nums1) there exists j with 0 <= j < len(nums2) and nums2[j] = nums1[i], then r[0] = len(nums1).
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 100, len(nums2) <= 100, for every i with 0 <= i < len(nums1) we have 1 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2) we have 1 <= nums2[j] <= 100. -/
theorem spec_6 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100) :
    ∀ r, find_intersection_values nums1 nums2 = ok r →
      (∀ (i : ℕ) (hi : i < slen nums1), Occurs (entry nums1 i hi) nums2.val) →
      vecAt r 0 = (slen nums1 : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100), ∀ r, find_intersection_values nums1 nums2 = ok r →
      (∀ (i : ℕ) (hi : i < slen nums1), Occurs (entry nums1 i hi) nums2.val) →
      vecAt r 0 = (slen nums1 : ℤ)) := by
  sorry

/-- Whenever find_intersection_values(nums1, nums2) returns a result r, if for every j with 0 <= j < len(nums2) there exists i with 0 <= i < len(nums1) and nums1[i] = nums2[j], then r[1] = len(nums2).
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 100, len(nums2) <= 100, for every i with 0 <= i < len(nums1) we have 1 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2) we have 1 <= nums2[j] <= 100. -/
theorem spec_7 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100) :
    ∀ r, find_intersection_values nums1 nums2 = ok r →
      (∀ (j : ℕ) (hj : j < slen nums2), Occurs (entry nums2 j hj) nums1.val) →
      vecAt r 1 = (slen nums2 : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100), ∀ r, find_intersection_values nums1 nums2 = ok r →
      (∀ (j : ℕ) (hj : j < slen nums2), Occurs (entry nums2 j hj) nums1.val) →
      vecAt r 1 = (slen nums2 : ℤ)) := by
  sorry

/-- Whenever find_intersection_values(nums1, nums2) returns a result r, the following three statements are equivalent: (a) there exist i and j with 0 <= i < len(nums1), 0 <= j < len(nums2), and nums1[i] = nums2[j]; (b) r[0] > 0; (c) r[1] > 0.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 100, len(nums2) <= 100, for every i with 0 <= i < len(nums1) we have 1 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2) we have 1 <= nums2[j] <= 100. -/
theorem spec_8 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100) :
    ∀ r, find_intersection_values nums1 nums2 = ok r →
      ((∃ (i : ℕ) (hi : i < slen nums1) (j : ℕ) (hj : j < slen nums2),
          entry nums1 i hi = entry nums2 j hj) ↔ vecAt r 0 > 0) ∧
        (vecAt r 0 > 0 ↔ vecAt r 1 > 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100), ∀ r, find_intersection_values nums1 nums2 = ok r →
      ((∃ (i : ℕ) (hi : i < slen nums1) (j : ℕ) (hj : j < slen nums2),
          entry nums1 i hi = entry nums2 j hj) ↔ vecAt r 0 > 0) ∧
        (vecAt r 0 > 0 ↔ vecAt r 1 > 0)) := by
  sorry

/-- Whenever find_intersection_values(nums1, nums2) returns a result r, for every integer v let c1(v) be the number of indices i with 0 <= i < len(nums1) and nums1[i] = v, and let c2(v) be the number of indices j with 0 <= j < len(nums2) and nums2[j] = v. Then r[0] = (sum over all integers v of c1(v) * (1 if c2(v) > 0 else 0)) and r[1] = (sum over all integers v of c2(v) * (1 if c1(v) > 0 else 0)).
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 100, len(nums2) <= 100, for every i with 0 <= i < len(nums1) we have 1 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2) we have 1 <= nums2[j] <= 100. -/
theorem spec_9 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100) :
    ∀ r, find_intersection_values nums1 nums2 = ok r →
      vecAt r 0 = countSum nums1.val nums2.val ∧
        vecAt r 1 = countSum nums2.val nums1.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100), ∀ r, find_intersection_values nums1 nums2 = ok r →
      vecAt r 0 = countSum nums1.val nums2.val ∧
        vecAt r 1 = countSum nums2.val nums1.val) := by
  sorry

/-- Whenever find_intersection_values(nums1, nums2) returns a result r and find_intersection_values(nums1', nums2') returns a result r', we have r[0] = r'[0] and r[1] = r'[1].
  Preconditions: nums1, nums2, nums1', and nums2' all satisfy the problem constraints: lengths are between 1 and 100 and all values are between 1 and 100. nums1' is a permutation of nums1 (same length and same multiset of values), and nums2' is a permutation of nums2. -/
theorem spec_10 (nums1 nums2 nums1' nums2' : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (h1lo' : 1 ≤ slen nums1') (h1hi' : slen nums1' ≤ 100)
    (h2lo' : 1 ≤ slen nums2') (h2hi' : slen nums2' ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100)
    (hv1' : ∀ (i : ℕ) (hi : i < slen nums1'), 1 ≤ entry nums1' i hi ∧ entry nums1' i hi ≤ 100)
    (hv2' : ∀ (j : ℕ) (hj : j < slen nums2'), 1 ≤ entry nums2' j hj ∧ entry nums2' j hj ≤ 100)
    (hp1 : List.Perm nums1.val nums1'.val) (hp2 : List.Perm nums2.val nums2'.val) :
    ∀ r r', find_intersection_values nums1 nums2 = ok r →
      find_intersection_values nums1' nums2' = ok r' →
      vecAt r 0 = vecAt r' 0 ∧ vecAt r 1 = vecAt r' 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums1 nums2 nums1' nums2' : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (h1lo' : 1 ≤ slen nums1') (h1hi' : slen nums1' ≤ 100)
    (h2lo' : 1 ≤ slen nums2') (h2hi' : slen nums2' ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100)
    (hv1' : ∀ (i : ℕ) (hi : i < slen nums1'), 1 ≤ entry nums1' i hi ∧ entry nums1' i hi ≤ 100)
    (hv2' : ∀ (j : ℕ) (hj : j < slen nums2'), 1 ≤ entry nums2' j hj ∧ entry nums2' j hj ≤ 100)
    (hp1 : List.Perm nums1.val nums1'.val) (hp2 : List.Perm nums2.val nums2'.val), ∀ r r', find_intersection_values nums1 nums2 = ok r →
      find_intersection_values nums1' nums2' = ok r' →
      vecAt r 0 = vecAt r' 0 ∧ vecAt r 1 = vecAt r' 1) := by
  sorry

/-- Whenever find_intersection_values(nums1, nums2) returns a result r and find_intersection_values(nums2, nums1) returns a result r', we have r[0] = r'[1] and r[1] = r'[0].
  Preconditions: nums1 and nums2 both satisfy the problem constraints: lengths are between 1 and 100 and all values are between 1 and 100. -/
theorem spec_11 (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100) :
    ∀ r r', find_intersection_values nums1 nums2 = ok r →
      find_intersection_values nums2 nums1 = ok r' →
      vecAt r 0 = vecAt r' 1 ∧ vecAt r 1 = vecAt r' 0 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100), ∀ r r', find_intersection_values nums1 nums2 = ok r →
      find_intersection_values nums2 nums1 = ok r' →
      vecAt r 0 = vecAt r' 1 ∧ vecAt r 1 = vecAt r' 0) := by
  sorry

/-- Whenever find_intersection_values(nums1, nums2) returns a result r and find_intersection_values(nums1, nums2') returns a result r', if nums2 and nums2' contain exactly the same set of values (for every integer v, v occurs in nums2 if and only if v occurs in nums2'), then r[0] = r'[0].
  Preconditions: nums1, nums2, and nums2' satisfy the problem constraints: lengths are between 1 and 100 and all values are between 1 and 100. -/
theorem spec_12 (nums1 nums2 nums2' : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (h2lo' : 1 ≤ slen nums2') (h2hi' : slen nums2' ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100)
    (hv2' : ∀ (j : ℕ) (hj : j < slen nums2'), 1 ≤ entry nums2' j hj ∧ entry nums2' j hj ≤ 100)
    (hset : ∀ v : ℤ, Occurs v nums2.val ↔ Occurs v nums2'.val) :
    ∀ r r', find_intersection_values nums1 nums2 = ok r →
      find_intersection_values nums1 nums2' = ok r' →
      vecAt r 0 = vecAt r' 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums1 nums2 nums2' : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (h2lo' : 1 ≤ slen nums2') (h2hi' : slen nums2' ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100)
    (hv2' : ∀ (j : ℕ) (hj : j < slen nums2'), 1 ≤ entry nums2' j hj ∧ entry nums2' j hj ≤ 100)
    (hset : ∀ v : ℤ, Occurs v nums2.val ↔ Occurs v nums2'.val), ∀ r r', find_intersection_values nums1 nums2 = ok r →
      find_intersection_values nums1 nums2' = ok r' →
      vecAt r 0 = vecAt r' 0) := by
  sorry

/-- Whenever find_intersection_values(nums1, nums2) returns a result r and find_intersection_values(nums1', nums2) returns a result r', if nums1 and nums1' contain exactly the same set of values (for every integer v, v occurs in nums1 if and only if v occurs in nums1'), then r[1] = r'[1].
  Preconditions: nums1, nums1', and nums2 satisfy the problem constraints: lengths are between 1 and 100 and all values are between 1 and 100. -/
theorem spec_13 (nums1 nums1' nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h1lo' : 1 ≤ slen nums1') (h1hi' : slen nums1' ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv1' : ∀ (i : ℕ) (hi : i < slen nums1'), 1 ≤ entry nums1' i hi ∧ entry nums1' i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100)
    (hset : ∀ v : ℤ, Occurs v nums1.val ↔ Occurs v nums1'.val) :
    ∀ r r', find_intersection_values nums1 nums2 = ok r →
      find_intersection_values nums1' nums2 = ok r' →
      vecAt r 1 = vecAt r' 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums1 nums1' nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h1lo' : 1 ≤ slen nums1') (h1hi' : slen nums1' ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv1' : ∀ (i : ℕ) (hi : i < slen nums1'), 1 ≤ entry nums1' i hi ∧ entry nums1' i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100)
    (hset : ∀ v : ℤ, Occurs v nums1.val ↔ Occurs v nums1'.val), ∀ r r', find_intersection_values nums1 nums2 = ok r →
      find_intersection_values nums1' nums2 = ok r' →
      vecAt r 1 = vecAt r' 1) := by
  sorry

/-- Whenever find_intersection_values(nums1, nums2) returns a result r and find_intersection_values(nums1, nums2') returns a result r', we have r'[0] >= r[0] and r'[1] = r[1] + (1 if there exists i with 0 <= i < len(nums1) and nums1[i] = c, else 0).
  Preconditions: nums1, nums2, and nums2' satisfy the problem constraints: lengths are between 1 and 100 and all values are between 1 and 100. There is an integer c with 1 <= c <= 100 such that nums2' is nums2 followed by c, so len(nums2') = len(nums2) + 1 <= 100. -/
theorem spec_14 (nums1 nums2 nums2' : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (h2lo' : 1 ≤ slen nums2') (h2hi' : slen nums2' ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100)
    (hv2' : ∀ (j : ℕ) (hj : j < slen nums2'), 1 ≤ entry nums2' j hj ∧ entry nums2' j hj ≤ 100)
    (c : Std.I64) (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100)
    (happend : nums2'.val = nums2.val ++ [c]) :
    ∀ r r', find_intersection_values nums1 nums2 = ok r →
      find_intersection_values nums1 nums2' = ok r' →
      vecAt r' 0 ≥ vecAt r 0 ∧
        vecAt r' 1 = vecAt r 1 + (if Occurs c.val nums1.val then 1 else 0) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums1 nums2 nums2' : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (h2lo' : 1 ≤ slen nums2') (h2hi' : slen nums2' ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100)
    (hv2' : ∀ (j : ℕ) (hj : j < slen nums2'), 1 ≤ entry nums2' j hj ∧ entry nums2' j hj ≤ 100)
    (c : Std.I64) (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100)
    (happend : nums2'.val = nums2.val ++ [c]), ∀ r r', find_intersection_values nums1 nums2 = ok r →
      find_intersection_values nums1 nums2' = ok r' →
      vecAt r' 0 ≥ vecAt r 0 ∧
        vecAt r' 1 = vecAt r 1 + (if Occurs c.val nums1.val then 1 else 0)) := by
  sorry

/-- Whenever find_intersection_values(nums1, nums2) returns a result r and find_intersection_values(nums1', nums2) returns a result r', we have r'[1] >= r[1] and r'[0] = r[0] + (1 if there exists j with 0 <= j < len(nums2) and nums2[j] = c, else 0).
  Preconditions: nums1, nums1', and nums2 satisfy the problem constraints: lengths are between 1 and 100 and all values are between 1 and 100. There is an integer c with 1 <= c <= 100 such that nums1' is nums1 followed by c, so len(nums1') = len(nums1) + 1 <= 100. -/
theorem spec_15 (nums1 nums1' nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h1lo' : 1 ≤ slen nums1') (h1hi' : slen nums1' ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv1' : ∀ (i : ℕ) (hi : i < slen nums1'), 1 ≤ entry nums1' i hi ∧ entry nums1' i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100)
    (c : Std.I64) (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100)
    (happend : nums1'.val = nums1.val ++ [c]) :
    ∀ r r', find_intersection_values nums1 nums2 = ok r →
      find_intersection_values nums1' nums2 = ok r' →
      vecAt r' 1 ≥ vecAt r 1 ∧
        vecAt r' 0 = vecAt r 0 + (if Occurs c.val nums2.val then 1 else 0) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums1 nums1' nums2 : Slice Std.I64)
    (h1lo : 1 ≤ slen nums1) (h1hi : slen nums1 ≤ 100)
    (h1lo' : 1 ≤ slen nums1') (h1hi' : slen nums1' ≤ 100)
    (h2lo : 1 ≤ slen nums2) (h2hi : slen nums2 ≤ 100)
    (hv1 : ∀ (i : ℕ) (hi : i < slen nums1), 1 ≤ entry nums1 i hi ∧ entry nums1 i hi ≤ 100)
    (hv1' : ∀ (i : ℕ) (hi : i < slen nums1'), 1 ≤ entry nums1' i hi ∧ entry nums1' i hi ≤ 100)
    (hv2 : ∀ (j : ℕ) (hj : j < slen nums2), 1 ≤ entry nums2 j hj ∧ entry nums2 j hj ≤ 100)
    (c : Std.I64) (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 100)
    (happend : nums1'.val = nums1.val ++ [c]), ∀ r r', find_intersection_values nums1 nums2 = ok r →
      find_intersection_values nums1' nums2 = ok r' →
      vecAt r' 1 ≥ vecAt r 1 ∧
        vecAt r' 0 = vecAt r 0 + (if Occurs c.val nums2.val then 1 else 0)) := by
  sorry

end AegisSpec.FindIntersectionValues
