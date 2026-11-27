import Aegis.GetCommon.Code.Funs

/-!
# Specifications of `Aegis.GetCommon.get_common`

LeetCode problem `minimum-common-value`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetCommon

def OccursAt (nums : Slice Std.I64) (i : Nat) (x : Int) : Prop :=
  ∃ _h : i < nums.val.length, (nums.val[i]).val = x

def Occurs (nums : Slice Std.I64) (x : Int) : Prop :=
  ∃ i, OccursAt nums i x

def IsCommon (nums1 nums2 : Slice Std.I64) (x : Int) : Prop :=
  Occurs nums1 x ∧ Occurs nums2 x

def HasCommon (nums1 nums2 : Slice Std.I64) : Prop :=
  ∃ x, IsCommon nums1 nums2 x

def IsNonDecr (nums : Slice Std.I64) : Prop :=
  ∀ (i : Nat) (h : i + 1 < nums.val.length), (nums.val[i]).val ≤ (nums.val[i + 1]).val

def first (nums : Slice Std.I64) (h : 0 < nums.val.length) : Int :=
  (nums.val.get ⟨0, h⟩).val

def last (nums : Slice Std.I64) (h : 0 < nums.val.length) : Int :=
  (nums.val.get ⟨nums.val.length - 1, by omega⟩).val

/-- Whenever the function returns a result r, the following holds. Say an integer x is common to nums1 and nums2 iff there exist indices i and j with 0 <= i < len(nums1), 0 <= j < len(nums2), and nums1[i] = nums2[j] = x. If there exists at least one common integer, then r is common to nums1 and nums2, and for every integer x that is common to nums1 and nums2, r <= x. If there does not exist any common integer, then r = -1.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 1000000000, for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 1000000000, nums1 is non-decreasing (for every i with 0 <= i + 1 < len(nums1), nums1[i] <= nums1[i+1]), and nums2 is non-decreasing (for every j with 0 <= j + 1 < len(nums2), nums2[j] <= nums2[j+1]). -/
theorem spec_1 (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r) :
    (HasCommon nums1 nums2 →
        IsCommon nums1 nums2 r.val ∧ ∀ x : Int, IsCommon nums1 nums2 x → r.val ≤ x) ∧
      (¬ HasCommon nums1 nums2 → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r), (HasCommon nums1 nums2 →
        IsCommon nums1 nums2 r.val ∧ ∀ x : Int, IsCommon nums1 nums2 x → r.val ≤ x) ∧
      (¬ HasCommon nums1 nums2 → r.val = -1)) := by
  sorry

/-- The function returns a result r (it does not fail) for every nums1 and nums2 satisfying the preconditions.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 1000000000, for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 1000000000, nums1 is non-decreasing (for every i with 0 <= i + 1 < len(nums1), nums1[i] <= nums1[i+1]), and nums2 is non-decreasing (for every j with 0 <= j + 1 < len(nums2), nums2[j] <= nums2[j+1]). -/
theorem spec_2 (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2) :
    ∃ r : Std.I64, Aegis.GetCommon.get_common nums1 nums2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2), ∃ r : Std.I64, Aegis.GetCommon.get_common nums1 nums2 = ok r) := by
  sorry

/-- Whenever the function returns a result r, -1 <= r.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 1000000000, for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 1000000000, nums1 is non-decreasing (for every i with 0 <= i + 1 < len(nums1), nums1[i] <= nums1[i+1]), and nums2 is non-decreasing (for every j with 0 <= j + 1 < len(nums2), nums2[j] <= nums2[j+1]). -/
theorem spec_3 (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r) :
    -1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r), -1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= 1000000000.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 1000000000, for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 1000000000, nums1 is non-decreasing (for every i with 0 <= i + 1 < len(nums1), nums1[i] <= nums1[i+1]), and nums2 is non-decreasing (for every j with 0 <= j + 1 < len(nums2), nums2[j] <= nums2[j+1]). -/
theorem spec_4 (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r) :
    r.val ≤ 1000000000 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r), r.val ≤ 1000000000) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if it is not the case that there exist indices i and j with 0 <= i < len(nums1), 0 <= j < len(nums2), and nums1[i] = nums2[j].
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 1000000000, for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 1000000000, nums1 is non-decreasing (for every i with 0 <= i + 1 < len(nums1), nums1[i] <= nums1[i+1]), and nums2 is non-decreasing (for every j with 0 <= j + 1 < len(nums2), nums2[j] <= nums2[j+1]). -/
theorem spec_5 (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r) :
    (r.val = -1 ↔ ¬ HasCommon nums1 nums2) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r), (r.val = -1 ↔ ¬ HasCommon nums1 nums2)) := by
  sorry

/-- Whenever the function returns a result r and r != -1, there exist indices i and j such that 0 <= i < len(nums1), 0 <= j < len(nums2), nums1[i] = r, and nums2[j] = r.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 1000000000, for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 1000000000, nums1 is non-decreasing (for every i with 0 <= i + 1 < len(nums1), nums1[i] <= nums1[i+1]), and nums2 is non-decreasing (for every j with 0 <= j + 1 < len(nums2), nums2[j] <= nums2[j+1]). -/
theorem spec_6 (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r)
    (hrne : r.val ≠ -1) :
    ∃ (i : Nat) (_hi : i < nums1.val.length) (j : Nat) (_hj : j < nums2.val.length),
      (nums1.val[i]).val = r.val ∧ (nums2.val[j]).val = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r)
    (hrne : r.val ≠ -1), ∃ (i : Nat) (_hi : i < nums1.val.length) (j : Nat) (_hj : j < nums2.val.length),
      (nums1.val[i]).val = r.val ∧ (nums2.val[j]).val = r.val) := by
  sorry

/-- Whenever the function returns a result r and r != -1, for every integer x, if there exist indices i and j with 0 <= i < len(nums1), 0 <= j < len(nums2), nums1[i] = x, and nums2[j] = x, then r <= x.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 1000000000, for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 1000000000, nums1 is non-decreasing (for every i with 0 <= i + 1 < len(nums1), nums1[i] <= nums1[i+1]), and nums2 is non-decreasing (for every j with 0 <= j + 1 < len(nums2), nums2[j] <= nums2[j+1]). -/
theorem spec_7 (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r)
    (hrne : r.val ≠ -1) :
    ∀ x : Int, IsCommon nums1 nums2 x → r.val ≤ x := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r)
    (hrne : r.val ≠ -1), ∀ x : Int, IsCommon nums1 nums2 x → r.val ≤ x) := by
  sorry

/-- Whenever the function returns a result r, let i be the least index such that 0 <= i < len(nums1) and there exists j with 0 <= j < len(nums2) and nums2[j] = nums1[i]; then r = nums1[i].
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 1000000000, for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 1000000000, nums1 is non-decreasing (for every i with 0 <= i + 1 < len(nums1), nums1[i] <= nums1[i+1]), nums2 is non-decreasing (for every j with 0 <= j + 1 < len(nums2), nums2[j] <= nums2[j+1]), and there exists at least one common integer: there exist indices i and j with 0 <= i < len(nums1), 0 <= j < len(nums2), and nums1[i] = nums2[j]. -/
theorem spec_8 (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (hcommon : HasCommon nums1 nums2)
    (i : Nat) (hi : i < nums1.val.length)
    (hocc : Occurs nums2 (nums1.val[i]).val)
    (hleast : ∀ (i' : Nat) (hi' : i' < nums1.val.length), i' < i →
      ¬ Occurs nums2 (nums1.val[i']).val)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r) :
    r.val = (nums1.val[i]).val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (hcommon : HasCommon nums1 nums2)
    (i : Nat) (hi : i < nums1.val.length)
    (hocc : Occurs nums2 (nums1.val[i]).val)
    (hleast : ∀ (i' : Nat) (hi' : i' < nums1.val.length), i' < i →
      ¬ Occurs nums2 (nums1.val[i']).val)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r), r.val = (nums1.val[i]).val) := by
  sorry

/-- Whenever the function returns a result r, let j be the least index such that 0 <= j < len(nums2) and there exists i with 0 <= i < len(nums1) and nums1[i] = nums2[j]; then r = nums2[j].
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 1000000000, for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 1000000000, nums1 is non-decreasing (for every i with 0 <= i + 1 < len(nums1), nums1[i] <= nums1[i+1]), nums2 is non-decreasing (for every j with 0 <= j + 1 < len(nums2), nums2[j] <= nums2[j+1]), and there exists at least one common integer: there exist indices i and j with 0 <= i < len(nums1), 0 <= j < len(nums2), and nums1[i] = nums2[j]. -/
theorem spec_9 (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (hcommon : HasCommon nums1 nums2)
    (j : Nat) (hj : j < nums2.val.length)
    (hocc : Occurs nums1 (nums2.val[j]).val)
    (hleast : ∀ (j' : Nat) (hj' : j' < nums2.val.length), j' < j →
      ¬ Occurs nums1 (nums2.val[j']).val)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r) :
    r.val = (nums2.val[j]).val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (hcommon : HasCommon nums1 nums2)
    (j : Nat) (hj : j < nums2.val.length)
    (hocc : Occurs nums1 (nums2.val[j]).val)
    (hleast : ∀ (j' : Nat) (hj' : j' < nums2.val.length), j' < j →
      ¬ Occurs nums1 (nums2.val[j']).val)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r), r.val = (nums2.val[j]).val) := by
  sorry

/-- Whenever the function returns a result r, if nums1[0] = nums2[0] then r = nums1[0], and otherwise r = -1.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 1000000000, for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 1000000000, nums1 is non-decreasing (for every i with 0 <= i + 1 < len(nums1), nums1[i] <= nums1[i+1]), nums2 is non-decreasing (for every j with 0 <= j + 1 < len(nums2), nums2[j] <= nums2[j+1]), len(nums1) = 1, and len(nums2) = 1. -/
theorem spec_10 (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (hlen1 : nums1.val.length = 1) (hlen2 : nums2.val.length = 1)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r) :
    (first nums1 h1 = first nums2 h2 → r.val = first nums1 h1) ∧
      (first nums1 h1 ≠ first nums2 h2 → r.val = -1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (hlen1 : nums1.val.length = 1) (hlen2 : nums2.val.length = 1)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r), (first nums1 h1 = first nums2 h2 → r.val = first nums1 h1) ∧
      (first nums1 h1 ≠ first nums2 h2 → r.val = -1)) := by
  sorry

/-- Whenever the function returns a result r, r = nums1[0].
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 1000000000, for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 1000000000, nums1 is non-decreasing (for every i with 0 <= i + 1 < len(nums1), nums1[i] <= nums1[i+1]), nums2 is non-decreasing (for every j with 0 <= j + 1 < len(nums2), nums2[j] <= nums2[j+1]), and nums1[0] = nums2[0]. -/
theorem spec_11 (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (hhead : first nums1 h1 = first nums2 h2)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r) :
    r.val = first nums1 h1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (hhead : first nums1 h1 = first nums2 h2)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r), r.val = first nums1 h1) := by
  sorry

/-- Whenever the function returns a result r, r = -1.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 1000000000, for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 1000000000, nums1 is non-decreasing (for every i with 0 <= i + 1 < len(nums1), nums1[i] <= nums1[i+1]), nums2 is non-decreasing (for every j with 0 <= j + 1 < len(nums2), nums2[j] <= nums2[j+1]), and nums1[len(nums1)-1] < nums2[0]. -/
theorem spec_12 (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (hsep : last nums1 h1 < first nums2 h2)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r) :
    r.val = -1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (hsep : last nums1 h1 < first nums2 h2)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r), r.val = -1) := by
  sorry

/-- Whenever the function returns a result r and r != -1, r >= nums1[0] and r >= nums2[0].
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 1000000000, for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 1000000000, nums1 is non-decreasing (for every i with 0 <= i + 1 < len(nums1), nums1[i] <= nums1[i+1]), and nums2 is non-decreasing (for every j with 0 <= j + 1 < len(nums2), nums2[j] <= nums2[j+1]). -/
theorem spec_13 (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r)
    (hrne : r.val ≠ -1) :
    first nums1 h1 ≤ r.val ∧ first nums2 h2 ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (r : Std.I64) (hr : Aegis.GetCommon.get_common nums1 nums2 = ok r)
    (hrne : r.val ≠ -1), first nums1 h1 ≤ r.val ∧ first nums2 h2 ≤ r.val) := by
  sorry

/-- For every nums1 and nums2 satisfying the preconditions, if the call get_common nums1 nums2 returns a result r1 and the call get_common nums2 nums1 returns a result r2, then r1 = r2.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 1000000000, for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 1000000000, nums1 is non-decreasing (for every i with 0 <= i + 1 < len(nums1), nums1[i] <= nums1[i+1]), and nums2 is non-decreasing (for every j with 0 <= j + 1 < len(nums2), nums2[j] <= nums2[j+1]). -/
theorem spec_14 (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (r1 r2 : Std.I64)
    (hr1 : Aegis.GetCommon.get_common nums1 nums2 = ok r1)
    (hr2 : Aegis.GetCommon.get_common nums2 nums1 = ok r2) :
    r1 = r2 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1 : 1 ≤ nums1.val.length) (h2 : 1 ≤ nums2.val.length)
    (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
      1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
    (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
      1 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
    (hs1 : IsNonDecr nums1) (hs2 : IsNonDecr nums2)
    (r1 r2 : Std.I64)
    (hr1 : Aegis.GetCommon.get_common nums1 nums2 = ok r1)
    (hr2 : Aegis.GetCommon.get_common nums2 nums1 = ok r2), r1 = r2) := by
  sorry

end AegisSpec.GetCommon
