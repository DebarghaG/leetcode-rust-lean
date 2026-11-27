import Aegis.Intersection.Code.Funs

/-!
# Specifications of `Aegis.Intersection.intersection`

LeetCode problem `intersection-of-two-arrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.Intersection

  def Occurs (l : List Aeneas.Std.I64) (v : ℤ) : Prop :=
    ∃ (i : Nat) (h : i < l.length), (l[i]'h).val = v

  def AllInRange (l : List Aeneas.Std.I64) (lo hi : ℤ) : Prop :=
    ∀ (i : Nat) (h : i < l.length), lo ≤ (l[i]'h).val ∧ (l[i]'h).val ≤ hi

  /-- Whenever the function returns a result r, for every integer v, v occurs in r if and only if both (there exists i with 0 <= i < len(nums1) and nums1[i] = v) and (there exists j with 0 <= j < len(nums2) and nums2[j] = v); moreover, r has no repeated entries: for every i and j with 0 <= i < len(r) and 0 <= j < len(r), if r[i] = r[j] then i = j.
    Preconditions: 1 <= len(nums1) <= 1000, 1 <= len(nums2) <= 1000, for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000, and for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000. -/
  theorem spec_1 (nums1 nums2 : Slice Aeneas.Std.I64)
      (h1_ge : 1 ≤ (Slice.len nums1).val) (h1_le : (Slice.len nums1).val ≤ 1000)
      (h2_ge : 1 ≤ (Slice.len nums2).val) (h2_le : (Slice.len nums2).val ≤ 1000)
      (h1_range : AllInRange nums1.val 0 1000)
      (h2_range : AllInRange nums2.val 0 1000) :
      ∀ (r : alloc.vec.Vec Aeneas.Std.I64),
        Aegis.Intersection.intersection nums1 nums2 = ok r →
        (∀ (v : ℤ), Occurs r.val v ↔ (Occurs nums1.val v ∧ Occurs nums2.val v)) ∧
        (∀ (i j : Nat) (hi : i < r.val.length) (hj : j < r.val.length),
          (r.val[i]'hi).val = (r.val[j]'hj).val → i = j) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums1 nums2 : Slice Aeneas.Std.I64)
        (h1_ge : 1 ≤ (Slice.len nums1).val) (h1_le : (Slice.len nums1).val ≤ 1000)
        (h2_ge : 1 ≤ (Slice.len nums2).val) (h2_le : (Slice.len nums2).val ≤ 1000)
        (h1_range : AllInRange nums1.val 0 1000)
        (h2_range : AllInRange nums2.val 0 1000), ∀ (r : alloc.vec.Vec Aeneas.Std.I64),
          Aegis.Intersection.intersection nums1 nums2 = ok r →
          (∀ (v : ℤ), Occurs r.val v ↔ (Occurs nums1.val v ∧ Occurs nums2.val v)) ∧
          (∀ (i j : Nat) (hi : i < r.val.length) (hj : j < r.val.length),
            (r.val[i]'hi).val = (r.val[j]'hj).val → i = j)) := by
    sorry

  /-- The function returns a result r and does not fail.
    Preconditions: 1 <= len(nums1) <= 1000, 1 <= len(nums2) <= 1000, for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000, and for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000. -/
  theorem spec_2 (nums1 nums2 : Slice Aeneas.Std.I64)
      (h1_ge : 1 ≤ (Slice.len nums1).val) (h1_le : (Slice.len nums1).val ≤ 1000)
      (h2_ge : 1 ≤ (Slice.len nums2).val) (h2_le : (Slice.len nums2).val ≤ 1000)
      (h1_range : AllInRange nums1.val 0 1000)
      (h2_range : AllInRange nums2.val 0 1000) :
      ∃ (r : alloc.vec.Vec Aeneas.Std.I64), Aegis.Intersection.intersection nums1 nums2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums1 nums2 : Slice Aeneas.Std.I64)
        (h1_ge : 1 ≤ (Slice.len nums1).val) (h1_le : (Slice.len nums1).val ≤ 1000)
        (h2_ge : 1 ≤ (Slice.len nums2).val) (h2_le : (Slice.len nums2).val ≤ 1000)
        (h1_range : AllInRange nums1.val 0 1000)
        (h2_range : AllInRange nums2.val 0 1000), ∃ (r : alloc.vec.Vec Aeneas.Std.I64), Aegis.Intersection.intersection nums1 nums2 = ok r) := by
    sorry

  end AegisSpec.Intersection
