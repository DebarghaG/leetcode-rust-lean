import Aegis.Intersect.Code.Funs

/-!
# Specifications of `Aegis.Intersect.intersect`

LeetCode problem `intersection-of-two-arrays-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.Intersect

  def cnt (xs : List Std.I64) (v : Int) : Nat :=
    xs.countP (fun x => x.val = v)

  def minCntSum (xs ys : List Std.I64) : Nat :=
    ∑ v ∈ Finset.range 1001, min (cnt xs (v : Int)) (cnt ys (v : Int))

  /-- Whenever intersect(nums1, nums2) returns a result r, for every integer v, cnt(r, v) = min(cnt(nums1, v), cnt(nums2, v)), where cnt(xs, v) is the number of indices k with 0 <= k < len(xs) and xs[k] = v.
    Preconditions: len(nums1) <= 1000, len(nums2) <= 1000, and for every index i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000; and for every index j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000. -/
  theorem spec_1 (nums1 nums2 : Slice Std.I64)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000)
      (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000)
      (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.Intersect.intersect nums1 nums2 = ok r) :
      ∀ v : Int, cnt r.val v = min (cnt nums1.val v) (cnt nums2.val v) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000)
        (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000)
        (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.Intersect.intersect nums1 nums2 = ok r), ∀ v : Int, cnt r.val v = min (cnt nums1.val v) (cnt nums2.val v)) := by
    sorry

  /-- For every nums1 and nums2 satisfying the preconditions, intersect(nums1, nums2) returns a result r; in other words, the function does not fail.
    Preconditions: len(nums1) <= 1000, len(nums2) <= 1000, and for every index i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000; and for every index j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000. -/
  theorem spec_2 (nums1 nums2 : Slice Std.I64)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000)
      (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000)
      (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.Intersect.intersect nums1 nums2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000)
        (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000)
        (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000), ∃ r : alloc.vec.Vec Std.I64, Aegis.Intersect.intersect nums1 nums2 = ok r) := by
    sorry

  /-- Whenever intersect(nums1, nums2) returns a result r, len(r) = sum over v = 0,1,...,1000 of min(cnt(nums1, v), cnt(nums2, v)), where cnt(xs, v) is the number of indices k with 0 <= k < len(xs) and xs[k] = v.
    Preconditions: len(nums1) <= 1000, len(nums2) <= 1000, and for every index i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000; and for every index j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000. -/
  theorem spec_3 (nums1 nums2 : Slice Std.I64)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000)
      (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000)
      (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.Intersect.intersect nums1 nums2 = ok r) :
      r.val.length = minCntSum nums1.val nums2.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000)
        (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000)
        (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.Intersect.intersect nums1 nums2 = ok r), r.val.length = minCntSum nums1.val nums2.val) := by
    sorry

  /-- Whenever intersect(nums1, nums2) returns a result r, for every integer v, cnt(r, v) <= cnt(nums1, v) and cnt(r, v) <= cnt(nums2, v), where cnt(xs, v) is the number of indices k with 0 <= k < len(xs) and xs[k] = v.
    Preconditions: len(nums1) <= 1000, len(nums2) <= 1000, and for every index i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000; and for every index j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000. -/
  theorem spec_4 (nums1 nums2 : Slice Std.I64)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000)
      (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000)
      (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.Intersect.intersect nums1 nums2 = ok r) :
      ∀ v : Int, cnt r.val v ≤ cnt nums1.val v ∧ cnt r.val v ≤ cnt nums2.val v := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000)
        (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000)
        (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.Intersect.intersect nums1 nums2 = ok r), ∀ v : Int, cnt r.val v ≤ cnt nums1.val v ∧ cnt r.val v ≤ cnt nums2.val v) := by
    sorry

  /-- Whenever intersect(nums1, nums2) returns a result r, for every integer v, if cnt(nums1, v) = 0 or cnt(nums2, v) = 0, then cnt(r, v) = 0, where cnt(xs, v) is the number of indices k with 0 <= k < len(xs) and xs[k] = v.
    Preconditions: len(nums1) <= 1000, len(nums2) <= 1000, and for every index i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000; and for every index j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000. -/
  theorem spec_5 (nums1 nums2 : Slice Std.I64)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000)
      (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000)
      (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.Intersect.intersect nums1 nums2 = ok r) :
      ∀ v : Int, (cnt nums1.val v = 0 ∨ cnt nums2.val v = 0) → cnt r.val v = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000)
        (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000)
        (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.Intersect.intersect nums1 nums2 = ok r), ∀ v : Int, (cnt nums1.val v = 0 ∨ cnt nums2.val v = 0) → cnt r.val v = 0) := by
    sorry

  /-- For all arrays nums1' and nums2' with the same multiplicities as nums1 and nums2 respectively (for every integer v, cnt(nums1', v) = cnt(nums1, v) and cnt(nums2', v) = cnt(nums2, v)), whenever intersect(nums1, nums2) returns r and intersect(nums1', nums2') returns r', it holds for every integer w that cnt(r, w) = cnt(r', w), where cnt(xs, v) is the number of indices k with 0 <= k < len(xs) and xs[k] = v.
    Preconditions: len(nums1) <= 1000, len(nums2) <= 1000, and for every index i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000; and for every index j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000. -/
  theorem spec_6 (nums1 nums2 : Slice Std.I64)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000)
      (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000)
      (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000)
      (nums1' nums2' : Slice Std.I64)
      (hc1 : ∀ v : Int, cnt nums1'.val v = cnt nums1.val v)
      (hc2 : ∀ v : Int, cnt nums2'.val v = cnt nums2.val v)
      (r r' : alloc.vec.Vec Std.I64)
      (hr : Aegis.Intersect.intersect nums1 nums2 = ok r)
      (hr' : Aegis.Intersect.intersect nums1' nums2' = ok r') :
      ∀ w : Int, cnt r.val w = cnt r'.val w := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000)
        (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000)
        (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000)
        (nums1' nums2' : Slice Std.I64)
        (hc1 : ∀ v : Int, cnt nums1'.val v = cnt nums1.val v)
        (hc2 : ∀ v : Int, cnt nums2'.val v = cnt nums2.val v)
        (r r' : alloc.vec.Vec Std.I64)
        (hr : Aegis.Intersect.intersect nums1 nums2 = ok r)
        (hr' : Aegis.Intersect.intersect nums1' nums2' = ok r'), ∀ w : Int, cnt r.val w = cnt r'.val w) := by
    sorry

  /-- Whenever intersect(nums1, nums2) returns a result r, for every integer v and every positive integer m, if cnt(nums1, v) >= m and cnt(nums2, v) >= m, then cnt(r, v) >= m, where cnt(xs, v) is the number of indices k with 0 <= k < len(xs) and xs[k] = v.
    Preconditions: len(nums1) <= 1000, len(nums2) <= 1000, and for every index i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000; and for every index j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000. -/
  theorem spec_7 (nums1 nums2 : Slice Std.I64)
      (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000)
      (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000)
      (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.Intersect.intersect nums1 nums2 = ok r) :
      ∀ (v : Int) (m : Nat), 0 < m →
        cnt nums1.val v ≥ m → cnt nums2.val v ≥ m → cnt r.val v ≥ m := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hlen1 : nums1.val.length ≤ 1000) (hlen2 : nums2.val.length ≤ 1000)
        (hb1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000)
        (hb2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.Intersect.intersect nums1 nums2 = ok r), ∀ (v : Int) (m : Nat), 0 < m →
          cnt nums1.val v ≥ m → cnt nums2.val v ≥ m → cnt r.val v ≥ m) := by
    sorry

  end AegisSpec.Intersect
