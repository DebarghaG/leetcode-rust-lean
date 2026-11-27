import Aegis.CheckOverlap.Code.Funs
import Mathlib

/-!
# Specifications of `Aegis.CheckOverlap.check_overlap`

LeetCode problem `circle-and-rectangle-overlapping`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CheckOverlap

def inClosedRect (x1 y1 x2 y2 : ℤ) (px py : ℝ) : Prop :=
  (x1 : ℝ) ≤ px ∧ px ≤ (x2 : ℝ) ∧ (y1 : ℝ) ≤ py ∧ py ≤ (y2 : ℝ)

def inClosedDisk (cx cy radius : ℤ) (px py : ℝ) : Prop :=
  (px - (cx : ℝ)) ^ 2 + (py - (cy : ℝ)) ^ 2 ≤ (radius : ℝ) ^ 2

def inClosedRectInt (x1 y1 x2 y2 px py : ℤ) : Prop :=
  x1 ≤ px ∧ px ≤ x2 ∧ y1 ≤ py ∧ py ≤ y2

def inClosedDiskInt (cx cy radius px py : ℤ) : Prop :=
  (px - cx) ^ 2 + (py - cy) ^ 2 ≤ radius ^ 2

def i64OfInt (n : ℤ) : Std.I64 := ⟨BitVec.ofInt 64 n⟩

/-- For every such input, check_overlap returns a result r (it does not fail), and r = true if and only if there exist real numbers px and py such that x1 <= px <= x2, y1 <= py <= y2, and (px - xCenter)^2 + (py - yCenter)^2 <= radius^2. Equivalently, r = false if and only if no point of the closed rectangle [x1,x2] x [y1,y2] lies in the closed disk of radius radius centered at (xCenter,yCenter).
  Preconditions: radius, xCenter, yCenter, x1, y1, x2, y2 are mathematical integers satisfying 1 <= radius <= 2000, -10000 <= xCenter <= 10000, -10000 <= yCenter <= 10000, -10000 <= x1 < x2 <= 10000, and -10000 <= y1 < y2 <= 10000. -/
theorem spec_1
    (radius xCenter yCenter x1 y1 x2 y2 : Std.I64)
    (hradius_lower : 1 ≤ radius.val) (hradius_upper : radius.val ≤ 2000)
    (hxCenter_lower : -10000 ≤ xCenter.val) (hxCenter_upper : xCenter.val ≤ 10000)
    (hyCenter_lower : -10000 ≤ yCenter.val) (hyCenter_upper : yCenter.val ≤ 10000)
    (hx1_lower : -10000 ≤ x1.val) (hxlt : x1.val < x2.val) (hx2_upper : x2.val ≤ 10000)
    (hy1_lower : -10000 ≤ y1.val) (hylt : y1.val < y2.val) (hy2_upper : y2.val ≤ 10000) :
    ∃ r, Aegis.CheckOverlap.check_overlap radius xCenter yCenter x1 y1 x2 y2 = ok r ∧
      (r = true ↔ ∃ px py : ℝ,
        inClosedRect x1.val y1.val x2.val y2.val px py ∧
        inClosedDisk xCenter.val yCenter.val radius.val px py) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (radius xCenter yCenter x1 y1 x2 y2 : Std.I64)
    (hradius_lower : 1 ≤ radius.val) (hradius_upper : radius.val ≤ 2000)
    (hxCenter_lower : -10000 ≤ xCenter.val) (hxCenter_upper : xCenter.val ≤ 10000)
    (hyCenter_lower : -10000 ≤ yCenter.val) (hyCenter_upper : yCenter.val ≤ 10000)
    (hx1_lower : -10000 ≤ x1.val) (hxlt : x1.val < x2.val) (hx2_upper : x2.val ≤ 10000)
    (hy1_lower : -10000 ≤ y1.val) (hylt : y1.val < y2.val) (hy2_upper : y2.val ≤ 10000), ∃ r, Aegis.CheckOverlap.check_overlap radius xCenter yCenter x1 y1 x2 y2 = ok r ∧
      (r = true ↔ ∃ px py : ℝ,
        inClosedRect x1.val y1.val x2.val y2.val px py ∧
        inClosedDisk xCenter.val yCenter.val radius.val px py)) := by
  sorry

/-- For every such input, check_overlap returns a Result Bool; in particular, it does not overflow, panic, or otherwise fail.
  Preconditions: radius, xCenter, yCenter, x1, y1, x2, y2 are mathematical integers satisfying 1 <= radius <= 2000, -10000 <= xCenter <= 10000, -10000 <= yCenter <= 10000, -10000 <= x1 < x2 <= 10000, and -10000 <= y1 < y2 <= 10000. -/
theorem spec_2
    (radius xCenter yCenter x1 y1 x2 y2 : Std.I64)
    (hradius_lower : 1 ≤ radius.val) (hradius_upper : radius.val ≤ 2000)
    (hxCenter_lower : -10000 ≤ xCenter.val) (hxCenter_upper : xCenter.val ≤ 10000)
    (hyCenter_lower : -10000 ≤ yCenter.val) (hyCenter_upper : yCenter.val ≤ 10000)
    (hx1_lower : -10000 ≤ x1.val) (hxlt : x1.val < x2.val) (hx2_upper : x2.val ≤ 10000)
    (hy1_lower : -10000 ≤ y1.val) (hylt : y1.val < y2.val) (hy2_upper : y2.val ≤ 10000) :
    ∃ r, Aegis.CheckOverlap.check_overlap radius xCenter yCenter x1 y1 x2 y2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (radius xCenter yCenter x1 y1 x2 y2 : Std.I64)
    (hradius_lower : 1 ≤ radius.val) (hradius_upper : radius.val ≤ 2000)
    (hxCenter_lower : -10000 ≤ xCenter.val) (hxCenter_upper : xCenter.val ≤ 10000)
    (hyCenter_lower : -10000 ≤ yCenter.val) (hyCenter_upper : yCenter.val ≤ 10000)
    (hx1_lower : -10000 ≤ x1.val) (hxlt : x1.val < x2.val) (hx2_upper : x2.val ≤ 10000)
    (hy1_lower : -10000 ≤ y1.val) (hylt : y1.val < y2.val) (hy2_upper : y2.val ≤ 10000), ∃ r, Aegis.CheckOverlap.check_overlap radius xCenter yCenter x1 y1 x2 y2 = ok r) := by
  sorry

/-- For every such input, whenever check_overlap returns a result r with r = true, there exist integers px and py such that x1 <= px <= x2, y1 <= py <= y2, and (px - xCenter)^2 + (py - yCenter)^2 <= radius^2.
  Preconditions: radius, xCenter, yCenter, x1, y1, x2, y2 are mathematical integers satisfying 1 <= radius <= 2000, -10000 <= xCenter <= 10000, -10000 <= yCenter <= 10000, -10000 <= x1 < x2 <= 10000, and -10000 <= y1 < y2 <= 10000. -/
theorem spec_3
    (radius xCenter yCenter x1 y1 x2 y2 : Std.I64)
    (hradius_lower : 1 ≤ radius.val) (hradius_upper : radius.val ≤ 2000)
    (hxCenter_lower : -10000 ≤ xCenter.val) (hxCenter_upper : xCenter.val ≤ 10000)
    (hyCenter_lower : -10000 ≤ yCenter.val) (hyCenter_upper : yCenter.val ≤ 10000)
    (hx1_lower : -10000 ≤ x1.val) (hxlt : x1.val < x2.val) (hx2_upper : x2.val ≤ 10000)
    (hy1_lower : -10000 ≤ y1.val) (hylt : y1.val < y2.val) (hy2_upper : y2.val ≤ 10000)
    (r : Bool)
    (hres : Aegis.CheckOverlap.check_overlap radius xCenter yCenter x1 y1 x2 y2 = ok r)
    (hr : r = true) :
    ∃ px py : ℤ,
      inClosedRectInt x1.val y1.val x2.val y2.val px py ∧
      inClosedDiskInt xCenter.val yCenter.val radius.val px py := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (radius xCenter yCenter x1 y1 x2 y2 : Std.I64)
    (hradius_lower : 1 ≤ radius.val) (hradius_upper : radius.val ≤ 2000)
    (hxCenter_lower : -10000 ≤ xCenter.val) (hxCenter_upper : xCenter.val ≤ 10000)
    (hyCenter_lower : -10000 ≤ yCenter.val) (hyCenter_upper : yCenter.val ≤ 10000)
    (hx1_lower : -10000 ≤ x1.val) (hxlt : x1.val < x2.val) (hx2_upper : x2.val ≤ 10000)
    (hy1_lower : -10000 ≤ y1.val) (hylt : y1.val < y2.val) (hy2_upper : y2.val ≤ 10000)
    (r : Bool)
    (hres : Aegis.CheckOverlap.check_overlap radius xCenter yCenter x1 y1 x2 y2 = ok r)
    (hr : r = true), ∃ px py : ℤ,
      inClosedRectInt x1.val y1.val x2.val y2.val px py ∧
      inClosedDiskInt xCenter.val yCenter.val radius.val px py) := by
  sorry

/-- Whenever check_overlap radius xCenter yCenter x1 y1 x2 y2 returns a result r and check_overlap R xCenter yCenter x1 y1 x2 y2 returns a result rR, if r = true then rR = true.
  Preconditions: radius, xCenter, yCenter, x1, y1, x2, y2 are mathematical integers satisfying 1 <= radius <= 2000, -10000 <= xCenter <= 10000, -10000 <= yCenter <= 10000, -10000 <= x1 < x2 <= 10000, and -10000 <= y1 < y2 <= 10000. Let R be an integer with radius <= R <= 2000. -/
theorem spec_4
    (radius R xCenter yCenter x1 y1 x2 y2 : Std.I64)
    (hradius_lower : 1 ≤ radius.val) (hradius_upper : radius.val ≤ 2000)
    (hR_lower : radius.val ≤ R.val) (hR_upper : R.val ≤ 2000)
    (hxCenter_lower : -10000 ≤ xCenter.val) (hxCenter_upper : xCenter.val ≤ 10000)
    (hyCenter_lower : -10000 ≤ yCenter.val) (hyCenter_upper : yCenter.val ≤ 10000)
    (hx1_lower : -10000 ≤ x1.val) (hxlt : x1.val < x2.val) (hx2_upper : x2.val ≤ 10000)
    (hy1_lower : -10000 ≤ y1.val) (hylt : y1.val < y2.val) (hy2_upper : y2.val ≤ 10000)
    (r rR : Bool)
    (hres : Aegis.CheckOverlap.check_overlap radius xCenter yCenter x1 y1 x2 y2 = ok r)
    (hresR : Aegis.CheckOverlap.check_overlap R xCenter yCenter x1 y1 x2 y2 = ok rR)
    (hr : r = true) :
    rR = true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (radius R xCenter yCenter x1 y1 x2 y2 : Std.I64)
    (hradius_lower : 1 ≤ radius.val) (hradius_upper : radius.val ≤ 2000)
    (hR_lower : radius.val ≤ R.val) (hR_upper : R.val ≤ 2000)
    (hxCenter_lower : -10000 ≤ xCenter.val) (hxCenter_upper : xCenter.val ≤ 10000)
    (hyCenter_lower : -10000 ≤ yCenter.val) (hyCenter_upper : yCenter.val ≤ 10000)
    (hx1_lower : -10000 ≤ x1.val) (hxlt : x1.val < x2.val) (hx2_upper : x2.val ≤ 10000)
    (hy1_lower : -10000 ≤ y1.val) (hylt : y1.val < y2.val) (hy2_upper : y2.val ≤ 10000)
    (r rR : Bool)
    (hres : Aegis.CheckOverlap.check_overlap radius xCenter yCenter x1 y1 x2 y2 = ok r)
    (hresR : Aegis.CheckOverlap.check_overlap R xCenter yCenter x1 y1 x2 y2 = ok rR)
    (hr : r = true), rR = true) := by
  sorry

/-- Whenever check_overlap radius xCenter yCenter x1 y1 x2 y2 returns a result r and check_overlap radius xCenter yCenter x1' y1' x2' y2' returns a result r', if r = true then r' = true.
  Preconditions: radius, xCenter, yCenter, x1, y1, x2, y2 are mathematical integers satisfying 1 <= radius <= 2000, -10000 <= xCenter <= 10000, -10000 <= yCenter <= 10000, -10000 <= x1 < x2 <= 10000, and -10000 <= y1 < y2 <= 10000. Let x1', y1', x2', y2' be integers satisfying -10000 <= x1' < x2' <= 10000, -10000 <= y1' < y2' <= 10000, x1' <= x1, y1' <= y1, x2' >= x2, and y2' >= y2. -/
theorem spec_5
    (radius xCenter yCenter x1 y1 x2 y2 x1' y1' x2' y2' : Std.I64)
    (hradius_lower : 1 ≤ radius.val) (hradius_upper : radius.val ≤ 2000)
    (hxCenter_lower : -10000 ≤ xCenter.val) (hxCenter_upper : xCenter.val ≤ 10000)
    (hyCenter_lower : -10000 ≤ yCenter.val) (hyCenter_upper : yCenter.val ≤ 10000)
    (hx1_lower : -10000 ≤ x1.val) (hxlt : x1.val < x2.val) (hx2_upper : x2.val ≤ 10000)
    (hy1_lower : -10000 ≤ y1.val) (hylt : y1.val < y2.val) (hy2_upper : y2.val ≤ 10000)
    (hx1'_lower : -10000 ≤ x1'.val) (hxlt' : x1'.val < x2'.val) (hx2'_upper : x2'.val ≤ 10000)
    (hy1'_lower : -10000 ≤ y1'.val) (hylt' : y1'.val < y2'.val) (hy2'_upper : y2'.val ≤ 10000)
    (hx1'_le : x1'.val ≤ x1.val) (hy1'_le : y1'.val ≤ y1.val)
    (hx2'_ge : x2.val ≤ x2'.val) (hy2'_ge : y2.val ≤ y2'.val)
    (r r' : Bool)
    (hres : Aegis.CheckOverlap.check_overlap radius xCenter yCenter x1 y1 x2 y2 = ok r)
    (hres' : Aegis.CheckOverlap.check_overlap radius xCenter yCenter x1' y1' x2' y2' = ok r')
    (hr : r = true) :
    r' = true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (radius xCenter yCenter x1 y1 x2 y2 x1' y1' x2' y2' : Std.I64)
    (hradius_lower : 1 ≤ radius.val) (hradius_upper : radius.val ≤ 2000)
    (hxCenter_lower : -10000 ≤ xCenter.val) (hxCenter_upper : xCenter.val ≤ 10000)
    (hyCenter_lower : -10000 ≤ yCenter.val) (hyCenter_upper : yCenter.val ≤ 10000)
    (hx1_lower : -10000 ≤ x1.val) (hxlt : x1.val < x2.val) (hx2_upper : x2.val ≤ 10000)
    (hy1_lower : -10000 ≤ y1.val) (hylt : y1.val < y2.val) (hy2_upper : y2.val ≤ 10000)
    (hx1'_lower : -10000 ≤ x1'.val) (hxlt' : x1'.val < x2'.val) (hx2'_upper : x2'.val ≤ 10000)
    (hy1'_lower : -10000 ≤ y1'.val) (hylt' : y1'.val < y2'.val) (hy2'_upper : y2'.val ≤ 10000)
    (hx1'_le : x1'.val ≤ x1.val) (hy1'_le : y1'.val ≤ y1.val)
    (hx2'_ge : x2.val ≤ x2'.val) (hy2'_ge : y2.val ≤ y2'.val)
    (r r' : Bool)
    (hres : Aegis.CheckOverlap.check_overlap radius xCenter yCenter x1 y1 x2 y2 = ok r)
    (hres' : Aegis.CheckOverlap.check_overlap radius xCenter yCenter x1' y1' x2' y2' = ok r')
    (hr : r = true), r' = true) := by
  sorry

/-- Whenever check_overlap radius xCenter yCenter x1 y1 x2 y2 returns a result r and check_overlap radius (xCenter+tx) (yCenter+ty) (x1+tx) (y1+ty) (x2+tx) (y2+ty) returns a result r', r = r'.
  Preconditions: radius, xCenter, yCenter, x1, y1, x2, y2 are mathematical integers satisfying 1 <= radius <= 2000, -10000 <= xCenter <= 10000, -10000 <= yCenter <= 10000, -10000 <= x1 < x2 <= 10000, and -10000 <= y1 < y2 <= 10000. Let tx and ty be integers such that -10000 <= xCenter+tx <= 10000, -10000 <= yCenter+ty <= 10000, -10000 <= x1+tx < x2+tx <= 10000, and -10000 <= y1+ty < y2+ty <= 10000. -/
theorem spec_6
    (radius xCenter yCenter x1 y1 x2 y2 : Std.I64) (tx ty : ℤ)
    (hradius_lower : 1 ≤ radius.val) (hradius_upper : radius.val ≤ 2000)
    (hxCenter_lower : -10000 ≤ xCenter.val) (hxCenter_upper : xCenter.val ≤ 10000)
    (hyCenter_lower : -10000 ≤ yCenter.val) (hyCenter_upper : yCenter.val ≤ 10000)
    (hx1_lower : -10000 ≤ x1.val) (hxlt : x1.val < x2.val) (hx2_upper : x2.val ≤ 10000)
    (hy1_lower : -10000 ≤ y1.val) (hylt : y1.val < y2.val) (hy2_upper : y2.val ≤ 10000)
    (hxCenter'_lower : -10000 ≤ xCenter.val + tx) (hxCenter'_upper : xCenter.val + tx ≤ 10000)
    (hyCenter'_lower : -10000 ≤ yCenter.val + ty) (hyCenter'_upper : yCenter.val + ty ≤ 10000)
    (hx1'_lower : -10000 ≤ x1.val + tx) (hxlt' : x1.val + tx < x2.val + tx)
    (hx2'_upper : x2.val + tx ≤ 10000)
    (hy1'_lower : -10000 ≤ y1.val + ty) (hylt' : y1.val + ty < y2.val + ty)
    (hy2'_upper : y2.val + ty ≤ 10000)
    (r r' : Bool)
    (hres : Aegis.CheckOverlap.check_overlap radius xCenter yCenter x1 y1 x2 y2 = ok r)
    (hres' : Aegis.CheckOverlap.check_overlap radius
        (i64OfInt (xCenter.val + tx)) (i64OfInt (yCenter.val + ty))
        (i64OfInt (x1.val + tx)) (i64OfInt (y1.val + ty))
        (i64OfInt (x2.val + tx)) (i64OfInt (y2.val + ty)) = ok r') :
    r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (radius xCenter yCenter x1 y1 x2 y2 : Std.I64) (tx ty : ℤ)
    (hradius_lower : 1 ≤ radius.val) (hradius_upper : radius.val ≤ 2000)
    (hxCenter_lower : -10000 ≤ xCenter.val) (hxCenter_upper : xCenter.val ≤ 10000)
    (hyCenter_lower : -10000 ≤ yCenter.val) (hyCenter_upper : yCenter.val ≤ 10000)
    (hx1_lower : -10000 ≤ x1.val) (hxlt : x1.val < x2.val) (hx2_upper : x2.val ≤ 10000)
    (hy1_lower : -10000 ≤ y1.val) (hylt : y1.val < y2.val) (hy2_upper : y2.val ≤ 10000)
    (hxCenter'_lower : -10000 ≤ xCenter.val + tx) (hxCenter'_upper : xCenter.val + tx ≤ 10000)
    (hyCenter'_lower : -10000 ≤ yCenter.val + ty) (hyCenter'_upper : yCenter.val + ty ≤ 10000)
    (hx1'_lower : -10000 ≤ x1.val + tx) (hxlt' : x1.val + tx < x2.val + tx)
    (hx2'_upper : x2.val + tx ≤ 10000)
    (hy1'_lower : -10000 ≤ y1.val + ty) (hylt' : y1.val + ty < y2.val + ty)
    (hy2'_upper : y2.val + ty ≤ 10000)
    (r r' : Bool)
    (hres : Aegis.CheckOverlap.check_overlap radius xCenter yCenter x1 y1 x2 y2 = ok r)
    (hres' : Aegis.CheckOverlap.check_overlap radius
        (i64OfInt (xCenter.val + tx)) (i64OfInt (yCenter.val + ty))
        (i64OfInt (x1.val + tx)) (i64OfInt (y1.val + ty))
        (i64OfInt (x2.val + tx)) (i64OfInt (y2.val + ty)) = ok r'), r = r') := by
  sorry

/-- Whenever check_overlap radius xCenter yCenter x1 y1 x2 y2 returns a result r and check_overlap radius (-xCenter) yCenter (-x2) y1 (-x1) y2 returns a result r', r = r'.
  Preconditions: radius, xCenter, yCenter, x1, y1, x2, y2 are mathematical integers satisfying 1 <= radius <= 2000, -10000 <= xCenter <= 10000, -10000 <= yCenter <= 10000, -10000 <= x1 < x2 <= 10000, and -10000 <= y1 < y2 <= 10000. -/
theorem spec_7
    (radius xCenter yCenter x1 y1 x2 y2 : Std.I64)
    (hradius_lower : 1 ≤ radius.val) (hradius_upper : radius.val ≤ 2000)
    (hxCenter_lower : -10000 ≤ xCenter.val) (hxCenter_upper : xCenter.val ≤ 10000)
    (hyCenter_lower : -10000 ≤ yCenter.val) (hyCenter_upper : yCenter.val ≤ 10000)
    (hx1_lower : -10000 ≤ x1.val) (hxlt : x1.val < x2.val) (hx2_upper : x2.val ≤ 10000)
    (hy1_lower : -10000 ≤ y1.val) (hylt : y1.val < y2.val) (hy2_upper : y2.val ≤ 10000)
    (r r' : Bool)
    (hres : Aegis.CheckOverlap.check_overlap radius xCenter yCenter x1 y1 x2 y2 = ok r)
    (hres' : Aegis.CheckOverlap.check_overlap radius
        (i64OfInt (-xCenter.val)) yCenter (i64OfInt (-x2.val)) y1 (i64OfInt (-x1.val)) y2 = ok r') :
    r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (radius xCenter yCenter x1 y1 x2 y2 : Std.I64)
    (hradius_lower : 1 ≤ radius.val) (hradius_upper : radius.val ≤ 2000)
    (hxCenter_lower : -10000 ≤ xCenter.val) (hxCenter_upper : xCenter.val ≤ 10000)
    (hyCenter_lower : -10000 ≤ yCenter.val) (hyCenter_upper : yCenter.val ≤ 10000)
    (hx1_lower : -10000 ≤ x1.val) (hxlt : x1.val < x2.val) (hx2_upper : x2.val ≤ 10000)
    (hy1_lower : -10000 ≤ y1.val) (hylt : y1.val < y2.val) (hy2_upper : y2.val ≤ 10000)
    (r r' : Bool)
    (hres : Aegis.CheckOverlap.check_overlap radius xCenter yCenter x1 y1 x2 y2 = ok r)
    (hres' : Aegis.CheckOverlap.check_overlap radius
        (i64OfInt (-xCenter.val)) yCenter (i64OfInt (-x2.val)) y1 (i64OfInt (-x1.val)) y2 = ok r'), r = r') := by
  sorry

/-- Whenever check_overlap radius xCenter yCenter x1 y1 x2 y2 returns a result r and check_overlap radius yCenter xCenter y1 x1 y2 x2 returns a result r', r = r'.
  Preconditions: radius, xCenter, yCenter, x1, y1, x2, y2 are mathematical integers satisfying 1 <= radius <= 2000, -10000 <= xCenter <= 10000, -10000 <= yCenter <= 10000, -10000 <= x1 < x2 <= 10000, and -10000 <= y1 < y2 <= 10000. -/
theorem spec_8
    (radius xCenter yCenter x1 y1 x2 y2 : Std.I64)
    (hradius_lower : 1 ≤ radius.val) (hradius_upper : radius.val ≤ 2000)
    (hxCenter_lower : -10000 ≤ xCenter.val) (hxCenter_upper : xCenter.val ≤ 10000)
    (hyCenter_lower : -10000 ≤ yCenter.val) (hyCenter_upper : yCenter.val ≤ 10000)
    (hx1_lower : -10000 ≤ x1.val) (hxlt : x1.val < x2.val) (hx2_upper : x2.val ≤ 10000)
    (hy1_lower : -10000 ≤ y1.val) (hylt : y1.val < y2.val) (hy2_upper : y2.val ≤ 10000)
    (r r' : Bool)
    (hres : Aegis.CheckOverlap.check_overlap radius xCenter yCenter x1 y1 x2 y2 = ok r)
    (hres' : Aegis.CheckOverlap.check_overlap radius yCenter xCenter y1 x1 y2 x2 = ok r') :
    r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (radius xCenter yCenter x1 y1 x2 y2 : Std.I64)
    (hradius_lower : 1 ≤ radius.val) (hradius_upper : radius.val ≤ 2000)
    (hxCenter_lower : -10000 ≤ xCenter.val) (hxCenter_upper : xCenter.val ≤ 10000)
    (hyCenter_lower : -10000 ≤ yCenter.val) (hyCenter_upper : yCenter.val ≤ 10000)
    (hx1_lower : -10000 ≤ x1.val) (hxlt : x1.val < x2.val) (hx2_upper : x2.val ≤ 10000)
    (hy1_lower : -10000 ≤ y1.val) (hylt : y1.val < y2.val) (hy2_upper : y2.val ≤ 10000)
    (r r' : Bool)
    (hres : Aegis.CheckOverlap.check_overlap radius xCenter yCenter x1 y1 x2 y2 = ok r)
    (hres' : Aegis.CheckOverlap.check_overlap radius yCenter xCenter y1 x1 y2 x2 = ok r'), r = r') := by
  sorry

end AegisSpec.CheckOverlap
