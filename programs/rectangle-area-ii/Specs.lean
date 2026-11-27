import Mathlib.Basic.Real.Basic
import Aegis.RectangleArea.Code.Funs

/-!
# Specifications of `Aegis.RectangleArea.rectangle_area`

LeetCode problem `rectangle-area-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.RectangleArea (rectangle_area)

namespace AegisSpec.RectangleArea

def M : ℤ := 1000000007

structure Rect where
  x1 : ℤ
  y1 : ℤ
  x2 : ℤ
  y2 : ℤ
  deriving Inhabited, DecidableEq, Repr

def Rect.Bounded (B : Rect) : Prop :=
  0 ≤ B.x1 ∧ B.x1 < B.x2 ∧ B.x2 ≤ 2000000000 ∧
    0 ≤ B.y1 ∧ B.y1 < B.y2 ∧ B.y2 ≤ 2000000000

def toRect (v : alloc.vec.Vec Std.I64) : Option Rect :=
  match v.val with
  | [a, b, c, d] => some ⟨a.val, b.val, c.val, d.val⟩
  | _ => none

def toRects : List (alloc.vec.Vec Std.I64) → Option (List Rect)
  | [] => some []
  | v :: vs =>
    match toRect v, toRects vs with
    | some B, some l => some (B :: l)
    | _, _ => none

def inputRects (rectangles : Slice (alloc.vec.Vec Std.I64)) : Option (List Rect) :=
  toRects rectangles.val

def intRange (lo hi : ℤ) : List ℤ := (List.range (hi - lo).toNat).map (fun k => lo + (k : ℤ))

def unionSet (rects : List Rect) : Set (ℝ × ℝ) :=
  {p | ∃ B ∈ rects,
    (B.x1 : ℝ) ≤ p.1 ∧ p.1 ≤ (B.x2 : ℝ) ∧ (B.y1 : ℝ) ≤ p.2 ∧ p.2 ≤ (B.y2 : ℝ)}

def cells (rects : List Rect) : Finset (ℤ × ℤ) :=
  (rects.flatMap fun B => (intRange B.x1 B.x2).product (intRange B.y1 B.y2)).toFinset

def unionArea (rects : List Rect) : ℤ := ((cells rects).card : ℤ)

def sumArea (rects : List Rect) : ℤ :=
  (rects.map fun B => (B.x2 - B.x1) * (B.y2 - B.y1)).sum

def IsResidue (A r : ℤ) : Prop :=
  0 ≤ r ∧ r < M ∧ Int.ModEq M r A ∧
    ∀ r' : ℤ, 0 ≤ r' → r' < M → Int.ModEq M r' A → r' = r

def DisjointInterior (A B : Rect) : Prop :=
  A.x2 ≤ B.x1 ∨ B.x2 ≤ A.x1 ∨ A.y2 ≤ B.y1 ∨ B.y2 ≤ A.y1

def PairwiseDisjointInterior (rects : List Rect) : Prop :=
  ∀ (i j : Nat) (hi : i < rects.length) (hj : j < rects.length), i < j →
    DisjointInterior (rects.get ⟨i, hi⟩) (rects.get ⟨j, hj⟩)

def scaledBy (k : ℤ) (rects : List Rect) : List Rect :=
  rects.map fun B => ⟨k * B.x1, k * B.y1, k * B.x2, k * B.y2⟩

def foldMin (f : Rect → ℤ) (rects : List Rect) : ℤ :=
  match rects with
  | [] => 0
  | B₀ :: _ => rects.foldr (fun B acc => min (f B) acc) (f B₀)

def foldMax (f : Rect → ℤ) (rects : List Rect) : ℤ :=
  match rects with
  | [] => 0
  | B₀ :: _ => rects.foldr (fun B acc => max (f B) acc) (f B₀)

def bboxLeft (rects : List Rect) : ℤ := foldMin Rect.x1 rects

def bboxRight (rects : List Rect) : ℤ := foldMax Rect.x2 rects

def bboxBottom (rects : List Rect) : ℤ := foldMin Rect.y1 rects

def bboxTop (rects : List Rect) : ℤ := foldMax Rect.y2 rects

def BBoxCovered (rects : List Rect) : Prop :=
  ∀ (x y : ℝ),
    (bboxLeft rects : ℝ) ≤ x → x ≤ (bboxRight rects : ℝ) →
      (bboxBottom rects : ℝ) ≤ y → y ≤ (bboxTop rects : ℝ) →
        ∃ (i : Nat) (hi : i < rects.length),
          ((rects.get ⟨i, hi⟩).x1 : ℝ) ≤ x ∧ x ≤ ((rects.get ⟨i, hi⟩).x2 : ℝ) ∧
            ((rects.get ⟨i, hi⟩).y1 : ℝ) ≤ y ∧ y ≤ ((rects.get ⟨i, hi⟩).y2 : ℝ)

def SeparatedAt (rects : List Rect) (m : Nat) : Prop :=
  (∀ B ∈ rects.take m, ∀ C ∈ rects.drop m, B.x2 ≤ C.x1) ∨
    (∀ B ∈ rects.take m, ∀ C ∈ rects.drop m, B.y2 ≤ C.y1)

/-- Let M = 1000000007. Let U = { (x,y) in R x R | there exists i with 0 <= i < len(rectangles), x1_i <= x <= x2_i, and y1_i <= y <= y2_i }, and let A be the ordinary planar area of U. Whenever rectangle_area rectangles returns a result r, r is the unique integer such that 0 <= r < M and r is congruent to A modulo M.
  Preconditions: Assume: (i) 1 <= len(rectangles) <= 200; (ii) for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4; (iii) writing rectangles[i] = [x1_i, y1_i, x2_i, y2_i], for every such i we have 0 <= x1_i < x2_i <= 2000000000 and 0 <= y1_i < y2_i <= 2000000000. -/
theorem spec_1 (rectangles : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length ≤ 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded)
    (r : Std.I64) (hr : rectangle_area rectangles = ok r) :
    IsResidue (unionArea rects) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length ≤ 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded)
    (r : Std.I64) (hr : rectangle_area rectangles = ok r), IsResidue (unionArea rects) r.val) := by
  sorry

/-- For every input satisfying the preconditions, rectangle_area rectangles returns a result r; it does not fail, panic, or overflow.
  Preconditions: Assume: (i) 1 <= len(rectangles) <= 200; (ii) for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4; (iii) writing rectangles[i] = [x1_i, y1_i, x2_i, y2_i], for every such i we have 0 <= x1_i < x2_i <= 2000000000 and 0 <= y1_i < y2_i <= 2000000000. -/
theorem spec_2 (rectangles : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length ≤ 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded) :
    ∃ r : Std.I64, rectangle_area rectangles = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length ≤ 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded), ∃ r : Std.I64, rectangle_area rectangles = ok r) := by
  sorry

/-- Whenever rectangle_area rectangles returns a result r, 0 <= r < 1000000007.
  Preconditions: Assume: (i) 1 <= len(rectangles) <= 200; (ii) for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4; (iii) writing rectangles[i] = [x1_i, y1_i, x2_i, y2_i], for every such i we have 0 <= x1_i < x2_i <= 2000000000 and 0 <= y1_i < y2_i <= 2000000000. -/
theorem spec_3 (rectangles : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length ≤ 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded)
    (r : Std.I64) (hr : rectangle_area rectangles = ok r) :
    0 ≤ r.val ∧ r.val < M := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length ≤ 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded)
    (r : Std.I64) (hr : rectangle_area rectangles = ok r), 0 ≤ r.val ∧ r.val < M) := by
  sorry

/-- Let M = 1000000007 and let S = Sum_{i=0}^{len(rectangles)-1} (x2_i - x1_i) * (y2_i - y1_i). Whenever rectangle_area rectangles returns a result r, r is the unique integer such that 0 <= r < M and r is congruent to S modulo M.
  Preconditions: Assume: (i) 1 <= len(rectangles) <= 200; (ii) for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4; (iii) writing rectangles[i] = [x1_i, y1_i, x2_i, y2_i], for every such i we have 0 <= x1_i < x2_i <= 2000000000 and 0 <= y1_i < y2_i <= 2000000000; (iv) for every pair i < j, the two rectangles have disjoint interiors, meaning x2_i <= x1_j or x2_j <= x1_i or y2_i <= y1_j or y2_j <= y1_i. -/
theorem spec_4 (rectangles : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length ≤ 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded)
    (hdisj : PairwiseDisjointInterior rects)
    (r : Std.I64) (hr : rectangle_area rectangles = ok r) :
    IsResidue (sumArea rects) r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length ≤ 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded)
    (hdisj : PairwiseDisjointInterior rects)
    (r : Std.I64) (hr : rectangle_area rectangles = ok r), IsResidue (sumArea rects) r.val) := by
  sorry

/-- Whenever rectangle_area rectangles returns a result r and rectangle_area rectangles' returns a result r', we have r = r'.
  Preconditions: Assume: (i) 1 <= len(rectangles) <= 200; (ii) for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4; (iii) writing rectangles[i] = [x1_i, y1_i, x2_i, y2_i], for every such i we have 0 <= x1_i < x2_i <= 2000000000 and 0 <= y1_i < y2_i <= 2000000000. Choose k with 0 <= k < len(rectangles). Let rectangles' be obtained by inserting an additional copy of rectangles[k] at any position, and assume len(rectangles') <= 200. -/
theorem spec_5 (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length ≤ 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded)
    (k : Nat) (hk : k < rects.length)
    (p : Nat) (hp : p ≤ rects.length)
    (hins : inputRects rectangles' = some (rects.take p ++ [rects.get ⟨k, hk⟩] ++ rects.drop p))
    (hle' : rectangles'.val.length ≤ 200)
    (r r' : Std.I64) (hr : rectangle_area rectangles = ok r)
    (hr' : rectangle_area rectangles' = ok r') :
    r = r' := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length ≤ 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded)
    (k : Nat) (hk : k < rects.length)
    (p : Nat) (hp : p ≤ rects.length)
    (hins : inputRects rectangles' = some (rects.take p ++ [rects.get ⟨k, hk⟩] ++ rects.drop p))
    (hle' : rectangles'.val.length ≤ 200)
    (r r' : Std.I64) (hr : rectangle_area rectangles = ok r)
    (hr' : rectangle_area rectangles' = ok r'), r = r') := by
  sorry

/-- Let M = 1000000007. Whenever rectangle_area rectangles returns a result r and rectangle_area rectangles' returns a result r', r' is the unique integer such that 0 <= r' < M and r' is congruent to k*k*r modulo M.
  Preconditions: Assume: (i) 1 <= len(rectangles) <= 200; (ii) for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4; (iii) writing rectangles[i] = [x1_i, y1_i, x2_i, y2_i], for every such i we have 0 <= x1_i < x2_i <= 2000000000 and 0 <= y1_i < y2_i <= 2000000000. Let k >= 1 be an integer, and define rectangles'[i] = [k*x1_i, k*y1_i, k*x2_i, k*y2_i]. Assume rectangles' satisfies the same length and coordinate conditions (i)-(iii). -/
theorem spec_6 (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length ≤ 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded)
    (k : ℤ) (hk : 1 ≤ k)
    (hne' : 1 ≤ rectangles'.val.length) (hle' : rectangles'.val.length ≤ 200)
    (hscaled : inputRects rectangles' = some (scaledBy k rects))
    (hbounds' : ∀ B ∈ scaledBy k rects, B.Bounded)
    (r r' : Std.I64) (hr : rectangle_area rectangles = ok r)
    (hr' : rectangle_area rectangles' = ok r') :
    IsResidue (k * k * r.val) r'.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length ≤ 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded)
    (k : ℤ) (hk : 1 ≤ k)
    (hne' : 1 ≤ rectangles'.val.length) (hle' : rectangles'.val.length ≤ 200)
    (hscaled : inputRects rectangles' = some (scaledBy k rects))
    (hbounds' : ∀ B ∈ scaledBy k rects, B.Bounded)
    (r r' : Std.I64) (hr : rectangle_area rectangles = ok r)
    (hr' : rectangle_area rectangles' = ok r'), IsResidue (k * k * r.val) r'.val) := by
  sorry

/-- Let M = 1000000007. Whenever rectangle_area rectangles returns a result r, r is the unique integer such that 0 <= r < M and r is congruent to (v-u)*(z-w) modulo M.
  Preconditions: Assume: (i) 1 <= len(rectangles) <= 200; (ii) for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4; (iii) writing rectangles[i] = [x1_i, y1_i, x2_i, y2_i], for every such i we have 0 <= x1_i < x2_i <= 2000000000 and 0 <= y1_i < y2_i <= 2000000000. Let u = min_i x1_i, v = max_i x2_i, w = min_i y1_i, and z = max_i y2_i. Assume every point of the bounding box [u,v] x [w,z] is covered by at least one rectangle: for every real x,y with u <= x <= v and w <= y <= z there exists i with x1_i <= x <= x2_i and y1_i <= y <= y2_i. -/
theorem spec_7 (rectangles : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length ≤ 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded)
    (hcover : BBoxCovered rects)
    (r : Std.I64) (hr : rectangle_area rectangles = ok r) :
    IsResidue ((bboxRight rects - bboxLeft rects) * (bboxTop rects - bboxBottom rects)) r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length ≤ 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded)
    (hcover : BBoxCovered rects)
    (r : Std.I64) (hr : rectangle_area rectangles = ok r), IsResidue ((bboxRight rects - bboxLeft rects) * (bboxTop rects - bboxBottom rects)) r.val) := by
  sorry

/-- Let U and U' be the unions of rectangles and rectangles', respectively, and let A and A' be their ordinary planar areas. Whenever rectangle_area rectangles returns a result r and rectangle_area rectangles' returns a result r', we have A <= A', r is the unique integer such that 0 <= r < 1000000007 and r is congruent to A modulo 1000000007, and r' is the unique integer such that 0 <= r' < 1000000007 and r' is congruent to A' modulo 1000000007.
  Preconditions: Assume: (i) 1 <= len(rectangles) < 200; (ii) for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4; (iii) writing rectangles[i] = [x1_i, y1_i, x2_i, y2_i], for every such i we have 0 <= x1_i < x2_i <= 2000000000 and 0 <= y1_i < y2_i <= 2000000000. Let q = [a1,b1,a2,b2] with 0 <= a1 < a2 <= 2000000000 and 0 <= b1 < b2 <= 2000000000, and let rectangles' be rectangles with q appended. -/
theorem spec_8 (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (q : Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length < 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded)
    (hq : q.Bounded)
    (hrows' : inputRects rectangles' = some (rects ++ [q]))
    (r r' : Std.I64) (hr : rectangle_area rectangles = ok r)
    (hr' : rectangle_area rectangles' = ok r') :
    unionArea rects ≤ unionArea (rects ++ [q]) ∧
      IsResidue (unionArea rects) r.val ∧ IsResidue (unionArea (rects ++ [q])) r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (q : Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length < 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded)
    (hq : q.Bounded)
    (hrows' : inputRects rectangles' = some (rects ++ [q]))
    (r r' : Std.I64) (hr : rectangle_area rectangles = ok r)
    (hr' : rectangle_area rectangles' = ok r'), unionArea rects ≤ unionArea (rects ++ [q]) ∧
      IsResidue (unionArea rects) r.val ∧ IsResidue (unionArea (rects ++ [q])) r'.val) := by
  sorry

/-- Let U be the union of the rectangles and A its ordinary planar area. Let S = Sum_{i=0}^{len(rectangles)-1} (x2_i - x1_i) * (y2_i - y1_i). Whenever rectangle_area rectangles returns a result r, r is the unique integer such that 0 <= r < 1000000007 and r is congruent to A modulo 1000000007, and A <= S.
  Preconditions: Assume: (i) 1 <= len(rectangles) <= 200; (ii) for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4; (iii) writing rectangles[i] = [x1_i, y1_i, x2_i, y2_i], for every such i we have 0 <= x1_i < x2_i <= 2000000000 and 0 <= y1_i < y2_i <= 2000000000. -/
theorem spec_9 (rectangles : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length ≤ 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded)
    (r : Std.I64) (hr : rectangle_area rectangles = ok r) :
    IsResidue (unionArea rects) r.val ∧ unionArea rects ≤ sumArea rects := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length ≤ 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded)
    (r : Std.I64) (hr : rectangle_area rectangles = ok r), IsResidue (unionArea rects) r.val ∧ unionArea rects ≤ sumArea rects) := by
  sorry

/-- Let U1 be the union of rectangles[0],...,rectangles[m-1] and U2 the union of rectangles[m],...,rectangles[len(rectangles)-1], and let A1 and A2 be their ordinary planar areas. Whenever rectangle_area rectangles returns a result r, r is the unique integer such that 0 <= r < 1000000007 and r is congruent to A1 + A2 modulo 1000000007; under the separation assumption the total union area is exactly A1 + A2.
  Preconditions: Assume: (i) 1 <= len(rectangles) <= 200; (ii) for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4; (iii) writing rectangles[i] = [x1_i, y1_i, x2_i, y2_i], for every such i we have 0 <= x1_i < x2_i <= 2000000000 and 0 <= y1_i < y2_i <= 2000000000. Choose m with 1 <= m < len(rectangles). Assume either max_{0 <= i < m} x2_i <= min_{m <= j < len(rectangles)} x1_j or max_{0 <= i < m} y2_i <= min_{m <= j < len(rectangles)} y1_j. -/
theorem spec_10 (rectangles : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length ≤ 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded)
    (m : Nat) (hm1 : 1 ≤ m) (hm2 : m < rects.length)
    (hsep : SeparatedAt rects m)
    (r : Std.I64) (hr : rectangle_area rectangles = ok r) :
    unionArea rects = unionArea (rects.take m) + unionArea (rects.drop m) ∧
      IsResidue (unionArea (rects.take m) + unionArea (rects.drop m)) r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64)) (rects : List Rect)
    (hne : 1 ≤ rectangles.val.length) (hle : rectangles.val.length ≤ 200)
    (hrows : inputRects rectangles = some rects)
    (hbounds : ∀ B ∈ rects, B.Bounded)
    (m : Nat) (hm1 : 1 ≤ m) (hm2 : m < rects.length)
    (hsep : SeparatedAt rects m)
    (r : Std.I64) (hr : rectangle_area rectangles = ok r), unionArea rects = unionArea (rects.take m) + unionArea (rects.drop m) ∧
      IsResidue (unionArea (rects.take m) + unionArea (rects.drop m)) r.val) := by
  sorry

end AegisSpec.RectangleArea
