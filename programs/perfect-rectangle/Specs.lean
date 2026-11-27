import Aegis.IsRectangleCover.Code.Funs

/-!
# Specifications of `Aegis.IsRectangleCover.is_rectangle_cover`

LeetCode problem `perfect-rectangle`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsRectangleCover

  open Aeneas Aeneas.Std Result

  open Aegis.IsRectangleCover (is_rectangle_cover)

  def rows (rectangles : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    rectangles.list.toList.map (fun v => v.slice.list.toList.map (fun c => c.val))

  def x1 (rs : List (List Int)) (i : Nat) : Int := (rs.getD i []).getD 0 0

  def y1 (rs : List (List Int)) (i : Nat) : Int := (rs.getD i []).getD 1 0

  def x2 (rs : List (List Int)) (i : Nat) : Int := (rs.getD i []).getD 2 0

  def y2 (rs : List (List Int)) (i : Nat) : Int := (rs.getD i []).getD 3 0

  def listMin (l : List Int) (d : Int) : Int := l.min?.getD d

  def listMax (l : List Int) (d : Int) : Int := l.max?.getD d

  def xmin (rs : List (List Int)) : Int := listMin ((List.range rs.length).map (x1 rs)) 0

  def xmax (rs : List (List Int)) : Int := listMax ((List.range rs.length).map (x2 rs)) 0

  def ymin (rs : List (List Int)) : Int := listMin ((List.range rs.length).map (y1 rs)) 0

  def ymax (rs : List (List Int)) : Int := listMax ((List.range rs.length).map (y2 rs)) 0

  def RectPre (rectangles : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    let rs := rows rectangles
    1 ≤ rs.length ∧ rs.length ≤ 20000 ∧
      (∀ i, i < rs.length →
        (rs.getD i []).length = 4 ∧
          -100000 ≤ x1 rs i ∧ x1 rs i < x2 rs i ∧ x2 rs i ≤ 100000 ∧
          -100000 ≤ y1 rs i ∧ y1 rs i < y2 rs i ∧ y2 rs i ≤ 100000)

  def OpenDisjoint (rs : List (List Int)) : Prop :=
    ∀ i j, i < j → j < rs.length →
      x2 rs i ≤ x1 rs j ∨ x2 rs j ≤ x1 rs i ∨ y2 rs i ≤ y1 rs j ∨ y2 rs j ≤ y1 rs i

  def InBox (rs : List (List Int)) (u v : Rat) : Prop :=
    (xmin rs : Rat) ≤ u ∧ u ≤ (xmax rs : Rat) ∧ (ymin rs : Rat) ≤ v ∧ v ≤ (ymax rs : Rat)

  def InRect (rs : List (List Int)) (i : Nat) (u v : Rat) : Prop :=
    (x1 rs i : Rat) ≤ u ∧ u ≤ (x2 rs i : Rat) ∧ (y1 rs i : Rat) ≤ v ∧ v ≤ (y2 rs i : Rat)

  def CoverBox (rs : List (List Int)) : Prop :=
    ∀ u v : Rat, InBox rs u v ↔ ∃ i, i < rs.length ∧ InRect rs i u v

  def areaSum (rs : List (List Int)) : Int :=
    ((List.range rs.length).map (fun i => (x2 rs i - x1 rs i) * (y2 rs i - y1 rs i))).sum

  def boundingArea (rs : List (List Int)) : Int :=
    (xmax rs - xmin rs) * (ymax rs - ymin rs)

  def corners (rs : List (List Int)) : List (Int × Int) :=
    (List.range rs.length).flatMap (fun i =>
      [(x1 rs i, y1 rs i), (x1 rs i, y2 rs i), (x2 rs i, y1 rs i), (x2 rs i, y2 rs i)])

  def cornerCount (rs : List (List Int)) (p : Int × Int) : Nat :=
    (corners rs).countP (fun q => decide (q = p))

  def SameRect (rs : List (List Int)) (i j : Nat) : Prop :=
    x1 rs i = x1 rs j ∧ y1 rs i = y1 rs j ∧ x2 rs i = x2 rs j ∧ y2 rs i = y2 rs j

  def translateRow (r : List Int) (dx dy : Int) : List Int :=
    [r.getD 0 0 + dx, r.getD 1 0 + dy, r.getD 2 0 + dx, r.getD 3 0 + dy]

  def reflectRow (r : List Int) : List Int :=
    [-(r.getD 2 0), r.getD 1 0, -(r.getD 0 0), r.getD 3 0]

  def rotateRow (r : List Int) : List Int :=
    [-(r.getD 3 0), r.getD 0 0, -(r.getD 1 0), r.getD 2 0]

  def scaleRow (r : List Int) (k : Int) : List Int :=
    [k * r.getD 0 0, k * r.getD 1 0, k * r.getD 2 0, k * r.getD 3 0]

  def translate (rs : List (List Int)) (dx dy : Int) : List (List Int) :=
    rs.map (fun r => translateRow r dx dy)

  def reflect (rs : List (List Int)) : List (List Int) := rs.map reflectRow

  def rotate (rs : List (List Int)) : List (List Int) := rs.map rotateRow

  def scale (rs : List (List Int)) (k : Int) : List (List Int) :=
    rs.map (fun r => scaleRow r k)

  /-- Whenever the function returns a result r, r = true if and only if the following two conditions hold: (1) for every i,j with 0 <= i < j < len(rectangles), the open rectangles I_i = (x_i,a_i) x (y_i,b_i) and I_j = (x_j,a_j) x (y_j,b_j) are disjoint; (2) the union of all closed rectangles R_i = [x_i,a_i] x [y_i,b_i], for 0 <= i < len(rectangles), is exactly the closed bounding rectangle B = [Xmin,Xmax] x [Ymin,Ymax], where Xmin = min_i x_i, Xmax = max_i a_i, Ymin = min_i y_i, Ymax = max_i b_i. Equivalently, r = true exactly when the rectangles form an exact cover of a rectangular region, and r = false otherwise.
    Preconditions: len(rectangles) >= 1 and len(rectangles) <= 20000; for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4, and writing x_i = rectangles[i][0], y_i = rectangles[i][1], a_i = rectangles[i][2], b_i = rectangles[i][3], we have -100000 <= x_i < a_i <= 100000 and -100000 <= y_i < b_i <= 100000. -/
  theorem spec_1 (rectangles : Slice (alloc.vec.Vec Std.I64))
      (hpre : RectPre rectangles) :
      ∀ r : Bool, is_rectangle_cover rectangles = ok r →
        (r = true ↔ OpenDisjoint (rows rectangles) ∧ CoverBox (rows rectangles)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64))
        (hpre : RectPre rectangles), ∀ r : Bool, is_rectangle_cover rectangles = ok r →
          (r = true ↔ OpenDisjoint (rows rectangles) ∧ CoverBox (rows rectangles))) := by
    sorry

  /-- The function returns a result r (either true or false); it does not fail, panic, or overflow on any input satisfying the preconditions.
    Preconditions: len(rectangles) >= 1 and len(rectangles) <= 20000; for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4, and writing x_i = rectangles[i][0], y_i = rectangles[i][1], a_i = rectangles[i][2], b_i = rectangles[i][3], we have -100000 <= x_i < a_i <= 100000 and -100000 <= y_i < b_i <= 100000. -/
  theorem spec_2 (rectangles : Slice (alloc.vec.Vec Std.I64))
      (hpre : RectPre rectangles) :
      ∃ r : Bool, is_rectangle_cover rectangles = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64))
        (hpre : RectPre rectangles), ∃ r : Bool, is_rectangle_cover rectangles = ok r) := by
    sorry

  /-- Whenever the function returns true, sum_{i=0}^{len(rectangles)-1} (a_i - x_i) * (b_i - y_i) equals (Xmax - Xmin) * (Ymax - Ymin), where Xmin = min_i x_i, Xmax = max_i a_i, Ymin = min_i y_i, Ymax = max_i b_i.
    Preconditions: len(rectangles) >= 1 and len(rectangles) <= 20000; for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4, and writing x_i = rectangles[i][0], y_i = rectangles[i][1], a_i = rectangles[i][2], b_i = rectangles[i][3], we have -100000 <= x_i < a_i <= 100000 and -100000 <= y_i < b_i <= 100000. -/
  theorem spec_3 (rectangles : Slice (alloc.vec.Vec Std.I64))
      (hpre : RectPre rectangles) :
      ∀ r : Bool, is_rectangle_cover rectangles = ok r → r = true →
        areaSum (rows rectangles) = boundingArea (rows rectangles) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64))
        (hpre : RectPre rectangles), ∀ r : Bool, is_rectangle_cover rectangles = ok r → r = true →
          areaSum (rows rectangles) = boundingArea (rows rectangles)) := by
    sorry

  /-- Whenever the function returns true, for every i,j with 0 <= i < j < len(rectangles), the open rectangles I_i = (x_i,a_i) x (y_i,b_i) and I_j = (x_j,a_j) x (y_j,b_j) are disjoint. Equivalently, at least one of a_i <= x_j, a_j <= x_i, b_i <= y_j, or b_j <= y_i holds, so two rectangles may touch only along an edge or at a corner.
    Preconditions: len(rectangles) >= 1 and len(rectangles) <= 20000; for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4, and writing x_i = rectangles[i][0], y_i = rectangles[i][1], a_i = rectangles[i][2], b_i = rectangles[i][3], we have -100000 <= x_i < a_i <= 100000 and -100000 <= y_i < b_i <= 100000. -/
  theorem spec_4 (rectangles : Slice (alloc.vec.Vec Std.I64))
      (hpre : RectPre rectangles) :
      ∀ r : Bool, is_rectangle_cover rectangles = ok r → r = true →
        OpenDisjoint (rows rectangles) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64))
        (hpre : RectPre rectangles), ∀ r : Bool, is_rectangle_cover rectangles = ok r → r = true →
          OpenDisjoint (rows rectangles)) := by
    sorry

  /-- Whenever the function returns true, for every real point (u,v) with Xmin <= u <= Xmax and Ymin <= v <= Ymax, there exists an index i with 0 <= i < len(rectangles) such that x_i <= u <= a_i and y_i <= v <= b_i. Here Xmin = min_i x_i, Xmax = max_i a_i, Ymin = min_i y_i, Ymax = max_i b_i.
    Preconditions: len(rectangles) >= 1 and len(rectangles) <= 20000; for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4, and writing x_i = rectangles[i][0], y_i = rectangles[i][1], a_i = rectangles[i][2], b_i = rectangles[i][3], we have -100000 <= x_i < a_i <= 100000 and -100000 <= y_i < b_i <= 100000. -/
  theorem spec_5 (rectangles : Slice (alloc.vec.Vec Std.I64))
      (hpre : RectPre rectangles) :
      ∀ r : Bool, is_rectangle_cover rectangles = ok r → r = true →
        ∀ u v : Rat, InBox (rows rectangles) u v →
          ∃ i, i < (rows rectangles).length ∧ InRect (rows rectangles) i u v := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64))
        (hpre : RectPre rectangles), ∀ r : Bool, is_rectangle_cover rectangles = ok r → r = true →
          ∀ u v : Rat, InBox (rows rectangles) u v →
            ∃ i, i < (rows rectangles).length ∧ InRect (rows rectangles) i u v) := by
    sorry

  /-- Whenever, in addition to the preconditions, the open rectangles I_i = (x_i,a_i) x (y_i,b_i) are pairwise disjoint for all 0 <= i < j < len(rectangles), and sum_{i=0}^{len(rectangles)-1} (a_i - x_i) * (b_i - y_i) equals (Xmax - Xmin) * (Ymax - Ymin), where Xmin = min_i x_i, Xmax = max_i a_i, Ymin = min_i y_i, Ymax = max_i b_i, the function returns true.
    Preconditions: len(rectangles) >= 1 and len(rectangles) <= 20000; for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4, and writing x_i = rectangles[i][0], y_i = rectangles[i][1], a_i = rectangles[i][2], b_i = rectangles[i][3], we have -100000 <= x_i < a_i <= 100000 and -100000 <= y_i < b_i <= 100000. -/
  theorem spec_6 (rectangles : Slice (alloc.vec.Vec Std.I64))
      (hpre : RectPre rectangles)
      (hdisj : OpenDisjoint (rows rectangles))
      (harea : areaSum (rows rectangles) = boundingArea (rows rectangles)) :
      is_rectangle_cover rectangles = ok true := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64))
        (hpre : RectPre rectangles)
        (hdisj : OpenDisjoint (rows rectangles))
        (harea : areaSum (rows rectangles) = boundingArea (rows rectangles)), is_rectangle_cover rectangles = ok true) := by
    sorry

  /-- For every permutation pi of the index set {0,...,len(rectangles)-1}, let rectangles' be the slice of the same length with rectangles'[i] = rectangles[pi(i)] for every i. Whenever the function returns r on rectangles and r' on rectangles', r = r'.
    Preconditions: len(rectangles) >= 1 and len(rectangles) <= 20000; for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4, and writing x_i = rectangles[i][0], y_i = rectangles[i][1], a_i = rectangles[i][2], b_i = rectangles[i][3], we have -100000 <= x_i < a_i <= 100000 and -100000 <= y_i < b_i <= 100000. -/
  theorem spec_7 (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64))
      (hpre : RectPre rectangles)
      (hperm : (rows rectangles').Perm (rows rectangles)) :
      ∀ r r' : Bool, is_rectangle_cover rectangles = ok r →
        is_rectangle_cover rectangles' = ok r' → r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64))
        (hpre : RectPre rectangles)
        (hperm : (rows rectangles').Perm (rows rectangles)), ∀ r r' : Bool, is_rectangle_cover rectangles = ok r →
          is_rectangle_cover rectangles' = ok r' → r = r') := by
    sorry

  /-- For every pair of integers (dx,dy) such that the translated slice rectangles', defined by rectangles'[i] = [x_i + dx, y_i + dy, a_i + dx, b_i + dy] for every i, also satisfies the preconditions, the result of the function on rectangles equals its result on rectangles'.
    Preconditions: len(rectangles) >= 1 and len(rectangles) <= 20000; for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4, and writing x_i = rectangles[i][0], y_i = rectangles[i][1], a_i = rectangles[i][2], b_i = rectangles[i][3], we have -100000 <= x_i < a_i <= 100000 and -100000 <= y_i < b_i <= 100000. -/
  theorem spec_8 (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64))
      (dx dy : Int)
      (hpre : RectPre rectangles)
      (htrans : rows rectangles' = translate (rows rectangles) dx dy)
      (hpre' : RectPre rectangles') :
      ∀ r r' : Bool, is_rectangle_cover rectangles = ok r →
        is_rectangle_cover rectangles' = ok r' → r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64))
        (dx dy : Int)
        (hpre : RectPre rectangles)
        (htrans : rows rectangles' = translate (rows rectangles) dx dy)
        (hpre' : RectPre rectangles'), ∀ r r' : Bool, is_rectangle_cover rectangles = ok r →
          is_rectangle_cover rectangles' = ok r' → r = r') := by
    sorry

  /-- Let rectangles' be obtained from rectangles by replacing each entry [x_i,y_i,a_i,b_i] with [-a_i,y_i,-x_i,b_i], which is reflection in the y-axis. Whenever rectangles' also satisfies the preconditions, the result of the function on rectangles equals its result on rectangles'.
    Preconditions: len(rectangles) >= 1 and len(rectangles) <= 20000; for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4, and writing x_i = rectangles[i][0], y_i = rectangles[i][1], a_i = rectangles[i][2], b_i = rectangles[i][3], we have -100000 <= x_i < a_i <= 100000 and -100000 <= y_i < b_i <= 100000. -/
  theorem spec_9 (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64))
      (hpre : RectPre rectangles)
      (hreflect : rows rectangles' = reflect (rows rectangles))
      (hpre' : RectPre rectangles') :
      ∀ r r' : Bool, is_rectangle_cover rectangles = ok r →
        is_rectangle_cover rectangles' = ok r' → r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64))
        (hpre : RectPre rectangles)
        (hreflect : rows rectangles' = reflect (rows rectangles))
        (hpre' : RectPre rectangles'), ∀ r r' : Bool, is_rectangle_cover rectangles = ok r →
          is_rectangle_cover rectangles' = ok r' → r = r') := by
    sorry

  /-- Let rectangles' be obtained from rectangles by replacing each entry [x_i,y_i,a_i,b_i] with [-b_i,x_i,-y_i,a_i], which is 90-degree counterclockwise rotation about the origin. Whenever rectangles' also satisfies the preconditions, the result of the function on rectangles equals its result on rectangles'.
    Preconditions: len(rectangles) >= 1 and len(rectangles) <= 20000; for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4, and writing x_i = rectangles[i][0], y_i = rectangles[i][1], a_i = rectangles[i][2], b_i = rectangles[i][3], we have -100000 <= x_i < a_i <= 100000 and -100000 <= y_i < b_i <= 100000. -/
  theorem spec_10 (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64))
      (hpre : RectPre rectangles)
      (hrotate : rows rectangles' = rotate (rows rectangles))
      (hpre' : RectPre rectangles') :
      ∀ r r' : Bool, is_rectangle_cover rectangles = ok r →
        is_rectangle_cover rectangles' = ok r' → r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64))
        (hpre : RectPre rectangles)
        (hrotate : rows rectangles' = rotate (rows rectangles))
        (hpre' : RectPre rectangles'), ∀ r r' : Bool, is_rectangle_cover rectangles = ok r →
          is_rectangle_cover rectangles' = ok r' → r = r') := by
    sorry

  /-- For every positive integer k such that the slice rectangles', defined by rectangles'[i] = [k*x_i, k*y_i, k*a_i, k*b_i] for every i, also satisfies the preconditions, the result of the function on rectangles equals its result on rectangles'.
    Preconditions: len(rectangles) >= 1 and len(rectangles) <= 20000; for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4, and writing x_i = rectangles[i][0], y_i = rectangles[i][1], a_i = rectangles[i][2], b_i = rectangles[i][3], we have -100000 <= x_i < a_i <= 100000 and -100000 <= y_i < b_i <= 100000. -/
  theorem spec_11 (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64))
      (k : Int) (hk : 0 < k)
      (hpre : RectPre rectangles)
      (hscale : rows rectangles' = scale (rows rectangles) k)
      (hpre' : RectPre rectangles') :
      ∀ r r' : Bool, is_rectangle_cover rectangles = ok r →
        is_rectangle_cover rectangles' = ok r' → r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (rectangles rectangles' : Slice (alloc.vec.Vec Std.I64))
        (k : Int) (hk : 0 < k)
        (hpre : RectPre rectangles)
        (hscale : rows rectangles' = scale (rows rectangles) k)
        (hpre' : RectPre rectangles'), ∀ r r' : Bool, is_rectangle_cover rectangles = ok r →
          is_rectangle_cover rectangles' = ok r' → r = r') := by
    sorry

  /-- The function returns false.
    Preconditions: len(rectangles) >= 2 and len(rectangles) <= 20000; for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4, and writing x_i = rectangles[i][0], y_i = rectangles[i][1], a_i = rectangles[i][2], b_i = rectangles[i][3], we have -100000 <= x_i < a_i <= 100000 and -100000 <= y_i < b_i <= 100000; there exist i,j with 0 <= i < j < len(rectangles) such that rectangles[i] and rectangles[j] have the same four coordinates. -/
  theorem spec_12 (rectangles : Slice (alloc.vec.Vec Std.I64))
      (hpre : RectPre rectangles)
      (hlen : 2 ≤ (rows rectangles).length)
      (hdup : ∃ i j, i < j ∧ j < (rows rectangles).length ∧
        SameRect (rows rectangles) i j) :
      is_rectangle_cover rectangles = ok false := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64))
        (hpre : RectPre rectangles)
        (hlen : 2 ≤ (rows rectangles).length)
        (hdup : ∃ i j, i < j ∧ j < (rows rectangles).length ∧
          SameRect (rows rectangles) i j), is_rectangle_cover rectangles = ok false) := by
    sorry

  /-- Whenever the function returns true, let c(p) be the number of indices i and corners C in {(x_i,y_i),(x_i,b_i),(a_i,y_i),(a_i,b_i)} with C = p. Let Xmin = min_i x_i, Xmax = max_i a_i, Ymin = min_i y_i, Ymax = max_i b_i. Then c(Xmin,Ymin) = c(Xmin,Ymax) = c(Xmax,Ymin) = c(Xmax,Ymax) = 1, and for every integer point p not equal to one of these four bounding-box corners, c(p) is even.
    Preconditions: len(rectangles) >= 1 and len(rectangles) <= 20000; for every i with 0 <= i < len(rectangles), len(rectangles[i]) = 4, and writing x_i = rectangles[i][0], y_i = rectangles[i][1], a_i = rectangles[i][2], b_i = rectangles[i][3], we have -100000 <= x_i < a_i <= 100000 and -100000 <= y_i < b_i <= 100000. -/
  theorem spec_13 (rectangles : Slice (alloc.vec.Vec Std.I64))
      (hpre : RectPre rectangles) :
      ∀ r : Bool, is_rectangle_cover rectangles = ok r → r = true →
        cornerCount (rows rectangles) (xmin (rows rectangles), ymin (rows rectangles)) = 1 ∧
        cornerCount (rows rectangles) (xmin (rows rectangles), ymax (rows rectangles)) = 1 ∧
        cornerCount (rows rectangles) (xmax (rows rectangles), ymin (rows rectangles)) = 1 ∧
        cornerCount (rows rectangles) (xmax (rows rectangles), ymax (rows rectangles)) = 1 ∧
        ∀ p : Int × Int,
          p ≠ (xmin (rows rectangles), ymin (rows rectangles)) →
          p ≠ (xmin (rows rectangles), ymax (rows rectangles)) →
          p ≠ (xmax (rows rectangles), ymin (rows rectangles)) →
          p ≠ (xmax (rows rectangles), ymax (rows rectangles)) →
          Even (cornerCount (rows rectangles) p) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (rectangles : Slice (alloc.vec.Vec Std.I64))
        (hpre : RectPre rectangles), ∀ r : Bool, is_rectangle_cover rectangles = ok r → r = true →
          cornerCount (rows rectangles) (xmin (rows rectangles), ymin (rows rectangles)) = 1 ∧
          cornerCount (rows rectangles) (xmin (rows rectangles), ymax (rows rectangles)) = 1 ∧
          cornerCount (rows rectangles) (xmax (rows rectangles), ymin (rows rectangles)) = 1 ∧
          cornerCount (rows rectangles) (xmax (rows rectangles), ymax (rows rectangles)) = 1 ∧
          ∀ p : Int × Int,
            p ≠ (xmin (rows rectangles), ymin (rows rectangles)) →
            p ≠ (xmin (rows rectangles), ymax (rows rectangles)) →
            p ≠ (xmax (rows rectangles), ymin (rows rectangles)) →
            p ≠ (xmax (rows rectangles), ymax (rows rectangles)) →
            Even (cornerCount (rows rectangles) p)) := by
    sorry

  end AegisSpec.IsRectangleCover
