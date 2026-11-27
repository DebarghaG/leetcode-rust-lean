import Aegis.CountRectangles.Code.Funs

/-!
# Specifications of `Aegis.CountRectangles.count_rectangles`

LeetCode problem `count-number-of-rectangles-containing-each-point`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountRectangles

  def coordsOf (v : alloc.vec.Vec Std.I64) : Option (Int × Int) :=
    match v.val.map (fun x => x.val) with
    | [a, b] => some (a, b)
    | _ => none

  def coordsAt (s : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Option (Int × Int) :=
    match s.val[i]? with
    | some v => coordsOf v
    | none => none

  def xAt (s : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    match coordsAt s i with
    | some (a, _) => a
    | none => 0

  def yAt (s : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    match coordsAt s i with
    | some (_, b) => b
    | none => 0

  def Contains (rectangles points : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Prop :=
    ∃ a b c d : Int,
      coordsAt rectangles i = some (a, b) ∧ coordsAt points j = some (c, d) ∧ c ≤ a ∧ d ≤ b

  def Outside (rectangles points : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Prop :=
    ∃ a b c d : Int,
      coordsAt rectangles i = some (a, b) ∧ coordsAt points j = some (c, d) ∧ (a < c ∨ b < d)

  def containsB (rectangles points : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Bool :=
    match coordsAt rectangles i, coordsAt points j with
    | some (a, b), some (c, d) => decide (c ≤ a ∧ d ≤ b)
    | _, _ => false

  def countIndices (n : Nat) (p : Nat → Bool) : Nat :=
    (List.range n).countP p

  def countContaining (rectangles points : Slice (alloc.vec.Vec Std.I64)) (j : Nat) : Nat :=
    countIndices rectangles.val.length (fun i => containsB rectangles points i j)

  def outAt (r : alloc.vec.Vec Std.I64) (j : Nat) : Int :=
    match r.val[j]? with
    | some x => x.val
    | none => 0

  def sumOut (r : alloc.vec.Vec Std.I64) (m : Nat) : Int :=
    ((List.range m).map (fun j => outAt r j)).sum

  def countPairs (rectangles points : Slice (alloc.vec.Vec Std.I64)) (m : Nat) : Nat :=
    ((List.range rectangles.val.length).map
      (fun i => countIndices m (fun j => containsB rectangles points i j))).sum

  def RectanglesWellFormed (rectangles : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ i : Nat, i < rectangles.val.length → ∃ a b : Int,
      coordsAt rectangles i = some (a, b) ∧ 1 ≤ a ∧ a ≤ 1000000000 ∧ 1 ≤ b ∧ b ≤ 100

  def PointsWellFormed (points : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ j : Nat, j < points.val.length → ∃ c d : Int,
      coordsAt points j = some (c, d) ∧ 1 ≤ c ∧ c ≤ 1000000000 ∧ 1 ≤ d ∧ d ≤ 100

  def PointsDistinct (points : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ j k : Nat, j < k → k < points.val.length → ∀ c d c' d' : Int,
      coordsAt points j = some (c, d) → coordsAt points k = some (c', d') → (c, d) ≠ (c', d')

  /-- Whenever the function returns a result r, len(r) = len(points) and for every j with 0 <= j < len(points), r[j] is the number of indices i with 0 <= i < len(rectangles) such that points[j][0] <= rectangles[i][0] and points[j][1] <= rectangles[i][1]. Equivalently, r[j] is the number of rectangles containing points[j], where rectangle i contains point j exactly when 0 <= points[j][0] <= rectangles[i][0] and 0 <= points[j][1] <= rectangles[i][1]; the lower bounds are automatic from the preconditions.
    Preconditions: Let n = len(rectangles) and m = len(points). We have 1 <= n <= 50000 and 1 <= m <= 50000. For every i with 0 <= i < n, rectangles[i] has length 2 and its entries satisfy 1 <= rectangles[i][0] <= 10^9 and 1 <= rectangles[i][1] <= 100. For every j with 0 <= j < m, points[j] has length 2 and its entries satisfy 1 <= points[j][0] <= 10^9 and 1 <= points[j][1] <= 100. The points are pairwise distinct: if 0 <= j < k < m then (points[j][0], points[j][1]) != (points[k][0], points[k][1]). -/
  theorem spec_1
      (rectangles points : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
      (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
      (hrect : RectanglesWellFormed rectangles)
      (hpts : PointsWellFormed points)
      (hdist : PointsDistinct points)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r) :
      r.val.length = points.val.length ∧
        ∀ j : Nat, j < points.val.length →
          outAt r j = (countContaining rectangles points j : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (rectangles points : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
        (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
        (hrect : RectanglesWellFormed rectangles)
        (hpts : PointsWellFormed points)
        (hdist : PointsDistinct points)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r), r.val.length = points.val.length ∧
          ∀ j : Nat, j < points.val.length →
            outAt r j = (countContaining rectangles points j : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail (for example, via overflow, out-of-bounds access, or panic).
    Preconditions: Let n = len(rectangles) and m = len(points). We have 1 <= n <= 50000 and 1 <= m <= 50000. For every i with 0 <= i < n, rectangles[i] has length 2 and its entries satisfy 1 <= rectangles[i][0] <= 10^9 and 1 <= rectangles[i][1] <= 100. For every j with 0 <= j < m, points[j] has length 2 and its entries satisfy 1 <= points[j][0] <= 10^9 and 1 <= points[j][1] <= 100. The points are pairwise distinct: if 0 <= j < k < m then (points[j][0], points[j][1]) != (points[k][0], points[k][1]). -/
  theorem spec_2
      (rectangles points : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
      (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
      (hrect : RectanglesWellFormed rectangles)
      (hpts : PointsWellFormed points)
      (hdist : PointsDistinct points) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.CountRectangles.count_rectangles rectangles points = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (rectangles points : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
        (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
        (hrect : RectanglesWellFormed rectangles)
        (hpts : PointsWellFormed points)
        (hdist : PointsDistinct points), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.CountRectangles.count_rectangles rectangles points = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(points) and j < len(r), r[j] = 0 if and only if for every i with 0 <= i < len(rectangles), either points[j][0] > rectangles[i][0] or points[j][1] > rectangles[i][1].
    Preconditions: Let n = len(rectangles) and m = len(points). We have 1 <= n <= 50000 and 1 <= m <= 50000. For every i with 0 <= i < n, rectangles[i] has length 2 and its entries satisfy 1 <= rectangles[i][0] <= 10^9 and 1 <= rectangles[i][1] <= 100. For every j with 0 <= j < m, points[j] has length 2 and its entries satisfy 1 <= points[j][0] <= 10^9 and 1 <= points[j][1] <= 100. The points are pairwise distinct: if 0 <= j < k < m then (points[j][0], points[j][1]) != (points[k][0], points[k][1]). -/
  theorem spec_3
      (rectangles points : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
      (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
      (hrect : RectanglesWellFormed rectangles)
      (hpts : PointsWellFormed points)
      (hdist : PointsDistinct points)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r) :
      ∀ j : Nat, j < points.val.length → j < r.val.length →
        (outAt r j = 0 ↔
          ∀ i : Nat, i < rectangles.val.length → Outside rectangles points i j) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (rectangles points : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
        (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
        (hrect : RectanglesWellFormed rectangles)
        (hpts : PointsWellFormed points)
        (hdist : PointsDistinct points)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r), ∀ j : Nat, j < points.val.length → j < r.val.length →
          (outAt r j = 0 ↔
            ∀ i : Nat, i < rectangles.val.length → Outside rectangles points i j)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(points) and j < len(r), r[j] = len(rectangles) if and only if for every i with 0 <= i < len(rectangles), points[j][0] <= rectangles[i][0] and points[j][1] <= rectangles[i][1].
    Preconditions: Let n = len(rectangles) and m = len(points). We have 1 <= n <= 50000 and 1 <= m <= 50000. For every i with 0 <= i < n, rectangles[i] has length 2 and its entries satisfy 1 <= rectangles[i][0] <= 10^9 and 1 <= rectangles[i][1] <= 100. For every j with 0 <= j < m, points[j] has length 2 and its entries satisfy 1 <= points[j][0] <= 10^9 and 1 <= points[j][1] <= 100. The points are pairwise distinct: if 0 <= j < k < m then (points[j][0], points[j][1]) != (points[k][0], points[k][1]). -/
  theorem spec_4
      (rectangles points : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
      (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
      (hrect : RectanglesWellFormed rectangles)
      (hpts : PointsWellFormed points)
      (hdist : PointsDistinct points)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r) :
      ∀ j : Nat, j < points.val.length → j < r.val.length →
        (outAt r j = (rectangles.val.length : Int) ↔
          ∀ i : Nat, i < rectangles.val.length → Contains rectangles points i j) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (rectangles points : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
        (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
        (hrect : RectanglesWellFormed rectangles)
        (hpts : PointsWellFormed points)
        (hdist : PointsDistinct points)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r), ∀ j : Nat, j < points.val.length → j < r.val.length →
          (outAt r j = (rectangles.val.length : Int) ↔
            ∀ i : Nat, i < rectangles.val.length → Contains rectangles points i j)) := by
    sorry

  /-- Whenever the function returns a result r, for any j and k with 0 <= j < len(points), 0 <= k < len(points), j < len(r), and k < len(r), if points[j][0] <= points[k][0] and points[j][1] <= points[k][1], then r[j] >= r[k].
    Preconditions: Let n = len(rectangles) and m = len(points). We have 1 <= n <= 50000 and 1 <= m <= 50000. For every i with 0 <= i < n, rectangles[i] has length 2 and its entries satisfy 1 <= rectangles[i][0] <= 10^9 and 1 <= rectangles[i][1] <= 100. For every j with 0 <= j < m, points[j] has length 2 and its entries satisfy 1 <= points[j][0] <= 10^9 and 1 <= points[j][1] <= 100. The points are pairwise distinct: if 0 <= j < k < m then (points[j][0], points[j][1]) != (points[k][0], points[k][1]). -/
  theorem spec_5
      (rectangles points : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
      (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
      (hrect : RectanglesWellFormed rectangles)
      (hpts : PointsWellFormed points)
      (hdist : PointsDistinct points)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r) :
      ∀ j k : Nat, j < points.val.length → k < points.val.length →
        j < r.val.length → k < r.val.length →
        xAt points j ≤ xAt points k → yAt points j ≤ yAt points k →
        outAt r k ≤ outAt r j := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (rectangles points : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
        (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
        (hrect : RectanglesWellFormed rectangles)
        (hpts : PointsWellFormed points)
        (hdist : PointsDistinct points)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r), ∀ j k : Nat, j < points.val.length → k < points.val.length →
          j < r.val.length → k < r.val.length →
          xAt points j ≤ xAt points k → yAt points j ≤ yAt points k →
          outAt r k ≤ outAt r j) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(points) and j < len(r), r[j] is at most the number of indices i with 0 <= i < len(rectangles) and rectangles[i][1] >= points[j][1].
    Preconditions: Let n = len(rectangles) and m = len(points). We have 1 <= n <= 50000 and 1 <= m <= 50000. For every i with 0 <= i < n, rectangles[i] has length 2 and its entries satisfy 1 <= rectangles[i][0] <= 10^9 and 1 <= rectangles[i][1] <= 100. For every j with 0 <= j < m, points[j] has length 2 and its entries satisfy 1 <= points[j][0] <= 10^9 and 1 <= points[j][1] <= 100. The points are pairwise distinct: if 0 <= j < k < m then (points[j][0], points[j][1]) != (points[k][0], points[k][1]). -/
  theorem spec_6
      (rectangles points : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
      (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
      (hrect : RectanglesWellFormed rectangles)
      (hpts : PointsWellFormed points)
      (hdist : PointsDistinct points)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r) :
      ∀ j : Nat, j < points.val.length → j < r.val.length →
        outAt r j ≤
          (countIndices rectangles.val.length
            (fun i => decide (yAt points j ≤ yAt rectangles i)) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (rectangles points : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
        (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
        (hrect : RectanglesWellFormed rectangles)
        (hpts : PointsWellFormed points)
        (hdist : PointsDistinct points)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r), ∀ j : Nat, j < points.val.length → j < r.val.length →
          outAt r j ≤
            (countIndices rectangles.val.length
              (fun i => decide (yAt points j ≤ yAt rectangles i)) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(points) and j < len(r), r[j] is at most the number of indices i with 0 <= i < len(rectangles) and rectangles[i][0] >= points[j][0].
    Preconditions: Let n = len(rectangles) and m = len(points). We have 1 <= n <= 50000 and 1 <= m <= 50000. For every i with 0 <= i < n, rectangles[i] has length 2 and its entries satisfy 1 <= rectangles[i][0] <= 10^9 and 1 <= rectangles[i][1] <= 100. For every j with 0 <= j < m, points[j] has length 2 and its entries satisfy 1 <= points[j][0] <= 10^9 and 1 <= points[j][1] <= 100. The points are pairwise distinct: if 0 <= j < k < m then (points[j][0], points[j][1]) != (points[k][0], points[k][1]). -/
  theorem spec_7
      (rectangles points : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
      (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
      (hrect : RectanglesWellFormed rectangles)
      (hpts : PointsWellFormed points)
      (hdist : PointsDistinct points)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r) :
      ∀ j : Nat, j < points.val.length → j < r.val.length →
        outAt r j ≤
          (countIndices rectangles.val.length
            (fun i => decide (xAt points j ≤ xAt rectangles i)) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (rectangles points : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
        (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
        (hrect : RectanglesWellFormed rectangles)
        (hpts : PointsWellFormed points)
        (hdist : PointsDistinct points)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r), ∀ j : Nat, j < points.val.length → j < r.val.length →
          outAt r j ≤
            (countIndices rectangles.val.length
              (fun i => decide (xAt points j ≤ xAt rectangles i)) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(points), j < len(r), and points[j][1] = 100, r[j] is equal to the number of indices i with 0 <= i < len(rectangles), rectangles[i][1] = 100, and rectangles[i][0] >= points[j][0].
    Preconditions: Let n = len(rectangles) and m = len(points). We have 1 <= n <= 50000 and 1 <= m <= 50000. For every i with 0 <= i < n, rectangles[i] has length 2 and its entries satisfy 1 <= rectangles[i][0] <= 10^9 and 1 <= rectangles[i][1] <= 100. For every j with 0 <= j < m, points[j] has length 2 and its entries satisfy 1 <= points[j][0] <= 10^9 and 1 <= points[j][1] <= 100. The points are pairwise distinct: if 0 <= j < k < m then (points[j][0], points[j][1]) != (points[k][0], points[k][1]). -/
  theorem spec_8
      (rectangles points : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
      (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
      (hrect : RectanglesWellFormed rectangles)
      (hpts : PointsWellFormed points)
      (hdist : PointsDistinct points)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r) :
      ∀ j : Nat, j < points.val.length → j < r.val.length → yAt points j = 100 →
        outAt r j =
          (countIndices rectangles.val.length
            (fun i => decide (yAt rectangles i = 100 ∧ xAt points j ≤ xAt rectangles i)) : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (rectangles points : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
        (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
        (hrect : RectanglesWellFormed rectangles)
        (hpts : PointsWellFormed points)
        (hdist : PointsDistinct points)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r), ∀ j : Nat, j < points.val.length → j < r.val.length → yAt points j = 100 →
          outAt r j =
            (countIndices rectangles.val.length
              (fun i => decide (yAt rectangles i = 100 ∧ xAt points j ≤ xAt rectangles i)) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(points), j < len(r), and points[j][0] = 1000000000, r[j] is equal to the number of indices i with 0 <= i < len(rectangles), rectangles[i][0] = 1000000000, and rectangles[i][1] >= points[j][1].
    Preconditions: Let n = len(rectangles) and m = len(points). We have 1 <= n <= 50000 and 1 <= m <= 50000. For every i with 0 <= i < n, rectangles[i] has length 2 and its entries satisfy 1 <= rectangles[i][0] <= 10^9 and 1 <= rectangles[i][1] <= 100. For every j with 0 <= j < m, points[j] has length 2 and its entries satisfy 1 <= points[j][0] <= 10^9 and 1 <= points[j][1] <= 100. The points are pairwise distinct: if 0 <= j < k < m then (points[j][0], points[j][1]) != (points[k][0], points[k][1]). -/
  theorem spec_9
      (rectangles points : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
      (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
      (hrect : RectanglesWellFormed rectangles)
      (hpts : PointsWellFormed points)
      (hdist : PointsDistinct points)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r) :
      ∀ j : Nat, j < points.val.length → j < r.val.length → xAt points j = 1000000000 →
        outAt r j =
          (countIndices rectangles.val.length
            (fun i =>
              decide (xAt rectangles i = 1000000000 ∧ yAt points j ≤ yAt rectangles i)) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (rectangles points : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
        (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
        (hrect : RectanglesWellFormed rectangles)
        (hpts : PointsWellFormed points)
        (hdist : PointsDistinct points)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r), ∀ j : Nat, j < points.val.length → j < r.val.length → xAt points j = 1000000000 →
          outAt r j =
            (countIndices rectangles.val.length
              (fun i =>
                decide (xAt rectangles i = 1000000000 ∧ yAt points j ≤ yAt rectangles i)) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(points), j < len(r), and points[j][1] = 1, r[j] is equal to the number of indices i with 0 <= i < len(rectangles) and rectangles[i][0] >= points[j][0].
    Preconditions: Let n = len(rectangles) and m = len(points). We have 1 <= n <= 50000 and 1 <= m <= 50000. For every i with 0 <= i < n, rectangles[i] has length 2 and its entries satisfy 1 <= rectangles[i][0] <= 10^9 and 1 <= rectangles[i][1] <= 100. For every j with 0 <= j < m, points[j] has length 2 and its entries satisfy 1 <= points[j][0] <= 10^9 and 1 <= points[j][1] <= 100. The points are pairwise distinct: if 0 <= j < k < m then (points[j][0], points[j][1]) != (points[k][0], points[k][1]). -/
  theorem spec_10
      (rectangles points : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
      (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
      (hrect : RectanglesWellFormed rectangles)
      (hpts : PointsWellFormed points)
      (hdist : PointsDistinct points)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r) :
      ∀ j : Nat, j < points.val.length → j < r.val.length → yAt points j = 1 →
        outAt r j =
          (countIndices rectangles.val.length
            (fun i => decide (xAt points j ≤ xAt rectangles i)) : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (rectangles points : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
        (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
        (hrect : RectanglesWellFormed rectangles)
        (hpts : PointsWellFormed points)
        (hdist : PointsDistinct points)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r), ∀ j : Nat, j < points.val.length → j < r.val.length → yAt points j = 1 →
          outAt r j =
            (countIndices rectangles.val.length
              (fun i => decide (xAt points j ≤ xAt rectangles i)) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(points), j < len(r), and points[j][0] = 1, r[j] is equal to the number of indices i with 0 <= i < len(rectangles) and rectangles[i][1] >= points[j][1].
    Preconditions: Let n = len(rectangles) and m = len(points). We have 1 <= n <= 50000 and 1 <= m <= 50000. For every i with 0 <= i < n, rectangles[i] has length 2 and its entries satisfy 1 <= rectangles[i][0] <= 10^9 and 1 <= rectangles[i][1] <= 100. For every j with 0 <= j < m, points[j] has length 2 and its entries satisfy 1 <= points[j][0] <= 10^9 and 1 <= points[j][1] <= 100. The points are pairwise distinct: if 0 <= j < k < m then (points[j][0], points[j][1]) != (points[k][0], points[k][1]). -/
  theorem spec_11
      (rectangles points : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
      (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
      (hrect : RectanglesWellFormed rectangles)
      (hpts : PointsWellFormed points)
      (hdist : PointsDistinct points)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r) :
      ∀ j : Nat, j < points.val.length → j < r.val.length → xAt points j = 1 →
        outAt r j =
          (countIndices rectangles.val.length
            (fun i => decide (yAt points j ≤ yAt rectangles i)) : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (rectangles points : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
        (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
        (hrect : RectanglesWellFormed rectangles)
        (hpts : PointsWellFormed points)
        (hdist : PointsDistinct points)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r), ∀ j : Nat, j < points.val.length → j < r.val.length → xAt points j = 1 →
          outAt r j =
            (countIndices rectangles.val.length
              (fun i => decide (yAt points j ≤ yAt rectangles i)) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, the sum of r[j] over all j with 0 <= j < len(points) and j < len(r) equals the number of pairs (i,j) with 0 <= i < len(rectangles), 0 <= j < len(points), j < len(r), points[j][0] <= rectangles[i][0], and points[j][1] <= rectangles[i][1].
    Preconditions: Let n = len(rectangles) and m = len(points). We have 1 <= n <= 50000 and 1 <= m <= 50000. For every i with 0 <= i < n, rectangles[i] has length 2 and its entries satisfy 1 <= rectangles[i][0] <= 10^9 and 1 <= rectangles[i][1] <= 100. For every j with 0 <= j < m, points[j] has length 2 and its entries satisfy 1 <= points[j][0] <= 10^9 and 1 <= points[j][1] <= 100. The points are pairwise distinct: if 0 <= j < k < m then (points[j][0], points[j][1]) != (points[k][0], points[k][1]). -/
  theorem spec_12
      (rectangles points : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
      (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
      (hrect : RectanglesWellFormed rectangles)
      (hpts : PointsWellFormed points)
      (hdist : PointsDistinct points)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r) :
      sumOut r (Nat.min points.val.length r.val.length) =
        (countPairs rectangles points (Nat.min points.val.length r.val.length) : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (rectangles points : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ rectangles.val.length) (hn_hi : rectangles.val.length ≤ 50000)
        (hm_lo : 1 ≤ points.val.length) (hm_hi : points.val.length ≤ 50000)
        (hrect : RectanglesWellFormed rectangles)
        (hpts : PointsWellFormed points)
        (hdist : PointsDistinct points)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.CountRectangles.count_rectangles rectangles points = ok r), sumOut r (Nat.min points.val.length r.val.length) =
          (countPairs rectangles points (Nat.min points.val.length r.val.length) : Int)) := by
    sorry

  end AegisSpec.CountRectangles
