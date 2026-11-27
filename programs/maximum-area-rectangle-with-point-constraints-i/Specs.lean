import Aegis.MaxRectangleArea.Code.Funs

/-!
# Specifications of `Aegis.MaxRectangleArea.max_rectangle_area`

LeetCode problem `maximum-area-rectangle-with-point-constraints-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxRectangleArea

  open Aegis.MaxRectangleArea

  abbrev PointList := Slice (alloc.vec.Vec Std.I64)

  def entryCoords (v : alloc.vec.Vec Std.I64) : Option (ℤ × ℤ) :=
    match v.val with
    | [x, y] => some (x.val, y.val)
    | _ => none

  def coords (points : PointList) : List (ℤ × ℤ) :=
    (points.val.map entryCoords).filterMap id

  def entriesInBox (points : PointList) : Prop :=
    ∀ v ∈ points.val, v.val.length = 2 ∧ ∀ z ∈ v.val, 0 ≤ z.val ∧ z.val ≤ 100

  def pairwiseDistinct (points : PointList) : Prop := (coords points).Nodup

  def inClosedBox (a c b d : ℤ) (p : ℤ × ℤ) : Prop :=
    a ≤ p.1 ∧ p.1 ≤ c ∧ b ≤ p.2 ∧ p.2 ≤ d

  def rectArea (a c b d : ℤ) : ℤ := (c - a) * (d - b)

  def validRect (pts : List (ℤ × ℤ)) (a c b d : ℤ) : Prop :=
    a < c ∧ b < d ∧ (a, b) ∈ pts ∧ (a, d) ∈ pts ∧ (c, b) ∈ pts ∧ (c, d) ∈ pts ∧
      ∀ p ∈ pts,
        inClosedBox a c b d p → p = (a, b) ∨ p = (a, d) ∨ p = (c, b) ∨ p = (c, d)

  def hasValidRect (pts : List (ℤ × ℤ)) : Prop := ∃ a c b d : ℤ, validRect pts a c b d

  def isCornerSet (pts : List (ℤ × ℤ)) (a c b d : ℤ) : Prop :=
    List.Perm pts [(a, b), (a, d), (c, b), (c, d)]

  def listMax : List ℤ → ℤ
    | [] => 0
    | x :: xs => xs.foldr max x

  def listMin : List ℤ → ℤ
    | [] => 0
    | x :: xs => xs.foldr min x

  def maxX (pts : List (ℤ × ℤ)) : ℤ := listMax (pts.map Prod.fst)

  def minX (pts : List (ℤ × ℤ)) : ℤ := listMin (pts.map Prod.fst)

  def maxY (pts : List (ℤ × ℤ)) : ℤ := listMax (pts.map Prod.snd)

  def minY (pts : List (ℤ × ℤ)) : ℤ := listMin (pts.map Prod.snd)

  /-- Whenever the function returns a result r, the following holds. Call an axis-aligned rectangle valid for points if its four corners are four distinct input points and no other input point lies inside or on the border of the rectangle; its area is width*height. If at least one valid rectangle exists, then r equals the maximum area among all valid rectangles; in particular r != -1 and there is a valid rectangle of area r. If no valid rectangle exists, then r = -1.
    Preconditions: points is a slice with 1 <= len(points) <= 10; for every i with 0 <= i < len(points), points[i] has length 2 and 0 <= points[i][0] <= 100 and 0 <= points[i][1] <= 100; for every i,j with 0 <= i < j < len(points), points[i] != points[j]. -/
  theorem spec_1 (points : PointList)
      (hcard : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
      (hpoints : entriesInBox points)
      (hdistinct : pairwiseDistinct points) :
      ∀ r : Std.I64, max_rectangle_area points = ok r →
        (hasValidRect (coords points) →
          r.val ≠ (-1) ∧
          (∃ a c b d : ℤ, validRect (coords points) a c b d ∧ rectArea a c b d = r.val) ∧
          (∀ a c b d : ℤ, validRect (coords points) a c b d → rectArea a c b d ≤ r.val)) ∧
        ((¬ hasValidRect (coords points)) → r.val = (-1)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (points : PointList)
        (hcard : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
        (hpoints : entriesInBox points)
        (hdistinct : pairwiseDistinct points), ∀ r : Std.I64, max_rectangle_area points = ok r →
          (hasValidRect (coords points) →
            r.val ≠ (-1) ∧
            (∃ a c b d : ℤ, validRect (coords points) a c b d ∧ rectArea a c b d = r.val) ∧
            (∀ a c b d : ℤ, validRect (coords points) a c b d → rectArea a c b d ≤ r.val)) ∧
          ((¬ hasValidRect (coords points)) → r.val = (-1))) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (i.e., it does not fail).
    Preconditions: points is a slice with 1 <= len(points) <= 10; for every i with 0 <= i < len(points), points[i] has length 2 and 0 <= points[i][0] <= 100 and 0 <= points[i][1] <= 100; for every i,j with 0 <= i < j < len(points), points[i] != points[j]. -/
  theorem spec_2 (points : PointList)
      (hcard : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
      (hpoints : entriesInBox points)
      (hdistinct : pairwiseDistinct points) :
      ∃ r : Std.I64, max_rectangle_area points = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (points : PointList)
        (hcard : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
        (hpoints : entriesInBox points)
        (hdistinct : pairwiseDistinct points), ∃ r : Std.I64, max_rectangle_area points = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 1 <= r <= 10000.
    Preconditions: points is a slice with 1 <= len(points) <= 10; for every i with 0 <= i < len(points), points[i] has length 2 and 0 <= points[i][0] <= 100 and 0 <= points[i][1] <= 100; for every i,j with 0 <= i < j < len(points), points[i] != points[j]. -/
  theorem spec_3 (points : PointList)
      (hcard : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
      (hpoints : entriesInBox points)
      (hdistinct : pairwiseDistinct points) :
      ∀ r : Std.I64, max_rectangle_area points = ok r →
        r.val = (-1) ∨ (1 ≤ r.val ∧ r.val ≤ 10000) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (points : PointList)
        (hcard : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
        (hpoints : entriesInBox points)
        (hdistinct : pairwiseDistinct points), ∀ r : Std.I64, max_rectangle_area points = ok r →
          r.val = (-1) ∨ (1 ≤ r.val ∧ r.val ≤ 10000)) := by
    sorry

  /-- Whenever the function returns a result r, r = -1.
    Preconditions: points is a slice with 1 <= len(points) < 4; for every i with 0 <= i < len(points), points[i] has length 2 and 0 <= points[i][0] <= 100 and 0 <= points[i][1] <= 100; for every i,j with 0 <= i < j < len(points), points[i] != points[j]. -/
  theorem spec_4 (points : PointList)
      (hcard : 1 ≤ points.val.length ∧ points.val.length < 4)
      (hpoints : entriesInBox points)
      (hdistinct : pairwiseDistinct points) :
      ∀ r : Std.I64, max_rectangle_area points = ok r → r.val = (-1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (points : PointList)
        (hcard : 1 ≤ points.val.length ∧ points.val.length < 4)
        (hpoints : entriesInBox points)
        (hdistinct : pairwiseDistinct points), ∀ r : Std.I64, max_rectangle_area points = ok r → r.val = (-1)) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, there exist four input points that are the corners of an axis-aligned rectangle of positive width and height, no other input point lies inside or on the border of that rectangle, and width*height = r.
    Preconditions: points is a slice with 1 <= len(points) <= 10; for every i with 0 <= i < len(points), points[i] has length 2 and 0 <= points[i][0] <= 100 and 0 <= points[i][1] <= 100; for every i,j with 0 <= i < j < len(points), points[i] != points[j]. -/
  theorem spec_5 (points : PointList)
      (hcard : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
      (hpoints : entriesInBox points)
      (hdistinct : pairwiseDistinct points) :
      ∀ r : Std.I64, max_rectangle_area points = ok r → r.val ≠ (-1) →
        ∃ a c b d : ℤ, validRect (coords points) a c b d ∧ rectArea a c b d = r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (points : PointList)
        (hcard : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
        (hpoints : entriesInBox points)
        (hdistinct : pairwiseDistinct points), ∀ r : Std.I64, max_rectangle_area points = ok r → r.val ≠ (-1) →
          ∃ a c b d : ℤ, validRect (coords points) a c b d ∧ rectArea a c b d = r.val) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, for every axis-aligned rectangle whose four corners are input points, which has positive width and height, and which contains no other input point inside or on its border, the area of that rectangle is at most r.
    Preconditions: points is a slice with 1 <= len(points) <= 10; for every i with 0 <= i < len(points), points[i] has length 2 and 0 <= points[i][0] <= 100 and 0 <= points[i][1] <= 100; for every i,j with 0 <= i < j < len(points), points[i] != points[j]. -/
  theorem spec_6 (points : PointList)
      (hcard : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
      (hpoints : entriesInBox points)
      (hdistinct : pairwiseDistinct points) :
      ∀ r : Std.I64, max_rectangle_area points = ok r → r.val ≠ (-1) →
        ∀ a c b d : ℤ, validRect (coords points) a c b d → rectArea a c b d ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (points : PointList)
        (hcard : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
        (hpoints : entriesInBox points)
        (hdistinct : pairwiseDistinct points), ∀ r : Std.I64, max_rectangle_area points = ok r → r.val ≠ (-1) →
          ∀ a c b d : ℤ, validRect (coords points) a c b d → rectArea a c b d ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r with r = -1, there is no axis-aligned rectangle with positive width and height whose four corners are input points and which contains no other input point inside or on its border.
    Preconditions: points is a slice with 1 <= len(points) <= 10; for every i with 0 <= i < len(points), points[i] has length 2 and 0 <= points[i][0] <= 100 and 0 <= points[i][1] <= 100; for every i,j with 0 <= i < j < len(points), points[i] != points[j]. -/
  theorem spec_7 (points : PointList)
      (hcard : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
      (hpoints : entriesInBox points)
      (hdistinct : pairwiseDistinct points) :
      ∀ r : Std.I64, max_rectangle_area points = ok r → r.val = (-1) →
        ¬ hasValidRect (coords points) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (points : PointList)
        (hcard : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
        (hpoints : entriesInBox points)
        (hdistinct : pairwiseDistinct points), ∀ r : Std.I64, max_rectangle_area points = ok r → r.val = (-1) →
          ¬ hasValidRect (coords points)) := by
    sorry

  /-- Whenever the function returns a result r, r != -1 if and only if the four input points are exactly the four corners of some axis-aligned rectangle with positive width and height; when this holds, r = (max_x - min_x)*(max_y - min_y), where max_x and min_x are the maximum and minimum x-coordinates among the four input points and max_y and min_y are the maximum and minimum y-coordinates among the four input points; when this does not hold, r = -1.
    Preconditions: points is a slice with len(points) = 4; for every i with 0 <= i < len(points), points[i] has length 2 and 0 <= points[i][0] <= 100 and 0 <= points[i][1] <= 100; for every i,j with 0 <= i < j < len(points), points[i] != points[j]. -/
  theorem spec_8 (points : PointList)
      (hcard : points.val.length = 4)
      (hpoints : entriesInBox points)
      (hdistinct : pairwiseDistinct points) :
      ∀ r : Std.I64, max_rectangle_area points = ok r →
        ((r.val ≠ (-1) ↔
            ∃ a c b d : ℤ, a < c ∧ b < d ∧ isCornerSet (coords points) a c b d) ∧
          ((∃ a c b d : ℤ, a < c ∧ b < d ∧ isCornerSet (coords points) a c b d) →
            r.val =
              (maxX (coords points) - minX (coords points)) *
                (maxY (coords points) - minY (coords points))) ∧
          ((¬ ∃ a c b d : ℤ, a < c ∧ b < d ∧ isCornerSet (coords points) a c b d) →
            r.val = (-1))) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (points : PointList)
        (hcard : points.val.length = 4)
        (hpoints : entriesInBox points)
        (hdistinct : pairwiseDistinct points), ∀ r : Std.I64, max_rectangle_area points = ok r →
          ((r.val ≠ (-1) ↔
              ∃ a c b d : ℤ, a < c ∧ b < d ∧ isCornerSet (coords points) a c b d) ∧
            ((∃ a c b d : ℤ, a < c ∧ b < d ∧ isCornerSet (coords points) a c b d) →
              r.val =
                (maxX (coords points) - minX (coords points)) *
                  (maxY (coords points) - minY (coords points))) ∧
            ((¬ ∃ a c b d : ℤ, a < c ∧ b < d ∧ isCornerSet (coords points) a c b d) →
              r.val = (-1)))) := by
    sorry

  /-- Whenever the function returns r on points and r' on points', r = r'.
    Preconditions: points and points' each satisfy: 1 <= len <= 10; every entry has length 2 with coordinates in [0,100]; all coordinate pairs are distinct. Also, points' is a permutation of points (the same multiset of coordinate pairs). -/
  theorem spec_9 (points points' : PointList)
      (hcard : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
      (hpoints : entriesInBox points)
      (hdistinct : pairwiseDistinct points)
      (hcard' : 1 ≤ points'.val.length ∧ points'.val.length ≤ 10)
      (hpoints' : entriesInBox points')
      (hdistinct' : pairwiseDistinct points')
      (hperm : List.Perm (coords points') (coords points)) :
      ∀ r r' : Std.I64, max_rectangle_area points = ok r →
        max_rectangle_area points' = ok r' → r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (points points' : PointList)
        (hcard : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
        (hpoints : entriesInBox points)
        (hdistinct : pairwiseDistinct points)
        (hcard' : 1 ≤ points'.val.length ∧ points'.val.length ≤ 10)
        (hpoints' : entriesInBox points')
        (hdistinct' : pairwiseDistinct points')
        (hperm : List.Perm (coords points') (coords points)), ∀ r r' : Std.I64, max_rectangle_area points = ok r →
          max_rectangle_area points' = ok r' → r = r') := by
    sorry

  /-- Whenever the function returns a result r with r != -1, r <= (max_x - min_x)*(max_y - min_y), where max_x and min_x are the maximum and minimum x-coordinates among all input points, and max_y and min_y are the maximum and minimum y-coordinates among all input points.
    Preconditions: points is a slice with 1 <= len(points) <= 10; for every i with 0 <= i < len(points), points[i] has length 2 and 0 <= points[i][0] <= 100 and 0 <= points[i][1] <= 100; for every i,j with 0 <= i < j < len(points), points[i] != points[j]. -/
  theorem spec_10 (points : PointList)
      (hcard : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
      (hpoints : entriesInBox points)
      (hdistinct : pairwiseDistinct points) :
      ∀ r : Std.I64, max_rectangle_area points = ok r → r.val ≠ (-1) →
        r.val ≤
          (maxX (coords points) - minX (coords points)) *
            (maxY (coords points) - minY (coords points)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (points : PointList)
        (hcard : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
        (hpoints : entriesInBox points)
        (hdistinct : pairwiseDistinct points), ∀ r : Std.I64, max_rectangle_area points = ok r → r.val ≠ (-1) →
          r.val ≤
            (maxX (coords points) - minX (coords points)) *
              (maxY (coords points) - minY (coords points))) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, there exist distinct indices i,j,k,l with 0 <= i,j,k,l < len(points) and integers a < c and b < d such that points[i][0] = a, points[i][1] = b, points[j][0] = a, points[j][1] = d, points[k][0] = c, points[k][1] = b, points[l][0] = c, points[l][1] = d, and r = (c-a)*(d-b).
    Preconditions: points is a slice with 1 <= len(points) <= 10; for every i with 0 <= i < len(points), points[i] has length 2 and 0 <= points[i][0] <= 100 and 0 <= points[i][1] <= 100; for every i,j with 0 <= i < j < len(points), points[i] != points[j]. -/
  theorem spec_11 (points : PointList)
      (hcard : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
      (hpoints : entriesInBox points)
      (hdistinct : pairwiseDistinct points) :
      ∀ r : Std.I64, max_rectangle_area points = ok r → r.val ≠ (-1) →
        ∃ (i j k l : ℕ) (a b c d : ℤ),
          i < (coords points).length ∧ j < (coords points).length ∧
            k < (coords points).length ∧ l < (coords points).length ∧
            i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
            a < c ∧ b < d ∧
            (coords points)[i]? = some (a, b) ∧
            (coords points)[j]? = some (a, d) ∧
            (coords points)[k]? = some (c, b) ∧
            (coords points)[l]? = some (c, d) ∧
            r.val = (c - a) * (d - b) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (points : PointList)
        (hcard : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
        (hpoints : entriesInBox points)
        (hdistinct : pairwiseDistinct points), ∀ r : Std.I64, max_rectangle_area points = ok r → r.val ≠ (-1) →
          ∃ (i j k l : ℕ) (a b c d : ℤ),
            i < (coords points).length ∧ j < (coords points).length ∧
              k < (coords points).length ∧ l < (coords points).length ∧
              i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
              a < c ∧ b < d ∧
              (coords points)[i]? = some (a, b) ∧
              (coords points)[j]? = some (a, d) ∧
              (coords points)[k]? = some (c, b) ∧
              (coords points)[l]? = some (c, d) ∧
              r.val = (c - a) * (d - b)) := by
    sorry

  end AegisSpec.MaxRectangleArea
