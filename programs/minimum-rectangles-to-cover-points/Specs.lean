import Aegis.MinRectanglesToCoverPoints.Code.Funs

/-!
# Specifications of `Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points`

LeetCode problem `minimum-rectangles-to-cover-points`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinRectanglesToCoverPoints

  def coordsOf (p : alloc.vec.Vec Std.I64) : List ℤ := p.val.map (fun z => z.val)

  def xOf (p : alloc.vec.Vec Std.I64) : ℤ := (coordsOf p).getD 0 0

  def yOf (p : alloc.vec.Vec Std.I64) : ℤ := (coordsOf p).getD 1 0

  def xsOf (points : Slice (alloc.vec.Vec Std.I64)) : List ℤ := points.val.map xOf

  def xAt (points : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ := (xsOf points).getD i 0

  def xSetOf (points : Slice (alloc.vec.Vec Std.I64)) : Finset ℤ := (xsOf points).toFinset

  def distinctXCount (points : Slice (alloc.vec.Vec Std.I64)) : ℕ := (xSetOf points).card

  def maxX (points : Slice (alloc.vec.Vec Std.I64)) : ℤ := (xsOf points).foldr max 0

  def minX (points : Slice (alloc.vec.Vec Std.I64)) : ℤ := (xsOf points).foldr min 0

  structure WRect where

    a : ℤ

    b : ℤ

    Y : ℤ
    deriving DecidableEq, Repr

  namespace WRect

  def IsW (R : WRect) (w : ℤ) : Prop := R.a ≤ R.b ∧ 0 ≤ R.Y ∧ R.b - R.a ≤ w

  def Covers (R : WRect) (p : alloc.vec.Vec Std.I64) : Prop :=
    R.a ≤ xOf p ∧ xOf p ≤ R.b ∧ yOf p ≤ R.Y

  end WRect

  def AllWRects (w : ℤ) (Rs : List WRect) : Prop := ∀ R ∈ Rs, R.IsW w

  def CoversPoints (Rs : List WRect) (points : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ p ∈ points.val, ∃ R ∈ Rs, R.Covers p

  def IsCover (w : ℤ) (Rs : List WRect) (points : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    AllWRects w Rs ∧ CoversPoints Rs points

  def IsMinRectCover (points : Slice (alloc.vec.Vec Std.I64)) (w : ℤ) (k : ℤ) : Prop :=
    (∃ Rs : List WRect, (Rs.length : ℤ) = k ∧ IsCover w Rs points) ∧
      ∀ k' : ℤ, 0 ≤ k' → k' < k →
        ¬ ∃ Rs : List WRect, (Rs.length : ℤ) = k' ∧ IsCover w Rs points

  def SparseIndexSet (points : Slice (alloc.vec.Vec Std.I64)) (w : ℤ) (S : Finset ℕ) : Prop :=
    (∀ i ∈ S, i < points.val.length) ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → w < |xAt points i - xAt points j|

  def Partitionable (points : Slice (alloc.vec.Vec Std.I64)) (w : ℤ) (k : ℕ) : Prop :=
    ∃ g : (i : ℕ) → i < points.val.length → Fin k,
      (∀ t : Fin k, ∃ (i : ℕ) (hi : i < points.val.length), g i hi = t) ∧
        (∀ (i j : ℕ) (hi : i < points.val.length) (hj : j < points.val.length),
          g i hi = g j hj → |xAt points i - xAt points j| ≤ w)

  def ValidInput (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64) : Prop :=
    1 ≤ points.val.length ∧
      points.val.length ≤ 100000 ∧
      (∀ p ∈ points.val,
        (coordsOf p).length = 2 ∧
          0 ≤ xOf p ∧ xOf p ≤ 10 ^ 9 ∧ 0 ≤ yOf p ∧ yOf p ≤ 10 ^ 9) ∧
      0 ≤ w.val ∧ w.val ≤ 10 ^ 9 ∧
      (points.val.map (fun p => (xOf p, yOf p))).Nodup

  /-- The function returns a result r, and r is the minimum number of w-rectangles needed to cover all points: (i) there exists a cover of all points by r w-rectangles, and (ii) for every integer k with 0 <= k < r, no cover of all points by k w-rectangles exists. Here a w-rectangle is a rectangle [a,b] x [0,Y] with a <= b, Y >= 0, and b-a <= w; it covers a point p iff a <= p[0] <= b and p[1] <= Y.
    Preconditions: len(points) >= 1 and len(points) <= 100000; for every i with 0 <= i < len(points), len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9; 0 <= w <= 10^9; all pairs (points[i][0], points[i][1]) are distinct. -/
  theorem spec_1 (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
      (h : ValidInput points w) :
      ∃ r : Std.I64,
        Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
          IsMinRectCover points w.val r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
        (h : ValidInput points w), ∃ r : Std.I64,
          Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
            IsMinRectCover points w.val r.val) := by
    sorry

  /-- The function returns a Std.I64 result r (it does not fail, overflow, panic, or access out of bounds) for every input satisfying the preconditions.
    Preconditions: len(points) >= 1 and len(points) <= 100000; for every i with 0 <= i < len(points), len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9; 0 <= w <= 10^9; all pairs (points[i][0], points[i][1]) are distinct. -/
  theorem spec_2 (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
      (h : ValidInput points w) :
      ∃ r : Std.I64,
        Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
        (h : ValidInput points w), ∃ r : Std.I64,
          Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r) := by
    sorry

  /-- The function returns a result r and r >= 1.
    Preconditions: len(points) >= 1 and len(points) <= 100000; for every i with 0 <= i < len(points), len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9; 0 <= w <= 10^9; all pairs (points[i][0], points[i][1]) are distinct. -/
  theorem spec_3 (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
      (h : ValidInput points w) :
      ∃ r : Std.I64,
        Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
          1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
        (h : ValidInput points w), ∃ r : Std.I64,
          Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
            1 ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= len(points).
    Preconditions: len(points) >= 1 and len(points) <= 100000; for every i with 0 <= i < len(points), len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9; 0 <= w <= 10^9; all pairs (points[i][0], points[i][1]) are distinct. -/
  theorem spec_4 (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
      (h : ValidInput points w) :
      ∃ r : Std.I64,
        Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
          r.val ≤ (points.val.length : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
        (h : ValidInput points w), ∃ r : Std.I64,
          Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
            r.val ≤ (points.val.length : ℤ)) := by
    sorry

  /-- The function returns a result r and r <= |{points[i][0] : 0 <= i < len(points)}|, the number of distinct x-coordinates among the points.
    Preconditions: len(points) >= 1 and len(points) <= 100000; for every i with 0 <= i < len(points), len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9; 0 <= w <= 10^9; all pairs (points[i][0], points[i][1]) are distinct. -/
  theorem spec_5 (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
      (h : ValidInput points w) :
      ∃ r : Std.I64,
        Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
          r.val ≤ (distinctXCount points : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
        (h : ValidInput points w), ∃ r : Std.I64,
          Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
            r.val ≤ (distinctXCount points : ℤ)) := by
    sorry

  /-- The function returns a result r and r = |{points[i][0] : 0 <= i < len(points)}|.
    Preconditions: len(points) >= 1 and len(points) <= 100000; for every i with 0 <= i < len(points), len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9; w = 0; all pairs (points[i][0], points[i][1]) are distinct. -/
  theorem spec_6 (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
      (h : ValidInput points w) (hw : w.val = 0) :
      ∃ r : Std.I64,
        Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
          r.val = (distinctXCount points : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
        (h : ValidInput points w) (hw : w.val = 0), ∃ r : Std.I64,
          Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
            r.val = (distinctXCount points : ℤ)) := by
    sorry

  /-- The function returns a result r and r = 1.
    Preconditions: len(points) >= 1 and len(points) <= 100000; for every i with 0 <= i < len(points), len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9; 0 <= w <= 10^9; all pairs (points[i][0], points[i][1]) are distinct; max_{0 <= i < len(points)} points[i][0] - min_{0 <= i < len(points)} points[i][0] <= w. -/
  theorem spec_7 (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
      (h : ValidInput points w) (hwidth : maxX points - minX points ≤ w.val) :
      ∃ r : Std.I64,
        Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
          r.val = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
        (h : ValidInput points w) (hwidth : maxX points - minX points ≤ w.val), ∃ r : Std.I64,
          Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
            r.val = 1) := by
    sorry

  /-- The function returns a result r and r = len(points).
    Preconditions: len(points) >= 1 and len(points) <= 100000; for every i with 0 <= i < len(points), len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9; 0 <= w <= 10^9; all pairs (points[i][0], points[i][1]) are distinct; for every i,j with 0 <= i < j < len(points), |points[i][0] - points[j][0]| > w. -/
  theorem spec_8 (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
      (h : ValidInput points w)
      (hsep : ∀ (i j : ℕ) (hi : i < points.val.length) (hj : j < points.val.length),
        i < j → w.val < |xAt points i - xAt points j|) :
      ∃ r : Std.I64,
        Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
          r.val = (points.val.length : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
        (h : ValidInput points w)
        (hsep : ∀ (i j : ℕ) (hi : i < points.val.length) (hj : j < points.val.length),
          i < j → w.val < |xAt points i - xAt points j|), ∃ r : Std.I64,
          Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
            r.val = (points.val.length : ℤ)) := by
    sorry

  /-- The function returns a result r, and r is the maximum cardinality of a subset S of {0,...,len(points)-1} such that for all distinct i,j in S, |points[i][0] - points[j][0]| > w.
    Preconditions: len(points) >= 1 and len(points) <= 100000; for every i with 0 <= i < len(points), len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9; 0 <= w <= 10^9; all pairs (points[i][0], points[i][1]) are distinct. -/
  theorem spec_9 (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
      (h : ValidInput points w) :
      ∃ r : Std.I64,
        Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
          ∃ S : Finset ℕ,
            SparseIndexSet points w.val S ∧ (S.card : ℤ) = r.val ∧
              ∀ T : Finset ℕ, SparseIndexSet points w.val T → T.card ≤ S.card := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
        (h : ValidInput points w), ∃ r : Std.I64,
          Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
            ∃ S : Finset ℕ,
              SparseIndexSet points w.val S ∧ (S.card : ℤ) = r.val ∧
                ∀ T : Finset ℕ, SparseIndexSet points w.val T → T.card ≤ S.card) := by
    sorry

  /-- The function returns a result r, and r is the smallest integer k such that the index set {0,...,len(points)-1} can be partitioned into k nonempty groups G_1,...,G_k satisfying: for every t with 1 <= t <= k and every i,j in G_t, |points[i][0] - points[j][0]| <= w.
    Preconditions: len(points) >= 1 and len(points) <= 100000; for every i with 0 <= i < len(points), len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9; 0 <= w <= 10^9; all pairs (points[i][0], points[i][1]) are distinct. -/
  theorem spec_10 (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
      (h : ValidInput points w) :
      ∃ (r : Std.I64) (k : ℕ),
        Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
          r.val = (k : ℤ) ∧ Partitionable points w.val k ∧
            ∀ k' : ℕ, k' < k → ¬ Partitionable points w.val k' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
        (h : ValidInput points w), ∃ (r : Std.I64) (k : ℕ),
          Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
            r.val = (k : ℤ) ∧ Partitionable points w.val k ∧
              ∀ k' : ℕ, k' < k → ¬ Partitionable points w.val k') := by
    sorry

  /-- The function returns a result r, and r depends only on the set X = {points[i][0] : 0 <= i < len(points)} and on w: for every valid list q of points with the same set of x-coordinates as points, min_rectangles_to_cover_points(q, w) returns r.
    Preconditions: len(points) >= 1 and len(points) <= 100000; for every i with 0 <= i < len(points), len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9; 0 <= w <= 10^9; all pairs (points[i][0], points[i][1]) are distinct. -/
  theorem spec_11 (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
      (h : ValidInput points w) :
      ∃ r : Std.I64,
        Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
          ∀ q : Slice (alloc.vec.Vec Std.I64), ValidInput q w → xSetOf q = xSetOf points →
            Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points q w = ok r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
        (h : ValidInput points w), ∃ r : Std.I64,
          Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
            ∀ q : Slice (alloc.vec.Vec Std.I64), ValidInput q w → xSetOf q = xSetOf points →
              Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points q w = ok r) := by
    sorry

  /-- The function returns a result r, and for every integer W with W >= w, if r_W is the minimum number of rectangles [a,b] x [0,Y] with a <= b, Y >= 0, and b-a <= W needed to cover the same points, then r_W <= r.
    Preconditions: len(points) >= 1 and len(points) <= 100000; for every i with 0 <= i < len(points), len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9; 0 <= w <= 10^9; all pairs (points[i][0], points[i][1]) are distinct. -/
  theorem spec_12 (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
      (h : ValidInput points w) :
      ∃ r : Std.I64,
        Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
          ∀ (W rW : ℤ), w.val ≤ W → IsMinRectCover points W rW → rW ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
        (h : ValidInput points w), ∃ r : Std.I64,
          Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
            ∀ (W rW : ℤ), w.val ≤ W → IsMinRectCover points W rW → rW ≤ r.val) := by
    sorry

  /-- The function returns a result r, and there exist r w-rectangles that together cover all points (a w-rectangle is [a,b] x [0,Y] with a <= b, Y >= 0, b-a <= w, and it covers p iff a <= p[0] <= b and p[1] <= Y).
    Preconditions: len(points) >= 1 and len(points) <= 100000; for every i with 0 <= i < len(points), len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9; 0 <= w <= 10^9; all pairs (points[i][0], points[i][1]) are distinct. -/
  theorem spec_13 (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
      (h : ValidInput points w) :
      ∃ r : Std.I64,
        Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
          ∃ Rs : List WRect, (Rs.length : ℤ) = r.val ∧ IsCover w.val Rs points := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
        (h : ValidInput points w), ∃ r : Std.I64,
          Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
            ∃ Rs : List WRect, (Rs.length : ℤ) = r.val ∧ IsCover w.val Rs points) := by
    sorry

  /-- The function returns a result r, and for every integer k with 0 <= k < r, there do not exist k w-rectangles that cover all points (with w-rectangle defined as above).
    Preconditions: len(points) >= 1 and len(points) <= 100000; for every i with 0 <= i < len(points), len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9; 0 <= w <= 10^9; all pairs (points[i][0], points[i][1]) are distinct. -/
  theorem spec_14 (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
      (h : ValidInput points w) :
      ∃ r : Std.I64,
        Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
          ∀ k : ℤ, 0 ≤ k → k < r.val →
            ¬ ∃ Rs : List WRect, (Rs.length : ℤ) = k ∧ IsCover w.val Rs points := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (w : Std.I64)
        (h : ValidInput points w), ∃ r : Std.I64,
          Aegis.MinRectanglesToCoverPoints.min_rectangles_to_cover_points points w = ok r ∧
            ∀ k : ℤ, 0 ≤ k → k < r.val →
              ¬ ∃ Rs : List WRect, (Rs.length : ℤ) = k ∧ IsCover w.val Rs points) := by
    sorry

  end AegisSpec.MinRectanglesToCoverPoints
