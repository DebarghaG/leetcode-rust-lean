import Aegis.NearestValidPoint.Code.Funs

/-!
# Specifications of `Aegis.NearestValidPoint.nearest_valid_point`

LeetCode problem `find-nearest-point-that-has-the-same-x-or-y-coordinate`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NearestValidPoint

  abbrev Points : Type := Aeneas.Std.Slice (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)

  def coord (points : Points) (i j : ℕ) : ℤ :=
    ((points.val[i]?).bind (fun v => (v.val[j]?).map (fun a => a.val))).getD 0

  def manhattanDist (x y : Std.I64) (points : Points) (i : ℕ) : ℤ :=
    |coord points i 0 - x.val| + |coord points i 1 - y.val|

  def Matches (x y : Std.I64) (points : Points) (i : ℕ) : Prop :=
    coord points i 0 = x.val ∨ coord points i 1 = y.val

  def ValidPoint (v : alloc.vec.Vec Std.I64) : Prop :=
    v.val.length = 2 ∧
      ∃ px py : Std.I64, v.val = [px, py] ∧
        1 ≤ px.val ∧ px.val ≤ 10000 ∧ 1 ≤ py.val ∧ py.val ≤ 10000

  def ValidInput (x y : Std.I64) (points : Points) : Prop :=
    1 ≤ points.val.length ∧ points.val.length ≤ 10000 ∧
      (∀ (i : ℕ) (hi : i < points.val.length), ValidPoint (points.val[i]'hi)) ∧
      1 ≤ x.val ∧ x.val ≤ 10000 ∧ 1 ≤ y.val ∧ y.val ≤ 10000

  def IsSwapped (points swapped : Points) : Prop :=
    swapped.val.length = points.val.length ∧
      ∀ i : ℕ, i < points.val.length →
        coord swapped i 0 = coord points i 1 ∧ coord swapped i 1 = coord points i 0

  /-- The function returns a result r (it does not fail). For 0 <= i < len(points), say that i matches when points[i][0] = x or points[i][1] = y, and let dist(i) = |points[i][0] - x| + |points[i][1] - y|. Then: (a) if there is no i with 0 <= i < len(points) that matches, r = -1; (b) if there is some i with 0 <= i < len(points) that matches, then 0 <= r < len(points), r matches, and for every matching i with 0 <= i < len(points), either dist(r) < dist(i), or (dist(r) = dist(i) and r <= i).
    Preconditions: 1 <= len(points) <= 10000; for every i with 0 <= i < len(points): len(points[i]) = 2, 1 <= points[i][0] <= 10000, and 1 <= points[i][1] <= 10000; 1 <= x <= 10000; 1 <= y <= 10000. -/
  theorem spec_1 (x y : Std.I64) (points : Points) (hpre : ValidInput x y points) :
      ∃ r : Std.I64, Aegis.NearestValidPoint.nearest_valid_point x y points = ok r ∧
        ((∀ i : ℕ, i < points.val.length → ¬ Matches x y points i) → r.val = -1) ∧
        ((∃ i : ℕ, i < points.val.length ∧ Matches x y points i) →
          0 ≤ r.val ∧ r.val < (points.val.length : ℤ) ∧
            Matches x y points r.val.toNat ∧
            ∀ i : ℕ, i < points.val.length → Matches x y points i →
              manhattanDist x y points r.val.toNat < manhattanDist x y points i ∨
                (manhattanDist x y points r.val.toNat = manhattanDist x y points i ∧
                  r.val ≤ (i : ℤ))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (x y : Std.I64) (points : Points) (hpre : ValidInput x y points), ∃ r : Std.I64, Aegis.NearestValidPoint.nearest_valid_point x y points = ok r ∧
          ((∀ i : ℕ, i < points.val.length → ¬ Matches x y points i) → r.val = -1) ∧
          ((∃ i : ℕ, i < points.val.length ∧ Matches x y points i) →
            0 ≤ r.val ∧ r.val < (points.val.length : ℤ) ∧
              Matches x y points r.val.toNat ∧
              ∀ i : ℕ, i < points.val.length → Matches x y points i →
                manhattanDist x y points r.val.toNat < manhattanDist x y points i ∨
                  (manhattanDist x y points r.val.toNat = manhattanDist x y points i ∧
                    r.val ≤ (i : ℤ)))) := by
    sorry

  /-- The function returns a result r (it never fails).
    Preconditions: 1 <= len(points) <= 10000; for every i with 0 <= i < len(points): len(points[i]) = 2, 1 <= points[i][0] <= 10000, and 1 <= points[i][1] <= 10000; 1 <= x <= 10000; 1 <= y <= 10000. -/
  theorem spec_2 (x y : Std.I64) (points : Points) (hpre : ValidInput x y points) :
      ∃ r : Std.I64, Aegis.NearestValidPoint.nearest_valid_point x y points = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (x y : Std.I64) (points : Points) (hpre : ValidInput x y points), ∃ r : Std.I64, Aegis.NearestValidPoint.nearest_valid_point x y points = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 0 <= r < len(points).
    Preconditions: 1 <= len(points) <= 10000; for every i with 0 <= i < len(points): len(points[i]) = 2, 1 <= points[i][0] <= 10000, and 1 <= points[i][1] <= 10000; 1 <= x <= 10000; 1 <= y <= 10000. -/
  theorem spec_3 (x y : Std.I64) (points : Points) (hpre : ValidInput x y points)
      (r : Std.I64) (hr : Aegis.NearestValidPoint.nearest_valid_point x y points = ok r) :
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val < (points.val.length : ℤ)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (x y : Std.I64) (points : Points) (hpre : ValidInput x y points)
        (r : Std.I64) (hr : Aegis.NearestValidPoint.nearest_valid_point x y points = ok r), r.val = -1 ∨ (0 ≤ r.val ∧ r.val < (points.val.length : ℤ))) := by
    sorry

  /-- Whenever the function returns a result r, if for every i with 0 <= i < len(points) both points[i][0] != x and points[i][1] != y, then r = -1.
    Preconditions: 1 <= len(points) <= 10000; for every i with 0 <= i < len(points): len(points[i]) = 2, 1 <= points[i][0] <= 10000, and 1 <= points[i][1] <= 10000; 1 <= x <= 10000; 1 <= y <= 10000. -/
  theorem spec_4 (x y : Std.I64) (points : Points) (hpre : ValidInput x y points)
      (r : Std.I64) (hr : Aegis.NearestValidPoint.nearest_valid_point x y points = ok r)
      (h : ∀ i : ℕ, i < points.val.length → coord points i 0 ≠ x.val ∧ coord points i 1 ≠ y.val) :
      r.val = -1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (x y : Std.I64) (points : Points) (hpre : ValidInput x y points)
        (r : Std.I64) (hr : Aegis.NearestValidPoint.nearest_valid_point x y points = ok r)
        (h : ∀ i : ℕ, i < points.val.length → coord points i 0 ≠ x.val ∧ coord points i 1 ≠ y.val), r.val = -1) := by
    sorry

  /-- Whenever the function returns a result r, if r = -1 then for every i with 0 <= i < len(points), points[i][0] != x and points[i][1] != y.
    Preconditions: 1 <= len(points) <= 10000; for every i with 0 <= i < len(points): len(points[i]) = 2, 1 <= points[i][0] <= 10000, and 1 <= points[i][1] <= 10000; 1 <= x <= 10000; 1 <= y <= 10000. -/
  theorem spec_5 (x y : Std.I64) (points : Points) (hpre : ValidInput x y points)
      (r : Std.I64) (hr : Aegis.NearestValidPoint.nearest_valid_point x y points = ok r)
      (h : r.val = -1) :
      ∀ i : ℕ, i < points.val.length → coord points i 0 ≠ x.val ∧ coord points i 1 ≠ y.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (x y : Std.I64) (points : Points) (hpre : ValidInput x y points)
        (r : Std.I64) (hr : Aegis.NearestValidPoint.nearest_valid_point x y points = ok r)
        (h : r.val = -1), ∀ i : ℕ, i < points.val.length → coord points i 0 ≠ x.val ∧ coord points i 1 ≠ y.val) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, then 0 <= r < len(points) and (points[r][0] = x or points[r][1] = y).
    Preconditions: 1 <= len(points) <= 10000; for every i with 0 <= i < len(points): len(points[i]) = 2, 1 <= points[i][0] <= 10000, and 1 <= points[i][1] <= 10000; 1 <= x <= 10000; 1 <= y <= 10000. -/
  theorem spec_6 (x y : Std.I64) (points : Points) (hpre : ValidInput x y points)
      (r : Std.I64) (hr : Aegis.NearestValidPoint.nearest_valid_point x y points = ok r)
      (h : 0 ≤ r.val) :
      0 ≤ r.val ∧ r.val < (points.val.length : ℤ) ∧ Matches x y points r.val.toNat := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (x y : Std.I64) (points : Points) (hpre : ValidInput x y points)
        (r : Std.I64) (hr : Aegis.NearestValidPoint.nearest_valid_point x y points = ok r)
        (h : 0 ≤ r.val), 0 ≤ r.val ∧ r.val < (points.val.length : ℤ) ∧ Matches x y points r.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r with 0 <= r < len(points) and (points[r][0] = x or points[r][1] = y), then for every i with 0 <= i < len(points) such that points[i][0] = x or points[i][1] = y, |points[r][0] - x| + |points[r][1] - y| <= |points[i][0] - x| + |points[i][1] - y|.
    Preconditions: 1 <= len(points) <= 10000; for every i with 0 <= i < len(points): len(points[i]) = 2, 1 <= points[i][0] <= 10000, and 1 <= points[i][1] <= 10000; 1 <= x <= 10000; 1 <= y <= 10000. -/
  theorem spec_7 (x y : Std.I64) (points : Points) (hpre : ValidInput x y points)
      (r : Std.I64) (hr : Aegis.NearestValidPoint.nearest_valid_point x y points = ok r)
      (h : 0 ≤ r.val ∧ r.val < (points.val.length : ℤ) ∧ Matches x y points r.val.toNat) :
      ∀ i : ℕ, i < points.val.length → Matches x y points i →
        manhattanDist x y points r.val.toNat ≤ manhattanDist x y points i := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (x y : Std.I64) (points : Points) (hpre : ValidInput x y points)
        (r : Std.I64) (hr : Aegis.NearestValidPoint.nearest_valid_point x y points = ok r)
        (h : 0 ≤ r.val ∧ r.val < (points.val.length : ℤ) ∧ Matches x y points r.val.toNat), ∀ i : ℕ, i < points.val.length → Matches x y points i →
          manhattanDist x y points r.val.toNat ≤ manhattanDist x y points i) := by
    sorry

  /-- Whenever the function returns a result r with 0 <= r < len(points) and (points[r][0] = x or points[r][1] = y), for every i with 0 <= i < r such that points[i][0] = x or points[i][1] = y, |points[i][0] - x| + |points[i][1] - y| > |points[r][0] - x| + |points[r][1] - y|.
    Preconditions: 1 <= len(points) <= 10000; for every i with 0 <= i < len(points): len(points[i]) = 2, 1 <= points[i][0] <= 10000, and 1 <= points[i][1] <= 10000; 1 <= x <= 10000; 1 <= y <= 10000. -/
  theorem spec_8 (x y : Std.I64) (points : Points) (hpre : ValidInput x y points)
      (r : Std.I64) (hr : Aegis.NearestValidPoint.nearest_valid_point x y points = ok r)
      (h : 0 ≤ r.val ∧ r.val < (points.val.length : ℤ) ∧ Matches x y points r.val.toNat) :
      ∀ i : ℕ, (i : ℤ) < r.val → Matches x y points i →
        manhattanDist x y points r.val.toNat < manhattanDist x y points i := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (x y : Std.I64) (points : Points) (hpre : ValidInput x y points)
        (r : Std.I64) (hr : Aegis.NearestValidPoint.nearest_valid_point x y points = ok r)
        (h : 0 ≤ r.val ∧ r.val < (points.val.length : ℤ) ∧ Matches x y points r.val.toNat), ∀ i : ℕ, (i : ℤ) < r.val → Matches x y points i →
          manhattanDist x y points r.val.toNat < manhattanDist x y points i) := by
    sorry

  /-- Whenever the function returns a result r, if there is an index i with 0 <= i < len(points) such that points[i][0] = x and points[i][1] = y, then 0 <= r < len(points), points[r][0] = x, points[r][1] = y, and for every j with 0 <= j < r, not (points[j][0] = x and points[j][1] = y).
    Preconditions: 1 <= len(points) <= 10000; for every i with 0 <= i < len(points): len(points[i]) = 2, 1 <= points[i][0] <= 10000, and 1 <= points[i][1] <= 10000; 1 <= x <= 10000; 1 <= y <= 10000. -/
  theorem spec_9 (x y : Std.I64) (points : Points) (hpre : ValidInput x y points)
      (r : Std.I64) (hr : Aegis.NearestValidPoint.nearest_valid_point x y points = ok r)
      (h : ∃ i : ℕ, i < points.val.length ∧ coord points i 0 = x.val ∧ coord points i 1 = y.val) :
      0 ≤ r.val ∧ r.val < (points.val.length : ℤ) ∧
        coord points r.val.toNat 0 = x.val ∧ coord points r.val.toNat 1 = y.val ∧
        ∀ j : ℕ, (j : ℤ) < r.val → ¬ (coord points j 0 = x.val ∧ coord points j 1 = y.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (x y : Std.I64) (points : Points) (hpre : ValidInput x y points)
        (r : Std.I64) (hr : Aegis.NearestValidPoint.nearest_valid_point x y points = ok r)
        (h : ∃ i : ℕ, i < points.val.length ∧ coord points i 0 = x.val ∧ coord points i 1 = y.val), 0 ≤ r.val ∧ r.val < (points.val.length : ℤ) ∧
          coord points r.val.toNat 0 = x.val ∧ coord points r.val.toNat 1 = y.val ∧
          ∀ j : ℕ, (j : ℤ) < r.val → ¬ (coord points j 0 = x.val ∧ coord points j 1 = y.val)) := by
    sorry

  /-- Let points' be the slice with len(points') = len(points) and points'[i] = [points[i][1], points[i][0]] for every i with 0 <= i < len(points). Whenever the function returns a result r on input (x, y, points) and a result r' on input (y, x, points'), we have r = r'.
    Preconditions: 1 <= len(points) <= 10000; for every i with 0 <= i < len(points): len(points[i]) = 2, 1 <= points[i][0] <= 10000, and 1 <= points[i][1] <= 10000; 1 <= x <= 10000; 1 <= y <= 10000. -/
  theorem spec_10 (x y : Std.I64) (points swapped : Points)
      (hpre : ValidInput x y points) (hswap : IsSwapped points swapped)
      (r r' : Std.I64)
      (hr : Aegis.NearestValidPoint.nearest_valid_point x y points = ok r)
      (hr' : Aegis.NearestValidPoint.nearest_valid_point y x swapped = ok r') :
      r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (x y : Std.I64) (points swapped : Points)
        (hpre : ValidInput x y points) (hswap : IsSwapped points swapped)
        (r r' : Std.I64)
        (hr : Aegis.NearestValidPoint.nearest_valid_point x y points = ok r)
        (hr' : Aegis.NearestValidPoint.nearest_valid_point y x swapped = ok r'), r = r') := by
    sorry

  end AegisSpec.NearestValidPoint
