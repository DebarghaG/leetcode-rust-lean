import Aegis.MaxWidthOfVerticalArea.Code.Funs

/-!
# Specifications of `Aegis.MaxWidthOfVerticalArea.max_width_of_vertical_area`

LeetCode problem `widest-vertical-area-between-two-points-containing-no-points`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxWidthOfVerticalArea

  abbrev mwva := Aegis.MaxWidthOfVerticalArea.max_width_of_vertical_area

  def xAt (points : Slice (alloc.vec.Vec I64)) (i : ℕ) : ℤ :=
    match points.val[i]? with
    | some p => (p.val.map (fun x => x.val)).headD 0
    | none => 0

  def xList (points : Slice (alloc.vec.Vec I64)) (n : ℕ) : List ℤ :=
    (List.range n).map (xAt points)

  def insertDistinct (y : ℤ) : List ℤ → List ℤ
    | [] => [y]
    | a :: rest =>
      if y = a then a :: rest
      else if y < a then y :: a :: rest
      else a :: insertDistinct y rest

  def sortDistinct (l : List ℤ) : List ℤ := l.foldr insertDistinct []

  def distinctSortedX (points : Slice (alloc.vec.Vec I64)) (n : ℕ) : List ℤ :=
    sortDistinct (xList points n)

  def adjacentGaps : List ℤ → List ℤ
    | [] => []
    | [_] => []
    | a :: b :: rest => (b - a) :: adjacentGaps (b :: rest)

  def maxAdjacentGap (l : List ℤ) : ℤ := (adjacentGaps l).foldr max 0

  def listMax : List ℤ → ℤ
    | [] => 0
    | a :: rest => rest.foldr max a

  def listMin : List ℤ → ℤ
    | [] => 0
    | a :: rest => rest.foldr min a

  def maxX (points : Slice (alloc.vec.Vec I64)) (n : ℕ) : ℤ := listMax (xList points n)

  def minX (points : Slice (alloc.vec.Vec I64)) (n : ℕ) : ℤ := listMin (xList points n)

  def maxGapX (points : Slice (alloc.vec.Vec I64)) (n : ℕ) : ℤ :=
    maxAdjacentGap (distinctSortedX points n)

  def PointsOK (points : Slice (alloc.vec.Vec I64)) : Prop :=
    ∀ p ∈ points.val, p.val.length = 2 ∧ ∃ a b : ℤ,
      p.val.map (fun x => x.val) = [a, b] ∧
        0 ≤ a ∧ a ≤ 10 ^ 9 ∧ 0 ≤ b ∧ b ≤ 10 ^ 9

  /-- Whenever the function returns a result r, r is the maximum of the set of values points[j][0] - points[i][0] over all ordered pairs (i,j) with 0 <= i < n, 0 <= j < n, points[i][0] < points[j][0], and no k with 0 <= k < n satisfying points[i][0] < points[k][0] < points[j][0]; if there is no such pair (equivalently, all x-coordinates are equal), then r = 0.
    Preconditions: n = len(points); 2 <= n <= 10^5; for every i with 0 <= i < n, len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9. -/
  theorem spec_1 (points : Slice (alloc.vec.Vec I64)) (n : ℕ)
      (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpoints : PointsOK points) :
      ∀ r, mwva points = ok r →
        (∀ i j : ℕ, i < n → j < n → xAt points i < xAt points j →
            (∀ k, k < n →
              ¬ (xAt points i < xAt points k ∧ xAt points k < xAt points j)) →
            xAt points j - xAt points i ≤ r.val) ∧
          (r.val = 0 ∨ ∃ i j : ℕ, i < n ∧ j < n ∧ xAt points i < xAt points j ∧
            (∀ k, k < n →
              ¬ (xAt points i < xAt points k ∧ xAt points k < xAt points j)) ∧
            xAt points j - xAt points i = r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (n : ℕ)
        (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpoints : PointsOK points), ∀ r, mwva points = ok r →
          (∀ i j : ℕ, i < n → j < n → xAt points i < xAt points j →
              (∀ k, k < n →
                ¬ (xAt points i < xAt points k ∧ xAt points k < xAt points j)) →
              xAt points j - xAt points i ≤ r.val) ∧
            (r.val = 0 ∨ ∃ i j : ℕ, i < n ∧ j < n ∧ xAt points i < xAt points j ∧
              (∀ k, k < n →
                ¬ (xAt points i < xAt points k ∧ xAt points k < xAt points j)) ∧
              xAt points j - xAt points i = r.val)) := by
    sorry

  /-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
    Preconditions: n = len(points); 2 <= n <= 10^5; for every i with 0 <= i < n, len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9. -/
  theorem spec_2 (points : Slice (alloc.vec.Vec I64)) (n : ℕ)
      (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpoints : PointsOK points) :
      ∃ r, mwva points = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (n : ℕ)
        (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpoints : PointsOK points), ∃ r, mwva points = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= 10^9.
    Preconditions: n = len(points); 2 <= n <= 10^5; for every i with 0 <= i < n, len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9. -/
  theorem spec_3 (points : Slice (alloc.vec.Vec I64)) (n : ℕ)
      (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpoints : PointsOK points) :
      ∀ r, mwva points = ok r → 0 ≤ r.val ∧ r.val ≤ 10 ^ 9 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (n : ℕ)
        (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpoints : PointsOK points), ∀ r, mwva points = ok r → 0 ≤ r.val ∧ r.val ≤ 10 ^ 9) := by
    sorry

  /-- Whenever the function returns a result r, r <= (max over 0 <= i < n of points[i][0]) - (min over 0 <= i < n of points[i][0]).
    Preconditions: n = len(points); 2 <= n <= 10^5; for every i with 0 <= i < n, len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9. -/
  theorem spec_4 (points : Slice (alloc.vec.Vec I64)) (n : ℕ)
      (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpoints : PointsOK points) :
      ∀ r, mwva points = ok r → r.val ≤ maxX points n - minX points n := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (n : ℕ)
        (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpoints : PointsOK points), ∀ r, mwva points = ok r → r.val ≤ maxX points n - minX points n) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if points[i][0] = points[j][0] for every i,j with 0 <= i < n and 0 <= j < n (that is, all x-coordinates are equal).
    Preconditions: n = len(points); 2 <= n <= 10^5; for every i with 0 <= i < n, len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9. -/
  theorem spec_5 (points : Slice (alloc.vec.Vec I64)) (n : ℕ)
      (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpoints : PointsOK points) :
      ∀ r, mwva points = ok r →
        (r.val = 0 ↔ ∀ i j, i < n → j < n → xAt points i = xAt points j) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (n : ℕ)
        (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpoints : PointsOK points), ∀ r, mwva points = ok r →
          (r.val = 0 ↔ ∀ i j, i < n → j < n → xAt points i = xAt points j)) := by
    sorry

  /-- Whenever the function returns a result r and r > 0, there exist indices p and q with 0 <= p < n and 0 <= q < n such that points[p][0] < points[q][0], points[q][0] - points[p][0] = r, and no k with 0 <= k < n satisfies points[p][0] < points[k][0] < points[q][0].
    Preconditions: n = len(points); 2 <= n <= 10^5; for every i with 0 <= i < n, len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9. -/
  theorem spec_6 (points : Slice (alloc.vec.Vec I64)) (n : ℕ)
      (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpoints : PointsOK points) :
      ∀ r, mwva points = ok r → 0 < r.val → ∃ p q : ℕ,
        p < n ∧ q < n ∧ xAt points p < xAt points q ∧
          xAt points q - xAt points p = r.val ∧
          ∀ k, k < n → ¬ (xAt points p < xAt points k ∧ xAt points k < xAt points q) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (n : ℕ)
        (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpoints : PointsOK points), ∀ r, mwva points = ok r → 0 < r.val → ∃ p q : ℕ,
          p < n ∧ q < n ∧ xAt points p < xAt points q ∧
            xAt points q - xAt points p = r.val ∧
            ∀ k, k < n → ¬ (xAt points p < xAt points k ∧ xAt points k < xAt points q)) := by
    sorry

  /-- Whenever the function returns a result r, for every i,j with 0 <= i < n, 0 <= j < n, points[i][0] < points[j][0], and no k with 0 <= k < n and points[i][0] < points[k][0] < points[j][0], we have points[j][0] - points[i][0] <= r.
    Preconditions: n = len(points); 2 <= n <= 10^5; for every i with 0 <= i < n, len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9. -/
  theorem spec_7 (points : Slice (alloc.vec.Vec I64)) (n : ℕ)
      (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpoints : PointsOK points) :
      ∀ r, mwva points = ok r → ∀ i j : ℕ, i < n → j < n →
        xAt points i < xAt points j →
          (∀ k, k < n → ¬ (xAt points i < xAt points k ∧ xAt points k < xAt points j)) →
          xAt points j - xAt points i ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (n : ℕ)
        (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpoints : PointsOK points), ∀ r, mwva points = ok r → ∀ i j : ℕ, i < n → j < n →
          xAt points i < xAt points j →
            (∀ k, k < n → ¬ (xAt points i < xAt points k ∧ xAt points k < xAt points j)) →
            xAt points j - xAt points i ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every i,j with 0 <= i < n and 0 <= j < n such that points[j][0] - points[i][0] > r, there exists k with 0 <= k < n and points[i][0] < points[k][0] < points[j][0].
    Preconditions: n = len(points); 2 <= n <= 10^5; for every i with 0 <= i < n, len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9. -/
  theorem spec_8 (points : Slice (alloc.vec.Vec I64)) (n : ℕ)
      (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpoints : PointsOK points) :
      ∀ r, mwva points = ok r → ∀ i j : ℕ, i < n → j < n →
        r.val < xAt points j - xAt points i →
          ∃ k, k < n ∧ xAt points i < xAt points k ∧ xAt points k < xAt points j := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (n : ℕ)
        (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpoints : PointsOK points), ∀ r, mwva points = ok r → ∀ i j : ℕ, i < n → j < n →
          r.val < xAt points j - xAt points i →
            ∃ k, k < n ∧ xAt points i < xAt points k ∧ xAt points k < xAt points j) := by
    sorry

  /-- Whenever the function returns a result r, let y_0 < y_1 < ... < y_{m-1} be the strictly increasing list of distinct values among points[0][0], ..., points[n-1][0]. If m = 1, then r = 0. If m >= 2, then r = max over 0 <= t < m-1 of (y_{t+1} - y_t).
    Preconditions: n = len(points); 2 <= n <= 10^5; for every i with 0 <= i < n, len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9. -/
  theorem spec_9 (points : Slice (alloc.vec.Vec I64)) (n : ℕ)
      (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpoints : PointsOK points) :
      ∀ r, mwva points = ok r →
        ((distinctSortedX points n).length = 1 → r.val = 0) ∧
          (2 ≤ (distinctSortedX points n).length →
            r.val = maxAdjacentGap (distinctSortedX points n)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (n : ℕ)
        (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpoints : PointsOK points), ∀ r, mwva points = ok r →
          ((distinctSortedX points n).length = 1 → r.val = 0) ∧
            (2 ≤ (distinctSortedX points n).length →
              r.val = maxAdjacentGap (distinctSortedX points n))) := by
    sorry

  /-- Whenever the function returns results r on points and r' on points', if the set of distinct x-coordinates appearing among points equals the set of distinct x-coordinates appearing among points', then r = r'.
    Preconditions: Both points and points' satisfy: n = len(points) (respectively n' = len(points')) with 2 <= n <= 10^5, for every i with 0 <= i < n, len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9; and the same for points' with n'. -/
  theorem spec_10 (points points' : Slice (alloc.vec.Vec I64)) (n n' : ℕ)
      (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpoints : PointsOK points)
      (hn' : points'.val.length = n') (hn_lo' : 2 ≤ n') (hn_hi' : n' ≤ 10 ^ 5)
      (hpoints' : PointsOK points') :
      ∀ r r', mwva points = ok r → mwva points' = ok r' →
        (∀ y : ℤ, (∃ i, i < n ∧ xAt points i = y) ↔ (∃ i, i < n' ∧ xAt points' i = y)) →
        r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (points points' : Slice (alloc.vec.Vec I64)) (n n' : ℕ)
        (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpoints : PointsOK points)
        (hn' : points'.val.length = n') (hn_lo' : 2 ≤ n') (hn_hi' : n' ≤ 10 ^ 5)
        (hpoints' : PointsOK points'), ∀ r r', mwva points = ok r → mwva points' = ok r' →
          (∀ y : ℤ, (∃ i, i < n ∧ xAt points i = y) ↔ (∃ i, i < n' ∧ xAt points' i = y)) →
          r.val = r'.val) := by
    sorry

  /-- Whenever the function returns results r on points and r' on points', if every distinct x-coordinate appearing among points also appears among points' (i.e., the set of distinct x-coordinates of points is a subset of that of points'), then r' <= r.
    Preconditions: Both points and points' satisfy: n = len(points) (respectively n' = len(points')) with 2 <= n <= 10^5, for every i with 0 <= i < n, len(points[i]) = 2, 0 <= points[i][0] <= 10^9, and 0 <= points[i][1] <= 10^9; and the same for points' with n'. -/
  theorem spec_11 (points points' : Slice (alloc.vec.Vec I64)) (n n' : ℕ)
      (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
      (hpoints : PointsOK points)
      (hn' : points'.val.length = n') (hn_lo' : 2 ≤ n') (hn_hi' : n' ≤ 10 ^ 5)
      (hpoints' : PointsOK points') :
      ∀ r r', mwva points = ok r → mwva points' = ok r' →
        (∀ y : ℤ, (∃ i, i < n ∧ xAt points i = y) → (∃ i, i < n' ∧ xAt points' i = y)) →
        r'.val ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (points points' : Slice (alloc.vec.Vec I64)) (n n' : ℕ)
        (hn : points.val.length = n) (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
        (hpoints : PointsOK points)
        (hn' : points'.val.length = n') (hn_lo' : 2 ≤ n') (hn_hi' : n' ≤ 10 ^ 5)
        (hpoints' : PointsOK points'), ∀ r r', mwva points = ok r → mwva points' = ok r' →
          (∀ y : ℤ, (∃ i, i < n ∧ xAt points i = y) → (∃ i, i < n' ∧ xAt points' i = y)) →
          r'.val ≤ r.val) := by
    sorry

  end AegisSpec.MaxWidthOfVerticalArea
