import Aegis.IsBoomerang.Code.Funs

/-!
# Specifications of `Aegis.IsBoomerang.is_boomerang`

LeetCode problem `valid-boomerang`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsBoomerang

abbrev Points := Slice (alloc.vec.Vec Std.I64)

def row (points : Points) (i : Nat) : List Int :=
  match points.val[i]? with
  | none => []
  | some v => v.val.map (fun x => x.val)

def coord (points : Points) (i j : Nat) : Int :=
  match points.val[i]? with
  | none => 0
  | some v =>
    match v.val[j]? with
    | none => 0
    | some x => x.val

def det (points : Points) : Int :=
  (coord points 1 0 - coord points 0 0) * (coord points 2 1 - coord points 0 1) -
    (coord points 1 1 - coord points 0 1) * (coord points 2 0 - coord points 0 0)

def OnLine (points : Points) (i j k : Nat) : Prop :=
  ∃ t : ℚ,
    ((coord points k 0 - coord points i 0 : Int) : ℚ) =
        t * ((coord points j 0 - coord points i 0 : Int) : ℚ) ∧
      ((coord points k 1 - coord points i 1 : Int) : ℚ) =
        t * ((coord points j 1 - coord points i 1 : Int) : ℚ)

def HasCommonLine (points : Points) : Prop :=
  ∃ a b c : ℚ,
    (a ≠ 0 ∨ b ≠ 0) ∧
      ∀ i, i < 3 → a * ((coord points i 0 : Int) : ℚ) +
        b * ((coord points i 1 : Int) : ℚ) + c = 0

/-- Let x_i = points[i][0] and y_i = points[i][1] for i = 0,1,2, and let D = (x_1 - x_0)*(y_2 - y_0) - (y_1 - y_0)*(x_2 - x_0). The function returns a result r and r = true if and only if the three points (x_0,y_0), (x_1,y_1), (x_2,y_2) are pairwise distinct and are not all collinear; equivalently, r = true if and only if D != 0, and r = false if and only if D = 0.
  Preconditions: len(points) = 3; for every i with 0 <= i < 3, len(points[i]) = 2; and for every i with 0 <= i < 3 and j with 0 <= j < 2, 0 <= points[i][j] <= 100. All coordinates are i64 machine integers. -/
theorem spec_1 (points : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100) :
    ∃ r, Aegis.IsBoomerang.is_boomerang points = ok r ∧
      (r = true ↔ det points ≠ 0) ∧ (r = false ↔ det points = 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (points : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100), ∃ r, Aegis.IsBoomerang.is_boomerang points = ok r ∧
      (r = true ↔ det points ≠ 0) ∧ (r = false ↔ det points = 0)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, go out of bounds, or overflow on any input satisfying the preconditions.
  Preconditions: len(points) = 3; for every i with 0 <= i < 3, len(points[i]) = 2; and for every i with 0 <= i < 3 and j with 0 <= j < 2, 0 <= points[i][j] <= 100. All coordinates are i64 machine integers. -/
theorem spec_2 (points : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100) :
    ∃ r, Aegis.IsBoomerang.is_boomerang points = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (points : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100), ∃ r, Aegis.IsBoomerang.is_boomerang points = ok r) := by
  sorry

/-- Let D = (points[1][0]-points[0][0])*(points[2][1]-points[0][1]) - (points[1][1]-points[0][1])*(points[2][0]-points[0][0]). If D = 0, then the function returns a result r with r = false.
  Preconditions: len(points) = 3; for every i with 0 <= i < 3, len(points[i]) = 2; and for every i with 0 <= i < 3 and j with 0 <= j < 2, 0 <= points[i][j] <= 100. All coordinates are i64 machine integers. -/
theorem spec_3 (points : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100)
    (hD : det points = 0) :
    ∃ r, Aegis.IsBoomerang.is_boomerang points = ok r ∧ r = false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (points : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100)
    (hD : det points = 0), ∃ r, Aegis.IsBoomerang.is_boomerang points = ok r ∧ r = false) := by
  sorry

/-- Let D = (points[1][0]-points[0][0])*(points[2][1]-points[0][1]) - (points[1][1]-points[0][1])*(points[2][0]-points[0][0]). Whenever the function returns a result r with r = true, the integer D satisfies 1 <= |D| <= 20000.
  Preconditions: len(points) = 3; for every i with 0 <= i < 3, len(points[i]) = 2; and for every i with 0 <= i < 3 and j with 0 <= j < 2, 0 <= points[i][j] <= 100. All coordinates are i64 machine integers. -/
theorem spec_4 (points : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100) :
    ∀ r, Aegis.IsBoomerang.is_boomerang points = ok r → r = true →
      1 ≤ (det points).natAbs ∧ (det points).natAbs ≤ 20000 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (points : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100), ∀ r, Aegis.IsBoomerang.is_boomerang points = ok r → r = true →
      1 ≤ (det points).natAbs ∧ (det points).natAbs ≤ 20000) := by
  sorry

/-- If the function returns a result r with r = true, then for every choice of distinct indices i,j,k from {0,1,2}, the point (points[k][0],points[k][1]) does not lie on the straight line through (points[i][0],points[i][1]) and (points[j][0],points[j][1]); equivalently, there is no real number t such that points[k][0]-points[i][0] = t*(points[j][0]-points[i][0]) and points[k][1]-points[i][1] = t*(points[j][1]-points[i][1]).
  Preconditions: len(points) = 3; for every i with 0 <= i < 3, len(points[i]) = 2; and for every i with 0 <= i < 3 and j with 0 <= j < 2, 0 <= points[i][j] <= 100. All coordinates are i64 machine integers. -/
theorem spec_5 (points : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100) :
    ∀ r, Aegis.IsBoomerang.is_boomerang points = ok r → r = true →
      ∀ i j k : Nat, i < 3 → j < 3 → k < 3 → i ≠ j → i ≠ k → j ≠ k →
        ¬ OnLine points i j k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (points : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100), ∀ r, Aegis.IsBoomerang.is_boomerang points = ok r → r = true →
      ∀ i j k : Nat, i < 3 → j < 3 → k < 3 → i ≠ j → i ≠ k → j ≠ k →
        ¬ OnLine points i j k) := by
  sorry

/-- If the function returns a result r with r = false, then D = 0 for D = (points[1][0]-points[0][0])*(points[2][1]-points[0][1]) - (points[1][1]-points[0][1])*(points[2][0]-points[0][0]); consequently, there exists a straight line in the plane containing all three points (with coincident points allowed).
  Preconditions: len(points) = 3; for every i with 0 <= i < 3, len(points[i]) = 2; and for every i with 0 <= i < 3 and j with 0 <= j < 2, 0 <= points[i][j] <= 100. All coordinates are i64 machine integers. -/
theorem spec_6 (points : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100) :
    ∀ r, Aegis.IsBoomerang.is_boomerang points = ok r → r = false →
      det points = 0 ∧ HasCommonLine points := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (points : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100), ∀ r, Aegis.IsBoomerang.is_boomerang points = ok r → r = false →
      det points = 0 ∧ HasCommonLine points) := by
  sorry

/-- For every permutation sigma of {0,1,2}, let points' be the input with points'[i] = points[sigma(i)] for i = 0,1,2. The function returns a result r on points and a result r' on points', and r = r'.
  Preconditions: len(points) = 3; for every i with 0 <= i < 3, len(points[i]) = 2; and for every i with 0 <= i < 3 and j with 0 <= j < 2, 0 <= points[i][j] <= 100. All coordinates are i64 machine integers. -/
theorem spec_7 (points points' : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100)
    (h_len' : points'.val.length = 3)
    (h_rows' : ∀ v ∈ points'.val, v.val.length = 2)
    (h_bounds' : ∀ v ∈ points'.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100)
    (σ : Equiv.Perm (Fin 3))
    (h_perm : ∀ i : Fin 3, row points' i.val = row points (σ i).val) :
    ∃ r r', Aegis.IsBoomerang.is_boomerang points = ok r ∧
      Aegis.IsBoomerang.is_boomerang points' = ok r' ∧ r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (points points' : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100)
    (h_len' : points'.val.length = 3)
    (h_rows' : ∀ v ∈ points'.val, v.val.length = 2)
    (h_bounds' : ∀ v ∈ points'.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100)
    (σ : Equiv.Perm (Fin 3))
    (h_perm : ∀ i : Fin 3, row points' i.val = row points (σ i).val), ∃ r r', Aegis.IsBoomerang.is_boomerang points = ok r ∧
      Aegis.IsBoomerang.is_boomerang points' = ok r' ∧ r = r') := by
  sorry

/-- For every pair of integers dx and dy such that 0 <= points[i][0]+dx <= 100 and 0 <= points[i][1]+dy <= 100 for i = 0,1,2, let points' be defined by points'[i][0] = points[i][0]+dx and points'[i][1] = points[i][1]+dy. The function returns a result r on points and a result r' on points', and r = r'.
  Preconditions: len(points) = 3; for every i with 0 <= i < 3, len(points[i]) = 2; and for every i with 0 <= i < 3 and j with 0 <= j < 2, 0 <= points[i][j] <= 100. All coordinates are i64 machine integers. -/
theorem spec_8 (points points' : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100)
    (h_len' : points'.val.length = 3)
    (h_rows' : ∀ v ∈ points'.val, v.val.length = 2)
    (h_bounds' : ∀ v ∈ points'.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100)
    (dx dy : Int)
    (h_shift : ∀ i, i < 3 →
      coord points' i 0 = coord points i 0 + dx ∧
        coord points' i 1 = coord points i 1 + dy) :
    ∃ r r', Aegis.IsBoomerang.is_boomerang points = ok r ∧
      Aegis.IsBoomerang.is_boomerang points' = ok r' ∧ r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (points points' : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100)
    (h_len' : points'.val.length = 3)
    (h_rows' : ∀ v ∈ points'.val, v.val.length = 2)
    (h_bounds' : ∀ v ∈ points'.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100)
    (dx dy : Int)
    (h_shift : ∀ i, i < 3 →
      coord points' i 0 = coord points i 0 + dx ∧
        coord points' i 1 = coord points i 1 + dy), ∃ r r', Aegis.IsBoomerang.is_boomerang points = ok r ∧
      Aegis.IsBoomerang.is_boomerang points' = ok r' ∧ r = r') := by
  sorry

/-- Let points' be defined by points'[i][0] = points[i][1] and points'[i][1] = points[i][0] for i = 0,1,2. The function returns a result r on points and a result r' on points', and r = r'.
  Preconditions: len(points) = 3; for every i with 0 <= i < 3, len(points[i]) = 2; and for every i with 0 <= i < 3 and j with 0 <= j < 2, 0 <= points[i][j] <= 100. All coordinates are i64 machine integers. -/
theorem spec_9 (points points' : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100)
    (h_len' : points'.val.length = 3)
    (h_rows' : ∀ v ∈ points'.val, v.val.length = 2)
    (h_bounds' : ∀ v ∈ points'.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100)
    (h_swap : ∀ i, i < 3 →
      coord points' i 0 = coord points i 1 ∧
        coord points' i 1 = coord points i 0) :
    ∃ r r', Aegis.IsBoomerang.is_boomerang points = ok r ∧
      Aegis.IsBoomerang.is_boomerang points' = ok r' ∧ r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (points points' : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100)
    (h_len' : points'.val.length = 3)
    (h_rows' : ∀ v ∈ points'.val, v.val.length = 2)
    (h_bounds' : ∀ v ∈ points'.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100)
    (h_swap : ∀ i, i < 3 →
      coord points' i 0 = coord points i 1 ∧
        coord points' i 1 = coord points i 0), ∃ r r', Aegis.IsBoomerang.is_boomerang points = ok r ∧
      Aegis.IsBoomerang.is_boomerang points' = ok r' ∧ r = r') := by
  sorry

/-- For every integer k with k >= 1 and with 0 <= k*points[i][0] <= 100 and 0 <= k*points[i][1] <= 100 for i = 0,1,2, let points' be defined by points'[i][0] = k*points[i][0] and points'[i][1] = k*points[i][1]. The function returns a result r on points and a result r' on points', and r = r'.
  Preconditions: len(points) = 3; for every i with 0 <= i < 3, len(points[i]) = 2; and for every i with 0 <= i < 3 and j with 0 <= j < 2, 0 <= points[i][j] <= 100. All coordinates are i64 machine integers. -/
theorem spec_10 (points points' : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100)
    (h_len' : points'.val.length = 3)
    (h_rows' : ∀ v ∈ points'.val, v.val.length = 2)
    (h_bounds' : ∀ v ∈ points'.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100)
    (k : Int) (hk : 1 ≤ k)
    (h_scale : ∀ i, i < 3 →
      coord points' i 0 = k * coord points i 0 ∧
        coord points' i 1 = k * coord points i 1) :
    ∃ r r', Aegis.IsBoomerang.is_boomerang points = ok r ∧
      Aegis.IsBoomerang.is_boomerang points' = ok r' ∧ r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (points points' : Points)
    (h_len : points.val.length = 3)
    (h_rows : ∀ v ∈ points.val, v.val.length = 2)
    (h_bounds : ∀ v ∈ points.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100)
    (h_len' : points'.val.length = 3)
    (h_rows' : ∀ v ∈ points'.val, v.val.length = 2)
    (h_bounds' : ∀ v ∈ points'.val, ∀ x ∈ v.val, 0 ≤ x.val ∧ x.val ≤ 100)
    (k : Int) (hk : 1 ≤ k)
    (h_scale : ∀ i, i < 3 →
      coord points' i 0 = k * coord points i 0 ∧
        coord points' i 1 = k * coord points i 1), ∃ r r', Aegis.IsBoomerang.is_boomerang points = ok r ∧
      Aegis.IsBoomerang.is_boomerang points' = ok r' ∧ r = r') := by
  sorry

end AegisSpec.IsBoomerang
