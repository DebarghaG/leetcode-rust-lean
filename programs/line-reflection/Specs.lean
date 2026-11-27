import Aegis.IsReflected.Code.Funs

/-!
# Specifications of `Aegis.IsReflected.is_reflected`

LeetCode problem `line-reflection`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.IsReflected

namespace AegisSpec.IsReflected

def coords (v : alloc.vec.Vec Std.I64) : List ℤ :=
  v.val.map (fun c => c.val)

def pointList (points : Slice (alloc.vec.Vec Std.I64)) : List (ℤ × ℤ) :=
  points.val.map (fun v => ((coords v).getD 0 0, (coords v).getD 1 0))

def xs (points : Slice (alloc.vec.Vec Std.I64)) : List ℤ :=
  (pointList points).map (fun p => p.1)

def minX (points : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
  (xs points).min?.getD 0

def maxX (points : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
  (xs points).max?.getD 0

def IsReflectedSet (points : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∀ p ∈ pointList points, (minX points + maxX points - p.1, p.2) ∈ pointList points

def pointSetQ (points : Slice (alloc.vec.Vec Std.I64)) : Set (ℚ × ℚ) :=
  {q | ∃ p ∈ pointList points, q = ((p.1 : ℚ), (p.2 : ℚ))}

def rowXs (points : Slice (alloc.vec.Vec Std.I64)) (y : ℤ) : List ℤ :=
  (pointList points).filterMap (fun p => if p.2 = y then some p.1 else none)

def rowMin (points : Slice (alloc.vec.Vec Std.I64)) (y : ℤ) : ℤ :=
  (rowXs points y).min?.getD 0

def rowMax (points : Slice (alloc.vec.Vec Std.I64)) (y : ℤ) : ℤ :=
  (rowXs points y).max?.getD 0

def IsValidPoints (points : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  1 ≤ points.val.length ∧ points.val.length ≤ 10000 ∧
    (∀ v ∈ points.val, v.val.length = 2) ∧
    (∀ v ∈ points.val, ∀ c ∈ v.val, -100000000 ≤ c.val ∧ c.val ≤ 100000000)

/-- Let S = { (points[i][0], points[i][1]) | 0 <= i < len(points) }. Let minX be the minimum x over all (x,y) in S and maxX the maximum x over all (x,y) in S. Whenever the function returns a result r, r = true iff for every (x,y) in S the pair (minX + maxX - x, y) also belongs to S.
  Preconditions: 1 <= len(points) <= 10000; for every i with 0 <= i < len(points), len(points[i]) = 2; and for every i with 0 <= i < len(points) and j = 0 or j = 1, -100000000 <= points[i][j] <= 100000000. -/
theorem spec_1 (points : Slice (alloc.vec.Vec Std.I64)) (h : IsValidPoints points) :
    ∃ r, is_reflected points = ok r ∧
      (r = true ↔ IsReflectedSet points) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : IsValidPoints points), ∃ r, is_reflected points = ok r ∧
      (r = true ↔ IsReflectedSet points)) := by
  sorry

/-- The function returns a result r (it does not fail).
  Preconditions: 1 <= len(points) <= 10000; for every i with 0 <= i < len(points), len(points[i]) = 2; and for every i with 0 <= i < len(points) and j = 0 or j = 1, -100000000 <= points[i][j] <= 100000000. -/
theorem spec_2 (points : Slice (alloc.vec.Vec Std.I64)) (h : IsValidPoints points) :
    ∃ r, is_reflected points = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : IsValidPoints points), ∃ r, is_reflected points = ok r) := by
  sorry

/-- Let S = { (points[i][0], points[i][1]) | 0 <= i < len(points) }. Let minX be the minimum x over all (x,y) in S and maxX the maximum x over all (x,y) in S. Whenever the function returns true, for every real number c such that for every (x,y) in S the pair (2c-x, y) belongs to S, we have 2c = minX + maxX.
  Preconditions: 1 <= len(points) <= 10000; for every i with 0 <= i < len(points), len(points[i]) = 2; and for every i with 0 <= i < len(points) and j = 0 or j = 1, -100000000 <= points[i][j] <= 100000000. -/
theorem spec_3 (points : Slice (alloc.vec.Vec Std.I64)) (h : IsValidPoints points)
    (hres : is_reflected points = ok true) :
    ∀ c : ℚ, (∀ p ∈ pointList points, ((2 : ℚ) * c - (p.1 : ℚ), (p.2 : ℚ)) ∈ pointSetQ points) →
      (2 : ℚ) * c = ((minX points + maxX points : ℤ) : ℚ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : IsValidPoints points)
    (hres : is_reflected points = ok true), ∀ c : ℚ, (∀ p ∈ pointList points, ((2 : ℚ) * c - (p.1 : ℚ), (p.2 : ℚ)) ∈ pointSetQ points) →
      (2 : ℚ) * c = ((minX points + maxX points : ℤ) : ℚ)) := by
  sorry

/-- Whenever is_reflected(points) returns r and is_reflected(q) returns r', we have r = r'.
  Preconditions: Both points and q satisfy the input constraints: their lengths are between 1 and 10000, every point has length 2, and all coordinates lie between -100000000 and 100000000. Also, q is obtained from points by inserting or deleting copies of points, so the set { (points[i][0], points[i][1]) } equals { (q[i][0], q[i][1]) }. -/
theorem spec_4 (points q : Slice (alloc.vec.Vec Std.I64))
    (hp : IsValidPoints points) (hq : IsValidPoints q)
    (hsame : ∀ p, p ∈ pointList points ↔ p ∈ pointList q) :
    ∀ r r', is_reflected points = ok r → is_reflected q = ok r' → r = r' := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (points q : Slice (alloc.vec.Vec Std.I64))
    (hp : IsValidPoints points) (hq : IsValidPoints q)
    (hsame : ∀ p, p ∈ pointList points ↔ p ∈ pointList q), ∀ r r', is_reflected points = ok r → is_reflected q = ok r' → r = r') := by
  sorry

/-- Let S = { (points[i][0], points[i][1]) | 0 <= i < len(points) }. Let minX be the minimum x over S and maxX the maximum x over S. Whenever the function returns true, for every integer y such that X_y = { x | (x,y) belongs to S } is nonempty, if m_y = min(X_y) and M_y = max(X_y), then m_y + M_y = minX + maxX.
  Preconditions: 1 <= len(points) <= 10000; for every i with 0 <= i < len(points), len(points[i]) = 2; and for every i with 0 <= i < len(points) and j = 0 or j = 1, -100000000 <= points[i][j] <= 100000000. -/
theorem spec_5 (points : Slice (alloc.vec.Vec Std.I64)) (h : IsValidPoints points)
    (hres : is_reflected points = ok true) :
    ∀ y : ℤ, (∃ p ∈ pointList points, p.2 = y) →
      rowMin points y + rowMax points y = minX points + maxX points := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : IsValidPoints points)
    (hres : is_reflected points = ok true), ∀ y : ℤ, (∃ p ∈ pointList points, p.2 = y) →
      rowMin points y + rowMax points y = minX points + maxX points) := by
  sorry

/-- Let S = { (points[i][0], points[i][1]) | 0 <= i < len(points) }. Let minX be the minimum x over S and maxX the maximum x over S. Whenever the function returns true, for every i with 0 <= i < len(points) there exists j with 0 <= j < len(points) such that points[j][1] = points[i][1] and points[j][0] + points[i][0] = minX + maxX.
  Preconditions: 1 <= len(points) <= 10000; for every i with 0 <= i < len(points), len(points[i]) = 2; and for every i with 0 <= i < len(points) and j = 0 or j = 1, -100000000 <= points[i][j] <= 100000000. -/
theorem spec_6 (points : Slice (alloc.vec.Vec Std.I64)) (h : IsValidPoints points)
    (hres : is_reflected points = ok true) :
    ∀ p ∈ pointList points, ∃ q ∈ pointList points,
      q.2 = p.2 ∧ q.1 + p.1 = minX points + maxX points := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : IsValidPoints points)
    (hres : is_reflected points = ok true), ∀ p ∈ pointList points, ∃ q ∈ pointList points,
      q.2 = p.2 ∧ q.1 + p.1 = minX points + maxX points) := by
  sorry

end AegisSpec.IsReflected
