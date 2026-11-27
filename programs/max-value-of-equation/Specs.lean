import Aegis.FindMaxValueOfEquation.Code.Funs

/-!
# Specifications of `Aegis.FindMaxValueOfEquation.find_max_value_of_equation`

LeetCode problem `max-value-of-equation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.FindMaxValueOfEquation

  namespace AegisSpec.FindMaxValueOfEquation

  def intPoints (points : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    points.val.map (fun v => v.val.map (fun x => x.val))

  def nOf (points : Slice (alloc.vec.Vec Std.I64)) : ℕ := (intPoints points).length

  def row (pts : List (List ℤ)) (i : ℕ) : List ℤ := pts.getD i []

  def px (pts : List (List ℤ)) (i : ℕ) : ℤ := (row pts i).getD 0 0

  def py (pts : List (List ℤ)) (i : ℕ) : ℤ := (row pts i).getD 1 0

  def ysOf (pts : List (List ℤ)) : List ℤ := pts.map (fun r => r.getD 1 0)

  def listMin : List ℤ → ℤ
    | [] => 0
    | x :: xs => xs.foldl (fun a b => min a b) x

  def listMax : List ℤ → ℤ
    | [] => 0
    | x :: xs => xs.foldl (fun a b => max a b) x

  def minY (points : Slice (alloc.vec.Vec Std.I64)) : ℤ := listMin (ysOf (intPoints points))

  def maxY (points : Slice (alloc.vec.Vec Std.I64)) : ℤ := listMax (ysOf (intPoints points))

  def dist (pts : List (List ℤ)) (i j : ℕ) : ℤ := |px pts i - px pts j|

  def cand (pts : List (List ℤ)) (i j : ℕ) : ℤ := py pts i + py pts j + dist pts i j

  def cand' (pts : List (List ℤ)) (i j : ℕ) : ℤ :=
    (py pts i - px pts i) + (py pts j + px pts j)

  def ValidPoints (points : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    2 ≤ nOf points ∧ nOf points ≤ 100000 ∧
    (∀ i, i < nOf points → (row (intPoints points) i).length = 2) ∧
    (∀ i, i < nOf points →
      -100000000 ≤ px (intPoints points) i ∧ px (intPoints points) i ≤ 100000000) ∧
    (∀ i, i < nOf points →
      -100000000 ≤ py (intPoints points) i ∧ py (intPoints points) i ≤ 100000000) ∧
    (∀ i j, i < j → j < nOf points → px (intPoints points) i < px (intPoints points) j)

  def KInRange (k : Std.I64) : Prop := 0 ≤ k.val ∧ k.val ≤ 200000000

  def ExistsPairWithin (points : Slice (alloc.vec.Vec Std.I64)) (k : ℤ) : Prop :=
    ∃ i j, i < j ∧ j < nOf points ∧ dist (intPoints points) i j ≤ k

  def ValidInput (points : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) : Prop :=
    ValidPoints points ∧ KInRange k ∧ ExistsPairWithin points k.val

  def IsXShift (points points' : Slice (alloc.vec.Vec Std.I64)) (c : ℤ) : Prop :=
    nOf points' = nOf points ∧
    (∀ i, i < nOf points → px (intPoints points') i = px (intPoints points) i + c) ∧
    (∀ i, i < nOf points → py (intPoints points') i = py (intPoints points) i)

  def IsYShift (points points' : Slice (alloc.vec.Vec Std.I64)) (c : ℤ) : Prop :=
    nOf points' = nOf points ∧
    (∀ i, i < nOf points → px (intPoints points') i = px (intPoints points) i) ∧
    (∀ i, i < nOf points → py (intPoints points') i = py (intPoints points) i + c)

  /-- Whenever the function returns a result r, r is the maximum of the set { points[i][1] + points[j][1] + |points[i][0] - points[j][0]| | 0 <= i < j < n and |points[i][0] - points[j][0]| <= k }. Equivalently, for every such pair the candidate value is at most r, and there exists such a pair whose candidate value is exactly r.
    Preconditions: Let n = len(points). 2 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2, and points[i][0] and points[i][1] are integers in the closed interval [-100000000, 100000000]. For every 0 <= i < j < n, points[i][0] < points[j][0]. 0 <= k <= 200000000. There exist indices i,j with 0 <= i < j < n and |points[i][0] - points[j][0]| <= k. -/
  theorem spec_1 (points : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (r : Std.I64)
      (h : ValidInput points k) (hr : find_max_value_of_equation points k = ok r) :
      (∀ i j, i < j → j < nOf points → dist (intPoints points) i j ≤ k.val →
        cand (intPoints points) i j ≤ r.val) ∧
      (∃ i j, i < j ∧ j < nOf points ∧ dist (intPoints points) i j ≤ k.val ∧
        cand (intPoints points) i j = r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (r : Std.I64)
        (h : ValidInput points k) (hr : find_max_value_of_equation points k = ok r), (∀ i j, i < j → j < nOf points → dist (intPoints points) i j ≤ k.val →
          cand (intPoints points) i j ≤ r.val) ∧
        (∃ i j, i < j ∧ j < nOf points ∧ dist (intPoints points) i j ≤ k.val ∧
          cand (intPoints points) i j = r.val)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, overflow, or panic.
    Preconditions: Let n = len(points). 2 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2, and points[i][0] and points[i][1] are integers in the closed interval [-100000000, 100000000]. For every 0 <= i < j < n, points[i][0] < points[j][0]. 0 <= k <= 200000000. There exist indices i,j with 0 <= i < j < n and |points[i][0] - points[j][0]| <= k. -/
  theorem spec_2 (points : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (h : ValidInput points k) :
      ∃ r : Std.I64, find_max_value_of_equation points k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (h : ValidInput points k), ∃ r : Std.I64, find_max_value_of_equation points k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of indices i,j with 0 <= i < j < n and |points[i][0] - points[j][0]| <= k, we have points[i][1] + points[j][1] + |points[i][0] - points[j][0]| <= r.
    Preconditions: Let n = len(points). 2 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2, and points[i][0] and points[i][1] are integers in the closed interval [-100000000, 100000000]. For every 0 <= i < j < n, points[i][0] < points[j][0]. 0 <= k <= 200000000. There exist indices i,j with 0 <= i < j < n and |points[i][0] - points[j][0]| <= k. -/
  theorem spec_3 (points : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (r : Std.I64)
      (h : ValidInput points k) (hr : find_max_value_of_equation points k = ok r) :
      ∀ i j, i < j → j < nOf points → dist (intPoints points) i j ≤ k.val →
        cand (intPoints points) i j ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (r : Std.I64)
        (h : ValidInput points k) (hr : find_max_value_of_equation points k = ok r), ∀ i j, i < j → j < nOf points → dist (intPoints points) i j ≤ k.val →
          cand (intPoints points) i j ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices i,j with 0 <= i < j < n and |points[i][0] - points[j][0]| <= k such that points[i][1] + points[j][1] + |points[i][0] - points[j][0]| = r.
    Preconditions: Let n = len(points). 2 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2, and points[i][0] and points[i][1] are integers in the closed interval [-100000000, 100000000]. For every 0 <= i < j < n, points[i][0] < points[j][0]. 0 <= k <= 200000000. There exist indices i,j with 0 <= i < j < n and |points[i][0] - points[j][0]| <= k. -/
  theorem spec_4 (points : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (r : Std.I64)
      (h : ValidInput points k) (hr : find_max_value_of_equation points k = ok r) :
      ∃ i j, i < j ∧ j < nOf points ∧ dist (intPoints points) i j ≤ k.val ∧
        cand (intPoints points) i j = r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (r : Std.I64)
        (h : ValidInput points k) (hr : find_max_value_of_equation points k = ok r), ∃ i j, i < j ∧ j < nOf points ∧ dist (intPoints points) i j ≤ k.val ∧
          cand (intPoints points) i j = r.val) := by
    sorry

  /-- Whenever the function returns a result r, if minY = min_{0 <= i < n} points[i][1] and maxY = max_{0 <= i < n} points[i][1], then 2*minY <= r <= 2*maxY + k.
    Preconditions: Let n = len(points). 2 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2, and points[i][0] and points[i][1] are integers in the closed interval [-100000000, 100000000]. For every 0 <= i < j < n, points[i][0] < points[j][0]. 0 <= k <= 200000000. There exist indices i,j with 0 <= i < j < n and |points[i][0] - points[j][0]| <= k. -/
  theorem spec_5 (points : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (r : Std.I64)
      (h : ValidInput points k) (hr : find_max_value_of_equation points k = ok r) :
      2 * minY points ≤ r.val ∧ r.val ≤ 2 * maxY points + k.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (r : Std.I64)
        (h : ValidInput points k) (hr : find_max_value_of_equation points k = ok r), 2 * minY points ≤ r.val ∧ r.val ≤ 2 * maxY points + k.val) := by
    sorry

  /-- Whenever the function returns a result r, r equals the maximum of the set { (points[i][1] - points[i][0]) + (points[j][1] + points[j][0]) | 0 <= i < j < n and points[j][0] - points[i][0] <= k }.
    Preconditions: Let n = len(points). 2 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2, and points[i][0] and points[i][1] are integers in the closed interval [-100000000, 100000000]. For every 0 <= i < j < n, points[i][0] < points[j][0]. 0 <= k <= 200000000. There exist indices i,j with 0 <= i < j < n and |points[i][0] - points[j][0]| <= k. -/
  theorem spec_6 (points : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (r : Std.I64)
      (h : ValidInput points k) (hr : find_max_value_of_equation points k = ok r) :
      (∀ i j, i < j → j < nOf points →
        px (intPoints points) j - px (intPoints points) i ≤ k.val →
        cand' (intPoints points) i j ≤ r.val) ∧
      (∃ i j, i < j ∧ j < nOf points ∧
        px (intPoints points) j - px (intPoints points) i ≤ k.val ∧
        cand' (intPoints points) i j = r.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (r : Std.I64)
        (h : ValidInput points k) (hr : find_max_value_of_equation points k = ok r), (∀ i j, i < j → j < nOf points →
          px (intPoints points) j - px (intPoints points) i ≤ k.val →
          cand' (intPoints points) i j ≤ r.val) ∧
        (∃ i j, i < j ∧ j < nOf points ∧
          px (intPoints points) j - px (intPoints points) i ≤ k.val ∧
          cand' (intPoints points) i j = r.val)) := by
    sorry

  /-- Whenever the function returns r1 on input (points, k1) and returns r2 on input (points, k2), we have r1 <= r2.
    Preconditions: Let n = len(points). 2 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2, and points[i][0] and points[i][1] are integers in the closed interval [-100000000, 100000000]. For every 0 <= i < j < n, points[i][0] < points[j][0]. Let k1 and k2 be integers with 0 <= k1 <= k2 <= 200000000. There exist indices i,j with 0 <= i < j < n and |points[i][0] - points[j][0]| <= k1. (This implies the same existence condition holds for k2.) -/
  theorem spec_7 (points : Slice (alloc.vec.Vec Std.I64)) (k1 k2 : Std.I64) (r1 r2 : Std.I64)
      (hp : ValidPoints points)
      (hk1 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 200000000)
      (hex : ExistsPairWithin points k1.val)
      (h1 : find_max_value_of_equation points k1 = ok r1)
      (h2 : find_max_value_of_equation points k2 = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (k1 k2 : Std.I64) (r1 r2 : Std.I64)
        (hp : ValidPoints points)
        (hk1 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 200000000)
        (hex : ExistsPairWithin points k1.val)
        (h1 : find_max_value_of_equation points k1 = ok r1)
        (h2 : find_max_value_of_equation points k2 = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- Whenever the function returns r on input (points, k) and returns r' on input (points', k), we have r = r'.
    Preconditions: Let n = len(points). 2 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2, and points[i][0] and points[i][1] are integers in the closed interval [-100000000, 100000000]. For every 0 <= i < j < n, points[i][0] < points[j][0]. 0 <= k <= 200000000. There exist indices i,j with 0 <= i < j < n and |points[i][0] - points[j][0]| <= k. Let c be an integer such that points[i][0] + c is in [-100000000, 100000000] for every i. Define points' by points'[i][0] = points[i][0] + c and points'[i][1] = points[i][1] for 0 <= i < n. Then points' and k also satisfy the usual constraints. -/
  theorem spec_8 (points points' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (c : ℤ)
      (r r' : Std.I64)
      (h : ValidInput points k) (h' : ValidInput points' k)
      (hc : ∀ i, i < nOf points →
        -100000000 ≤ px (intPoints points) i + c ∧ px (intPoints points) i + c ≤ 100000000)
      (hs : IsXShift points points' c)
      (h1 : find_max_value_of_equation points k = ok r)
      (h2 : find_max_value_of_equation points' k = ok r') :
      r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (points points' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (c : ℤ)
        (r r' : Std.I64)
        (h : ValidInput points k) (h' : ValidInput points' k)
        (hc : ∀ i, i < nOf points →
          -100000000 ≤ px (intPoints points) i + c ∧ px (intPoints points) i + c ≤ 100000000)
        (hs : IsXShift points points' c)
        (h1 : find_max_value_of_equation points k = ok r)
        (h2 : find_max_value_of_equation points' k = ok r'), r = r') := by
    sorry

  /-- Whenever the function returns r on input (points, k) and returns r' on input (points', k), we have r' = r + 2*c.
    Preconditions: Let n = len(points). 2 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2, and points[i][0] and points[i][1] are integers in the closed interval [-100000000, 100000000]. For every 0 <= i < j < n, points[i][0] < points[j][0]. 0 <= k <= 200000000. There exist indices i,j with 0 <= i < j < n and |points[i][0] - points[j][0]| <= k. Let c be an integer such that points[i][1] + c is in [-100000000, 100000000] for every i. Define points' by points'[i][0] = points[i][0] and points'[i][1] = points[i][1] + c for 0 <= i < n. Then points' and k also satisfy the usual constraints. -/
  theorem spec_9 (points points' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (c : ℤ)
      (r r' : Std.I64)
      (h : ValidInput points k) (h' : ValidInput points' k)
      (hc : ∀ i, i < nOf points →
        -100000000 ≤ py (intPoints points) i + c ∧ py (intPoints points) i + c ≤ 100000000)
      (hs : IsYShift points points' c)
      (h1 : find_max_value_of_equation points k = ok r)
      (h2 : find_max_value_of_equation points' k = ok r') :
      r'.val = r.val + 2 * c := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (points points' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (c : ℤ)
        (r r' : Std.I64)
        (h : ValidInput points k) (h' : ValidInput points' k)
        (hc : ∀ i, i < nOf points →
          -100000000 ≤ py (intPoints points) i + c ∧ py (intPoints points) i + c ≤ 100000000)
        (hs : IsYShift points points' c)
        (h1 : find_max_value_of_equation points k = ok r)
        (h2 : find_max_value_of_equation points' k = ok r'), r'.val = r.val + 2 * c) := by
    sorry

  end AegisSpec.FindMaxValueOfEquation
