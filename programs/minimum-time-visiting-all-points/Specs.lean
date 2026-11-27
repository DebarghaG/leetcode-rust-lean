import Aegis.MinTimeToVisitAllPoints.Code.Funs

/-!
# Specifications of `Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points`

LeetCode problem `minimum-time-visiting-all-points`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinTimeToVisitAllPoints

  def coordOf (l : List Std.I64) (j : ℕ) : ℤ :=
    match l[j]? with
    | some x => x.val
    | none => 0

  def pts (points : Slice (alloc.vec.Vec Std.I64)) : List (List Std.I64) :=
    points.val.map (fun v => v.val)

  def coordAt (points : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
    coordOf ((pts points).getD i []) j

  def metric (p q : List Std.I64) : ℤ :=
    max (|coordOf p 0 - coordOf q 0|) (|coordOf p 1 - coordOf q 1|)

  def distAt (l : List (List Std.I64)) (i j : ℕ) : ℤ :=
    metric (l.getD i []) (l.getD j [])

  def totalTime : List (List Std.I64) → ℤ
    | p :: q :: rest => metric p q + totalTime (q :: rest)
    | _ => 0

  def insertCopy {α : Type} (l : List α) (k : ℕ) : List α :=
    l.take (k + 1) ++ l.drop k

  def Precond (points : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    1 ≤ points.val.length ∧ points.val.length ≤ 100 ∧
      ∀ p ∈ points.val, p.val.length = 2 ∧
        -1000 ≤ coordOf p.val 0 ∧ coordOf p.val 0 ≤ 1000 ∧
        -1000 ≤ coordOf p.val 1 ∧ coordOf p.val 1 ≤ 1000

  /-- The function returns a result r, and r = sum_{i=0}^{n-2} max(|points[i][0] - points[i+1][0]|, |points[i][1] - points[i+1][1]|). If n = 1 the sum is empty and r = 0.
    Preconditions: Let n = len(points). The input satisfies 1 <= n <= 100; for every i with 0 <= i < n, len(points[i]) = 2 and -1000 <= points[i][0] <= 1000 and -1000 <= points[i][1] <= 1000. Indices are 0-based. -/
  theorem spec_1 (points : Slice (alloc.vec.Vec Std.I64)) (h : Precond points) :
      ∃ r, Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points = ok r ∧
        r.val = totalTime (pts points) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : Precond points), ∃ r, Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points = ok r ∧
          r.val = totalTime (pts points)) := by
    sorry

  /-- The function returns a result r (it does not fail: no arithmetic overflow, out-of-bounds access, or panic occurs).
    Preconditions: Let n = len(points). The input satisfies 1 <= n <= 100; for every i with 0 <= i < n, len(points[i]) = 2 and -1000 <= points[i][0] <= 1000 and -1000 <= points[i][1] <= 1000. Indices are 0-based. -/
  theorem spec_2 (points : Slice (alloc.vec.Vec Std.I64)) (h : Precond points) :
      ∃ r, Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : Precond points), ∃ r, Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= 2000 * (n - 1).
    Preconditions: Let n = len(points). The input satisfies 1 <= n <= 100; for every i with 0 <= i < n, len(points[i]) = 2 and -1000 <= points[i][0] <= 1000 and -1000 <= points[i][1] <= 1000. Indices are 0-based. -/
  theorem spec_3 (points : Slice (alloc.vec.Vec Std.I64)) (h : Precond points) :
      ∀ r, Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points = ok r →
        0 ≤ r.val ∧ r.val ≤ 2000 * ((points.val.length : ℤ) - 1) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : Precond points), ∀ r, Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points = ok r →
          0 ≤ r.val ∧ r.val ≤ 2000 * ((points.val.length : ℤ) - 1)) := by
    sorry

  /-- The function returns results r and r' for points and points', respectively, and r = r'.
    Preconditions: The list points satisfies the standard precondition: n = len(points), 1 <= n <= 100, and for every i with 0 <= i < n, len(points[i]) = 2 and -1000 <= points[i][0] <= 1000 and -1000 <= points[i][1] <= 1000. Let a and b be integers, and define points'[i][0] = points[i][0] + a and points'[i][1] = points[i][1] + b for every i; assume points' also satisfies the standard precondition. -/
  theorem spec_4 (points points' : Slice (alloc.vec.Vec Std.I64)) (a b : ℤ)
      (h : Precond points) (h' : Precond points')
      (hlen : points'.val.length = points.val.length)
      (htrans : ∀ i : ℕ, i < points.val.length →
        coordAt points' i 0 = coordAt points i 0 + a ∧
        coordAt points' i 1 = coordAt points i 1 + b) :
      ∃ r r', Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points = ok r ∧
        Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points' = ok r' ∧
        r.val = r'.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (points points' : Slice (alloc.vec.Vec Std.I64)) (a b : ℤ)
        (h : Precond points) (h' : Precond points')
        (hlen : points'.val.length = points.val.length)
        (htrans : ∀ i : ℕ, i < points.val.length →
          coordAt points' i 0 = coordAt points i 0 + a ∧
          coordAt points' i 1 = coordAt points i 1 + b), ∃ r r', Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points = ok r ∧
          Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points' = ok r' ∧
          r.val = r'.val) := by
    sorry

  /-- The function returns results r and r' for points and points', respectively, and r' = c * r.
    Preconditions: The list points satisfies the standard precondition: n = len(points), 1 <= n <= 100, and for every i with 0 <= i < n, len(points[i]) = 2 and -1000 <= points[i][0] <= 1000 and -1000 <= points[i][1] <= 1000. Let c be a nonnegative integer such that for every i, -1000 <= c * points[i][0] <= 1000 and -1000 <= c * points[i][1] <= 1000. Define points'[i][0] = c * points[i][0] and points'[i][1] = c * points[i][1]. -/
  theorem spec_5 (points points' : Slice (alloc.vec.Vec Std.I64)) (c : ℤ)
      (h : Precond points) (hc : 0 ≤ c)
      (hbounds : ∀ i : ℕ, i < points.val.length →
        -1000 ≤ c * coordAt points i 0 ∧ c * coordAt points i 0 ≤ 1000 ∧
        -1000 ≤ c * coordAt points i 1 ∧ c * coordAt points i 1 ≤ 1000)
      (hlen : points'.val.length = points.val.length)
      (hscale : ∀ i : ℕ, i < points.val.length →
        coordAt points' i 0 = c * coordAt points i 0 ∧
        coordAt points' i 1 = c * coordAt points i 1) :
      ∃ r r', Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points = ok r ∧
        Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points' = ok r' ∧
        r'.val = c * r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (points points' : Slice (alloc.vec.Vec Std.I64)) (c : ℤ)
        (h : Precond points) (hc : 0 ≤ c)
        (hbounds : ∀ i : ℕ, i < points.val.length →
          -1000 ≤ c * coordAt points i 0 ∧ c * coordAt points i 0 ≤ 1000 ∧
          -1000 ≤ c * coordAt points i 1 ∧ c * coordAt points i 1 ≤ 1000)
        (hlen : points'.val.length = points.val.length)
        (hscale : ∀ i : ℕ, i < points.val.length →
          coordAt points' i 0 = c * coordAt points i 0 ∧
          coordAt points' i 1 = c * coordAt points i 1), ∃ r r', Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points = ok r ∧
          Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points' = ok r' ∧
          r'.val = c * r.val) := by
    sorry

  /-- The function returns results r and r' for points and points', respectively, and r' = r.
    Preconditions: The list points satisfies the standard precondition: n = len(points), 1 <= n <= 100, and for every i with 0 <= i < n, len(points[i]) = 2 and -1000 <= points[i][0] <= 1000 and -1000 <= points[i][1] <= 1000. Let k be an integer with 0 <= k < n and n <= 99. Let points' be the list obtained from points by inserting an additional copy of points[k] immediately after index k. -/
  theorem spec_6 (points points' : Slice (alloc.vec.Vec Std.I64)) (k : ℕ)
      (h : Precond points) (hk : k < points.val.length)
      (hn : points.val.length ≤ 99)
      (hins : pts points' = insertCopy (pts points) k) :
      ∃ r r', Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points = ok r ∧
        Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points' = ok r' ∧
        r.val = r'.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (points points' : Slice (alloc.vec.Vec Std.I64)) (k : ℕ)
        (h : Precond points) (hk : k < points.val.length)
        (hn : points.val.length ≤ 99)
        (hins : pts points' = insertCopy (pts points) k), ∃ r r', Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points = ok r ∧
          Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points' = ok r' ∧
          r.val = r'.val) := by
    sorry

  /-- The function returns results r, r_L, and r_R for points, L, and R, respectively, and r = r_L + d + r_R.
    Preconditions: The list points satisfies the standard precondition: n = len(points), 1 <= n <= 100, and for every i with 0 <= i < n, len(points[i]) = 2 and -1000 <= points[i][0] <= 1000 and -1000 <= points[i][1] <= 1000. Let k be an integer with 1 <= k < n. Let L be the list points[0],...,points[k-1] and R the list points[k],...,points[n-1]. Let d = max(|points[k-1][0] - points[k][0]|, |points[k-1][1] - points[k][1]|). -/
  theorem spec_7 (points L R : Slice (alloc.vec.Vec Std.I64)) (k : ℕ)
      (h : Precond points) (hk1 : 1 ≤ k) (hkn : k < points.val.length)
      (hL : pts L = (pts points).take k) (hR : pts R = (pts points).drop k) :
      ∃ r rL rR, Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points = ok r ∧
        Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points L = ok rL ∧
        Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points R = ok rR ∧
        r.val = rL.val + distAt (pts points) (k - 1) k + rR.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (points L R : Slice (alloc.vec.Vec Std.I64)) (k : ℕ)
        (h : Precond points) (hk1 : 1 ≤ k) (hkn : k < points.val.length)
        (hL : pts L = (pts points).take k) (hR : pts R = (pts points).drop k), ∃ r rL rR, Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points = ok r ∧
          Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points L = ok rL ∧
          Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points R = ok rR ∧
          r.val = rL.val + distAt (pts points) (k - 1) k + rR.val) := by
    sorry

  /-- Whenever the function returns a result r, r >= max(|points[0][0] - points[n-1][0]|, |points[0][1] - points[n-1][1]|).
    Preconditions: Let n = len(points). The input satisfies 1 <= n <= 100; for every i with 0 <= i < n, len(points[i]) = 2 and -1000 <= points[i][0] <= 1000 and -1000 <= points[i][1] <= 1000. Indices are 0-based. -/
  theorem spec_8 (points : Slice (alloc.vec.Vec Std.I64)) (h : Precond points) :
      ∀ r, Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points = ok r →
        distAt (pts points) 0 (points.val.length - 1) ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : Precond points), ∀ r, Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points = ok r →
          distAt (pts points) 0 (points.val.length - 1) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer i with 0 <= i < n-1, r >= max(|points[i][0] - points[i+1][0]|, |points[i][1] - points[i+1][1]|).
    Preconditions: Let n = len(points). The input satisfies 1 <= n <= 100; for every i with 0 <= i < n, len(points[i]) = 2 and -1000 <= points[i][0] <= 1000 and -1000 <= points[i][1] <= 1000. Indices are 0-based. -/
  theorem spec_9 (points : Slice (alloc.vec.Vec Std.I64)) (h : Precond points) :
      ∀ r, Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points = ok r →
        ∀ i : ℕ, i < points.val.length - 1 → distAt (pts points) i (i + 1) ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : Precond points), ∀ r, Aegis.MinTimeToVisitAllPoints.min_time_to_visit_all_points points = ok r →
          ∀ i : ℕ, i < points.val.length - 1 → distAt (pts points) i (i + 1) ≤ r.val) := by
    sorry

  end AegisSpec.MinTimeToVisitAllPoints
