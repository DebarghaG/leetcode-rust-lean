import Aegis.MinDayskVariants.Code.Funs

/-!
# Specifications of `Aegis.MinDayskVariants.min_daysk_variants`

LeetCode problem `minimum-time-for-k-virus-variants-to-spread`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
  open Aegis.MinDayskVariants

  namespace AegisSpec.MinDayskVariants

  def pointX (p : alloc.vec.Vec I64) : Int :=
    match p.val[0]? with
    | some v => v.val
    | none => 0

  def pointY (p : alloc.vec.Vec I64) : Int :=
    match p.val[1]? with
    | some v => v.val
    | none => 0

  def pointAt (pts : List (alloc.vec.Vec I64)) (i : Nat) : Option (alloc.vec.Vec I64) :=
    pts[i]?

  def lenAt (pts : List (alloc.vec.Vec I64)) (i : Nat) : Nat :=
    match pointAt pts i with
    | some p => p.val.length
    | none => 0

  def xAt (pts : List (alloc.vec.Vec I64)) (i : Nat) : Int :=
    match pointAt pts i with
    | some p => pointX p
    | none => 0

  def yAt (pts : List (alloc.vec.Vec I64)) (i : Nat) : Int :=
    match pointAt pts i with
    | some p => pointY p
    | none => 0

  def centerDist (cx cy : Int) (p : alloc.vec.Vec I64) : Int :=
    |cx - pointX p| + |cy - pointY p|

  def nearCount (pts : List (alloc.vec.Vec I64)) (cx cy t : Int) : Int :=
    ((pts.filter (fun p => decide (centerDist cx cy p ≤ t))).length : Int)

  def maxCenterDist (pts : List (alloc.vec.Vec I64)) : Int :=
    pts.foldr (fun p acc => max acc (centerDist 50 50 p)) 0

  def pairDist (p q : alloc.vec.Vec I64) : Int :=
    |pointX p - pointX q| + |pointY p - pointY q|

  def diam (pts : List (alloc.vec.Vec I64)) : Int :=
    pts.foldr (fun p acc => max acc (pts.foldr (fun q acc' => max acc' (pairDist p q)) 0)) 0

  def minSubsetDiam (pts : List (alloc.vec.Vec I64)) (k : Int) : Int :=
    match (pts.sublists.filter (fun S => decide ((S.length : Int) = k))).map diam with
    | [] => 0
    | d :: ds => ds.foldr min d

  /-- Whenever the function returns a result r, r is the least non-negative integer t for which there exist integers x and y such that the number of indices i with 0 <= i < n and |x - points[i][0]| + |y - points[i][1]| <= t is at least k.
    Preconditions: Let n = len(points). The input satisfies 2 <= n <= 50, 2 <= k <= n, and for every i with 0 <= i < n, len(points[i]) = 2, 1 <= points[i][0] <= 100, and 1 <= points[i][1] <= 100. -/
  theorem spec_1
    (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (h_n : points.val.length = n)
    (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
    (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
    (h_rows : ∀ i, i < n →
      lenAt points.val i = 2 ∧
      1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
      1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
    (r : I64) (h_r : min_daysk_variants points k = ok r) :
    0 ≤ r.val ∧
      (∃ x y : Int, k.val ≤ nearCount points.val x y r.val) ∧
      (∀ t : Int, 0 ≤ t →
        (∃ x y : Int, k.val ≤ nearCount points.val x y t) → r.val ≤ t) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
      (h_n : points.val.length = n)
      (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
      (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
      (h_rows : ∀ i, i < n →
        lenAt points.val i = 2 ∧
        1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
        1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
      (r : I64) (h_r : min_daysk_variants points k = ok r), 0 ≤ r.val ∧
        (∃ x y : Int, k.val ≤ nearCount points.val x y r.val) ∧
        (∀ t : Int, 0 ≤ t →
          (∃ x y : Int, k.val ≤ nearCount points.val x y t) → r.val ≤ t)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; in particular, it does not fail, overflow, panic, or access an out-of-bounds index.
    Preconditions: Let n = len(points). The input satisfies 2 <= n <= 50, 2 <= k <= n, and for every i with 0 <= i < n, len(points[i]) = 2, 1 <= points[i][0] <= 100, and 1 <= points[i][1] <= 100. -/
  theorem spec_2
    (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (h_n : points.val.length = n)
    (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
    (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
    (h_rows : ∀ i, i < n →
      lenAt points.val i = 2 ∧
      1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
      1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100) :
    ∃ r : I64, min_daysk_variants points k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
      (h_n : points.val.length = n)
      (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
      (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
      (h_rows : ∀ i, i < n →
        lenAt points.val i = 2 ∧
        1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
        1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100), ∃ r : I64, min_daysk_variants points k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r <= max_{0 <= i < n} (|50 - points[i][0]| + |50 - points[i][1]|).
    Preconditions: Let n = len(points). The input satisfies 2 <= n <= 50, 2 <= k <= n, and for every i with 0 <= i < n, len(points[i]) = 2, 1 <= points[i][0] <= 100, and 1 <= points[i][1] <= 100. -/
  theorem spec_3
    (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (h_n : points.val.length = n)
    (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
    (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
    (h_rows : ∀ i, i < n →
      lenAt points.val i = 2 ∧
      1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
      1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
    (r : I64) (h_r : min_daysk_variants points k = ok r) :
    r.val ≤ maxCenterDist points.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
      (h_n : points.val.length = n)
      (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
      (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
      (h_rows : ∀ i, i < n →
        lenAt points.val i = 2 ∧
        1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
        1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
      (r : I64) (h_r : min_daysk_variants points k = ok r), r.val ≤ maxCenterDist points.val) := by
    sorry

  /-- Whenever the function returns a result r, 2*r >= D, where D is the minimum, over all subsets S of {0,...,n-1} with exactly k elements, of the maximum of |points[i][0] - points[j][0]| + |points[i][1] - points[j][1]| over all i in S and j in S.
    Preconditions: Let n = len(points). The input satisfies 2 <= n <= 50, 2 <= k <= n, and for every i with 0 <= i < n, len(points[i]) = 2, 1 <= points[i][0] <= 100, and 1 <= points[i][1] <= 100. -/
  theorem spec_4
    (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (h_n : points.val.length = n)
    (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
    (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
    (h_rows : ∀ i, i < n →
      lenAt points.val i = 2 ∧
      1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
      1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
    (r : I64) (h_r : min_daysk_variants points k = ok r) :
    2 * r.val ≥ minSubsetDiam points.val k.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
      (h_n : points.val.length = n)
      (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
      (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
      (h_rows : ∀ i, i < n →
        lenAt points.val i = 2 ∧
        1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
        1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
      (r : I64) (h_r : min_daysk_variants points k = ok r), 2 * r.val ≥ minSubsetDiam points.val k.val) := by
    sorry

  /-- Whenever the function returns a result r, there exist integers x and y such that the number of indices i with 0 <= i < n and |x - points[i][0]| + |y - points[i][1]| <= r is at least k.
    Preconditions: Let n = len(points). The input satisfies 2 <= n <= 50, 2 <= k <= n, and for every i with 0 <= i < n, len(points[i]) = 2, 1 <= points[i][0] <= 100, and 1 <= points[i][1] <= 100. -/
  theorem spec_5
    (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (h_n : points.val.length = n)
    (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
    (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
    (h_rows : ∀ i, i < n →
      lenAt points.val i = 2 ∧
      1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
      1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
    (r : I64) (h_r : min_daysk_variants points k = ok r) :
    ∃ x y : Int, k.val ≤ nearCount points.val x y r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
      (h_n : points.val.length = n)
      (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
      (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
      (h_rows : ∀ i, i < n →
        lenAt points.val i = 2 ∧
        1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
        1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
      (r : I64) (h_r : min_daysk_variants points k = ok r), ∃ x y : Int, k.val ≤ nearCount points.val x y r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer t with 0 <= t < r and every pair of integers x and y, the number of indices i with 0 <= i < n and |x - points[i][0]| + |y - points[i][1]| <= t is less than k.
    Preconditions: Let n = len(points). The input satisfies 2 <= n <= 50, 2 <= k <= n, and for every i with 0 <= i < n, len(points[i]) = 2, 1 <= points[i][0] <= 100, and 1 <= points[i][1] <= 100. -/
  theorem spec_6
    (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (h_n : points.val.length = n)
    (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
    (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
    (h_rows : ∀ i, i < n →
      lenAt points.val i = 2 ∧
      1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
      1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
    (r : I64) (h_r : min_daysk_variants points k = ok r) :
    ∀ t : Int, 0 ≤ t → t < r.val →
      ∀ x y : Int, nearCount points.val x y t < k.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
      (h_n : points.val.length = n)
      (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
      (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
      (h_rows : ∀ i, i < n →
        lenAt points.val i = 2 ∧
        1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
        1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
      (r : I64) (h_r : min_daysk_variants points k = ok r), ∀ t : Int, 0 ≤ t → t < r.val →
        ∀ x y : Int, nearCount points.val x y t < k.val) := by
    sorry

  /-- For every permutation P of {0,...,n-1}, let q be the array of length n defined by q[i] = points[P(i)] for 0 <= i < n. If the function returns r on (points,k) and returns r' on (q,k), then r' = r.
    Preconditions: Let n = len(points). The input satisfies 2 <= n <= 50, 2 <= k <= n, and for every i with 0 <= i < n, len(points[i]) = 2, 1 <= points[i][0] <= 100, and 1 <= points[i][1] <= 100. -/
  theorem spec_7
    (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (h_n : points.val.length = n)
    (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
    (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
    (h_rows : ∀ i, i < n →
      lenAt points.val i = 2 ∧
      1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
      1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
    (q : Slice (alloc.vec.Vec I64)) (h_q : q.val.Perm points.val)
    (r r' : I64)
    (h_r : min_daysk_variants points k = ok r)
    (h_r' : min_daysk_variants q k = ok r') :
    r' = r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
      (h_n : points.val.length = n)
      (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
      (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
      (h_rows : ∀ i, i < n →
        lenAt points.val i = 2 ∧
        1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
        1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
      (q : Slice (alloc.vec.Vec I64)) (h_q : q.val.Perm points.val)
      (r r' : I64)
      (h_r : min_daysk_variants points k = ok r)
      (h_r' : min_daysk_variants q k = ok r'), r' = r) := by
    sorry

  /-- For any integers a and b such that 1 <= points[i][0] + a <= 100 and 1 <= points[i][1] + b <= 100 for every i with 0 <= i < n, let q be the array with q[i] = [points[i][0] + a, points[i][1] + b]. If the function returns r on (points,k) and returns r' on (q,k), then r' = r.
    Preconditions: Let n = len(points). The input satisfies 2 <= n <= 50, 2 <= k <= n, and for every i with 0 <= i < n, len(points[i]) = 2, 1 <= points[i][0] <= 100, and 1 <= points[i][1] <= 100. -/
  theorem spec_8
    (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (h_n : points.val.length = n)
    (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
    (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
    (h_rows : ∀ i, i < n →
      lenAt points.val i = 2 ∧
      1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
      1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
    (a b : Int)
    (h_ab : ∀ i, i < n →
      1 ≤ xAt points.val i + a ∧ xAt points.val i + a ≤ 100 ∧
      1 ≤ yAt points.val i + b ∧ yAt points.val i + b ≤ 100)
    (q : Slice (alloc.vec.Vec I64)) (h_q_len : q.val.length = n)
    (h_q : ∀ i, i < n →
      xAt q.val i = xAt points.val i + a ∧ yAt q.val i = yAt points.val i + b)
    (r r' : I64)
    (h_r : min_daysk_variants points k = ok r)
    (h_r' : min_daysk_variants q k = ok r') :
    r' = r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
      (h_n : points.val.length = n)
      (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
      (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
      (h_rows : ∀ i, i < n →
        lenAt points.val i = 2 ∧
        1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
        1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
      (a b : Int)
      (h_ab : ∀ i, i < n →
        1 ≤ xAt points.val i + a ∧ xAt points.val i + a ≤ 100 ∧
        1 ≤ yAt points.val i + b ∧ yAt points.val i + b ≤ 100)
      (q : Slice (alloc.vec.Vec I64)) (h_q_len : q.val.length = n)
      (h_q : ∀ i, i < n →
        xAt q.val i = xAt points.val i + a ∧ yAt q.val i = yAt points.val i + b)
      (r r' : I64)
      (h_r : min_daysk_variants points k = ok r)
      (h_r' : min_daysk_variants q k = ok r'), r' = r) := by
    sorry

  /-- Let q be the array with q[i] = [101 - points[i][0], points[i][1]] for every i with 0 <= i < n. If the function returns r on (points,k) and returns r' on (q,k), then r' = r.
    Preconditions: Let n = len(points). The input satisfies 2 <= n <= 50, 2 <= k <= n, and for every i with 0 <= i < n, len(points[i]) = 2, 1 <= points[i][0] <= 100, and 1 <= points[i][1] <= 100. -/
  theorem spec_9
    (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (h_n : points.val.length = n)
    (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
    (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
    (h_rows : ∀ i, i < n →
      lenAt points.val i = 2 ∧
      1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
      1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
    (q : Slice (alloc.vec.Vec I64)) (h_q_len : q.val.length = n)
    (h_q : ∀ i, i < n →
      xAt q.val i = 101 - xAt points.val i ∧ yAt q.val i = yAt points.val i)
    (r r' : I64)
    (h_r : min_daysk_variants points k = ok r)
    (h_r' : min_daysk_variants q k = ok r') :
    r' = r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
      (h_n : points.val.length = n)
      (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
      (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
      (h_rows : ∀ i, i < n →
        lenAt points.val i = 2 ∧
        1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
        1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
      (q : Slice (alloc.vec.Vec I64)) (h_q_len : q.val.length = n)
      (h_q : ∀ i, i < n →
        xAt q.val i = 101 - xAt points.val i ∧ yAt q.val i = yAt points.val i)
      (r r' : I64)
      (h_r : min_daysk_variants points k = ok r)
      (h_r' : min_daysk_variants q k = ok r'), r' = r) := by
    sorry

  /-- Let q be the array with q[i] = [points[i][1], points[i][0]] for every i with 0 <= i < n. If the function returns r on (points,k) and returns r' on (q,k), then r' = r.
    Preconditions: Let n = len(points). The input satisfies 2 <= n <= 50, 2 <= k <= n, and for every i with 0 <= i < n, len(points[i]) = 2, 1 <= points[i][0] <= 100, and 1 <= points[i][1] <= 100. -/
  theorem spec_10
    (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (h_n : points.val.length = n)
    (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
    (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
    (h_rows : ∀ i, i < n →
      lenAt points.val i = 2 ∧
      1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
      1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
    (q : Slice (alloc.vec.Vec I64)) (h_q_len : q.val.length = n)
    (h_q : ∀ i, i < n →
      xAt q.val i = yAt points.val i ∧ yAt q.val i = xAt points.val i)
    (r r' : I64)
    (h_r : min_daysk_variants points k = ok r)
    (h_r' : min_daysk_variants q k = ok r') :
    r' = r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
      (h_n : points.val.length = n)
      (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
      (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
      (h_rows : ∀ i, i < n →
        lenAt points.val i = 2 ∧
        1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
        1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
      (q : Slice (alloc.vec.Vec I64)) (h_q_len : q.val.length = n)
      (h_q : ∀ i, i < n →
        xAt q.val i = yAt points.val i ∧ yAt q.val i = xAt points.val i)
      (r r' : I64)
      (h_r : min_daysk_variants points k = ok r)
      (h_r' : min_daysk_variants q k = ok r'), r' = r) := by
    sorry

  /-- For any integer k' with k <= k' <= n, if the function returns r on (points,k) and returns r' on (points,k'), then r <= r'.
    Preconditions: Let n = len(points). The input satisfies 2 <= n <= 50, 2 <= k <= n, and for every i with 0 <= i < n, len(points[i]) = 2, 1 <= points[i][0] <= 100, and 1 <= points[i][1] <= 100. -/
  theorem spec_11
    (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (h_n : points.val.length = n)
    (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
    (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
    (h_rows : ∀ i, i < n →
      lenAt points.val i = 2 ∧
      1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
      1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
    (k' : I64) (h_k' : k.val ≤ k'.val) (h_k'n : k'.val ≤ (n : Int))
    (r r' : I64)
    (h_r : min_daysk_variants points k = ok r)
    (h_r' : min_daysk_variants points k' = ok r') :
    r.val ≤ r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
      (h_n : points.val.length = n)
      (h_n2 : 2 ≤ n) (h_n50 : n ≤ 50)
      (h_k2 : 2 ≤ k.val) (h_kn : k.val ≤ (n : Int))
      (h_rows : ∀ i, i < n →
        lenAt points.val i = 2 ∧
        1 ≤ xAt points.val i ∧ xAt points.val i ≤ 100 ∧
        1 ≤ yAt points.val i ∧ yAt points.val i ≤ 100)
      (k' : I64) (h_k' : k.val ≤ k'.val) (h_k'n : k'.val ≤ (n : Int))
      (r r' : I64)
      (h_r : min_daysk_variants points k = ok r)
      (h_r' : min_daysk_variants points k' = ok r'), r.val ≤ r'.val) := by
    sorry

  end AegisSpec.MinDayskVariants
