import Aegis.MaxDistance.Code.Funs

/-!
# Specifications of `Aegis.MaxDistance.max_distance`

LeetCode problem `maximize-the-distance-between-points-on-a-square`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxDistance

def absDiff (a b : Int) : Int := if a ≤ b then b - a else a - b

def coordOf (v : alloc.vec.Vec I64) (t : Nat) : Int :=
  ((v.val[t]?).map (fun z => z.val)).getD 0

def coords (points : Slice (alloc.vec.Vec I64)) : List (Int × Int) :=
  points.val.map (fun v => (coordOf v 0, coordOf v 1))

def numPoints (points : Slice (alloc.vec.Vec I64)) : Nat := points.val.length

def pairAt (points : Slice (alloc.vec.Vec I64)) (i : Nat) : Int × Int :=
  ((coords points)[i]?).getD (0, 0)

def manhattan (points : Slice (alloc.vec.Vec I64)) (i j : Nat) : Int :=
  absDiff (pairAt points i).1 (pairAt points j).1 +
    absDiff (pairAt points i).2 (pairAt points j).2

def pointSet (points : Slice (alloc.vec.Vec I64)) : Finset (Int × Int) :=
  (coords points).toFinset

def kSubsets (n k : Nat) : Finset (Finset Nat) :=
  (Finset.range n).powersetCard k

noncomputable def minPairDist (points : Slice (alloc.vec.Vec I64)) (S : Finset Nat) : Int :=
  let T : Finset Int :=
    ((S.product S).filter (fun p : Nat × Nat => p.1 < p.2)).image (fun p => manhattan points p.1 p.2)
  if h : T.Nonempty then T.min' h else 0

noncomputable def maxMinDist (points : Slice (alloc.vec.Vec I64)) (n k : Nat) : Int :=
  let F : Finset Int := (kSubsets n k).image (minPairDist points)
  if h : F.Nonempty then F.max' h else 0

def ValidInput (side : I64) (points : Slice (alloc.vec.Vec I64)) (k : I64) : Prop :=
  (∀ v ∈ points.val, v.val.length = 2) ∧
  1 ≤ side.val ∧ side.val ≤ 1000000000 ∧
  numPoints points ≤ 15000 ∧
  4 ≤ k.val ∧ k.val ≤ min (25 : Int) (numPoints points : Int) ∧
  (numPoints points : Int) ≤ 4 * side.val ∧
  (∀ p ∈ coords points, 0 ≤ p.1 ∧ p.1 ≤ side.val ∧ 0 ≤ p.2 ∧ p.2 ≤ side.val) ∧
  (∀ p ∈ coords points, p.1 = 0 ∨ p.1 = side.val ∨ p.2 = 0 ∨ p.2 = side.val) ∧
  (coords points).Nodup

/-- Whenever the function returns a result r, r is the maximum possible minimum Manhattan distance: r = max { min { D(i,j) : i and j are in S and i < j } : S is a subset of {0,...,n-1} with |S| = k }. Equivalently, there exists a k-element index set S with D(i,j) >= r for all distinct i,j in S, and for every k-element index set T there exist distinct i,j in T with D(i,j) <= r.
  Preconditions: Let n = len(points). For every i with 0 <= i < n, len(points[i]) = 2; write x_i = points[i][0], y_i = points[i][1], and D(i,j) = |x_i - x_j| + |y_i - y_j|. Assume 1 <= side <= 10^9, n <= 15000, 4 <= k <= min(25, n), n <= 4*side, 0 <= x_i <= side, 0 <= y_i <= side, each (x_i, y_i) lies on the boundary of the square (x_i = 0 or x_i = side or y_i = 0 or y_i = side), and (x_i, y_i) != (x_j, y_j) for every i != j. -/
theorem spec_1 (side : I64) (points : Slice (alloc.vec.Vec I64)) (k : I64) (r : I64)
    (h : ValidInput side points k)
    (hr : Aegis.MaxDistance.max_distance side points k = ok r) :
    r.val = maxMinDist points (numPoints points) k.val.toNat ∧
      (∃ S : Finset Nat,
        S ⊆ Finset.range (numPoints points) ∧ S.card = k.val.toNat ∧
          ∀ i ∈ S, ∀ j ∈ S, i < j → r.val ≤ manhattan points i j) ∧
      (∀ T : Finset Nat,
        T ⊆ Finset.range (numPoints points) → T.card = k.val.toNat →
          ∃ i ∈ T, ∃ j ∈ T, i < j ∧ manhattan points i j ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (side : I64) (points : Slice (alloc.vec.Vec I64)) (k : I64) (r : I64)
    (h : ValidInput side points k)
    (hr : Aegis.MaxDistance.max_distance side points k = ok r), r.val = maxMinDist points (numPoints points) k.val.toNat ∧
      (∃ S : Finset Nat,
        S ⊆ Finset.range (numPoints points) ∧ S.card = k.val.toNat ∧
          ∀ i ∈ S, ∀ j ∈ S, i < j → r.val ≤ manhattan points i j) ∧
      (∀ T : Finset Nat,
        T ⊆ Finset.range (numPoints points) → T.card = k.val.toNat →
          ∃ i ∈ T, ∃ j ∈ T, i < j ∧ manhattan points i j ≤ r.val)) := by
  sorry

/-- The function returns a result r; it does not fail, overflow, panic, or go out of bounds.
  Preconditions: Let n = len(points). For every i with 0 <= i < n, len(points[i]) = 2; write x_i = points[i][0], y_i = points[i][1]. Assume 1 <= side <= 10^9, n <= 15000, 4 <= k <= min(25, n), n <= 4*side, 0 <= x_i <= side, 0 <= y_i <= side, each (x_i, y_i) lies on the boundary of the square (x_i = 0 or x_i = side or y_i = 0 or y_i = side), and (x_i, y_i) != (x_j, y_j) for every i != j. -/
theorem spec_2 (side : I64) (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (h : ValidInput side points k) :
    ∃ r : I64, Aegis.MaxDistance.max_distance side points k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (side : I64) (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (h : ValidInput side points k), ∃ r : I64, Aegis.MaxDistance.max_distance side points k = ok r) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r <= side.
  Preconditions: Let n = len(points). For every i with 0 <= i < n, len(points[i]) = 2; write x_i = points[i][0], y_i = points[i][1], and D(i,j) = |x_i - x_j| + |y_i - y_j|. Assume 1 <= side <= 10^9, n <= 15000, 4 <= k <= min(25, n), n <= 4*side, 0 <= x_i <= side, 0 <= y_i <= side, each (x_i, y_i) lies on the boundary of the square (x_i = 0 or x_i = side or y_i = 0 or y_i = side), and (x_i, y_i) != (x_j, y_j) for every i != j. -/
theorem spec_3 (side : I64) (points : Slice (alloc.vec.Vec I64)) (k : I64) (r : I64)
    (h : ValidInput side points k)
    (hr : Aegis.MaxDistance.max_distance side points k = ok r) :
    1 ≤ r.val ∧ r.val ≤ side.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (side : I64) (points : Slice (alloc.vec.Vec I64)) (k : I64) (r : I64)
    (h : ValidInput side points k)
    (hr : Aegis.MaxDistance.max_distance side points k = ok r), 1 ≤ r.val ∧ r.val ≤ side.val) := by
  sorry

/-- Whenever the function returns a result r, there exists a set S of exactly k indices from {0,...,n-1} such that min { D(i,j) : i and j are in S and i < j } = r.
  Preconditions: Let n = len(points). For every i with 0 <= i < n, len(points[i]) = 2; write x_i = points[i][0], y_i = points[i][1], and D(i,j) = |x_i - x_j| + |y_i - y_j|. Assume 1 <= side <= 10^9, n <= 15000, 4 <= k <= min(25, n), n <= 4*side, 0 <= x_i <= side, 0 <= y_i <= side, each (x_i, y_i) lies on the boundary of the square (x_i = 0 or x_i = side or y_i = 0 or y_i = side), and (x_i, y_i) != (x_j, y_j) for every i != j. -/
theorem spec_4 (side : I64) (points : Slice (alloc.vec.Vec I64)) (k : I64) (r : I64)
    (h : ValidInput side points k)
    (hr : Aegis.MaxDistance.max_distance side points k = ok r) :
    ∃ S : Finset Nat,
      S ⊆ Finset.range (numPoints points) ∧ S.card = k.val.toNat ∧
        minPairDist points S = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (side : I64) (points : Slice (alloc.vec.Vec I64)) (k : I64) (r : I64)
    (h : ValidInput side points k)
    (hr : Aegis.MaxDistance.max_distance side points k = ok r), ∃ S : Finset Nat,
      S ⊆ Finset.range (numPoints points) ∧ S.card = k.val.toNat ∧
        minPairDist points S = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every set T of exactly k indices from {0,...,n-1}, there exist distinct i,j in T with D(i,j) <= r.
  Preconditions: Let n = len(points). For every i with 0 <= i < n, len(points[i]) = 2; write x_i = points[i][0], y_i = points[i][1], and D(i,j) = |x_i - x_j| + |y_i - y_j|. Assume 1 <= side <= 10^9, n <= 15000, 4 <= k <= min(25, n), n <= 4*side, 0 <= x_i <= side, 0 <= y_i <= side, each (x_i, y_i) lies on the boundary of the square (x_i = 0 or x_i = side or y_i = 0 or y_i = side), and (x_i, y_i) != (x_j, y_j) for every i != j. -/
theorem spec_5 (side : I64) (points : Slice (alloc.vec.Vec I64)) (k : I64) (r : I64)
    (h : ValidInput side points k)
    (hr : Aegis.MaxDistance.max_distance side points k = ok r) :
    ∀ T : Finset Nat,
      T ⊆ Finset.range (numPoints points) → T.card = k.val.toNat →
        ∃ i ∈ T, ∃ j ∈ T, i < j ∧ manhattan points i j ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (side : I64) (points : Slice (alloc.vec.Vec I64)) (k : I64) (r : I64)
    (h : ValidInput side points k)
    (hr : Aegis.MaxDistance.max_distance side points k = ok r), ∀ T : Finset Nat,
      T ⊆ Finset.range (numPoints points) → T.card = k.val.toNat →
        ∃ i ∈ T, ∃ j ∈ T, i < j ∧ manhattan points i j ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = min { D(i,j) : 0 <= i < j < n }.
  Preconditions: Let n = len(points). For every i with 0 <= i < n, len(points[i]) = 2; write x_i = points[i][0], y_i = points[i][1], and D(i,j) = |x_i - x_j| + |y_i - y_j|. Assume 1 <= side <= 10^9, n <= 15000, 4 <= k <= min(25, n), n <= 4*side, 0 <= x_i <= side, 0 <= y_i <= side, each (x_i, y_i) lies on the boundary of the square (x_i = 0 or x_i = side or y_i = 0 or y_i = side), (x_i, y_i) != (x_j, y_j) for every i != j, and k = n. -/
theorem spec_6 (side : I64) (points : Slice (alloc.vec.Vec I64)) (k : I64) (r : I64)
    (h : ValidInput side points k) (hkn : k.val = (numPoints points : Int))
    (hr : Aegis.MaxDistance.max_distance side points k = ok r) :
    r.val = minPairDist points (Finset.range (numPoints points)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (side : I64) (points : Slice (alloc.vec.Vec I64)) (k : I64) (r : I64)
    (h : ValidInput side points k) (hkn : k.val = (numPoints points : Int))
    (hr : Aegis.MaxDistance.max_distance side points k = ok r), r.val = minPairDist points (Finset.range (numPoints points))) := by
  sorry

/-- Whenever the function returns a result r, r = side.
  Preconditions: Let n = len(points). For every i with 0 <= i < n, len(points[i]) = 2; write x_i = points[i][0], y_i = points[i][1], and D(i,j) = |x_i - x_j| + |y_i - y_j|. Assume 1 <= side <= 10^9, n <= 15000, 4 <= k <= min(25, n), n <= 4*side, 0 <= x_i <= side, 0 <= y_i <= side, each (x_i, y_i) lies on the boundary of the square (x_i = 0 or x_i = side or y_i = 0 or y_i = side), (x_i, y_i) != (x_j, y_j) for every i != j, k = 4, and the four coordinate pairs (0,0), (0,side), (side,0), (side,side) all occur among the points. -/
theorem spec_7 (side : I64) (points : Slice (alloc.vec.Vec I64)) (k : I64) (r : I64)
    (h : ValidInput side points k) (hk4 : k.val = 4)
    (hc : (0, 0) ∈ pointSet points ∧ (0, side.val) ∈ pointSet points ∧
      (side.val, 0) ∈ pointSet points ∧ (side.val, side.val) ∈ pointSet points)
    (hr : Aegis.MaxDistance.max_distance side points k = ok r) :
    r.val = side.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (side : I64) (points : Slice (alloc.vec.Vec I64)) (k : I64) (r : I64)
    (h : ValidInput side points k) (hk4 : k.val = 4)
    (hc : (0, 0) ∈ pointSet points ∧ (0, side.val) ∈ pointSet points ∧
      (side.val, 0) ∈ pointSet points ∧ (side.val, side.val) ∈ pointSet points)
    (hr : Aegis.MaxDistance.max_distance side points k = ok r), r.val = side.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer t with 0 <= t <= side, r >= t if and only if there exists a set S of exactly k indices such that D(i,j) >= t for all distinct i,j in S.
  Preconditions: Let n = len(points). For every i with 0 <= i < n, len(points[i]) = 2; write x_i = points[i][0], y_i = points[i][1], and D(i,j) = |x_i - x_j| + |y_i - y_j|. Assume 1 <= side <= 10^9, n <= 15000, 4 <= k <= min(25, n), n <= 4*side, 0 <= x_i <= side, 0 <= y_i <= side, each (x_i, y_i) lies on the boundary of the square (x_i = 0 or x_i = side or y_i = 0 or y_i = side), and (x_i, y_i) != (x_j, y_j) for every i != j. -/
theorem spec_8 (side : I64) (points : Slice (alloc.vec.Vec I64)) (k : I64) (r : I64)
    (h : ValidInput side points k)
    (hr : Aegis.MaxDistance.max_distance side points k = ok r) :
    ∀ t : Int,
      0 ≤ t → t ≤ side.val →
        (t ≤ r.val ↔
          ∃ S : Finset Nat,
            S ⊆ Finset.range (numPoints points) ∧ S.card = k.val.toNat ∧
              ∀ i ∈ S, ∀ j ∈ S, i < j → t ≤ manhattan points i j) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (side : I64) (points : Slice (alloc.vec.Vec I64)) (k : I64) (r : I64)
    (h : ValidInput side points k)
    (hr : Aegis.MaxDistance.max_distance side points k = ok r), ∀ t : Int,
      0 ≤ t → t ≤ side.val →
        (t ≤ r.val ↔
          ∃ S : Finset Nat,
            S ⊆ Finset.range (numPoints points) ∧ S.card = k.val.toNat ∧
              ∀ i ∈ S, ∀ j ∈ S, i < j → t ≤ manhattan points i j)) := by
  sorry

/-- Whenever the function returns r for (side, points, k) and returns r2 for (side, points, k2), we have r >= r2.
  Preconditions: Let n = len(points). For every i with 0 <= i < n, len(points[i]) = 2; write x_i = points[i][0], y_i = points[i][1], and D(i,j) = |x_i - x_j| + |y_i - y_j|. Assume 1 <= side <= 10^9, n <= 15000, 4 <= k <= min(25, n), n <= 4*side, 0 <= x_i <= side, 0 <= y_i <= side, each (x_i, y_i) lies on the boundary of the square (x_i = 0 or x_i = side or y_i = 0 or y_i = side), and (x_i, y_i) != (x_j, y_j) for every i != j. Let k2 be an integer with k <= k2 <= min(25, n). -/
theorem spec_9 (side : I64) (points : Slice (alloc.vec.Vec I64)) (k k2 : I64) (r r2 : I64)
    (h : ValidInput side points k)
    (hkk : k.val ≤ k2.val ∧ k2.val ≤ min (25 : Int) (numPoints points : Int))
    (hr : Aegis.MaxDistance.max_distance side points k = ok r)
    (hr2 : Aegis.MaxDistance.max_distance side points k2 = ok r2) :
    r2.val ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (side : I64) (points : Slice (alloc.vec.Vec I64)) (k k2 : I64) (r r2 : I64)
    (h : ValidInput side points k)
    (hkk : k.val ≤ k2.val ∧ k2.val ≤ min (25 : Int) (numPoints points : Int))
    (hr : Aegis.MaxDistance.max_distance side points k = ok r)
    (hr2 : Aegis.MaxDistance.max_distance side points k2 = ok r2), r2.val ≤ r.val) := by
  sorry

/-- Whenever the function returns r for (side, points, k) and returns r_q for (side, q, k), we have r = r_q.
  Preconditions: Let n = len(points). For every i with 0 <= i < n, len(points[i]) = 2; write x_i = points[i][0], y_i = points[i][1]. Assume 1 <= side <= 10^9, n <= 15000, 4 <= k <= min(25, n), n <= 4*side, 0 <= x_i <= side, 0 <= y_i <= side, each (x_i, y_i) lies on the boundary of the square (x_i = 0 or x_i = side or y_i = 0 or y_i = side), and (x_i, y_i) != (x_j, y_j) for every i != j. Let q be any list of length n that is a permutation of the entries of points. -/
theorem spec_10 (side : I64) (points q : Slice (alloc.vec.Vec I64)) (k : I64) (r rq : I64)
    (h : ValidInput side points k)
    (hperm : q.val.Perm points.val)
    (hr : Aegis.MaxDistance.max_distance side points k = ok r)
    (hrq : Aegis.MaxDistance.max_distance side q k = ok rq) :
    r.val = rq.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (side : I64) (points q : Slice (alloc.vec.Vec I64)) (k : I64) (r rq : I64)
    (h : ValidInput side points k)
    (hperm : q.val.Perm points.val)
    (hr : Aegis.MaxDistance.max_distance side points k = ok r)
    (hrq : Aegis.MaxDistance.max_distance side q k = ok rq), r.val = rq.val) := by
  sorry

/-- Whenever the function returns r for (side, points, k) and returns r_q for (side, q, k), we have r_q >= r.
  Preconditions: Let n = len(points). For every i with 0 <= i < n, len(points[i]) = 2; write x_i = points[i][0], y_i = points[i][1], and D(i,j) = |x_i - x_j| + |y_i - y_j|. Assume 1 <= side <= 10^9, n <= 15000, 4 <= k <= min(25, n), n <= 4*side, 0 <= x_i <= side, 0 <= y_i <= side, each (x_i, y_i) lies on the boundary of the square (x_i = 0 or x_i = side or y_i = 0 or y_i = side), and (x_i, y_i) != (x_j, y_j) for every i != j. Let q be any list of points on the same square satisfying the same side and k constraints, with len(q) <= 15000, len(q) <= 4*side, 4 <= k <= min(25, len(q)), all entries of q distinct, and such that every coordinate pair occurring in points also occurs in q. -/
theorem spec_11 (side : I64) (points q : Slice (alloc.vec.Vec I64)) (k : I64) (r rq : I64)
    (h : ValidInput side points k)
    (hq : ValidInput side q k)
    (hcov : pointSet points ⊆ pointSet q)
    (hr : Aegis.MaxDistance.max_distance side points k = ok r)
    (hrq : Aegis.MaxDistance.max_distance side q k = ok rq) :
    r.val ≤ rq.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (side : I64) (points q : Slice (alloc.vec.Vec I64)) (k : I64) (r rq : I64)
    (h : ValidInput side points k)
    (hq : ValidInput side q k)
    (hcov : pointSet points ⊆ pointSet q)
    (hr : Aegis.MaxDistance.max_distance side points k = ok r)
    (hrq : Aegis.MaxDistance.max_distance side q k = ok rq), r.val ≤ rq.val) := by
  sorry

/-- Whenever the function returns a result r, there exist distinct indices i,j with 0 <= i < j < n such that r = D(i,j).
  Preconditions: Let n = len(points). For every i with 0 <= i < n, len(points[i]) = 2; write x_i = points[i][0], y_i = points[i][1], and D(i,j) = |x_i - x_j| + |y_i - y_j|. Assume 1 <= side <= 10^9, n <= 15000, 4 <= k <= min(25, n), n <= 4*side, 0 <= x_i <= side, 0 <= y_i <= side, each (x_i, y_i) lies on the boundary of the square (x_i = 0 or x_i = side or y_i = 0 or y_i = side), and (x_i, y_i) != (x_j, y_j) for every i != j. -/
theorem spec_12 (side : I64) (points : Slice (alloc.vec.Vec I64)) (k : I64) (r : I64)
    (h : ValidInput side points k)
    (hr : Aegis.MaxDistance.max_distance side points k = ok r) :
    ∃ i j : Nat, i < j ∧ j < numPoints points ∧ r.val = manhattan points i j := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (side : I64) (points : Slice (alloc.vec.Vec I64)) (k : I64) (r : I64)
    (h : ValidInput side points k)
    (hr : Aegis.MaxDistance.max_distance side points k = ok r), ∃ i j : Nat, i < j ∧ j < numPoints points ∧ r.val = manhattan points i j) := by
  sorry

end AegisSpec.MaxDistance
