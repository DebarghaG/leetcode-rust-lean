import Aegis.FindMinArrowShots.Code.Funs

/-!
# Specifications of `Aegis.FindMinArrowShots.find_min_arrow_shots`

LeetCode problem `minimum-number-of-arrows-to-burst-balloons`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindMinArrowShots

open Aegis.FindMinArrowShots (find_min_arrow_shots)

def rowOf (points : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
  ((points.val[i]?).map fun v => v.val.map fun x => x.val).getD []

def count (points : Slice (alloc.vec.Vec Std.I64)) : Nat := points.val.length

def lOf (points : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int := (rowOf points i).getD 0 0

def rOf (points : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int := (rowOf points i).getD 1 0

def InI32Range (x : Int) : Prop := -(2 : Int) ^ 31 ≤ x ∧ x ≤ (2 : Int) ^ 31 - 1

def ValidInput (points : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  1 ≤ count points ∧ count points ≤ 100000 ∧
    ∀ i, i < count points →
      (rowOf points i).length = 2 ∧ lOf points i < rOf points i ∧
        InI32Range (lOf points i) ∧ InI32Range (rOf points i)

def Covers (points : Slice (alloc.vec.Vec Std.I64)) (S : Finset Int) : Prop :=
  ∀ i, i < count points → ∃ x ∈ S, lOf points i ≤ x ∧ x ≤ rOf points i

def PairwiseDisjoint (points : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∀ i j, i < j → j < count points →
    rOf points i < lOf points j ∨ rOf points j < lOf points i

def PairwiseIntersecting (points : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∀ i j, i < j → j < count points →
    ∃ x : Int, lOf points i ≤ x ∧ x ≤ rOf points i ∧ lOf points j ≤ x ∧ x ≤ rOf points j

def DisjointOn (points : Slice (alloc.vec.Vec Std.I64)) (T : Finset Nat) : Prop :=
  ∀ i ∈ T, ∀ j ∈ T, i ≠ j → rOf points i < lOf points j ∨ rOf points j < lOf points i

def maxL (points : Slice (alloc.vec.Vec Std.I64)) : Int :=
  ((List.range (count points)).map (lOf points)).max?.getD 0

def minR (points : Slice (alloc.vec.Vec Std.I64)) : Int :=
  ((List.range (count points)).map (rOf points)).min?.getD 0

def distinctRightEndpoints (points : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  ((Finset.range (count points)).image (rOf points)).card

def PermByIndex {α : Type} (a b : List α) : Prop :=
  ∃ h : a.length = b.length, ∃ π : Equiv.Perm (Fin a.length),
    ∀ j : Fin a.length, b.get (Fin.cast h j) = a.get (π j)

/-- Whenever find_min_arrow_shots(points) returns a result r, r is the smallest non-negative integer k for which there exists a finite set S of k integers such that for every i with 0 <= i < n, there is some x in S with l_i <= x <= r_i. Equivalently, r = min { |S| : S is a finite set of integers and for all i, exists x in S with l_i <= x <= r_i }.
  Preconditions: Let n = len(points). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2; write l_i = points[i][0] and r_i = points[i][1]. Then l_i < r_i and -2^31 <= l_i, r_i <= 2^31 - 1. -/
theorem spec_1 (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points) :
    ∀ r : Std.I64, find_min_arrow_shots points = ok r →
      ∃ k : Nat, r.val = (k : Int) ∧
        (∃ S : Finset Int, S.card = k ∧ Covers points S) ∧
        ∀ S : Finset Int, Covers points S → k ≤ S.card := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points), ∀ r : Std.I64, find_min_arrow_shots points = ok r →
      ∃ k : Nat, r.val = (k : Int) ∧
        (∃ S : Finset Int, S.card = k ∧ Covers points S) ∧
        ∀ S : Finset Int, Covers points S → k ≤ S.card) := by
  sorry

/-- For every points satisfying the preconditions, find_min_arrow_shots(points) returns a result r; it does not fail due to integer overflow, out-of-bounds access, or panic.
  Preconditions: Let n = len(points). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2; write l_i = points[i][0] and r_i = points[i][1]. Then l_i < r_i and -2^31 <= l_i, r_i <= 2^31 - 1. -/
theorem spec_2 (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points) :
    ∃ r : Std.I64, find_min_arrow_shots points = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points), ∃ r : Std.I64, find_min_arrow_shots points = ok r) := by
  sorry

/-- Whenever find_min_arrow_shots(points) returns a result r, r >= 1.
  Preconditions: Let n = len(points). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2; write l_i = points[i][0] and r_i = points[i][1]. Then l_i < r_i and -2^31 <= l_i, r_i <= 2^31 - 1. -/
theorem spec_3 (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points) :
    ∀ r : Std.I64, find_min_arrow_shots points = ok r → 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points), ∀ r : Std.I64, find_min_arrow_shots points = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever find_min_arrow_shots(points) returns a result r, r <= n = len(points).
  Preconditions: Let n = len(points). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2; write l_i = points[i][0] and r_i = points[i][1]. Then l_i < r_i and -2^31 <= l_i, r_i <= 2^31 - 1. -/
theorem spec_4 (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points) :
    ∀ r : Std.I64, find_min_arrow_shots points = ok r → r.val ≤ (count points : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points), ∀ r : Std.I64, find_min_arrow_shots points = ok r → r.val ≤ (count points : Int)) := by
  sorry

/-- Whenever find_min_arrow_shots(points) returns a result r, r = 1 if and only if max_{0 <= i < n} l_i <= min_{0 <= i < n} r_i.
  Preconditions: Let n = len(points). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2; write l_i = points[i][0] and r_i = points[i][1]. Then l_i < r_i and -2^31 <= l_i, r_i <= 2^31 - 1. -/
theorem spec_5 (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points) :
    ∀ r : Std.I64, find_min_arrow_shots points = ok r →
      (r.val = 1 ↔ maxL points ≤ minR points) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points), ∀ r : Std.I64, find_min_arrow_shots points = ok r →
      (r.val = 1 ↔ maxL points ≤ minR points)) := by
  sorry

/-- Whenever find_min_arrow_shots(points) returns a result r, r = n if and only if the intervals are pairwise disjoint, i.e., for every i and j with 0 <= i < j < n, either r_i < l_j or r_j < l_i.
  Preconditions: Let n = len(points). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2; write l_i = points[i][0] and r_i = points[i][1]. Then l_i < r_i and -2^31 <= l_i, r_i <= 2^31 - 1. -/
theorem spec_6 (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points) :
    ∀ r : Std.I64, find_min_arrow_shots points = ok r →
      (r.val = (count points : Int) ↔ PairwiseDisjoint points) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points), ∀ r : Std.I64, find_min_arrow_shots points = ok r →
      (r.val = (count points : Int) ↔ PairwiseDisjoint points)) := by
  sorry

/-- Whenever find_min_arrow_shots(points) returns a result r, r is the maximum cardinality of a subset T of {0, ..., n-1} such that the intervals indexed by T are pairwise disjoint: for all distinct i, j in T, either r_i < l_j or r_j < l_i.
  Preconditions: Let n = len(points). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2; write l_i = points[i][0] and r_i = points[i][1]. Then l_i < r_i and -2^31 <= l_i, r_i <= 2^31 - 1. -/
theorem spec_7 (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points) :
    ∀ r : Std.I64, find_min_arrow_shots points = ok r →
      ∃ T : Finset Nat, T ⊆ Finset.range (count points) ∧ DisjointOn points T ∧
        (T.card : Int) = r.val ∧
        ∀ T' : Finset Nat, T' ⊆ Finset.range (count points) → DisjointOn points T' →
          T'.card ≤ T.card := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points), ∀ r : Std.I64, find_min_arrow_shots points = ok r →
      ∃ T : Finset Nat, T ⊆ Finset.range (count points) ∧ DisjointOn points T ∧
        (T.card : Int) = r.val ∧
        ∀ T' : Finset Nat, T' ⊆ Finset.range (count points) → DisjointOn points T' →
          T'.card ≤ T.card) := by
  sorry

/-- If points' is a permutation of points (there is a bijection π from {0,...,n-1} to itself such that points'[j] = points[π(j)] for all j), then whenever find_min_arrow_shots(points) returns r and find_min_arrow_shots(points') returns r', we have r = r'.
  Preconditions: points and points' are two inputs satisfying the problem constraints, with n = len(points) = len(points'). For every i, write l_i = points[i][0], r_i = points[i][1], l'_i = points'[i][0], r'_i = points'[i][1]. -/
theorem spec_8 (points points' : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput points) (h' : ValidInput points')
    (hlen : count points = count points')
    (hperm : PermByIndex points.val points'.val) :
    ∀ r r' : Std.I64, find_min_arrow_shots points = ok r →
      find_min_arrow_shots points' = ok r' → r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (points points' : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput points) (h' : ValidInput points')
    (hlen : count points = count points')
    (hperm : PermByIndex points.val points'.val), ∀ r r' : Std.I64, find_min_arrow_shots points = ok r →
      find_min_arrow_shots points' = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever find_min_arrow_shots(points) returns r and find_min_arrow_shots(points') returns r', we have r = r'.
  Preconditions: Let n = len(points) = len(points'). Assume points and points' satisfy the problem constraints: for every i with 0 <= i < n, len(points[i]) = len(points'[i]) = 2; write l_i = points[i][0], r_i = points[i][1], l'_i = points'[i][0], r'_i = points'[i][1]; then l_i < r_i, l'_i < r'_i, and all endpoints are in [-2^31, 2^31 - 1]. There is an integer c such that for every i with 0 <= i < n, l'_i = l_i + c and r'_i = r_i + c. -/
theorem spec_9 (points points' : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput points) (h' : ValidInput points')
    (hlen : count points = count points')
    (hshift : ∃ c : Int, ∀ i, i < count points →
      lOf points' i = lOf points i + c ∧ rOf points' i = rOf points i + c) :
    ∀ r r' : Std.I64, find_min_arrow_shots points = ok r →
      find_min_arrow_shots points' = ok r' → r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (points points' : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput points) (h' : ValidInput points')
    (hlen : count points = count points')
    (hshift : ∃ c : Int, ∀ i, i < count points →
      lOf points' i = lOf points i + c ∧ rOf points' i = rOf points i + c), ∀ r r' : Std.I64, find_min_arrow_shots points = ok r →
      find_min_arrow_shots points' = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever find_min_arrow_shots(points) returns r and find_min_arrow_shots(points') returns r', we have r <= r' <= r + 1.
  Preconditions: points and points' satisfy the problem constraints. points' is obtained by appending one extra balloon to points: len(points') = n + 1, and for every i with 0 <= i < n, points'[i] = points[i]. The extra balloon points'[n] satisfies len(points'[n]) = 2 and l'_n < r'_n within the allowed range. -/
theorem spec_10 (points points' : Slice (alloc.vec.Vec Std.I64)) (extra : alloc.vec.Vec Std.I64)
    (h : ValidInput points) (h' : ValidInput points')
    (happend : points'.val = points.val ++ [extra]) :
    ∀ r r' : Std.I64, find_min_arrow_shots points = ok r →
      find_min_arrow_shots points' = ok r' → r.val ≤ r'.val ∧ r'.val ≤ r.val + 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (points points' : Slice (alloc.vec.Vec Std.I64)) (extra : alloc.vec.Vec Std.I64)
    (h : ValidInput points) (h' : ValidInput points')
    (happend : points'.val = points.val ++ [extra]), ∀ r r' : Std.I64, find_min_arrow_shots points = ok r →
      find_min_arrow_shots points' = ok r' → r.val ≤ r'.val ∧ r'.val ≤ r.val + 1) := by
  sorry

/-- Whenever find_min_arrow_shots(points) returns a result r, there exists a set S of exactly r integers such that: (a) every x in S is the right endpoint r_i of some balloon i with 0 <= i < n; and (b) for every i with 0 <= i < n, there is some x in S with l_i <= x <= r_i.
  Preconditions: Let n = len(points). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2; write l_i = points[i][0] and r_i = points[i][1]. Then l_i < r_i and -2^31 <= l_i, r_i <= 2^31 - 1. -/
theorem spec_11 (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points) :
    ∀ r : Std.I64, find_min_arrow_shots points = ok r →
      ∃ S : Finset Int, (S.card : Int) = r.val ∧
        (∀ x ∈ S, ∃ i, i < count points ∧ rOf points i = x) ∧ Covers points S := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points), ∀ r : Std.I64, find_min_arrow_shots points = ok r →
      ∃ S : Finset Int, (S.card : Int) = r.val ∧
        (∀ x ∈ S, ∃ i, i < count points ∧ rOf points i = x) ∧ Covers points S) := by
  sorry

/-- Whenever find_min_arrow_shots(points) returns r and find_min_arrow_shots(points') returns r', we have r' <= r.
  Preconditions: points and points' satisfy the problem constraints with the same length n. For every i, write l_i = points[i][0], r_i = points[i][1], l'_i = points'[i][0], r'_i = points'[i][1]. Assume l'_i <= l_i and r_i <= r'_i for all i (so each balloon of points is contained in the corresponding balloon of points'). -/
theorem spec_12 (points points' : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput points) (h' : ValidInput points')
    (hlen : count points = count points')
    (hcontained : ∀ i, i < count points →
      lOf points' i ≤ lOf points i ∧ rOf points i ≤ rOf points' i) :
    ∀ r r' : Std.I64, find_min_arrow_shots points = ok r →
      find_min_arrow_shots points' = ok r' → r'.val ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (points points' : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput points) (h' : ValidInput points')
    (hlen : count points = count points')
    (hcontained : ∀ i, i < count points →
      lOf points' i ≤ lOf points i ∧ rOf points i ≤ rOf points' i), ∀ r r' : Std.I64, find_min_arrow_shots points = ok r →
      find_min_arrow_shots points' = ok r' → r'.val ≤ r.val) := by
  sorry

/-- If the balloons are pairwise intersecting, i.e., for every i and j with 0 <= i < j < n there exists a point x with l_i <= x <= r_i and l_j <= x <= r_j, then whenever find_min_arrow_shots(points) returns r, we have r = 1.
  Preconditions: Let n = len(points). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2; write l_i = points[i][0] and r_i = points[i][1]. Then l_i < r_i and -2^31 <= l_i, r_i <= 2^31 - 1. -/
theorem spec_13 (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points)
    (hinter : PairwiseIntersecting points) :
    ∀ r : Std.I64, find_min_arrow_shots points = ok r → r.val = 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points)
    (hinter : PairwiseIntersecting points), ∀ r : Std.I64, find_min_arrow_shots points = ok r → r.val = 1) := by
  sorry

/-- Whenever find_min_arrow_shots(points) returns a result r, r <= |{ r_i : 0 <= i < n }|, the number of distinct right endpoints among all balloons.
  Preconditions: Let n = len(points). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2; write l_i = points[i][0] and r_i = points[i][1]. Then l_i < r_i and -2^31 <= l_i, r_i <= 2^31 - 1. -/
theorem spec_14 (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points) :
    ∀ r : Std.I64, find_min_arrow_shots points = ok r →
      r.val ≤ (distinctRightEndpoints points : Int) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points), ∀ r : Std.I64, find_min_arrow_shots points = ok r →
      r.val ≤ (distinctRightEndpoints points : Int)) := by
  sorry

/-- Whenever find_min_arrow_shots(points) returns a result r, there exists a set S of exactly r integers such that: (a) every x in S is the left endpoint l_i of some balloon i with 0 <= i < n; and (b) for every i with 0 <= i < n, there is some x in S with l_i <= x <= r_i.
  Preconditions: Let n = len(points). Assume 1 <= n <= 100000. For every i with 0 <= i < n, len(points[i]) = 2; write l_i = points[i][0] and r_i = points[i][1]. Then l_i < r_i and -2^31 <= l_i, r_i <= 2^31 - 1. -/
theorem spec_15 (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points) :
    ∀ r : Std.I64, find_min_arrow_shots points = ok r →
      ∃ S : Finset Int, (S.card : Int) = r.val ∧
        (∀ x ∈ S, ∃ i, i < count points ∧ lOf points i = x) ∧ Covers points S := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput points), ∀ r : Std.I64, find_min_arrow_shots points = ok r →
      ∃ S : Finset Int, (S.card : Int) = r.val ∧
        (∀ x ∈ S, ∃ i, i < count points ∧ lOf points i = x) ∧ Covers points S) := by
  sorry

/-- Whenever find_min_arrow_shots(points) returns r and find_min_arrow_shots(points') returns r', we have r' = r + 1.
  Preconditions: Let n = len(points). points and points' satisfy the problem constraints. points' is obtained by appending one extra balloon to points: len(points') = n + 1 and points'[i] = points[i] for every i with 0 <= i < n. Let l'_n = points'[n][0] and r'_n = points'[n][1]. Assume the extra balloon is disjoint from every original balloon: for every i with 0 <= i < n, either r'_n < l_i or r_i < l'_n. -/
theorem spec_16 (points points' : Slice (alloc.vec.Vec Std.I64)) (extra : alloc.vec.Vec Std.I64)
    (h : ValidInput points) (h' : ValidInput points')
    (happend : points'.val = points.val ++ [extra])
    (hdisjoint : ∀ i, i < count points →
      rOf points' (count points) < lOf points i ∨
        rOf points i < lOf points' (count points)) :
    ∀ r r' : Std.I64, find_min_arrow_shots points = ok r →
      find_min_arrow_shots points' = ok r' → r'.val = r.val + 1 := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (points points' : Slice (alloc.vec.Vec Std.I64)) (extra : alloc.vec.Vec Std.I64)
    (h : ValidInput points) (h' : ValidInput points')
    (happend : points'.val = points.val ++ [extra])
    (hdisjoint : ∀ i, i < count points →
      rOf points' (count points) < lOf points i ∨
        rOf points i < lOf points' (count points)), ∀ r r' : Std.I64, find_min_arrow_shots points = ok r →
      find_min_arrow_shots points' = ok r' → r'.val = r.val + 1) := by
  sorry

/-- Whenever find_min_arrow_shots(points) returns r and find_min_arrow_shots(points') returns r', we have r' = r.
  Preconditions: Let n = len(points). points and points' satisfy the problem constraints. points' is obtained by appending one extra balloon to points: len(points') = n + 1 and points'[i] = points[i] for every i with 0 <= i < n. Let l'_n = points'[n][0] and r'_n = points'[n][1]. Assume the extra balloon contains some original balloon j with 0 <= j < n: l'_n <= l_j and r_j <= r'_n. -/
theorem spec_17 (points points' : Slice (alloc.vec.Vec Std.I64)) (extra : alloc.vec.Vec Std.I64)
    (h : ValidInput points) (h' : ValidInput points')
    (happend : points'.val = points.val ++ [extra])
    (hcontains : ∃ j, j < count points ∧
      lOf points' (count points) ≤ lOf points j ∧
        rOf points j ≤ rOf points' (count points)) :
    ∀ r r' : Std.I64, find_min_arrow_shots points = ok r →
      find_min_arrow_shots points' = ok r' → r'.val = r.val := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (points points' : Slice (alloc.vec.Vec Std.I64)) (extra : alloc.vec.Vec Std.I64)
    (h : ValidInput points) (h' : ValidInput points')
    (happend : points'.val = points.val ++ [extra])
    (hcontains : ∃ j, j < count points ∧
      lOf points' (count points) ≤ lOf points j ∧
        rOf points j ≤ rOf points' (count points)), ∀ r r' : Std.I64, find_min_arrow_shots points = ok r →
      find_min_arrow_shots points' = ok r' → r'.val = r.val) := by
  sorry

end AegisSpec.FindMinArrowShots
