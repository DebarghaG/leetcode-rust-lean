import Aegis.KClosest.Code.Funs

/-!
# Specifications of `Aegis.KClosest.k_closest`

LeetCode problem `k-closest-points-to-origin`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.KClosest

def coord (p : alloc.vec.Vec I64) (j : Nat) : Int := (p.val[j]!).val

def dist2 (p : alloc.vec.Vec I64) : Int :=
  coord p 0 * coord p 0 + coord p 1 * coord p 1

def occ (p : alloc.vec.Vec I64) (l : List (alloc.vec.Vec I64)) : Nat :=
  l.countP (fun q => coord q 0 == coord p 0 && coord q 1 == coord p 1)

def sel (points : Slice (alloc.vec.Vec I64)) (S : List Nat) : List (alloc.vec.Vec I64) :=
  S.map (fun i => points.val[i]!)

def IsKClosestSel (points : Slice (alloc.vec.Vec I64)) (kn : Nat)
    (M : List (alloc.vec.Vec I64)) : Prop :=
  ∃ S : List Nat,
    S.Nodup ∧ (∀ i ∈ S, i < points.val.length) ∧ S.length = kn ∧
      M.Perm (sel points S) ∧
        ∀ i ∈ S, ∀ j, j < points.val.length → j ∉ S →
          dist2 (points.val[i]!) ≤ dist2 (points.val[j]!)

/-- Whenever k_closest(points, k) returns a result r, there exists a set S of indices with 0 <= i < len(points) and |S| = k such that r is a permutation of the list [points[i] | i in S] (same multiset of two-coordinate vectors, in any order), and for every i in S and every j with 0 <= j < len(points) and j not in S, dist2(points[i]) <= dist2(points[j]), where dist2(p) = p[0]*p[0] + p[1]*p[1].
  Preconditions: 1 <= k <= len(points) <= 10000; for every i with 0 <= i < len(points), len(points[i]) = 2 and -10000 <= points[i][0] <= 10000 and -10000 <= points[i][1] <= 10000. -/
theorem spec_1 (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (h : Aegis.KClosest.k_closest points k = ok r) :
    ∃ S : List Nat,
      S.Nodup ∧ (S.length : Int) = k.val ∧ (∀ i ∈ S, i < points.val.length) ∧
        r.val.Perm (sel points S) ∧
          ∀ i ∈ S, ∀ j, j < points.val.length → j ∉ S →
            dist2 (points.val[i]!) ≤ dist2 (points.val[j]!) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (h : Aegis.KClosest.k_closest points k = ok r), ∃ S : List Nat,
      S.Nodup ∧ (S.length : Int) = k.val ∧ (∀ i ∈ S, i < points.val.length) ∧
        r.val.Perm (sel points S) ∧
          ∀ i ∈ S, ∀ j, j < points.val.length → j ∉ S →
            dist2 (points.val[i]!) ≤ dist2 (points.val[j]!)) := by
  sorry

/-- For every points and k satisfying the preconditions, the evaluation of k_closest(points, k) returns a result r (there is no overflow, out-of-bounds access, or panic).
  Preconditions: 1 <= k <= len(points) <= 10000; for every i with 0 <= i < len(points), len(points[i]) = 2 and -10000 <= points[i][0] <= 10000 and -10000 <= points[i][1] <= 10000. -/
theorem spec_2 (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64), Aegis.KClosest.k_closest points k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64), Aegis.KClosest.k_closest points k = ok r) := by
  sorry

/-- Whenever k_closest(points, k) returns r, len(r) = k.
  Preconditions: 1 <= k <= len(points) <= 10000; for every i with 0 <= i < len(points), len(points[i]) = 2 and -10000 <= points[i][0] <= 10000 and -10000 <= points[i][1] <= 10000. -/
theorem spec_3 (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (h : Aegis.KClosest.k_closest points k = ok r) :
    (r.val.length : Int) = k.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (h : Aegis.KClosest.k_closest points k = ok r), (r.val.length : Int) = k.val) := by
  sorry

/-- Whenever k_closest(points, k) returns r, for every j with 0 <= j < len(r), len(r[j]) = 2.
  Preconditions: 1 <= k <= len(points) <= 10000; for every i with 0 <= i < len(points), len(points[i]) = 2 and -10000 <= points[i][0] <= 10000 and -10000 <= points[i][1] <= 10000. -/
theorem spec_4 (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (h : Aegis.KClosest.k_closest points k = ok r) :
    ∀ (j : Nat), j < r.val.length → (r.val[j]!).val.length = 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (h : Aegis.KClosest.k_closest points k = ok r), ∀ (j : Nat), j < r.val.length → (r.val[j]!).val.length = 2) := by
  sorry

/-- Whenever k_closest(points, k) returns r, for every j with 0 <= j < len(r), there exists i with 0 <= i < len(points) such that r[j][0] = points[i][0] and r[j][1] = points[i][1].
  Preconditions: 1 <= k <= len(points) <= 10000; for every i with 0 <= i < len(points), len(points[i]) = 2 and -10000 <= points[i][0] <= 10000 and -10000 <= points[i][1] <= 10000. -/
theorem spec_5 (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (h : Aegis.KClosest.k_closest points k = ok r) :
    ∀ (j : Nat), j < r.val.length → ∃ i : Nat, i < points.val.length ∧
      coord (r.val[j]!) 0 = coord (points.val[i]!) 0 ∧
        coord (r.val[j]!) 1 = coord (points.val[i]!) 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (h : Aegis.KClosest.k_closest points k = ok r), ∀ (j : Nat), j < r.val.length → ∃ i : Nat, i < points.val.length ∧
      coord (r.val[j]!) 0 = coord (points.val[i]!) 0 ∧
        coord (r.val[j]!) 1 = coord (points.val[i]!) 1) := by
  sorry

/-- Whenever k_closest(points, k) returns r, for every two-coordinate vector p, the number of indices j with 0 <= j < len(r) and r[j][0] = p[0] and r[j][1] = p[1] is at most the number of indices i with 0 <= i < len(points) and points[i][0] = p[0] and points[i][1] = p[1].
  Preconditions: 1 <= k <= len(points) <= 10000; for every i with 0 <= i < len(points), len(points[i]) = 2 and -10000 <= points[i][0] <= 10000 and -10000 <= points[i][1] <= 10000. -/
theorem spec_6 (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (h : Aegis.KClosest.k_closest points k = ok r) :
    ∀ p : alloc.vec.Vec I64, occ p r.val ≤ occ p points.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (h : Aegis.KClosest.k_closest points k = ok r), ∀ p : alloc.vec.Vec I64, occ p r.val ≤ occ p points.val) := by
  sorry

/-- Whenever k_closest(points, k) returns r, for every j with 0 <= j < len(r), -10000 <= r[j][0] <= 10000 and -10000 <= r[j][1] <= 10000.
  Preconditions: 1 <= k <= len(points) <= 10000; for every i with 0 <= i < len(points), len(points[i]) = 2 and -10000 <= points[i][0] <= 10000 and -10000 <= points[i][1] <= 10000. -/
theorem spec_7 (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (h : Aegis.KClosest.k_closest points k = ok r) :
    ∀ (j : Nat), j < r.val.length →
      -10000 ≤ coord (r.val[j]!) 0 ∧ coord (r.val[j]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (r.val[j]!) 1 ∧ coord (r.val[j]!) 1 ≤ 10000 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (h : Aegis.KClosest.k_closest points k = ok r), ∀ (j : Nat), j < r.val.length →
      -10000 ≤ coord (r.val[j]!) 0 ∧ coord (r.val[j]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (r.val[j]!) 1 ∧ coord (r.val[j]!) 1 ≤ 10000) := by
  sorry

/-- Whenever k_closest(points, k) returns r, let s be a nondecreasing list of length len(points) whose multiset of entries is {dist2(points[i]) | 0 <= i < len(points)}, where dist2(p) = p[0]*p[0] + p[1]*p[1]. Then the multiset {dist2(r[j]) | 0 <= j < len(r)} equals the multiset {s[0], s[1], ..., s[k-1]}.
  Preconditions: 1 <= k <= len(points) <= 10000; for every i with 0 <= i < len(points), len(points[i]) = 2 and -10000 <= points[i][0] <= 10000 and -10000 <= points[i][1] <= 10000. -/
theorem spec_8 (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (h : Aegis.KClosest.k_closest points k = ok r)
    (s : List Int) (hs_len : s.length = points.val.length)
    (hs_sorted : s.Pairwise (· ≤ ·))
    (hs_mult : s.Perm (points.val.map dist2)) :
    (r.val.map dist2).Perm (s.take k.val.toNat) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (h : Aegis.KClosest.k_closest points k = ok r)
    (s : List Int) (hs_len : s.length = points.val.length)
    (hs_sorted : s.Pairwise (· ≤ ·))
    (hs_mult : s.Perm (points.val.map dist2)), (r.val.map dist2).Perm (s.take k.val.toNat)) := by
  sorry

/-- Whenever k_closest(points, k) returns r, there exists j with 0 <= j < len(r) such that r[j][0] = 0 and r[j][1] = 0.
  Preconditions: 1 <= k <= len(points) <= 10000; for every i with 0 <= i < len(points), len(points[i]) = 2 and -10000 <= points[i][0] <= 10000 and -10000 <= points[i][1] <= 10000; there exists i with 0 <= i < len(points) such that points[i][0] = 0 and points[i][1] = 0. -/
theorem spec_9 (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000)
    (horigin : ∃ i : Nat, i < points.val.length ∧ coord (points.val[i]!) 0 = 0 ∧
      coord (points.val[i]!) 1 = 0)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (h : Aegis.KClosest.k_closest points k = ok r) :
    ∃ j : Nat, j < r.val.length ∧ coord (r.val[j]!) 0 = 0 ∧ coord (r.val[j]!) 1 = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000)
    (horigin : ∃ i : Nat, i < points.val.length ∧ coord (points.val[i]!) 0 = 0 ∧
      coord (points.val[i]!) 1 = 0)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (h : Aegis.KClosest.k_closest points k = ok r), ∃ j : Nat, j < r.val.length ∧ coord (r.val[j]!) 0 = 0 ∧ coord (r.val[j]!) 1 = 0) := by
  sorry

/-- Whenever k_closest(points, k) returns r and k_closest(points', k) returns r', r is a permutation of r' (same multiset of two-coordinate vectors).
  Preconditions: 1 <= k <= len(points) <= 10000; for every i with 0 <= i < len(points), len(points[i]) = 2 and -10000 <= points[i][0] <= 10000 and -10000 <= points[i][1] <= 10000; 1 <= k <= len(points') <= 10000; for every i with 0 <= i < len(points'), len(points'[i]) = 2 and -10000 <= points'[i][0] <= 10000 and -10000 <= points'[i][1] <= 10000; points' is a permutation of points (same multiset of two-coordinate vectors); the k closest points for points are unique up to order, meaning there is exactly one multiset of k point vectors obtainable by selecting k occurrences from points such that every selected occurrence has dist2 no greater than every omitted occurrence, where dist2(p)=p[0]*p[0]+p[1]*p[1]. -/
theorem spec_10 (points points' : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000)
    (hk2' : k.val ≤ (points'.val.length : Int))
    (hlen' : points'.val.length ≤ 10000)
    (hshape' : ∀ (i : Nat), i < points'.val.length → (points'.val[i]!).val.length = 2)
    (hbox' : ∀ (i : Nat), i < points'.val.length →
      -10000 ≤ coord (points'.val[i]!) 0 ∧ coord (points'.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points'.val[i]!) 1 ∧ coord (points'.val[i]!) 1 ≤ 10000)
    (hperm : points'.val.Perm points.val)
    (huniq : ∃ M : List (alloc.vec.Vec I64),
      IsKClosestSel points k.val.toNat M ∧
        ∀ M' : List (alloc.vec.Vec I64),
          IsKClosestSel points k.val.toNat M' → M'.Perm M)
    (r r' : alloc.vec.Vec (alloc.vec.Vec I64))
    (h : Aegis.KClosest.k_closest points k = ok r)
    (h' : Aegis.KClosest.k_closest points' k = ok r') :
    r.val.Perm r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (points points' : Slice (alloc.vec.Vec I64)) (k : I64)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (points.val.length : Int))
    (hlen : points.val.length ≤ 10000)
    (hshape : ∀ (i : Nat), i < points.val.length → (points.val[i]!).val.length = 2)
    (hbox : ∀ (i : Nat), i < points.val.length →
      -10000 ≤ coord (points.val[i]!) 0 ∧ coord (points.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points.val[i]!) 1 ∧ coord (points.val[i]!) 1 ≤ 10000)
    (hk2' : k.val ≤ (points'.val.length : Int))
    (hlen' : points'.val.length ≤ 10000)
    (hshape' : ∀ (i : Nat), i < points'.val.length → (points'.val[i]!).val.length = 2)
    (hbox' : ∀ (i : Nat), i < points'.val.length →
      -10000 ≤ coord (points'.val[i]!) 0 ∧ coord (points'.val[i]!) 0 ≤ 10000 ∧
        -10000 ≤ coord (points'.val[i]!) 1 ∧ coord (points'.val[i]!) 1 ≤ 10000)
    (hperm : points'.val.Perm points.val)
    (huniq : ∃ M : List (alloc.vec.Vec I64),
      IsKClosestSel points k.val.toNat M ∧
        ∀ M' : List (alloc.vec.Vec I64),
          IsKClosestSel points k.val.toNat M' → M'.Perm M)
    (r r' : alloc.vec.Vec (alloc.vec.Vec I64))
    (h : Aegis.KClosest.k_closest points k = ok r)
    (h' : Aegis.KClosest.k_closest points' k = ok r'), r.val.Perm r'.val) := by
  sorry

end AegisSpec.KClosest
