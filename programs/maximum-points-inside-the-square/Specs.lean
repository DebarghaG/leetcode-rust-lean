import Aegis.MaxPointsInsideSquare.Code.Funs

/-!
# Specifications of `Aegis.MaxPointsInsideSquare.max_points_inside_square`

LeetCode problem `maximum-points-inside-the-square`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aeneas.Std.alloc.vec

set_option maxHeartbeats 1000000

namespace AegisSpec.MaxPointsInsideSquare

def coord (p : Vec I64) (k : Nat) : Int :=
  match p.val[k]? with
  | some x => x.val
  | none => 0

def cheb (p : Vec I64) : Int :=
  max |coord p 0| |coord p 1|

def dists (points : Slice (Vec I64)) : List Int :=
  points.val.map cheb

def bytes (s : Slice U8) : List Nat :=
  s.val.map (fun b => b.val)

def dAt (points : Slice (Vec I64)) (i : Nat) : Int :=
  ((dists points)[i]?).getD 0

def byteAt (s : Slice U8) (i : Nat) : Nat :=
  ((bytes s)[i]?).getD 0

def classValues (points : Slice (Vec I64)) (s : Slice U8) (c : Nat) : List Int :=
  ((dists points).zip (bytes s)).filterMap
    (fun q => if q.2 = c then some q.1 else none)

def nthSmallest? (l : List Int) (k : Nat) : Option Int :=
  (l.mergeSort (fun a b => decide (a ≤ b)))[k]?

def secondSmallest? (l : List Int) : Option Int :=
  nthSmallest? l 1

def countBelow (points : Slice (Vec I64)) (L : Int) : Nat :=
  (dists points).countP (fun d => decide (d < L))

def countLe (points : Slice (Vec I64)) (R : Int) : Nat :=
  (dists points).countP (fun d => decide (d ≤ R))

def countEq (points : Slice (Vec I64)) (D : Int) : Nat :=
  (dists points).countP (fun d => decide (d = D))

def bytesLe (points : Slice (Vec I64)) (s : Slice U8) (R : Int) : List Nat :=
  ((dists points).zip (bytes s)).filterMap
    (fun q => if q.1 ≤ R then some q.2 else none)

def bytesEq (points : Slice (Vec I64)) (s : Slice U8) (D : Int) : List Nat :=
  ((dists points).zip (bytes s)).filterMap
    (fun q => if q.1 = D then some q.2 else none)

def PointOK (p : Vec I64) : Prop :=
  p.val.length = 2 ∧
    -1000000000 ≤ coord p 0 ∧ coord p 0 ≤ 1000000000 ∧
    -1000000000 ≤ coord p 1 ∧ coord p 1 ≤ 1000000000

def PointsPre (points : Slice (Vec I64)) : Prop :=
  1 ≤ points.val.length ∧
    points.val.length ≤ 100000 ∧
    (∀ (i : Nat) (hi : i < points.val.length), PointOK (points.val[i]'hi)) ∧
    (∀ (i j : Nat) (hi : i < points.val.length) (hj : j < points.val.length),
      coord (points.val[i]'hi) 0 = coord (points.val[j]'hj) 0 →
        coord (points.val[i]'hi) 1 = coord (points.val[j]'hj) 1 → i = j)

def BytesLower (s : Slice U8) : Prop :=
  ∀ (i : Nat) (hi : i < s.val.length),
    97 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 122

def Pre (points : Slice (Vec I64)) (s : Slice U8) : Prop :=
  points.val.length = s.val.length ∧ PointsPre points ∧ BytesLower s

/-- Whenever the function returns a result r, the following holds. Let n = len(points) and, for each 0 <= i < n, let d(i) = max(abs(points[i][0]), abs(points[i][1])). For each byte c, let R_c be the nondecreasing list of all d(i) with s[i] = c. If at least one byte c has len(R_c) >= 2, let L be the minimum over all such c of R_c[1], the second smallest element of R_c with multiplicity. Then r equals the number of indices i with 0 <= i < n and d(i) < L. If no byte c has len(R_c) >= 2, then r = n.
  Preconditions: len(points) = len(s), 1 <= len(points) <= 10^5, each points[i] has length 2, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9 for every 0 <= i < len(points), the coordinate pairs points[i] are pairwise distinct, and each s[i] is a lowercase English letter (ASCII byte). -/
theorem spec_1 (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s) :
    ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      (∃ L : Int,
          (∃ c : Nat,
              2 ≤ (classValues points s c).length ∧
                secondSmallest? (classValues points s c) = some L) ∧
            (∀ (c : Nat) (t : Int),
              2 ≤ (classValues points s c).length →
                secondSmallest? (classValues points s c) = some t → L ≤ t) ∧
            r.val = (countBelow points L : Int)) ∨
        (r.val = (points.val.length : Int) ∧
          ∀ c : Nat, (classValues points s c).length < 2) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s), ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      (∃ L : Int,
          (∃ c : Nat,
              2 ≤ (classValues points s c).length ∧
                secondSmallest? (classValues points s c) = some L) ∧
            (∀ (c : Nat) (t : Int),
              2 ≤ (classValues points s c).length →
                secondSmallest? (classValues points s c) = some t → L ≤ t) ∧
            r.val = (countBelow points L : Int)) ∨
        (r.val = (points.val.length : Int) ∧
          ∀ c : Nat, (classValues points s c).length < 2)) := by
  sorry

/-- The function returns a result (an Ok i64 value); it does not fail, overflow, panic, or access an out-of-bounds index on any input satisfying the preconditions.
  Preconditions: len(points) = len(s), 1 <= len(points) <= 10^5, each points[i] has length 2, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9 for every 0 <= i < len(points), the coordinate pairs points[i] are pairwise distinct, and each s[i] is a lowercase English letter (ASCII byte). -/
theorem spec_2 (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s) :
    ∃ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s), ∃ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r) := by
  sorry

/-- Whenever the function returns a result r, there exists a real number R >= 0 such that exactly r indices i with 0 <= i < len(points) satisfy max(abs(points[i][0]), abs(points[i][1])) <= R, and the bytes s[i] for those r indices are pairwise distinct.
  Preconditions: len(points) = len(s), 1 <= len(points) <= 10^5, each points[i] has length 2, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9 for every 0 <= i < len(points), the coordinate pairs points[i] are pairwise distinct, and each s[i] is a lowercase English letter (ASCII byte). -/
theorem spec_3 (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s) :
    ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      ∃ R : Int,
        0 ≤ R ∧ r.val = (countLe points R : Int) ∧ (bytesLe points s R).Nodup := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s), ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      ∃ R : Int,
        0 ≤ R ∧ r.val = (countLe points R : Int) ∧ (bytesLe points s R).Nodup) := by
  sorry

/-- Whenever the function returns a result r, for every real number R >= 0, if the bytes s[i] for all indices i with max(abs(points[i][0]), abs(points[i][1])) <= R are pairwise distinct, then the number of such indices is at most r.
  Preconditions: len(points) = len(s), 1 <= len(points) <= 10^5, each points[i] has length 2, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9 for every 0 <= i < len(points), the coordinate pairs points[i] are pairwise distinct, and each s[i] is a lowercase English letter (ASCII byte). -/
theorem spec_4 (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s) :
    ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      ∀ R : Int, 0 ≤ R → (bytesLe points s R).Nodup →
        (countLe points R : Int) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s), ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      ∀ R : Int, 0 ≤ R → (bytesLe points s R).Nodup →
        (countLe points R : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = len(points) if and only if no byte value occurs twice in s (equivalently, for all 0 <= i < len(points) and 0 <= j < len(points), s[i] = s[j] implies i = j).
  Preconditions: len(points) = len(s), 1 <= len(points) <= 10^5, each points[i] has length 2, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9 for every 0 <= i < len(points), the coordinate pairs points[i] are pairwise distinct, and each s[i] is a lowercase English letter (ASCII byte). -/
theorem spec_5 (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s) :
    ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      (r.val = (points.val.length : Int) ↔ (bytes s).Nodup) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s), ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      (r.val = (points.val.length : Int) ↔ (bytes s).Nodup)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there exist distinct indices i and j with 0 <= i < len(points), 0 <= j < len(points) such that s[i] = s[j] and max(abs(points[i][0]), abs(points[i][1])) = max(abs(points[j][0]), abs(points[j][1])) = min_{0 <= k < len(points)} max(abs(points[k][0]), abs(points[k][1])).
  Preconditions: len(points) = len(s), 1 <= len(points) <= 10^5, each points[i] has length 2, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9 for every 0 <= i < len(points), the coordinate pairs points[i] are pairwise distinct, and each s[i] is a lowercase English letter (ASCII byte). -/
theorem spec_6 (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s) :
    ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      (r.val = 0 ↔
        ∃ i j : Nat,
          i < points.val.length ∧ j < points.val.length ∧ i ≠ j ∧
            byteAt s i = byteAt s j ∧ dAt points i = dAt points j ∧
            (dists points).min? = some (dAt points i)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s), ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      (r.val = 0 ↔
        ∃ i j : Nat,
          i < points.val.length ∧ j < points.val.length ∧ i ≠ j ∧
            byteAt s i = byteAt s j ∧ dAt points i = dAt points j ∧
            (dists points).min? = some (dAt points i))) := by
  sorry

/-- Whenever the function returns a result r, if all bytes in s are equal and the values max(abs(points[i][0]), abs(points[i][1])) are pairwise distinct for 0 <= i < len(points), then r = 1.
  Preconditions: len(points) = len(s), 1 <= len(points) <= 10^5, each points[i] has length 2, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9 for every 0 <= i < len(points), the coordinate pairs points[i] are pairwise distinct, and each s[i] is a lowercase English letter (ASCII byte). -/
theorem spec_7 (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s) :
    ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      (∀ i j : Nat, i < points.val.length → j < points.val.length →
          byteAt s i = byteAt s j) →
        (dists points).Nodup → r.val = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s), ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      (∀ i j : Nat, i < points.val.length → j < points.val.length →
          byteAt s i = byteAt s j) →
        (dists points).Nodup → r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, r <= the number of distinct byte values occurring in s, i.e. the cardinality of the set {s[i] | 0 <= i < len(points)}.
  Preconditions: len(points) = len(s), 1 <= len(points) <= 10^5, each points[i] has length 2, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9 for every 0 <= i < len(points), the coordinate pairs points[i] are pairwise distinct, and each s[i] is a lowercase English letter (ASCII byte). -/
theorem spec_8 (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s) :
    ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      r.val ≤ ((bytes s).dedup.length : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s), ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      r.val ≤ ((bytes s).dedup.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every byte c that occurs at least twice in s, let t_c be the second smallest value, with multiplicity, in the multiset {max(abs(points[k][0]), abs(points[k][1])) | 0 <= k < len(points) and s[k] = c}. Then r <= the number of indices k with 0 <= k < len(points) and max(abs(points[k][0]), abs(points[k][1])) < t_c.
  Preconditions: len(points) = len(s), 1 <= len(points) <= 10^5, each points[i] has length 2, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9 for every 0 <= i < len(points), the coordinate pairs points[i] are pairwise distinct, and each s[i] is a lowercase English letter (ASCII byte). -/
theorem spec_9 (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s) :
    ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      ∀ (c : Nat) (t : Int),
        2 ≤ (classValues points s c).length →
          secondSmallest? (classValues points s c) = some t →
            r.val ≤ (countBelow points t : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s), ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      ∀ (c : Nat) (t : Int),
        2 ≤ (classValues points s c).length →
          secondSmallest? (classValues points s c) = some t →
            r.val ≤ (countBelow points t : Int)) := by
  sorry

/-- Whenever the function returns a result r on points and s, for any points2 such that len(points2) = len(points), each points2[i] has length 2, -10^9 <= points2[i][0] <= 10^9 and -10^9 <= points2[i][1] <= 10^9 for every 0 <= i < len(points2), the coordinate pairs points2[i] are pairwise distinct, and for every 0 <= i < len(points), max(abs(points2[i][0]), abs(points2[i][1])) = max(abs(points[i][0]), abs(points[i][1])), if the function returns r2 on points2 and the same s, then r2 = r.
  Preconditions: len(points) = len(s), 1 <= len(points) <= 10^5, each points[i] has length 2, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9 for every 0 <= i < len(points), the coordinate pairs points[i] are pairwise distinct, and each s[i] is a lowercase English letter (ASCII byte). -/
theorem spec_10 (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s) :
    ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      ∀ points2 : Slice (Vec I64),
        points2.val.length = points.val.length →
          PointsPre points2 →
            (∀ i : Nat, i < points.val.length → dAt points2 i = dAt points i) →
              ∀ r2 : I64,
                Aegis.MaxPointsInsideSquare.max_points_inside_square points2 s = ok r2 →
                  r2 = r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s), ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      ∀ points2 : Slice (Vec I64),
        points2.val.length = points.val.length →
          PointsPre points2 →
            (∀ i : Nat, i < points.val.length → dAt points2 i = dAt points i) →
              ∀ r2 : I64,
                Aegis.MaxPointsInsideSquare.max_points_inside_square points2 s = ok r2 →
                  r2 = r) := by
  sorry

/-- Whenever the function returns r on points and s, for any bijection pi of the index set {0,...,len(points)-1}, if points2[i] = points[pi(i)] and s2[i] = s[pi(i)] for every i, and the function returns r2 on points2 and s2, then r2 = r.
  Preconditions: len(points) = len(s), 1 <= len(points) <= 10^5, each points[i] has length 2, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9 for every 0 <= i < len(points), the coordinate pairs points[i] are pairwise distinct, and each s[i] is a lowercase English letter (ASCII byte). -/
theorem spec_11 (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s) :
    ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      ∀ (points2 : Slice (Vec I64)) (s2 : Slice U8),
        (∃ π : Equiv.Perm (Fin points.val.length),
            points2.val = List.ofFn (fun i : Fin points.val.length => points.val.get (π i)) ∧
              s2.val = List.ofFn (fun i : Fin points.val.length =>
                s.val.get ⟨(π i).val, by
                  rw [← hpre.1]
                  exact (π i).isLt⟩)) →
          ∀ r2 : I64,
            Aegis.MaxPointsInsideSquare.max_points_inside_square points2 s2 = ok r2 →
              r2 = r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s), ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      ∀ (points2 : Slice (Vec I64)) (s2 : Slice U8),
        (∃ π : Equiv.Perm (Fin points.val.length),
            points2.val = List.ofFn (fun i : Fin points.val.length => points.val.get (π i)) ∧
              s2.val = List.ofFn (fun i : Fin points.val.length =>
                s.val.get ⟨(π i).val, by
                  rw [← hpre.1]
                  exact (π i).isLt⟩)) →
          ∀ r2 : I64,
            Aegis.MaxPointsInsideSquare.max_points_inside_square points2 s2 = ok r2 →
              r2 = r) := by
  sorry

/-- Whenever the function returns a result r, let D = min_{0 <= k < len(points)} max(abs(points[k][0]), abs(points[k][1])). If the bytes s[i] for all indices i with max(abs(points[i][0]), abs(points[i][1])) = D are pairwise distinct, then r >= the number of indices i with max(abs(points[i][0]), abs(points[i][1])) = D.
  Preconditions: len(points) = len(s), 1 <= len(points) <= 10^5, each points[i] has length 2, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9 for every 0 <= i < len(points), the coordinate pairs points[i] are pairwise distinct, and each s[i] is a lowercase English letter (ASCII byte). -/
theorem spec_12 (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s) :
    ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      ∀ D : Int,
        (dists points).min? = some D →
          (bytesEq points s D).Nodup → (countEq points D : Int) ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s), ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      ∀ D : Int,
        (dists points).min? = some D →
          (bytesEq points s D).Nodup → (countEq points D : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists R >= 0 such that R = 0 or R = max(abs(points[i][0]), abs(points[i][1])) for some 0 <= i < len(points), exactly r indices j satisfy max(abs(points[j][0]), abs(points[j][1])) <= R, and the bytes s[j] for those r indices are pairwise distinct.
  Preconditions: len(points) = len(s), 1 <= len(points) <= 10^5, each points[i] has length 2, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9 for every 0 <= i < len(points), the coordinate pairs points[i] are pairwise distinct, and each s[i] is a lowercase English letter (ASCII byte). -/
theorem spec_13 (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s) :
    ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      ∃ R : Int,
        0 ≤ R ∧
          (R = 0 ∨ ∃ i : Nat, i < points.val.length ∧ R = dAt points i) ∧
            r.val = (countLe points R : Int) ∧ (bytesLe points s R).Nodup := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (points : Slice (Vec I64)) (s : Slice U8) (hpre : Pre points s), ∀ r : I64, Aegis.MaxPointsInsideSquare.max_points_inside_square points s = ok r →
      ∃ R : Int,
        0 ≤ R ∧
          (R = 0 ∨ ∃ i : Nat, i < points.val.length ∧ R = dAt points i) ∧
            r.val = (countLe points R : Int) ∧ (bytesLe points s R).Nodup) := by
  sorry

end AegisSpec.MaxPointsInsideSquare
