import Aegis.CountPoints.Code.Funs

/-!
# Specifications of `Aegis.CountPoints.count_points`

LeetCode problem `queries-on-number-of-points-inside-a-circle`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aeneas.Std.alloc.vec

namespace AegisSpec.CountPoints

open Aegis.CountPoints (count_points)

def entry (v : Vec I64) (k : Nat) : Option Int := (v.val[k]?).map (fun x => x.val)

def coord (s : Slice (Vec I64)) (i k : Nat) : Int :=
  ((s.val[i]?).map (fun v => (entry v k).getD 0)).getD 0

def dimAt (s : Slice (Vec I64)) (i : Nat) : Nat :=
  ((s.val[i]?).map (fun v => v.val.length)).getD 0

def px (points : Slice (Vec I64)) (i : Nat) : Int := coord points i 0

def py (points : Slice (Vec I64)) (i : Nat) : Int := coord points i 1

def qx (queries : Slice (Vec I64)) (j : Nat) : Int := coord queries j 0

def qy (queries : Slice (Vec I64)) (j : Nat) : Int := coord queries j 1

def qr (queries : Slice (Vec I64)) (j : Nat) : Int := coord queries j 2

def D (points queries : Slice (Vec I64)) (i j : Nat) : Int :=
  (px points i - qx queries j) ^ 2 + (py points i - qy queries j) ^ 2

def R2 (queries : Slice (Vec I64)) (j : Nat) : Int := (qr queries j) ^ 2

def countWithin (points queries : Slice (Vec I64)) (j : Nat) : Nat :=
  (List.range points.val.length).countP
    (fun i => decide (D points queries i j ≤ R2 queries j))

def coincidenceCount (points queries : Slice (Vec I64)) (j : Nat) : Nat :=
  (List.range points.val.length).countP
    (fun i => decide (px points i = qx queries j ∧ py points i = qy queries j))

def entryLe (r r' : Vec I64) (j j' : Nat) : Prop :=
  ∃ a b : Int, entry r j = some a ∧ entry r' j' = some b ∧ a ≤ b

/-- Let D(i,j) = (points[i][0] - queries[j][0])^2 + (points[i][1] - queries[j][1])^2, computed as an ordinary integer. The function returns a result r such that len(r) = len(queries), and for every j with 0 <= j < len(queries), r[j] is the cardinality of the set { i : 0 <= i < len(points) and D(i,j) <= (queries[j][2])^2 }. Equivalently, r[j] is the number of point indices whose Euclidean distance to the center (queries[j][0], queries[j][1]) is at most queries[j][2]. Points exactly on the circle border satisfy equality and are counted because the comparison is <=.
  Preconditions: len(points) is an integer with 1 <= len(points) <= 500. For every i with 0 <= i < len(points), len(points[i]) = 2, and points[i][0] and points[i][1] are integers with 0 <= points[i][0] <= 500 and 0 <= points[i][1] <= 500. len(queries) is an integer with 1 <= len(queries) <= 500. For every j with 0 <= j < len(queries), len(queries[j]) = 3, and queries[j][0], queries[j][1], queries[j][2] are integers with 0 <= queries[j][0] <= 500, 0 <= queries[j][1] <= 500, and 1 <= queries[j][2] <= 500. All vector entries are I64 values; every integer expression used in the statement stays within the I64 range. -/
theorem spec_1 (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500) :
    ∃ r : Vec I64,
      count_points points queries = ok r ∧
      r.val.length = queries.val.length ∧
      ∀ j, j < queries.val.length →
        entry r j = some (↑(countWithin points queries j) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500), ∃ r : Vec I64,
      count_points points queries = ok r ∧
      r.val.length = queries.val.length ∧
      ∀ j, j < queries.val.length →
        entry r j = some (↑(countWithin points queries j) : Int)) := by
  sorry

/-- The function returns a result r; that is, there exists a Vec I64 value r such that count_points points queries = Result.ok r. In particular, under these preconditions the function does not fail, panic, or overflow.
  Preconditions: len(points) is an integer with 1 <= len(points) <= 500. For every i with 0 <= i < len(points), len(points[i]) = 2, and points[i][0] and points[i][1] are integers with 0 <= points[i][0] <= 500 and 0 <= points[i][1] <= 500. len(queries) is an integer with 1 <= len(queries) <= 500. For every j with 0 <= j < len(queries), len(queries[j]) = 3, and queries[j][0], queries[j][1], queries[j][2] are integers with 0 <= queries[j][0] <= 500, 0 <= queries[j][1] <= 500, and 1 <= queries[j][2] <= 500. All vector entries are I64 values; every integer expression used in the statement stays within the I64 range. -/
theorem spec_2 (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500) :
    ∃ r : Vec I64, count_points points queries = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500), ∃ r : Vec I64, count_points points queries = ok r) := by
  sorry

/-- Whenever count_points points queries returns a result r, len(r) = len(queries). In other words, the output has exactly one entry for each query and no additional entries.
  Preconditions: len(points) is an integer with 1 <= len(points) <= 500. For every i with 0 <= i < len(points), len(points[i]) = 2, and points[i][0] and points[i][1] are integers with 0 <= points[i][0] <= 500 and 0 <= points[i][1] <= 500. len(queries) is an integer with 1 <= len(queries) <= 500. For every j with 0 <= j < len(queries), len(queries[j]) = 3, and queries[j][0], queries[j][1], queries[j][2] are integers with 0 <= queries[j][0] <= 500, 0 <= queries[j][1] <= 500, and 1 <= queries[j][2] <= 500. All vector entries are I64 values; every integer expression used in the statement stays within the I64 range. -/
theorem spec_3 (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500) :
    ∀ r : Vec I64, count_points points queries = ok r → r.val.length = queries.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500), ∀ r : Vec I64, count_points points queries = ok r → r.val.length = queries.val.length) := by
  sorry

/-- Whenever count_points points queries returns a result r, for every j with 0 <= j < len(queries), 0 <= r[j] <= len(points).
  Preconditions: len(points) is an integer with 1 <= len(points) <= 500. For every i with 0 <= i < len(points), len(points[i]) = 2, and points[i][0] and points[i][1] are integers with 0 <= points[i][0] <= 500 and 0 <= points[i][1] <= 500. len(queries) is an integer with 1 <= len(queries) <= 500. For every j with 0 <= j < len(queries), len(queries[j]) = 3, and queries[j][0], queries[j][1], queries[j][2] are integers with 0 <= queries[j][0] <= 500, 0 <= queries[j][1] <= 500, and 1 <= queries[j][2] <= 500. All vector entries are I64 values; every integer expression used in the statement stays within the I64 range. -/
theorem spec_4 (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500) :
    ∀ r : Vec I64, count_points points queries = ok r →
      ∀ j, j < queries.val.length →
        ∃ n : Int, entry r j = some n ∧ 0 ≤ n ∧ n ≤ (points.val.length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500), ∀ r : Vec I64, count_points points queries = ok r →
      ∀ j, j < queries.val.length →
        ∃ n : Int, entry r j = some n ∧ 0 ≤ n ∧ n ≤ (points.val.length : Int)) := by
  sorry

/-- Let D(i,j) = (points[i][0] - queries[j][0])^2 + (points[i][1] - queries[j][1])^2. If for some query index j there exists a point index i0 with 0 <= i0 < len(points) such that D(i0,j) = (queries[j][2])^2 and for every other point index i with 0 <= i < len(points) and i != i0, D(i,j) > (queries[j][2])^2, then whenever count_points returns r, r[j] = 1.
  Preconditions: len(points) is an integer with 1 <= len(points) <= 500. For every i with 0 <= i < len(points), len(points[i]) = 2, and points[i][0] and points[i][1] are integers with 0 <= points[i][0] <= 500 and 0 <= points[i][1] <= 500. len(queries) is an integer with 1 <= len(queries) <= 500. For every j with 0 <= j < len(queries), len(queries[j]) = 3, and queries[j][0], queries[j][1], queries[j][2] are integers with 0 <= queries[j][0] <= 500, 0 <= queries[j][1] <= 500, and 1 <= queries[j][2] <= 500. All vector entries are I64 values; every integer expression used in the statement stays within the I64 range. -/
theorem spec_5 (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500) :
    ∀ j, j < queries.val.length →
      (∃ i0, i0 < points.val.length ∧ D points queries i0 j = R2 queries j ∧
        ∀ i, i < points.val.length → i ≠ i0 → R2 queries j < D points queries i j) →
      ∀ r : Vec I64, count_points points queries = ok r → entry r j = some 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500), ∀ j, j < queries.val.length →
      (∃ i0, i0 < points.val.length ∧ D points queries i0 j = R2 queries j ∧
        ∀ i, i < points.val.length → i ≠ i0 → R2 queries j < D points queries i j) →
      ∀ r : Vec I64, count_points points queries = ok r → entry r j = some 1) := by
  sorry

/-- Let D(i,j) = (points[i][0] - queries[j][0])^2 + (points[i][1] - queries[j][1])^2. If for some query index j, for every point index i with 0 <= i < len(points), D(i,j) > (queries[j][2])^2, then whenever count_points returns r, r[j] = 0.
  Preconditions: len(points) is an integer with 1 <= len(points) <= 500. For every i with 0 <= i < len(points), len(points[i]) = 2, and points[i][0] and points[i][1] are integers with 0 <= points[i][0] <= 500 and 0 <= points[i][1] <= 500. len(queries) is an integer with 1 <= len(queries) <= 500. For every j with 0 <= j < len(queries), len(queries[j]) = 3, and queries[j][0], queries[j][1], queries[j][2] are integers with 0 <= queries[j][0] <= 500, 0 <= queries[j][1] <= 500, and 1 <= queries[j][2] <= 500. All vector entries are I64 values; every integer expression used in the statement stays within the I64 range. -/
theorem spec_6 (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500) :
    ∀ j, j < queries.val.length →
      (∀ i, i < points.val.length → R2 queries j < D points queries i j) →
      ∀ r : Vec I64, count_points points queries = ok r → entry r j = some 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500), ∀ j, j < queries.val.length →
      (∀ i, i < points.val.length → R2 queries j < D points queries i j) →
      ∀ r : Vec I64, count_points points queries = ok r → entry r j = some 0) := by
  sorry

/-- Let D(i,j) = (points[i][0] - queries[j][0])^2 + (points[i][1] - queries[j][1])^2. If for some query index j, for every point index i with 0 <= i < len(points), D(i,j) <= (queries[j][2])^2, then whenever count_points returns r, r[j] = len(points).
  Preconditions: len(points) is an integer with 1 <= len(points) <= 500. For every i with 0 <= i < len(points), len(points[i]) = 2, and points[i][0] and points[i][1] are integers with 0 <= points[i][0] <= 500 and 0 <= points[i][1] <= 500. len(queries) is an integer with 1 <= len(queries) <= 500. For every j with 0 <= j < len(queries), len(queries[j]) = 3, and queries[j][0], queries[j][1], queries[j][2] are integers with 0 <= queries[j][0] <= 500, 0 <= queries[j][1] <= 500, and 1 <= queries[j][2] <= 500. All vector entries are I64 values; every integer expression used in the statement stays within the I64 range. -/
theorem spec_7 (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500) :
    ∀ j, j < queries.val.length →
      (∀ i, i < points.val.length → D points queries i j ≤ R2 queries j) →
      ∀ r : Vec I64, count_points points queries = ok r →
        entry r j = some (points.val.length : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500), ∀ j, j < queries.val.length →
      (∀ i, i < points.val.length → D points queries i j ≤ R2 queries j) →
      ∀ r : Vec I64, count_points points queries = ok r →
        entry r j = some (points.val.length : Int)) := by
  sorry

/-- For any query indices j1,j2 with 0 <= j1,j2 < len(queries), if queries[j1][0] = queries[j2][0] and queries[j1][1] = queries[j2][1] and queries[j1][2] <= queries[j2][2], then whenever count_points returns r, r[j1] <= r[j2].
  Preconditions: len(points) is an integer with 1 <= len(points) <= 500. For every i with 0 <= i < len(points), len(points[i]) = 2, and points[i][0] and points[i][1] are integers with 0 <= points[i][0] <= 500 and 0 <= points[i][1] <= 500. len(queries) is an integer with 1 <= len(queries) <= 500. For every j with 0 <= j < len(queries), len(queries[j]) = 3, and queries[j][0], queries[j][1], queries[j][2] are integers with 0 <= queries[j][0] <= 500, 0 <= queries[j][1] <= 500, and 1 <= queries[j][2] <= 500. All vector entries are I64 values; every integer expression used in the statement stays within the I64 range. -/
theorem spec_8 (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500) :
    ∀ j1 j2, j1 < queries.val.length → j2 < queries.val.length →
      qx queries j1 = qx queries j2 → qy queries j1 = qy queries j2 →
      qr queries j1 ≤ qr queries j2 →
      ∀ r : Vec I64, count_points points queries = ok r → entryLe r r j1 j2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500), ∀ j1 j2, j1 < queries.val.length → j2 < queries.val.length →
      qx queries j1 = qx queries j2 → qy queries j1 = qy queries j2 →
      qr queries j1 ≤ qr queries j2 →
      ∀ r : Vec I64, count_points points queries = ok r → entryLe r r j1 j2) := by
  sorry

/-- Whenever count_points points queries returns r and count_points points' queries returns r', for every j with 0 <= j < len(queries), r[j] = r'[j].
  Preconditions: len(points) is an integer with 1 <= len(points) <= 500. For every i with 0 <= i < len(points), len(points[i]) = 2, and points[i][0] and points[i][1] are integers with 0 <= points[i][0] <= 500 and 0 <= points[i][1] <= 500. len(queries) is an integer with 1 <= len(queries) <= 500. For every j with 0 <= j < len(queries), len(queries[j]) = 3, and queries[j][0], queries[j][1], queries[j][2] are integers with 0 <= queries[j][0] <= 500, 0 <= queries[j][1] <= 500, and 1 <= queries[j][2] <= 500. In addition, points' is a point array with 1 <= len(points') <= 500, for every i with 0 <= i < len(points'), len(points'[i]) = 2, 0 <= points'[i][0] <= 500, and 0 <= points'[i][1] <= 500; len(points') = len(points); and there exists a permutation π of {0,...,len(points)-1} such that points'[i] = points[π(i)] for every i with 0 <= i < len(points). All vector entries are I64 values; every integer expression used in the statement stays within the I64 range. -/
theorem spec_9 (points points' queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500)
    (hpc' : 1 ≤ points'.val.length ∧ points'.val.length ≤ 500)
    (hpdim' : ∀ i, i < points'.val.length → dimAt points' i = 2)
    (hpx' : ∀ i, i < points'.val.length → 0 ≤ px points' i ∧ px points' i ≤ 500)
    (hpy' : ∀ i, i < points'.val.length → 0 ≤ py points' i ∧ py points' i ≤ 500)
    (hlen : points'.val.length = points.val.length)
    (hperm : ∃ π : Equiv.Perm (Fin points.val.length),
      ∀ (i : Nat) (h : i < points.val.length),
        px points' i = px points (π ⟨i, h⟩) ∧ py points' i = py points (π ⟨i, h⟩)) :
    ∀ r r' : Vec I64, count_points points queries = ok r →
      count_points points' queries = ok r' →
      ∀ j, j < queries.val.length → entry r j = entry r' j := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (points points' queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500)
    (hpc' : 1 ≤ points'.val.length ∧ points'.val.length ≤ 500)
    (hpdim' : ∀ i, i < points'.val.length → dimAt points' i = 2)
    (hpx' : ∀ i, i < points'.val.length → 0 ≤ px points' i ∧ px points' i ≤ 500)
    (hpy' : ∀ i, i < points'.val.length → 0 ≤ py points' i ∧ py points' i ≤ 500)
    (hlen : points'.val.length = points.val.length)
    (hperm : ∃ π : Equiv.Perm (Fin points.val.length),
      ∀ (i : Nat) (h : i < points.val.length),
        px points' i = px points (π ⟨i, h⟩) ∧ py points' i = py points (π ⟨i, h⟩)), ∀ r r' : Vec I64, count_points points queries = ok r →
      count_points points' queries = ok r' →
      ∀ j, j < queries.val.length → entry r j = entry r' j) := by
  sorry

/-- If count_points points queries returns r and count_points points queries' returns r', then for every j with 0 <= j < len(queries), r'[j] = r[π(j)].
  Preconditions: len(points) is an integer with 1 <= len(points) <= 500. For every i with 0 <= i < len(points), len(points[i]) = 2, and points[i][0] and points[i][1] are integers with 0 <= points[i][0] <= 500 and 0 <= points[i][1] <= 500. len(queries) is an integer with 1 <= len(queries) <= 500. For every j with 0 <= j < len(queries), len(queries[j]) = 3, and queries[j][0], queries[j][1], queries[j][2] are integers with 0 <= queries[j][0] <= 500, 0 <= queries[j][1] <= 500, and 1 <= queries[j][2] <= 500. In addition, queries' is a query array with 1 <= len(queries') <= 500, for every j with 0 <= j < len(queries'), len(queries'[j]) = 3, 0 <= queries'[j][0] <= 500, 0 <= queries'[j][1] <= 500, and 1 <= queries'[j][2] <= 500; len(queries') = len(queries); and there exists a permutation π of {0,...,len(queries)-1} such that queries'[j] = queries[π(j)] for every j with 0 <= j < len(queries). All vector entries are I64 values; every integer expression used in the statement stays within the I64 range. -/
theorem spec_10 (points queries queries' : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500)
    (hqc' : 1 ≤ queries'.val.length ∧ queries'.val.length ≤ 500)
    (hqdim' : ∀ j, j < queries'.val.length → dimAt queries' j = 3)
    (hqx' : ∀ j, j < queries'.val.length → 0 ≤ qx queries' j ∧ qx queries' j ≤ 500)
    (hqy' : ∀ j, j < queries'.val.length → 0 ≤ qy queries' j ∧ qy queries' j ≤ 500)
    (hqr' : ∀ j, j < queries'.val.length → 1 ≤ qr queries' j ∧ qr queries' j ≤ 500)
    (hlen : queries'.val.length = queries.val.length)
    (π : Equiv.Perm (Fin queries.val.length))
    (hperm : ∀ (j : Nat) (h : j < queries.val.length),
      qx queries' j = qx queries (π ⟨j, h⟩) ∧ qy queries' j = qy queries (π ⟨j, h⟩) ∧
        qr queries' j = qr queries (π ⟨j, h⟩)) :
    ∀ r r' : Vec I64, count_points points queries = ok r →
      count_points points queries' = ok r' →
      ∀ (j : Nat) (h : j < queries.val.length), entry r' j = entry r (π ⟨j, h⟩) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (points queries queries' : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500)
    (hqc' : 1 ≤ queries'.val.length ∧ queries'.val.length ≤ 500)
    (hqdim' : ∀ j, j < queries'.val.length → dimAt queries' j = 3)
    (hqx' : ∀ j, j < queries'.val.length → 0 ≤ qx queries' j ∧ qx queries' j ≤ 500)
    (hqy' : ∀ j, j < queries'.val.length → 0 ≤ qy queries' j ∧ qy queries' j ≤ 500)
    (hqr' : ∀ j, j < queries'.val.length → 1 ≤ qr queries' j ∧ qr queries' j ≤ 500)
    (hlen : queries'.val.length = queries.val.length)
    (π : Equiv.Perm (Fin queries.val.length))
    (hperm : ∀ (j : Nat) (h : j < queries.val.length),
      qx queries' j = qx queries (π ⟨j, h⟩) ∧ qy queries' j = qy queries (π ⟨j, h⟩) ∧
        qr queries' j = qr queries (π ⟨j, h⟩)), ∀ r r' : Vec I64, count_points points queries = ok r →
      count_points points queries' = ok r' →
      ∀ (j : Nat) (h : j < queries.val.length), entry r' j = entry r (π ⟨j, h⟩)) := by
  sorry

/-- For any indices j1,j2 with 0 <= j1,j2 < len(queries), if queries[j1][0] = queries[j2][0], queries[j1][1] = queries[j2][1], and queries[j1][2] = queries[j2][2], then whenever count_points returns r, r[j1] = r[j2].
  Preconditions: len(points) is an integer with 1 <= len(points) <= 500. For every i with 0 <= i < len(points), len(points[i]) = 2, and points[i][0] and points[i][1] are integers with 0 <= points[i][0] <= 500 and 0 <= points[i][1] <= 500. len(queries) is an integer with 1 <= len(queries) <= 500. For every j with 0 <= j < len(queries), len(queries[j]) = 3, and queries[j][0], queries[j][1], queries[j][2] are integers with 0 <= queries[j][0] <= 500, 0 <= queries[j][1] <= 500, and 1 <= queries[j][2] <= 500. All vector entries are I64 values; every integer expression used in the statement stays within the I64 range. -/
theorem spec_11 (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500) :
    ∀ j1 j2, j1 < queries.val.length → j2 < queries.val.length →
      qx queries j1 = qx queries j2 → qy queries j1 = qy queries j2 →
      qr queries j1 = qr queries j2 →
      ∀ r : Vec I64, count_points points queries = ok r → entry r j1 = entry r j2 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500), ∀ j1 j2, j1 < queries.val.length → j2 < queries.val.length →
      qx queries j1 = qx queries j2 → qy queries j1 = qy queries j2 →
      qr queries j1 = qr queries j2 →
      ∀ r : Vec I64, count_points points queries = ok r → entry r j1 = entry r j2) := by
  sorry

/-- If count_points points queries returns r and count_points points⁺ queries returns r⁺, then for every j with 0 <= j < len(queries), r⁺[j] = r[j] + I_j, where I_j = 1 if (p[0]-queries[j][0])^2 + (p[1]-queries[j][1])^2 <= (queries[j][2])^2, and I_j = 0 otherwise.
  Preconditions: len(points) is an integer with 1 <= len(points) <= 500. For every i with 0 <= i < len(points), len(points[i]) = 2, and points[i][0] and points[i][1] are integers with 0 <= points[i][0] <= 500 and 0 <= points[i][1] <= 500. len(queries) is an integer with 1 <= len(queries) <= 500. For every j with 0 <= j < len(queries), len(queries[j]) = 3, and queries[j][0], queries[j][1], queries[j][2] are integers with 0 <= queries[j][0] <= 500, 0 <= queries[j][1] <= 500, and 1 <= queries[j][2] <= 500. In addition, points⁺ is a point array with 1 <= len(points⁺) <= 500, for every i with 0 <= i < len(points⁺), len(points⁺[i]) = 2, 0 <= points⁺[i][0] <= 500, and 0 <= points⁺[i][1] <= 500; len(points⁺) = len(points)+1; points⁺[i] = points[i] for every i with 0 <= i < len(points); and p = points⁺[len(points)] is the appended point. All vector entries are I64 values; every integer expression used in the statement stays within the I64 range. -/
theorem spec_12 (points pointsExt queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500)
    (hpcExt : 1 ≤ pointsExt.val.length ∧ pointsExt.val.length ≤ 500)
    (hpdimExt : ∀ i, i < pointsExt.val.length → dimAt pointsExt i = 2)
    (hpxExt : ∀ i, i < pointsExt.val.length → 0 ≤ px pointsExt i ∧ px pointsExt i ≤ 500)
    (hpyExt : ∀ i, i < pointsExt.val.length → 0 ≤ py pointsExt i ∧ py pointsExt i ≤ 500)
    (hlen : pointsExt.val.length = points.val.length + 1)
    (hpre : ∀ i, i < points.val.length →
      px pointsExt i = px points i ∧ py pointsExt i = py points i) :
    ∀ r rExt : Vec I64, count_points points queries = ok r →
      count_points pointsExt queries = ok rExt →
      ∀ j, j < queries.val.length →
        ∃ a b : Int, entry r j = some a ∧ entry rExt j = some b ∧
          b = a + (if D pointsExt queries points.val.length j ≤ R2 queries j then (1 : Int) else 0) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (points pointsExt queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500)
    (hpcExt : 1 ≤ pointsExt.val.length ∧ pointsExt.val.length ≤ 500)
    (hpdimExt : ∀ i, i < pointsExt.val.length → dimAt pointsExt i = 2)
    (hpxExt : ∀ i, i < pointsExt.val.length → 0 ≤ px pointsExt i ∧ px pointsExt i ≤ 500)
    (hpyExt : ∀ i, i < pointsExt.val.length → 0 ≤ py pointsExt i ∧ py pointsExt i ≤ 500)
    (hlen : pointsExt.val.length = points.val.length + 1)
    (hpre : ∀ i, i < points.val.length →
      px pointsExt i = px points i ∧ py pointsExt i = py points i), ∀ r rExt : Vec I64, count_points points queries = ok r →
      count_points pointsExt queries = ok rExt →
      ∀ j, j < queries.val.length →
        ∃ a b : Int, entry r j = some a ∧ entry rExt j = some b ∧
          b = a + (if D pointsExt queries points.val.length j ≤ R2 queries j then (1 : Int) else 0)) := by
  sorry

/-- If count_points points queries returns r and count_points points' queries' returns r', then for every j with 0 <= j < len(queries), r[j] = r'[j].
  Preconditions: len(points) is an integer with 1 <= len(points) <= 500. For every i with 0 <= i < len(points), len(points[i]) = 2, and points[i][0] and points[i][1] are integers with 0 <= points[i][0] <= 500 and 0 <= points[i][1] <= 500. len(queries) is an integer with 1 <= len(queries) <= 500. For every j with 0 <= j < len(queries), len(queries[j]) = 3, and queries[j][0], queries[j][1], queries[j][2] are integers with 0 <= queries[j][0] <= 500, 0 <= queries[j][1] <= 500, and 1 <= queries[j][2] <= 500. In addition, points' is a point array with 1 <= len(points') <= 500, for every i with 0 <= i < len(points'), len(points'[i]) = 2, 0 <= points'[i][0] <= 500, and 0 <= points'[i][1] <= 500; queries' is a query array with 1 <= len(queries') <= 500, for every j with 0 <= j < len(queries'), len(queries'[j]) = 3, 0 <= queries'[j][0] <= 500, 0 <= queries'[j][1] <= 500, and 1 <= queries'[j][2] <= 500; len(points') = len(points); len(queries') = len(queries); and there exist integers tx,ty such that for every i with 0 <= i < len(points), points'[i][0] = points[i][0]+tx and points'[i][1] = points[i][1]+ty, and for every j with 0 <= j < len(queries), queries'[j][0] = queries[j][0]+tx, queries'[j][1] = queries[j][1]+ty, and queries'[j][2] = queries[j][2]. All vector entries are I64 values; every integer expression used in the statement stays within the I64 range. -/
theorem spec_13 (points points' queries queries' : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500)
    (hpc' : 1 ≤ points'.val.length ∧ points'.val.length ≤ 500)
    (hpdim' : ∀ i, i < points'.val.length → dimAt points' i = 2)
    (hpx' : ∀ i, i < points'.val.length → 0 ≤ px points' i ∧ px points' i ≤ 500)
    (hpy' : ∀ i, i < points'.val.length → 0 ≤ py points' i ∧ py points' i ≤ 500)
    (hqc' : 1 ≤ queries'.val.length ∧ queries'.val.length ≤ 500)
    (hqdim' : ∀ j, j < queries'.val.length → dimAt queries' j = 3)
    (hqx' : ∀ j, j < queries'.val.length → 0 ≤ qx queries' j ∧ qx queries' j ≤ 500)
    (hqy' : ∀ j, j < queries'.val.length → 0 ≤ qy queries' j ∧ qy queries' j ≤ 500)
    (hqr' : ∀ j, j < queries'.val.length → 1 ≤ qr queries' j ∧ qr queries' j ≤ 500)
    (hlenp : points'.val.length = points.val.length)
    (hlenq : queries'.val.length = queries.val.length)
    (htrans : ∃ tx ty : Int,
      (∀ i, i < points.val.length →
        px points' i = px points i + tx ∧ py points' i = py points i + ty) ∧
      (∀ j, j < queries.val.length →
        qx queries' j = qx queries j + tx ∧ qy queries' j = qy queries j + ty ∧
          qr queries' j = qr queries j)) :
    ∀ r r' : Vec I64, count_points points queries = ok r →
      count_points points' queries' = ok r' →
      ∀ j, j < queries.val.length → entry r j = entry r' j := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (points points' queries queries' : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500)
    (hpc' : 1 ≤ points'.val.length ∧ points'.val.length ≤ 500)
    (hpdim' : ∀ i, i < points'.val.length → dimAt points' i = 2)
    (hpx' : ∀ i, i < points'.val.length → 0 ≤ px points' i ∧ px points' i ≤ 500)
    (hpy' : ∀ i, i < points'.val.length → 0 ≤ py points' i ∧ py points' i ≤ 500)
    (hqc' : 1 ≤ queries'.val.length ∧ queries'.val.length ≤ 500)
    (hqdim' : ∀ j, j < queries'.val.length → dimAt queries' j = 3)
    (hqx' : ∀ j, j < queries'.val.length → 0 ≤ qx queries' j ∧ qx queries' j ≤ 500)
    (hqy' : ∀ j, j < queries'.val.length → 0 ≤ qy queries' j ∧ qy queries' j ≤ 500)
    (hqr' : ∀ j, j < queries'.val.length → 1 ≤ qr queries' j ∧ qr queries' j ≤ 500)
    (hlenp : points'.val.length = points.val.length)
    (hlenq : queries'.val.length = queries.val.length)
    (htrans : ∃ tx ty : Int,
      (∀ i, i < points.val.length →
        px points' i = px points i + tx ∧ py points' i = py points i + ty) ∧
      (∀ j, j < queries.val.length →
        qx queries' j = qx queries j + tx ∧ qy queries' j = qy queries j + ty ∧
          qr queries' j = qr queries j)), ∀ r r' : Vec I64, count_points points queries = ok r →
      count_points points' queries' = ok r' →
      ∀ j, j < queries.val.length → entry r j = entry r' j) := by
  sorry

/-- For every query index j with 0 <= j < len(queries), let C_j be the number of point indices i with 0 <= i < len(points) such that points[i][0] = queries[j][0] and points[i][1] = queries[j][1]. Whenever count_points returns r, r[j] >= C_j.
  Preconditions: len(points) is an integer with 1 <= len(points) <= 500. For every i with 0 <= i < len(points), len(points[i]) = 2, and points[i][0] and points[i][1] are integers with 0 <= points[i][0] <= 500 and 0 <= points[i][1] <= 500. len(queries) is an integer with 1 <= len(queries) <= 500. For every j with 0 <= j < len(queries), len(queries[j]) = 3, and queries[j][0], queries[j][1], queries[j][2] are integers with 0 <= queries[j][0] <= 500, 0 <= queries[j][1] <= 500, and 1 <= queries[j][2] <= 500. All vector entries are I64 values; every integer expression used in the statement stays within the I64 range. -/
theorem spec_14 (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500) :
    ∀ j, j < queries.val.length →
      ∀ r : Vec I64, count_points points queries = ok r →
        ∃ n : Int, entry r j = some n ∧ (coincidenceCount points queries j : Int) ≤ n := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (points queries : Slice (Vec I64))
    (hpc : 1 ≤ points.val.length ∧ points.val.length ≤ 500)
    (hpdim : ∀ i, i < points.val.length → dimAt points i = 2)
    (hpx : ∀ i, i < points.val.length → 0 ≤ px points i ∧ px points i ≤ 500)
    (hpy : ∀ i, i < points.val.length → 0 ≤ py points i ∧ py points i ≤ 500)
    (hqc : 1 ≤ queries.val.length ∧ queries.val.length ≤ 500)
    (hqdim : ∀ j, j < queries.val.length → dimAt queries j = 3)
    (hqx : ∀ j, j < queries.val.length → 0 ≤ qx queries j ∧ qx queries j ≤ 500)
    (hqy : ∀ j, j < queries.val.length → 0 ≤ qy queries j ∧ qy queries j ≤ 500)
    (hqr : ∀ j, j < queries.val.length → 1 ≤ qr queries j ∧ qr queries j ≤ 500), ∀ j, j < queries.val.length →
      ∀ r : Vec I64, count_points points queries = ok r →
        ∃ n : Int, entry r j = some n ∧ (coincidenceCount points queries j : Int) ≤ n) := by
  sorry

end AegisSpec.CountPoints
