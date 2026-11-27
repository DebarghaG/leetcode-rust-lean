import Aegis.NumberOfPairs.Code.Funs

/-!
# Specifications of `Aegis.NumberOfPairs.number_of_pairs`

LeetCode problem `find-the-number-of-ways-to-place-people-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.NumberOfPairs (number_of_pairs)

namespace AegisSpec.NumberOfPairs

abbrev Point : Type := ℤ × ℤ

abbrev Pts : Type := Slice (alloc.vec.Vec Std.I64)

def pointAt (points : Pts) (i : ℕ) : Point :=
  match points.val[i]? with
  | none => (0, 0)
  | some v =>
    match v.val with
    | [] => (0, 0)
    | [x] => (x.val, 0)
    | x :: y :: _ => (x.val, y.val)

def coordX (points : Pts) (i : ℕ) : ℤ := (pointAt points i).1

def coordY (points : Pts) (i : ℕ) : ℤ := (pointAt points i).2

def ValidInput (points : Pts) : Prop :=
  2 ≤ points.val.length ∧
  points.val.length ≤ 1000 ∧
  (∀ i, i < points.val.length → ∃ v, points.val[i]? = some v ∧ v.val.length = 2) ∧
  (∀ i, i < points.val.length →
    -1000000000 ≤ coordX points i ∧ coordX points i ≤ 1000000000 ∧
    -1000000000 ≤ coordY points i ∧ coordY points i ≤ 1000000000) ∧
  (∀ i j, i < j → j < points.val.length → pointAt points i ≠ pointAt points j)

def IsCountedPair (points : Pts) (i j : ℕ) : Prop :=
  i < points.val.length ∧ j < points.val.length ∧ i ≠ j ∧
  coordX points i ≤ coordX points j ∧
  coordY points j ≤ coordY points i ∧
  ∀ k, k < points.val.length → k ≠ i → k ≠ j →
    ¬ (coordX points i ≤ coordX points k ∧ coordX points k ≤ coordX points j ∧
       coordY points j ≤ coordY points k ∧ coordY points k ≤ coordY points i)

noncomputable def pairCount (points : Pts) : ℕ := by
  classical
  exact (((Finset.range points.val.length).product (Finset.range points.val.length)).filter
    (fun p => IsCountedPair points p.1 p.2)).card

def IsImage (T : Point → Point) (points q : Pts) : Prop :=
  q.val.length = points.val.length ∧
  ∀ i, i < points.val.length →
    (∃ v w, points.val[i]? = some v ∧ q.val[i]? = some w ∧ w.val.length = v.val.length) ∧
    pointAt q i = T (pointAt points i)

def IsPermutationOf (points q : Pts) (pi : Equiv.Perm (Fin points.val.length)) : Prop :=
  q.val.length = points.val.length ∧
  ∀ i : Fin points.val.length,
    (∃ v w, points.val[i.val]? = some v ∧ q.val[i.val]? = some w ∧ w.val.length = v.val.length) ∧
    pointAt q i.val = pointAt points (pi i).val

/-- Whenever the function returns a result r, r equals the number of ordered pairs (i,j) of indices with 0 <= i < n, 0 <= j < n, and i != j, such that all of: (1) points[i][0] <= points[j][0]; (2) points[i][1] >= points[j][1]; (3) for every k with 0 <= k < n, k != i, and k != j, it is not the case that points[i][0] <= points[k][0] <= points[j][0] and points[j][1] <= points[k][1] <= points[i][1]. Here (i,j) means Alice is at points[i] and Bob is at points[j].
  Preconditions: Let n = len(points). The input satisfies: 2 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2; for every i with 0 <= i < n, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9; and for all i,j with 0 <= i < j < n, points[i] != points[j] (equivalently, points[i][0] != points[j][0] or points[i][1] != points[j][1]). -/
theorem spec_1 (points : Pts) (h : ValidInput points) :
    ∀ r, number_of_pairs points = ok r → r.val = (pairCount points : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (points : Pts) (h : ValidInput points), ∀ r, number_of_pairs points = ok r → r.val = (pairCount points : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, i.e. no arithmetic overflow, out-of-bounds access, or panic occurs.
  Preconditions: Let n = len(points). The input satisfies: 2 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2; for every i with 0 <= i < n, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9; and for all i,j with 0 <= i < j < n, points[i] != points[j] (equivalently, points[i][0] != points[j][0] or points[i][1] != points[j][1]). -/
theorem spec_2 (points : Pts) (h : ValidInput points) :
    ∃ r, number_of_pairs points = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (points : Pts) (h : ValidInput points), ∃ r, number_of_pairs points = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= n*(n-1)/2, where n = len(points).
  Preconditions: Let n = len(points). The input satisfies: 2 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2; for every i with 0 <= i < n, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9; and for all i,j with 0 <= i < j < n, points[i] != points[j] (equivalently, points[i][0] != points[j][0] or points[i][1] != points[j][1]). -/
theorem spec_3 (points : Pts) (h : ValidInput points) :
    ∀ r, number_of_pairs points = ok r →
      r.val ≤ (((points.val.length * (points.val.length - 1)) / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (points : Pts) (h : ValidInput points), ∀ r, number_of_pairs points = ok r →
      r.val ≤ (((points.val.length * (points.val.length - 1)) / 2 : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: Let n = len(points). The input satisfies: 2 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2; for every i with 0 <= i < n, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9; for all i,j with 0 <= i < j < n, points[i] != points[j]; and additionally, for every i,j with 0 <= i < n, 0 <= j < n, and i != j, it is not the case that points[i][0] <= points[j][0] and points[i][1] >= points[j][1]. -/
theorem spec_4 (points : Pts) (h : ValidInput points)
    (hno : ∀ i j, i < points.val.length → j < points.val.length → i ≠ j →
      ¬ (coordX points i ≤ coordX points j ∧ coordY points j ≤ coordY points i)) :
    ∀ r, number_of_pairs points = ok r → r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (points : Pts) (h : ValidInput points)
    (hno : ∀ i j, i < points.val.length → j < points.val.length → i ≠ j →
      ¬ (coordX points i ≤ coordX points j ∧ coordY points j ≤ coordY points i)), ∀ r, number_of_pairs points = ok r → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = n - 1.
  Preconditions: Let n = len(points). The input satisfies: 2 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2; for every i with 0 <= i < n, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9; for all i,j with 0 <= i < j < n, points[i] != points[j]; and additionally, for all i,j with 0 <= i < n and 0 <= j < n, if points[i][0] < points[j][0] then points[i][1] >= points[j][1]. -/
theorem spec_5 (points : Pts) (h : ValidInput points)
    (hsorted : ∀ i j, i < points.val.length → j < points.val.length →
      coordX points i < coordX points j → coordY points j ≤ coordY points i) :
    ∀ r, number_of_pairs points = ok r → r.val = (points.val.length : ℤ) - 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (points : Pts) (h : ValidInput points)
    (hsorted : ∀ i j, i < points.val.length → j < points.val.length →
      coordX points i < coordX points j → coordY points j ≤ coordY points i), ∀ r, number_of_pairs points = ok r → r.val = (points.val.length : ℤ) - 1) := by
  sorry

/-- Whenever the function returns a result r on points, for every permutation pi of {0,...,n-1}, if q is the input defined by q[i] = points[pi(i)] for 0 <= i < n, then whenever the function returns a result r' on q, r' = r. Here q automatically satisfies the preconditions.
  Preconditions: Let n = len(points). The input satisfies: 2 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2; for every i with 0 <= i < n, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9; and for all i,j with 0 <= i < j < n, points[i] != points[j] (equivalently, points[i][0] != points[j][0] or points[i][1] != points[j][1]). -/
theorem spec_6 (points q : Pts) (h : ValidInput points)
    (pi : Equiv.Perm (Fin points.val.length)) (hq : IsPermutationOf points q pi) :
    ValidInput q ∧
      ∀ r r', number_of_pairs points = ok r → number_of_pairs q = ok r' → r' = r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (points q : Pts) (h : ValidInput points)
    (pi : Equiv.Perm (Fin points.val.length)) (hq : IsPermutationOf points q pi), ValidInput q ∧
      ∀ r r', number_of_pairs points = ok r → number_of_pairs q = ok r' → r' = r) := by
  sorry

/-- Whenever the function returns a result r on points, for any integers dx and dy, let q be defined by q[i][0] = points[i][0] + dx and q[i][1] = points[i][1] + dy for 0 <= i < n. If every q[i] has both coordinates in [-10^9,10^9] (so q also satisfies the preconditions), then whenever the function returns a result r' on q, r' = r.
  Preconditions: Let n = len(points). The input satisfies: 2 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2; for every i with 0 <= i < n, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9; and for all i,j with 0 <= i < j < n, points[i] != points[j] (equivalently, points[i][0] != points[j][0] or points[i][1] != points[j][1]). -/
theorem spec_7 (points q : Pts) (h : ValidInput points) (dx dy : ℤ)
    (hq : IsImage (fun p => (p.1 + dx, p.2 + dy)) points q)
    (hrange : ∀ i, i < q.val.length →
      -1000000000 ≤ coordX q i ∧ coordX q i ≤ 1000000000 ∧
      -1000000000 ≤ coordY q i ∧ coordY q i ≤ 1000000000) :
    ValidInput q ∧
      ∀ r r', number_of_pairs points = ok r → number_of_pairs q = ok r' → r' = r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (points q : Pts) (h : ValidInput points) (dx dy : ℤ)
    (hq : IsImage (fun p => (p.1 + dx, p.2 + dy)) points q)
    (hrange : ∀ i, i < q.val.length →
      -1000000000 ≤ coordX q i ∧ coordX q i ≤ 1000000000 ∧
      -1000000000 ≤ coordY q i ∧ coordY q i ≤ 1000000000), ValidInput q ∧
      ∀ r r', number_of_pairs points = ok r → number_of_pairs q = ok r' → r' = r) := by
  sorry

/-- Whenever the function returns a result r on points, let q be defined by q[i][0] = -points[i][0] and q[i][1] = -points[i][1] for 0 <= i < n. Then q satisfies the preconditions, and whenever the function returns a result r' on q, r' = r.
  Preconditions: Let n = len(points). The input satisfies: 2 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2; for every i with 0 <= i < n, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9; and for all i,j with 0 <= i < j < n, points[i] != points[j] (equivalently, points[i][0] != points[j][0] or points[i][1] != points[j][1]). -/
theorem spec_8 (points q : Pts) (h : ValidInput points)
    (hq : IsImage (fun p => (-p.1, -p.2)) points q) :
    ValidInput q ∧
      ∀ r r', number_of_pairs points = ok r → number_of_pairs q = ok r' → r' = r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (points q : Pts) (h : ValidInput points)
    (hq : IsImage (fun p => (-p.1, -p.2)) points q), ValidInput q ∧
      ∀ r r', number_of_pairs points = ok r → number_of_pairs q = ok r' → r' = r) := by
  sorry

/-- Whenever the function returns a result r on points, let q be defined by q[i][0] = points[i][1] and q[i][1] = points[i][0] for 0 <= i < n. Then q satisfies the preconditions, and whenever the function returns a result r' on q, r' = r.
  Preconditions: Let n = len(points). The input satisfies: 2 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2; for every i with 0 <= i < n, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9; and for all i,j with 0 <= i < j < n, points[i] != points[j] (equivalently, points[i][0] != points[j][0] or points[i][1] != points[j][1]). -/
theorem spec_9 (points q : Pts) (h : ValidInput points)
    (hq : IsImage (fun p => (p.2, p.1)) points q) :
    ValidInput q ∧
      ∀ r r', number_of_pairs points = ok r → number_of_pairs q = ok r' → r' = r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (points q : Pts) (h : ValidInput points)
    (hq : IsImage (fun p => (p.2, p.1)) points q), ValidInput q ∧
      ∀ r r', number_of_pairs points = ok r → number_of_pairs q = ok r' → r' = r) := by
  sorry

/-- Whenever the function returns a result r on points, let q be defined by q[i][0] = -points[i][1] and q[i][1] = -points[i][0] for 0 <= i < n. Then q satisfies the preconditions, and whenever the function returns a result r' on q, r' = r.
  Preconditions: Let n = len(points). The input satisfies: 2 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2; for every i with 0 <= i < n, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9; and for all i,j with 0 <= i < j < n, points[i] != points[j] (equivalently, points[i][0] != points[j][0] or points[i][1] != points[j][1]). -/
theorem spec_10 (points q : Pts) (h : ValidInput points)
    (hq : IsImage (fun p => (-p.2, -p.1)) points q) :
    ValidInput q ∧
      ∀ r r', number_of_pairs points = ok r → number_of_pairs q = ok r' → r' = r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (points q : Pts) (h : ValidInput points)
    (hq : IsImage (fun p => (-p.2, -p.1)) points q), ValidInput q ∧
      ∀ r r', number_of_pairs points = ok r → number_of_pairs q = ok r' → r' = r) := by
  sorry

/-- Whenever the function returns a result r on points, for any positive integer c, let q be defined by q[i][0] = c * points[i][0] and q[i][1] = c * points[i][1] for 0 <= i < n. If every q[i] has both coordinates in [-10^9,10^9] (so q also satisfies the preconditions), then whenever the function returns a result r' on q, r' = r.
  Preconditions: Let n = len(points). The input satisfies: 2 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2; for every i with 0 <= i < n, -10^9 <= points[i][0] <= 10^9 and -10^9 <= points[i][1] <= 10^9; and for all i,j with 0 <= i < j < n, points[i] != points[j] (equivalently, points[i][0] != points[j][0] or points[i][1] != points[j][1]). -/
theorem spec_11 (points q : Pts) (h : ValidInput points) (c : ℕ) (hc : 0 < c)
    (hq : IsImage (fun p => ((c : ℤ) * p.1, (c : ℤ) * p.2)) points q)
    (hrange : ∀ i, i < q.val.length →
      -1000000000 ≤ coordX q i ∧ coordX q i ≤ 1000000000 ∧
      -1000000000 ≤ coordY q i ∧ coordY q i ≤ 1000000000) :
    ValidInput q ∧
      ∀ r r', number_of_pairs points = ok r → number_of_pairs q = ok r' → r' = r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (points q : Pts) (h : ValidInput points) (c : ℕ) (hc : 0 < c)
    (hq : IsImage (fun p => ((c : ℤ) * p.1, (c : ℤ) * p.2)) points q)
    (hrange : ∀ i, i < q.val.length →
      -1000000000 ≤ coordX q i ∧ coordX q i ≤ 1000000000 ∧
      -1000000000 ≤ coordY q i ∧ coordY q i ≤ 1000000000), ValidInput q ∧
      ∀ r r', number_of_pairs points = ok r → number_of_pairs q = ok r' → r' = r) := by
  sorry

end AegisSpec.NumberOfPairs
