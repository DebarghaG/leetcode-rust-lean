import Aegis.MinimumLines.Code.Funs

/-!
# Specifications of `Aegis.MinimumLines.minimum_lines`

LeetCode problem `minimum-number-of-lines-to-cover-points`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumLines

abbrev Point := Int × Int

def Pt (v : alloc.vec.Vec I64) : Point :=
  (((v.val[0]?).map (fun x => x.val)).getD 0, ((v.val[1]?).map (fun x => x.val)).getD 0)

def BoundedPt (p : Point) : Prop :=
  -100 ≤ p.1 ∧ p.1 ≤ 100 ∧ -100 ≤ p.2 ∧ p.2 ≤ 100

def PtList (points : Slice (alloc.vec.Vec I64)) : List Point :=
  points.val.map Pt

def ceilDiv2 (n : Nat) : Nat :=
  (n + 1) / 2

structure StraightLine where

  a : ℚ

  b : ℚ

  c : ℚ

  nz : a ≠ 0 ∨ b ≠ 0

namespace StraightLine

def LiesOn (L : StraightLine) (p : Point) : Prop :=
  L.a * (p.1 : ℚ) + L.b * (p.2 : ℚ) + L.c = 0

end StraightLine

def Collinear (ps : List Point) : Prop :=
  ∃ L : StraightLine, ∀ p ∈ ps, L.LiesOn p

noncomputable def numOn (L : StraightLine) (ps : List Point) : Nat := by
  classical
  exact (ps.filter (fun p => L.LiesOn p)).length

def Covers (Ls : List StraightLine) (ps : List Point) : Prop :=
  ∀ p ∈ ps, ∃ L ∈ Ls, L.LiesOn p

def CoverableBy (k : Nat) (ps : List Point) : Prop :=
  ∃ Ls : List StraightLine, Ls.length = k ∧ Covers Ls ps

def IsMinLineCover (ps : List Point) (r : Int) : Prop :=
  0 ≤ r ∧ CoverableBy r.toNat ps ∧ ∀ k : Nat, (k : Int) < r → ¬ CoverableBy k ps

def PartitionIntoCollinear (k : Nat) (ps : List Point) : Prop :=
  ∃ blocks : List (List Point),
    blocks.length = k ∧ (∀ B ∈ blocks, B ≠ [] ∧ Collinear B) ∧ ps.Perm blocks.flatten

def IsLeastCollinearPartition (ps : List Point) (r : Int) : Prop :=
  0 ≤ r ∧ PartitionIntoCollinear r.toNat ps ∧
    ∀ k : Nat, PartitionIntoCollinear k ps → r ≤ (k : Int)

/-- The function returns a result r and, interpreting r as an integer, 0 <= r, and r is the minimum number of straight lines needed to cover all points. Precisely: there exist r straight lines L_1,...,L_r such that for every i with 0 <= i < len(points), the point (points[i][0], points[i][1]) lies on at least one L_t; and for every integer k with 0 <= k < r, there do not exist k straight lines covering all points. A straight line means a set of points (x,y) satisfying a*x + b*y + c = 0 for some real numbers a,b,c with (a,b) not equal to (0,0).
  Preconditions: len(points) is an integer with 1 <= len(points) <= 10; for every i with 0 <= i < len(points), len(points[i]) = 2; for every i with 0 <= i < len(points), -100 <= points[i][0] <= 100 and -100 <= points[i][1] <= 100; for every i and j with 0 <= i < j < len(points), (points[i][0], points[i][1]) is not equal to (points[j][0], points[j][1]). -/
theorem spec_1 (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)) :
    ∃ r : I64, Aegis.MinimumLines.minimum_lines points = ok r ∧
      IsMinLineCover (PtList points) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)), ∃ r : I64, Aegis.MinimumLines.minimum_lines points = ok r ∧
      IsMinLineCover (PtList points) r.val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not overflow, panic, or otherwise fail, so the integer value of r is defined.
  Preconditions: len(points) is an integer with 1 <= len(points) <= 10; for every i with 0 <= i < len(points), len(points[i]) = 2; for every i with 0 <= i < len(points), -100 <= points[i][0] <= 100 and -100 <= points[i][1] <= 100; for every i and j with 0 <= i < j < len(points), (points[i][0], points[i][1]) is not equal to (points[j][0], points[j][1]). -/
theorem spec_2 (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)) :
    ∃ r : I64, Aegis.MinimumLines.minimum_lines points = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)), ∃ r : I64, Aegis.MinimumLines.minimum_lines points = ok r) := by
  sorry

/-- Whenever the function returns a result r, interpreting r as an integer, r >= 1.
  Preconditions: len(points) is an integer with 1 <= len(points) <= 10; for every i with 0 <= i < len(points), len(points[i]) = 2; for every i with 0 <= i < len(points), -100 <= points[i][0] <= 100 and -100 <= points[i][1] <= 100; for every i and j with 0 <= i < j < len(points), (points[i][0], points[i][1]) is not equal to (points[j][0], points[j][1]). -/
theorem spec_3 (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)) :
    ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r → 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)), ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, interpreting r as an integer, r <= ceil(len(points)/2), where ceil is the smallest integer greater than or equal to its argument.
  Preconditions: len(points) is an integer with 1 <= len(points) <= 10; for every i with 0 <= i < len(points), len(points[i]) = 2; for every i with 0 <= i < len(points), -100 <= points[i][0] <= 100 and -100 <= points[i][1] <= 100; for every i and j with 0 <= i < j < len(points), (points[i][0], points[i][1]) is not equal to (points[j][0], points[j][1]). -/
theorem spec_4 (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)) :
    ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r →
      r.val ≤ (ceilDiv2 points.val.length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)), ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r →
      r.val ≤ (ceilDiv2 points.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, interpreting r as an integer, r = 1 if and only if there exists a straight line L such that every point lies on L: for every i with 0 <= i < len(points), (points[i][0], points[i][1]) lies on L.
  Preconditions: len(points) is an integer with 1 <= len(points) <= 10; for every i with 0 <= i < len(points), len(points[i]) = 2; for every i with 0 <= i < len(points), -100 <= points[i][0] <= 100 and -100 <= points[i][1] <= 100; for every i and j with 0 <= i < j < len(points), (points[i][0], points[i][1]) is not equal to (points[j][0], points[j][1]). -/
theorem spec_5 (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)) :
    ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r →
      (r.val = 1 ↔ Collinear (PtList points)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)), ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r →
      (r.val = 1 ↔ Collinear (PtList points))) := by
  sorry

/-- Whenever the function returns a result r, interpreting r as an integer, there exist r straight lines L_1,...,L_r such that for every i with 0 <= i < len(points), the point (points[i][0], points[i][1]) lies on at least one L_t.
  Preconditions: len(points) is an integer with 1 <= len(points) <= 10; for every i with 0 <= i < len(points), len(points[i]) = 2; for every i with 0 <= i < len(points), -100 <= points[i][0] <= 100 and -100 <= points[i][1] <= 100; for every i and j with 0 <= i < j < len(points), (points[i][0], points[i][1]) is not equal to (points[j][0], points[j][1]). -/
theorem spec_6 (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)) :
    ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r →
      0 ≤ r.val ∧ ∃ Ls : List StraightLine, Ls.length = r.val.toNat ∧
        Covers Ls (PtList points) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)), ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r →
      0 ≤ r.val ∧ ∃ Ls : List StraightLine, Ls.length = r.val.toNat ∧
        Covers Ls (PtList points)) := by
  sorry

/-- Whenever the function returns a result r, interpreting r as an integer, for every integer k with 0 <= k < r, there do not exist k straight lines L_1,...,L_k such that every point lies on at least one of them.
  Preconditions: len(points) is an integer with 1 <= len(points) <= 10; for every i with 0 <= i < len(points), len(points[i]) = 2; for every i with 0 <= i < len(points), -100 <= points[i][0] <= 100 and -100 <= points[i][1] <= 100; for every i and j with 0 <= i < j < len(points), (points[i][0], points[i][1]) is not equal to (points[j][0], points[j][1]). -/
theorem spec_7 (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)) :
    ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r →
      ∀ k : Nat, (k : Int) < r.val → ¬ CoverableBy k (PtList points) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)), ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r →
      ∀ k : Nat, (k : Int) < r.val → ¬ CoverableBy k (PtList points)) := by
  sorry

/-- Whenever the function returns a result r, interpreting r as an integer, r = ceil(len(points)/2), where ceil is the smallest integer greater than or equal to its argument.
  Preconditions: len(points) is an integer with 1 <= len(points) <= 10; for every i with 0 <= i < len(points), len(points[i]) = 2; for every i with 0 <= i < len(points), -100 <= points[i][0] <= 100 and -100 <= points[i][1] <= 100; for every i and j with 0 <= i < j < len(points), (points[i][0], points[i][1]) is not equal to (points[j][0], points[j][1]); for every i, j, k with 0 <= i < j < k < len(points), the three points (points[i][0], points[i][1]), (points[j][0], points[j][1]), (points[k][0], points[k][1]) are not collinear (no straight line contains all three). -/
theorem spec_8 (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j))
    (hgeneral : ∀ i j k : Fin points.val.length, i < j → j < k →
      ¬ Collinear [Pt (points.val.get i), Pt (points.val.get j), Pt (points.val.get k)]) :
    ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r →
      r.val = (ceilDiv2 points.val.length : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j))
    (hgeneral : ∀ i j k : Fin points.val.length, i < j → j < k →
      ¬ Collinear [Pt (points.val.get i), Pt (points.val.get j), Pt (points.val.get k)]), ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r →
      r.val = (ceilDiv2 points.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, interpreting r as an integer, r = 2.
  Preconditions: len(points) is an integer with 3 <= len(points) <= 10; for every i with 0 <= i < len(points), len(points[i]) = 2; for every i with 0 <= i < len(points), -100 <= points[i][0] <= 100 and -100 <= points[i][1] <= 100; for every i and j with 0 <= i < j < len(points), (points[i][0], points[i][1]) is not equal to (points[j][0], points[j][1]); there exists a straight line L such that exactly len(points)-1 of the points lie on L and at least one point does not lie on L. -/
theorem spec_9 (points : Slice (alloc.vec.Vec I64))
    (hlen : 3 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j))
    (hline : ∃ L : StraightLine,
      numOn L (PtList points) = (PtList points).length - 1 ∧
      ∃ p ∈ PtList points, ¬ L.LiesOn p) :
    ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r → r.val = 2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64))
    (hlen : 3 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j))
    (hline : ∃ L : StraightLine,
      numOn L (PtList points) = (PtList points).length - 1 ∧
      ∃ p ∈ PtList points, ¬ L.LiesOn p), ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r → r.val = 2) := by
  sorry

/-- Let r be the result returned by the function on points and r' be the result returned by the function on points'. Whenever both calls return results, interpreting r and r' as integers, r = r'.
  Preconditions: Both points and points' satisfy: len is between 1 and 10 inclusive; every element has length 2; every coordinate is between -100 and 100 inclusive; all points are distinct. Additionally, points' is a permutation of points: len(points') = len(points) and there is a bijection p from {0,...,len(points)-1} to {0,...,len(points')-1} such that for every i, (points'[p(i)][0], points'[p(i)][1]) = (points[i][0], points[i][1]). -/
theorem spec_10 (points points' : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j))
    (hlen' : 1 ≤ points'.val.length ∧ points'.val.length ≤ 10)
    (hshape' : ∀ i : Fin points'.val.length, (points'.val.get i).val.length = 2)
    (hrange' : ∀ i : Fin points'.val.length, BoundedPt (Pt (points'.val.get i)))
    (hdistinct' : ∀ i j : Fin points'.val.length, i < j →
      Pt (points'.val.get i) ≠ Pt (points'.val.get j))
    (hperm : ∃ e : Fin points.val.length ≃ Fin points'.val.length,
      ∀ i : Fin points.val.length, Pt (points'.val.get (e i)) = Pt (points.val.get i)) :
    ∀ r r' : I64, Aegis.MinimumLines.minimum_lines points = ok r →
      Aegis.MinimumLines.minimum_lines points' = ok r' → r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (points points' : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j))
    (hlen' : 1 ≤ points'.val.length ∧ points'.val.length ≤ 10)
    (hshape' : ∀ i : Fin points'.val.length, (points'.val.get i).val.length = 2)
    (hrange' : ∀ i : Fin points'.val.length, BoundedPt (Pt (points'.val.get i)))
    (hdistinct' : ∀ i j : Fin points'.val.length, i < j →
      Pt (points'.val.get i) ≠ Pt (points'.val.get j))
    (hperm : ∃ e : Fin points.val.length ≃ Fin points'.val.length,
      ∀ i : Fin points.val.length, Pt (points'.val.get (e i)) = Pt (points.val.get i)), ∀ r r' : I64, Aegis.MinimumLines.minimum_lines points = ok r →
      Aegis.MinimumLines.minimum_lines points' = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, interpreting r as an integer, r is the least integer k such that the set of all points can be partitioned into k nonempty subsets, each of which is collinear (each subset is contained in some straight line).
  Preconditions: len(points) is an integer with 1 <= len(points) <= 10; for every i with 0 <= i < len(points), len(points[i]) = 2; for every i with 0 <= i < len(points), -100 <= points[i][0] <= 100 and -100 <= points[i][1] <= 100; for every i and j with 0 <= i < j < len(points), (points[i][0], points[i][1]) is not equal to (points[j][0], points[j][1]). -/
theorem spec_11 (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)) :
    ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r →
      IsLeastCollinearPartition (PtList points) r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)), ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r →
      IsLeastCollinearPartition (PtList points) r.val) := by
  sorry

/-- Whenever the function returns a result r, interpreting r as an integer, if r = 2 then there exists a straight line L such that at least ceil(len(points)/2) of the points lie on L, where ceil is the smallest integer greater than or equal to its argument.
  Preconditions: len(points) is an integer with 1 <= len(points) <= 10; for every i with 0 <= i < len(points), len(points[i]) = 2; for every i with 0 <= i < len(points), -100 <= points[i][0] <= 100 and -100 <= points[i][1] <= 100; for every i and j with 0 <= i < j < len(points), (points[i][0], points[i][1]) is not equal to (points[j][0], points[j][1]). -/
theorem spec_12 (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)) :
    ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r → r.val = 2 →
      ∃ L : StraightLine, ceilDiv2 points.val.length ≤ numOn L (PtList points) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)), ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r → r.val = 2 →
      ∃ L : StraightLine, ceilDiv2 points.val.length ≤ numOn L (PtList points)) := by
  sorry

/-- Whenever the function returns a result r, interpreting r as an integer, for every integer m with 1 <= m <= len(points) such that some straight line contains exactly m of the points, r <= 1 + ceil((len(points)-m)/2), where ceil is the smallest integer greater than or equal to its argument.
  Preconditions: len(points) is an integer with 1 <= len(points) <= 10; for every i with 0 <= i < len(points), len(points[i]) = 2; for every i with 0 <= i < len(points), -100 <= points[i][0] <= 100 and -100 <= points[i][1] <= 100; for every i and j with 0 <= i < j < len(points), (points[i][0], points[i][1]) is not equal to (points[j][0], points[j][1]). -/
theorem spec_13 (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)) :
    ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r →
      ∀ m : Nat, 1 ≤ m → m ≤ points.val.length →
        (∃ L : StraightLine, numOn L (PtList points) = m) →
        r.val ≤ 1 + (ceilDiv2 (points.val.length - m) : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec I64))
    (hlen : 1 ≤ points.val.length ∧ points.val.length ≤ 10)
    (hshape : ∀ i : Fin points.val.length, (points.val.get i).val.length = 2)
    (hrange : ∀ i : Fin points.val.length, BoundedPt (Pt (points.val.get i)))
    (hdistinct : ∀ i j : Fin points.val.length, i < j →
      Pt (points.val.get i) ≠ Pt (points.val.get j)), ∀ r : I64, Aegis.MinimumLines.minimum_lines points = ok r →
      ∀ m : Nat, 1 ≤ m → m ≤ points.val.length →
        (∃ L : StraightLine, numOn L (PtList points) = m) →
        r.val ≤ 1 + (ceilDiv2 (points.val.length - m) : Int)) := by
  sorry

end AegisSpec.MinimumLines
