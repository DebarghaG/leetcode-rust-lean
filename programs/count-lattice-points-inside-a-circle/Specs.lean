import Aegis.CountLatticePoints.Code.Funs

/-!
# Specifications of `Aegis.CountLatticePoints.count_lattice_points`

LeetCode problem `count-lattice-points-inside-a-circle`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace AegisSpec.CountLatticePoints

open Aegis.CountLatticePoints

def rows (circles : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  circles.val.map (fun v => v.val.map (fun z => z.val))

def rowX (c : List Int) : Int := c.getD 0 0

def rowY (c : List Int) : Int := c.getD 1 0

def rowR (c : List Int) : Int := c.getD 2 0

def rowAt (cs : List (List Int)) (i : Nat) : List Int := cs[i]?.getD []

def xAt (cs : List (List Int)) (i : Nat) : Int := rowX (rowAt cs i)

def yAt (cs : List (List Int)) (i : Nat) : Int := rowY (rowAt cs i)

def rAt (cs : List (List Int)) (i : Nat) : Int := rowR (rowAt cs i)

def InCircle (c : List Int) (a b : Int) : Prop :=
  (a - rowX c) ^ 2 + (b - rowY c) ^ 2 ≤ (rowR c) ^ 2

def InSomeCircle (cs : List (List Int)) (a b : Int) : Prop :=
  ∃ i, i < cs.length ∧ InCircle (rowAt cs i) a b

noncomputable def countPoints (cs : List (List Int)) : Nat :=
  Nat.card {p : Int × Int // InSomeCircle cs p.1 p.2}

noncomputable def countPointsInCircle (c : List Int) : Nat :=
  Nat.card {p : Int × Int // InCircle c p.1 p.2}

def ValidRow (c : List Int) : Prop :=
  c.length = 3 ∧
    1 ≤ rowX c ∧ rowX c ≤ 100 ∧
      1 ≤ rowY c ∧ rowY c ≤ 100 ∧ 1 ≤ rowR c ∧ rowR c ≤ min (rowX c) (rowY c)

def ValidCircles (cs : List (List Int)) : Prop :=
  1 ≤ cs.length ∧ cs.length ≤ 200 ∧ ∀ i, i < cs.length → ValidRow (rowAt cs i)

def ValidInput (circles : Slice (alloc.vec.Vec Std.I64)) : Prop := ValidCircles (rows circles)

def perCircleLowerBound (c : List Int) : Int := 2 * rowR c ^ 2 + 2 * rowR c + 1

def maxPerCircleLowerBound (cs : List (List Int)) : Int :=
  cs.foldr (fun c m => max m (perCircleLowerBound c)) 0

/-- Whenever count_lattice_points returns a result r (i.e. evaluates to Result.ok r), r equals the number of distinct lattice points (a,b) in Z^2 for which there exists an index i with 0 <= i < len(circles) such that (a - x_i)^2 + (b - y_i)^2 <= r_i^2. Thus a point is counted if it lies inside or on the circumference of at least one circle, and a point lying inside several circles is counted only once.
  Preconditions: circles is a slice of vectors of 64-bit integers such that 1 <= len(circles) <= 200, and for every i with 0 <= i < len(circles), len(circles[i]) = 3. Write x_i = circles[i][0], y_i = circles[i][1], r_i = circles[i][2]. The constraints are 1 <= x_i <= 100, 1 <= y_i <= 100, and 1 <= r_i <= min(x_i, y_i). -/
theorem spec_1 (circles : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput circles) :
    ∀ r : Std.I64, count_lattice_points circles = ok r →
      r.val = (countPoints (rows circles) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (circles : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput circles), ∀ r : Std.I64, count_lattice_points circles = ok r →
      r.val = (countPoints (rows circles) : Int)) := by
  sorry

/-- For every input satisfying the preconditions, count_lattice_points returns a result: there exists a 64-bit integer r such that the function evaluates to Result.ok r. It does not panic, fail, or overflow on these inputs.
  Preconditions: The same problem constraints as in spec_1: 1 <= len(circles) <= 200, each len(circles[i]) = 3, and for every i, 1 <= x_i <= 100, 1 <= y_i <= 100, 1 <= r_i <= min(x_i, y_i). -/
theorem spec_2 (circles : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput circles) :
    ∃ r : Std.I64, count_lattice_points circles = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (circles : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput circles), ∃ r : Std.I64, count_lattice_points circles = ok r) := by
  sorry

/-- Whenever count_lattice_points returns Result.ok r, 0 <= r <= 201*201 = 40401. Moreover, every lattice point (a,b) that is counted lies in the square 0 <= a <= 200 and 0 <= b <= 200; hence r cannot exceed the 40401 lattice points in that square.
  Preconditions: circles is a slice of vectors of 64-bit integers such that 1 <= len(circles) <= 200, and for every i with 0 <= i < len(circles), len(circles[i]) = 3. Write x_i = circles[i][0], y_i = circles[i][1], r_i = circles[i][2]. The constraints are 1 <= x_i <= 100, 1 <= y_i <= 100, and 1 <= r_i <= min(x_i, y_i). -/
theorem spec_3 (circles : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput circles) :
    (∀ r : Std.I64, count_lattice_points circles = ok r → 0 ≤ r.val ∧ r.val ≤ 201 * 201) ∧
      ∀ a b : Int, InSomeCircle (rows circles) a b → 0 ≤ a ∧ a ≤ 200 ∧ 0 ≤ b ∧ b ≤ 200 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (circles : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput circles), (∀ r : Std.I64, count_lattice_points circles = ok r → 0 ≤ r.val ∧ r.val ≤ 201 * 201) ∧
      ∀ a b : Int, InSomeCircle (rows circles) a b → 0 ≤ a ∧ a ≤ 200 ∧ 0 ≤ b ∧ b ≤ 200) := by
  sorry

/-- Whenever count_lattice_points returns a result r, r >= max over all i with 0 <= i < len(circles) of (2*(circles[i][2])^2 + 2*circles[i][2] + 1).
  Preconditions: The same problem constraints as in spec_1. -/
theorem spec_4 (circles : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput circles) :
    ∀ r : Std.I64, count_lattice_points circles = ok r →
      maxPerCircleLowerBound (rows circles) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (circles : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput circles), ∀ r : Std.I64, count_lattice_points circles = ok r →
      maxPerCircleLowerBound (rows circles) ≤ r.val) := by
  sorry

/-- If count_lattice_points returns r on circles and returns r2 on circles2, then r = r2.
  Preconditions: circles is valid as in spec_1. circles2 is any permutation of the rows of circles; hence circles2 is also valid and has the same length. -/
theorem spec_5 (circles circles2 : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput circles)
    (hperm : (rows circles2).Perm (rows circles)) :
    ∀ r r2 : Std.I64, count_lattice_points circles = ok r →
      count_lattice_points circles2 = ok r2 → r = r2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (circles circles2 : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput circles)
    (hperm : (rows circles2).Perm (rows circles)), ∀ r r2 : Std.I64, count_lattice_points circles = ok r →
      count_lattice_points circles2 = ok r2 → r = r2) := by
  sorry

/-- If count_lattice_points returns r on circles and returns r2 on circles2, then r <= r2.
  Preconditions: circles is valid as in spec_1, and len(circles) < 200. Let d = [x,y,R] be a row satisfying 1 <= x <= 100, 1 <= y <= 100, and 1 <= R <= min(x,y). Let circles2 be obtained from circles by inserting d at any position. Then circles2 is also a valid input. -/
theorem spec_6 (circles circles2 : Slice (alloc.vec.Vec Std.I64)) (x y R : Int)
    (hvalid : ValidInput circles) (hlen : (rows circles).length < 200)
    (hx1 : 1 ≤ x) (hx2 : x ≤ 100) (hy1 : 1 ≤ y) (hy2 : y ≤ 100)
    (hR1 : 1 ≤ R) (hR2 : R ≤ min x y)
    (hins : ∃ i, i ≤ (rows circles).length ∧
      rows circles2 = (rows circles).take i ++ [[x, y, R]] ++ (rows circles).drop i) :
    ∀ r r2 : Std.I64, count_lattice_points circles = ok r →
      count_lattice_points circles2 = ok r2 → r.val ≤ r2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (circles circles2 : Slice (alloc.vec.Vec Std.I64)) (x y R : Int)
    (hvalid : ValidInput circles) (hlen : (rows circles).length < 200)
    (hx1 : 1 ≤ x) (hx2 : x ≤ 100) (hy1 : 1 ≤ y) (hy2 : y ≤ 100)
    (hR1 : 1 ≤ R) (hR2 : R ≤ min x y)
    (hins : ∃ i, i ≤ (rows circles).length ∧
      rows circles2 = (rows circles).take i ++ [[x, y, R]] ++ (rows circles).drop i), ∀ r r2 : Std.I64, count_lattice_points circles = ok r →
      count_lattice_points circles2 = ok r2 → r.val ≤ r2.val) := by
  sorry

/-- Whenever count_lattice_points returns r, let C_i be the number of lattice points (a,b) in Z^2 with (a - circles[i][0])^2 + (b - circles[i][1])^2 <= (circles[i][2])^2, for each i with 0 <= i < len(circles). Then r <= sum over i from 0 to len(circles)-1 of C_i.
  Preconditions: The same problem constraints as in spec_1. -/
theorem spec_7 (circles : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput circles) :
    ∀ r : Std.I64, count_lattice_points circles = ok r →
      r.val ≤ (((rows circles).map countPointsInCircle).sum : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (circles : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput circles), ∀ r : Std.I64, count_lattice_points circles = ok r →
      r.val ≤ (((rows circles).map countPointsInCircle).sum : Int)) := by
  sorry

/-- If count_lattice_points returns r_A on A, r_B on B, and r_C on C, then r_C = r_A + r_B.
  Preconditions: Let A and B be valid inputs as in spec_1 with len(A) + len(B) <= 200. Assume that no lattice point is inside at least one circle of A and also inside at least one circle of B: for every (a,b) in Z^2 there do not exist i < len(A) and j < len(B) with (a - A[i][0])^2 + (b - A[i][1])^2 <= A[i][2]^2 and (a - B[j][0])^2 + (b - B[j][1])^2 <= B[j][2]^2. Let C be the concatenation A ++ B, which is a valid input. -/
theorem spec_8 (A B C : Slice (alloc.vec.Vec Std.I64)) (hA : ValidInput A) (hB : ValidInput B)
    (hlen : (rows A).length + (rows B).length ≤ 200)
    (hdisj : ∀ a b : Int,
      ¬ ((∃ i, i < (rows A).length ∧ InCircle (rowAt (rows A) i) a b) ∧
          ∃ j, j < (rows B).length ∧ InCircle (rowAt (rows B) j) a b))
    (hC : rows C = rows A ++ rows B) :
    ∀ rA rB rC : Std.I64, count_lattice_points A = ok rA →
      count_lattice_points B = ok rB → count_lattice_points C = ok rC →
        rC.val = rA.val + rB.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (A B C : Slice (alloc.vec.Vec Std.I64)) (hA : ValidInput A) (hB : ValidInput B)
    (hlen : (rows A).length + (rows B).length ≤ 200)
    (hdisj : ∀ a b : Int,
      ¬ ((∃ i, i < (rows A).length ∧ InCircle (rowAt (rows A) i) a b) ∧
          ∃ j, j < (rows B).length ∧ InCircle (rowAt (rows B) j) a b))
    (hC : rows C = rows A ++ rows B), ∀ rA rB rC : Std.I64, count_lattice_points A = ok rA →
      count_lattice_points B = ok rB → count_lattice_points C = ok rC →
        rC.val = rA.val + rB.val) := by
  sorry

end AegisSpec.CountLatticePoints
