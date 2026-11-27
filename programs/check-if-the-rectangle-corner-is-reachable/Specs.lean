import Aegis.CanReachCorner.Code.Funs
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.UniformSpace.Real

/-!
# Specifications of `Aegis.CanReachCorner.can_reach_corner`

LeetCode problem `check-if-the-rectangle-corner-is-reachable`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CanReachCorner

structure Circle where

  x : ℤ

  y : ℤ

  r : ℤ
deriving DecidableEq, Repr

def coord (v : alloc.vec.Vec Std.I64) (k : Nat) : ℤ :=
  match v.val[k]? with
  | some c => c.val
  | none => 0

def toCircle (v : alloc.vec.Vec Std.I64) : Circle :=
  ⟨coord v 0, coord v 1, coord v 2⟩

def toCircles (circles : Slice (alloc.vec.Vec Std.I64)) : List Circle :=
  circles.val.map toCircle

def circleAt (circles : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Circle :=
  match circles.val[i]? with
  | some v => toCircle v
  | none => ⟨0, 0, 0⟩

def Circle.Bounded (c : Circle) : Prop :=
  1 ≤ c.x ∧ c.x ≤ 1000000000 ∧ 1 ≤ c.y ∧ c.y ≤ 1000000000 ∧ 1 ≤ c.r ∧ c.r ≤ 1000000000

def EntryOK (v : alloc.vec.Vec Std.I64) : Prop :=
  v.val.length = 3 ∧ (toCircle v).Bounded

def Circle.touchesBottom (c : Circle) (X : ℤ) : Prop :=
  (c.x ≤ X ∧ c.y ≤ c.r) ∨ (X < c.x ∧ (c.x - X) ^ 2 + c.y ^ 2 ≤ c.r ^ 2)

def Circle.touchesRight (c : Circle) (X Y : ℤ) : Prop :=
  (c.y ≤ Y ∧ |c.x - X| ≤ c.r) ∨ (Y < c.y ∧ (c.x - X) ^ 2 + (c.y - Y) ^ 2 ≤ c.r ^ 2)

def Circle.touchesLeft (c : Circle) (Y : ℤ) : Prop :=
  (c.y ≤ Y ∧ c.x ≤ c.r) ∨ (Y < c.y ∧ c.x ^ 2 + (c.y - Y) ^ 2 ≤ c.r ^ 2)

def Circle.touchesTop (c : Circle) (X Y : ℤ) : Prop :=
  (c.x ≤ X ∧ |c.y - Y| ≤ c.r) ∨ (X < c.x ∧ (c.x - X) ^ 2 + (c.y - Y) ^ 2 ≤ c.r ^ 2)

def MeetsA (X Y : ℤ) (c : Circle) : Prop := c.touchesBottom X ∨ c.touchesRight X Y

def MeetsB (X Y : ℤ) (c : Circle) : Prop := c.touchesLeft Y ∨ c.touchesTop X Y

def MissesRect (X Y : ℤ) (c : Circle) : Prop :=
  (max (c.x - X) 0) ^ 2 + (max (c.y - Y) 0) ^ 2 > c.r ^ 2

def adjacent (c₁ c₂ : Circle) : Prop :=
  (c₁.x - c₂.x) ^ 2 + (c₁.y - c₂.y) ^ 2 ≤ (c₁.r + c₂.r) ^ 2

def Adj (circles : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Prop :=
  adjacent (circleAt circles i) (circleAt circles j)

def Reachable (circles : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Prop :=
  Relation.ReflTransGen (Adj circles) i j

def IsEscapingPath (X Y : ℤ) (cs : List Circle) (γ : ℝ → ℝ × ℝ) : Prop :=
  Continuous γ ∧
    γ 0 = (0, 0) ∧
    γ 1 = ((X : ℝ), (Y : ℝ)) ∧
    (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      (γ t).1 ∈ Set.Icc (0 : ℝ) (X : ℝ) ∧ (γ t).2 ∈ Set.Icc (0 : ℝ) (Y : ℝ)) ∧
    (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ c ∈ cs,
      ((γ t).1 - (c.x : ℝ)) ^ 2 + ((γ t).2 - (c.y : ℝ)) ^ 2 > (c.r : ℝ) ^ 2) ∧
    (∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
      (γ t).1 ∈ Set.Ioo (0 : ℝ) (X : ℝ) ∧ (γ t).2 ∈ Set.Ioo (0 : ℝ) (Y : ℝ))

def HasEscapingPath (X Y : ℤ) (cs : List Circle) : Prop :=
  ∃ γ : ℝ → ℝ × ℝ, IsEscapingPath X Y cs γ

/-- Let X = xCorner and Y = yCorner. For each i, let (xi, yi, ri) = (circles[i][0], circles[i][1], circles[i][2]). Define the following predicates for a circle c = (x,y,r): touches_bottom(c) := (x <= X and y <= r) or (x > X and (x-X)^2 + y^2 <= r^2); touches_right(c) := (y <= Y and |x - X| <= r) or (y > Y and (x-X)^2 + (y-Y)^2 <= r^2); touches_left(c) := (y <= Y and x <= r) or (y > Y and x^2 + (y-Y)^2 <= r^2); touches_top(c) := (x <= X and |y - Y| <= r) or (x > X and (x-X)^2 + (y-Y)^2 <= r^2). Define circles i and j to be adjacent if (xi-xj)^2 + (yi-yj)^2 <= (ri+rj)^2. Let a component be a connected component of the graph on {0,...,n-1} with these edges. The function returns false if and only if there exists a component C such that (there exists i in C with touches_bottom(circles[i]) or touches_right(circles[i])) and (there exists j in C with touches_left(circles[j]) or touches_top(circles[j])). Otherwise, it returns true.
  Preconditions: xCorner and yCorner are integers with 3 <= xCorner, yCorner <= 10^9. circles is a slice of length n with 1 <= n <= 1000. Each circles[i] is a vector of length 3 with entries xi, yi, ri such that 1 <= xi, yi, ri <= 10^9. -/
theorem spec_1 (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v) :
    ∃ r, Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok r ∧
      (r = false ↔
        ∃ i j : Nat, i < n ∧ j < n ∧ Reachable circles i j ∧
          MeetsA xCorner.val yCorner.val (circleAt circles i) ∧
          MeetsB xCorner.val yCorner.val (circleAt circles j)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v), ∃ r, Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok r ∧
      (r = false ↔
        ∃ i j : Nat, i < n ∧ j < n ∧ Reachable circles i j ∧
          MeetsA xCorner.val yCorner.val (circleAt circles i) ∧
          MeetsB xCorner.val yCorner.val (circleAt circles j))) := by
  sorry

/-- The function returns a result (i.e., it does not return an error or panic) for every input satisfying the preconditions.
  Preconditions: xCorner and yCorner are integers with 3 <= xCorner, yCorner <= 10^9. circles is a slice of length n with 1 <= n <= 1000. Each circles[i] is a vector of length 3 with entries xi, yi, ri such that 1 <= xi, yi, ri <= 10^9. -/
theorem spec_2 (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v) :
    ∃ r, Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v), ∃ r, Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok r) := by
  sorry

/-- If there exists an index i such that xi^2 + yi^2 <= ri^2, then the function returns false.
  Preconditions: xCorner and yCorner are integers with 3 <= xCorner, yCorner <= 10^9. circles is a slice of length n with 1 <= n <= 1000. Each circles[i] is a vector of length 3 with entries xi, yi, ri such that 1 <= xi, yi, ri <= 10^9. -/
theorem spec_3 (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v)
    (h : ∃ i : Nat, i < n ∧
      (circleAt circles i).x ^ 2 + (circleAt circles i).y ^ 2 ≤ (circleAt circles i).r ^ 2) :
    Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v)
    (h : ∃ i : Nat, i < n ∧
      (circleAt circles i).x ^ 2 + (circleAt circles i).y ^ 2 ≤ (circleAt circles i).r ^ 2), Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok false) := by
  sorry

/-- If there exists an index i such that (xi - xCorner)^2 + (yi - yCorner)^2 <= ri^2, then the function returns false.
  Preconditions: xCorner and yCorner are integers with 3 <= xCorner, yCorner <= 10^9. circles is a slice of length n with 1 <= n <= 1000. Each circles[i] is a vector of length 3 with entries xi, yi, ri such that 1 <= xi, yi, ri <= 10^9. -/
theorem spec_4 (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v)
    (h : ∃ i : Nat, i < n ∧
      ((circleAt circles i).x - xCorner.val) ^ 2 + ((circleAt circles i).y - yCorner.val) ^ 2 ≤
        (circleAt circles i).r ^ 2) :
    Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok false := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v)
    (h : ∃ i : Nat, i < n ∧
      ((circleAt circles i).x - xCorner.val) ^ 2 + ((circleAt circles i).y - yCorner.val) ^ 2 ≤
        (circleAt circles i).r ^ 2), Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok false) := by
  sorry

/-- If can_reach_corner(xCorner, yCorner, circles1) returns false, then can_reach_corner(xCorner, yCorner, circles2) returns false.
  Preconditions: xCorner and yCorner are integers with 3 <= xCorner, yCorner <= 10^9. circles1 and circles2 are slices of lengths n1, n2 with 1 <= n1, n2 <= 1000. Each entry satisfies the circle constraints 1 <= xi, yi, ri <= 10^9, and circles2 is obtained from circles1 by adding zero or more circles (as a multiset). -/
theorem spec_5 (xCorner yCorner : Std.I64)
    (circles1 circles2 : Slice (alloc.vec.Vec Std.I64)) (n1 n2 : Nat)
    (hn1 : circles1.val.length = n1) (hn1_pos : 1 ≤ n1) (hn1_le : n1 ≤ 1000)
    (hn2 : circles2.val.length = n2) (hn2_pos : 1 ≤ n2) (hn2_le : n2 ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries1 : ∀ v ∈ circles1.val, EntryOK v)
    (hentries2 : ∀ v ∈ circles2.val, EntryOK v)
    (hadd : ∃ extra : List Circle, List.Perm (toCircles circles1 ++ extra) (toCircles circles2)) :
    Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles1 = ok false →
      Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles2 = ok false := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (xCorner yCorner : Std.I64)
    (circles1 circles2 : Slice (alloc.vec.Vec Std.I64)) (n1 n2 : Nat)
    (hn1 : circles1.val.length = n1) (hn1_pos : 1 ≤ n1) (hn1_le : n1 ≤ 1000)
    (hn2 : circles2.val.length = n2) (hn2_pos : 1 ≤ n2) (hn2_le : n2 ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries1 : ∀ v ∈ circles1.val, EntryOK v)
    (hentries2 : ∀ v ∈ circles2.val, EntryOK v)
    (hadd : ∃ extra : List Circle, List.Perm (toCircles circles1 ++ extra) (toCircles circles2)), Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles1 = ok false →
      Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles2 = ok false) := by
  sorry

/-- If for every i, (max(xi - xCorner, 0))^2 + (max(yi - yCorner, 0))^2 > ri^2, then the function returns true.
  Preconditions: xCorner and yCorner are integers with 3 <= xCorner, yCorner <= 10^9. circles is a slice of length n with 1 <= n <= 1000. Each circles[i] is a vector of length 3 with entries xi, yi, ri such that 1 <= xi, yi, ri <= 10^9. -/
theorem spec_6 (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v)
    (h : ∀ i : Nat, i < n → MissesRect xCorner.val yCorner.val (circleAt circles i)) :
    Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok true := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v)
    (h : ∀ i : Nat, i < n → MissesRect xCorner.val yCorner.val (circleAt circles i)), Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok true) := by
  sorry

/-- If for every i, circle i does not intersect A = bottom ∪ right (i.e., neither touches_bottom nor touches_right holds as defined in spec_1), then the function returns true.
  Preconditions: xCorner and yCorner are integers with 3 <= xCorner, yCorner <= 10^9. circles is a slice of length n with 1 <= n <= 1000. Each circles[i] is a vector of length 3 with entries xi, yi, ri such that 1 <= xi, yi, ri <= 10^9. -/
theorem spec_7 (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v)
    (h : ∀ i : Nat, i < n → ¬ MeetsA xCorner.val yCorner.val (circleAt circles i)) :
    Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok true := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v)
    (h : ∀ i : Nat, i < n → ¬ MeetsA xCorner.val yCorner.val (circleAt circles i)), Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok true) := by
  sorry

/-- If for every i, circle i does not intersect B = left ∪ top (i.e., neither touches_left nor touches_top holds as defined in spec_1), then the function returns true.
  Preconditions: xCorner and yCorner are integers with 3 <= xCorner, yCorner <= 10^9. circles is a slice of length n with 1 <= n <= 1000. Each circles[i] is a vector of length 3 with entries xi, yi, ri such that 1 <= xi, yi, ri <= 10^9. -/
theorem spec_8 (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v)
    (h : ∀ i : Nat, i < n → ¬ MeetsB xCorner.val yCorner.val (circleAt circles i)) :
    Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok true := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v)
    (h : ∀ i : Nat, i < n → ¬ MeetsB xCorner.val yCorner.val (circleAt circles i)), Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok true) := by
  sorry

/-- If the function returns true, then there exists a continuous path γ: [0,1] -> R^2 such that γ(0) = (0,0), γ(1) = (xCorner,yCorner), for all t in [0,1], γ(t) lies in the rectangle [0,xCorner]×[0,yCorner], for all t in [0,1] and all i, the distance from γ(t) to (xi,yi) is strictly greater than ri, and for all t in (0,1), γ(t) lies in the open rectangle (0,xCorner)×(0,yCorner).
  Preconditions: xCorner and yCorner are integers with 3 <= xCorner, yCorner <= 10^9. circles is a slice of length n with 1 <= n <= 1000. Each circles[i] is a vector of length 3 with entries xi, yi, ri such that 1 <= xi, yi, ri <= 10^9. -/
theorem spec_9 (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v) :
    Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok true →
      HasEscapingPath xCorner.val yCorner.val (toCircles circles) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v), Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok true →
      HasEscapingPath xCorner.val yCorner.val (toCircles circles)) := by
  sorry

/-- If the function returns false, then there does not exist a continuous path γ: [0,1] -> R^2 satisfying the conditions in spec_9.
  Preconditions: xCorner and yCorner are integers with 3 <= xCorner, yCorner <= 10^9. circles is a slice of length n with 1 <= n <= 1000. Each circles[i] is a vector of length 3 with entries xi, yi, ri such that 1 <= xi, yi, ri <= 10^9. -/
theorem spec_10 (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v) :
    Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok false →
      ¬ HasEscapingPath xCorner.val yCorner.val (toCircles circles) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v), Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok false →
      ¬ HasEscapingPath xCorner.val yCorner.val (toCircles circles)) := by
  sorry

/-- For any permutation of the entries of circles, the function returns the same result.
  Preconditions: xCorner and yCorner are integers with 3 <= xCorner, yCorner <= 10^9. circles is a slice of length n with 1 <= n <= 1000. Each circles[i] is a vector of length 3 with entries xi, yi, ri such that 1 <= xi, yi, ri <= 10^9. -/
theorem spec_11 (xCorner yCorner : Std.I64)
    (circles circles' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v)
    (hentries' : ∀ v ∈ circles'.val, EntryOK v)
    (hperm : List.Perm (toCircles circles) (toCircles circles')) :
    ∀ r r', Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok r →
      Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles' = ok r' → r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (xCorner yCorner : Std.I64)
    (circles circles' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v)
    (hentries' : ∀ v ∈ circles'.val, EntryOK v)
    (hperm : List.Perm (toCircles circles) (toCircles circles')), ∀ r r', Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok r →
      Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles' = ok r' → r = r') := by
  sorry

/-- If there exists a sequence of indices i1, i2, ..., ik such that circle i1 intersects A = bottom ∪ right, circle ik intersects B = left ∪ top, and for each 1 <= t < k, the closed disks of circles i_t and i_{t+1} intersect (i.e., (xi_t - xi_{t+1})^2 + (yi_t - yi_{t+1})^2 <= (ri_t + ri_{t+1})^2), then the function returns false.
  Preconditions: xCorner and yCorner are integers with 3 <= xCorner, yCorner <= 10^9. circles is a slice of length n with 1 <= n <= 1000. Each circles[i] is a vector of length 3 with entries xi, yi, ri such that 1 <= xi, yi, ri <= 10^9. -/
theorem spec_12 (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v)
    (h : ∃ i j : Nat, i < n ∧ j < n ∧ Reachable circles i j ∧
      MeetsA xCorner.val yCorner.val (circleAt circles i) ∧
      MeetsB xCorner.val yCorner.val (circleAt circles j)) :
    Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok false := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (xCorner yCorner : Std.I64) (circles : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v)
    (h : ∃ i j : Nat, i < n ∧ j < n ∧ Reachable circles i j ∧
      MeetsA xCorner.val yCorner.val (circleAt circles i) ∧
      MeetsB xCorner.val yCorner.val (circleAt circles j)), Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok false) := by
  sorry

/-- can_reach_corner(xCorner, yCorner, circles) = can_reach_corner(yCorner, xCorner, circles').
  Preconditions: xCorner and yCorner are integers with 3 <= xCorner, yCorner <= 10^9. circles is a slice of length n with 1 <= n <= 1000. Each circles[i] = [xi, yi, ri] has 1 <= xi, yi, ri <= 10^9. Let circles' be the slice with circles'[i] = [yi, xi, ri]. -/
theorem spec_13 (xCorner yCorner : Std.I64)
    (circles circles' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v)
    (hentries' : ∀ v ∈ circles'.val, EntryOK v)
    (hswap : toCircles circles' = (toCircles circles).map (fun c => ⟨c.y, c.x, c.r⟩)) :
    ∀ r, (Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok r) ↔
      (Aegis.CanReachCorner.can_reach_corner yCorner xCorner circles' = ok r) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (xCorner yCorner : Std.I64)
    (circles circles' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : circles.val.length = n) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v)
    (hentries' : ∀ v ∈ circles'.val, EntryOK v)
    (hswap : toCircles circles' = (toCircles circles).map (fun c => ⟨c.y, c.x, c.r⟩)), ∀ r, (Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok r) ↔
      (Aegis.CanReachCorner.can_reach_corner yCorner xCorner circles' = ok r)) := by
  sorry

/-- can_reach_corner(xCorner, yCorner, circles) = can_reach_corner(xCorner, yCorner, circles').
  Preconditions: xCorner and yCorner are integers with 3 <= xCorner, yCorner <= 10^9. circles is a slice of length n with 2 <= n <= 1000. Each circles[i] = [xi, yi, ri] has 1 <= xi, yi, ri <= 10^9. There is an index i such that (max(xi - xCorner, 0))^2 + (max(yi - yCorner, 0))^2 > ri^2, so the closed disk of circle i does not meet the rectangle. Let circles' be circles with entry i removed. -/
theorem spec_14 (xCorner yCorner : Std.I64)
    (circles circles' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : circles.val.length = n) (hn_pos : 2 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v)
    (hentries' : ∀ v ∈ circles'.val, EntryOK v)
    (i : Nat) (hi : i < n)
    (hmiss : MissesRect xCorner.val yCorner.val (circleAt circles i))
    (hdel : toCircles circles' = (toCircles circles).eraseIdx i) :
    ∀ r, (Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok r) ↔
      (Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles' = ok r) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (xCorner yCorner : Std.I64)
    (circles circles' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : circles.val.length = n) (hn_pos : 2 ≤ n) (hn_le : n ≤ 1000)
    (hx_lo : (3 : ℤ) ≤ xCorner.val) (hx_hi : xCorner.val ≤ 1000000000)
    (hy_lo : (3 : ℤ) ≤ yCorner.val) (hy_hi : yCorner.val ≤ 1000000000)
    (hentries : ∀ v ∈ circles.val, EntryOK v)
    (hentries' : ∀ v ∈ circles'.val, EntryOK v)
    (i : Nat) (hi : i < n)
    (hmiss : MissesRect xCorner.val yCorner.val (circleAt circles i))
    (hdel : toCircles circles' = (toCircles circles).eraseIdx i), ∀ r, (Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles = ok r) ↔
      (Aegis.CanReachCorner.can_reach_corner xCorner yCorner circles' = ok r)) := by
  sorry

end AegisSpec.CanReachCorner
