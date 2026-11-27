import Aegis.IsConvex.Code.Funs
import Mathlib.Basic.Real.Basic

/-!
# Specifications of `Aegis.IsConvex.is_convex`

LeetCode problem `convex-polygon`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsConvex

def vecToPoint? (v : alloc.vec.Vec Std.I64) : Option (Int × Int) :=
  match v.val with
  | [a, b] => some (a.val, b.val)
  | _ => none

def coords (points : Slice (alloc.vec.Vec Std.I64)) : Option (List (Int × Int)) :=
  points.val.mapM vecToPoint?

def HasCoords (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int)) : Prop :=
  coords points = some ps

def ptAt (ps : List (Int × Int)) (i : Nat) : Int × Int := ps.getD i (0, 0)

theorem mapM_vecToPoint?_length :
    ∀ (l : List (alloc.vec.Vec Std.I64)) (ps : List (Int × Int)),
      l.mapM vecToPoint? = some ps → ps.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro ps h
    simp [List.mapM_nil] at h
    subst h
    rfl
  | cons a rest ih =>
    intro ps h
    rw [List.mapM_cons] at h
    cases hf : vecToPoint? a with
    | none =>
      rw [hf] at h
      simp at h
    | some p =>
      cases hs : rest.mapM vecToPoint? with
      | none =>
        rw [hf, hs] at h
        simp at h
      | some ps' =>
        rw [hf, hs] at h
        simp at h
        rw [← h]
        simp [ih ps' hs]

theorem HasCoords.length (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (h : HasCoords points ps) : ps.length = points.val.length :=
  mapM_vecToPoint?_length points.val ps h

def xAt (ps : List (Int × Int)) (i : Nat) : Int := (ptAt ps i).1

def yAt (ps : List (Int × Int)) (i : Nat) : Int := (ptAt ps i).2

def crossAt (ps : List (Int × Int)) (i : Nat) : Int :=
  (xAt ps ((i + 1) % ps.length) - xAt ps (i % ps.length))
      * (yAt ps ((i + 2) % ps.length) - yAt ps (i % ps.length))
    - (yAt ps ((i + 1) % ps.length) - yAt ps (i % ps.length))
      * (xAt ps ((i + 2) % ps.length) - xAt ps (i % ps.length))

def AllNonneg (ps : List (Int × Int)) : Prop := ∀ i, i < ps.length → 0 ≤ crossAt ps i

def AllNonpos (ps : List (Int × Int)) : Prop := ∀ i, i < ps.length → crossAt ps i ≤ 0

def HasMixedSign (ps : List (Int × Int)) : Prop :=
  ∃ i j, i < ps.length ∧ j < ps.length ∧ 0 < crossAt ps i ∧ crossAt ps j < 0

def InBounds (ps : List (Int × Int)) : Prop :=
  ∀ i, i < ps.length →
    -(10 ^ 4 : Int) ≤ xAt ps i ∧ xAt ps i ≤ 10 ^ 4 ∧
      -(10 ^ 4 : Int) ≤ yAt ps i ∧ yAt ps i ≤ 10 ^ 4

def PairwiseDistinct (ps : List (Int × Int)) : Prop :=
  ∀ i j, i < ps.length → j < ps.length → i ≠ j → ptAt ps i ≠ ptAt ps j

def Pre (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int)) : Prop :=
  HasCoords points ps ∧ 3 ≤ ps.length ∧ ps.length ≤ 10 ^ 4 ∧ InBounds ps ∧
    PairwiseDistinct ps

/-- Whenever is_convex(points) returns a result r, r = true if and only if either (for every i with 0 <= i < n, cross(i) >= 0) or (for every i with 0 <= i < n, cross(i) <= 0). Equivalently, r = false if and only if there exist i and j with 0 <= i, j < n such that cross(i) > 0 and cross(j) < 0.
  Preconditions: Let n = len(points). Assume 3 <= n <= 10^4. For every i with 0 <= i < n, points[i] has length 2; write points[i] = [x_i, y_i]. Assume -10^4 <= x_i <= 10^4 and -10^4 <= y_i <= 10^4. Assume the points are pairwise distinct: for all i != j, (x_i, y_i) != (x_j, y_j). For 0 <= i < n, all subscripts in the definition of cross(i) are taken modulo n, and cross(i) = (x_{i+1} - x_i) * (y_{i+2} - y_i) - (y_{i+1} - y_i) * (x_{i+2} - x_i). -/
theorem spec_1 (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) :
    ∀ r : Bool, Aegis.IsConvex.is_convex points = ok r →
      ((r = true ↔ (AllNonneg ps ∨ AllNonpos ps)) ∧
        (r = false ↔ HasMixedSign ps)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps), ∀ r : Bool, Aegis.IsConvex.is_convex points = ok r →
      ((r = true ↔ (AllNonneg ps ∨ AllNonpos ps)) ∧
        (r = false ↔ HasMixedSign ps))) := by
  sorry

/-- For every input satisfying the precondition, is_convex(points) returns a result r (either true or false); it does not fail.
  Preconditions: Assume the precondition of spec_1, including the definition of cross(i). -/
theorem spec_2 (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) :
    ∃ r : Bool, Aegis.IsConvex.is_convex points = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps), ∃ r : Bool, Aegis.IsConvex.is_convex points = ok r) := by
  sorry

/-- For every such input, is_convex(points) returns true.
  Preconditions: Assume the precondition of spec_1 and additionally n = 3. -/
theorem spec_3 (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) (hn : ps.length = 3) :
    Aegis.IsConvex.is_convex points = ok true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) (hn : ps.length = 3), Aegis.IsConvex.is_convex points = ok true) := by
  sorry

/-- If there exist i and j with 0 <= i, j < n such that cross(i) > 0 and cross(j) < 0, then is_convex(points) returns false.
  Preconditions: Assume the precondition of spec_1, including the definition of cross(i). -/
theorem spec_4 (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) (hmixed : HasMixedSign ps) :
    Aegis.IsConvex.is_convex points = ok false := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) (hmixed : HasMixedSign ps), Aegis.IsConvex.is_convex points = ok false) := by
  sorry

/-- If cross(i) >= 0 for every i with 0 <= i < n, then is_convex(points) returns true.
  Preconditions: Assume the precondition of spec_1, including the definition of cross(i). -/
theorem spec_5 (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) (hall : AllNonneg ps) :
    Aegis.IsConvex.is_convex points = ok true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) (hall : AllNonneg ps), Aegis.IsConvex.is_convex points = ok true) := by
  sorry

/-- If cross(i) <= 0 for every i with 0 <= i < n, then is_convex(points) returns true.
  Preconditions: Assume the precondition of spec_1, including the definition of cross(i). -/
theorem spec_6 (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) (hall : AllNonpos ps) :
    Aegis.IsConvex.is_convex points = ok true := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) (hall : AllNonpos ps), Aegis.IsConvex.is_convex points = ok true) := by
  sorry

/-- Whenever is_convex(points) returns false, there exist i and j with 0 <= i, j < n such that cross(i) > 0 and cross(j) < 0.
  Preconditions: Assume the precondition of spec_1, including the definition of cross(i). -/
theorem spec_7 (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) :
    ∀ r : Bool, Aegis.IsConvex.is_convex points = ok r → r = false → HasMixedSign ps := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps), ∀ r : Bool, Aegis.IsConvex.is_convex points = ok r → r = false → HasMixedSign ps) := by
  sorry

/-- For every k with 0 <= k < n, is_convex(points) and is_convex(rotated) both return a Boolean result, and the two returned Booleans are equal.
  Preconditions: Assume the precondition of spec_1. For an integer k with 0 <= k < n, define rotated[i] = points[(i+k) mod n] for 0 <= i < n; this is a slice of length n whose entries are the same Vec<i64> points in cyclic order. -/
theorem spec_8 (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) :
    ∀ (k : Nat) (rotated : Slice (alloc.vec.Vec Std.I64)),
      k < ps.length → rotated.val = points.val.rotate k →
      ∃ (r₁ r₂ : Bool),
        Aegis.IsConvex.is_convex points = ok r₁ ∧
          Aegis.IsConvex.is_convex rotated = ok r₂ ∧ r₁ = r₂ := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps), ∀ (k : Nat) (rotated : Slice (alloc.vec.Vec Std.I64)),
      k < ps.length → rotated.val = points.val.rotate k →
      ∃ (r₁ r₂ : Bool),
        Aegis.IsConvex.is_convex points = ok r₁ ∧
          Aegis.IsConvex.is_convex rotated = ok r₂ ∧ r₁ = r₂) := by
  sorry

/-- is_convex(points) and is_convex(reversed) both return a Boolean result, and the two returned Booleans are equal.
  Preconditions: Assume the precondition of spec_1. Define reversed[i] = points[n-1-i] for 0 <= i < n. -/
theorem spec_9 (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) :
    ∀ reversed : Slice (alloc.vec.Vec Std.I64),
      reversed.val = points.val.reverse →
      ∃ (r₁ r₂ : Bool),
        Aegis.IsConvex.is_convex points = ok r₁ ∧
          Aegis.IsConvex.is_convex reversed = ok r₂ ∧ r₁ = r₂ := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps), ∀ reversed : Slice (alloc.vec.Vec Std.I64),
      reversed.val = points.val.reverse →
      ∃ (r₁ r₂ : Bool),
        Aegis.IsConvex.is_convex points = ok r₁ ∧
          Aegis.IsConvex.is_convex reversed = ok r₂ ∧ r₁ = r₂) := by
  sorry

/-- is_convex(points) and is_convex(translated) both return a Boolean result, and the two returned Booleans are equal.
  Preconditions: Assume the precondition of spec_1. Let a and b be integers such that for every i with 0 <= i < n, the point (x_i + a, y_i + b) has coordinates in [-10^4, 10^4]. Define translated[i] = [x_i + a, y_i + b] for 0 <= i < n. -/
theorem spec_10 (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) (a b : Int)
    (hbounds : InBounds (ps.map fun p => (p.1 + a, p.2 + b))) :
    ∀ translated : Slice (alloc.vec.Vec Std.I64),
      HasCoords translated (ps.map fun p => (p.1 + a, p.2 + b)) →
      ∃ (r₁ r₂ : Bool),
        Aegis.IsConvex.is_convex points = ok r₁ ∧
          Aegis.IsConvex.is_convex translated = ok r₂ ∧ r₁ = r₂ := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) (a b : Int)
    (hbounds : InBounds (ps.map fun p => (p.1 + a, p.2 + b))), ∀ translated : Slice (alloc.vec.Vec Std.I64),
      HasCoords translated (ps.map fun p => (p.1 + a, p.2 + b)) →
      ∃ (r₁ r₂ : Bool),
        Aegis.IsConvex.is_convex points = ok r₁ ∧
          Aegis.IsConvex.is_convex translated = ok r₂ ∧ r₁ = r₂) := by
  sorry

/-- is_convex(points) and is_convex(scaled) both return a Boolean result, and the two returned Booleans are equal.
  Preconditions: Assume the precondition of spec_1. Let c be a positive integer such that for every i with 0 <= i < n, the point (c*x_i, c*y_i) has coordinates in [-10^4, 10^4]. Define scaled[i] = [c*x_i, c*y_i] for 0 <= i < n. -/
theorem spec_11 (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) (c : Int) (hc : 0 < c)
    (hbounds : InBounds (ps.map fun p => (c * p.1, c * p.2))) :
    ∀ scaled : Slice (alloc.vec.Vec Std.I64),
      HasCoords scaled (ps.map fun p => (c * p.1, c * p.2)) →
      ∃ (r₁ r₂ : Bool),
        Aegis.IsConvex.is_convex points = ok r₁ ∧
          Aegis.IsConvex.is_convex scaled = ok r₂ ∧ r₁ = r₂ := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) (c : Int) (hc : 0 < c)
    (hbounds : InBounds (ps.map fun p => (c * p.1, c * p.2))), ∀ scaled : Slice (alloc.vec.Vec Std.I64),
      HasCoords scaled (ps.map fun p => (c * p.1, c * p.2)) →
      ∃ (r₁ r₂ : Bool),
        Aegis.IsConvex.is_convex points = ok r₁ ∧
          Aegis.IsConvex.is_convex scaled = ok r₂ ∧ r₁ = r₂) := by
  sorry

/-- is_convex(points) and is_convex(points') both return a Boolean result, and the two returned Booleans are equal.
  Preconditions: Assume the precondition of spec_1, including the definition of cross(i), and n < 10^4. Let i be an integer with 0 <= i < n. Let q = [x, y] be an integer point such that q is not equal to any points[j], q has coordinates in [-10^4, 10^4], and q lies strictly between points[i] and points[(i+1) mod n]: there exists a real t with 0 < t < 1 such that x = (1-t)*x_i + t*x_{i+1} and y = (1-t)*y_i + t*y_{i+1}, where the subscript i+1 is taken modulo n. Define points' to be the slice obtained by inserting q immediately after position i in points; thus len(points') = n+1 <= 10^4. -/
theorem spec_12 (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) (hnlt : ps.length < 10 ^ 4) (i : Nat) (hi : i < ps.length)
    (q : Int × Int)
    (hq_not_mem : ∀ j, j < ps.length → q ≠ ptAt ps j)
    (hq_bounds : -(10 ^ 4 : Int) ≤ q.1 ∧ q.1 ≤ 10 ^ 4 ∧
      -(10 ^ 4 : Int) ≤ q.2 ∧ q.2 ≤ 10 ^ 4)
    (hq_between : ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      (q.1 : ℝ) = (1 - t) * (xAt ps i : ℝ) + t * (xAt ps ((i + 1) % ps.length) : ℝ) ∧
      (q.2 : ℝ) = (1 - t) * (yAt ps i : ℝ) + t * (yAt ps ((i + 1) % ps.length) : ℝ)) :
    ∀ points' : Slice (alloc.vec.Vec Std.I64),
      HasCoords points' (ps.take (i + 1) ++ (q :: ps.drop (i + 1))) →
      ∃ (r₁ r₂ : Bool),
        Aegis.IsConvex.is_convex points = ok r₁ ∧
          Aegis.IsConvex.is_convex points' = ok r₂ ∧ r₁ = r₂ := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) (hnlt : ps.length < 10 ^ 4) (i : Nat) (hi : i < ps.length)
    (q : Int × Int)
    (hq_not_mem : ∀ j, j < ps.length → q ≠ ptAt ps j)
    (hq_bounds : -(10 ^ 4 : Int) ≤ q.1 ∧ q.1 ≤ 10 ^ 4 ∧
      -(10 ^ 4 : Int) ≤ q.2 ∧ q.2 ≤ 10 ^ 4)
    (hq_between : ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      (q.1 : ℝ) = (1 - t) * (xAt ps i : ℝ) + t * (xAt ps ((i + 1) % ps.length) : ℝ) ∧
      (q.2 : ℝ) = (1 - t) * (yAt ps i : ℝ) + t * (yAt ps ((i + 1) % ps.length) : ℝ)), ∀ points' : Slice (alloc.vec.Vec Std.I64),
      HasCoords points' (ps.take (i + 1) ++ (q :: ps.drop (i + 1))) →
      ∃ (r₁ r₂ : Bool),
        Aegis.IsConvex.is_convex points = ok r₁ ∧
          Aegis.IsConvex.is_convex points' = ok r₂ ∧ r₁ = r₂) := by
  sorry

/-- is_convex(points) and is_convex(transformed) both return a Boolean result, and the two returned Booleans are equal.
  Preconditions: Assume the precondition of spec_1. Let a, b, c, d, e, f be integers such that a*d - b*c != 0. For each i, let x'_i = a*x_i + b*y_i + e and y'_i = c*x_i + d*y_i + f, and assume -10^4 <= x'_i <= 10^4 and -10^4 <= y'_i <= 10^4. Define transformed[i] = [x'_i, y'_i] for 0 <= i < n. -/
theorem spec_13 (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) (a b c d e f : Int) (hdet : a * d - b * c ≠ 0)
    (hbounds : InBounds (ps.map fun p => (a * p.1 + b * p.2 + e, c * p.1 + d * p.2 + f))) :
    ∀ transformed : Slice (alloc.vec.Vec Std.I64),
      HasCoords transformed (ps.map fun p => (a * p.1 + b * p.2 + e, c * p.1 + d * p.2 + f)) →
      ∃ (r₁ r₂ : Bool),
        Aegis.IsConvex.is_convex points = ok r₁ ∧
          Aegis.IsConvex.is_convex transformed = ok r₂ ∧ r₁ = r₂ := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) (a b c d e f : Int) (hdet : a * d - b * c ≠ 0)
    (hbounds : InBounds (ps.map fun p => (a * p.1 + b * p.2 + e, c * p.1 + d * p.2 + f))), ∀ transformed : Slice (alloc.vec.Vec Std.I64),
      HasCoords transformed (ps.map fun p => (a * p.1 + b * p.2 + e, c * p.1 + d * p.2 + f)) →
      ∃ (r₁ r₂ : Bool),
        Aegis.IsConvex.is_convex points = ok r₁ ∧
          Aegis.IsConvex.is_convex transformed = ok r₂ ∧ r₁ = r₂) := by
  sorry

/-- is_convex(points) and is_convex(removed) both return a Boolean result, and the two returned Booleans are equal.
  Preconditions: Assume the precondition of spec_1 and n > 3. Let i be an integer with 0 <= i < n such that cross(i-1) = 0 and points[i] lies strictly between points[(i-1) mod n] and points[(i+1) mod n]: there exists a real t with 0 < t < 1 such that x_i = (1-t)*x_{i-1} + t*x_{i+1} and y_i = (1-t)*y_{i-1} + t*y_{i+1}, where subscripts are taken modulo n. Define removed to be the slice obtained by deleting position i from points; thus len(removed) = n-1. -/
theorem spec_14 (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) (hn : 3 < ps.length) (i : Nat) (hi : i < ps.length)
    (hcross_zero : crossAt ps ((i + ps.length - 1) % ps.length) = 0)
    (hbetween : ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      (xAt ps i : ℝ)
        = (1 - t) * (xAt ps ((i + ps.length - 1) % ps.length) : ℝ)
            + t * (xAt ps ((i + 1) % ps.length) : ℝ) ∧
      (yAt ps i : ℝ)
        = (1 - t) * (yAt ps ((i + ps.length - 1) % ps.length) : ℝ)
            + t * (yAt ps ((i + 1) % ps.length) : ℝ)) :
    ∀ removed : Slice (alloc.vec.Vec Std.I64),
      HasCoords removed (ps.take i ++ ps.drop (i + 1)) →
      ∃ (r₁ r₂ : Bool),
        Aegis.IsConvex.is_convex points = ok r₁ ∧
          Aegis.IsConvex.is_convex removed = ok r₂ ∧ r₁ = r₂ := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64)) (ps : List (Int × Int))
    (hpre : Pre points ps) (hn : 3 < ps.length) (i : Nat) (hi : i < ps.length)
    (hcross_zero : crossAt ps ((i + ps.length - 1) % ps.length) = 0)
    (hbetween : ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      (xAt ps i : ℝ)
        = (1 - t) * (xAt ps ((i + ps.length - 1) % ps.length) : ℝ)
            + t * (xAt ps ((i + 1) % ps.length) : ℝ) ∧
      (yAt ps i : ℝ)
        = (1 - t) * (yAt ps ((i + ps.length - 1) % ps.length) : ℝ)
            + t * (yAt ps ((i + 1) % ps.length) : ℝ)), ∀ removed : Slice (alloc.vec.Vec Std.I64),
      HasCoords removed (ps.take i ++ ps.drop (i + 1)) →
      ∃ (r₁ r₂ : Bool),
        Aegis.IsConvex.is_convex points = ok r₁ ∧
          Aegis.IsConvex.is_convex removed = ok r₂ ∧ r₁ = r₂) := by
  sorry

end AegisSpec.IsConvex
