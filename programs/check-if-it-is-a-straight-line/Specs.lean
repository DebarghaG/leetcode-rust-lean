import Aegis.CheckStraightLine.Code.Funs

/-!
# Specifications of `Aegis.CheckStraightLine.check_straight_line`

LeetCode problem `check-if-it-is-a-straight-line`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CheckStraightLine

  open Aegis.CheckStraightLine

  def pts (coordinates : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    coordinates.val.map (fun v => v.val.map (fun z => z.val))

  def px (coordinates : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    ((pts coordinates).getD i []).getD 0 0

  def py (coordinates : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    ((pts coordinates).getD i []).getD 1 0

  def D (coordinates : Slice (alloc.vec.Vec Std.I64)) (i j k : ℕ) : ℤ :=
    (px coordinates j - px coordinates i) * (py coordinates k - py coordinates i) -
      (py coordinates j - py coordinates i) * (px coordinates k - px coordinates i)

  def Dshift (coordinates : Slice (alloc.vec.Vec Std.I64)) (u v : ℤ) (i j k : ℕ) : ℤ :=
    ((px coordinates j + u) - (px coordinates i + u)) *
        ((py coordinates k + v) - (py coordinates i + v)) -
      ((py coordinates j + v) - (py coordinates i + v)) *
        ((px coordinates k + u) - (px coordinates i + u))

  def Dswap (coordinates : Slice (alloc.vec.Vec Std.I64)) (i j k : ℕ) : ℤ :=
    (py coordinates j - py coordinates i) * (px coordinates k - px coordinates i) -
      (px coordinates j - px coordinates i) * (py coordinates k - py coordinates i)

  def Collinear (coordinates : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ i j k : ℕ, i < j → j < k → k < coordinates.val.length → D coordinates i j k = 0

  def CollinearShift (coordinates : Slice (alloc.vec.Vec Std.I64)) (u v : ℤ) : Prop :=
    ∀ i j k : ℕ, i < j → j < k → k < coordinates.val.length →
      Dshift coordinates u v i j k = 0

  def CollinearSwap (coordinates : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ i j k : ℕ, i < j → j < k → k < coordinates.val.length →
      Dswap coordinates i j k = 0

  structure Pre (coordinates : Slice (alloc.vec.Vec Std.I64)) : Prop where

    len_ge_two : 2 ≤ coordinates.val.length

    len_le_thousand : coordinates.val.length ≤ 1000

    dims : ∀ i, i < coordinates.val.length → ((pts coordinates).getD i []).length = 2

    x_bounds : ∀ i, i < coordinates.val.length →
      -10000 ≤ px coordinates i ∧ px coordinates i ≤ 10000

    y_bounds : ∀ i, i < coordinates.val.length →
      -10000 ≤ py coordinates i ∧ py coordinates i ≤ 10000

    distinct : ∀ i j, i < j → j < coordinates.val.length →
      ¬ (px coordinates i = px coordinates j ∧ py coordinates i = py coordinates j)

  /-- Let n = len(coordinates). For 0 <= i < n let x_i = coordinates[i][0] and y_i = coordinates[i][1], interpreted as mathematical integers. For 0 <= i,j,k < n define D(i,j,k) = (x_j - x_i)*(y_k - y_i) - (y_j - y_i)*(x_k - x_i). Whenever the function returns a result r, r = true if and only if for every i,j,k with 0 <= i < j < k < n, D(i,j,k) = 0. When n = 2 this condition is vacuous and r must be true.
    Preconditions: 2 <= len(coordinates) <= 1000; for every i with 0 <= i < len(coordinates), len(coordinates[i]) = 2, -10000 <= coordinates[i][0] <= 10000, and -10000 <= coordinates[i][1] <= 10000; for every i,j with 0 <= i < j < len(coordinates), not (coordinates[i][0] = coordinates[j][0] and coordinates[i][1] = coordinates[j][1]). -/
  theorem spec_1 (coordinates : Slice (alloc.vec.Vec Std.I64)) (h : Pre coordinates) :
      ∀ r : Bool, check_straight_line coordinates = ok r →
        (r = true ↔ Collinear coordinates) ∧ (coordinates.val.length = 2 → r = true) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (coordinates : Slice (alloc.vec.Vec Std.I64)) (h : Pre coordinates), ∀ r : Bool, check_straight_line coordinates = ok r →
          (r = true ↔ Collinear coordinates) ∧ (coordinates.val.length = 2 → r = true)) := by
    sorry

  /-- Under the preconditions, the function returns a result r (some Bool); in particular it does not fail by overflow, out-of-bounds indexing, or panic.
    Preconditions: 2 <= len(coordinates) <= 1000; for every i with 0 <= i < len(coordinates), len(coordinates[i]) = 2, -10000 <= coordinates[i][0] <= 10000, and -10000 <= coordinates[i][1] <= 10000; for every i,j with 0 <= i < j < len(coordinates), not (coordinates[i][0] = coordinates[j][0] and coordinates[i][1] = coordinates[j][1]). -/
  theorem spec_2 (coordinates : Slice (alloc.vec.Vec Std.I64)) (h : Pre coordinates) :
      ∃ r : Bool, check_straight_line coordinates = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (coordinates : Slice (alloc.vec.Vec Std.I64)) (h : Pre coordinates), ∃ r : Bool, check_straight_line coordinates = ok r) := by
    sorry

  /-- Let n = len(coordinates). For 0 <= i < n let x_i = coordinates[i][0] and y_i = coordinates[i][1]. Define D(i,j,k) = (x_j - x_i)*(y_k - y_i) - (y_j - y_i)*(x_k - x_i). Whenever the function returns a result r, if r = false then there exist indices i,j,k with 0 <= i < j < k < n such that D(i,j,k) != 0.
    Preconditions: 2 <= len(coordinates) <= 1000; for every i with 0 <= i < len(coordinates), len(coordinates[i]) = 2, -10000 <= coordinates[i][0] <= 10000, and -10000 <= coordinates[i][1] <= 10000; for every i,j with 0 <= i < j < len(coordinates), not (coordinates[i][0] = coordinates[j][0] and coordinates[i][1] = coordinates[j][1]). -/
  theorem spec_3 (coordinates : Slice (alloc.vec.Vec Std.I64)) (h : Pre coordinates) :
      ∀ r : Bool, check_straight_line coordinates = ok r → r = false →
        ∃ i j k : ℕ, i < j ∧ j < k ∧ k < coordinates.val.length ∧
          D coordinates i j k ≠ 0 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (coordinates : Slice (alloc.vec.Vec Std.I64)) (h : Pre coordinates), ∀ r : Bool, check_straight_line coordinates = ok r → r = false →
          ∃ i j k : ℕ, i < j ∧ j < k ∧ k < coordinates.val.length ∧
            D coordinates i j k ≠ 0) := by
    sorry

  /-- Let n = len(coordinates). For 0 <= i < n let x_i = coordinates[i][0] and y_i = coordinates[i][1]. Whenever the function returns a result r, if r = true then for every i with 0 <= i < n, (x_i - x_0)*(y_1 - y_0) = (y_i - y_0)*(x_1 - x_0).
    Preconditions: 2 <= len(coordinates) <= 1000; for every i with 0 <= i < len(coordinates), len(coordinates[i]) = 2, -10000 <= coordinates[i][0] <= 10000, and -10000 <= coordinates[i][1] <= 10000; for every i,j with 0 <= i < j < len(coordinates), not (coordinates[i][0] = coordinates[j][0] and coordinates[i][1] = coordinates[j][1]). -/
  theorem spec_4 (coordinates : Slice (alloc.vec.Vec Std.I64)) (h : Pre coordinates) :
      ∀ r : Bool, check_straight_line coordinates = ok r → r = true →
        ∀ i : ℕ, i < coordinates.val.length →
          (px coordinates i - px coordinates 0) * (py coordinates 1 - py coordinates 0) =
            (py coordinates i - py coordinates 0) * (px coordinates 1 - px coordinates 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (coordinates : Slice (alloc.vec.Vec Std.I64)) (h : Pre coordinates), ∀ r : Bool, check_straight_line coordinates = ok r → r = true →
          ∀ i : ℕ, i < coordinates.val.length →
            (px coordinates i - px coordinates 0) * (py coordinates 1 - py coordinates 0) =
              (py coordinates i - py coordinates 0) * (px coordinates 1 - px coordinates 0)) := by
    sorry

  /-- Let n = len(coordinates). For 0 <= i < n let x_i = coordinates[i][0] and y_i = coordinates[i][1]. Whenever the function returns a result r, if r = false then n >= 3 and there exists an index i with 2 <= i < n such that (x_i - x_0)*(y_1 - y_0) != (y_i - y_0)*(x_1 - x_0).
    Preconditions: 2 <= len(coordinates) <= 1000; for every i with 0 <= i < len(coordinates), len(coordinates[i]) = 2, -10000 <= coordinates[i][0] <= 10000, and -10000 <= coordinates[i][1] <= 10000; for every i,j with 0 <= i < j < len(coordinates), not (coordinates[i][0] = coordinates[j][0] and coordinates[i][1] = coordinates[j][1]). -/
  theorem spec_5 (coordinates : Slice (alloc.vec.Vec Std.I64)) (h : Pre coordinates) :
      ∀ r : Bool, check_straight_line coordinates = ok r → r = false →
        3 ≤ coordinates.val.length ∧
          ∃ i : ℕ, 2 ≤ i ∧ i < coordinates.val.length ∧
            (px coordinates i - px coordinates 0) * (py coordinates 1 - py coordinates 0) ≠
              (py coordinates i - py coordinates 0) * (px coordinates 1 - px coordinates 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (coordinates : Slice (alloc.vec.Vec Std.I64)) (h : Pre coordinates), ∀ r : Bool, check_straight_line coordinates = ok r → r = false →
          3 ≤ coordinates.val.length ∧
            ∃ i : ℕ, 2 ≤ i ∧ i < coordinates.val.length ∧
              (px coordinates i - px coordinates 0) * (py coordinates 1 - py coordinates 0) ≠
                (py coordinates i - py coordinates 0) * (px coordinates 1 - px coordinates 0)) := by
    sorry

  /-- Let n = len(coordinates). For 0 <= i < n let x_i = coordinates[i][0] and y_i = coordinates[i][1]. Define D(i,j,k) = (x_j - x_i)*(y_k - y_i) - (y_j - y_i)*(x_k - x_i). Whenever the function returns a result r, for every permutation pi of {0,...,n-1}, r = true if and only if for every a,b,c with 0 <= a < b < c < n, D(pi(a), pi(b), pi(c)) = 0.
    Preconditions: 2 <= len(coordinates) <= 1000; for every i with 0 <= i < len(coordinates), len(coordinates[i]) = 2, -10000 <= coordinates[i][0] <= 10000, and -10000 <= coordinates[i][1] <= 10000; for every i,j with 0 <= i < j < len(coordinates), not (coordinates[i][0] = coordinates[j][0] and coordinates[i][1] = coordinates[j][1]). -/
  theorem spec_6 (coordinates : Slice (alloc.vec.Vec Std.I64)) (h : Pre coordinates) :
      ∀ r : Bool, check_straight_line coordinates = ok r →
        ∀ π : Equiv.Perm (Fin coordinates.val.length),
          (r = true ↔
            ∀ a b c : Fin coordinates.val.length, a < b → b < c →
              D coordinates (π a) (π b) (π c) = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (coordinates : Slice (alloc.vec.Vec Std.I64)) (h : Pre coordinates), ∀ r : Bool, check_straight_line coordinates = ok r →
          ∀ π : Equiv.Perm (Fin coordinates.val.length),
            (r = true ↔
              ∀ a b c : Fin coordinates.val.length, a < b → b < c →
                D coordinates (π a) (π b) (π c) = 0)) := by
    sorry

  /-- Let n = len(coordinates). For 0 <= i < n let x_i = coordinates[i][0] and y_i = coordinates[i][1]. Whenever the function returns a result r, for every pair of integers (u,v) such that -10000 <= x_i + u <= 10000 and -10000 <= y_i + v <= 10000 for all i with 0 <= i < n, r = true if and only if the translated points (x_i + u, y_i + v) are collinear, i.e., for every 0 <= i < j < k < n, ((x_j + u) - (x_i + u))*((y_k + v) - (y_i + v)) - ((y_j + v) - (y_i + v))*((x_k + u) - (x_i + u)) = 0.
    Preconditions: 2 <= len(coordinates) <= 1000; for every i with 0 <= i < len(coordinates), len(coordinates[i]) = 2, -10000 <= coordinates[i][0] <= 10000, and -10000 <= coordinates[i][1] <= 10000; for every i,j with 0 <= i < j < len(coordinates), not (coordinates[i][0] = coordinates[j][0] and coordinates[i][1] = coordinates[j][1]). -/
  theorem spec_7 (coordinates : Slice (alloc.vec.Vec Std.I64)) (h : Pre coordinates) :
      ∀ r : Bool, check_straight_line coordinates = ok r →
        ∀ u v : ℤ,
          (∀ i : ℕ, i < coordinates.val.length →
            -10000 ≤ px coordinates i + u ∧ px coordinates i + u ≤ 10000) →
          (∀ i : ℕ, i < coordinates.val.length →
            -10000 ≤ py coordinates i + v ∧ py coordinates i + v ≤ 10000) →
          (r = true ↔ CollinearShift coordinates u v) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (coordinates : Slice (alloc.vec.Vec Std.I64)) (h : Pre coordinates), ∀ r : Bool, check_straight_line coordinates = ok r →
          ∀ u v : ℤ,
            (∀ i : ℕ, i < coordinates.val.length →
              -10000 ≤ px coordinates i + u ∧ px coordinates i + u ≤ 10000) →
            (∀ i : ℕ, i < coordinates.val.length →
              -10000 ≤ py coordinates i + v ∧ py coordinates i + v ≤ 10000) →
            (r = true ↔ CollinearShift coordinates u v)) := by
    sorry

  /-- Let n = len(coordinates). For 0 <= i < n let x_i = coordinates[i][0] and y_i = coordinates[i][1]. Whenever the function returns a result r, r = true if and only if the reflected points (y_i, x_i) are collinear, i.e., for every 0 <= i < j < k < n, (y_j - y_i)*(x_k - x_i) - (x_j - x_i)*(y_k - y_i) = 0.
    Preconditions: 2 <= len(coordinates) <= 1000; for every i with 0 <= i < len(coordinates), len(coordinates[i]) = 2, -10000 <= coordinates[i][0] <= 10000, and -10000 <= coordinates[i][1] <= 10000; for every i,j with 0 <= i < j < len(coordinates), not (coordinates[i][0] = coordinates[j][0] and coordinates[i][1] = coordinates[j][1]). -/
  theorem spec_8 (coordinates : Slice (alloc.vec.Vec Std.I64)) (h : Pre coordinates) :
      ∀ r : Bool, check_straight_line coordinates = ok r →
        (r = true ↔ CollinearSwap coordinates) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (coordinates : Slice (alloc.vec.Vec Std.I64)) (h : Pre coordinates), ∀ r : Bool, check_straight_line coordinates = ok r →
          (r = true ↔ CollinearSwap coordinates)) := by
    sorry

  /-- Let n = len(coordinates). For 0 <= i < n let x_i = coordinates[i][0] and y_i = coordinates[i][1]. Define D(i,j,k) = (x_j - x_i)*(y_k - y_i) - (y_j - y_i)*(x_k - x_i). Whenever the function returns a result r, if there exist indices i,j,k with 0 <= i < j < k < n such that D(i,j,k) != 0, then r = false.
    Preconditions: 2 <= len(coordinates) <= 1000; for every i with 0 <= i < len(coordinates), len(coordinates[i]) = 2, -10000 <= coordinates[i][0] <= 10000, and -10000 <= coordinates[i][1] <= 10000; for every i,j with 0 <= i < j < len(coordinates), not (coordinates[i][0] = coordinates[j][0] and coordinates[i][1] = coordinates[j][1]). -/
  theorem spec_9 (coordinates : Slice (alloc.vec.Vec Std.I64)) (h : Pre coordinates) :
      ∀ r : Bool, check_straight_line coordinates = ok r →
        (∃ i j k : ℕ, i < j ∧ j < k ∧ k < coordinates.val.length ∧
            D coordinates i j k ≠ 0) →
          r = false := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (coordinates : Slice (alloc.vec.Vec Std.I64)) (h : Pre coordinates), ∀ r : Bool, check_straight_line coordinates = ok r →
          (∃ i j k : ℕ, i < j ∧ j < k ∧ k < coordinates.val.length ∧
              D coordinates i j k ≠ 0) →
            r = false) := by
    sorry

  end AegisSpec.CheckStraightLine
