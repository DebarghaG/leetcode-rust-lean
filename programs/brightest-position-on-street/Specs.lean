import Aegis.BrightestPosition.Code.Funs

/-!
# Specifications of `Aegis.BrightestPosition.brightest_position`

LeetCode problem `brightest-position-on-street`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.BrightestPosition

  def asLight (v : alloc.vec.Vec Std.I64) : Option (Int × Int) :=
    match v.val with
    | [x, y] => some (x.val, y.val)
    | _ => none

  def innerLen (lights : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Option Nat :=
    (lights.val[i]?).map (fun v => v.val.length)

  def lightPairs (lights : Slice (alloc.vec.Vec Std.I64)) : List (Int × Int) :=
    lights.val.filterMap asLight

  def pairAt (lights : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Option (Int × Int) :=
    (lightPairs lights)[i]?

  def startOf (l : Int × Int) : Int := l.1 - l.2

  def endOf (l : Int × Int) : Int := l.1 + l.2

  def minStart (lights : Slice (alloc.vec.Vec Std.I64)) : Option Int :=
    (lightPairs lights).map startOf |>.min?

  def maxStart (lights : Slice (alloc.vec.Vec Std.I64)) : Option Int :=
    (lightPairs lights).map startOf |>.max?

  def minEnd (lights : Slice (alloc.vec.Vec Std.I64)) : Option Int :=
    (lightPairs lights).map endOf |>.min?

  def maxEnd (lights : Slice (alloc.vec.Vec Std.I64)) : Option Int :=
    (lightPairs lights).map endOf |>.max?

  def coverage (lights : Slice (alloc.vec.Vec Std.I64)) (p : Int) : Nat :=
    ((lightPairs lights).filter (fun l => decide (startOf l ≤ p ∧ p ≤ endOf l))).length

  def positionCount (lights : Slice (alloc.vec.Vec Std.I64)) (p : Int) : Nat :=
    ((lightPairs lights).filter (fun l => decide (l.1 = p))).length

  def precond (lights : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    1 ≤ lights.val.length ∧
      lights.val.length ≤ 100000 ∧
      (∀ i, i < lights.val.length → innerLen lights i = some 2) ∧
      (∀ i, i < lights.val.length →
        ∃ x y : Int,
          pairAt lights i = some (x, y) ∧
            -100000000 ≤ x ∧ x ≤ 100000000 ∧ 0 ≤ y ∧ y ≤ 100000000)

  def IsPermOn (n : Nat) (pi : Nat → Nat) : Prop :=
    (∀ i, i < n → pi i < n) ∧ (∀ i j, i < n → j < n → pi i = pi j → i = j)

  /-- Let B(p) be, for every integer p, the number of indices i with 0 <= i < len(lights) and lights[i][0] - lights[i][1] <= p <= lights[i][0] + lights[i][1]. The function returns a result r and: (a) for every integer p, B(p) <= B(r); (b) for every integer q < r, B(q) < B(r).
    Preconditions: 1 <= len(lights) <= 100000; for every i with 0 <= i < len(lights), len(lights[i]) = 2; for every i with 0 <= i < len(lights), -100000000 <= lights[i][0] <= 100000000 and 0 <= lights[i][1] <= 100000000. -/
  theorem spec_1 (lights : Slice (alloc.vec.Vec Std.I64)) (h : precond lights) :
      ∃ r : Std.I64,
        Aegis.BrightestPosition.brightest_position lights = ok r ∧
          (∀ p : Int, coverage lights p ≤ coverage lights r.val) ∧
          (∀ q : Int, q < r.val → coverage lights q < coverage lights r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (lights : Slice (alloc.vec.Vec Std.I64)) (h : precond lights), ∃ r : Std.I64,
          Aegis.BrightestPosition.brightest_position lights = ok r ∧
            (∀ p : Int, coverage lights p ≤ coverage lights r.val) ∧
            (∀ q : Int, q < r.val → coverage lights q < coverage lights r.val)) := by
    sorry

  /-- The function returns a result r; it does not fail.
    Preconditions: 1 <= len(lights) <= 100000; for every i with 0 <= i < len(lights), len(lights[i]) = 2; for every i with 0 <= i < len(lights), -100000000 <= lights[i][0] <= 100000000 and 0 <= lights[i][1] <= 100000000. -/
  theorem spec_2 (lights : Slice (alloc.vec.Vec Std.I64)) (h : precond lights) :
      ∃ r : Std.I64, Aegis.BrightestPosition.brightest_position lights = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (lights : Slice (alloc.vec.Vec Std.I64)) (h : precond lights), ∃ r : Std.I64, Aegis.BrightestPosition.brightest_position lights = ok r) := by
    sorry

  /-- The function returns a result r and there exists an index i with 0 <= i < len(lights) such that lights[i][0] - lights[i][1] <= r <= lights[i][0] + lights[i][1].
    Preconditions: 1 <= len(lights) <= 100000; for every i with 0 <= i < len(lights), len(lights[i]) = 2; for every i with 0 <= i < len(lights), -100000000 <= lights[i][0] <= 100000000 and 0 <= lights[i][1] <= 100000000. -/
  theorem spec_3 (lights : Slice (alloc.vec.Vec Std.I64)) (h : precond lights) :
      ∃ r : Std.I64,
        Aegis.BrightestPosition.brightest_position lights = ok r ∧
          ∃ i : Nat,
            i < lights.val.length ∧
              ∃ x y : Int,
                pairAt lights i = some (x, y) ∧ x - y ≤ r.val ∧ r.val ≤ x + y := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (lights : Slice (alloc.vec.Vec Std.I64)) (h : precond lights), ∃ r : Std.I64,
          Aegis.BrightestPosition.brightest_position lights = ok r ∧
            ∃ i : Nat,
              i < lights.val.length ∧
                ∃ x y : Int,
                  pairAt lights i = some (x, y) ∧ x - y ≤ r.val ∧ r.val ≤ x + y) := by
    sorry

  /-- The function returns a result r and there exists an index i with 0 <= i < len(lights) such that r = lights[i][0] - lights[i][1].
    Preconditions: 1 <= len(lights) <= 100000; for every i with 0 <= i < len(lights), len(lights[i]) = 2; for every i with 0 <= i < len(lights), -100000000 <= lights[i][0] <= 100000000 and 0 <= lights[i][1] <= 100000000. -/
  theorem spec_4 (lights : Slice (alloc.vec.Vec Std.I64)) (h : precond lights) :
      ∃ r : Std.I64,
        Aegis.BrightestPosition.brightest_position lights = ok r ∧
          ∃ i : Nat,
            i < lights.val.length ∧
              ∃ x y : Int, pairAt lights i = some (x, y) ∧ r.val = x - y := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (lights : Slice (alloc.vec.Vec Std.I64)) (h : precond lights), ∃ r : Std.I64,
          Aegis.BrightestPosition.brightest_position lights = ok r ∧
            ∃ i : Nat,
              i < lights.val.length ∧
                ∃ x y : Int, pairAt lights i = some (x, y) ∧ r.val = x - y) := by
    sorry

  /-- The function returns a result r and min_{0 <= i < len(lights)} (lights[i][0] - lights[i][1]) <= r <= max_{0 <= i < len(lights)} (lights[i][0] + lights[i][1]).
    Preconditions: 1 <= len(lights) <= 100000; for every i with 0 <= i < len(lights), len(lights[i]) = 2; for every i with 0 <= i < len(lights), -100000000 <= lights[i][0] <= 100000000 and 0 <= lights[i][1] <= 100000000. -/
  theorem spec_5 (lights : Slice (alloc.vec.Vec Std.I64)) (h : precond lights) :
      ∃ r : Std.I64,
        Aegis.BrightestPosition.brightest_position lights = ok r ∧
          ∃ lo hi : Int, minStart lights = some lo ∧ maxEnd lights = some hi ∧
            lo ≤ r.val ∧ r.val ≤ hi := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (lights : Slice (alloc.vec.Vec Std.I64)) (h : precond lights), ∃ r : Std.I64,
          Aegis.BrightestPosition.brightest_position lights = ok r ∧
            ∃ lo hi : Int, minStart lights = some lo ∧ maxEnd lights = some hi ∧
              lo ≤ r.val ∧ r.val ≤ hi) := by
    sorry

  /-- The function returns a result r and r = lights[0][0] - lights[0][1].
    Preconditions: 1 <= len(lights) <= 100000; for every i with 0 <= i < len(lights), len(lights[i]) = 2; for every i with 0 <= i < len(lights), -100000000 <= lights[i][0] <= 100000000 and 0 <= lights[i][1] <= 100000000; len(lights) = 1. -/
  theorem spec_6 (lights : Slice (alloc.vec.Vec Std.I64)) (h : precond lights)
      (h_len : lights.val.length = 1) :
      ∃ r : Std.I64,
        Aegis.BrightestPosition.brightest_position lights = ok r ∧
          ∃ x y : Int, pairAt lights 0 = some (x, y) ∧ r.val = x - y := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (lights : Slice (alloc.vec.Vec Std.I64)) (h : precond lights)
        (h_len : lights.val.length = 1), ∃ r : Std.I64,
          Aegis.BrightestPosition.brightest_position lights = ok r ∧
            ∃ x y : Int, pairAt lights 0 = some (x, y) ∧ r.val = x - y) := by
    sorry

  /-- The function returns a result r and, letting C(p) be the number of indices i with 0 <= i < len(lights) and lights[i][0] = p for every integer p, we have: (a) for every integer p, C(p) <= C(r); (b) for every integer q < r, C(q) < C(r).
    Preconditions: 1 <= len(lights) <= 100000; for every i with 0 <= i < len(lights), len(lights[i]) = 2; for every i with 0 <= i < len(lights), -100000000 <= lights[i][0] <= 100000000 and 0 <= lights[i][1] <= 100000000; for every i with 0 <= i < len(lights), lights[i][1] = 0. -/
  theorem spec_7 (lights : Slice (alloc.vec.Vec Std.I64)) (h : precond lights)
      (h_ranges : ∀ i, i < lights.val.length →
        ∃ x y : Int, pairAt lights i = some (x, y) ∧ y = 0) :
      ∃ r : Std.I64,
        Aegis.BrightestPosition.brightest_position lights = ok r ∧
          (∀ p : Int, positionCount lights p ≤ positionCount lights r.val) ∧
          (∀ q : Int, q < r.val →
            positionCount lights q < positionCount lights r.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (lights : Slice (alloc.vec.Vec Std.I64)) (h : precond lights)
        (h_ranges : ∀ i, i < lights.val.length →
          ∃ x y : Int, pairAt lights i = some (x, y) ∧ y = 0), ∃ r : Std.I64,
          Aegis.BrightestPosition.brightest_position lights = ok r ∧
            (∀ p : Int, positionCount lights p ≤ positionCount lights r.val) ∧
            (∀ q : Int, q < r.val →
              positionCount lights q < positionCount lights r.val)) := by
    sorry

  /-- The function returns a result r and r = max_{0 <= i < len(lights)} (lights[i][0] - lights[i][1]).
    Preconditions: 1 <= len(lights) <= 100000; for every i with 0 <= i < len(lights), len(lights[i]) = 2; for every i with 0 <= i < len(lights), -100000000 <= lights[i][0] <= 100000000 and 0 <= lights[i][1] <= 100000000; max_{0 <= i < len(lights)} (lights[i][0] - lights[i][1]) <= min_{0 <= i < len(lights)} (lights[i][0] + lights[i][1]). -/
  theorem spec_8 (lights : Slice (alloc.vec.Vec Std.I64)) (h : precond lights)
      (h_common : ∃ a b : Int, maxStart lights = some a ∧ minEnd lights = some b ∧ a ≤ b) :
      ∃ r : Std.I64,
        Aegis.BrightestPosition.brightest_position lights = ok r ∧
          ∃ a : Int, maxStart lights = some a ∧ r.val = a := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (lights : Slice (alloc.vec.Vec Std.I64)) (h : precond lights)
        (h_common : ∃ a b : Int, maxStart lights = some a ∧ minEnd lights = some b ∧ a ≤ b), ∃ r : Std.I64,
          Aegis.BrightestPosition.brightest_position lights = ok r ∧
            ∃ a : Int, maxStart lights = some a ∧ r.val = a) := by
    sorry

  /-- The function returns a result r and r = min_{0 <= i < len(lights)} (lights[i][0] - lights[i][1]).
    Preconditions: 1 <= len(lights) <= 100000; for every i with 0 <= i < len(lights), len(lights[i]) = 2; for every i with 0 <= i < len(lights), -100000000 <= lights[i][0] <= 100000000 and 0 <= lights[i][1] <= 100000000; for every i and j with 0 <= i < j < len(lights), either lights[i][0] + lights[i][1] < lights[j][0] - lights[j][1] or lights[j][0] + lights[j][1] < lights[i][0] - lights[i][1]. -/
  theorem spec_9 (lights : Slice (alloc.vec.Vec Std.I64)) (h : precond lights)
      (h_disj : ∀ i j : Nat, i < j → j < lights.val.length →
        ∃ x y x' y' : Int,
          pairAt lights i = some (x, y) ∧ pairAt lights j = some (x', y') ∧
            (x + y < x' - y' ∨ x' + y' < x - y)) :
      ∃ r : Std.I64,
        Aegis.BrightestPosition.brightest_position lights = ok r ∧
          ∃ a : Int, minStart lights = some a ∧ r.val = a := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (lights : Slice (alloc.vec.Vec Std.I64)) (h : precond lights)
        (h_disj : ∀ i j : Nat, i < j → j < lights.val.length →
          ∃ x y x' y' : Int,
            pairAt lights i = some (x, y) ∧ pairAt lights j = some (x', y') ∧
              (x + y < x' - y' ∨ x' + y' < x - y)), ∃ r : Std.I64,
          Aegis.BrightestPosition.brightest_position lights = ok r ∧
            ∃ a : Int, minStart lights = some a ∧ r.val = a) := by
    sorry

  /-- The function returns a result r on lights, and the function returns a result r' on lights', and r' = r + c.
    Preconditions: 1 <= len(lights) <= 100000; for every i with 0 <= i < len(lights), len(lights[i]) = 2; for every i with 0 <= i < len(lights), -100000000 <= lights[i][0] <= 100000000 and 0 <= lights[i][1] <= 100000000. Let lights' be any slice of vectors satisfying the same constraints with lights replaced by lights' and with len(lights') = len(lights). Suppose there is an integer c such that for every i with 0 <= i < len(lights), lights'[i][0] = lights[i][0] + c and lights'[i][1] = lights[i][1]. -/
  theorem spec_10 (lights lights' : Slice (alloc.vec.Vec Std.I64))
      (h : precond lights) (h' : precond lights')
      (h_len : lights'.val.length = lights.val.length) (c : Int)
      (h_shift : ∀ i, i < lights.val.length →
        ∃ x y x' y' : Int,
          pairAt lights i = some (x, y) ∧ pairAt lights' i = some (x', y') ∧
            x' = x + c ∧ y' = y) :
      ∃ r r' : Std.I64,
        Aegis.BrightestPosition.brightest_position lights = ok r ∧
          Aegis.BrightestPosition.brightest_position lights' = ok r' ∧
            r'.val = r.val + c := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (lights lights' : Slice (alloc.vec.Vec Std.I64))
        (h : precond lights) (h' : precond lights')
        (h_len : lights'.val.length = lights.val.length) (c : Int)
        (h_shift : ∀ i, i < lights.val.length →
          ∃ x y x' y' : Int,
            pairAt lights i = some (x, y) ∧ pairAt lights' i = some (x', y') ∧
              x' = x + c ∧ y' = y), ∃ r r' : Std.I64,
          Aegis.BrightestPosition.brightest_position lights = ok r ∧
            Aegis.BrightestPosition.brightest_position lights' = ok r' ∧
              r'.val = r.val + c) := by
    sorry

  /-- The function returns a result r on lights, and the function returns a result r' on lights', and r' = r.
    Preconditions: 1 <= len(lights) <= 100000; for every i with 0 <= i < len(lights), len(lights[i]) = 2; for every i with 0 <= i < len(lights), -100000000 <= lights[i][0] <= 100000000 and 0 <= lights[i][1] <= 100000000. Let lights' be any slice of vectors satisfying the same constraints with lights replaced by lights' and with len(lights') = len(lights). Suppose there is a permutation pi of {0, ..., len(lights)-1} such that for every i with 0 <= i < len(lights), lights'[i][0] = lights[pi(i)][0] and lights'[i][1] = lights[pi(i)][1]. -/
  theorem spec_11 (lights lights' : Slice (alloc.vec.Vec Std.I64))
      (h : precond lights) (h' : precond lights')
      (h_len : lights'.val.length = lights.val.length)
      (pi : Nat → Nat) (h_pi : IsPermOn lights.val.length pi)
      (h_perm : ∀ i, i < lights.val.length → pairAt lights' i = pairAt lights (pi i)) :
      ∃ r r' : Std.I64,
        Aegis.BrightestPosition.brightest_position lights = ok r ∧
          Aegis.BrightestPosition.brightest_position lights' = ok r' ∧
            r'.val = r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (lights lights' : Slice (alloc.vec.Vec Std.I64))
        (h : precond lights) (h' : precond lights')
        (h_len : lights'.val.length = lights.val.length)
        (pi : Nat → Nat) (h_pi : IsPermOn lights.val.length pi)
        (h_perm : ∀ i, i < lights.val.length → pairAt lights' i = pairAt lights (pi i)), ∃ r r' : Std.I64,
          Aegis.BrightestPosition.brightest_position lights = ok r ∧
            Aegis.BrightestPosition.brightest_position lights' = ok r' ∧
              r'.val = r.val) := by
    sorry

  /-- The function returns a result r on lights, and the function returns a result r' on lights', and r' = k * r.
    Preconditions: 1 <= len(lights) <= 100000; for every i with 0 <= i < len(lights), len(lights[i]) = 2; for every i with 0 <= i < len(lights), -100000000 <= lights[i][0] <= 100000000 and 0 <= lights[i][1] <= 100000000. Let k be any positive integer. Let lights' be any slice of vectors satisfying the same constraints with lights replaced by lights' and with len(lights') = len(lights). Suppose for every i with 0 <= i < len(lights), lights'[i][0] = k * lights[i][0] and lights'[i][1] = k * lights[i][1]. -/
  theorem spec_12 (lights lights' : Slice (alloc.vec.Vec Std.I64))
      (h : precond lights) (h' : precond lights')
      (h_len : lights'.val.length = lights.val.length)
      (k : Int) (h_k : 0 < k)
      (h_scale : ∀ i, i < lights.val.length →
        ∃ x y x' y' : Int,
          pairAt lights i = some (x, y) ∧ pairAt lights' i = some (x', y') ∧
            x' = k * x ∧ y' = k * y) :
      ∃ r r' : Std.I64,
        Aegis.BrightestPosition.brightest_position lights = ok r ∧
          Aegis.BrightestPosition.brightest_position lights' = ok r' ∧
            r'.val = k * r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (lights lights' : Slice (alloc.vec.Vec Std.I64))
        (h : precond lights) (h' : precond lights')
        (h_len : lights'.val.length = lights.val.length)
        (k : Int) (h_k : 0 < k)
        (h_scale : ∀ i, i < lights.val.length →
          ∃ x y x' y' : Int,
            pairAt lights i = some (x, y) ∧ pairAt lights' i = some (x', y') ∧
              x' = k * x ∧ y' = k * y), ∃ r r' : Std.I64,
          Aegis.BrightestPosition.brightest_position lights = ok r ∧
            Aegis.BrightestPosition.brightest_position lights' = ok r' ∧
              r'.val = k * r.val) := by
    sorry

  end AegisSpec.BrightestPosition
