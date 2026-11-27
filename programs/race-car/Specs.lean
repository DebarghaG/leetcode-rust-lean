import Aegis.Racecar.Code.Funs

/-!
# Specifications of `Aegis.Racecar.racecar`

LeetCode problem `race-car`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.Racecar

  inductive Instr where
    | A : Instr
    | R : Instr
    deriving DecidableEq, Repr

  abbrev CarState : Type := Int × Int

  def initState : CarState := (0, 1)

  def Instr.step : Instr → CarState → CarState
    | .A, (pos, spd) => (pos + spd, 2 * spd)
    | .R, (pos, spd) => (pos, if spd > 0 then -1 else 1)

  def execInstrs (st : CarState) : List Instr → CarState
    | [] => st
    | i :: rest => execInstrs (Instr.step i st) rest

  def Reaches (s : List Instr) (target : Int) : Prop :=
    (execInstrs initState s).1 = target

  def IsMinLength (target r : Int) : Prop :=
    (∃ s : List Instr, (s.length : Int) = r ∧ Reaches s target) ∧
      ∀ s : List Instr, Reaches s target → r ≤ (s.length : Int)

  def IsLeastPow (target : Int) (m : Nat) : Prop :=
    target ≤ (2 : Int) ^ m - 1 ∧ ∀ k : Nat, target ≤ (2 : Int) ^ k - 1 → m ≤ k

  /-- The function returns a result r, and r is the minimum length of a finite sequence s over the alphabet {A,R} such that executing s from the initial state (position 0, speed +1) leaves the car at position target. Here an A instruction sets position := position + speed and speed := 2*speed, while an R instruction leaves position unchanged and sets speed := -1 if speed > 0, otherwise speed := 1. Thus there exists such a sequence of length r, and every such sequence has length at least r.
    Preconditions: target is an integer with 1 <= target <= 10000. -/
  theorem spec_1 (target : Std.I64) (hlo : 1 ≤ target.val) (hhi : target.val ≤ 10000) :
      ∃ r : Std.I64, Aegis.Racecar.racecar target = ok r ∧ IsMinLength target.val r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (target : Std.I64) (hlo : 1 ≤ target.val) (hhi : target.val ≤ 10000), ∃ r : Std.I64, Aegis.Racecar.racecar target = ok r ∧ IsMinLength target.val r.val) := by
    sorry

  /-- For every target satisfying 1 <= target <= 10000, the function returns a result r and does not fail, panic, or overflow.
    Preconditions: target is an integer with 1 <= target <= 10000. -/
  theorem spec_2 (target : Std.I64) (hlo : 1 ≤ target.val) (hhi : target.val ≤ 10000) :
      ∃ r : Std.I64, Aegis.Racecar.racecar target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (target : Std.I64) (hlo : 1 ≤ target.val) (hhi : target.val ≤ 10000), ∃ r : Std.I64, Aegis.Racecar.racecar target = ok r) := by
    sorry

  /-- The function returns a result r, and there exists a finite instruction sequence s over {A,R} of length r which, when executed from position 0 and speed +1 with the problem's A and R rules, ends at position target.
    Preconditions: target is an integer with 1 <= target <= 10000. -/
  theorem spec_3 (target : Std.I64) (hlo : 1 ≤ target.val) (hhi : target.val ≤ 10000) :
      ∃ r : Std.I64,
        Aegis.Racecar.racecar target = ok r ∧
          ∃ s : List Instr, (s.length : Int) = r.val ∧ Reaches s target.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (target : Std.I64) (hlo : 1 ≤ target.val) (hhi : target.val ≤ 10000), ∃ r : Std.I64,
          Aegis.Racecar.racecar target = ok r ∧
            ∃ s : List Instr, (s.length : Int) = r.val ∧ Reaches s target.val) := by
    sorry

  /-- The function returns a result r, and every finite instruction sequence s over {A,R} that is executed from position 0 and speed +1 under the problem's A and R rules and ends at position target has length at least r.
    Preconditions: target is an integer with 1 <= target <= 10000. -/
  theorem spec_4 (target : Std.I64) (hlo : 1 ≤ target.val) (hhi : target.val ≤ 10000) :
      ∃ r : Std.I64,
        Aegis.Racecar.racecar target = ok r ∧
          ∀ s : List Instr, Reaches s target.val → r.val ≤ (s.length : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (target : Std.I64) (hlo : 1 ≤ target.val) (hhi : target.val ≤ 10000), ∃ r : Std.I64,
          Aegis.Racecar.racecar target = ok r ∧
            ∀ s : List Instr, Reaches s target.val → r.val ≤ (s.length : Int)) := by
    sorry

  /-- Let m be the smallest nonnegative integer such that 2^m - 1 >= target. The function returns a result r and r >= m.
    Preconditions: target is an integer with 1 <= target <= 10000. -/
  theorem spec_5 (target : Std.I64) (hlo : 1 ≤ target.val) (hhi : target.val ≤ 10000) :
      ∃ r : Std.I64,
        Aegis.Racecar.racecar target = ok r ∧
          ∃ m : Nat, IsLeastPow target.val m ∧ (m : Int) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (target : Std.I64) (hlo : 1 ≤ target.val) (hhi : target.val ≤ 10000), ∃ r : Std.I64,
          Aegis.Racecar.racecar target = ok r ∧
            ∃ m : Nat, IsLeastPow target.val m ∧ (m : Int) ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= 200.
    Preconditions: target is an integer with 1 <= target <= 10000. -/
  theorem spec_6 (target : Std.I64) (hlo : 1 ≤ target.val) (hhi : target.val ≤ 10000) :
      ∃ r : Std.I64, Aegis.Racecar.racecar target = ok r ∧ r.val ≤ 200 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (target : Std.I64) (hlo : 1 ≤ target.val) (hhi : target.val ≤ 10000), ∃ r : Std.I64, Aegis.Racecar.racecar target = ok r ∧ r.val ≤ 200) := by
    sorry

  /-- The function returns a result r, and r = 1 if and only if target = 1.
    Preconditions: target is an integer with 1 <= target <= 10000. -/
  theorem spec_7 (target : Std.I64) (hlo : 1 ≤ target.val) (hhi : target.val ≤ 10000) :
      ∃ r : Std.I64, Aegis.Racecar.racecar target = ok r ∧ (r.val = 1 ↔ target.val = 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (target : Std.I64) (hlo : 1 ≤ target.val) (hhi : target.val ≤ 10000), ∃ r : Std.I64, Aegis.Racecar.racecar target = ok r ∧ (r.val = 1 ↔ target.val = 1)) := by
    sorry

  end AegisSpec.Racecar
