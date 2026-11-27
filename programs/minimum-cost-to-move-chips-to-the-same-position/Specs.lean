import Aegis.MinCostToMoveChips.Code.Funs

/-!
# Specifications of `Aegis.MinCostToMoveChips.min_cost_to_move_chips`

LeetCode problem `minimum-cost-to-move-chips-to-the-same-position`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinCostToMoveChips

open Aegis.MinCostToMoveChips

def evenP (n : Int) : Bool := n % 2 == 0

def numEven (l : List Int) : Nat := l.countP evenP

def numOdd (l : List Int) : Nat := l.countP (fun n => !evenP n)

def numDiffParity (l : List Int) (t : Int) : Nat :=
  l.countP (fun n => evenP n != evenP t)

def allSameParity (l : List Int) : Prop :=
  (∀ n ∈ l, evenP n = true) ∨ (∀ n ∈ l, evenP n = false)

def validPositions (position : Slice Std.I64) : Prop :=
  1 ≤ position.val.length ∧ position.val.length ≤ 100 ∧
    ∀ x ∈ position.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9

/-- The function returns a result r and r = min(c_odd, c_even), where c_odd is the number of indices i with 0 <= i < len(position) such that position[i] is odd, and c_even is the number of indices i with 0 <= i < len(position) such that position[i] is even.
  Preconditions: position satisfies the problem constraints: 1 <= len(position) <= 100 and for every i with 0 <= i < len(position), 1 <= position[i] <= 10^9. -/
theorem spec_1 (position : Slice Std.I64) (h : validPositions position) :
    ∃ r, min_cost_to_move_chips position = ok r ∧
      r.val = ((min (numOdd position.val) (numEven position.val) : Nat) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (position : Slice Std.I64) (h : validPositions position), ∃ r, min_cost_to_move_chips position = ok r ∧
      r.val = ((min (numOdd position.val) (numEven position.val) : Nat) : Int)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: position satisfies the problem constraints: 1 <= len(position) <= 100 and for every i with 0 <= i < len(position), 1 <= position[i] <= 10^9. -/
theorem spec_2 (position : Slice Std.I64) (h : validPositions position) :
    ∃ r, min_cost_to_move_chips position = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (position : Slice Std.I64) (h : validPositions position), ∃ r, min_cost_to_move_chips position = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: position satisfies the problem constraints: 1 <= len(position) <= 100 and for every i with 0 <= i < len(position), 1 <= position[i] <= 10^9. -/
theorem spec_3 (position : Slice Std.I64) (h : validPositions position)
    (r : Std.I64) (hr : min_cost_to_move_chips position = ok r) : 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (position : Slice Std.I64) (h : validPositions position)
    (r : Std.I64) (hr : min_cost_to_move_chips position = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, 2 * r <= len(position).
  Preconditions: position satisfies the problem constraints: 1 <= len(position) <= 100 and for every i with 0 <= i < len(position), 1 <= position[i] <= 10^9. -/
theorem spec_4 (position : Slice Std.I64) (h : validPositions position)
    (r : Std.I64) (hr : min_cost_to_move_chips position = ok r) :
    2 * r.val ≤ ((position.val.length : Nat) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (position : Slice Std.I64) (h : validPositions position)
    (r : Std.I64) (hr : min_cost_to_move_chips position = ok r), 2 * r.val ≤ ((position.val.length : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every integer t, the number of indices i with 0 <= i < len(position) such that position[i] and t have different parity is at least r.
  Preconditions: position satisfies the problem constraints: 1 <= len(position) <= 100 and for every i with 0 <= i < len(position), 1 <= position[i] <= 10^9. -/
theorem spec_5 (position : Slice Std.I64) (h : validPositions position)
    (r : Std.I64) (hr : min_cost_to_move_chips position = ok r) :
    ∀ t : Int, r.val ≤ ((numDiffParity position.val t : Nat) : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (position : Slice Std.I64) (h : validPositions position)
    (r : Std.I64) (hr : min_cost_to_move_chips position = ok r), ∀ t : Int, r.val ≤ ((numDiffParity position.val t : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, there exists an integer t such that the number of indices i with 0 <= i < len(position) such that position[i] and t have different parity is exactly r.
  Preconditions: position satisfies the problem constraints: 1 <= len(position) <= 100 and for every i with 0 <= i < len(position), 1 <= position[i] <= 10^9. -/
theorem spec_6 (position : Slice Std.I64) (h : validPositions position)
    (r : Std.I64) (hr : min_cost_to_move_chips position = ok r) :
    ∃ t : Int, ((numDiffParity position.val t : Nat) : Int) = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (position : Slice Std.I64) (h : validPositions position)
    (r : Std.I64) (hr : min_cost_to_move_chips position = ok r), ∃ t : Int, ((numDiffParity position.val t : Nat) : Int) = r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if all entries position[i] have the same parity (all even or all odd).
  Preconditions: position satisfies the problem constraints: 1 <= len(position) <= 100 and for every i with 0 <= i < len(position), 1 <= position[i] <= 10^9. -/
theorem spec_7 (position : Slice Std.I64) (h : validPositions position)
    (r : Std.I64) (hr : min_cost_to_move_chips position = ok r) :
    r.val = 0 ↔ allSameParity position.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (position : Slice Std.I64) (h : validPositions position)
    (r : Std.I64) (hr : min_cost_to_move_chips position = ok r), r.val = 0 ↔ allSameParity position.val) := by
  sorry

/-- Whenever the function returns a result r on position and a result r' on other, r = r'.
  Preconditions: position satisfies the problem constraints: 1 <= len(position) <= 100 and for every i with 0 <= i < len(position), 1 <= position[i] <= 10^9. Also, other is any slice satisfying the same constraints with len(other) = len(position) and, for every i with 0 <= i < len(position), position[i] and other[i] have the same parity. -/
theorem spec_8 (position other : Slice Std.I64)
    (h : validPositions position) (h' : validPositions other)
    (hlen : other.val.length = position.val.length)
    (hpar : ∀ (i : Nat) (h₁ : i < position.val.length) (h₂ : i < other.val.length),
      evenP (position.val[i]'h₁) = evenP (other.val[i]'h₂)) :
    ∀ r r', min_cost_to_move_chips position = ok r →
      min_cost_to_move_chips other = ok r' → r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (position other : Slice Std.I64)
    (h : validPositions position) (h' : validPositions other)
    (hlen : other.val.length = position.val.length)
    (hpar : ∀ (i : Nat) (h₁ : i < position.val.length) (h₂ : i < other.val.length),
      evenP (position.val[i]'h₁) = evenP (other.val[i]'h₂)), ∀ r r', min_cost_to_move_chips position = ok r →
      min_cost_to_move_chips other = ok r' → r.val = r'.val) := by
  sorry

end AegisSpec.MinCostToMoveChips
