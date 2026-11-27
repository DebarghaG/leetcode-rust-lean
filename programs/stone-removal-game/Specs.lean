import Aegis.CanAliceWin.Code.Funs

/-!
# Specifications of `Aegis.CanAliceWin.can_alice_win`

LeetCode problem `stone-removal-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CanAliceWin

def S : Nat → Int
  | 0 => 10
  | 1 => 19
  | 2 => 27
  | 3 => 34
  | 4 => 40
  | 5 => 45
  | 6 => 49
  | 7 => 52
  | _ => 52

def FirstExceeds (n : Int) (bound t : Nat) : Prop :=
  t ≤ bound ∧ n < S t ∧ ∀ i : Nat, i < t → S i ≤ n

def WinIntervals (n : Int) : Prop :=
  (10 ≤ n ∧ n ≤ 18) ∨ (27 ≤ n ∧ n ≤ 33) ∨ (40 ≤ n ∧ n ≤ 44) ∨ (49 ≤ n ∧ n ≤ 50)

/-- Let S_0 = 10, S_1 = 19, S_2 = 27, S_3 = 34, S_4 = 40, S_5 = 45, S_6 = 49, and S_7 = 52. Let t be the least integer with 0 <= t <= 7 such that S_t > n. The function returns a result r and does not fail, and r = true if and only if t is odd. Equivalently, r = true exactly when n lies in one of the inclusive integer intervals [10,18], [27,33], [40,44], or [49,50], and r = false exactly when n lies in [1,9], [19,26], [34,39], or [45,48].
  Preconditions: 1 <= n <= 50, where n is the integer value of the Std.I64 parameter. -/
theorem spec_1 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 50) :
    ∃ r : Bool, Aegis.CanAliceWin.can_alice_win n = ok r ∧
      (∀ t : Nat, FirstExceeds n.val 7 t → (r = true ↔ Odd t)) ∧
      (r = true ↔ WinIntervals n.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 50), ∃ r : Bool, Aegis.CanAliceWin.can_alice_win n = ok r ∧
      (∀ t : Nat, FirstExceeds n.val 7 t → (r = true ↔ Odd t)) ∧
      (r = true ↔ WinIntervals n.val)) := by
  sorry

/-- The function returns a result r; it does not fail, overflow, or panic.
  Preconditions: 1 <= n <= 50, where n is the integer value of the Std.I64 parameter. -/
theorem spec_2 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 50) :
    ∃ r : Bool, Aegis.CanAliceWin.can_alice_win n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 50), ∃ r : Bool, Aegis.CanAliceWin.can_alice_win n = ok r) := by
  sorry

/-- Whenever the function returns a result r, if r = true then there exists an odd integer t with 0 <= t <= 7 such that S_t > n and S_i <= n for every integer i with 0 <= i < t, where S_0 = 10, S_1 = 19, S_2 = 27, S_3 = 34, S_4 = 40, S_5 = 45, S_6 = 49, and S_7 = 52. Equivalently, the first required removal that exceeds the remaining stones occurs on Bob's turn.
  Preconditions: 1 <= n <= 50, where n is the integer value of the Std.I64 parameter. -/
theorem spec_3 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 50) :
    ∀ r : Bool, Aegis.CanAliceWin.can_alice_win n = ok r → r = true →
      ∃ t : Nat, FirstExceeds n.val 7 t ∧ Odd t := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 50), ∀ r : Bool, Aegis.CanAliceWin.can_alice_win n = ok r → r = true →
      ∃ t : Nat, FirstExceeds n.val 7 t ∧ Odd t) := by
  sorry

/-- Whenever the function returns a result r, if r = false then there exists an even integer t with 0 <= t <= 6 such that S_t > n and S_i <= n for every integer i with 0 <= i < t, where S_0 = 10, S_1 = 19, S_2 = 27, S_3 = 34, S_4 = 40, S_5 = 45, and S_6 = 49. Equivalently, the first required removal that exceeds the remaining stones occurs on Alice's turn.
  Preconditions: 1 <= n <= 50, where n is the integer value of the Std.I64 parameter. -/
theorem spec_4 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 50) :
    ∀ r : Bool, Aegis.CanAliceWin.can_alice_win n = ok r → r = false →
      ∃ t : Nat, FirstExceeds n.val 6 t ∧ Even t := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 50), ∀ r : Bool, Aegis.CanAliceWin.can_alice_win n = ok r → r = false →
      ∃ t : Nat, FirstExceeds n.val 6 t ∧ Even t) := by
  sorry

end AegisSpec.CanAliceWin
