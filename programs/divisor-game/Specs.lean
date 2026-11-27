import Aegis.DivisorGame.Code.Funs

/-!
# Specifications of `Aegis.DivisorGame.divisor_game`

LeetCode problem `divisor-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DivisorGame

def W (m : ℕ) : Bool :=
  if m ≤ 1 then false
  else
    (List.range m).any (fun x =>
      if _h : 0 < x ∧ m - x < m then decide (x ∣ m) && !W (m - x) else false)
termination_by m

theorem W_one : W 1 = false := by
  rw [W]
  simp

theorem W_step {m : ℕ} (hm : 1 < m) :
    (W m = true ↔ ∃ x : ℕ, 0 < x ∧ x < m ∧ x ∣ m ∧ W (m - x) = false) := by
  have hm' : ¬ m ≤ 1 := by omega

  have key : ∀ x : ℕ, x < m →
      ((if _h : 0 < x ∧ m - x < m then decide (x ∣ m) && !W (m - x) else false) = true
        ↔ (0 < x ∧ x ∣ m ∧ W (m - x) = false)) := by
    intro x hx
    by_cases h0 : 0 < x
    · rw [dite_eq_left (show 0 < x ∧ m - x < m from ⟨h0, by omega⟩)]
      by_cases hd : x ∣ m <;> by_cases hw : W (m - x) = true <;> simp_all
    · rw [dite_eq_right (show ¬ (0 < x ∧ m - x < m) from fun hh => h0 hh.1)]
      simp [h0]
  rw [W, ite_eq_right hm', List.any_eq_true]
  constructor
  · rintro ⟨x, hxmem, hxT⟩
    have hx : x < m := List.mem_range.mp hxmem
    obtain ⟨h0, hd, hw⟩ := (key x hx).mp hxT
    exact ⟨x, h0, hx, hd, hw⟩
  · rintro ⟨x, h0, hx, hd, hw⟩
    exact ⟨x, List.mem_range.mpr hx, (key x hx).mpr ⟨h0, hd, hw⟩⟩

/-- Define W on positive integers by: W(1) = false; for m > 1, W(m) = true if and only if there exists an integer x with 0 < x < m and x divides m such that W(m - x) = false. Equivalently, W(m) says that the player whose turn it is at m can force a win. Whenever divisor_game n returns a result r, r = true if and only if W(n) = true, i.e. Alice, who moves first starting from n, wins under optimal play.
  Preconditions: n is an integer satisfying 1 <= n <= 1000. -/
theorem spec_1 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
    ∀ r : Bool, Aegis.DivisorGame.divisor_game n = ok r → (r = true ↔ W n.val.toNat = true) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : Bool, Aegis.DivisorGame.divisor_game n = ok r → (r = true ↔ W n.val.toNat = true)) := by
  sorry

/-- divisor_game n returns a result; it does not fail, overflow, panic, or otherwise enter the failure case of Result.
  Preconditions: n is an integer satisfying 1 <= n <= 1000. -/
theorem spec_2 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
    ∃ r : Bool, Aegis.DivisorGame.divisor_game n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∃ r : Bool, Aegis.DivisorGame.divisor_game n = ok r) := by
  sorry

/-- Whenever divisor_game n returns a result r, r = true if and only if n is even (that is, n mod 2 = 0).
  Preconditions: n is an integer satisfying 1 <= n <= 1000. -/
theorem spec_3 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
    ∀ r : Bool, Aegis.DivisorGame.divisor_game n = ok r → (r = true ↔ n.val % 2 = 0) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : Bool, Aegis.DivisorGame.divisor_game n = ok r → (r = true ↔ n.val % 2 = 0)) := by
  sorry

end AegisSpec.DivisorGame
