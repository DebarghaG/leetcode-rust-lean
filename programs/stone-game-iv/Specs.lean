import Aegis.WinnerSquareGame.Code.Funs

/-!
# Specifications of `Aegis.WinnerSquareGame.winner_square_game`

LeetCode problem `stone-game-iv`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.WinnerSquareGame

def W (m : ℤ) : Prop :=
  if h : 0 < m then
    ∃ k : ℤ, ∃ (hk : 0 < k), ∃ (hle : k * k ≤ m), ¬ W (m - k * k)
  else False
termination_by Int.natAbs m
decreasing_by
  have hkk : 0 < k * k := Int.mul_pos hk hk
  omega

theorem W_zero : ¬ W 0 := by
  rw [W.eq_def]
  simp

theorem W_pos {m : ℤ} (hm : 0 < m) :
    W m ↔ ∃ k : ℤ, 0 < k ∧ k * k ≤ m ∧ ¬ W (m - k * k) := by
  rw [W.eq_def, dite_eq_left hm]
  constructor <;> rintro ⟨k, hk, hle, hw⟩ <;> exact ⟨k, hk, hle, hw⟩

/-- Let W be the predicate on nonnegative integers defined by: W(0) = false, and for m > 0, W(m) = true if and only if there exists a positive integer k such that k*k <= m and W(m - k*k) = false. Whenever the function returns a result r, r = true if and only if W(n) = true.
  Preconditions: n is an integer with 1 <= n <= 10^5. -/
theorem spec_1 (n : Aeneas.Std.I64) (r : Bool)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hres : Aegis.WinnerSquareGame.winner_square_game n = ok r) :
    (r = true ↔ W n.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (r : Bool)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hres : Aegis.WinnerSquareGame.winner_square_game n = ok r), (r = true ↔ W n.val)) := by
  sorry

/-- The function returns a result r (i.e., it does not fail, overflow, or panic).
  Preconditions: n is an integer with 1 <= n <= 10^5. -/
theorem spec_2 (n : Aeneas.Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000) :
    ∃ r : Bool, Aegis.WinnerSquareGame.winner_square_game n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Aeneas.Std.I64)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000), ∃ r : Bool, Aegis.WinnerSquareGame.winner_square_game n = ok r) := by
  sorry

/-- Let W be defined as in spec_1. Whenever the function returns a result r, if r = true then there exists a positive integer k with k*k <= n and W(n - k*k) = false.
  Preconditions: n is an integer with 1 <= n <= 10^5. -/
theorem spec_3 (n : Aeneas.Std.I64) (r : Bool)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hres : Aegis.WinnerSquareGame.winner_square_game n = ok r) :
    r = true → ∃ k : ℤ, 0 < k ∧ k * k ≤ n.val ∧ ¬ W (n.val - k * k) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (r : Bool)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hres : Aegis.WinnerSquareGame.winner_square_game n = ok r), r = true → ∃ k : ℤ, 0 < k ∧ k * k ≤ n.val ∧ ¬ W (n.val - k * k)) := by
  sorry

/-- Let W be defined as in spec_1. Whenever the function returns a result r, if r = false then for every positive integer k with k*k <= n, W(n - k*k) = true.
  Preconditions: n is an integer with 1 <= n <= 10^5. -/
theorem spec_4 (n : Aeneas.Std.I64) (r : Bool)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hres : Aegis.WinnerSquareGame.winner_square_game n = ok r) :
    r = false → ∀ k : ℤ, 0 < k → k * k ≤ n.val → W (n.val - k * k) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (r : Bool)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hres : Aegis.WinnerSquareGame.winner_square_game n = ok r), r = false → ∀ k : ℤ, 0 < k → k * k ≤ n.val → W (n.val - k * k)) := by
  sorry

/-- Let W be defined as in spec_1. If there exists a positive integer k with k*k <= n and W(n - k*k) = false, then whenever the function returns a result r, r = true.
  Preconditions: n is an integer with 1 <= n <= 10^5. -/
theorem spec_5 (n : Aeneas.Std.I64) (r : Bool)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hres : Aegis.WinnerSquareGame.winner_square_game n = ok r)
    (hwit : ∃ k : ℤ, 0 < k ∧ k * k ≤ n.val ∧ ¬ W (n.val - k * k)) :
    r = true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (r : Bool)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hres : Aegis.WinnerSquareGame.winner_square_game n = ok r)
    (hwit : ∃ k : ℤ, 0 < k ∧ k * k ≤ n.val ∧ ¬ W (n.val - k * k)), r = true) := by
  sorry

/-- Let W be defined as in spec_1. If for every positive integer k with k*k <= n, W(n - k*k) = true, then whenever the function returns a result r, r = false.
  Preconditions: n is an integer with 1 <= n <= 10^5. -/
theorem spec_6 (n : Aeneas.Std.I64) (r : Bool)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hres : Aegis.WinnerSquareGame.winner_square_game n = ok r)
    (hall : ∀ k : ℤ, 0 < k → k * k ≤ n.val → W (n.val - k * k)) :
    r = false := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (r : Bool)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
    (hres : Aegis.WinnerSquareGame.winner_square_game n = ok r)
    (hall : ∀ k : ℤ, 0 < k → k * k ≤ n.val → W (n.val - k * k)), r = false) := by
  sorry

end AegisSpec.WinnerSquareGame
