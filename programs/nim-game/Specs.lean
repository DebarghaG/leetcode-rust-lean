import Aegis.CanWinNim.Code.Funs

/-!
# Specifications of `Aegis.CanWinNim.can_win_nim`

LeetCode problem `nim-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CanWinNim

  open Aegis.CanWinNim

  /-- The function returns an ok Boolean r (it does not fail), and r = true if and only if n mod 4 != 0; equivalently, r = false if and only if n is divisible by 4.
    Preconditions: n is the I64 parameter, interpreted as a mathematical integer, and 1 <= n <= 2^31 - 1 = 2147483647. -/
  theorem spec_1 (n : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 2147483647) :
      ∃ r : Bool,
        can_win_nim n = ok r ∧ (r = true ↔ n.val % 4 ≠ 0) ∧ (r = false ↔ n.val % 4 = 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 2147483647), ∃ r : Bool,
          can_win_nim n = ok r ∧ (r = true ↔ n.val % 4 ≠ 0) ∧ (r = false ↔ n.val % 4 = 0)) := by
    sorry

  /-- For every allowed n, can_win_nim n returns an ok Boolean result and does not fail with panic, arithmetic overflow, or out-of-bounds behavior.
    Preconditions: 1 <= n <= 2^31 - 1 = 2147483647. -/
  theorem spec_2 (n : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 2147483647) :
      ∃ r : Bool, can_win_nim n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 2147483647), ∃ r : Bool, can_win_nim n = ok r) := by
    sorry

  /-- Both calls can_win_nim n and can_win_nim m return ok Boolean values r_n and r_m respectively, and r_n = r_m.
    Preconditions: 1 <= n <= 2^31 - 1 = 2147483647, 1 <= m <= 2^31 - 1 = 2147483647, and n mod 4 = m mod 4. -/
  theorem spec_3 (n m : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 2147483647)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 2147483647) (hmod : n.val % 4 = m.val % 4) :
      ∃ rn rm : Bool, can_win_nim n = ok rn ∧ can_win_nim m = ok rm ∧ rn = rm := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n m : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 2147483647)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 2147483647) (hmod : n.val % 4 = m.val % 4), ∃ rn rm : Bool, can_win_nim n = ok rn ∧ can_win_nim m = ok rm ∧ rn = rm) := by
    sorry

  /-- The calls can_win_nim n, can_win_nim (n-1), can_win_nim (n-2), and can_win_nim (n-3) all return ok Boolean values; let r, r1, r2, r3 be those values respectively. Then r = true if and only if at least one of r1, r2, r3 is false.
    Preconditions: 4 <= n <= 2^31 - 1 = 2147483647. -/
  theorem spec_4 (n : I64) (hn_lo : 4 ≤ n.val) (hn_hi : n.val ≤ 2147483647) :
      ∃ r r1 r2 r3 : Bool,
        can_win_nim n = ok r ∧
          can_win_nim (I64.ofInt (n.val - 1) (by scalar_tac)) = ok r1 ∧
          can_win_nim (I64.ofInt (n.val - 2) (by scalar_tac)) = ok r2 ∧
          can_win_nim (I64.ofInt (n.val - 3) (by scalar_tac)) = ok r3 ∧
          (r = true ↔ r1 = false ∨ r2 = false ∨ r3 = false) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (hn_lo : 4 ≤ n.val) (hn_hi : n.val ≤ 2147483647), ∃ r r1 r2 r3 : Bool,
          can_win_nim n = ok r ∧
            can_win_nim (I64.ofInt (n.val - 1) (by scalar_tac)) = ok r1 ∧
            can_win_nim (I64.ofInt (n.val - 2) (by scalar_tac)) = ok r2 ∧
            can_win_nim (I64.ofInt (n.val - 3) (by scalar_tac)) = ok r3 ∧
            (r = true ↔ r1 = false ∨ r2 = false ∨ r3 = false)) := by
    sorry

  /-- If can_win_nim n returns ok true, then there exists an integer k such that 1 <= k <= 3, k <= n, and either n-k = 0 or can_win_nim (n-k) returns ok false.
    Preconditions: 1 <= n <= 2^31 - 1 = 2147483647. -/
  theorem spec_5 (n : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 2147483647)
      (hcan : can_win_nim n = ok true) :
      ∃ k : ℤ, 1 ≤ k ∧ k ≤ 3 ∧ k ≤ n.val ∧
        (n.val - k = 0 ∨ ∃ nk : I64, nk.val = n.val - k ∧ can_win_nim nk = ok false) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 2147483647)
        (hcan : can_win_nim n = ok true), ∃ k : ℤ, 1 ≤ k ∧ k ≤ 3 ∧ k ≤ n.val ∧
          (n.val - k = 0 ∨ ∃ nk : I64, nk.val = n.val - k ∧ can_win_nim nk = ok false)) := by
    sorry

  /-- If can_win_nim n returns ok false, then for every integer k with 1 <= k <= 3 and k <= n, the call can_win_nim (n-k) returns ok true.
    Preconditions: 1 <= n <= 2^31 - 1 = 2147483647. -/
  theorem spec_6 (n : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 2147483647)
      (hcan : can_win_nim n = ok false) :
      ∀ (k : ℤ) (hk_lo : 1 ≤ k) (hk_hi : k ≤ 3) (hk_n : k ≤ n.val),
        can_win_nim (I64.ofInt (n.val - k) (by scalar_tac)) = ok true := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 2147483647)
        (hcan : can_win_nim n = ok false), ∀ (k : ℤ) (hk_lo : 1 ≤ k) (hk_hi : k ≤ 3) (hk_n : k ≤ n.val),
          can_win_nim (I64.ofInt (n.val - k) (by scalar_tac)) = ok true) := by
    sorry

  end AegisSpec.CanWinNim
