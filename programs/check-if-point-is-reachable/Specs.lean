import Aegis.IsReachable.Code.Funs

/-!
# Specifications of `Aegis.IsReachable.is_reachable`

LeetCode problem `check-if-point-is-reachable`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsReachable

  def Step (p q : ℤ × ℤ) : Prop :=
    q = (p.1, p.2 - p.1) ∨ q = (p.1 - p.2, p.2) ∨ q = (2 * p.1, p.2) ∨ q = (p.1, 2 * p.2)

  def reachable (a b : ℤ) : Prop := Relation.ReflTransGen Step (1, 1) (a, b)

  def IsOddPrime (p : ℕ) : Prop := p.Prime ∧ p % 2 = 1

  /-- Let reachable(a,b) mean that there exist an integer n >= 0 and integer points (x_i,y_i) for 0 <= i <= n such that (x_0,y_0)=(1,1), (x_n,y_n)=(a,b), and for every i with 0 <= i < n the point (x_{i+1},y_{i+1}) is one of (x_i, y_i - x_i), (x_i - y_i, y_i), (2*x_i, y_i), (x_i, 2*y_i). For every targetX,targetY satisfying the preconditions, whenever is_reachable(targetX,targetY) returns a result r, r = true if and only if reachable(targetX,targetY). Equivalently (and this equivalence is part of the specification), r = true if and only if gcd(targetX,targetY) = 2^k for some integer k >= 0, where gcd is the greatest positive common divisor.
    Preconditions: 1 <= targetX <= 10^9 and 1 <= targetY <= 10^9. -/
  theorem spec_1 (targetX targetY : Std.I64)
      (hx_lo : 1 ≤ targetX.val) (hx_hi : targetX.val ≤ 10 ^ 9)
      (hy_lo : 1 ≤ targetY.val) (hy_hi : targetY.val ≤ 10 ^ 9) :
      ∀ (r : Bool), Aegis.IsReachable.is_reachable targetX targetY = Aeneas.Std.Result.ok r →
        (r = true ↔ reachable targetX.val targetY.val) ∧
        (r = true ↔ ∃ k : ℕ, Int.gcd targetX.val targetY.val = 2 ^ k) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (targetX targetY : Std.I64)
        (hx_lo : 1 ≤ targetX.val) (hx_hi : targetX.val ≤ 10 ^ 9)
        (hy_lo : 1 ≤ targetY.val) (hy_hi : targetY.val ≤ 10 ^ 9), ∀ (r : Bool), Aegis.IsReachable.is_reachable targetX targetY = Aeneas.Std.Result.ok r →
          (r = true ↔ reachable targetX.val targetY.val) ∧
          (r = true ↔ ∃ k : ℕ, Int.gcd targetX.val targetY.val = 2 ^ k)) := by
    sorry

  /-- For every targetX,targetY satisfying the preconditions, the call is_reachable(targetX,targetY) returns a result r; it does not fail, panic, overflow, or go out of bounds.
    Preconditions: 1 <= targetX <= 10^9 and 1 <= targetY <= 10^9. -/
  theorem spec_2 (targetX targetY : Std.I64)
      (hx_lo : 1 ≤ targetX.val) (hx_hi : targetX.val ≤ 10 ^ 9)
      (hy_lo : 1 ≤ targetY.val) (hy_hi : targetY.val ≤ 10 ^ 9) :
      ∃ r : Bool, Aegis.IsReachable.is_reachable targetX targetY = Aeneas.Std.Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (targetX targetY : Std.I64)
        (hx_lo : 1 ≤ targetX.val) (hx_hi : targetX.val ≤ 10 ^ 9)
        (hy_lo : 1 ≤ targetY.val) (hy_hi : targetY.val ≤ 10 ^ 9), ∃ r : Bool, Aegis.IsReachable.is_reachable targetX targetY = Aeneas.Std.Result.ok r) := by
    sorry

  /-- For every targetX,targetY satisfying the preconditions, if is_reachable(targetX,targetY) returns r and is_reachable(targetY,targetX) returns s, then r = s.
    Preconditions: 1 <= targetX <= 10^9 and 1 <= targetY <= 10^9. -/
  theorem spec_3 (targetX targetY : Std.I64)
      (hx_lo : 1 ≤ targetX.val) (hx_hi : targetX.val ≤ 10 ^ 9)
      (hy_lo : 1 ≤ targetY.val) (hy_hi : targetY.val ≤ 10 ^ 9) :
      ∀ (r s : Bool), Aegis.IsReachable.is_reachable targetX targetY = Aeneas.Std.Result.ok r →
        Aegis.IsReachable.is_reachable targetY targetX = Aeneas.Std.Result.ok s → r = s := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (targetX targetY : Std.I64)
        (hx_lo : 1 ≤ targetX.val) (hx_hi : targetX.val ≤ 10 ^ 9)
        (hy_lo : 1 ≤ targetY.val) (hy_hi : targetY.val ≤ 10 ^ 9), ∀ (r s : Bool), Aegis.IsReachable.is_reachable targetX targetY = Aeneas.Std.Result.ok r →
          Aegis.IsReachable.is_reachable targetY targetX = Aeneas.Std.Result.ok s → r = s) := by
    sorry

  /-- Whenever is_reachable(targetX,targetY) returns r and is_reachable(targetX/2,targetY/2) returns s, where / denotes exact integer division, then r = s.
    Preconditions: 1 <= targetX <= 10^9, 1 <= targetY <= 10^9, targetX is even, and targetY is even. -/
  theorem spec_4 (targetX targetY : Std.I64)
      (hx_lo : 1 ≤ targetX.val) (hx_hi : targetX.val ≤ 10 ^ 9)
      (hy_lo : 1 ≤ targetY.val) (hy_hi : targetY.val ≤ 10 ^ 9)
      (hx_even : targetX.val % 2 = 0) (hy_even : targetY.val % 2 = 0)
      (X Y : Std.I64) (hX : X.val = targetX.val / 2) (hY : Y.val = targetY.val / 2) :
      ∀ (r s : Bool), Aegis.IsReachable.is_reachable targetX targetY = Aeneas.Std.Result.ok r →
        Aegis.IsReachable.is_reachable X Y = Aeneas.Std.Result.ok s → r = s := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (targetX targetY : Std.I64)
        (hx_lo : 1 ≤ targetX.val) (hx_hi : targetX.val ≤ 10 ^ 9)
        (hy_lo : 1 ≤ targetY.val) (hy_hi : targetY.val ≤ 10 ^ 9)
        (hx_even : targetX.val % 2 = 0) (hy_even : targetY.val % 2 = 0)
        (X Y : Std.I64) (hX : X.val = targetX.val / 2) (hY : Y.val = targetY.val / 2), ∀ (r s : Bool), Aegis.IsReachable.is_reachable targetX targetY = Aeneas.Std.Result.ok r →
          Aegis.IsReachable.is_reachable X Y = Aeneas.Std.Result.ok s → r = s) := by
    sorry

  /-- Whenever is_reachable(targetX,targetY) returns a result r, r = false.
    Preconditions: 1 <= targetX <= 10^9, 1 <= targetY <= 10^9, and there exist an odd prime p and positive integers a,b such that targetX = p*a and targetY = p*b. -/
  theorem spec_5 (targetX targetY : Std.I64)
      (hx_lo : 1 ≤ targetX.val) (hx_hi : targetX.val ≤ 10 ^ 9)
      (hy_lo : 1 ≤ targetY.val) (hy_hi : targetY.val ≤ 10 ^ 9)
      (hcommon : ∃ p : ℕ, IsOddPrime p ∧
        ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
          targetX.val = (p : ℤ) * (a : ℤ) ∧ targetY.val = (p : ℤ) * (b : ℤ)) :
      ∀ (r : Bool), Aegis.IsReachable.is_reachable targetX targetY = Aeneas.Std.Result.ok r →
        r = false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (targetX targetY : Std.I64)
        (hx_lo : 1 ≤ targetX.val) (hx_hi : targetX.val ≤ 10 ^ 9)
        (hy_lo : 1 ≤ targetY.val) (hy_hi : targetY.val ≤ 10 ^ 9)
        (hcommon : ∃ p : ℕ, IsOddPrime p ∧
          ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
            targetX.val = (p : ℤ) * (a : ℤ) ∧ targetY.val = (p : ℤ) * (b : ℤ)), ∀ (r : Bool), Aegis.IsReachable.is_reachable targetX targetY = Aeneas.Std.Result.ok r →
          r = false) := by
    sorry

  /-- Whenever is_reachable(targetX,targetY) returns a result r, r = true.
    Preconditions: 1 <= targetX <= 10^9, 1 <= targetY <= 10^9, and gcd(targetX,targetY)=1. -/
  theorem spec_6 (targetX targetY : Std.I64)
      (hx_lo : 1 ≤ targetX.val) (hx_hi : targetX.val ≤ 10 ^ 9)
      (hy_lo : 1 ≤ targetY.val) (hy_hi : targetY.val ≤ 10 ^ 9)
      (hcoprime : Int.gcd targetX.val targetY.val = 1) :
      ∀ (r : Bool), Aegis.IsReachable.is_reachable targetX targetY = Aeneas.Std.Result.ok r →
        r = true := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (targetX targetY : Std.I64)
        (hx_lo : 1 ≤ targetX.val) (hx_hi : targetX.val ≤ 10 ^ 9)
        (hy_lo : 1 ≤ targetY.val) (hy_hi : targetY.val ≤ 10 ^ 9)
        (hcoprime : Int.gcd targetX.val targetY.val = 1), ∀ (r : Bool), Aegis.IsReachable.is_reachable targetX targetY = Aeneas.Std.Result.ok r →
          r = true) := by
    sorry

  /-- Whenever is_reachable(targetX,targetY) returns a result r, r = true if and only if gcd(targetX,targetY)=1, where gcd is the greatest positive common divisor.
    Preconditions: 1 <= targetX <= 10^9, 1 <= targetY <= 10^9, targetX is odd, and targetY is odd. -/
  theorem spec_7 (targetX targetY : Std.I64)
      (hx_lo : 1 ≤ targetX.val) (hx_hi : targetX.val ≤ 10 ^ 9)
      (hy_lo : 1 ≤ targetY.val) (hy_hi : targetY.val ≤ 10 ^ 9)
      (hx_odd : targetX.val % 2 = 1) (hy_odd : targetY.val % 2 = 1) :
      ∀ (r : Bool), Aegis.IsReachable.is_reachable targetX targetY = Aeneas.Std.Result.ok r →
        (r = true ↔ Int.gcd targetX.val targetY.val = 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (targetX targetY : Std.I64)
        (hx_lo : 1 ≤ targetX.val) (hx_hi : targetX.val ≤ 10 ^ 9)
        (hy_lo : 1 ≤ targetY.val) (hy_hi : targetY.val ≤ 10 ^ 9)
        (hx_odd : targetX.val % 2 = 1) (hy_odd : targetY.val % 2 = 1), ∀ (r : Bool), Aegis.IsReachable.is_reachable targetX targetY = Aeneas.Std.Result.ok r →
          (r = true ↔ Int.gcd targetX.val targetY.val = 1)) := by
    sorry

  /-- Whenever is_reachable(targetX,targetY) returns a result r, r = true if and only if targetX = 2^k for some integer k >= 0.
    Preconditions: 1 <= targetX <= 10^9, 1 <= targetY <= 10^9, and targetX divides targetY, meaning there exists a positive integer q with targetY = q*targetX. -/
  theorem spec_8 (targetX targetY : Std.I64)
      (hx_lo : 1 ≤ targetX.val) (hx_hi : targetX.val ≤ 10 ^ 9)
      (hy_lo : 1 ≤ targetY.val) (hy_hi : targetY.val ≤ 10 ^ 9)
      (hdvd : ∃ q : ℕ, 0 < q ∧ targetY.val = (q : ℤ) * targetX.val) :
      ∀ (r : Bool), Aegis.IsReachable.is_reachable targetX targetY = Aeneas.Std.Result.ok r →
        (r = true ↔ ∃ k : ℕ, targetX.val = (2 : ℤ) ^ k) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (targetX targetY : Std.I64)
        (hx_lo : 1 ≤ targetX.val) (hx_hi : targetX.val ≤ 10 ^ 9)
        (hy_lo : 1 ≤ targetY.val) (hy_hi : targetY.val ≤ 10 ^ 9)
        (hdvd : ∃ q : ℕ, 0 < q ∧ targetY.val = (q : ℤ) * targetX.val), ∀ (r : Bool), Aegis.IsReachable.is_reachable targetX targetY = Aeneas.Std.Result.ok r →
          (r = true ↔ ∃ k : ℕ, targetX.val = (2 : ℤ) ^ k)) := by
    sorry

  end AegisSpec.IsReachable
