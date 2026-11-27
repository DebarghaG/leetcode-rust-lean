import Aegis.BrokenCalc.Code.Funs

/-!
# Specifications of `Aegis.BrokenCalc.broken_calc`

LeetCode problem `broken-calculator`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.BrokenCalc

def Allowed (x y : Int) : Prop := y = 2 * x ∨ y = x - 1

def RevAllowed (y z : Int) : Prop := z = y + 1 ∨ (y % 2 = 0 ∧ z = y / 2)

def Reach (R : Int → Int → Prop) (n : Nat) (a b : Int) : Prop :=
  ∃ p : Nat → Int, p 0 = a ∧ p n = b ∧ ∀ i, i < n → R (p i) (p (i + 1))

def IsMinLen (R : Int → Int → Prop) (r : Nat) (a b : Int) : Prop :=
  Reach R r a b ∧ ∀ m : Nat, Reach R m a b → r ≤ m

noncomputable def least (P : Nat → Prop) : Nat := by
  classical
  exact if h : ∃ n, P n then Nat.find h else 0

noncomputable def d (a b : Int) : Nat := least (fun n => Reach Allowed n a b)

noncomputable def leastK (s t : Int) : Nat := least (fun k => t ≤ s * (2 : Int) ^ k)

/-- Whenever the function returns a result r, r is the minimum length of a finite sequence of allowed operations that starts with startValue and ends with target, where an allowed operation on an integer x is either replacing x by 2*x or replacing x by x-1. Empty sequences are allowed, so if startValue = target the minimum length is 0.
  Preconditions: startValue and target are integers with 1 <= startValue <= 10^9 and 1 <= target <= 10^9. -/
theorem spec_1 (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9) :
    ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      IsMinLen Allowed r.val.toNat startValue.val target.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9), ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      IsMinLen Allowed r.val.toNat startValue.val target.val) := by
  sorry

/-- For every startValue and target satisfying the preconditions, the function returns a result r (it does not overflow, panic, or get stuck).
  Preconditions: startValue and target are integers with 1 <= startValue <= 10^9 and 1 <= target <= 10^9. -/
theorem spec_2 (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9) :
    ∃ r, Aegis.BrokenCalc.broken_calc startValue target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9), ∃ r, Aegis.BrokenCalc.broken_calc startValue target = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = startValue - target.
  Preconditions: startValue and target are integers with 1 <= startValue <= 10^9, 1 <= target <= 10^9, and startValue >= target. -/
theorem spec_3 (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9)
    (hge : target.val ≤ startValue.val) :
    ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      r.val = startValue.val - target.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9)
    (hge : target.val ≤ startValue.val), ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      r.val = startValue.val - target.val) := by
  sorry

/-- Whenever the function returns a result r, r = k.
  Preconditions: startValue and target are integers with 1 <= startValue <= 10^9, 1 <= target <= 10^9, and there exists an integer k >= 0 such that target = startValue * 2^k. -/
theorem spec_4 (startValue target : Std.I64) (k : Nat)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9)
    (hk : target.val = startValue.val * (2 : Int) ^ k) :
    ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      r.val = (k : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (startValue target : Std.I64) (k : Nat)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9)
    (hk : target.val = startValue.val * (2 : Int) ^ k), ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      r.val = (k : Int)) := by
  sorry

/-- Whenever the function returns a result r, there exists a finite sequence of exactly r allowed operations that starts with startValue and ends with target, where an allowed operation on an integer x is either replacing x by 2*x or replacing x by x-1.
  Preconditions: startValue and target are integers with 1 <= startValue <= 10^9 and 1 <= target <= 10^9. -/
theorem spec_5 (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9) :
    ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      Reach Allowed r.val.toNat startValue.val target.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9), ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      Reach Allowed r.val.toNat startValue.val target.val) := by
  sorry

/-- Whenever the function returns a result r, there is no finite sequence of allowed operations of length less than r that starts with startValue and ends with target, where an allowed operation on an integer x is either replacing x by 2*x or replacing x by x-1.
  Preconditions: startValue and target are integers with 1 <= startValue <= 10^9 and 1 <= target <= 10^9. -/
theorem spec_6 (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9) :
    ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      ∀ m : Nat, m < r.val.toNat → ¬ Reach Allowed m startValue.val target.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9), ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      ∀ m : Nat, m < r.val.toNat → ¬ Reach Allowed m startValue.val target.val) := by
  sorry

/-- Whenever the function returns a result r, r = 1 + d(startValue, target + 1), where d(a,b) is the minimum length of a finite sequence of allowed operations from the integer a to the integer b, and an allowed operation on an integer x is either replacing x by 2*x or replacing x by x-1.
  Preconditions: startValue and target are integers with 1 <= startValue <= 10^9, 1 <= target <= 10^9, startValue < target, and target is odd. -/
theorem spec_7 (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9)
    (hlt : startValue.val < target.val) (hodd : target.val % 2 = 1) :
    ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      r.val = 1 + (d startValue.val (target.val + 1) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9)
    (hlt : startValue.val < target.val) (hodd : target.val % 2 = 1), ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      r.val = 1 + (d startValue.val (target.val + 1) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 1 + min(d(startValue, target / 2), d(startValue, target + 1)), where target / 2 is exact integer division (target is even), d(a,b) is the minimum length of a finite sequence of allowed operations from the integer a to the integer b, and an allowed operation on an integer x is either replacing x by 2*x or replacing x by x-1.
  Preconditions: startValue and target are integers with 1 <= startValue <= 10^9, 1 <= target <= 10^9, startValue < target, and target is even. -/
theorem spec_8 (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9)
    (hlt : startValue.val < target.val) (heven : target.val % 2 = 0) :
    ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      r.val = 1 + ((min (d startValue.val (target.val / 2))
        (d startValue.val (target.val + 1)) : Nat) : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9)
    (hlt : startValue.val < target.val) (heven : target.val % 2 = 0), ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      r.val = 1 + ((min (d startValue.val (target.val / 2))
        (d startValue.val (target.val + 1)) : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, startValue * 2^r >= target, where 2^r is the mathematical integer power and the multiplication is mathematical integer multiplication, not machine arithmetic.
  Preconditions: startValue and target are integers with 1 <= startValue <= 10^9, 1 <= target <= 10^9, and startValue < target. -/
theorem spec_9 (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9)
    (hlt : startValue.val < target.val) :
    ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      target.val ≤ startValue.val * (2 : Int) ^ r.val.toNat := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9)
    (hlt : startValue.val < target.val), ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      target.val ≤ startValue.val * (2 : Int) ^ r.val.toNat) := by
  sorry

/-- Let k be the least nonnegative integer such that startValue * 2^k >= target. Whenever the function returns a result r, r <= k + startValue * 2^k - target, where all arithmetic in this expression is mathematical integer arithmetic.
  Preconditions: startValue and target are integers with 1 <= startValue <= 10^9, 1 <= target <= 10^9, and startValue < target. -/
theorem spec_10 (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9)
    (hlt : startValue.val < target.val) :
    ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      r.val ≤ (leastK startValue.val target.val : Int) +
        (startValue.val * (2 : Int) ^ leastK startValue.val target.val - target.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9)
    (hlt : startValue.val < target.val), ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      r.val ≤ (leastK startValue.val target.val : Int) +
        (startValue.val * (2 : Int) ^ leastK startValue.val target.val - target.val)) := by
  sorry

/-- Whenever the function returns a result r, r is the minimum length of a finite sequence of reverse operations that starts at target and ends at startValue, where a reverse operation on an integer y is either replacing y by y+1 or, when y is even, replacing y by y/2 (integer division).
  Preconditions: startValue and target are integers with 1 <= startValue <= 10^9 and 1 <= target <= 10^9. -/
theorem spec_11 (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9) :
    ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      IsMinLen RevAllowed r.val.toNat target.val startValue.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9), ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      IsMinLen RevAllowed r.val.toNat target.val startValue.val) := by
  sorry

/-- Whenever the function returns a result r, every sequence of exactly r allowed operations that starts with startValue and ends with target uses only decrement operations (it contains no doubling operation).
  Preconditions: startValue and target are integers with 1 <= startValue <= 10^9, 1 <= target <= 10^9, and startValue > target. -/
theorem spec_12 (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9)
    (hgt : target.val < startValue.val) :
    ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      ∀ (p : Nat → Int), p 0 = startValue.val → p r.val.toNat = target.val →
        (∀ i, i < r.val.toNat → Allowed (p i) (p (i + 1))) →
        ∀ i, i < r.val.toNat → p (i + 1) = p i - 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (startValue target : Std.I64)
    (hstart_lo : 1 ≤ startValue.val) (hstart_hi : startValue.val ≤ 10 ^ 9)
    (htarget_lo : 1 ≤ target.val) (htarget_hi : target.val ≤ 10 ^ 9)
    (hgt : target.val < startValue.val), ∀ r, Aegis.BrokenCalc.broken_calc startValue target = ok r →
      ∀ (p : Nat → Int), p 0 = startValue.val → p r.val.toNat = target.val →
        (∀ i, i < r.val.toNat → Allowed (p i) (p (i + 1))) →
        ∀ i, i < r.val.toNat → p (i + 1) = p i - 1) := by
  sorry

end AegisSpec.BrokenCalc
