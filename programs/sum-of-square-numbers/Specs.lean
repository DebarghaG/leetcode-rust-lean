import Aegis.JudgeSquareSum.Code.Funs

/-!
# Specifications of `Aegis.JudgeSquareSum.judge_square_sum`

LeetCode problem `sum-of-square-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open Aegis.JudgeSquareSum

namespace AegisSpec.JudgeSquareSum

/-- Whenever judge_square_sum(c) returns a result r, r = true if and only if there exist integers a and b such that a*a + b*b = c.
  Preconditions: c is an integer with 0 <= c <= 2147483647 (2^31 - 1). -/
theorem spec_1 (c : Std.I64) (r : Bool)
    (hc0 : 0 ≤ c.val) (hc1 : c.val ≤ 2147483647)
    (hr : judge_square_sum c = ok r) :
    (r = true ↔ ∃ a b : ℤ, a * a + b * b = c.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (c : Std.I64) (r : Bool)
    (hc0 : 0 ≤ c.val) (hc1 : c.val ≤ 2147483647)
    (hr : judge_square_sum c = ok r), (r = true ↔ ∃ a b : ℤ, a * a + b * b = c.val)) := by
  sorry

/-- The function judge_square_sum(c) returns a result r; it does not fail, panic, or overflow.
  Preconditions: c is an integer with 0 <= c <= 2147483647 (2^31 - 1). -/
theorem spec_2 (c : Std.I64)
    (hc0 : 0 ≤ c.val) (hc1 : c.val ≤ 2147483647) :
    ∃ r : Bool, judge_square_sum c = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (c : Std.I64)
    (hc0 : 0 ≤ c.val) (hc1 : c.val ≤ 2147483647), ∃ r : Bool, judge_square_sum c = ok r) := by
  sorry

/-- Whenever judge_square_sum(c) returns a result r and r = true, there exist integers a and b such that 0 <= a <= b <= 46340 and a*a + b*b = c.
  Preconditions: c is an integer with 0 <= c <= 2147483647 (2^31 - 1). -/
theorem spec_3 (c : Std.I64) (r : Bool)
    (hc0 : 0 ≤ c.val) (hc1 : c.val ≤ 2147483647)
    (hr : judge_square_sum c = ok r) (htrue : r = true) :
    ∃ a b : ℤ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 46340 ∧ a * a + b * b = c.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (c : Std.I64) (r : Bool)
    (hc0 : 0 ≤ c.val) (hc1 : c.val ≤ 2147483647)
    (hr : judge_square_sum c = ok r) (htrue : r = true), ∃ a b : ℤ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 46340 ∧ a * a + b * b = c.val) := by
  sorry

/-- Whenever judge_square_sum(c) returns a result r, r = true.
  Preconditions: c is an integer with 0 <= c <= 2147483647 (2^31 - 1) and there exists an integer k such that c = k*k. -/
theorem spec_4 (c : Std.I64) (r : Bool)
    (hc0 : 0 ≤ c.val) (hc1 : c.val ≤ 2147483647)
    (hsq : ∃ k : ℤ, c.val = k * k)
    (hr : judge_square_sum c = ok r) :
    r = true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (c : Std.I64) (r : Bool)
    (hc0 : 0 ≤ c.val) (hc1 : c.val ≤ 2147483647)
    (hsq : ∃ k : ℤ, c.val = k * k)
    (hr : judge_square_sum c = ok r), r = true) := by
  sorry

/-- Whenever judge_square_sum(c) returns a result r, r = false.
  Preconditions: c is an integer with 0 <= c <= 2147483647 (2^31 - 1) and c mod 4 = 3. -/
theorem spec_5 (c : Std.I64) (r : Bool)
    (hc0 : 0 ≤ c.val) (hc1 : c.val ≤ 2147483647)
    (hmod : c.val % 4 = 3)
    (hr : judge_square_sum c = ok r) :
    r = false := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (c : Std.I64) (r : Bool)
    (hc0 : 0 ≤ c.val) (hc1 : c.val ≤ 2147483647)
    (hmod : c.val % 4 = 3)
    (hr : judge_square_sum c = ok r), r = false) := by
  sorry

/-- Whenever judge_square_sum(c) returns a result r_c and judge_square_sum(c/4) returns a result r_d, we have r_c = r_d.
  Preconditions: c is an integer with 0 <= c <= 2147483647 (2^31 - 1) and c mod 4 = 0. -/
theorem spec_6 (c d : Std.I64) (r_c r_d : Bool)
    (hc0 : 0 ≤ c.val) (hc1 : c.val ≤ 2147483647)
    (hmod : c.val % 4 = 0) (hd : d.val = c.val / 4)
    (hrc : judge_square_sum c = ok r_c) (hrd : judge_square_sum d = ok r_d) :
    r_c = r_d := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (c d : Std.I64) (r_c r_d : Bool)
    (hc0 : 0 ≤ c.val) (hc1 : c.val ≤ 2147483647)
    (hmod : c.val % 4 = 0) (hd : d.val = c.val / 4)
    (hrc : judge_square_sum c = ok r_c) (hrd : judge_square_sum d = ok r_d), r_c = r_d) := by
  sorry

/-- Whenever judge_square_sum(c) returns a result r_c and judge_square_sum(c*k*k) returns a result r_m, if r_c = true then r_m = true.
  Preconditions: c is an integer with 0 <= c <= 2147483647 (2^31 - 1), k is an integer with 0 <= k, and c*k*k <= 2147483647. -/
theorem spec_7 (c m : Std.I64) (k : ℤ) (r_c r_m : Bool)
    (hc0 : 0 ≤ c.val) (hc1 : c.val ≤ 2147483647)
    (hk : 0 ≤ k) (hmul : c.val * k * k ≤ 2147483647)
    (hm : m.val = c.val * k * k)
    (hrc : judge_square_sum c = ok r_c) (hrm : judge_square_sum m = ok r_m)
    (htrue : r_c = true) :
    r_m = true := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (c m : Std.I64) (k : ℤ) (r_c r_m : Bool)
    (hc0 : 0 ≤ c.val) (hc1 : c.val ≤ 2147483647)
    (hk : 0 ≤ k) (hmul : c.val * k * k ≤ 2147483647)
    (hm : m.val = c.val * k * k)
    (hrc : judge_square_sum c = ok r_c) (hrm : judge_square_sum m = ok r_m)
    (htrue : r_c = true), r_m = true) := by
  sorry

/-- Whenever judge_square_sum(c) returns a result r and r = true, we have c mod 4 = 1.
  Preconditions: c is an integer with 0 <= c <= 2147483647 (2^31 - 1) and c mod 2 = 1. -/
theorem spec_8 (c : Std.I64) (r : Bool)
    (hc0 : 0 ≤ c.val) (hc1 : c.val ≤ 2147483647)
    (hodd : c.val % 2 = 1)
    (hr : judge_square_sum c = ok r) (htrue : r = true) :
    c.val % 4 = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (c : Std.I64) (r : Bool)
    (hc0 : 0 ≤ c.val) (hc1 : c.val ≤ 2147483647)
    (hodd : c.val % 2 = 1)
    (hr : judge_square_sum c = ok r) (htrue : r = true), c.val % 4 = 1) := by
  sorry

end AegisSpec.JudgeSquareSum
