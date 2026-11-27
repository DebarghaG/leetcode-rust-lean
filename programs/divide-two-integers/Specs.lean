import Aegis.Divide.Code.Funs

/-!
# Specifications of `Aegis.Divide.divide`

LeetCode problem `divide-two-integers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.Divide

def clamp (x lo hi : ℤ) : ℤ :=
  if x < lo then lo else if hi < x then hi else x

def truncDiv (a b : ℤ) : ℤ :=
  if a = 0 then 0
  else if 0 < a * b then ((a.natAbs / b.natAbs : ℕ) : ℤ)
  else -((a.natAbs / b.natAbs : ℕ) : ℤ)

/-- For every dividend and divisor satisfying the preconditions, the function returns Result.ok r with r = clamp(T, -2147483648, 2147483647), where T is defined as follows: if dividend = 0 then T = 0; otherwise let q = |dividend| / |divisor| (integer division of nonnegative integers); if dividend and divisor have the same sign then T = q, and if they have opposite signs then T = -q. Here clamp(x,L,U) = L if x < L, U if x > U, and x otherwise.
  Preconditions: -2147483648 <= dividend <= 2147483647, -2147483648 <= divisor <= 2147483647, and divisor != 0. -/
theorem spec_1 (dividend divisor : Std.I64)
    (hd_low : -2147483648 ≤ dividend.val) (hd_high : dividend.val ≤ 2147483647)
    (hs_low : -2147483648 ≤ divisor.val) (hs_high : divisor.val ≤ 2147483647)
    (hs_ne : divisor.val ≠ 0) :
    ∃ r : Std.I64,
      Aegis.Divide.divide dividend divisor = ok r ∧
        r.val = clamp (truncDiv dividend.val divisor.val) (-2147483648) 2147483647 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (dividend divisor : Std.I64)
    (hd_low : -2147483648 ≤ dividend.val) (hd_high : dividend.val ≤ 2147483647)
    (hs_low : -2147483648 ≤ divisor.val) (hs_high : divisor.val ≤ 2147483647)
    (hs_ne : divisor.val ≠ 0), ∃ r : Std.I64,
      Aegis.Divide.divide dividend divisor = ok r ∧
        r.val = clamp (truncDiv dividend.val divisor.val) (-2147483648) 2147483647) := by
  sorry

/-- For every dividend and divisor satisfying the preconditions, there exists an integer r such that the function returns r; the function does not fail or panic.
  Preconditions: -2147483648 <= dividend <= 2147483647, -2147483648 <= divisor <= 2147483647, and divisor != 0. -/
theorem spec_2 (dividend divisor : Std.I64)
    (hd_low : -2147483648 ≤ dividend.val) (hd_high : dividend.val ≤ 2147483647)
    (hs_low : -2147483648 ≤ divisor.val) (hs_high : divisor.val ≤ 2147483647)
    (hs_ne : divisor.val ≠ 0) :
    ∃ r : Std.I64, Aegis.Divide.divide dividend divisor = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (dividend divisor : Std.I64)
    (hd_low : -2147483648 ≤ dividend.val) (hd_high : dividend.val ≤ 2147483647)
    (hs_low : -2147483648 ≤ divisor.val) (hs_high : divisor.val ≤ 2147483647)
    (hs_ne : divisor.val ≠ 0), ∃ r : Std.I64, Aegis.Divide.divide dividend divisor = ok r) := by
  sorry

/-- Whenever the function returns a result r for inputs satisfying the preconditions, -2147483648 <= r <= 2147483647.
  Preconditions: -2147483648 <= dividend <= 2147483647, -2147483648 <= divisor <= 2147483647, and divisor != 0. -/
theorem spec_3 (dividend divisor : Std.I64)
    (hd_low : -2147483648 ≤ dividend.val) (hd_high : dividend.val ≤ 2147483647)
    (hs_low : -2147483648 ≤ divisor.val) (hs_high : divisor.val ≤ 2147483647)
    (hs_ne : divisor.val ≠ 0)
    (r : Std.I64) (hr : Aegis.Divide.divide dividend divisor = ok r) :
    -2147483648 ≤ r.val ∧ r.val ≤ 2147483647 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (dividend divisor : Std.I64)
    (hd_low : -2147483648 ≤ dividend.val) (hd_high : dividend.val ≤ 2147483647)
    (hs_low : -2147483648 ≤ divisor.val) (hs_high : divisor.val ≤ 2147483647)
    (hs_ne : divisor.val ≠ 0)
    (r : Std.I64) (hr : Aegis.Divide.divide dividend divisor = ok r), -2147483648 ≤ r.val ∧ r.val ≤ 2147483647) := by
  sorry

/-- Whenever the function returns a result r, if dividend*divisor > 0 then r >= 0, if dividend*divisor < 0 then r <= 0, and if dividend = 0 then r = 0.
  Preconditions: -2147483648 <= dividend <= 2147483647, -2147483648 <= divisor <= 2147483647, and divisor != 0. -/
theorem spec_4 (dividend divisor : Std.I64)
    (hd_low : -2147483648 ≤ dividend.val) (hd_high : dividend.val ≤ 2147483647)
    (hs_low : -2147483648 ≤ divisor.val) (hs_high : divisor.val ≤ 2147483647)
    (hs_ne : divisor.val ≠ 0)
    (r : Std.I64) (hr : Aegis.Divide.divide dividend divisor = ok r) :
    (0 < dividend.val * divisor.val → 0 ≤ r.val) ∧
      (dividend.val * divisor.val < 0 → r.val ≤ 0) ∧
        (dividend.val = 0 → r.val = 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (dividend divisor : Std.I64)
    (hd_low : -2147483648 ≤ dividend.val) (hd_high : dividend.val ≤ 2147483647)
    (hs_low : -2147483648 ≤ divisor.val) (hs_high : divisor.val ≤ 2147483647)
    (hs_ne : divisor.val ≠ 0)
    (r : Std.I64) (hr : Aegis.Divide.divide dividend divisor = ok r), (0 < dividend.val * divisor.val → 0 ≤ r.val) ∧
      (dividend.val * divisor.val < 0 → r.val ≤ 0) ∧
        (dividend.val = 0 → r.val = 0)) := by
  sorry

/-- Whenever the function returns a result r, |r| <= |dividend|.
  Preconditions: -2147483648 <= dividend <= 2147483647, -2147483648 <= divisor <= 2147483647, and divisor != 0. -/
theorem spec_5 (dividend divisor : Std.I64)
    (hd_low : -2147483648 ≤ dividend.val) (hd_high : dividend.val ≤ 2147483647)
    (hs_low : -2147483648 ≤ divisor.val) (hs_high : divisor.val ≤ 2147483647)
    (hs_ne : divisor.val ≠ 0)
    (r : Std.I64) (hr : Aegis.Divide.divide dividend divisor = ok r) :
    r.val.natAbs ≤ dividend.val.natAbs := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (dividend divisor : Std.I64)
    (hd_low : -2147483648 ≤ dividend.val) (hd_high : dividend.val ≤ 2147483647)
    (hs_low : -2147483648 ≤ divisor.val) (hs_high : divisor.val ≤ 2147483647)
    (hs_ne : divisor.val ≠ 0)
    (r : Std.I64) (hr : Aegis.Divide.divide dividend divisor = ok r), r.val.natAbs ≤ dividend.val.natAbs) := by
  sorry

/-- For every integer c >= 1 such that -2147483648 <= c*dividend <= 2147483647 and -2147483648 <= c*divisor <= 2147483647, if the function returns r for (dividend, divisor) and returns r' for (c*dividend, c*divisor), then r = r'.
  Preconditions: -2147483648 <= dividend <= 2147483647, -2147483648 <= divisor <= 2147483647, and divisor != 0. -/
theorem spec_6 (dividend divisor : Std.I64) (c : ℤ)
    (hd_low : -2147483648 ≤ dividend.val) (hd_high : dividend.val ≤ 2147483647)
    (hs_low : -2147483648 ≤ divisor.val) (hs_high : divisor.val ≤ 2147483647)
    (hs_ne : divisor.val ≠ 0)
    (hc : 1 ≤ c)
    (hmul_d_low : -2147483648 ≤ c * dividend.val)
    (hmul_d_high : c * dividend.val ≤ 2147483647)
    (hmul_s_low : -2147483648 ≤ c * divisor.val)
    (hmul_s_high : c * divisor.val ≤ 2147483647)
    (r r' : Std.I64)
    (hr : Aegis.Divide.divide dividend divisor = ok r)
    (hr' : Aegis.Divide.divide (Std.I64.ofInt (c * dividend.val) (by scalar_tac))
        (Std.I64.ofInt (c * divisor.val) (by scalar_tac)) = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (dividend divisor : Std.I64) (c : ℤ)
    (hd_low : -2147483648 ≤ dividend.val) (hd_high : dividend.val ≤ 2147483647)
    (hs_low : -2147483648 ≤ divisor.val) (hs_high : divisor.val ≤ 2147483647)
    (hs_ne : divisor.val ≠ 0)
    (hc : 1 ≤ c)
    (hmul_d_low : -2147483648 ≤ c * dividend.val)
    (hmul_d_high : c * dividend.val ≤ 2147483647)
    (hmul_s_low : -2147483648 ≤ c * divisor.val)
    (hmul_s_high : c * divisor.val ≤ 2147483647)
    (r r' : Std.I64)
    (hr : Aegis.Divide.divide dividend divisor = ok r)
    (hr' : Aegis.Divide.divide (Std.I64.ofInt (c * dividend.val) (by scalar_tac))
        (Std.I64.ofInt (c * divisor.val) (by scalar_tac)) = ok r'), r.val = r'.val) := by
  sorry

/-- If the function returns r for (dividend, divisor) and returns r' for (-dividend, divisor), then r' = -r.
  Preconditions: -2147483648 <= dividend <= 2147483647, -2147483648 <= divisor <= 2147483647, divisor != 0, and dividend != -2147483648. -/
theorem spec_7 (dividend divisor : Std.I64)
    (hd_low : -2147483648 ≤ dividend.val) (hd_high : dividend.val ≤ 2147483647)
    (hs_low : -2147483648 ≤ divisor.val) (hs_high : divisor.val ≤ 2147483647)
    (hs_ne : divisor.val ≠ 0)
    (hd_ne : dividend.val ≠ -2147483648)
    (r r' : Std.I64)
    (hr : Aegis.Divide.divide dividend divisor = ok r)
    (hr' : Aegis.Divide.divide (Std.I64.ofInt (-dividend.val) (by scalar_tac)) divisor = ok r') :
    r'.val = -r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (dividend divisor : Std.I64)
    (hd_low : -2147483648 ≤ dividend.val) (hd_high : dividend.val ≤ 2147483647)
    (hs_low : -2147483648 ≤ divisor.val) (hs_high : divisor.val ≤ 2147483647)
    (hs_ne : divisor.val ≠ 0)
    (hd_ne : dividend.val ≠ -2147483648)
    (r r' : Std.I64)
    (hr : Aegis.Divide.divide dividend divisor = ok r)
    (hr' : Aegis.Divide.divide (Std.I64.ofInt (-dividend.val) (by scalar_tac)) divisor = ok r'), r'.val = -r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists an integer rem such that dividend = r*divisor + rem, |rem| < |divisor|, and either rem = 0 or rem has the same sign as dividend.
  Preconditions: -2147483648 <= dividend <= 2147483647, -2147483648 <= divisor <= 2147483647, divisor != 0, and not (dividend = -2147483648 and divisor = -1). -/
theorem spec_8 (dividend divisor : Std.I64)
    (hd_low : -2147483648 ≤ dividend.val) (hd_high : dividend.val ≤ 2147483647)
    (hs_low : -2147483648 ≤ divisor.val) (hs_high : divisor.val ≤ 2147483647)
    (hs_ne : divisor.val ≠ 0)
    (hnot : ¬ (dividend.val = -2147483648 ∧ divisor.val = -1))
    (r : Std.I64) (hr : Aegis.Divide.divide dividend divisor = ok r) :
    ∃ rem : ℤ,
      dividend.val = r.val * divisor.val + rem ∧
        rem.natAbs < divisor.val.natAbs ∧
          (rem = 0 ∨ (0 < rem ∧ 0 < dividend.val) ∨ (rem < 0 ∧ dividend.val < 0)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (dividend divisor : Std.I64)
    (hd_low : -2147483648 ≤ dividend.val) (hd_high : dividend.val ≤ 2147483647)
    (hs_low : -2147483648 ≤ divisor.val) (hs_high : divisor.val ≤ 2147483647)
    (hs_ne : divisor.val ≠ 0)
    (hnot : ¬ (dividend.val = -2147483648 ∧ divisor.val = -1))
    (r : Std.I64) (hr : Aegis.Divide.divide dividend divisor = ok r), ∃ rem : ℤ,
      dividend.val = r.val * divisor.val + rem ∧
        rem.natAbs < divisor.val.natAbs ∧
          (rem = 0 ∨ (0 < rem ∧ 0 < dividend.val) ∨ (rem < 0 ∧ dividend.val < 0))) := by
  sorry

end AegisSpec.Divide
