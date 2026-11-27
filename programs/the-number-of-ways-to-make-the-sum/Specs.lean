import Aegis.NumberOfWays.Code.Funs
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Int.ModEq

/-!
# Specifications of `Aegis.NumberOfWays.number_of_ways`

LeetCode problem `the-number-of-ways-to-make-the-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace AegisSpec.NumberOfWays

def triplesOfSum (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  let r := Finset.range (m + 1)
  (r ×ˢ (r ×ˢ r)).filter fun p => p.1 + 2 * p.2.1 + 6 * p.2.2 = m

def P (m : ℤ) : ℕ :=
  if m < 0 then 0 else (triplesOfSum m.toNat).card

def C (n : ℤ) : ℕ := P n + P (n - 4) + P (n - 8)

noncomputable def aegisSeries : PowerSeries ℤ :=
  (1 + PowerSeries.X ^ 4 + PowerSeries.X ^ 8) *
    (PowerSeries.invOfUnit (1 - PowerSeries.X) (1 : ℤˣ) *
      (PowerSeries.invOfUnit (1 - PowerSeries.X ^ 2) (1 : ℤˣ) *
        PowerSeries.invOfUnit (1 - PowerSeries.X ^ 6) (1 : ℤˣ)))

noncomputable def aegisCoeff (n : ℕ) : ℤ := PowerSeries.coeff n aegisSeries

/-- The function returns a result r such that 0 <= r < 10^9 + 7 and r ≡ C(n) (mod 10^9 + 7), where C(n) = P(n) + P(n-4) + P(n-8), and for any integer m, P(m) is defined as: P(m) = 0 if m < 0, and otherwise P(m) = |{(a,b,c) ∈ ℕ³ : a + 2b + 6c = m}|. (Here ℕ denotes the non-negative integers.)
  Preconditions: 1 <= n <= 10^5, where n is the i64 parameter. -/
theorem spec_1 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 10 ^ 5) :
    ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧
      0 ≤ r.val ∧ r.val < 10 ^ 9 + 7 ∧ r.val ≡ (C n.val : ℤ) [ZMOD 10 ^ 9 + 7] := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 10 ^ 5), ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧
      0 ≤ r.val ∧ r.val < 10 ^ 9 + 7 ∧ r.val ≡ (C n.val : ℤ) [ZMOD 10 ^ 9 + 7]) := by
  sorry

/-- For every n satisfying the precondition, the function returns a result r (i.e., it does not fail, panic, or overflow).
  Preconditions: 1 <= n <= 10^5. -/
theorem spec_2 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 10 ^ 5) :
    ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 10 ^ 5), ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r) := by
  sorry

/-- Whenever the function returns a result r, it holds that 0 <= r < 10^9 + 7.
  Preconditions: 1 <= n <= 10^5. -/
theorem spec_3 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 10 ^ 5) (r : Std.I64)
    (hr : Aegis.NumberOfWays.number_of_ways n = ok r) :
    0 ≤ r.val ∧ r.val < 10 ^ 9 + 7 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 10 ^ 5) (r : Std.I64)
    (hr : Aegis.NumberOfWays.number_of_ways n = ok r), 0 ≤ r.val ∧ r.val < 10 ^ 9 + 7) := by
  sorry

/-- The function returns 1.
  Preconditions: n = 1. -/
theorem spec_4 (n : Std.I64) (hn : n.val = 1) :
    ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧ r.val = 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 1), ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧ r.val = 1) := by
  sorry

/-- The function returns 2.
  Preconditions: n = 2. -/
theorem spec_5 (n : Std.I64) (hn : n.val = 2) :
    ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧ r.val = 2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 2), ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧ r.val = 2) := by
  sorry

/-- The function returns 4.
  Preconditions: n = 4. -/
theorem spec_6 (n : Std.I64) (hn : n.val = 4) :
    ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧ r.val = 4 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 4), ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧ r.val = 4) := by
  sorry

/-- The function returns 7.
  Preconditions: n = 6. -/
theorem spec_7 (n : Std.I64) (hn : n.val = 6) :
    ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧ r.val = 7 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 6), ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧ r.val = 7) := by
  sorry

/-- The function returns 22.
  Preconditions: n = 12. -/
theorem spec_8 (n : Std.I64) (hn : n.val = 12) :
    ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧ r.val = 22 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 12), ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧ r.val = 22) := by
  sorry

/-- The function returns 121.
  Preconditions: n = 30. -/
theorem spec_9 (n : Std.I64) (hn : n.val = 30) :
    ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧ r.val = 121 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 30), ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧ r.val = 121) := by
  sorry

/-- The function returns 1276.
  Preconditions: n = 100. -/
theorem spec_10 (n : Std.I64) (hn : n.val = 100) :
    ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧ r.val = 1276 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 100), ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧ r.val = 1276) := by
  sorry

/-- The function returns 250024994.
  Preconditions: n = 100000. -/
theorem spec_11 (n : Std.I64) (hn : n.val = 100000) :
    ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧ r.val = 250024994 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 100000), ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧ r.val = 250024994) := by
  sorry

/-- The function returns r = floor(n/2) + 1 + (if n >= 4 then floor((n-4)/2) + 1 else 0).
  Preconditions: 1 <= n <= 5. -/
theorem spec_12 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 5) :
    ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧
      r.val = n.val / 2 + 1 + (if n.val ≥ 4 then (n.val - 4) / 2 + 1 else 0) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 5), ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧
      r.val = n.val / 2 + 1 + (if n.val ≥ 4 then (n.val - 4) / 2 + 1 else 0)) := by
  sorry

/-- The result r is congruent modulo 10^9 + 7 to the coefficient of x^n in the formal power series (1 + x^4 + x^8) / ((1 - x)(1 - x^2)(1 - x^6)).
  Preconditions: 1 <= n <= 10^5. -/
theorem spec_13 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 10 ^ 5) :
    ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧
      r.val ≡ aegisCoeff n.val.toNat [ZMOD 10 ^ 9 + 7] := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 10 ^ 5), ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways n = ok r ∧
      r.val ≡ aegisCoeff n.val.toNat [ZMOD 10 ^ 9 + 7]) := by
  sorry

end AegisSpec.NumberOfWays
