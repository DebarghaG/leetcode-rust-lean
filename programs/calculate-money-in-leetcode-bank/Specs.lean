import Aegis.TotalMoney.Code.Funs

/-!
# Specifications of `Aegis.TotalMoney.total_money`

LeetCode problem `calculate-money-in-leetcode-bank`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.TotalMoney

def i64OfInt (x : ℤ) : Aeneas.Std.I64 := ⟨BitVec.ofInt 64 x⟩

/-- The function returns a result r and r = Σ_{d=1}^{n} ( ((d-1) / 7) + 1 + ((d-1) mod 7) ), where / is integer division (floor) and mod is the remainder, so 0 <= (d-1) mod 7 < 7.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_1 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
    ∃ r : Aeneas.Std.I64, Aegis.TotalMoney.total_money n = ok r ∧
      r.val = ∑ d ∈ Finset.Icc (1 : ℕ) n.val.toNat,
        (((d : ℤ) - 1) / 7 + 1 + ((d : ℤ) - 1) % 7) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∃ r : Aeneas.Std.I64, Aegis.TotalMoney.total_money n = ok r ∧
      r.val = ∑ d ∈ Finset.Icc (1 : ℕ) n.val.toNat,
        (((d : ℤ) - 1) / 7 + 1 + ((d : ℤ) - 1) % 7)) := by
  sorry

/-- Let q = n / 7 and rem = n mod 7, where / is integer division (floor) and mod is the remainder (0 <= rem < 7). The function returns a result r and r = 7*q*(q+1)/2 + 21*q + rem*(q+1) + rem*(rem-1)/2. The divisions by 2 are exact.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_2 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
    ∃ r : Aeneas.Std.I64, Aegis.TotalMoney.total_money n = ok r ∧
      r.val = (let q := n.val / 7
               let rem := n.val % 7
               7 * q * (q + 1) / 2 + 21 * q + rem * (q + 1) + rem * (rem - 1) / 2) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∃ r : Aeneas.Std.I64, Aegis.TotalMoney.total_money n = ok r ∧
      r.val = (let q := n.val / 7
               let rem := n.val % 7
               7 * q * (q + 1) / 2 + 21 * q + rem * (q + 1) + rem * (rem - 1) / 2)) := by
  sorry

/-- The function returns a result r and r >= n.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_3 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
    ∃ r : Aeneas.Std.I64, Aegis.TotalMoney.total_money n = ok r ∧ n.val ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∃ r : Aeneas.Std.I64, Aegis.TotalMoney.total_money n = ok r ∧ n.val ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= 74926.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_4 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
    ∃ r : Aeneas.Std.I64, Aegis.TotalMoney.total_money n = ok r ∧ r.val ≤ 74926 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∃ r : Aeneas.Std.I64, Aegis.TotalMoney.total_money n = ok r ∧ r.val ≤ 74926) := by
  sorry

/-- Let r_n be the result returned by total_money(n) and r_{n-1} be the result returned by total_money(n-1). Then r_n - r_{n-1} = ((n-1) / 7) + 1 + ((n-1) mod 7), with / and mod as integer division and remainder.
  Preconditions: 2 <= n <= 1000. -/
theorem spec_5 (n : Aeneas.Std.I64) (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 1000) :
    ∃ rn rprev : Aeneas.Std.I64,
      Aegis.TotalMoney.total_money n = ok rn ∧
      Aegis.TotalMoney.total_money (i64OfInt (n.val - 1)) = ok rprev ∧
      rn.val - rprev.val = (n.val - 1) / 7 + 1 + (n.val - 1) % 7 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 1000), ∃ rn rprev : Aeneas.Std.I64,
      Aegis.TotalMoney.total_money n = ok rn ∧
      Aegis.TotalMoney.total_money (i64OfInt (n.val - 1)) = ok rprev ∧
      rn.val - rprev.val = (n.val - 1) / 7 + 1 + (n.val - 1) % 7) := by
  sorry

/-- Let r_n = total_money(n) and r_m = total_money(m). Then r_m > r_n.
  Preconditions: 1 <= n < m <= 1000. -/
theorem spec_6 (n m : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hnm : n.val < m.val)
    (hm : m.val ≤ 1000) :
    ∃ rn rm : Aeneas.Std.I64,
      Aegis.TotalMoney.total_money n = ok rn ∧
      Aegis.TotalMoney.total_money m = ok rm ∧
      rn.val < rm.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n m : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hnm : n.val < m.val)
    (hm : m.val ≤ 1000), ∃ rn rm : Aeneas.Std.I64,
      Aegis.TotalMoney.total_money n = ok rn ∧
      Aegis.TotalMoney.total_money m = ok rm ∧
      rn.val < rm.val) := by
  sorry

/-- Let r = total_money(7*k) and r' = total_money(7*(k-1)). Then r - r' = 7*k + 21.
  Preconditions: 2 <= k and 7*k <= 1000. -/
theorem spec_7 (k : ℤ) (hk1 : 2 ≤ k) (hk2 : 7 * k ≤ 1000) :
    ∃ r r' : Aeneas.Std.I64,
      Aegis.TotalMoney.total_money (i64OfInt (7 * k)) = ok r ∧
      Aegis.TotalMoney.total_money (i64OfInt (7 * (k - 1))) = ok r' ∧
      r.val - r'.val = 7 * k + 21 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (k : ℤ) (hk1 : 2 ≤ k) (hk2 : 7 * k ≤ 1000), ∃ r r' : Aeneas.Std.I64,
      Aegis.TotalMoney.total_money (i64OfInt (7 * k)) = ok r ∧
      Aegis.TotalMoney.total_money (i64OfInt (7 * (k - 1))) = ok r' ∧
      r.val - r'.val = 7 * k + 21) := by
  sorry

/-- Let r = total_money(n+7) and r' = total_money(n). Then r - r' = 7*(n/7) + 28 + (n mod 7), where / is integer division and mod is remainder.
  Preconditions: 1 <= n and n+7 <= 1000. -/
theorem spec_8 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn7 : n.val + 7 ≤ 1000) :
    ∃ r r' : Aeneas.Std.I64,
      Aegis.TotalMoney.total_money (i64OfInt (n.val + 7)) = ok r ∧
      Aegis.TotalMoney.total_money n = ok r' ∧
      r.val - r'.val = 7 * (n.val / 7) + 28 + n.val % 7 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn7 : n.val + 7 ≤ 1000), ∃ r r' : Aeneas.Std.I64,
      Aegis.TotalMoney.total_money (i64OfInt (n.val + 7)) = ok r ∧
      Aegis.TotalMoney.total_money n = ok r' ∧
      r.val - r'.val = 7 * (n.val / 7) + 28 + n.val % 7) := by
  sorry

/-- The function returns a result (it does not fail).
  Preconditions: 1 <= n <= 1000. -/
theorem spec_9 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
    ∃ r : Aeneas.Std.I64, Aegis.TotalMoney.total_money n = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∃ r : Aeneas.Std.I64, Aegis.TotalMoney.total_money n = ok r) := by
  sorry

end AegisSpec.TotalMoney
