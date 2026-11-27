import Aegis.GetMoneyAmount.Code.Funs

/-!
# Specifications of `Aegis.GetMoneyAmount.get_money_amount`

LeetCode problem `guess-number-higher-or-lower-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetMoneyAmount

noncomputable def C (a b : ℤ) : ℤ :=
  if h : a < b then
    (Finset.range ((b - a).toNat + 1)).attach.inf'
      (by simp)
      (fun k => (a + (k.val : ℤ)) +
        max (C a (a + (k.val : ℤ) - 1)) (C (a + (k.val : ℤ) + 1) b))
  else 0
termination_by (b - a).toNat
decreasing_by
  all_goals
    have hpos : 0 < b - a := by omega
    have hn : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg hpos.le
    have hmem : k.val < (b - a).toNat + 1 := Finset.mem_range.mp k.2
    have _hcast : (k.val : ℤ) ≤ ((b - a).toNat : ℤ) := by
      have h1 : k.val ≤ (b - a).toNat := Nat.lt_succ_iff.mp hmem
      exact_mod_cast h1
    have _hk : (k.val : ℤ) ≤ b - a := by omega
    rw [Int.toNat_lt_toNat hpos]
    omega

theorem C_of_ge {a b : ℤ} (h : b ≤ a) : C a b = 0 := by
  rw [C]
  simp [show ¬ a < b by omega]

/-- Whenever get_money_amount(n) returns a result r, r = C(1,n), where C is defined for integer intervals as follows. Extend C by C(a,b) = 0 whenever a >= b (empty or singleton interval). For a < b, C(a,b) = min over integers x with a <= x <= b of ( x + max(C(a,x-1), C(x+1,b)) ).
  Preconditions: n is an integer with 1 <= n <= 200. -/
theorem spec_1 (n r : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 200)
    (h : Aegis.GetMoneyAmount.get_money_amount n = ok r) : r.val = C 1 n.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n r : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 200)
    (h : Aegis.GetMoneyAmount.get_money_amount n = ok r), r.val = C 1 n.val) := by
  sorry

/-- For every such n, get_money_amount(n) returns a result (it does not fail, overflow, or panic).
  Preconditions: n is an integer with 1 <= n <= 200. -/
theorem spec_2 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 200) :
    ∃ r, Aegis.GetMoneyAmount.get_money_amount n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 200), ∃ r, Aegis.GetMoneyAmount.get_money_amount n = ok r) := by
  sorry

/-- Whenever get_money_amount(n) returns a result r, r = 0 if and only if n = 1.
  Preconditions: n is an integer with 1 <= n <= 200. -/
theorem spec_3 (n r : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 200)
    (h : Aegis.GetMoneyAmount.get_money_amount n = ok r) : r.val = 0 ↔ n.val = 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n r : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 200)
    (h : Aegis.GetMoneyAmount.get_money_amount n = ok r), r.val = 0 ↔ n.val = 1) := by
  sorry

/-- Whenever get_money_amount(n) returns a result r, r >= n - 1.
  Preconditions: n is an integer with 1 <= n <= 200. -/
theorem spec_4 (n r : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 200)
    (h : Aegis.GetMoneyAmount.get_money_amount n = ok r) : r.val ≥ n.val - 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n r : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 200)
    (h : Aegis.GetMoneyAmount.get_money_amount n = ok r), r.val ≥ n.val - 1) := by
  sorry

/-- Whenever get_money_amount(n) returns a result r, r <= n*(n-1)/2.
  Preconditions: n is an integer with 1 <= n <= 200. -/
theorem spec_5 (n r : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 200)
    (h : Aegis.GetMoneyAmount.get_money_amount n = ok r) :
    r.val ≤ n.val * (n.val - 1) / 2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n r : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 200)
    (h : Aegis.GetMoneyAmount.get_money_amount n = ok r), r.val ≤ n.val * (n.val - 1) / 2) := by
  sorry

/-- Whenever get_money_amount(n) returns r_n and get_money_amount(m) returns r_m, we have r_n <= r_m.
  Preconditions: n and m are integers with 1 <= n <= m <= 200. -/
theorem spec_6 (n m rn rm : Std.I64) (hn1 : 1 ≤ n.val) (hnm : n.val ≤ m.val)
    (hm2 : m.val ≤ 200) (hn : Aegis.GetMoneyAmount.get_money_amount n = ok rn)
    (hm : Aegis.GetMoneyAmount.get_money_amount m = ok rm) : rn.val ≤ rm.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n m rn rm : Std.I64) (hn1 : 1 ≤ n.val) (hnm : n.val ≤ m.val)
    (hm2 : m.val ≤ 200) (hn : Aegis.GetMoneyAmount.get_money_amount n = ok rn)
    (hm : Aegis.GetMoneyAmount.get_money_amount m = ok rm), rn.val ≤ rm.val) := by
  sorry

/-- Whenever get_money_amount(n) returns a result r, r = 1.
  Preconditions: n = 2. -/
theorem spec_7 (n r : Std.I64) (hn : n.val = 2)
    (h : Aegis.GetMoneyAmount.get_money_amount n = ok r) : r.val = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n r : Std.I64) (hn : n.val = 2)
    (h : Aegis.GetMoneyAmount.get_money_amount n = ok r), r.val = 1) := by
  sorry

/-- Whenever get_money_amount(n) returns a result r, r = 16.
  Preconditions: n = 10. -/
theorem spec_8 (n r : Std.I64) (hn : n.val = 10)
    (h : Aegis.GetMoneyAmount.get_money_amount n = ok r) : r.val = 16 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n r : Std.I64) (hn : n.val = 10)
    (h : Aegis.GetMoneyAmount.get_money_amount n = ok r), r.val = 16) := by
  sorry

/-- Whenever get_money_amount(n) returns a result r, r = 30.
  Preconditions: n = 15. -/
theorem spec_9 (n r : Std.I64) (hn : n.val = 15)
    (h : Aegis.GetMoneyAmount.get_money_amount n = ok r) : r.val = 30 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n r : Std.I64) (hn : n.val = 15)
    (h : Aegis.GetMoneyAmount.get_money_amount n = ok r), r.val = 30) := by
  sorry

/-- Whenever get_money_amount(n) returns a result r, r = 400.
  Preconditions: n = 100. -/
theorem spec_10 (n r : Std.I64) (hn : n.val = 100)
    (h : Aegis.GetMoneyAmount.get_money_amount n = ok r) : r.val = 400 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n r : Std.I64) (hn : n.val = 100)
    (h : Aegis.GetMoneyAmount.get_money_amount n = ok r), r.val = 400) := by
  sorry

/-- Whenever get_money_amount(n) returns a result r, r = 952.
  Preconditions: n = 200. -/
theorem spec_11 (n r : Std.I64) (hn : n.val = 200)
    (h : Aegis.GetMoneyAmount.get_money_amount n = ok r) : r.val = 952 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n r : Std.I64) (hn : n.val = 200)
    (h : Aegis.GetMoneyAmount.get_money_amount n = ok r), r.val = 952) := by
  sorry

end AegisSpec.GetMoneyAmount
