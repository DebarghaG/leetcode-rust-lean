import Aegis.BulbSwitch.Code.Funs

/-!
# Specifications of `Aegis.BulbSwitch.bulb_switch`

LeetCode problem `bulb-switcher`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.BulbSwitch

open Aegis.BulbSwitch (bulb_switch)

def isSquare (z : ℤ) : Prop := ∃ k : ℤ, z = k * k

noncomputable def squareCount (n : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 n).filter (fun (i : ℕ) => isSquare (i : ℤ))).card

noncomputable def posDivisorCount (i : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 i).filter (fun d => d ∣ i)).card

noncomputable def oddDivisorCount (n : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 n).filter (fun i => Odd (posDivisorCount i))).card

/-- Whenever bulb_switch(n) returns a result r, r equals the number of integers i with 1 <= i <= n for which there exists an integer k such that i = k*k. Equivalently, r is the number of perfect squares in the interval [1, n] (this count is 0 when n = 0).
  Preconditions: 0 <= n <= 1000000000. -/
theorem spec_1 (n r : Std.I64) (hn : 0 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
    (hr : bulb_switch n = ok r) :
    r.val = (squareCount n.val.toNat : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n r : Std.I64) (hn : 0 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
    (hr : bulb_switch n = ok r), r.val = (squareCount n.val.toNat : ℤ)) := by
  sorry

/-- For every n with 0 <= n <= 1000000000, the call bulb_switch(n) returns some result r; it does not fail, panic, or overflow.
  Preconditions: 0 <= n <= 1000000000. -/
theorem spec_2 (n : Std.I64) (hn : 0 ≤ n.val) (hn_ub : n.val ≤ 1000000000) :
    ∃ r : Std.I64, bulb_switch n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn : 0 ≤ n.val) (hn_ub : n.val ≤ 1000000000), ∃ r : Std.I64, bulb_switch n = ok r) := by
  sorry

/-- Whenever bulb_switch(n) returns a result r, 0 <= r <= n and r <= 31622.
  Preconditions: 0 <= n <= 1000000000. -/
theorem spec_3 (n r : Std.I64) (hn : 0 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
    (hr : bulb_switch n = ok r) :
    0 ≤ r.val ∧ r.val ≤ n.val ∧ r.val ≤ 31622 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n r : Std.I64) (hn : 0 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
    (hr : bulb_switch n = ok r), 0 ≤ r.val ∧ r.val ≤ n.val ∧ r.val ≤ 31622) := by
  sorry

/-- Whenever bulb_switch(n) returns a result r, r*r <= n.
  Preconditions: 0 <= n <= 1000000000. -/
theorem spec_4 (n r : Std.I64) (hn : 0 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
    (hr : bulb_switch n = ok r) :
    r.val * r.val ≤ n.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n r : Std.I64) (hn : 0 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
    (hr : bulb_switch n = ok r), r.val * r.val ≤ n.val) := by
  sorry

/-- Whenever bulb_switch(n) returns a result r, n < (r+1)*(r+1).
  Preconditions: 0 <= n <= 1000000000. -/
theorem spec_5 (n r : Std.I64) (hn : 0 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
    (hr : bulb_switch n = ok r) :
    n.val < (r.val + 1) * (r.val + 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n r : Std.I64) (hn : 0 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
    (hr : bulb_switch n = ok r), n.val < (r.val + 1) * (r.val + 1)) := by
  sorry

/-- Whenever bulb_switch(n) returns a result r, r = 0 if and only if n = 0.
  Preconditions: 0 <= n <= 1000000000. -/
theorem spec_6 (n r : Std.I64) (hn : 0 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
    (hr : bulb_switch n = ok r) :
    r.val = 0 ↔ n.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n r : Std.I64) (hn : 0 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
    (hr : bulb_switch n = ok r), r.val = 0 ↔ n.val = 0) := by
  sorry

/-- Whenever bulb_switch(n) returns a result r, r = 1 if and only if 1 <= n <= 3.
  Preconditions: 0 <= n <= 1000000000. -/
theorem spec_7 (n r : Std.I64) (hn : 0 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
    (hr : bulb_switch n = ok r) :
    r.val = 1 ↔ 1 ≤ n.val ∧ n.val ≤ 3 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n r : Std.I64) (hn : 0 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
    (hr : bulb_switch n = ok r), r.val = 1 ↔ 1 ≤ n.val ∧ n.val ≤ 3) := by
  sorry

/-- Whenever bulb_switch(n) returns a result r, r equals the number of integers i with 1 <= i <= n whose number of positive divisors is odd.
  Preconditions: 0 <= n <= 1000000000. -/
theorem spec_8 (n r : Std.I64) (hn : 0 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
    (hr : bulb_switch n = ok r) :
    r.val = (oddDivisorCount n.val.toNat : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n r : Std.I64) (hn : 0 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
    (hr : bulb_switch n = ok r), r.val = (oddDivisorCount n.val.toNat : ℤ)) := by
  sorry

/-- If bulb_switch(a) returns ra and bulb_switch(b) returns rb, then ra <= rb.
  Preconditions: 0 <= a <= b <= 1000000000. -/
theorem spec_9 (a b ra rb : Std.I64) (ha : 0 ≤ a.val) (hab : a.val ≤ b.val)
    (hb_ub : b.val ≤ 1000000000) (hra : bulb_switch a = ok ra) (hrb : bulb_switch b = ok rb) :
    ra.val ≤ rb.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (a b ra rb : Std.I64) (ha : 0 ≤ a.val) (hab : a.val ≤ b.val)
    (hb_ub : b.val ≤ 1000000000) (hra : bulb_switch a = ok ra) (hrb : bulb_switch b = ok rb), ra.val ≤ rb.val) := by
  sorry

/-- If bulb_switch(n) returns r and bulb_switch(n-1) returns rprev, then r = rprev + 1 when n is a perfect square (that is, when n = k*k for some integer k), and r = rprev otherwise.
  Preconditions: 1 <= n <= 1000000000. -/
theorem spec_10 (n m r rprev : Std.I64) (hn : 1 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
    (hm : m.val = n.val - 1) (hr : bulb_switch n = ok r) (hrprev : bulb_switch m = ok rprev) :
    (isSquare n.val → r.val = rprev.val + 1) ∧
      (¬ isSquare n.val → r.val = rprev.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n m r rprev : Std.I64) (hn : 1 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
    (hm : m.val = n.val - 1) (hr : bulb_switch n = ok r) (hrprev : bulb_switch m = ok rprev), (isSquare n.val → r.val = rprev.val + 1) ∧
      (¬ isSquare n.val → r.val = rprev.val)) := by
  sorry

end AegisSpec.BulbSwitch
