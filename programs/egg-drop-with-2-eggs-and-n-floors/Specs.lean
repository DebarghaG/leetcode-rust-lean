import Aegis.TwoEggDrop.Code.Funs

/-!
# Specifications of `Aegis.TwoEggDrop.two_egg_drop`

LeetCode problem `egg-drop-with-2-eggs-and-n-floors`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.TwoEggDrop

namespace AegisSpec.TwoEggDrop

def T (m : ℤ) : ℤ := m * (m + 1) / 2

/-- Whenever the function returns a result r, r is the least nonnegative integer m such that T(m) >= n.
  Preconditions: n is an integer with 1 <= n <= 1000. Let T(m)=m(m+1)/2 for integers m >= 0. -/
theorem spec_1 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000) :
    ∀ r : Std.I64, two_egg_drop n = ok r →
      0 ≤ r.val ∧ n.val ≤ T r.val ∧ ∀ m : ℤ, 0 ≤ m → n.val ≤ T m → r.val ≤ m := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000), ∀ r : Std.I64, two_egg_drop n = ok r →
      0 ≤ r.val ∧ n.val ≤ T r.val ∧ ∀ m : ℤ, 0 ≤ m → n.val ≤ T m → r.val ≤ m) := by
  sorry

/-- The function returns a result r for every such n.
  Preconditions: n is an integer with 1 <= n <= 1000. -/
theorem spec_2 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000) :
    ∃ r : Std.I64, two_egg_drop n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000), ∃ r : Std.I64, two_egg_drop n = ok r) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r <= 45.
  Preconditions: n is an integer with 1 <= n <= 1000. Let T(m)=m(m+1)/2. -/
theorem spec_3 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000) :
    ∀ r : Std.I64, two_egg_drop n = ok r → 1 ≤ r.val ∧ r.val ≤ 45 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000), ∀ r : Std.I64, two_egg_drop n = ok r → 1 ≤ r.val ∧ r.val ≤ 45) := by
  sorry

/-- Whenever the function returns a result r, r <= n.
  Preconditions: n is an integer with 1 <= n <= 1000. -/
theorem spec_4 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000) :
    ∀ r : Std.I64, two_egg_drop n = ok r → r.val ≤ n.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000), ∀ r : Std.I64, two_egg_drop n = ok r → r.val ≤ n.val) := by
  sorry

/-- Whenever the function returns a result r, r >= 1 and T(r-1) < n <= T(r).
  Preconditions: n is an integer with 1 <= n <= 1000. Let T(m)=m(m+1)/2 for integers m >= 0. -/
theorem spec_5 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000) :
    ∀ r : Std.I64, two_egg_drop n = ok r →
      1 ≤ r.val ∧ T (r.val - 1) < n.val ∧ n.val ≤ T r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000), ∀ r : Std.I64, two_egg_drop n = ok r →
      1 ≤ r.val ∧ T (r.val - 1) < n.val ∧ n.val ≤ T r.val) := by
  sorry

/-- Whenever the function returns a result r, r >= 1 and 0 <= T(r) - n <= r - 1.
  Preconditions: n is an integer with 1 <= n <= 1000. Let T(m)=m(m+1)/2 for integers m >= 0. -/
theorem spec_6 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000) :
    ∀ r : Std.I64, two_egg_drop n = ok r →
      1 ≤ r.val ∧ 0 ≤ T r.val - n.val ∧ T r.val - n.val ≤ r.val - 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000), ∀ r : Std.I64, two_egg_drop n = ok r →
      1 ≤ r.val ∧ 0 ≤ T r.val - n.val ∧ T r.val - n.val ≤ r.val - 1) := by
  sorry

/-- Whenever the function returns a result r, for every integer m with 0 <= m <= 45, r <= m if and only if T(m) >= n.
  Preconditions: n is an integer with 1 <= n <= 1000. Let T(m)=m(m+1)/2. -/
theorem spec_7 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000) :
    ∀ r : Std.I64, two_egg_drop n = ok r →
      ∀ m : ℤ, 0 ≤ m → m ≤ 45 → (r.val ≤ m ↔ n.val ≤ T m) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000), ∀ r : Std.I64, two_egg_drop n = ok r →
      ∀ m : ℤ, 0 ≤ m → m ≤ 45 → (r.val ≤ m ↔ n.val ≤ T m)) := by
  sorry

/-- Whenever the function returns r1 for n1 and r2 for n2, r1 <= r2.
  Preconditions: n1 and n2 are integers with 1 <= n1 <= n2 <= 1000. -/
theorem spec_8 (n1 n2 : Std.I64) (hn : 1 ≤ n1.val ∧ n1.val ≤ n2.val ∧ n2.val ≤ 1000) :
    ∀ r1 r2 : Std.I64, two_egg_drop n1 = ok r1 → two_egg_drop n2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n1 n2 : Std.I64) (hn : 1 ≤ n1.val ∧ n1.val ≤ n2.val ∧ n2.val ≤ 1000), ∀ r1 r2 : Std.I64, two_egg_drop n1 = ok r1 → two_egg_drop n2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- Whenever the function returns r for n and s for n+1, we have r >= 1 and either s = r or s = r+1; moreover s = r+1 if and only if n = T(r).
  Preconditions: n is an integer with 1 <= n < 1000. Let T(m)=m(m+1)/2. -/
theorem spec_9 (n n' : Std.I64) (hn : 1 ≤ n.val ∧ n.val < 1000) (hn' : n'.val = n.val + 1) :
    ∀ r s : Std.I64, two_egg_drop n = ok r → two_egg_drop n' = ok s →
      1 ≤ r.val ∧ (s.val = r.val ∨ s.val = r.val + 1) ∧
        (s.val = r.val + 1 ↔ n.val = T r.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n n' : Std.I64) (hn : 1 ≤ n.val ∧ n.val < 1000) (hn' : n'.val = n.val + 1), ∀ r s : Std.I64, two_egg_drop n = ok r → two_egg_drop n' = ok s →
      1 ≤ r.val ∧ (s.val = r.val ∨ s.val = r.val + 1) ∧
        (s.val = r.val + 1 ↔ n.val = T r.val)) := by
  sorry

end AegisSpec.TwoEggDrop
