import Aegis.SmallestEvenMultiple.Code.Funs

/-!
# Specifications of `Aegis.SmallestEvenMultiple.smallest_even_multiple`

LeetCode problem `smallest-even-multiple`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SmallestEvenMultiple

/-- Whenever smallest_even_multiple n returns a result r, the integer value of r equals n if n is even (n mod 2 = 0), and equals 2*n if n is odd (n mod 2 = 1).
  Preconditions: n is a signed 64-bit integer with 1 <= n <= 150. -/
theorem spec_1 (n r : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 150)
    (hr : Aegis.SmallestEvenMultiple.smallest_even_multiple n = ok r) :
    (n.val % 2 = 0 → r.val = n.val) ∧ (n.val % 2 = 1 → r.val = 2 * n.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n r : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 150)
    (hr : Aegis.SmallestEvenMultiple.smallest_even_multiple n = ok r), (n.val % 2 = 0 → r.val = n.val) ∧ (n.val % 2 = 1 → r.val = 2 * n.val)) := by
  sorry

/-- For every such n, smallest_even_multiple n returns a result r; it does not fail by overflow, panic, or out-of-bounds access.
  Preconditions: n is a signed 64-bit integer with 1 <= n <= 150. -/
theorem spec_2 (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 150) :
    ∃ r : I64, Aegis.SmallestEvenMultiple.smallest_even_multiple n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 150), ∃ r : I64, Aegis.SmallestEvenMultiple.smallest_even_multiple n = ok r) := by
  sorry

/-- Whenever smallest_even_multiple n returns a result r, the integer value of r satisfies n <= r <= 2*n.
  Preconditions: n is a signed 64-bit integer with 1 <= n <= 150. -/
theorem spec_3 (n r : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 150)
    (hr : Aegis.SmallestEvenMultiple.smallest_even_multiple n = ok r) :
    n.val ≤ r.val ∧ r.val ≤ 2 * n.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n r : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 150)
    (hr : Aegis.SmallestEvenMultiple.smallest_even_multiple n = ok r), n.val ≤ r.val ∧ r.val ≤ 2 * n.val) := by
  sorry

/-- Whenever smallest_even_multiple n returns a result r, there exists an integer k such that the integer value of r equals 2*k; equivalently, r is even.
  Preconditions: n is a signed 64-bit integer with 1 <= n <= 150. -/
theorem spec_4 (n r : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 150)
    (hr : Aegis.SmallestEvenMultiple.smallest_even_multiple n = ok r) :
    ∃ k : ℤ, r.val = 2 * k := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n r : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 150)
    (hr : Aegis.SmallestEvenMultiple.smallest_even_multiple n = ok r), ∃ k : ℤ, r.val = 2 * k) := by
  sorry

/-- Whenever smallest_even_multiple n returns a result r, there exists an integer q such that the integer value of r equals n*q; equivalently, n divides r.
  Preconditions: n is a signed 64-bit integer with 1 <= n <= 150. -/
theorem spec_5 (n r : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 150)
    (hr : Aegis.SmallestEvenMultiple.smallest_even_multiple n = ok r) :
    ∃ q : ℤ, r.val = n.val * q := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n r : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 150)
    (hr : Aegis.SmallestEvenMultiple.smallest_even_multiple n = ok r), ∃ q : ℤ, r.val = n.val * q) := by
  sorry

/-- Whenever smallest_even_multiple n returns a result r, for every positive integer m that is a multiple of both 2 and n (that is, 2 divides m and n divides m), the inequality r <= m holds.
  Preconditions: n is a signed 64-bit integer with 1 <= n <= 150. -/
theorem spec_6 (n r : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 150)
    (hr : Aegis.SmallestEvenMultiple.smallest_even_multiple n = ok r) :
    ∀ m : ℤ, 0 < m → (2 : ℤ) ∣ m → n.val ∣ m → r.val ≤ m := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n r : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 150)
    (hr : Aegis.SmallestEvenMultiple.smallest_even_multiple n = ok r), ∀ m : ℤ, 0 < m → (2 : ℤ) ∣ m → n.val ∣ m → r.val ≤ m) := by
  sorry

/-- Whenever smallest_even_multiple n returns a result r, the integer value of r is either n or 2*n.
  Preconditions: n is a signed 64-bit integer with 1 <= n <= 150. -/
theorem spec_7 (n r : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 150)
    (hr : Aegis.SmallestEvenMultiple.smallest_even_multiple n = ok r) :
    r.val = n.val ∨ r.val = 2 * n.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n r : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 150)
    (hr : Aegis.SmallestEvenMultiple.smallest_even_multiple n = ok r), r.val = n.val ∨ r.val = 2 * n.val) := by
  sorry

/-- Whenever smallest_even_multiple n returns a result r, the exact integer quotient r / n equals 1 if n is even and equals 2 if n is odd.
  Preconditions: n is a signed 64-bit integer with 1 <= n <= 150. -/
theorem spec_8 (n r : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 150)
    (hr : Aegis.SmallestEvenMultiple.smallest_even_multiple n = ok r) :
    (n.val % 2 = 0 → r.val / n.val = 1) ∧ (n.val % 2 = 1 → r.val / n.val = 2) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n r : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 150)
    (hr : Aegis.SmallestEvenMultiple.smallest_even_multiple n = ok r), (n.val % 2 = 0 → r.val / n.val = 1) ∧ (n.val % 2 = 1 → r.val / n.val = 2)) := by
  sorry

/-- If smallest_even_multiple n returns a result r and smallest_even_multiple (2*n) returns a result s, then the integer values of r and s are equal.
  Preconditions: n is a signed 64-bit integer with 1 <= n <= 150, n mod 2 = 1, and 2*n <= 150. -/
theorem spec_9 (n r s : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 150) (hodd : n.val % 2 = 1)
    (h2n : 2 * n.val ≤ 150)
    (hr : Aegis.SmallestEvenMultiple.smallest_even_multiple n = ok r)
    (hs : Aegis.SmallestEvenMultiple.smallest_even_multiple (2 * n.val)#i64 = ok s) :
    r.val = s.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n r s : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 150) (hodd : n.val % 2 = 1)
    (h2n : 2 * n.val ≤ 150)
    (hr : Aegis.SmallestEvenMultiple.smallest_even_multiple n = ok r)
    (hs : Aegis.SmallestEvenMultiple.smallest_even_multiple (2 * n.val)#i64 = ok s), r.val = s.val) := by
  sorry

end AegisSpec.SmallestEvenMultiple
