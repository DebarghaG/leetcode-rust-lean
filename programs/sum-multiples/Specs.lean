import Aegis.SumOfMultiples.Code.Funs

/-!
# Specifications of `Aegis.SumOfMultiples.sum_of_multiples`

LeetCode problem `sum-multiples`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SumOfMultiples

def value (k : ℤ) : ℤ := if 3 ∣ k ∨ 5 ∣ k ∨ 7 ∣ k then k else 0

def sumTo (n : ℤ) : ℤ := ∑ k ∈ Finset.Icc (1 : ℕ) n.toNat, value (k : ℤ)

/-- The function returns a result r and r = sum_{k=1}^{n} value(k), where value(k) = k if k is divisible by 3, 5, or 7, and value(k) = 0 otherwise. Equivalently, r is the sum of every integer k such that 1 <= k <= n and k is divisible by 3, 5, or 7.
  Preconditions: n is an integer with 1 <= n <= 1000. -/
theorem spec_1 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.SumOfMultiples.sum_of_multiples n = ok r ∧ r.val = sumTo n.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000), ∃ r : Std.I64,
      Aegis.SumOfMultiples.sum_of_multiples n = ok r ∧ r.val = sumTo n.val) := by
  sorry

/-- The function returns a result r; it does not fail (no panic, out-of-bounds, or arithmetic overflow).
  Preconditions: n is an integer with 1 <= n <= 1000. -/
theorem spec_2 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000) :
    ∃ r : Std.I64, Aegis.SumOfMultiples.sum_of_multiples n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000), ∃ r : Std.I64, Aegis.SumOfMultiples.sum_of_multiples n = ok r) := by
  sorry

/-- The function returns a result r and r >= 0.
  Preconditions: n is an integer with 1 <= n <= 1000. -/
theorem spec_3 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.SumOfMultiples.sum_of_multiples n = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000), ∃ r : Std.I64,
      Aegis.SumOfMultiples.sum_of_multiples n = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= n*(n+1)/2.
  Preconditions: n is an integer with 1 <= n <= 1000. -/
theorem spec_4 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.SumOfMultiples.sum_of_multiples n = ok r ∧
        r.val ≤ n.val * (n.val + 1) / 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000), ∃ r : Std.I64,
      Aegis.SumOfMultiples.sum_of_multiples n = ok r ∧
        r.val ≤ n.val * (n.val + 1) / 2) := by
  sorry

/-- The function returns a result r and, for every integer k such that 1 <= k <= n and k is divisible by 3, 5, or 7, we have r >= k.
  Preconditions: n is an integer with 1 <= n <= 1000. -/
theorem spec_5 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.SumOfMultiples.sum_of_multiples n = ok r ∧
        ∀ k : ℤ, 1 ≤ k → k ≤ n.val → (3 ∣ k ∨ 5 ∣ k ∨ 7 ∣ k) → k ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000), ∃ r : Std.I64,
      Aegis.SumOfMultiples.sum_of_multiples n = ok r ∧
        ∀ k : ℤ, 1 ≤ k → k ≤ n.val → (3 ∣ k ∨ 5 ∣ k ∨ 7 ∣ k) → k ≤ r.val) := by
  sorry

/-- The function returns results r for n and r_prev for n - 1, and r = r_prev + (if n is divisible by 3 or n is divisible by 5 or n is divisible by 7 then n else 0).
  Preconditions: n is an integer with 2 <= n <= 1000. -/
theorem spec_6 (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000) :
    ∃ np r r_prev : Std.I64,
      n - 1#i64 = ok np ∧ np.val = n.val - 1 ∧
        Aegis.SumOfMultiples.sum_of_multiples n = ok r ∧
        Aegis.SumOfMultiples.sum_of_multiples np = ok r_prev ∧
        r.val = r_prev.val + (if 3 ∣ n.val ∨ 5 ∣ n.val ∨ 7 ∣ n.val then n.val else 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1000), ∃ np r r_prev : Std.I64,
      n - 1#i64 = ok np ∧ np.val = n.val - 1 ∧
        Aegis.SumOfMultiples.sum_of_multiples n = ok r ∧
        Aegis.SumOfMultiples.sum_of_multiples np = ok r_prev ∧
        r.val = r_prev.val + (if 3 ∣ n.val ∨ 5 ∣ n.val ∨ 7 ∣ n.val then n.val else 0)) := by
  sorry

/-- Let r_m be the result of sum_of_multiples(m) and let r_n be the result of sum_of_multiples(n). Then r_m <= r_n.
  Preconditions: m and n are integers with 1 <= m <= n <= 1000. -/
theorem spec_7 (m n : Std.I64) (hm_lo : 1 ≤ m.val) (hmn : m.val ≤ n.val)
    (hn_hi : n.val ≤ 1000) :
    ∃ r_m r_n : Std.I64,
      Aegis.SumOfMultiples.sum_of_multiples m = ok r_m ∧
        Aegis.SumOfMultiples.sum_of_multiples n = ok r_n ∧ r_m.val ≤ r_n.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (m n : Std.I64) (hm_lo : 1 ≤ m.val) (hmn : m.val ≤ n.val)
    (hn_hi : n.val ≤ 1000), ∃ r_m r_n : Std.I64,
      Aegis.SumOfMultiples.sum_of_multiples m = ok r_m ∧
        Aegis.SumOfMultiples.sum_of_multiples n = ok r_n ∧ r_m.val ≤ r_n.val) := by
  sorry

end AegisSpec.SumOfMultiples
