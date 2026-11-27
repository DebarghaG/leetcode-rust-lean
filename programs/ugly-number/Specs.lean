import Aegis.IsUgly.Code.Funs

/-!
# Specifications of `Aegis.IsUgly.is_ugly`

LeetCode problem `ugly-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsUgly

def FiveSmooth (n : ℤ) : Prop :=
  0 < n ∧ ∃ a b c : ℕ, n = 2 ^ a * 3 ^ b * 5 ^ c

/-- For every such n, the function returns a result r, and r = true exactly when n > 0 and there exist nonnegative integers a, b, c such that n = 2^a * 3^b * 5^c; for all other such n, r = false.
  Preconditions: -2^31 <= n <= 2^31 - 1. -/
theorem spec_1 (n : Aeneas.Std.I64)
    (hlo : -(2 : ℤ) ^ 31 ≤ n.val) (hhi : n.val ≤ (2 : ℤ) ^ 31 - 1) :
    ∃ r : Bool, Aegis.IsUgly.is_ugly n = Aeneas.Std.Result.ok r ∧
      (r = true ↔ FiveSmooth n.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Aeneas.Std.I64)
    (hlo : -(2 : ℤ) ^ 31 ≤ n.val) (hhi : n.val ≤ (2 : ℤ) ^ 31 - 1), ∃ r : Bool, Aegis.IsUgly.is_ugly n = Aeneas.Std.Result.ok r ∧
      (r = true ↔ FiveSmooth n.val)) := by
  sorry

/-- For every such n, the function does not fail or panic; it returns some result of type Bool.
  Preconditions: -2^31 <= n <= 2^31 - 1. -/
theorem spec_2 (n : Aeneas.Std.I64)
    (hlo : -(2 : ℤ) ^ 31 ≤ n.val) (hhi : n.val ≤ (2 : ℤ) ^ 31 - 1) :
    ∃ r : Bool, Aegis.IsUgly.is_ugly n = Aeneas.Std.Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Aeneas.Std.I64)
    (hlo : -(2 : ℤ) ^ 31 ≤ n.val) (hhi : n.val ≤ (2 : ℤ) ^ 31 - 1), ∃ r : Bool, Aegis.IsUgly.is_ugly n = Aeneas.Std.Result.ok r) := by
  sorry

/-- For every such n, the function returns false.
  Preconditions: -2^31 <= n <= 0. -/
theorem spec_3 (n : Aeneas.Std.I64)
    (hlo : -(2 : ℤ) ^ 31 ≤ n.val) (hhi : n.val ≤ 0) :
    Aegis.IsUgly.is_ugly n = Aeneas.Std.Result.ok false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Aeneas.Std.I64)
    (hlo : -(2 : ℤ) ^ 31 ≤ n.val) (hhi : n.val ≤ 0), Aegis.IsUgly.is_ugly n = Aeneas.Std.Result.ok false) := by
  sorry

/-- For every such n, the function returns true if and only if n = 1.
  Preconditions: -2^31 <= n <= 2^31 - 1, n > 0, and n is not divisible by 2, by 3, or by 5. -/
theorem spec_4 (n : Aeneas.Std.I64)
    (hlo : -(2 : ℤ) ^ 31 ≤ n.val) (hhi : n.val ≤ (2 : ℤ) ^ 31 - 1)
    (hpos : 0 < n.val)
    (h2 : ¬ (2 : ℤ) ∣ n.val) (h3 : ¬ (3 : ℤ) ∣ n.val) (h5 : ¬ (5 : ℤ) ∣ n.val) :
    ∃ r : Bool, Aegis.IsUgly.is_ugly n = Aeneas.Std.Result.ok r ∧
      (r = true ↔ n.val = 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Aeneas.Std.I64)
    (hlo : -(2 : ℤ) ^ 31 ≤ n.val) (hhi : n.val ≤ (2 : ℤ) ^ 31 - 1)
    (hpos : 0 < n.val)
    (h2 : ¬ (2 : ℤ) ∣ n.val) (h3 : ¬ (3 : ℤ) ∣ n.val) (h5 : ¬ (5 : ℤ) ∣ n.val), ∃ r : Bool, Aegis.IsUgly.is_ugly n = Aeneas.Std.Result.ok r ∧
      (r = true ↔ n.val = 1)) := by
  sorry

/-- For every such n, if the function returns true, then every prime p that divides n is equal to 2, 3, or 5.
  Preconditions: -2^31 <= n <= 2^31 - 1. -/
theorem spec_5 (n : Aeneas.Std.I64)
    (hlo : -(2 : ℤ) ^ 31 ≤ n.val) (hhi : n.val ≤ (2 : ℤ) ^ 31 - 1) :
    Aegis.IsUgly.is_ugly n = Aeneas.Std.Result.ok true →
      ∀ p : ℕ, Nat.Prime p → (p : ℤ) ∣ n.val → p = 2 ∨ p = 3 ∨ p = 5 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Aeneas.Std.I64)
    (hlo : -(2 : ℤ) ^ 31 ≤ n.val) (hhi : n.val ≤ (2 : ℤ) ^ 31 - 1), Aegis.IsUgly.is_ugly n = Aeneas.Std.Result.ok true →
      ∀ p : ℕ, Nat.Prime p → (p : ℤ) ∣ n.val → p = 2 ∨ p = 3 ∨ p = 5) := by
  sorry

/-- For every such n, if the function returns false, then there exists a prime p with p not in {2, 3, 5} such that p divides n.
  Preconditions: -2^31 <= n <= 2^31 - 1 and n > 0. -/
theorem spec_6 (n : Aeneas.Std.I64)
    (hlo : -(2 : ℤ) ^ 31 ≤ n.val) (hhi : n.val ≤ (2 : ℤ) ^ 31 - 1)
    (hpos : 0 < n.val) :
    Aegis.IsUgly.is_ugly n = Aeneas.Std.Result.ok false →
      ∃ p : ℕ, Nat.Prime p ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ (p : ℤ) ∣ n.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Aeneas.Std.I64)
    (hlo : -(2 : ℤ) ^ 31 ≤ n.val) (hhi : n.val ≤ (2 : ℤ) ^ 31 - 1)
    (hpos : 0 < n.val), Aegis.IsUgly.is_ugly n = Aeneas.Std.Result.ok false →
      ∃ p : ℕ, Nat.Prime p ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ (p : ℤ) ∣ n.val) := by
  sorry

/-- For every such n, the function returns true.
  Preconditions: -2^31 <= n <= 2^31 - 1 and n = 2^a * 3^b * 5^c for some nonnegative integers a, b, c. -/
theorem spec_7 (n : Aeneas.Std.I64)
    (hlo : -(2 : ℤ) ^ 31 ≤ n.val) (hhi : n.val ≤ (2 : ℤ) ^ 31 - 1)
    (h : ∃ a b c : ℕ, n.val = 2 ^ a * 3 ^ b * 5 ^ c) :
    Aegis.IsUgly.is_ugly n = Aeneas.Std.Result.ok true := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Aeneas.Std.I64)
    (hlo : -(2 : ℤ) ^ 31 ≤ n.val) (hhi : n.val ≤ (2 : ℤ) ^ 31 - 1)
    (h : ∃ a b c : ℕ, n.val = 2 ^ a * 3 ^ b * 5 ^ c), Aegis.IsUgly.is_ugly n = Aeneas.Std.Result.ok true) := by
  sorry

/-- For every such n and every positive divisor d of n, writing k = n / d, the function returns true on input n if and only if it returns true on input d and it returns true on input k.
  Preconditions: -2^31 <= n <= 2^31 - 1 and n > 0. -/
theorem spec_8 (n d k : Aeneas.Std.I64)
    (hlo : -(2 : ℤ) ^ 31 ≤ n.val) (hhi : n.val ≤ (2 : ℤ) ^ 31 - 1)
    (hpos : 0 < n.val)
    (hdpos : 0 < d.val) (hdvd : d.val ∣ n.val) (hk : k.val = n.val / d.val) :
    (Aegis.IsUgly.is_ugly n = Aeneas.Std.Result.ok true ↔
      (Aegis.IsUgly.is_ugly d = Aeneas.Std.Result.ok true ∧
        Aegis.IsUgly.is_ugly k = Aeneas.Std.Result.ok true)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n d k : Aeneas.Std.I64)
    (hlo : -(2 : ℤ) ^ 31 ≤ n.val) (hhi : n.val ≤ (2 : ℤ) ^ 31 - 1)
    (hpos : 0 < n.val)
    (hdpos : 0 < d.val) (hdvd : d.val ∣ n.val) (hk : k.val = n.val / d.val), (Aegis.IsUgly.is_ugly n = Aeneas.Std.Result.ok true ↔
      (Aegis.IsUgly.is_ugly d = Aeneas.Std.Result.ok true ∧
        Aegis.IsUgly.is_ugly k = Aeneas.Std.Result.ok true))) := by
  sorry

/-- For every such n and N, the function returns the same Boolean on input n and on input N.
  Preconditions: -2^31 <= n <= 2^31 - 1, n > 0, and N = 2^a * 3^b * 5^c * n for some nonnegative integers a, b, c with -2^31 <= N <= 2^31 - 1. -/
theorem spec_9 (n N : Aeneas.Std.I64)
    (hlo : -(2 : ℤ) ^ 31 ≤ n.val) (hhi : n.val ≤ (2 : ℤ) ^ 31 - 1)
    (hpos : 0 < n.val)
    (hfac : ∃ a b c : ℕ, N.val = 2 ^ a * 3 ^ b * 5 ^ c * n.val)
    (hNlo : -(2 : ℤ) ^ 31 ≤ N.val) (hNhi : N.val ≤ (2 : ℤ) ^ 31 - 1) :
    ∃ r : Bool, Aegis.IsUgly.is_ugly n = Aeneas.Std.Result.ok r ∧
      Aegis.IsUgly.is_ugly N = Aeneas.Std.Result.ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n N : Aeneas.Std.I64)
    (hlo : -(2 : ℤ) ^ 31 ≤ n.val) (hhi : n.val ≤ (2 : ℤ) ^ 31 - 1)
    (hpos : 0 < n.val)
    (hfac : ∃ a b c : ℕ, N.val = 2 ^ a * 3 ^ b * 5 ^ c * n.val)
    (hNlo : -(2 : ℤ) ^ 31 ≤ N.val) (hNhi : N.val ≤ (2 : ℤ) ^ 31 - 1), ∃ r : Bool, Aegis.IsUgly.is_ugly n = Aeneas.Std.Result.ok r ∧
      Aegis.IsUgly.is_ugly N = Aeneas.Std.Result.ok r) := by
  sorry

end AegisSpec.IsUgly
