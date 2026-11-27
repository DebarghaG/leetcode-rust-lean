import Aegis.IsPowerOfThree.Code.Funs

/-!
# Specifications of `Aegis.IsPowerOfThree.is_power_of_three`

LeetCode problem `power-of-three`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsPowerOfThree

  open Aegis.IsPowerOfThree (is_power_of_three)

  def i64Of (x : ℤ) (hlo : -9223372036854775808 ≤ x) (hhi : x ≤ 9223372036854775807) :
      Std.I64 :=
    Std.I64.ofInt x (by
      simp only [Aeneas.Std.IScalar.cMin, Aeneas.Std.IScalar.cMax, Aeneas.Std.IScalar.rMin,
        Aeneas.Std.IScalar.rMax, Aeneas.Std.I64.rMin, Aeneas.Std.I64.rMax]
      omega)

  theorem i64Of_val (x : ℤ) (hlo : -9223372036854775808 ≤ x) (hhi : x ≤ 9223372036854775807) :
      (i64Of x hlo hhi).val = x := by
    simp only [i64Of, Aeneas.Std.I64.ofInt, Aeneas.Std.IScalar.ofInt_val_eq]

  /-- The function returns a Boolean result r, and r = true if and only if there exists a natural number k with k >= 0 such that the integer value of n equals 3^k; otherwise r = false. Equivalently, within the constrained range the true inputs are exactly 3^0, 3^1, ..., 3^19.
    Preconditions: n is a 64-bit integer with -2^31 <= n <= 2^31 - 1. -/
  theorem spec_1 (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 2147483647) :
      ∃ r : Bool, is_power_of_three n = ok r ∧ (r = true ↔ ∃ k : ℕ, n.val = 3 ^ k) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 2147483647), ∃ r : Bool, is_power_of_three n = ok r ∧ (r = true ↔ ∃ k : ℕ, n.val = 3 ^ k)) := by
    sorry

  /-- For every such n, the function returns some Boolean result; it does not fail, overflow, or panic.
    Preconditions: n is a 64-bit integer with -2^31 <= n <= 2^31 - 1. -/
  theorem spec_2 (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 2147483647) :
      ∃ r : Bool, is_power_of_three n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 2147483647), ∃ r : Bool, is_power_of_three n = ok r) := by
    sorry

  /-- The function returns false.
    Preconditions: n is a 64-bit integer with -2^31 <= n <= 0. -/
  theorem spec_3 (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 0) :
      ∃ r : Bool, is_power_of_three n = ok r ∧ r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 0), ∃ r : Bool, is_power_of_three n = ok r ∧ r = false) := by
    sorry

  /-- The function returns true.
    Preconditions: n is a 64-bit integer with n = 1. -/
  theorem spec_4 (n : Std.I64) (h : n.val = 1) :
      ∃ r : Bool, is_power_of_three n = ok r ∧ r = true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (h : n.val = 1), ∃ r : Bool, is_power_of_three n = ok r ∧ r = true) := by
    sorry

  /-- Whenever the function returns a Boolean result r with r = true, the integer value of n is at least 1.
    Preconditions: n is a 64-bit integer with -2^31 <= n <= 2^31 - 1. -/
  theorem spec_5 (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 2147483647)
      (r : Bool) (hr : is_power_of_three n = ok r) (htrue : r = true) : 1 ≤ n.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 2147483647)
        (r : Bool) (hr : is_power_of_three n = ok r) (htrue : r = true), 1 ≤ n.val) := by
    sorry

  /-- Whenever the function returns true, n <= 1162261467 (= 3^19).
    Preconditions: n is a 64-bit integer with -2^31 <= n <= 2^31 - 1. -/
  theorem spec_6 (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 2147483647)
      (r : Bool) (hr : is_power_of_three n = ok r) (htrue : r = true) :
      n.val ≤ 1162261467 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 2147483647)
        (r : Bool) (hr : is_power_of_three n = ok r) (htrue : r = true), n.val ≤ 1162261467) := by
    sorry

  /-- Whenever the function returns a Boolean result r with r = true, n is odd, i.e. n mod 2 = 1.
    Preconditions: n is a 64-bit integer with -2^31 <= n <= 2^31 - 1. -/
  theorem spec_7 (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 2147483647)
      (r : Bool) (hr : is_power_of_three n = ok r) (htrue : r = true) : n.val % 2 = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 2147483647)
        (r : Bool) (hr : is_power_of_three n = ok r) (htrue : r = true), n.val % 2 = 1) := by
    sorry

  /-- Whenever the function returns a Boolean result r with r = true, either n = 1 or n mod 3 = 0.
    Preconditions: n is a 64-bit integer with -2^31 <= n <= 2^31 - 1. -/
  theorem spec_8 (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 2147483647)
      (r : Bool) (hr : is_power_of_three n = ok r) (htrue : r = true) :
      n.val = 1 ∨ n.val % 3 = 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 2147483647)
        (r : Bool) (hr : is_power_of_three n = ok r) (htrue : r = true), n.val = 1 ∨ n.val % 3 = 0) := by
    sorry

  /-- The function returns results r and r' for n and n/3 respectively, and r = r'.
    Preconditions: n is a 64-bit integer with -2^31 <= n <= 2^31 - 1 and n mod 3 = 0, so n/3 is exact integer division. -/
  theorem spec_9 (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 2147483647)
      (hmod : n.val % 3 = 0) :
      ∃ r r' : Bool,
        is_power_of_three n = ok r ∧
          is_power_of_three (i64Of (n.val / 3) (by omega) (by omega)) = ok r' ∧ r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 2147483647)
        (hmod : n.val % 3 = 0), ∃ r r' : Bool,
          is_power_of_three n = ok r ∧
            is_power_of_three (i64Of (n.val / 3) (by omega) (by omega)) = ok r' ∧ r = r') := by
    sorry

  /-- The function returns results r and r' for n and 3*n respectively, and r = r'.
    Preconditions: n is a 64-bit integer such that both n and 3*n lie in the constrained range [-2^31, 2^31 - 1]. -/
  theorem spec_10 (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 2147483647)
      (h3lo : -2147483648 ≤ 3 * n.val) (h3hi : 3 * n.val ≤ 2147483647) :
      ∃ r r' : Bool,
        is_power_of_three n = ok r ∧
          is_power_of_three (i64Of (3 * n.val) (by omega) (by omega)) = ok r' ∧
            r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 2147483647)
        (h3lo : -2147483648 ≤ 3 * n.val) (h3hi : 3 * n.val ≤ 2147483647), ∃ r r' : Bool,
          is_power_of_three n = ok r ∧
            is_power_of_three (i64Of (3 * n.val) (by omega) (by omega)) = ok r' ∧
              r = r') := by
    sorry

  /-- For every such n, the function returns a Boolean result r for n, and r = true if and only if n mod 3 = 0 and the function returns true for the integer quotient n/3 (which is exact in that case). In particular, if n mod 3 != 0, then r = false.
    Preconditions: n is a 64-bit integer with -2^31 <= n <= 2^31 - 1 and n > 1. -/
  theorem spec_11 (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 2147483647)
      (hgt : 1 < n.val) :
      ∃ r : Bool,
        is_power_of_three n = ok r ∧
          (r = true ↔
            n.val % 3 = 0 ∧
              is_power_of_three (i64Of (n.val / 3) (by omega) (by omega)) = ok true) ∧
          (n.val % 3 ≠ 0 → r = false) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (hlo : -2147483648 ≤ n.val) (hhi : n.val ≤ 2147483647)
        (hgt : 1 < n.val), ∃ r : Bool,
          is_power_of_three n = ok r ∧
            (r = true ↔
              n.val % 3 = 0 ∧
                is_power_of_three (i64Of (n.val / 3) (by omega) (by omega)) = ok true) ∧
            (n.val % 3 ≠ 0 → r = false)) := by
    sorry

  end AegisSpec.IsPowerOfThree
