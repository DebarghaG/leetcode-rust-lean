import Aegis.PivotInteger.Code.Funs

/-!
# Specifications of `Aegis.PivotInteger.pivot_integer`

LeetCode problem `find-the-pivot-integer`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.PivotInteger

  open Aegis.PivotInteger

  def isumAux (a : ℤ) : ℕ → ℤ
    | 0 => 0
    | k + 1 => a + isumAux (a + 1) k

  def isum (a b : ℤ) : ℤ := isumAux a (Int.toNat (b - a + 1))

  /-- The function returns a result r, and either: (1) there is an integer x with 1 <= x <= n such that 1 + 2 + ... + x = x + (x+1) + ... + n, and r = x; or (2) no integer x with 1 <= x <= n satisfies that equality, and r = -1. Here each displayed sum is the ordinary integer sum over the indicated inclusive interval.
    Preconditions: 1 <= n <= 1000, where n is interpreted as its mathematical integer value. -/
  theorem spec_1
      (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
      ∃ r : Std.I64, pivot_integer n = ok r ∧
        ((∃ x : ℤ, 1 ≤ x ∧ x ≤ n.val ∧ isum 1 x = isum x n.val ∧ r.val = x) ∨
         (((∀ x : ℤ, ¬ (1 ≤ x ∧ x ≤ n.val ∧ isum 1 x = isum x n.val)) ∧ r.val = -1))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∃ r : Std.I64, pivot_integer n = ok r ∧
          ((∃ x : ℤ, 1 ≤ x ∧ x ≤ n.val ∧ isum 1 x = isum x n.val ∧ r.val = x) ∨
           (((∀ x : ℤ, ¬ (1 ≤ x ∧ x ≤ n.val ∧ isum 1 x = isum x n.val)) ∧ r.val = -1)))) := by
    sorry

  /-- The function returns a result r; it does not fail.
    Preconditions: 1 <= n <= 1000, where n is interpreted as its mathematical integer value. -/
  theorem spec_2
      (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
      ∃ r : Std.I64, pivot_integer n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∃ r : Std.I64, pivot_integer n = ok r) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, r satisfies 1 <= r <= n and 1 + 2 + ... + r = r + (r+1) + ... + n.
    Preconditions: 1 <= n <= 1000, where n is interpreted as its mathematical integer value. -/
  theorem spec_3
      (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
      ∀ r : Std.I64, pivot_integer n = ok r → r.val ≠ -1 →
        1 ≤ r.val ∧ r.val ≤ n.val ∧ isum 1 r.val = isum r.val n.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : Std.I64, pivot_integer n = ok r → r.val ≠ -1 →
          1 ≤ r.val ∧ r.val ≤ n.val ∧ isum 1 r.val = isum r.val n.val) := by
    sorry

  /-- Whenever the function returns a result r with r = -1, there is no integer x with 1 <= x <= n such that 1 + 2 + ... + x = x + (x+1) + ... + n.
    Preconditions: 1 <= n <= 1000, where n is interpreted as its mathematical integer value. -/
  theorem spec_4
      (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
      ∀ r : Std.I64, pivot_integer n = ok r → r.val = -1 →
        ¬ ∃ x : ℤ, 1 ≤ x ∧ x ≤ n.val ∧ isum 1 x = isum x n.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : Std.I64, pivot_integer n = ok r → r.val = -1 →
          ¬ ∃ x : ℤ, 1 ≤ x ∧ x ≤ n.val ∧ isum 1 x = isum x n.val) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, for every integer x with 1 <= x <= n, if 1 + 2 + ... + x = x + (x+1) + ... + n, then x = r.
    Preconditions: 1 <= n <= 1000, where n is interpreted as its mathematical integer value. -/
  theorem spec_5
      (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
      ∀ r : Std.I64, pivot_integer n = ok r → r.val ≠ -1 →
        ∀ x : ℤ, 1 ≤ x → x ≤ n.val → isum 1 x = isum x n.val → x = r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : Std.I64, pivot_integer n = ok r → r.val ≠ -1 →
          ∀ x : ℤ, 1 ≤ x → x ≤ n.val → isum 1 x = isum x n.val → x = r.val) := by
    sorry

  /-- Whenever the function returns a result r, r != -1 if and only if there exists an integer x with 1 <= x <= n such that 1 + 2 + ... + x = x + (x+1) + ... + n.
    Preconditions: 1 <= n <= 1000, where n is interpreted as its mathematical integer value. -/
  theorem spec_6
      (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
      ∀ r : Std.I64, pivot_integer n = ok r →
        (r.val ≠ -1 ↔ ∃ x : ℤ, 1 ≤ x ∧ x ≤ n.val ∧ isum 1 x = isum x n.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : Std.I64, pivot_integer n = ok r →
          (r.val ≠ -1 ↔ ∃ x : ℤ, 1 ≤ x ∧ x ≤ n.val ∧ isum 1 x = isum x n.val)) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, 2*r*r = n*(n+1).
    Preconditions: 1 <= n <= 1000, where n is interpreted as its mathematical integer value. -/
  theorem spec_7
      (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
      ∀ r : Std.I64, pivot_integer n = ok r → r.val ≠ -1 →
        2 * r.val * r.val = n.val * (n.val + 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : Std.I64, pivot_integer n = ok r → r.val ≠ -1 →
          2 * r.val * r.val = n.val * (n.val + 1)) := by
    sorry

  /-- Whenever the function returns a result r with r = -1, there is no integer x with 1 <= x <= n such that 2*x*x = n*(n+1).
    Preconditions: 1 <= n <= 1000, where n is interpreted as its mathematical integer value. -/
  theorem spec_8
      (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
      ∀ r : Std.I64, pivot_integer n = ok r → r.val = -1 →
        ¬ ∃ x : ℤ, 1 ≤ x ∧ x ≤ n.val ∧ 2 * x * x = n.val * (n.val + 1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : Std.I64, pivot_integer n = ok r → r.val = -1 →
          ¬ ∃ x : ℤ, 1 ≤ x ∧ x ≤ n.val ∧ 2 * x * x = n.val * (n.val + 1)) := by
    sorry

  end AegisSpec.PivotInteger
