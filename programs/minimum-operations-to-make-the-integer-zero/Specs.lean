import Aegis.MakeTheIntegerZero.Code.Funs

/-!
# Specifications of `Aegis.MakeTheIntegerZero.make_the_integer_zero`

LeetCode problem `minimum-operations-to-make-the-integer-zero`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MakeTheIntegerZero

def popcount (n : ℕ) : ℕ := (List.range (n + 1)).countP fun i => n.testBit i

def IsSumOfPowers (k n : ℤ) : Prop :=
  ∃ exps : List ℕ, (exps.length : ℤ) = k ∧ (∀ e ∈ exps, e ≤ 60) ∧
    (exps.map (fun e => (2 : ℤ) ^ e)).sum = n

def SpecP (num1 num2 k : ℤ) : Prop :=
  num1 - k * num2 > 0 ∧ IsSumOfPowers k (num1 - k * num2)

/-- Let P(k) be the property that num1 - k*num2 > 0 and there exist integers i_1, ..., i_k each in the range [0, 60] such that sum_{j=1}^k 2^{i_j} = num1 - k*num2. The function returns a result r (it does not fail) such that if there exists a k >= 0 satisfying P(k), then r is the smallest such k; otherwise r = -1.
  Preconditions: 1 <= num1 <= 10^9 and -10^9 <= num2 <= 10^9. -/
theorem spec_1 (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9) :
    ∃ r : Std.I64,
      Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r ∧
        ((∃ k : ℤ, 0 ≤ k ∧ SpecP num1.val num2.val k) →
          SpecP num1.val num2.val r.val ∧
            ∀ k : ℤ, 0 ≤ k → SpecP num1.val num2.val k → r.val ≤ k) ∧
        (¬ (∃ k : ℤ, 0 ≤ k ∧ SpecP num1.val num2.val k) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9), ∃ r : Std.I64,
      Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r ∧
        ((∃ k : ℤ, 0 ≤ k ∧ SpecP num1.val num2.val k) →
          SpecP num1.val num2.val r.val ∧
            ∀ k : ℤ, 0 ≤ k → SpecP num1.val num2.val k → r.val ≤ k) ∧
        (¬ (∃ k : ℤ, 0 ≤ k ∧ SpecP num1.val num2.val k) → r.val = -1)) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, there exist integers i_1, ..., i_r each in the range [0, 60] such that num1 = r*num2 + sum_{j=1}^r 2^{i_j}.
  Preconditions: 1 <= num1 <= 10^9 and -10^9 <= num2 <= 10^9. -/
theorem spec_2 (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9)
    (r : Std.I64) (hr : Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r)
    (hr0 : 0 ≤ r.val) :
    ∃ exps : List ℕ, (exps.length : ℤ) = r.val ∧ (∀ e ∈ exps, e ≤ 60) ∧
      num1.val = r.val * num2.val + (exps.map (fun e => (2 : ℤ) ^ e)).sum := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9)
    (r : Std.I64) (hr : Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r)
    (hr0 : 0 ≤ r.val), ∃ exps : List ℕ, (exps.length : ℤ) = r.val ∧ (∀ e ∈ exps, e ≤ 60) ∧
      num1.val = r.val * num2.val + (exps.map (fun e => (2 : ℤ) ^ e)).sum) := by
  sorry

/-- Whenever the function returns a result r with r > 0, for every integer k with 0 <= k < r, it is not the case that (num1 - k*num2 > 0 and there exist integers i_1, ..., i_k each in [0, 60] such that sum_{j=1}^k 2^{i_j} = num1 - k*num2).
  Preconditions: 1 <= num1 <= 10^9 and -10^9 <= num2 <= 10^9. -/
theorem spec_3 (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9)
    (r : Std.I64) (hr : Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r)
    (hr0 : 0 < r.val) :
    ∀ k : ℤ, 0 ≤ k → k < r.val → ¬ SpecP num1.val num2.val k := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9)
    (r : Std.I64) (hr : Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r)
    (hr0 : 0 < r.val), ∀ k : ℤ, 0 ≤ k → k < r.val → ¬ SpecP num1.val num2.val k) := by
  sorry

/-- Whenever the function returns a result r with r = -1, for every integer k >= 0, it is not the case that (num1 - k*num2 > 0 and there exist integers i_1, ..., i_k each in [0, 60] such that sum_{j=1}^k 2^{i_j} = num1 - k*num2).
  Preconditions: 1 <= num1 <= 10^9 and -10^9 <= num2 <= 10^9. -/
theorem spec_4 (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9)
    (r : Std.I64) (hr : Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r)
    (hr1 : r.val = -1) :
    ∀ k : ℤ, 0 ≤ k → ¬ SpecP num1.val num2.val k := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9)
    (r : Std.I64) (hr : Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r)
    (hr1 : r.val = -1), ∀ k : ℤ, 0 ≤ k → ¬ SpecP num1.val num2.val k) := by
  sorry

/-- Whenever the function returns a result r with r != -1, it holds that 1 <= r <= 35.
  Preconditions: 1 <= num1 <= 10^9 and -10^9 <= num2 <= 10^9. -/
theorem spec_5 (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9)
    (r : Std.I64) (hr : Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r)
    (hrne : r.val ≠ -1) :
    1 ≤ r.val ∧ r.val ≤ 35 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9)
    (r : Std.I64) (hr : Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r)
    (hrne : r.val ≠ -1), 1 ≤ r.val ∧ r.val ≤ 35) := by
  sorry

/-- If num2 = 0, then the function returns a result r and r = popcount(num1), where popcount(num1) is the number of indices i such that the i-th bit of num1 is 1 (equivalently, the number of 1s in the binary representation of num1).
  Preconditions: 1 <= num1 <= 10^9 and num2 = 0. -/
theorem spec_6 (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9) (h2 : num2.val = 0) :
    ∃ r : Std.I64,
      Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r ∧
        r.val = (popcount num1.val.toNat : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9) (h2 : num2.val = 0), ∃ r : Std.I64,
      Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r ∧
        r.val = (popcount num1.val.toNat : ℤ)) := by
  sorry

/-- If num2 >= num1, then the function returns a result r and r = -1.
  Preconditions: 1 <= num1 <= 10^9, 1 <= num2 <= 10^9, and num2 >= num1. -/
theorem spec_7 (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : 1 ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9) (h3 : num1.val ≤ num2.val) :
    ∃ r : Std.I64, Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r ∧ r.val = -1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : 1 ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9) (h3 : num1.val ≤ num2.val), ∃ r : Std.I64, Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r ∧ r.val = -1) := by
  sorry

/-- If num2 < 0, then the function returns a result r with r != -1 (i.e., a solution exists).
  Preconditions: 1 <= num1 <= 10^9 and -10^9 <= num2 <= -1. -/
theorem spec_8 (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ -1) :
    ∃ r : Std.I64, Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r ∧ r.val ≠ -1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ -1), ∃ r : Std.I64, Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r ∧ r.val ≠ -1) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, it holds that num1 - r*num2 > 0.
  Preconditions: 1 <= num1 <= 10^9 and -10^9 <= num2 <= 10^9. -/
theorem spec_9 (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9)
    (r : Std.I64) (hr : Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r)
    (hr0 : 0 ≤ r.val) :
    0 < num1.val - r.val * num2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9)
    (r : Std.I64) (hr : Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r)
    (hr0 : 0 ≤ r.val), 0 < num1.val - r.val * num2.val) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, it holds that num1 - r*num2 >= r.
  Preconditions: 1 <= num1 <= 10^9 and -10^9 <= num2 <= 10^9. -/
theorem spec_10 (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9)
    (r : Std.I64) (hr : Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r)
    (hr0 : 0 ≤ r.val) :
    num1.val - r.val * num2.val ≥ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9)
    (r : Std.I64) (hr : Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r)
    (hr0 : 0 ≤ r.val), num1.val - r.val * num2.val ≥ r.val) := by
  sorry

/-- Whenever the function returns a result r with r >= 0 and num2 > 0, it holds that r*(num2 + 1) <= num1.
  Preconditions: 1 <= num1 <= 10^9 and -10^9 <= num2 <= 10^9. -/
theorem spec_11 (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9)
    (r : Std.I64) (hr : Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r)
    (hr0 : 0 ≤ r.val)
    (hr2 : 0 < num2.val) :
    r.val * (num2.val + 1) ≤ num1.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9)
    (r : Std.I64) (hr : Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r)
    (hr0 : 0 ≤ r.val)
    (hr2 : 0 < num2.val), r.val * (num2.val + 1) ≤ num1.val) := by
  sorry

/-- For every num1 and num2 satisfying the preconditions, the function returns a result r (i.e., it does not fail, panic, or overflow).
  Preconditions: 1 <= num1 <= 10^9 and -10^9 <= num2 <= 10^9. -/
theorem spec_12 (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9) :
    ∃ r : Std.I64, Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9), ∃ r : Std.I64, Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r) := by
  sorry

/-- If num2 = -1, then the function returns a result r and r is the smallest integer k >= 1 such that popcount(num1 + k) <= k, where popcount(x) is the number of 1s in the binary representation of x.
  Preconditions: 1 <= num1 <= 10^9 and num2 = -1. -/
theorem spec_13 (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9) (h2 : num2.val = -1) :
    ∃ r : Std.I64,
      Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r ∧
        1 ≤ r.val ∧
        (popcount (num1.val + r.val).toNat : ℤ) ≤ r.val ∧
        ∀ k : ℤ, 1 ≤ k → (popcount (num1.val + k).toNat : ℤ) ≤ k → r.val ≤ k := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9) (h2 : num2.val = -1), ∃ r : Std.I64,
      Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r ∧
        1 ≤ r.val ∧
        (popcount (num1.val + r.val).toNat : ℤ) ≤ r.val ∧
        ∀ k : ℤ, 1 ≤ k → (popcount (num1.val + k).toNat : ℤ) ≤ k → r.val ≤ k) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, it holds that popcount(num1 - r*num2) <= r, where popcount(x) is the number of 1s in the binary representation of x.
  Preconditions: 1 <= num1 <= 10^9 and -10^9 <= num2 <= 10^9. -/
theorem spec_14 (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9)
    (r : Std.I64) (hr : Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r)
    (hr0 : 0 ≤ r.val) :
    (popcount (num1.val - r.val * num2.val).toNat : ℤ) ≤ r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (num1 num2 : Std.I64)
    (h1 : 1 ≤ num1.val) (h1' : num1.val ≤ (10 : ℤ) ^ 9)
    (h2 : -((10 : ℤ) ^ 9) ≤ num2.val) (h2' : num2.val ≤ (10 : ℤ) ^ 9)
    (r : Std.I64) (hr : Aegis.MakeTheIntegerZero.make_the_integer_zero num1 num2 = ok r)
    (hr0 : 0 ≤ r.val), (popcount (num1.val - r.val * num2.val).toNat : ℤ) ≤ r.val) := by
  sorry

end AegisSpec.MakeTheIntegerZero
