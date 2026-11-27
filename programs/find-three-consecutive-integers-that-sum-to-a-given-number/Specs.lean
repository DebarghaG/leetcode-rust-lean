import Aegis.SumOfThree.Code.Funs

/-!
# Specifications of `Aegis.SumOfThree.sum_of_three`

LeetCode problem `find-three-consecutive-integers-that-sum-to-a-given-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SumOfThree

  /-- The function returns a result r and: if 3 divides num (i.e., there is an integer q with num = 3*q), then len(r) = 3, r[0] = q - 1, r[1] = q, and r[2] = q + 1; if 3 does not divide num, then len(r) = 0.
    Preconditions: 0 <= num <= 1000000000000000. -/
  theorem spec_1 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.SumOfThree.sum_of_three num = ok r ∧
          ((∃ q : ℤ, num.val = 3 * q) →
            ∃ (q : ℤ) (hlen : r.val.length = 3),
              num.val = 3 * q ∧ (r.val[0]).val = q - 1 ∧ (r.val[1]).val = q ∧
                (r.val[2]).val = q + 1) ∧
          (¬ (∃ q : ℤ, num.val = 3 * q) → r.val.length = 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.SumOfThree.sum_of_three num = ok r ∧
            ((∃ q : ℤ, num.val = 3 * q) →
              ∃ (q : ℤ) (hlen : r.val.length = 3),
                num.val = 3 * q ∧ (r.val[0]).val = q - 1 ∧ (r.val[1]).val = q ∧
                  (r.val[2]).val = q + 1) ∧
            (¬ (∃ q : ℤ, num.val = 3 * q) → r.val.length = 0)) := by
    sorry

  /-- The function returns a result r and len(r) is either 0 or 3.
    Preconditions: 0 <= num <= 1000000000000000. -/
  theorem spec_2 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.SumOfThree.sum_of_three num = ok r ∧
          (r.val.length = 0 ∨ r.val.length = 3) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.SumOfThree.sum_of_three num = ok r ∧
            (r.val.length = 0 ∨ r.val.length = 3)) := by
    sorry

  /-- The function returns a result r and len(r) = 3 if and only if 3 divides num (i.e., num = 3*q for some integer q).
    Preconditions: 0 <= num <= 1000000000000000. -/
  theorem spec_3 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.SumOfThree.sum_of_three num = ok r ∧
          (r.val.length = 3 ↔ ∃ q : ℤ, num.val = 3 * q) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.SumOfThree.sum_of_three num = ok r ∧
            (r.val.length = 3 ↔ ∃ q : ℤ, num.val = 3 * q)) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 3, r[0] + r[1] + r[2] = num, using mathematical integer arithmetic.
    Preconditions: 0 <= num <= 1000000000000000. -/
  theorem spec_4 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000) :
      ∀ (r : alloc.vec.Vec Std.I64), Aegis.SumOfThree.sum_of_three num = ok r →
        (hlen : r.val.length = 3) →
          (r.val[0]).val + (r.val[1]).val + (r.val[2]).val = num.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000), ∀ (r : alloc.vec.Vec Std.I64), Aegis.SumOfThree.sum_of_three num = ok r →
          (hlen : r.val.length = 3) →
            (r.val[0]).val + (r.val[1]).val + (r.val[2]).val = num.val) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 3, r[1] = r[0] + 1 and r[2] = r[1] + 1, using mathematical integer arithmetic.
    Preconditions: 0 <= num <= 1000000000000000. -/
  theorem spec_5 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000) :
      ∀ (r : alloc.vec.Vec Std.I64), Aegis.SumOfThree.sum_of_three num = ok r →
        (hlen : r.val.length = 3) →
          (r.val[1]).val = (r.val[0]).val + 1 ∧ (r.val[2]).val = (r.val[1]).val + 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000), ∀ (r : alloc.vec.Vec Std.I64), Aegis.SumOfThree.sum_of_three num = ok r →
          (hlen : r.val.length = 3) →
            (r.val[1]).val = (r.val[0]).val + 1 ∧ (r.val[2]).val = (r.val[1]).val + 1) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 0, there is no integer x such that x + (x + 1) + (x + 2) = num.
    Preconditions: 0 <= num <= 1000000000000000. -/
  theorem spec_6 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000) :
      ∀ (r : alloc.vec.Vec Std.I64), Aegis.SumOfThree.sum_of_three num = ok r →
        r.val.length = 0 → ¬ (∃ x : ℤ, x + (x + 1) + (x + 2) = num.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000), ∀ (r : alloc.vec.Vec Std.I64), Aegis.SumOfThree.sum_of_three num = ok r →
          r.val.length = 0 → ¬ (∃ x : ℤ, x + (x + 1) + (x + 2) = num.val)) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 3, for every integer x, if x + (x + 1) + (x + 2) = num then x = r[0].
    Preconditions: 0 <= num <= 1000000000000000. -/
  theorem spec_7 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000) :
      ∀ (r : alloc.vec.Vec Std.I64), Aegis.SumOfThree.sum_of_three num = ok r →
        (hlen : r.val.length = 3) →
          ∀ x : ℤ, x + (x + 1) + (x + 2) = num.val → x = (r.val[0]).val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000), ∀ (r : alloc.vec.Vec Std.I64), Aegis.SumOfThree.sum_of_three num = ok r →
          (hlen : r.val.length = 3) →
            ∀ x : ℤ, x + (x + 1) + (x + 2) = num.val → x = (r.val[0]).val) := by
    sorry

  /-- The function returns a result r for every num satisfying the preconditions; it does not fail by overflow, panic, or out-of-bounds access.
    Preconditions: 0 <= num <= 1000000000000000. -/
  theorem spec_8 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.SumOfThree.sum_of_three num = ok r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000), ∃ r : alloc.vec.Vec Std.I64, Aegis.SumOfThree.sum_of_three num = ok r) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 3, every entry of r lies in the interval [-1, 333333333333334]; in particular -1 <= r[0] and r[2] <= 333333333333334.
    Preconditions: 0 <= num <= 1000000000000000. -/
  theorem spec_9 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000) :
      ∀ (r : alloc.vec.Vec Std.I64), Aegis.SumOfThree.sum_of_three num = ok r →
        (hlen : r.val.length = 3) →
          (∀ e : Std.I64, e ∈ r.val → -1 ≤ e.val ∧ e.val ≤ 333333333333334) ∧
            -1 ≤ (r.val[0]).val ∧ (r.val[2]).val ≤ 333333333333334 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000), ∀ (r : alloc.vec.Vec Std.I64), Aegis.SumOfThree.sum_of_three num = ok r →
          (hlen : r.val.length = 3) →
            (∀ e : Std.I64, e ∈ r.val → -1 ≤ e.val ∧ e.val ≤ 333333333333334) ∧
              -1 ≤ (r.val[0]).val ∧ (r.val[2]).val ≤ 333333333333334) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 3, r[1] = num/3 (the exact integer quotient when 3 divides num).
    Preconditions: 0 <= num <= 1000000000000000. -/
  theorem spec_10 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000) :
      ∀ (r : alloc.vec.Vec Std.I64), Aegis.SumOfThree.sum_of_three num = ok r →
        (hlen : r.val.length = 3) → (r.val[1]).val = num.val / 3 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000), ∀ (r : alloc.vec.Vec Std.I64), Aegis.SumOfThree.sum_of_three num = ok r →
          (hlen : r.val.length = 3) → (r.val[1]).val = num.val / 3) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 3, r[0] = num/3 - 1 (the exact integer quotient when 3 divides num).
    Preconditions: 0 <= num <= 1000000000000000. -/
  theorem spec_11 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000) :
      ∀ (r : alloc.vec.Vec Std.I64), Aegis.SumOfThree.sum_of_three num = ok r →
        (hlen : r.val.length = 3) → (r.val[0]).val = num.val / 3 - 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000), ∀ (r : alloc.vec.Vec Std.I64), Aegis.SumOfThree.sum_of_three num = ok r →
          (hlen : r.val.length = 3) → (r.val[0]).val = num.val / 3 - 1) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 3, r[2] = num/3 + 1 (the exact integer quotient when 3 divides num).
    Preconditions: 0 <= num <= 1000000000000000. -/
  theorem spec_12 (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000) :
      ∀ (r : alloc.vec.Vec Std.I64), Aegis.SumOfThree.sum_of_three num = ok r →
        (hlen : r.val.length = 3) → (r.val[2]).val = num.val / 3 + 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (num : Std.I64) (hlo : 0 ≤ num.val) (hhi : num.val ≤ 1000000000000000), ∀ (r : alloc.vec.Vec Std.I64), Aegis.SumOfThree.sum_of_three num = ok r →
          (hlen : r.val.length = 3) → (r.val[2]).val = num.val / 3 + 1) := by
    sorry

  end AegisSpec.SumOfThree
