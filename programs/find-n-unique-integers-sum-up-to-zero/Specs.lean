import Aegis.SumZero.Code.Funs

/-!
# Specifications of `Aegis.SumZero.sum_zero`

LeetCode problem `find-n-unique-integers-sum-up-to-zero`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SumZero

  def i64ToInt (x : I64) : ℤ := (x : IScalar IScalarTy.I64).val

  /-- For every n satisfying the precondition, whenever sum_zero n returns a result r, the following all hold: (1) len(r) = n; (2) for every i and j with 0 <= i < j < len(r), r[i] != r[j]; (3) interpreting each element of r as an integer, the mathematical sum of r[0], r[1], ..., r[len(r)-1] equals 0.
    Preconditions: The input n is an I64 with 1 <= n <= 1000. -/
  theorem spec_1 (n : I64) (hlo : 1 ≤ i64ToInt n) (hhi : i64ToInt n ≤ 1000) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.SumZero.sum_zero n = ok r →
        (r.val.length : ℤ) = i64ToInt n ∧
          (∀ (i j : Nat) (hi : i < r.val.length) (hj : j < r.val.length),
            i < j → r.val[i]'hi ≠ r.val[j]'hj) ∧
          (r.val.map i64ToInt).sum = 0 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (hlo : 1 ≤ i64ToInt n) (hhi : i64ToInt n ≤ 1000), ∀ r : alloc.vec.Vec I64,
          Aegis.SumZero.sum_zero n = ok r →
          (r.val.length : ℤ) = i64ToInt n ∧
            (∀ (i j : Nat) (hi : i < r.val.length) (hj : j < r.val.length),
              i < j → r.val[i]'hi ≠ r.val[j]'hj) ∧
            (r.val.map i64ToInt).sum = 0) := by
    sorry

  /-- For every n satisfying the precondition, sum_zero n returns a result r; it does not fail, overflow, panic, or go out of bounds.
    Preconditions: The input n is an I64 with 1 <= n <= 1000. -/
  theorem spec_2 (n : I64) (hlo : 1 ≤ i64ToInt n) (hhi : i64ToInt n ≤ 1000) :
      ∃ r : alloc.vec.Vec I64, Aegis.SumZero.sum_zero n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (hlo : 1 ≤ i64ToInt n) (hhi : i64ToInt n ≤ 1000), ∃ r : alloc.vec.Vec I64, Aegis.SumZero.sum_zero n = ok r) := by
    sorry

  /-- For every n satisfying the precondition, whenever sum_zero n returns a result r, there exists an index i with 0 <= i < len(r) such that r[i] > 0.
    Preconditions: The input n is an I64 with 2 <= n <= 1000. -/
  theorem spec_3 (n : I64) (hlo : 2 ≤ i64ToInt n) (hhi : i64ToInt n ≤ 1000) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.SumZero.sum_zero n = ok r →
        ∃ (i : Nat) (hi : i < r.val.length), 0 < i64ToInt (r.val[i]'hi) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (hlo : 2 ≤ i64ToInt n) (hhi : i64ToInt n ≤ 1000), ∀ r : alloc.vec.Vec I64,
          Aegis.SumZero.sum_zero n = ok r →
          ∃ (i : Nat) (hi : i < r.val.length), 0 < i64ToInt (r.val[i]'hi)) := by
    sorry

  /-- For every n satisfying the precondition, whenever sum_zero n returns a result r, there exists an index i with 0 <= i < len(r) such that r[i] < 0.
    Preconditions: The input n is an I64 with 2 <= n <= 1000. -/
  theorem spec_4 (n : I64) (hlo : 2 ≤ i64ToInt n) (hhi : i64ToInt n ≤ 1000) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.SumZero.sum_zero n = ok r →
        ∃ (i : Nat) (hi : i < r.val.length), i64ToInt (r.val[i]'hi) < 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (hlo : 2 ≤ i64ToInt n) (hhi : i64ToInt n ≤ 1000), ∀ r : alloc.vec.Vec I64,
          Aegis.SumZero.sum_zero n = ok r →
          ∃ (i : Nat) (hi : i < r.val.length), i64ToInt (r.val[i]'hi) < 0) := by
    sorry

  end AegisSpec.SumZero
