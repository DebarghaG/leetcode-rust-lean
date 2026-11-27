import Aegis.Sum.Code.Funs

/-!
# Specifications of `Aegis.Sum.sum`

LeetCode problem `add-two-integers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.Sum

theorem i64Bounds (x : ℤ) (hlo : -100 ≤ x) (hhi : x ≤ 100) :
    -2 ^ (Aeneas.Std.IScalarTy.I64.numBits - 1) ≤ x ∧
      x < 2 ^ (Aeneas.Std.IScalarTy.I64.numBits - 1) := by
  have h : Aeneas.Std.IScalarTy.I64.numBits = 64 := Aeneas.Std.IScalarTy.I64_numBits_eq
  rw [h]
  norm_num
  omega

def i64OfInt (x : ℤ) (hlo : -100 ≤ x) (hhi : x ≤ 100) : Aeneas.Std.I64 :=
  Aeneas.Std.IScalar.ofIntCore x (i64Bounds x hlo hhi)

theorem i64OfInt_val (x : ℤ) (hlo : -100 ≤ x) (hhi : x ≤ 100) :
    (i64OfInt x hlo hhi).val = x :=
  Aeneas.Std.IScalar.ofInt_val_eq (i64Bounds x hlo hhi)

/-- The function returns a result r, and the signed mathematical integer value of r equals num1 + num2.
  Preconditions: num1 and num2 are 64-bit signed integers whose mathematical values satisfy -100 <= num1 <= 100 and -100 <= num2 <= 100. -/
theorem spec_1 (num1 num2 : Aeneas.Std.I64)
    (h1lo : -100 ≤ num1.val) (h1hi : num1.val ≤ 100)
    (h2lo : -100 ≤ num2.val) (h2hi : num2.val ≤ 100) :
    ∃ r : Aeneas.Std.I64,
      Aegis.Sum.sum num1 num2 = ok r ∧ r.val = num1.val + num2.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (num1 num2 : Aeneas.Std.I64)
    (h1lo : -100 ≤ num1.val) (h1hi : num1.val ≤ 100)
    (h2lo : -100 ≤ num2.val) (h2hi : num2.val ≤ 100), ∃ r : Aeneas.Std.I64,
      Aegis.Sum.sum num1 num2 = ok r ∧ r.val = num1.val + num2.val) := by
  sorry

/-- For every such invocation, the function returns a result; it does not fail, overflow, or panic.
  Preconditions: num1 and num2 are 64-bit signed integers whose mathematical values satisfy -100 <= num1 <= 100 and -100 <= num2 <= 100. -/
theorem spec_2 (num1 num2 : Aeneas.Std.I64)
    (h1lo : -100 ≤ num1.val) (h1hi : num1.val ≤ 100)
    (h2lo : -100 ≤ num2.val) (h2hi : num2.val ≤ 100) :
    ∃ r : Aeneas.Std.I64, Aegis.Sum.sum num1 num2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (num1 num2 : Aeneas.Std.I64)
    (h1lo : -100 ≤ num1.val) (h1hi : num1.val ≤ 100)
    (h2lo : -100 ≤ num2.val) (h2hi : num2.val ≤ 100), ∃ r : Aeneas.Std.I64, Aegis.Sum.sum num1 num2 = ok r) := by
  sorry

/-- For every such invocation, the function returns a result r whose signed mathematical integer value lies in the inclusive range [-200, 200].
  Preconditions: num1 and num2 are 64-bit signed integers whose mathematical values satisfy -100 <= num1 <= 100 and -100 <= num2 <= 100. -/
theorem spec_3 (num1 num2 : Aeneas.Std.I64)
    (h1lo : -100 ≤ num1.val) (h1hi : num1.val ≤ 100)
    (h2lo : -100 ≤ num2.val) (h2hi : num2.val ≤ 100) :
    ∃ r : Aeneas.Std.I64,
      Aegis.Sum.sum num1 num2 = ok r ∧ -200 ≤ r.val ∧ r.val ≤ 200 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (num1 num2 : Aeneas.Std.I64)
    (h1lo : -100 ≤ num1.val) (h1hi : num1.val ≤ 100)
    (h2lo : -100 ≤ num2.val) (h2hi : num2.val ≤ 100), ∃ r : Aeneas.Std.I64,
      Aegis.Sum.sum num1 num2 = ok r ∧ -200 ≤ r.val ∧ r.val ≤ 200) := by
  sorry

/-- For every such pair, the two calls sum(num1, num2) and sum(num2, num1) both return results, and the signed mathematical integer values of those two results are equal.
  Preconditions: num1 and num2 are 64-bit signed integers whose mathematical values satisfy -100 <= num1 <= 100 and -100 <= num2 <= 100. -/
theorem spec_4 (num1 num2 : Aeneas.Std.I64)
    (h1lo : -100 ≤ num1.val) (h1hi : num1.val ≤ 100)
    (h2lo : -100 ≤ num2.val) (h2hi : num2.val ≤ 100) :
    ∃ r1 r2 : Aeneas.Std.I64,
      Aegis.Sum.sum num1 num2 = ok r1 ∧
      Aegis.Sum.sum num2 num1 = ok r2 ∧ r1.val = r2.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (num1 num2 : Aeneas.Std.I64)
    (h1lo : -100 ≤ num1.val) (h1hi : num1.val ≤ 100)
    (h2lo : -100 ≤ num2.val) (h2hi : num2.val ≤ 100), ∃ r1 r2 : Aeneas.Std.I64,
      Aegis.Sum.sum num1 num2 = ok r1 ∧
      Aegis.Sum.sum num2 num1 = ok r2 ∧ r1.val = r2.val) := by
  sorry

/-- The calls sum(a + k, b) and sum(a, b) both return results r1 and r2, and signed_value(r1) = signed_value(r2) + k, where signed_value denotes the mathematical integer value of the result.
  Preconditions: a, b, and k are integers such that -100 <= a <= 100, -100 <= a + k <= 100, and -100 <= b <= 100. -/
theorem spec_5 (a b : Aeneas.Std.I64) (k : ℤ)
    (halo : -100 ≤ a.val) (hahi : a.val ≤ 100)
    (haklo : -100 ≤ a.val + k) (hakhi : a.val + k ≤ 100)
    (hblo : -100 ≤ b.val) (hbhi : b.val ≤ 100) :
    ∃ r1 r2 : Aeneas.Std.I64,
      Aegis.Sum.sum (i64OfInt (a.val + k) haklo hakhi) b = ok r1 ∧
      Aegis.Sum.sum a b = ok r2 ∧ r1.val = r2.val + k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (a b : Aeneas.Std.I64) (k : ℤ)
    (halo : -100 ≤ a.val) (hahi : a.val ≤ 100)
    (haklo : -100 ≤ a.val + k) (hakhi : a.val + k ≤ 100)
    (hblo : -100 ≤ b.val) (hbhi : b.val ≤ 100), ∃ r1 r2 : Aeneas.Std.I64,
      Aegis.Sum.sum (i64OfInt (a.val + k) haklo hakhi) b = ok r1 ∧
      Aegis.Sum.sum a b = ok r2 ∧ r1.val = r2.val + k) := by
  sorry

end AegisSpec.Sum
