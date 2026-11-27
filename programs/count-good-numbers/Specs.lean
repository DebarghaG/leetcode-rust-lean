import Aegis.CountGoodNumbers.Code.Funs

/-!
# Specifications of `Aegis.CountGoodNumbers.count_good_numbers`

LeetCode problem `count-good-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountGoodNumbers

def imod (m a : ℤ) : ℤ := Int.emod a m

/-- The function returns a result r and does not fail. If exp = 0, then r = ControlFlow.break result. If exp > 0, then r = ControlFlow.continue (base_new, exp_new, result_new), where the three components are in the order (base, exponent, result), with base_new = (base * base) mod modulus, exp_new = exp / 2 (integer division), and result_new = (result * base) mod modulus if exp mod 2 = 1, and result_new = result if exp mod 2 = 0. Here a mod M means the unique integer q with 0 <= q < M and q congruent to a modulo M.
  Preconditions: modulus = 1000000007; 0 <= base < modulus; 0 <= exp; 0 <= result < modulus. -/
theorem spec_1 (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp_lo : 0 ≤ exp.val)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val) :
    ∃ r : ControlFlow (Std.I64 × Std.I64 × Std.I64) Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok r ∧
      (exp.val = 0 → r = ControlFlow.done result) ∧
      (0 < exp.val →
        ∃ base_new exp_new result_new : Std.I64,
          r = ControlFlow.cont (base_new, exp_new, result_new) ∧
          base_new.val = imod modulus.val (base.val * base.val) ∧
          exp_new.val = exp.val / 2 ∧
          result_new.val =
            (if exp.val % 2 = 1 then imod modulus.val (result.val * base.val)
             else result.val)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp_lo : 0 ≤ exp.val)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val), ∃ r : ControlFlow (Std.I64 × Std.I64 × Std.I64) Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok r ∧
      (exp.val = 0 → r = ControlFlow.done result) ∧
      (0 < exp.val →
        ∃ base_new exp_new result_new : Std.I64,
          r = ControlFlow.cont (base_new, exp_new, result_new) ∧
          base_new.val = imod modulus.val (base.val * base.val) ∧
          exp_new.val = exp.val / 2 ∧
          result_new.val =
            (if exp.val % 2 = 1 then imod modulus.val (result.val * base.val)
             else result.val))) := by
  sorry

/-- The function returns a value; it does not fail, panic, overflow, or divide by zero.
  Preconditions: 0 < modulus <= 1000000007; 0 <= base < modulus; 0 <= exp; 0 <= result < modulus. -/
theorem spec_2 (modulus base exp result : Std.I64)
    (hM_lo : 0 < modulus.val) (hM_hi : modulus.val ≤ 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp_lo : 0 ≤ exp.val)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val) :
    ∃ r : ControlFlow (Std.I64 × Std.I64 × Std.I64) Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (modulus base exp result : Std.I64)
    (hM_lo : 0 < modulus.val) (hM_hi : modulus.val ≤ 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp_lo : 0 ≤ exp.val)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val), ∃ r : ControlFlow (Std.I64 × Std.I64 × Std.I64) Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok r) := by
  sorry

/-- The function returns ControlFlow.break result.
  Preconditions: modulus = 1000000007; 0 <= base < modulus; exp = 0; 0 <= result < modulus. -/
theorem spec_3 (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : exp.val = 0)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val) :
    Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
      = ok (ControlFlow.done result) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : exp.val = 0)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val), Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
      = ok (ControlFlow.done result)) := by
  sorry

/-- The function returns a value of the form ControlFlow.continue (base_new, exp_new, result_new) for some base_new, exp_new, result_new; it does not return ControlFlow.break.
  Preconditions: modulus = 1000000007; 0 <= base < modulus; exp > 0; 0 <= result < modulus. -/
theorem spec_4 (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : 0 < exp.val)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val) :
    (∃ base_new exp_new result_new : Std.I64,
        Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
          = ok (ControlFlow.cont (base_new, exp_new, result_new))) ∧
    (¬ ∃ r : Std.I64,
        Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
          = ok (ControlFlow.done r)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : 0 < exp.val)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val), (∃ base_new exp_new result_new : Std.I64,
        Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
          = ok (ControlFlow.cont (base_new, exp_new, result_new))) ∧
    (¬ ∃ r : Std.I64,
        Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
          = ok (ControlFlow.done r))) := by
  sorry

/-- Whenever the function returns ControlFlow.continue (base_new, exp_new, result_new), the second component exp_new equals exp / 2, where / is integer division of non-negative integers.
  Preconditions: modulus = 1000000007; 0 <= base < modulus; exp > 0; 0 <= result < modulus. -/
theorem spec_5 (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : 0 < exp.val)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val) :
    ∀ base_new exp_new result_new : Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok (ControlFlow.cont (base_new, exp_new, result_new)) →
      exp_new.val = exp.val / 2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : 0 < exp.val)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val), ∀ base_new exp_new result_new : Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok (ControlFlow.cont (base_new, exp_new, result_new)) →
      exp_new.val = exp.val / 2) := by
  sorry

/-- Whenever the function returns ControlFlow.continue (base_new, exp_new, result_new), the first component base_new equals (base * base) mod modulus, the unique integer in [0, modulus) congruent to base^2 modulo modulus.
  Preconditions: modulus = 1000000007; 0 <= base < modulus; exp > 0; 0 <= result < modulus. -/
theorem spec_6 (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : 0 < exp.val)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val) :
    ∀ base_new exp_new result_new : Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok (ControlFlow.cont (base_new, exp_new, result_new)) →
      base_new.val = imod modulus.val (base.val * base.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : 0 < exp.val)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val), ∀ base_new exp_new result_new : Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok (ControlFlow.cont (base_new, exp_new, result_new)) →
      base_new.val = imod modulus.val (base.val * base.val)) := by
  sorry

/-- Whenever the function returns ControlFlow.continue (base_new, exp_new, result_new), the third component result_new equals (result * base) mod modulus, the unique integer in [0, modulus) congruent to result * base modulo modulus.
  Preconditions: modulus = 1000000007; 0 <= base < modulus; exp > 0; exp mod 2 = 1; 0 <= result < modulus. -/
theorem spec_7 (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : 0 < exp.val) (hodd : exp.val % 2 = 1)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val) :
    ∀ base_new exp_new result_new : Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok (ControlFlow.cont (base_new, exp_new, result_new)) →
      result_new.val = imod modulus.val (result.val * base.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : 0 < exp.val) (hodd : exp.val % 2 = 1)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val), ∀ base_new exp_new result_new : Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok (ControlFlow.cont (base_new, exp_new, result_new)) →
      result_new.val = imod modulus.val (result.val * base.val)) := by
  sorry

/-- Whenever the function returns ControlFlow.continue (base_new, exp_new, result_new), the third component result_new equals result.
  Preconditions: modulus = 1000000007; 0 <= base < modulus; exp > 0; exp mod 2 = 0; 0 <= result < modulus. -/
theorem spec_8 (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : 0 < exp.val) (heven : exp.val % 2 = 0)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val) :
    ∀ base_new exp_new result_new : Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok (ControlFlow.cont (base_new, exp_new, result_new)) →
      result_new.val = result.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : 0 < exp.val) (heven : exp.val % 2 = 0)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val), ∀ base_new exp_new result_new : Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok (ControlFlow.cont (base_new, exp_new, result_new)) →
      result_new.val = result.val) := by
  sorry

/-- Whenever the function returns ControlFlow.continue (base_new, exp_new, result_new), we have 0 <= base_new < modulus and 0 <= result_new < modulus.
  Preconditions: modulus = 1000000007; 0 <= base < modulus; exp > 0; 0 <= result < modulus. -/
theorem spec_9 (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : 0 < exp.val)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val) :
    ∀ base_new exp_new result_new : Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok (ControlFlow.cont (base_new, exp_new, result_new)) →
      0 ≤ base_new.val ∧ base_new.val < modulus.val ∧
        0 ≤ result_new.val ∧ result_new.val < modulus.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : 0 < exp.val)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val), ∀ base_new exp_new result_new : Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok (ControlFlow.cont (base_new, exp_new, result_new)) →
      0 ≤ base_new.val ∧ base_new.val < modulus.val ∧
        0 ≤ result_new.val ∧ result_new.val < modulus.val) := by
  sorry

/-- Whenever the function returns ControlFlow.continue (base_new, exp_new, result_new), the congruence result_new * (base_new^exp_new) is congruent to result * (base^exp) modulo modulus. Here exponentiation is ordinary integer exponentiation, and exp_new is non-negative.
  Preconditions: modulus = 1000000007; 0 <= base < modulus; exp > 0; 0 <= result < modulus. -/
theorem spec_10 (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : 0 < exp.val)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val) :
    ∀ base_new exp_new result_new : Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok (ControlFlow.cont (base_new, exp_new, result_new)) →
      result_new.val * base_new.val ^ exp_new.val.toNat
        ≡ result.val * base.val ^ exp.val.toNat [ZMOD modulus.val] := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : 0 < exp.val)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val), ∀ base_new exp_new result_new : Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok (ControlFlow.cont (base_new, exp_new, result_new)) →
      result_new.val * base_new.val ^ exp_new.val.toNat
        ≡ result.val * base.val ^ exp.val.toNat [ZMOD modulus.val]) := by
  sorry

/-- Whenever the function returns ControlFlow.continue (base_new, exp_new, result_new), we have 0 <= exp_new < exp.
  Preconditions: modulus = 1000000007; 0 <= base < modulus; exp > 0; 0 <= result < modulus. -/
theorem spec_11 (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : 0 < exp.val)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val) :
    ∀ base_new exp_new result_new : Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok (ControlFlow.cont (base_new, exp_new, result_new)) →
      0 ≤ exp_new.val ∧ exp_new.val < exp.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : 0 < exp.val)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val), ∀ base_new exp_new result_new : Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok (ControlFlow.cont (base_new, exp_new, result_new)) →
      0 ≤ exp_new.val ∧ exp_new.val < exp.val) := by
  sorry

/-- The function returns ControlFlow.continue ((base * base) mod modulus, 0, (result * base) mod modulus).
  Preconditions: modulus = 1000000007; 0 <= base < modulus; exp = 1; 0 <= result < modulus. -/
theorem spec_12 (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : exp.val = 1)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val) :
    ∃ base_new exp_new result_new : Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok (ControlFlow.cont (base_new, exp_new, result_new)) ∧
      base_new.val = imod modulus.val (base.val * base.val) ∧
      exp_new.val = 0 ∧
      result_new.val = imod modulus.val (result.val * base.val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (modulus base exp result : Std.I64)
    (hM : modulus.val = 1000000007)
    (hbase_lo : 0 ≤ base.val) (hbase_hi : base.val < modulus.val)
    (hexp : exp.val = 1)
    (hres_lo : 0 ≤ result.val) (hres_hi : result.val < modulus.val), ∃ base_new exp_new result_new : Std.I64,
      Aegis.CountGoodNumbers.count_good_numbers.pow_mod_loop.body modulus base exp result
        = ok (ControlFlow.cont (base_new, exp_new, result_new)) ∧
      base_new.val = imod modulus.val (base.val * base.val) ∧
      exp_new.val = 0 ∧
      result_new.val = imod modulus.val (result.val * base.val)) := by
  sorry

end AegisSpec.CountGoodNumbers
