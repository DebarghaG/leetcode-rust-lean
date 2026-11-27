import Aegis.GetSum.Code.Funs

/-!
# Specifications of `Aegis.GetSum.get_sum`

LeetCode problem `sum-of-two-integers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetSum

def i64OfInt (x : ℤ) : Aeneas.Std.I64 := ⟨BitVec.ofInt 64 x⟩

lemma i64OfInt_val {x : ℤ} (h1 : -1000 ≤ x) (h2 : x ≤ 1000) : (i64OfInt x).val = x := by
  have hlt : -2 ^ (IScalarTy.I64.numBits - 1) ≤ x := by
    rw [IScalarTy.I64_numBits_eq]; norm_num; linarith
  have hlt2 : x < 2 ^ (IScalarTy.I64.numBits - 1) := by
    rw [IScalarTy.I64_numBits_eq]; norm_num; linarith
  have hb : (BitVec.ofInt 64 x).toInt = x.bmod (2 ^ 64) := BitVec.toInt_ofInt (n := 64) x
  simp only [i64OfInt, Aeneas.Std.IScalar.val]
  rw [hb]
  exact Aeneas.Std.bmod_pow_numBits_eq_of_lt IScalarTy.I64 x hlt hlt2

/-- The function returns a result r (it does not fail) such that, viewed as a mathematical integer, r = a + b, i.e. r is the ordinary integer sum of the two inputs.
  Preconditions: -1000 <= a <= 1000 and -1000 <= b <= 1000, where a and b denote the mathematical integers represented by the Std.I64 arguments. -/
theorem spec_1 (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000) :
    ∃ r : Aeneas.Std.I64, Aegis.GetSum.get_sum a b = .ok r ∧ r.val = a.val + b.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000), ∃ r : Aeneas.Std.I64, Aegis.GetSum.get_sum a b = Result.ok r ∧ r.val = a.val + b.val) := by
  sorry

/-- For every pair of inputs satisfying the constraints, the function returns some result r; it never fails, panics, or overflows.
  Preconditions: -1000 <= a <= 1000 and -1000 <= b <= 1000. -/
theorem spec_2 (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000) :
    ∃ r : Aeneas.Std.I64, Aegis.GetSum.get_sum a b = .ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000), ∃ r : Aeneas.Std.I64, Aegis.GetSum.get_sum a b = Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, we have -2000 <= r <= 2000.
  Preconditions: -1000 <= a <= 1000 and -1000 <= b <= 1000. -/
theorem spec_3 (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000) :
    ∀ r : Aeneas.Std.I64, Aegis.GetSum.get_sum a b = .ok r → -2000 ≤ r.val ∧ r.val ≤ 2000 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000), ∀ r : Aeneas.Std.I64, Aegis.GetSum.get_sum a b = Result.ok r → -2000 ≤ r.val ∧ r.val ≤ 2000) := by
  sorry

/-- Whenever the function returns a result r, we have r >= a and r >= b (in particular r >= 0).
  Preconditions: -1000 <= a <= 1000, -1000 <= b <= 1000, 0 <= a and 0 <= b. -/
theorem spec_4 (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000)
    (ha_nn : 0 ≤ a.val) (hb_nn : 0 ≤ b.val) :
    ∀ r : Aeneas.Std.I64,
      Aegis.GetSum.get_sum a b = .ok r → a.val ≤ r.val ∧ b.val ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000)
    (ha_nn : 0 ≤ a.val) (hb_nn : 0 ≤ b.val), ∀ r : Aeneas.Std.I64,
      Aegis.GetSum.get_sum a b = Result.ok r → a.val ≤ r.val ∧ b.val ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, we have r <= a and r <= b (in particular r <= 0).
  Preconditions: -1000 <= a <= 1000, -1000 <= b <= 1000, a <= 0 and b <= 0. -/
theorem spec_5 (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000)
    (ha_np : a.val ≤ 0) (hb_np : b.val ≤ 0) :
    ∀ r : Aeneas.Std.I64,
      Aegis.GetSum.get_sum a b = .ok r → r.val ≤ a.val ∧ r.val ≤ b.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000)
    (ha_np : a.val ≤ 0) (hb_np : b.val ≤ 0), ∀ r : Aeneas.Std.I64,
      Aegis.GetSum.get_sum a b = Result.ok r → r.val ≤ a.val ∧ r.val ≤ b.val) := by
  sorry

/-- Whenever the function returns a result r, r lies between the two operands: min(a, b) <= r <= max(a, b).
  Preconditions: -1000 <= a <= 1000, -1000 <= b <= 1000, and min(a, b) <= 0 <= max(a, b) (the operands have opposite signs or one of them is zero). -/
theorem spec_6 (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000)
    (hmin : min a.val b.val ≤ 0) (hmax : 0 ≤ max a.val b.val) :
    ∀ r : Aeneas.Std.I64,
      Aegis.GetSum.get_sum a b = .ok r → min a.val b.val ≤ r.val ∧ r.val ≤ max a.val b.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000)
    (hmin : min a.val b.val ≤ 0) (hmax : 0 ≤ max a.val b.val), ∀ r : Aeneas.Std.I64,
      Aegis.GetSum.get_sum a b = Result.ok r → min a.val b.val ≤ r.val ∧ r.val ≤ max a.val b.val) := by
  sorry

/-- If the call with (a1, b) returns r1 and the call with (a2, b) returns r2, then r1 <= r2.
  Preconditions: -1000 <= a1 <= a2 <= 1000 and -1000 <= b <= 1000. -/
theorem spec_7 (a1 a2 b : Aeneas.Std.I64)
    (ha1_lb : -1000 ≤ a1.val) (ha12 : a1.val ≤ a2.val) (ha2_ub : a2.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000) :
    ∀ r1 r2 : Aeneas.Std.I64,
      Aegis.GetSum.get_sum a1 b = .ok r1 →
        Aegis.GetSum.get_sum a2 b = .ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (a1 a2 b : Aeneas.Std.I64)
    (ha1_lb : -1000 ≤ a1.val) (ha12 : a1.val ≤ a2.val) (ha2_ub : a2.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000), ∀ r1 r2 : Aeneas.Std.I64,
      Aegis.GetSum.get_sum a1 b = Result.ok r1 →
        Aegis.GetSum.get_sum a2 b = Result.ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- If the call with (a, b) returns r1 and the call with (b, a) returns r2, then r1 = r2, i.e. get_sum a b = get_sum b a.
  Preconditions: -1000 <= a <= 1000 and -1000 <= b <= 1000. -/
theorem spec_8 (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000) :
    ∀ r1 r2 : Aeneas.Std.I64,
      Aegis.GetSum.get_sum a b = .ok r1 →
        Aegis.GetSum.get_sum b a = .ok r2 → r1 = r2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000), ∀ r1 r2 : Aeneas.Std.I64,
      Aegis.GetSum.get_sum a b = Result.ok r1 →
        Aegis.GetSum.get_sum b a = Result.ok r2 → r1 = r2) := by
  sorry

/-- If the call with (-a, -b) returns r' and the call with (a, b) returns r, then r' = -r, i.e. get_sum (-a) (-b) = -(get_sum a b).
  Preconditions: -1000 <= a <= 1000 and -1000 <= b <= 1000 (so -a and -b also satisfy the constraints). -/
theorem spec_9 (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000) :
    ∀ r r' : Aeneas.Std.I64,
      Aegis.GetSum.get_sum (i64OfInt (-a.val)) (i64OfInt (-b.val)) = .ok r' →
        Aegis.GetSum.get_sum a b = .ok r → r'.val = -r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000), ∀ r r' : Aeneas.Std.I64,
      Aegis.GetSum.get_sum (i64OfInt (-a.val)) (i64OfInt (-b.val)) = Result.ok r' →
        Aegis.GetSum.get_sum a b = Result.ok r → r'.val = -r.val) := by
  sorry

/-- The two calls agree: get_sum a b = get_sum a' b'.
  Preconditions: a, b, a', b' all lie in [-1000, 1000] and a + b = a' + b'. -/
theorem spec_10 (a b a' b' : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000)
    (ha'_lb : -1000 ≤ a'.val) (ha'_ub : a'.val ≤ 1000)
    (hb'_lb : -1000 ≤ b'.val) (hb'_ub : b'.val ≤ 1000)
    (hsum : a.val + b.val = a'.val + b'.val) :
    ∀ r r' : Aeneas.Std.I64,
      Aegis.GetSum.get_sum a b = .ok r →
        Aegis.GetSum.get_sum a' b' = .ok r' → r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (a b a' b' : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000)
    (ha'_lb : -1000 ≤ a'.val) (ha'_ub : a'.val ≤ 1000)
    (hb'_lb : -1000 ≤ b'.val) (hb'_ub : b'.val ≤ 1000)
    (hsum : a.val + b.val = a'.val + b'.val), ∀ r r' : Aeneas.Std.I64,
      Aegis.GetSum.get_sum a b = Result.ok r →
        Aegis.GetSum.get_sum a' b' = Result.ok r' → r = r') := by
  sorry

/-- If the call with (a + c, b + c) returns r' and the call with (a, b) returns r, then, viewed as mathematical integers, r' = r + 2 * c (equivalently, the returned value for (a+c, b+c) equals the returned value for (a,b) plus 2c).
  Preconditions: -1000 <= a <= 1000, -1000 <= b <= 1000, and c is an integer such that -1000 <= a + c <= 1000 and -1000 <= b + c <= 1000. -/
theorem spec_11 (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000)
    (c : ℤ)
    (hac_lb : -1000 ≤ a.val + c) (hac_ub : a.val + c ≤ 1000)
    (hbc_lb : -1000 ≤ b.val + c) (hbc_ub : b.val + c ≤ 1000) :
    ∀ r r' : Aeneas.Std.I64,
      Aegis.GetSum.get_sum (i64OfInt (a.val + c)) (i64OfInt (b.val + c)) = .ok r' →
        Aegis.GetSum.get_sum a b = .ok r → r'.val = r.val + 2 * c := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000)
    (c : ℤ)
    (hac_lb : -1000 ≤ a.val + c) (hac_ub : a.val + c ≤ 1000)
    (hbc_lb : -1000 ≤ b.val + c) (hbc_ub : b.val + c ≤ 1000), ∀ r r' : Aeneas.Std.I64,
      Aegis.GetSum.get_sum (i64OfInt (a.val + c)) (i64OfInt (b.val + c)) = Result.ok r' →
        Aegis.GetSum.get_sum a b = Result.ok r → r'.val = r.val + 2 * c) := by
  sorry

/-- If a = 0, the call returns b; if b = 0, the call returns a (the value 0 is an identity for this operation on both sides).
  Preconditions: -1000 <= a <= 1000 and -1000 <= b <= 1000, and at least one of a, b is 0. -/
theorem spec_12 (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000)
    (hzero : a.val = 0 ∨ b.val = 0) :
    ∀ r : Aeneas.Std.I64,
      Aegis.GetSum.get_sum a b = .ok r → (a.val = 0 → r = b) ∧ (b.val = 0 → r = a) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (a b : Aeneas.Std.I64)
    (ha_lb : -1000 ≤ a.val) (ha_ub : a.val ≤ 1000)
    (hb_lb : -1000 ≤ b.val) (hb_ub : b.val ≤ 1000)
    (hzero : a.val = 0 ∨ b.val = 0), ∀ r : Aeneas.Std.I64,
      Aegis.GetSum.get_sum a b = Result.ok r → (a.val = 0 → r = b) ∧ (b.val = 0 → r = a)) := by
  sorry

end AegisSpec.GetSum
