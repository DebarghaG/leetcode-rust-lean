import Aegis.HasAlternatingBits.Code.Funs

/-!
# Specifications of `Aegis.HasAlternatingBits.has_alternating_bits`

LeetCode problem `binary-number-with-alternating-bits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.HasAlternatingBits

  def bitAt (m : ℤ) (i : ℕ) : ℤ := (m / (2 : ℤ) ^ i) % 2

  def IsBitLength (m : ℤ) (k : ℕ) : Prop :=
    0 < k ∧ (2 : ℤ) ^ (k - 1) ≤ m ∧ m < (2 : ℤ) ^ k

  def AlternatesUpTo (m : ℤ) (k : ℕ) : Prop :=
    ∀ i : ℕ, i + 1 < k → bitAt m i ≠ bitAt m (i + 1)

  def HasAlternatingDigits (m : ℤ) : Prop :=
    ∀ k : ℕ, IsBitLength m k → AlternatesUpTo m k

  def pow2DivThree (k : ℕ) : ℤ := ((2 : ℤ) ^ (k + 1)) / 3

  lemma i64_val_bounds (n : Aeneas.Std.I64) : -2 ^ 63 ≤ n.val ∧ n.val ≤ 2 ^ 63 - 1 := by
    have h1 := @BitVec.le_toInt 64 n.bv
    have h2 := @BitVec.toInt_lt 64 n.bv
    simp only [Aeneas.Std.IScalar.val] at h1 h2 ⊢
    norm_num at h1 h2 ⊢
    omega

  def i64OfInt (x : ℤ) (h : -2 ^ 63 ≤ x ∧ x ≤ 2 ^ 63 - 1) : Aeneas.Std.I64 :=
    Aeneas.Std.I64.ofInt x (by
      have hmin : Aeneas.Std.IScalar.cMin Aeneas.Std.IScalarTy.I64 = -2 ^ 63 := by decide
      have hmax : Aeneas.Std.IScalar.cMax Aeneas.Std.IScalarTy.I64 = 2 ^ 63 - 1 := by decide
      omega)

  def halfI64 (n : Aeneas.Std.I64) : Aeneas.Std.I64 :=
    i64OfInt (n.val / 2) (by
      have hb := i64_val_bounds n
      omega)

  def doubleI64 (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : 2 * n.val ≤ 2 ^ 31 - 1) :
      Aeneas.Std.I64 :=
    i64OfInt (2 * n.val) (by omega)

  /-- The call has_alternating_bits n returns a result r (it does not fail), and r = true if and only if the following holds: let k be the unique positive integer with 2^(k-1) <= n < 2^k, and for 0 <= i < k let bit_i = (n / 2^i) mod 2 (integer division and remainder). Then for every i with 0 <= i < k-1, bit_i != bit_{i+1}.
    Preconditions: 1 <= n <= 2^31 - 1. -/
  theorem spec_1 (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2 ^ 31 - 1) :
      ∃ r, Aegis.HasAlternatingBits.has_alternating_bits n = ok r ∧
        (r = true ↔ HasAlternatingDigits n.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2 ^ 31 - 1), ∃ r, Aegis.HasAlternatingBits.has_alternating_bits n = ok r ∧
          (r = true ↔ HasAlternatingDigits n.val)) := by
    sorry

  /-- The call has_alternating_bits n returns a result of type Bool; it does not fail.
    Preconditions: 1 <= n <= 2^31 - 1. -/
  theorem spec_2 (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2 ^ 31 - 1) :
      ∃ r, Aegis.HasAlternatingBits.has_alternating_bits n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2 ^ 31 - 1), ∃ r, Aegis.HasAlternatingBits.has_alternating_bits n = ok r) := by
    sorry

  /-- The call has_alternating_bits n returns true.
    Preconditions: n = 1. -/
  theorem spec_3 (n : Aeneas.Std.I64) (hn : n.val = 1) :
      Aegis.HasAlternatingBits.has_alternating_bits n = ok true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn : n.val = 1), Aegis.HasAlternatingBits.has_alternating_bits n = ok true) := by
    sorry

  /-- The call has_alternating_bits n returns false.
    Preconditions: n = 3. -/
  theorem spec_4 (n : Aeneas.Std.I64) (hn : n.val = 3) :
      Aegis.HasAlternatingBits.has_alternating_bits n = ok false := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn : n.val = 3), Aegis.HasAlternatingBits.has_alternating_bits n = ok false) := by
    sorry

  /-- If has_alternating_bits n returns true, then has_alternating_bits (n / 2) returns a result equal to true, where n / 2 is integer division.
    Preconditions: 2 <= n <= 2^31 - 1. -/
  theorem spec_5 (n : Aeneas.Std.I64) (h1 : 2 ≤ n.val) (h2 : n.val ≤ 2 ^ 31 - 1)
      (h : Aegis.HasAlternatingBits.has_alternating_bits n = ok true) :
      ∃ r, Aegis.HasAlternatingBits.has_alternating_bits (halfI64 n) = ok r ∧ r = true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (h1 : 2 ≤ n.val) (h2 : n.val ≤ 2 ^ 31 - 1)
        (h : Aegis.HasAlternatingBits.has_alternating_bits n = ok true), ∃ r, Aegis.HasAlternatingBits.has_alternating_bits (halfI64 n) = ok r ∧ r = true) := by
    sorry

  /-- If has_alternating_bits n returns true, then has_alternating_bits (2*n) returns a result equal to true.
    Preconditions: 1 <= n, n is odd, and 2*n <= 2^31 - 1. -/
  theorem spec_6 (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val)
      (hodd : ∃ q : ℤ, n.val = 2 * q + 1) (h2 : 2 * n.val ≤ 2 ^ 31 - 1)
      (h : Aegis.HasAlternatingBits.has_alternating_bits n = ok true) :
      ∃ r, Aegis.HasAlternatingBits.has_alternating_bits (doubleI64 n h1 h2) = ok r ∧
        r = true := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val)
        (hodd : ∃ q : ℤ, n.val = 2 * q + 1) (h2 : 2 * n.val ≤ 2 ^ 31 - 1)
        (h : Aegis.HasAlternatingBits.has_alternating_bits n = ok true), ∃ r, Aegis.HasAlternatingBits.has_alternating_bits (doubleI64 n h1 h2) = ok r ∧
          r = true) := by
    sorry

  /-- If has_alternating_bits n returns true, then for every i with 0 <= i <= k-3, where k is the unique positive integer with 2^(k-1) <= n < 2^k, we have ((n / 2^i) mod 2) = ((n / 2^(i+2)) mod 2).
    Preconditions: 1 <= n <= 2^31 - 1. -/
  theorem spec_7 (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2 ^ 31 - 1)
      (h : Aegis.HasAlternatingBits.has_alternating_bits n = ok true) :
      ∀ k : ℕ, IsBitLength n.val k → ∀ i : ℕ, i + 3 ≤ k → bitAt n.val i = bitAt n.val (i + 2) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2 ^ 31 - 1)
        (h : Aegis.HasAlternatingBits.has_alternating_bits n = ok true), ∀ k : ℕ, IsBitLength n.val k → ∀ i : ℕ, i + 3 ≤ k → bitAt n.val i = bitAt n.val (i + 2)) := by
    sorry

  /-- If has_alternating_bits n returns true, then there exists an integer k with 1 <= k <= 31 such that 2^(k-1) <= n < 2^k and n = floor(2^(k+1) / 3), where floor is the greatest integer not exceeding the rational value.
    Preconditions: 1 <= n <= 2^31 - 1. -/
  theorem spec_8 (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2 ^ 31 - 1)
      (h : Aegis.HasAlternatingBits.has_alternating_bits n = ok true) :
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ 31 ∧ IsBitLength n.val k ∧ n.val = pow2DivThree k := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2 ^ 31 - 1)
        (h : Aegis.HasAlternatingBits.has_alternating_bits n = ok true), ∃ k : ℕ, 1 ≤ k ∧ k ≤ 31 ∧ IsBitLength n.val k ∧ n.val = pow2DivThree k) := by
    sorry

  /-- If has_alternating_bits n returns true, then n <= 1431655765.
    Preconditions: 1 <= n <= 2^31 - 1. -/
  theorem spec_9 (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2 ^ 31 - 1)
      (h : Aegis.HasAlternatingBits.has_alternating_bits n = ok true) :
      n.val ≤ 1431655765 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2 ^ 31 - 1)
        (h : Aegis.HasAlternatingBits.has_alternating_bits n = ok true), n.val ≤ 1431655765) := by
    sorry

  end AegisSpec.HasAlternatingBits
