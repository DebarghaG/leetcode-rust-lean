import Aegis.Tribonacci.Code.Funs

/-!
# Specifications of `Aegis.Tribonacci.tribonacci`

LeetCode problem `n-th-tribonacci-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.Tribonacci

  def trib : ℕ → ℤ
    | 0 => 0
    | 1 => 1
    | 2 => 1
    | k + 3 => trib k + trib (k + 1) + trib (k + 2)
  termination_by n => n
  decreasing_by all_goals omega

  def i64OfInt (x : ℤ) : Std.I64 := Aeneas.Std.IScalar.mk (BitVec.ofInt 64 x)

  theorem i64OfInt_val (x : ℤ) (hlo : -9223372036854775808 ≤ x)
      (hhi : x ≤ 9223372036854775807) : (i64OfInt x).val = x := by
    have h := Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds 63 x (by norm_num; omega)
      (by norm_num; omega)
    simp only [i64OfInt, Aeneas.Std.IScalar.val]
    simpa using h

  def TribPrefix (a : ℕ → ℤ) (N : ℕ) : Prop :=
    a 0 = 0 ∧
    (1 ≤ N → a 1 = 1) ∧
    (2 ≤ N → a 2 = 1) ∧
    (∀ i : ℕ, i + 3 ≤ N → a (i + 3) = a i + a (i + 1) + a (i + 2))

  /-- The function returns a result r such that r = T(n), where T is the sequence defined by T(0)=0, T(1)=1, T(2)=1, and T(k+3)=T(k)+T(k+1)+T(k+2) for all k>=0.
    Preconditions: 0 <= n <= 37, where n is the integer value of the input. -/
  theorem spec_1 (n : Std.I64) (hlo : 0 ≤ n.val) (hhi : n.val ≤ 37) :
      ∃ r : Std.I64, Aegis.Tribonacci.tribonacci n = ok r ∧ r.val = trib n.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hlo : 0 ≤ n.val) (hhi : n.val ≤ 37), ∃ r : Std.I64, Aegis.Tribonacci.tribonacci n = ok r ∧ r.val = trib n.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= 2082876103.
    Preconditions: 0 <= n <= 37. -/
  theorem spec_2 (n : Std.I64) (hlo : 0 ≤ n.val) (hhi : n.val ≤ 37) :
      ∀ r : Std.I64, Aegis.Tribonacci.tribonacci n = ok r → 0 ≤ r.val ∧ r.val ≤ 2082876103 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hlo : 0 ≤ n.val) (hhi : n.val ≤ 37), ∀ r : Std.I64, Aegis.Tribonacci.tribonacci n = ok r → 0 ≤ r.val ∧ r.val ≤ 2082876103) := by
    sorry

  /-- Let r = tribonacci(n), r1 = tribonacci(n-1), r2 = tribonacci(n-2), r3 = tribonacci(n-3). If all these calls return results, then r = r1 + r2 + r3.
    Preconditions: 3 <= n <= 37. -/
  theorem spec_3 (n : Std.I64) (hlo : 3 ≤ n.val) (hhi : n.val ≤ 37) :
      ∀ r r1 r2 r3 : Std.I64,
        Aegis.Tribonacci.tribonacci n = ok r →
        Aegis.Tribonacci.tribonacci (i64OfInt (n.val - 1)) = ok r1 →
        Aegis.Tribonacci.tribonacci (i64OfInt (n.val - 2)) = ok r2 →
        Aegis.Tribonacci.tribonacci (i64OfInt (n.val - 3)) = ok r3 →
        r.val = r1.val + r2.val + r3.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hlo : 3 ≤ n.val) (hhi : n.val ≤ 37), ∀ r r1 r2 r3 : Std.I64,
          Aegis.Tribonacci.tribonacci n = ok r →
          Aegis.Tribonacci.tribonacci (i64OfInt (n.val - 1)) = ok r1 →
          Aegis.Tribonacci.tribonacci (i64OfInt (n.val - 2)) = ok r2 →
          Aegis.Tribonacci.tribonacci (i64OfInt (n.val - 3)) = ok r3 →
          r.val = r1.val + r2.val + r3.val) := by
    sorry

  /-- Let rn = tribonacci(n) and rm = tribonacci(m). If both calls return results, then rn <= rm.
    Preconditions: 0 <= n <= m <= 37. -/
  theorem spec_4 (n m : Std.I64) (hn : 0 ≤ n.val) (hnm : n.val ≤ m.val)
      (hm : m.val ≤ 37) :
      ∀ rn rm : Std.I64,
        Aegis.Tribonacci.tribonacci n = ok rn →
        Aegis.Tribonacci.tribonacci m = ok rm →
        rn.val ≤ rm.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n m : Std.I64) (hn : 0 ≤ n.val) (hnm : n.val ≤ m.val)
        (hm : m.val ≤ 37), ∀ rn rm : Std.I64,
          Aegis.Tribonacci.tribonacci n = ok rn →
          Aegis.Tribonacci.tribonacci m = ok rm →
          rn.val ≤ rm.val) := by
    sorry

  /-- Let rn = tribonacci(n) and rm = tribonacci(m). If both calls return results, then rn < rm.
    Preconditions: 2 <= n < m <= 37. -/
  theorem spec_5 (n m : Std.I64) (hn : 2 ≤ n.val) (hnm : n.val < m.val)
      (hm : m.val ≤ 37) :
      ∀ rn rm : Std.I64,
        Aegis.Tribonacci.tribonacci n = ok rn →
        Aegis.Tribonacci.tribonacci m = ok rm →
        rn.val < rm.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n m : Std.I64) (hn : 2 ≤ n.val) (hnm : n.val < m.val)
        (hm : m.val ≤ 37), ∀ rn rm : Std.I64,
          Aegis.Tribonacci.tribonacci n = ok rn →
          Aegis.Tribonacci.tribonacci m = ok rm →
          rn.val < rm.val) := by
    sorry

  /-- Let r = tribonacci(n). If the call returns a result, then r = 0 if and only if n = 0.
    Preconditions: 0 <= n <= 37. -/
  theorem spec_6 (n : Std.I64) (hlo : 0 ≤ n.val) (hhi : n.val ≤ 37) :
      ∀ r : Std.I64, Aegis.Tribonacci.tribonacci n = ok r → (r.val = 0 ↔ n.val = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hlo : 0 ≤ n.val) (hhi : n.val ≤ 37), ∀ r : Std.I64, Aegis.Tribonacci.tribonacci n = ok r → (r.val = 0 ↔ n.val = 0)) := by
    sorry

  /-- Whenever the function returns a result r, r >= 1.
    Preconditions: 1 <= n <= 37. -/
  theorem spec_7 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 37) :
      ∀ r : Std.I64, Aegis.Tribonacci.tribonacci n = ok r → 1 ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 37), ∀ r : Std.I64, Aegis.Tribonacci.tribonacci n = ok r → 1 ≤ r.val) := by
    sorry

  /-- Let r = tribonacci(n). If the call returns a result r, then there exists a finite sequence (a_i)_{i=0}^{n} of integers such that: (i) a_0=0; (ii) a_1=1 if n >= 1; (iii) a_2=1 if n >= 2; (iv) a_{i+3}=a_i+a_{i+1}+a_{i+2} for every integer i with 0 <= i and i+3 <= n; and (v) a_n = r.
    Preconditions: 0 <= n <= 37, where n is the integer value of the input. -/
  theorem spec_8 (n : Std.I64) (hlo : 0 ≤ n.val) (hhi : n.val ≤ 37) :
      ∀ r : Std.I64,
        Aegis.Tribonacci.tribonacci n = ok r →
        ∃ a : ℕ → ℤ, TribPrefix a n.val.toNat ∧ a n.val.toNat = r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hlo : 0 ≤ n.val) (hhi : n.val ≤ 37), ∀ r : Std.I64,
          Aegis.Tribonacci.tribonacci n = ok r →
          ∃ a : ℕ → ℤ, TribPrefix a n.val.toNat ∧ a n.val.toNat = r.val) := by
    sorry

  end AegisSpec.Tribonacci
