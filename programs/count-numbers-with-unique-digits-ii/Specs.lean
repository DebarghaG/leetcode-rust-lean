import Aegis.NumberCount.Code.Funs

/-!
# Specifications of `Aegis.NumberCount.number_count`

LeetCode problem `count-numbers-with-unique-digits-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberCount

def decDigitsFrom : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else decDigitsFrom fuel (n / 10) ++ [n % 10]

def decDigits (n : Nat) : List Nat := decDigitsFrom n n

def HasUniqueDigits (n : Int) : Prop := 0 < n ∧ (decDigits n.toNat).Nodup

def countIccAux (p : Int → Prop) [DecidablePred p] : Nat → Int → Int → Nat
  | 0, _, _ => 0
  | fuel + 1, lo, hi =>
    if lo ≤ hi then
      (if p lo then 1 else 0) + countIccAux p fuel (lo + 1) hi
    else 0

noncomputable def countIcc (p : Int → Prop) (lo hi : Int) : Nat :=
  @countIccAux p (Classical.decPred p) (hi - lo + 1).toNat lo hi

noncomputable def uniqueCount (a b : Int) : Nat := countIcc HasUniqueDigits a b

noncomputable def nonUniqueCount (a b : Int) : Nat :=
  countIcc (fun n => ¬ HasUniqueDigits n) a b

/-- Let U(n) mean that n is positive and that in the standard decimal representation of n without leading zeros, no digit occurs in two different positions. The function returns a result r and r is the number of integers n such that a <= n <= b and U(n).
  Preconditions: a and b are machine integers satisfying 1 <= a <= b <= 1000. -/
theorem spec_1 (a b : Std.I64)
    (ha : 1 ≤ a.val) (hab : a.val ≤ b.val) (hb : b.val ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.NumberCount.number_count a b = Result.ok r ∧
        r.val = (uniqueCount a.val b.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (a b : Std.I64)
    (ha : 1 ≤ a.val) (hab : a.val ≤ b.val) (hb : b.val ≤ 1000), ∃ r : Std.I64,
      Aegis.NumberCount.number_count a b = Result.ok r ∧
        r.val = (uniqueCount a.val b.val : Int)) := by
  sorry

/-- The function returns a result r for every input satisfying the precondition; it does not fail.
  Preconditions: a and b are machine integers satisfying 1 <= a <= b <= 1000. -/
theorem spec_2 (a b : Std.I64)
    (ha : 1 ≤ a.val) (hab : a.val ≤ b.val) (hb : b.val ≤ 1000) :
    ∃ r : Std.I64, Aegis.NumberCount.number_count a b = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (a b : Std.I64)
    (ha : 1 ≤ a.val) (hab : a.val ≤ b.val) (hb : b.val ≤ 1000), ∃ r : Std.I64, Aegis.NumberCount.number_count a b = Result.ok r) := by
  sorry

/-- The function returns a result r and r >= 0.
  Preconditions: a and b are machine integers satisfying 1 <= a <= b <= 1000. -/
theorem spec_3 (a b : Std.I64)
    (ha : 1 ≤ a.val) (hab : a.val ≤ b.val) (hb : b.val ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.NumberCount.number_count a b = Result.ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (a b : Std.I64)
    (ha : 1 ≤ a.val) (hab : a.val ≤ b.val) (hb : b.val ≤ 1000), ∃ r : Std.I64,
      Aegis.NumberCount.number_count a b = Result.ok r ∧ 0 ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= b - a + 1, where b - a + 1 is evaluated as an ordinary mathematical integer.
  Preconditions: a and b are machine integers satisfying 1 <= a <= b <= 1000. -/
theorem spec_4 (a b : Std.I64)
    (ha : 1 ≤ a.val) (hab : a.val ≤ b.val) (hb : b.val ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.NumberCount.number_count a b = Result.ok r ∧
        r.val ≤ b.val - a.val + 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (a b : Std.I64)
    (ha : 1 ≤ a.val) (hab : a.val ≤ b.val) (hb : b.val ≤ 1000), ∃ r : Std.I64,
      Aegis.NumberCount.number_count a b = Result.ok r ∧
        r.val ≤ b.val - a.val + 1) := by
  sorry

/-- Let r_ac be the result of number_count(a, c), r_ab the result of number_count(a, b), and r_bc the result of number_count(b + 1, c). The function returns these three results and r_ac = r_ab + r_bc.
  Preconditions: a, b, and c are machine integers satisfying 1 <= a <= b < c <= 1000. -/
theorem spec_5 (a b c : Std.I64)
    (ha : 1 ≤ a.val) (hab : a.val ≤ b.val) (hbc : b.val < c.val) (hc : c.val ≤ 1000) :
    ∃ r_ac r_ab r_bc : Std.I64,
      Aegis.NumberCount.number_count a c = Result.ok r_ac ∧
        Aegis.NumberCount.number_count a b = Result.ok r_ab ∧
          Aegis.NumberCount.number_count
              (Std.I64.ofInt (b.val + 1) (by
                have hmin : Aeneas.Std.IScalar.cMin Aeneas.Std.IScalarTy.I64 ≤ (0 : ℤ) := by
                  decide
                have hmax : (1000 : ℤ) ≤ Aeneas.Std.IScalar.cMax Aeneas.Std.IScalarTy.I64 := by
                  decide
                omega)) c = Result.ok r_bc ∧
            r_ac.val = r_ab.val + r_bc.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (a b c : Std.I64)
    (ha : 1 ≤ a.val) (hab : a.val ≤ b.val) (hbc : b.val < c.val) (hc : c.val ≤ 1000), ∃ r_ac r_ab r_bc : Std.I64,
      Aegis.NumberCount.number_count a c = Result.ok r_ac ∧
        Aegis.NumberCount.number_count a b = Result.ok r_ab ∧
          Aegis.NumberCount.number_count
              (Std.I64.ofInt (b.val + 1) (by
                have hmin : Aeneas.Std.IScalar.cMin Aeneas.Std.IScalarTy.I64 ≤ (0 : ℤ) := by
                  decide
                have hmax : (1000 : ℤ) ≤ Aeneas.Std.IScalar.cMax Aeneas.Std.IScalarTy.I64 := by
                  decide
                omega)) c = Result.ok r_bc ∧
            r_ac.val = r_ab.val + r_bc.val) := by
  sorry

/-- Let U(n) mean that n is positive and that in the standard decimal representation of n without leading zeros, no digit occurs in two different positions. The function returns a result r, and r > 0 if and only if there exists an integer n with a <= n <= b and U(n).
  Preconditions: a and b are machine integers satisfying 1 <= a <= b <= 1000. -/
theorem spec_6 (a b : Std.I64)
    (ha : 1 ≤ a.val) (hab : a.val ≤ b.val) (hb : b.val ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.NumberCount.number_count a b = Result.ok r ∧
        (0 < r.val ↔ ∃ n : Int, a.val ≤ n ∧ n ≤ b.val ∧ HasUniqueDigits n) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (a b : Std.I64)
    (ha : 1 ≤ a.val) (hab : a.val ≤ b.val) (hb : b.val ≤ 1000), ∃ r : Std.I64,
      Aegis.NumberCount.number_count a b = Result.ok r ∧
        (0 < r.val ↔ ∃ n : Int, a.val ≤ n ∧ n ≤ b.val ∧ HasUniqueDigits n)) := by
  sorry

/-- Let r1 be the result of number_count(a, b1) and r2 the result of number_count(a, b2). The function returns these two results and r1 <= r2.
  Preconditions: a, b1, and b2 are machine integers satisfying 1 <= a <= b1 <= b2 <= 1000. -/
theorem spec_7 (a b1 b2 : Std.I64)
    (ha : 1 ≤ a.val) (hab : a.val ≤ b1.val) (hb : b1.val ≤ b2.val) (hb2 : b2.val ≤ 1000) :
    ∃ r1 r2 : Std.I64,
      Aegis.NumberCount.number_count a b1 = Result.ok r1 ∧
        Aegis.NumberCount.number_count a b2 = Result.ok r2 ∧
          r1.val ≤ r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (a b1 b2 : Std.I64)
    (ha : 1 ≤ a.val) (hab : a.val ≤ b1.val) (hb : b1.val ≤ b2.val) (hb2 : b2.val ≤ 1000), ∃ r1 r2 : Std.I64,
      Aegis.NumberCount.number_count a b1 = Result.ok r1 ∧
        Aegis.NumberCount.number_count a b2 = Result.ok r2 ∧
          r1.val ≤ r2.val) := by
  sorry

/-- Let r1 be the result of number_count(a1, b) and r2 the result of number_count(a2, b). The function returns these two results and r2 <= r1.
  Preconditions: a1, a2, and b are machine integers satisfying 1 <= a1 <= a2 <= b <= 1000. -/
theorem spec_8 (a1 a2 b : Std.I64)
    (ha : 1 ≤ a1.val) (ha12 : a1.val ≤ a2.val) (hb : a2.val ≤ b.val) (hb2 : b.val ≤ 1000) :
    ∃ r1 r2 : Std.I64,
      Aegis.NumberCount.number_count a1 b = Result.ok r1 ∧
        Aegis.NumberCount.number_count a2 b = Result.ok r2 ∧
          r2.val ≤ r1.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (a1 a2 b : Std.I64)
    (ha : 1 ≤ a1.val) (ha12 : a1.val ≤ a2.val) (hb : a2.val ≤ b.val) (hb2 : b.val ≤ 1000), ∃ r1 r2 : Std.I64,
      Aegis.NumberCount.number_count a1 b = Result.ok r1 ∧
        Aegis.NumberCount.number_count a2 b = Result.ok r2 ∧
          r2.val ≤ r1.val) := by
  sorry

/-- Let U(n) mean that n is positive and that in the standard decimal representation of n without leading zeros, no digit occurs in two different positions. The function returns a result r, and (b - a + 1) - r is the number of integers n such that a <= n <= b and not U(n).
  Preconditions: a and b are machine integers satisfying 1 <= a <= b <= 1000. -/
theorem spec_9 (a b : Std.I64)
    (ha : 1 ≤ a.val) (hab : a.val ≤ b.val) (hb : b.val ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.NumberCount.number_count a b = Result.ok r ∧
        (b.val - a.val + 1) - r.val = (nonUniqueCount a.val b.val : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (a b : Std.I64)
    (ha : 1 ≤ a.val) (hab : a.val ≤ b.val) (hb : b.val ≤ 1000), ∃ r : Std.I64,
      Aegis.NumberCount.number_count a b = Result.ok r ∧
        (b.val - a.val + 1) - r.val = (nonUniqueCount a.val b.val : Int)) := by
  sorry

end AegisSpec.NumberCount
