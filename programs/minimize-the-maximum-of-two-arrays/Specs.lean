import Aegis.MinimizeSet.Code.Funs

/-!
# Specifications of `Aegis.MinimizeSet.minimize_set`

LeetCode problem `minimize-the-maximum-of-two-arrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aeneas.Std.Result

namespace AegisSpec.MinimizeSet

def Feasible (d1 d2 c1 c2 M : ℤ) : Prop :=
  ∃ A B : Finset ℤ,
    (∀ a ∈ A, 0 < a) ∧
    (∀ b ∈ B, 0 < b) ∧
    (A.card : ℤ) = c1 ∧
    (B.card : ℤ) = c2 ∧
    (∀ a ∈ A, ¬ d1 ∣ a) ∧
    (∀ b ∈ B, ¬ d2 ∣ b) ∧
    Disjoint A B ∧
    (∀ x ∈ A ∪ B, x ≤ M)

def IsLeastFeasible (d1 d2 c1 c2 r : ℤ) : Prop :=
  0 < r ∧ Feasible d1 d2 c1 c2 r ∧
    ∀ M : ℤ, 0 < M → Feasible d1 d2 c1 c2 M → r ≤ M

def FeasibleWitness (d1 d2 c1 c2 M : ℤ) : Prop :=
  ∃ A B : Finset ℤ,
    (∀ a ∈ A, 0 < a) ∧
    (∀ b ∈ B, 0 < b) ∧
    (A.card : ℤ) = c1 ∧
    (B.card : ℤ) = c2 ∧
    (∀ a ∈ A, ¬ d1 ∣ a) ∧
    (∀ b ∈ B, ¬ d2 ∣ b) ∧
    Disjoint A B ∧
    (∀ x ∈ A ∪ B, x ≤ M) ∧
    M ∈ A ∪ B

def IsLcm (a b L : ℤ) : Prop :=
  0 < L ∧ a ∣ L ∧ b ∣ L ∧ ∀ k : ℤ, 0 < k → a ∣ k → b ∣ k → L ≤ k

def IsLeastSingle (d c1 c2 r : ℤ) : Prop :=
  0 < r ∧ r - r / d ≥ c1 + c2 ∧
    ∀ M : ℤ, 0 < M → M - M / d ≥ c1 + c2 → r ≤ M

def CountingConditions (d1 d2 L c1 c2 M : ℤ) : Prop :=
  M - M / d1 ≥ c1 ∧ M - M / d2 ≥ c2 ∧ M - M / L ≥ c1 + c2

def IsLeastCounting (d1 d2 L c1 c2 r : ℤ) : Prop :=
  0 < r ∧ CountingConditions d1 d2 L c1 c2 r ∧
    ∀ M : ℤ, 0 < M → CountingConditions d1 d2 L c1 c2 M → r ≤ M

/-- Whenever minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2 returns a result r, r is the least positive integer M for which there exist finite sets A and B of positive integers such that |A| = unique_cnt1, |B| = unique_cnt2, every a in A is not divisible by divisor1, every b in B is not divisible by divisor2, A and B are disjoint, and every x in A union B satisfies x <= M.
  Preconditions: 2 <= divisor1 <= 100000; 2 <= divisor2 <= 100000; 1 <= unique_cnt1 < 1000000000; 1 <= unique_cnt2 < 1000000000; 2 <= unique_cnt1 + unique_cnt2 <= 1000000000. -/
theorem spec_1
    (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000) :
    ∀ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      IsLeastFeasible divisor1.val divisor2.val unique_cnt1.val unique_cnt2.val r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000), ∀ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      IsLeastFeasible divisor1.val divisor2.val unique_cnt1.val unique_cnt2.val r.val) := by
  sorry

/-- The function returns a result r, namely an Ok value; under these preconditions it does not fail, overflow, panic, or go out of bounds.
  Preconditions: 2 <= divisor1 <= 100000; 2 <= divisor2 <= 100000; 1 <= unique_cnt1 < 1000000000; 1 <= unique_cnt2 < 1000000000; 2 <= unique_cnt1 + unique_cnt2 <= 1000000000. -/
theorem spec_2
    (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000) :
    ∃ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000), ∃ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= unique_cnt1 + unique_cnt2.
  Preconditions: 2 <= divisor1 <= 100000; 2 <= divisor2 <= 100000; 1 <= unique_cnt1 < 1000000000; 1 <= unique_cnt2 < 1000000000; 2 <= unique_cnt1 + unique_cnt2 <= 1000000000. -/
theorem spec_3
    (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000) :
    ∀ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      r.val ≥ unique_cnt1.val + unique_cnt2.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000), ∀ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      r.val ≥ unique_cnt1.val + unique_cnt2.val) := by
  sorry

/-- Whenever the function returns a result r, r - floor(r / divisor1) >= unique_cnt1, where floor denotes mathematical floor division.
  Preconditions: 2 <= divisor1 <= 100000; 2 <= divisor2 <= 100000; 1 <= unique_cnt1 < 1000000000; 1 <= unique_cnt2 < 1000000000; 2 <= unique_cnt1 + unique_cnt2 <= 1000000000. -/
theorem spec_4
    (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000) :
    ∀ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      r.val - r.val / divisor1.val ≥ unique_cnt1.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000), ∀ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      r.val - r.val / divisor1.val ≥ unique_cnt1.val) := by
  sorry

/-- Whenever the function returns a result r, r - floor(r / divisor2) >= unique_cnt2, where floor denotes mathematical floor division.
  Preconditions: 2 <= divisor1 <= 100000; 2 <= divisor2 <= 100000; 1 <= unique_cnt1 < 1000000000; 1 <= unique_cnt2 < 1000000000; 2 <= unique_cnt1 + unique_cnt2 <= 1000000000. -/
theorem spec_5
    (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000) :
    ∀ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      r.val - r.val / divisor2.val ≥ unique_cnt2.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000), ∀ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      r.val - r.val / divisor2.val ≥ unique_cnt2.val) := by
  sorry

/-- Let L be the least positive integer divisible by both divisor1 and divisor2. Whenever the function returns a result r, r - floor(r / L) >= unique_cnt1 + unique_cnt2.
  Preconditions: 2 <= divisor1 <= 100000; 2 <= divisor2 <= 100000; 1 <= unique_cnt1 < 1000000000; 1 <= unique_cnt2 < 1000000000; 2 <= unique_cnt1 + unique_cnt2 <= 1000000000. -/
theorem spec_6
    (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000) :
    ∀ L : ℤ, IsLcm divisor1.val divisor2.val L →
    ∀ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      r.val - r.val / L ≥ unique_cnt1.val + unique_cnt2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000), ∀ L : ℤ, IsLcm divisor1.val divisor2.val L →
    ∀ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      r.val - r.val / L ≥ unique_cnt1.val + unique_cnt2.val) := by
  sorry

/-- Whenever the function returns a result r, there exist finite sets A and B of positive integers such that |A| = unique_cnt1, |B| = unique_cnt2, every a in A is not divisible by divisor1, every b in B is not divisible by divisor2, A and B are disjoint, every x in A union B satisfies x <= r, and at least one x in A union B equals r.
  Preconditions: 2 <= divisor1 <= 100000; 2 <= divisor2 <= 100000; 1 <= unique_cnt1 < 1000000000; 1 <= unique_cnt2 < 1000000000; 2 <= unique_cnt1 + unique_cnt2 <= 1000000000. -/
theorem spec_7
    (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000) :
    ∀ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      FeasibleWitness divisor1.val divisor2.val unique_cnt1.val unique_cnt2.val r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000), ∀ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      FeasibleWitness divisor1.val divisor2.val unique_cnt1.val unique_cnt2.val r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= 2 * (unique_cnt1 + unique_cnt2).
  Preconditions: 2 <= divisor1 <= 100000; 2 <= divisor2 <= 100000; 1 <= unique_cnt1 < 1000000000; 1 <= unique_cnt2 < 1000000000; 2 <= unique_cnt1 + unique_cnt2 <= 1000000000. -/
theorem spec_8
    (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000) :
    ∀ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      r.val ≤ 2 * (unique_cnt1.val + unique_cnt2.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000), ∀ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      r.val ≤ 2 * (unique_cnt1.val + unique_cnt2.val)) := by
  sorry

/-- Let L be the least positive integer divisible by both divisor1 and divisor2. Whenever the function returns a result r, L does not divide r.
  Preconditions: 2 <= divisor1 <= 100000; 2 <= divisor2 <= 100000; 1 <= unique_cnt1 < 1000000000; 1 <= unique_cnt2 < 1000000000; 2 <= unique_cnt1 + unique_cnt2 <= 1000000000. -/
theorem spec_9
    (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000) :
    ∀ L : ℤ, IsLcm divisor1.val divisor2.val L →
    ∀ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      ¬ L ∣ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000), ∀ L : ℤ, IsLcm divisor1.val divisor2.val L →
    ∀ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      ¬ L ∣ r.val) := by
  sorry

/-- Whenever minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2 returns r and minimize_set divisor2 divisor1 unique_cnt2 unique_cnt1 returns r', we have r = r'.
  Preconditions: 2 <= divisor1 <= 100000; 2 <= divisor2 <= 100000; 1 <= unique_cnt1 < 1000000000; 1 <= unique_cnt2 < 1000000000; 2 <= unique_cnt1 + unique_cnt2 <= 1000000000. -/
theorem spec_10
    (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000) :
    ∀ r r' : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      Aegis.MinimizeSet.minimize_set divisor2 divisor1 unique_cnt2 unique_cnt1
        = Aeneas.Std.Result.ok r' →
      r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000), ∀ r r' : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      Aegis.MinimizeSet.minimize_set divisor2 divisor1 unique_cnt2 unique_cnt1
        = Aeneas.Std.Result.ok r' →
      r = r') := by
  sorry

/-- If unique_cnt1 <= c1' and unique_cnt2 <= c2', and minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2 returns r while minimize_set divisor1 divisor2 c1' c2' returns r', then r <= r'.
  Preconditions: 2 <= divisor1 <= 100000; 2 <= divisor2 <= 100000; 1 <= unique_cnt1 < 1000000000; 1 <= unique_cnt2 < 1000000000; 2 <= unique_cnt1 + unique_cnt2 <= 1000000000; and for the comparison inputs c1' and c2' used in the statement, 1 <= c1' < 1000000000, 1 <= c2' < 1000000000, 2 <= c1' + c2' <= 1000000000. -/
theorem spec_11
    (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000)
    (c1' c2' : Aeneas.Std.I64)
    (hc1' : 1 ≤ c1'.val ∧ c1'.val < 1000000000)
    (hc2' : 1 ≤ c2'.val ∧ c2'.val < 1000000000)
    (hsum' : 2 ≤ c1'.val + c2'.val ∧ c1'.val + c2'.val ≤ 1000000000)
    (hle1 : unique_cnt1.val ≤ c1'.val)
    (hle2 : unique_cnt2.val ≤ c2'.val) :
    ∀ r r' : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 c1' c2'
        = Aeneas.Std.Result.ok r' →
      r.val ≤ r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000)
    (c1' c2' : Aeneas.Std.I64)
    (hc1' : 1 ≤ c1'.val ∧ c1'.val < 1000000000)
    (hc2' : 1 ≤ c2'.val ∧ c2'.val < 1000000000)
    (hsum' : 2 ≤ c1'.val + c2'.val ∧ c1'.val + c2'.val ≤ 1000000000)
    (hle1 : unique_cnt1.val ≤ c1'.val)
    (hle2 : unique_cnt2.val ≤ c2'.val), ∀ r r' : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 c1' c2'
        = Aeneas.Std.Result.ok r' →
      r.val ≤ r'.val) := by
  sorry

/-- Whenever minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2 returns r and minimize_set divisor1' divisor2 unique_cnt1 unique_cnt2 returns r', we have r' <= r.
  Preconditions: 2 <= divisor1 <= 100000; 2 <= divisor1' <= 100000; divisor1 divides divisor1'; 2 <= divisor2 <= 100000; 1 <= unique_cnt1 < 1000000000; 1 <= unique_cnt2 < 1000000000; 2 <= unique_cnt1 + unique_cnt2 <= 1000000000. -/
theorem spec_12
    (divisor1 divisor1' divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd1' : 2 ≤ divisor1'.val ∧ divisor1'.val ≤ 100000)
    (hdiv : divisor1.val ∣ divisor1'.val)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000) :
    ∀ r r' : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      Aegis.MinimizeSet.minimize_set divisor1' divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r' →
      r'.val ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (divisor1 divisor1' divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd1' : 2 ≤ divisor1'.val ∧ divisor1'.val ≤ 100000)
    (hdiv : divisor1.val ∣ divisor1'.val)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000), ∀ r r' : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      Aegis.MinimizeSet.minimize_set divisor1' divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r' →
      r'.val ≤ r.val) := by
  sorry

/-- Whenever divisor1 = divisor2 = d and the function returns a result r, r is the least positive integer M such that M - floor(M / d) >= unique_cnt1 + unique_cnt2.
  Preconditions: 2 <= divisor1 <= 100000; 2 <= divisor2 <= 100000; 1 <= unique_cnt1 < 1000000000; 1 <= unique_cnt2 < 1000000000; 2 <= unique_cnt1 + unique_cnt2 <= 1000000000; divisor1 = divisor2 = d. -/
theorem spec_13
    (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000) :
    ∀ d : ℤ, divisor1.val = d → divisor2.val = d →
    ∀ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      IsLeastSingle d unique_cnt1.val unique_cnt2.val r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000), ∀ d : ℤ, divisor1.val = d → divisor2.val = d →
    ∀ r : Aeneas.Std.I64,
      Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
        = Aeneas.Std.Result.ok r →
      IsLeastSingle d unique_cnt1.val unique_cnt2.val r.val) := by
  sorry

/-- Let L be the least positive integer divisible by both divisor1 and divisor2. For every positive integer M, there exist finite sets A and B of positive integers with |A| = unique_cnt1, |B| = unique_cnt2, every a in A not divisible by divisor1, every b in B not divisible by divisor2, A and B disjoint, and every x in A union B satisfying x <= M if and only if M - floor(M / divisor1) >= unique_cnt1, M - floor(M / divisor2) >= unique_cnt2, and M - floor(M / L) >= unique_cnt1 + unique_cnt2. Consequently, whenever minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2 returns r, r is the least positive integer satisfying these three counting inequalities.
  Preconditions: 2 <= divisor1 <= 100000; 2 <= divisor2 <= 100000; 1 <= unique_cnt1 < 1000000000; 1 <= unique_cnt2 < 1000000000; 2 <= unique_cnt1 + unique_cnt2 <= 1000000000. -/
theorem spec_14
    (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000) :
    (∀ L : ℤ, IsLcm divisor1.val divisor2.val L →
      ∀ M : ℤ, 0 < M →
        (Feasible divisor1.val divisor2.val unique_cnt1.val unique_cnt2.val M ↔
          CountingConditions divisor1.val divisor2.val L unique_cnt1.val unique_cnt2.val M)) ∧
    (∀ L : ℤ, IsLcm divisor1.val divisor2.val L →
      ∀ r : Aeneas.Std.I64,
        Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
          = Aeneas.Std.Result.ok r →
        IsLeastCounting divisor1.val divisor2.val L unique_cnt1.val unique_cnt2.val r.val) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (divisor1 divisor2 unique_cnt1 unique_cnt2 : Aeneas.Std.I64)
    (hd1 : 2 ≤ divisor1.val ∧ divisor1.val ≤ 100000)
    (hd2 : 2 ≤ divisor2.val ∧ divisor2.val ≤ 100000)
    (hc1 : 1 ≤ unique_cnt1.val ∧ unique_cnt1.val < 1000000000)
    (hc2 : 1 ≤ unique_cnt2.val ∧ unique_cnt2.val < 1000000000)
    (hsum : 2 ≤ unique_cnt1.val + unique_cnt2.val ∧
      unique_cnt1.val + unique_cnt2.val ≤ 1000000000), (∀ L : ℤ, IsLcm divisor1.val divisor2.val L →
      ∀ M : ℤ, 0 < M →
        (Feasible divisor1.val divisor2.val unique_cnt1.val unique_cnt2.val M ↔
          CountingConditions divisor1.val divisor2.val L unique_cnt1.val unique_cnt2.val M)) ∧
    (∀ L : ℤ, IsLcm divisor1.val divisor2.val L →
      ∀ r : Aeneas.Std.I64,
        Aegis.MinimizeSet.minimize_set divisor1 divisor2 unique_cnt1 unique_cnt2
          = Aeneas.Std.Result.ok r →
        IsLeastCounting divisor1.val divisor2.val L unique_cnt1.val unique_cnt2.val r.val)) := by
  sorry

end AegisSpec.MinimizeSet
