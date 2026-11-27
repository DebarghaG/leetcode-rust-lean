import Aegis.PoorPigs.Code.Funs

/-!
# Specifications of `Aegis.PoorPigs.poor_pigs`

LeetCode problem `poor-pigs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.PoorPigs

def q (minutesToDie minutesToTest : I64) : ℤ :=
  minutesToTest.val / minutesToDie.val

def base (minutesToDie minutesToTest : I64) : ℤ :=
  q minutesToDie minutesToTest + 1

def IsLeastPigs (buckets base r : ℤ) : Prop :=
  base ^ r.toNat ≥ buckets ∧ (r = 0 ∨ base ^ (r - 1).toNat < buckets)

/-- Let q = minutesToTest / minutesToDie (integer division) and let base = q + 1. The function returns a result r (so it does not fail), and r is the least nonnegative integer such that base^r >= buckets; equivalently, base^r >= buckets, and either r = 0 or base^(r-1) < buckets. Here exponentiation is ordinary integer exponentiation, not machine wrap-around.
  Preconditions: 1 <= buckets <= 1000 and 1 <= minutesToDie <= minutesToTest <= 100. -/
theorem spec_1 (buckets minutesToDie minutesToTest : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val)
    (hdie_test : minutesToDie.val ≤ minutesToTest.val)
    (htest_ub : minutesToTest.val ≤ 100) :
    ∃ r : I64,
      Aegis.PoorPigs.poor_pigs buckets minutesToDie minutesToTest = ok r ∧
        IsLeastPigs buckets.val (base minutesToDie minutesToTest) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (buckets minutesToDie minutesToTest : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val)
    (hdie_test : minutesToDie.val ≤ minutesToTest.val)
    (htest_ub : minutesToTest.val ≤ 100), ∃ r : I64,
      Aegis.PoorPigs.poor_pigs buckets minutesToDie minutesToTest = ok r ∧
        IsLeastPigs buckets.val (base minutesToDie minutesToTest) r.val) := by
  sorry

/-- The function returns a result r; it does not fail, overflow, panic, or go out of bounds.
  Preconditions: 1 <= buckets <= 1000 and 1 <= minutesToDie <= minutesToTest <= 100. -/
theorem spec_2 (buckets minutesToDie minutesToTest : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val)
    (hdie_test : minutesToDie.val ≤ minutesToTest.val)
    (htest_ub : minutesToTest.val ≤ 100) :
    ∃ r : I64, Aegis.PoorPigs.poor_pigs buckets minutesToDie minutesToTest = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (buckets minutesToDie minutesToTest : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val)
    (hdie_test : minutesToDie.val ≤ minutesToTest.val)
    (htest_ub : minutesToTest.val ≤ 100), ∃ r : I64, Aegis.PoorPigs.poor_pigs buckets minutesToDie minutesToTest = ok r) := by
  sorry

/-- The function returns a result r and r <= buckets - 1.
  Preconditions: 1 <= buckets <= 1000 and 1 <= minutesToDie <= minutesToTest <= 100. -/
theorem spec_3 (buckets minutesToDie minutesToTest : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val)
    (hdie_test : minutesToDie.val ≤ minutesToTest.val)
    (htest_ub : minutesToTest.val ≤ 100) :
    ∃ r : I64,
      Aegis.PoorPigs.poor_pigs buckets minutesToDie minutesToTest = ok r ∧
        r.val ≤ buckets.val - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (buckets minutesToDie minutesToTest : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val)
    (hdie_test : minutesToDie.val ≤ minutesToTest.val)
    (htest_ub : minutesToTest.val ≤ 100), ∃ r : I64,
      Aegis.PoorPigs.poor_pigs buckets minutesToDie minutesToTest = ok r ∧
        r.val ≤ buckets.val - 1) := by
  sorry

/-- The function returns a result r and r <= 10.
  Preconditions: 1 <= buckets <= 1000 and 1 <= minutesToDie <= minutesToTest <= 100. -/
theorem spec_4 (buckets minutesToDie minutesToTest : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val)
    (hdie_test : minutesToDie.val ≤ minutesToTest.val)
    (htest_ub : minutesToTest.val ≤ 100) :
    ∃ r : I64,
      Aegis.PoorPigs.poor_pigs buckets minutesToDie minutesToTest = ok r ∧
        r.val ≤ 10 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (buckets minutesToDie minutesToTest : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val)
    (hdie_test : minutesToDie.val ≤ minutesToTest.val)
    (htest_ub : minutesToTest.val ≤ 100), ∃ r : I64,
      Aegis.PoorPigs.poor_pigs buckets minutesToDie minutesToTest = ok r ∧
        r.val ≤ 10) := by
  sorry

/-- The function returns a result r and r = 0 if and only if buckets = 1.
  Preconditions: 1 <= buckets <= 1000 and 1 <= minutesToDie <= minutesToTest <= 100. -/
theorem spec_5 (buckets minutesToDie minutesToTest : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val)
    (hdie_test : minutesToDie.val ≤ minutesToTest.val)
    (htest_ub : minutesToTest.val ≤ 100) :
    ∃ r : I64,
      Aegis.PoorPigs.poor_pigs buckets minutesToDie minutesToTest = ok r ∧
        (r.val = 0 ↔ buckets.val = 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (buckets minutesToDie minutesToTest : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val)
    (hdie_test : minutesToDie.val ≤ minutesToTest.val)
    (htest_ub : minutesToTest.val ≤ 100), ∃ r : I64,
      Aegis.PoorPigs.poor_pigs buckets minutesToDie minutesToTest = ok r ∧
        (r.val = 0 ↔ buckets.val = 1)) := by
  sorry

/-- Let q = minutesToTest / minutesToDie and base = q + 1. The function returns a result r and r = 1 if and only if 2 <= buckets <= base.
  Preconditions: 1 <= buckets <= 1000 and 1 <= minutesToDie <= minutesToTest <= 100. -/
theorem spec_6 (buckets minutesToDie minutesToTest : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val)
    (hdie_test : minutesToDie.val ≤ minutesToTest.val)
    (htest_ub : minutesToTest.val ≤ 100) :
    ∃ r : I64,
      Aegis.PoorPigs.poor_pigs buckets minutesToDie minutesToTest = ok r ∧
        (r.val = 1 ↔ 2 ≤ buckets.val ∧ buckets.val ≤ base minutesToDie minutesToTest) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (buckets minutesToDie minutesToTest : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val)
    (hdie_test : minutesToDie.val ≤ minutesToTest.val)
    (htest_ub : minutesToTest.val ≤ 100), ∃ r : I64,
      Aegis.PoorPigs.poor_pigs buckets minutesToDie minutesToTest = ok r ∧
        (r.val = 1 ↔ 2 ≤ buckets.val ∧ buckets.val ≤ base minutesToDie minutesToTest)) := by
  sorry

/-- Let q = minutesToTest / minutesToDie and base = q + 1. The function returns a result r and, if r > 0, then base^(r-1) < buckets.
  Preconditions: 1 <= buckets <= 1000 and 1 <= minutesToDie <= minutesToTest <= 100. -/
theorem spec_7 (buckets minutesToDie minutesToTest : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val)
    (hdie_test : minutesToDie.val ≤ minutesToTest.val)
    (htest_ub : minutesToTest.val ≤ 100) :
    ∃ r : I64,
      Aegis.PoorPigs.poor_pigs buckets minutesToDie minutesToTest = ok r ∧
        (r.val > 0 → base minutesToDie minutesToTest ^ (r.val - 1).toNat < buckets.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (buckets minutesToDie minutesToTest : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val)
    (hdie_test : minutesToDie.val ≤ minutesToTest.val)
    (htest_ub : minutesToTest.val ≤ 100), ∃ r : I64,
      Aegis.PoorPigs.poor_pigs buckets minutesToDie minutesToTest = ok r ∧
        (r.val > 0 → base minutesToDie minutesToTest ^ (r.val - 1).toNat < buckets.val)) := by
  sorry

/-- Let q = minutesToTest / minutesToDie and base = q + 1. The function returns a result r and base^r >= buckets.
  Preconditions: 1 <= buckets <= 1000 and 1 <= minutesToDie <= minutesToTest <= 100. -/
theorem spec_8 (buckets minutesToDie minutesToTest : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val)
    (hdie_test : minutesToDie.val ≤ minutesToTest.val)
    (htest_ub : minutesToTest.val ≤ 100) :
    ∃ r : I64,
      Aegis.PoorPigs.poor_pigs buckets minutesToDie minutesToTest = ok r ∧
        base minutesToDie minutesToTest ^ r.val.toNat ≥ buckets.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (buckets minutesToDie minutesToTest : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val)
    (hdie_test : minutesToDie.val ≤ minutesToTest.val)
    (htest_ub : minutesToTest.val ≤ 100), ∃ r : I64,
      Aegis.PoorPigs.poor_pigs buckets minutesToDie minutesToTest = ok r ∧
        base minutesToDie minutesToTest ^ r.val.toNat ≥ buckets.val) := by
  sorry

/-- If the function returns r1 on (buckets1, minutesToDie, minutesToTest) and r2 on (buckets2, minutesToDie, minutesToTest), then r1 <= r2.
  Preconditions: For two inputs (buckets1, minutesToDie, minutesToTest) and (buckets2, minutesToDie, minutesToTest), assume 1 <= buckets1 <= buckets2 <= 1000 and 1 <= minutesToDie <= minutesToTest <= 100. -/
theorem spec_9 (buckets1 buckets2 minutesToDie minutesToTest : I64) (r1 r2 : I64)
    (hbuckets1_lb : 1 ≤ buckets1.val) (hbuckets12 : buckets1.val ≤ buckets2.val)
    (hbuckets2_ub : buckets2.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val)
    (hdie_test : minutesToDie.val ≤ minutesToTest.val)
    (htest_ub : minutesToTest.val ≤ 100)
    (h1 : Aegis.PoorPigs.poor_pigs buckets1 minutesToDie minutesToTest = ok r1)
    (h2 : Aegis.PoorPigs.poor_pigs buckets2 minutesToDie minutesToTest = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (buckets1 buckets2 minutesToDie minutesToTest : I64) (r1 r2 : I64)
    (hbuckets1_lb : 1 ≤ buckets1.val) (hbuckets12 : buckets1.val ≤ buckets2.val)
    (hbuckets2_ub : buckets2.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val)
    (hdie_test : minutesToDie.val ≤ minutesToTest.val)
    (htest_ub : minutesToTest.val ≤ 100)
    (h1 : Aegis.PoorPigs.poor_pigs buckets1 minutesToDie minutesToTest = ok r1)
    (h2 : Aegis.PoorPigs.poor_pigs buckets2 minutesToDie minutesToTest = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- If the function returns r1 on (buckets, minutesToDie1, minutesToTest1) and r2 on (buckets, minutesToDie2, minutesToTest2), then r1 >= r2.
  Preconditions: For two inputs (buckets, minutesToDie1, minutesToTest1) and (buckets, minutesToDie2, minutesToTest2), assume 1 <= buckets <= 1000, 1 <= minutesToDie1 <= minutesToTest1 <= 100, 1 <= minutesToDie2 <= minutesToTest2 <= 100, and let q1 = minutesToTest1 / minutesToDie1 and q2 = minutesToTest2 / minutesToDie2 with q1 <= q2. -/
theorem spec_10 (buckets minutesToDie1 minutesToTest1 minutesToDie2 minutesToTest2 : I64)
    (r1 r2 : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie1_lb : 1 ≤ minutesToDie1.val)
    (hdie1_test1 : minutesToDie1.val ≤ minutesToTest1.val)
    (htest1_ub : minutesToTest1.val ≤ 100)
    (hdie2_lb : 1 ≤ minutesToDie2.val)
    (hdie2_test2 : minutesToDie2.val ≤ minutesToTest2.val)
    (htest2_ub : minutesToTest2.val ≤ 100)
    (hq : q minutesToDie1 minutesToTest1 ≤ q minutesToDie2 minutesToTest2)
    (h1 : Aegis.PoorPigs.poor_pigs buckets minutesToDie1 minutesToTest1 = ok r1)
    (h2 : Aegis.PoorPigs.poor_pigs buckets minutesToDie2 minutesToTest2 = ok r2) :
    r1.val ≥ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (buckets minutesToDie1 minutesToTest1 minutesToDie2 minutesToTest2 : I64)
    (r1 r2 : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie1_lb : 1 ≤ minutesToDie1.val)
    (hdie1_test1 : minutesToDie1.val ≤ minutesToTest1.val)
    (htest1_ub : minutesToTest1.val ≤ 100)
    (hdie2_lb : 1 ≤ minutesToDie2.val)
    (hdie2_test2 : minutesToDie2.val ≤ minutesToTest2.val)
    (htest2_ub : minutesToTest2.val ≤ 100)
    (hq : q minutesToDie1 minutesToTest1 ≤ q minutesToDie2 minutesToTest2)
    (h1 : Aegis.PoorPigs.poor_pigs buckets minutesToDie1 minutesToTest1 = ok r1)
    (h2 : Aegis.PoorPigs.poor_pigs buckets minutesToDie2 minutesToTest2 = ok r2), r1.val ≥ r2.val) := by
  sorry

/-- If the function returns r1 on (buckets, minutesToDie1, minutesToTest1) and r2 on (buckets, minutesToDie2, minutesToTest2), then r1 = r2.
  Preconditions: For two inputs (buckets, minutesToDie1, minutesToTest1) and (buckets, minutesToDie2, minutesToTest2), assume 1 <= buckets <= 1000, 1 <= minutesToDie1 <= minutesToTest1 <= 100, 1 <= minutesToDie2 <= minutesToTest2 <= 100, and minutesToTest1 / minutesToDie1 = minutesToTest2 / minutesToDie2. -/
theorem spec_11 (buckets minutesToDie1 minutesToTest1 minutesToDie2 minutesToTest2 : I64)
    (r1 r2 : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie1_lb : 1 ≤ minutesToDie1.val)
    (hdie1_test1 : minutesToDie1.val ≤ minutesToTest1.val)
    (htest1_ub : minutesToTest1.val ≤ 100)
    (hdie2_lb : 1 ≤ minutesToDie2.val)
    (hdie2_test2 : minutesToDie2.val ≤ minutesToTest2.val)
    (htest2_ub : minutesToTest2.val ≤ 100)
    (hq : q minutesToDie1 minutesToTest1 = q minutesToDie2 minutesToTest2)
    (h1 : Aegis.PoorPigs.poor_pigs buckets minutesToDie1 minutesToTest1 = ok r1)
    (h2 : Aegis.PoorPigs.poor_pigs buckets minutesToDie2 minutesToTest2 = ok r2) :
    r1.val = r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (buckets minutesToDie1 minutesToTest1 minutesToDie2 minutesToTest2 : I64)
    (r1 r2 : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie1_lb : 1 ≤ minutesToDie1.val)
    (hdie1_test1 : minutesToDie1.val ≤ minutesToTest1.val)
    (htest1_ub : minutesToTest1.val ≤ 100)
    (hdie2_lb : 1 ≤ minutesToDie2.val)
    (hdie2_test2 : minutesToDie2.val ≤ minutesToTest2.val)
    (htest2_ub : minutesToTest2.val ≤ 100)
    (hq : q minutesToDie1 minutesToTest1 = q minutesToDie2 minutesToTest2)
    (h1 : Aegis.PoorPigs.poor_pigs buckets minutesToDie1 minutesToTest1 = ok r1)
    (h2 : Aegis.PoorPigs.poor_pigs buckets minutesToDie2 minutesToTest2 = ok r2), r1.val = r2.val) := by
  sorry

/-- The function returns a result r, and r is the least nonnegative integer such that 2^r >= buckets.
  Preconditions: 1 <= buckets <= 1000, 1 <= minutesToDie <= 100, and minutesToTest = minutesToDie. -/
theorem spec_12 (buckets minutesToDie minutesToTest : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val) (hdie_ub : minutesToDie.val ≤ 100)
    (htest_eq : minutesToTest.val = minutesToDie.val) :
    ∃ r : I64,
      Aegis.PoorPigs.poor_pigs buckets minutesToDie minutesToTest = ok r ∧
        IsLeastPigs buckets.val 2 r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (buckets minutesToDie minutesToTest : I64)
    (hbuckets_lb : 1 ≤ buckets.val) (hbuckets_ub : buckets.val ≤ 1000)
    (hdie_lb : 1 ≤ minutesToDie.val) (hdie_ub : minutesToDie.val ≤ 100)
    (htest_eq : minutesToTest.val = minutesToDie.val), ∃ r : I64,
      Aegis.PoorPigs.poor_pigs buckets minutesToDie minutesToTest = ok r ∧
        IsLeastPigs buckets.val 2 r.val) := by
  sorry

end AegisSpec.PoorPigs
