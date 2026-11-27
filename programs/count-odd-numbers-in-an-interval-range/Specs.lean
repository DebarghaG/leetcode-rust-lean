import Aegis.CountOdds.Code.Funs

/-!
# Specifications of `Aegis.CountOdds.count_odds`

LeetCode problem `count-odd-numbers-in-an-interval-range`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountOdds

  def countOddInRange (lo hi : ℤ) : ℕ :=
    ((List.range (hi - lo + 1).toNat).filter (fun i => (lo + (i : ℤ)) % 2 = 1)).length

  def countEvenInRange (lo hi : ℤ) : ℕ :=
    ((List.range (hi - lo + 1).toNat).filter (fun i => (lo + (i : ℤ)) % 2 = 0)).length

  def IsOddIn (lo hi k : ℤ) : Prop := k % 2 = 1 ∧ lo ≤ k ∧ k ≤ hi

  /-- Whenever count_odds returns a result r, the integer value of r is the number of integers k such that low <= k <= high and k is odd (k mod 2 = 1). Equivalently, r = (high + 1) / 2 - low / 2, where / denotes integer division rounding down.
    Preconditions: 0 <= low <= high <= 10^9, interpreting the I64 parameters low and high as their mathematical integer values. -/
  theorem spec_1 (low high r : Std.I64)
      (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
      (h_res : Aegis.CountOdds.count_odds low high = ok r) :
      (r.val = (countOddInRange low.val high.val : ℤ)) ∧
        r.val = (high.val + 1) / 2 - low.val / 2 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (low high r : Std.I64)
        (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
        (h_res : Aegis.CountOdds.count_odds low high = ok r), (r.val = (countOddInRange low.val high.val : ℤ)) ∧
          r.val = (high.val + 1) / 2 - low.val / 2) := by
    sorry

  /-- For every input satisfying the preconditions, count_odds returns a result r (it does not fail).
    Preconditions: 0 <= low <= high <= 10^9, interpreting the I64 parameters low and high as their mathematical integer values. -/
  theorem spec_2 (low high : Std.I64)
      (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ (10 ^ 9 : ℤ)) :
      ∃ r : Std.I64, Aegis.CountOdds.count_odds low high = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (low high : Std.I64)
        (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ (10 ^ 9 : ℤ)), ∃ r : Std.I64, Aegis.CountOdds.count_odds low high = ok r) := by
    sorry

  /-- Whenever count_odds returns a result r, 0 <= r.
    Preconditions: 0 <= low <= high <= 10^9, interpreting the I64 parameters low and high as their mathematical integer values. -/
  theorem spec_3 (low high r : Std.I64)
      (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
      (h_res : Aegis.CountOdds.count_odds low high = ok r) :
      0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (low high r : Std.I64)
        (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
        (h_res : Aegis.CountOdds.count_odds low high = ok r), 0 ≤ r.val) := by
    sorry

  /-- Whenever count_odds returns a result r, r <= (high - low + 2) / 2, where / denotes integer division rounding down.
    Preconditions: 0 <= low <= high <= 10^9, interpreting the I64 parameters low and high as their mathematical integer values. -/
  theorem spec_4 (low high r : Std.I64)
      (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
      (h_res : Aegis.CountOdds.count_odds low high = ok r) :
      r.val ≤ (high.val - low.val + 2) / 2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (low high r : Std.I64)
        (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
        (h_res : Aegis.CountOdds.count_odds low high = ok r), r.val ≤ (high.val - low.val + 2) / 2) := by
    sorry

  /-- Whenever count_odds returns a result r, r <= 500000000.
    Preconditions: 0 <= low <= high <= 10^9, interpreting the I64 parameters low and high as their mathematical integer values. -/
  theorem spec_5 (low high r : Std.I64)
      (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
      (h_res : Aegis.CountOdds.count_odds low high = ok r) :
      r.val ≤ 500000000 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (low high r : Std.I64)
        (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
        (h_res : Aegis.CountOdds.count_odds low high = ok r), r.val ≤ 500000000) := by
    sorry

  /-- Whenever count_odds returns a result r, r = (high - low + 1) / 2.
    Preconditions: 0 <= low <= high <= 10^9 and high - low is odd (so high - low + 1 is even), interpreting the I64 parameters low and high as their mathematical integer values. -/
  theorem spec_6 (low high r : Std.I64)
      (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
      (h_diff_odd : (high.val - low.val) % 2 = 1)
      (h_res : Aegis.CountOdds.count_odds low high = ok r) :
      r.val = (high.val - low.val + 1) / 2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (low high r : Std.I64)
        (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
        (h_diff_odd : (high.val - low.val) % 2 = 1)
        (h_res : Aegis.CountOdds.count_odds low high = ok r), r.val = (high.val - low.val + 1) / 2) := by
    sorry

  /-- Whenever count_odds returns a result r, if low is odd then r = (high - low + 2) / 2, and if low is even then r = (high - low) / 2.
    Preconditions: 0 <= low <= high <= 10^9 and high - low is even (so high - low + 1 is odd), interpreting the I64 parameters low and high as their mathematical integer values. -/
  theorem spec_7 (low high r : Std.I64)
      (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
      (h_diff_even : (high.val - low.val) % 2 = 0)
      (h_res : Aegis.CountOdds.count_odds low high = ok r) :
      ((low.val % 2 = 1 → r.val = (high.val - low.val + 2) / 2) ∧
        (low.val % 2 = 0 → r.val = (high.val - low.val) / 2)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (low high r : Std.I64)
        (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
        (h_diff_even : (high.val - low.val) % 2 = 0)
        (h_res : Aegis.CountOdds.count_odds low high = ok r), ((low.val % 2 = 1 → r.val = (high.val - low.val + 2) / 2) ∧
          (low.val % 2 = 0 → r.val = (high.val - low.val) / 2))) := by
    sorry

  /-- Whenever count_odds returns a result r, if low is odd then r >= 1, and if high is odd then r >= 1.
    Preconditions: 0 <= low <= high <= 10^9, interpreting the I64 parameters low and high as their mathematical integer values. -/
  theorem spec_8 (low high r : Std.I64)
      (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
      (h_res : Aegis.CountOdds.count_odds low high = ok r) :
      ((low.val % 2 = 1 → 1 ≤ r.val) ∧ (high.val % 2 = 1 → 1 ≤ r.val)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (low high r : Std.I64)
        (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
        (h_res : Aegis.CountOdds.count_odds low high = ok r), ((low.val % 2 = 1 → 1 ≤ r.val) ∧ (high.val % 2 = 1 → 1 ≤ r.val))) := by
    sorry

  /-- Whenever count_odds returns a result r and r > 0, there exists an odd integer k with low <= k <= high. In fact, one may take k = low when low is odd, and k = low + 1 when low is even.
    Preconditions: 0 <= low <= high <= 10^9, interpreting the I64 parameters low and high as their mathematical integer values. -/
  theorem spec_9 (low high r : Std.I64)
      (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
      (h_res : Aegis.CountOdds.count_odds low high = ok r)
      (h_pos : 0 < r.val) :
      (∃ k : ℤ, IsOddIn low.val high.val k) ∧
        (low.val % 2 = 1 → IsOddIn low.val high.val low.val) ∧
        (low.val % 2 = 0 → IsOddIn low.val high.val (low.val + 1)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (low high r : Std.I64)
        (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
        (h_res : Aegis.CountOdds.count_odds low high = ok r)
        (h_pos : 0 < r.val), (∃ k : ℤ, IsOddIn low.val high.val k) ∧
          (low.val % 2 = 1 → IsOddIn low.val high.val low.val) ∧
          (low.val % 2 = 0 → IsOddIn low.val high.val (low.val + 1))) := by
    sorry

  /-- Whenever count_odds returns a result r and r = 0, every integer k with low <= k <= high is even (k mod 2 = 0).
    Preconditions: 0 <= low <= high <= 10^9, interpreting the I64 parameters low and high as their mathematical integer values. -/
  theorem spec_10 (low high r : Std.I64)
      (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
      (h_res : Aegis.CountOdds.count_odds low high = ok r)
      (h_zero : r.val = 0) :
      ∀ k : ℤ, low.val ≤ k → k ≤ high.val → k % 2 = 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (low high r : Std.I64)
        (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
        (h_res : Aegis.CountOdds.count_odds low high = ok r)
        (h_zero : r.val = 0), ∀ k : ℤ, low.val ≤ k → k ≤ high.val → k % 2 = 0) := by
    sorry

  /-- Whenever count_odds returns a result r, r + E = high - low + 1, where E is the number of integers k such that low <= k <= high and k is even (k mod 2 = 0).
    Preconditions: 0 <= low <= high <= 10^9, interpreting the I64 parameters low and high as their mathematical integer values. -/
  theorem spec_11 (low high r : Std.I64)
      (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
      (h_res : Aegis.CountOdds.count_odds low high = ok r) :
      r.val + (countEvenInRange low.val high.val : ℤ) = high.val - low.val + 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (low high r : Std.I64)
        (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
        (h_res : Aegis.CountOdds.count_odds low high = ok r), r.val + (countEvenInRange low.val high.val : ℤ) = high.val - low.val + 1) := by
    sorry

  /-- Whenever count_odds returns a result r for (low, high), the integer value of r is the number of odd integers k such that low + 2 <= k <= high + 2.
    Preconditions: 0 <= low <= high <= 10^9, interpreting the I64 parameters low and high as their mathematical integer values. -/
  theorem spec_12 (low high r : Std.I64)
      (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
      (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
      (h_res : Aegis.CountOdds.count_odds low high = ok r) :
      r.val = (countOddInRange (low.val + 2) (high.val + 2) : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (low high r : Std.I64)
        (h_low_nonneg : 0 ≤ low.val) (h_low_le_high : low.val ≤ high.val)
        (h_high_le : high.val ≤ (10 ^ 9 : ℤ))
        (h_res : Aegis.CountOdds.count_odds low high = ok r), r.val = (countOddInRange (low.val + 2) (high.val + 2) : ℤ)) := by
    sorry

  end AegisSpec.CountOdds
