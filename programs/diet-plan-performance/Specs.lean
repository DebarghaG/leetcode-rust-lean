import Aegis.DietPlanPerformance.Code.Funs

/-!
# Specifications of `Aegis.DietPlanPerformance.diet_plan_performance`

LeetCode problem `diet-plan-performance`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.DietPlanPerformance

namespace AegisSpec.DietPlanPerformance

def vals (s : Slice Std.I64) : List Int := s.val.map (fun x => x.val)

def score (lower upper T : Int) : Int :=
  if T < lower then -1 else if T > upper then 1 else 0

def windowSum (l : List Int) (k i : Nat) : Int := ((l.drop i).take k).sum

def numWindows (n k : Nat) : Nat := n - k + 1

def winCount (calories : Slice Std.I64) (k : Int) : Nat :=
  numWindows (vals calories).length k.toNat

def totalScore (l : List Int) (k : Nat) (lower upper : Int) : Int :=
  ((List.range (numWindows l.length k)).map
    (fun i => score lower upper (windowSum l k i))).sum

def allWindowsAccepted (l : List Int) (k : Nat) (lower upper : Int) : Prop :=
  ∀ i, i < numWindows l.length k → lower ≤ windowSum l k i ∧ windowSum l k i ≤ upper

def allWindowsBelow (l : List Int) (k : Nat) (lower : Int) : Prop :=
  ∀ i, i < numWindows l.length k → windowSum l k i < lower

def allWindowsAbove (l : List Int) (k : Nat) (upper : Int) : Prop :=
  ∀ i, i < numWindows l.length k → upper < windowSum l k i

/-- Whenever the function returns a result r, r = Σ_{i=0}^{W-1} f(S(i)), where W = len(calories) - k + 1, S(i) = Σ_{j=0}^{k-1} calories[i+j] for 0 <= i < W, and f(T) = -1 if T < lower, f(T) = +1 if T > upper, and f(T) = 0 otherwise.
  Preconditions: Let n = len(calories). 1 <= k <= n <= 10^5. For every i with 0 <= i < n, 0 <= calories[i] <= 20000. 0 <= lower <= upper. All parameters are within the i64 range. -/
theorem spec_1 (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val) :
    ∀ r : Std.I64, diet_plan_performance calories k lower upper = ok r →
      r.val = totalScore (vals calories) k.val.toNat lower.val upper.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val), ∀ r : Std.I64, diet_plan_performance calories k lower upper = ok r →
      r.val = totalScore (vals calories) k.val.toNat lower.val upper.val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r (i.e., it does not fail or panic).
  Preconditions: Let n = len(calories). 1 <= k <= n <= 10^5. For every i with 0 <= i < n, 0 <= calories[i] <= 20000. 0 <= lower <= upper. All parameters are within the i64 range. -/
theorem spec_2 (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val) :
    ∃ r : Std.I64, diet_plan_performance calories k lower upper = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val), ∃ r : Std.I64, diet_plan_performance calories k lower upper = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= len(calories) - k + 1. (Let W = len(calories) - k + 1; each of the W windows contributes at most +1.)
  Preconditions: Let n = len(calories). 1 <= k <= n <= 10^5. For every i with 0 <= i < n, 0 <= calories[i] <= 20000. 0 <= lower <= upper. All parameters are within the i64 range. -/
theorem spec_3 (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val) :
    ∀ r : Std.I64, diet_plan_performance calories k lower upper = ok r →
      r.val ≤ ((winCount calories k.val : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val), ∀ r : Std.I64, diet_plan_performance calories k lower upper = ok r →
      r.val ≤ ((winCount calories k.val : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r >= -(len(calories) - k + 1). (Each of the W windows contributes at least -1.)
  Preconditions: Let n = len(calories). 1 <= k <= n <= 10^5. For every i with 0 <= i < n, 0 <= calories[i] <= 20000. 0 <= lower <= upper. All parameters are within the i64 range. -/
theorem spec_4 (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val) :
    ∀ r : Std.I64, diet_plan_performance calories k lower upper = ok r →
      -((winCount calories k.val : Nat) : Int) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val), ∀ r : Std.I64, diet_plan_performance calories k lower upper = ok r →
      -((winCount calories k.val : Nat) : Int) ≤ r.val) := by
  sorry

/-- If for every i with 0 <= i < W, lower <= S(i) <= upper, where W = len(calories) - k + 1 and S(i) = Σ_{j=0}^{k-1} calories[i+j], then whenever the function returns a result r, r = 0.
  Preconditions: Let n = len(calories). 1 <= k <= n <= 10^5. For every i with 0 <= i < n, 0 <= calories[i] <= 20000. 0 <= lower <= upper. All parameters are within the i64 range. -/
theorem spec_5 (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val)
    (hwithin : allWindowsAccepted (vals calories) k.val.toNat lower.val upper.val) :
    ∀ r : Std.I64, diet_plan_performance calories k lower upper = ok r → r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val)
    (hwithin : allWindowsAccepted (vals calories) k.val.toNat lower.val upper.val), ∀ r : Std.I64, diet_plan_performance calories k lower upper = ok r → r.val = 0) := by
  sorry

/-- If for every i with 0 <= i < W, S(i) < lower, where W = len(calories) - k + 1 and S(i) = Σ_{j=0}^{k-1} calories[i+j], then whenever the function returns a result r, r = -(len(calories) - k + 1).
  Preconditions: Let n = len(calories). 1 <= k <= n <= 10^5. For every i with 0 <= i < n, 0 <= calories[i] <= 20000. 0 <= lower <= upper. All parameters are within the i64 range. -/
theorem spec_6 (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val)
    (hbelow : allWindowsBelow (vals calories) k.val.toNat lower.val) :
    ∀ r : Std.I64, diet_plan_performance calories k lower upper = ok r →
      r.val = -((winCount calories k.val : Nat) : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val)
    (hbelow : allWindowsBelow (vals calories) k.val.toNat lower.val), ∀ r : Std.I64, diet_plan_performance calories k lower upper = ok r →
      r.val = -((winCount calories k.val : Nat) : Int)) := by
  sorry

/-- If for every i with 0 <= i < W, S(i) > upper, where W = len(calories) - k + 1 and S(i) = Σ_{j=0}^{k-1} calories[i+j], then whenever the function returns a result r, r = len(calories) - k + 1.
  Preconditions: Let n = len(calories). 1 <= k <= n <= 10^5. For every i with 0 <= i < n, 0 <= calories[i] <= 20000. 0 <= lower <= upper. All parameters are within the i64 range. -/
theorem spec_7 (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val)
    (habove : allWindowsAbove (vals calories) k.val.toNat upper.val) :
    ∀ r : Std.I64, diet_plan_performance calories k lower upper = ok r →
      r.val = ((winCount calories k.val : Nat) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val)
    (habove : allWindowsAbove (vals calories) k.val.toNat upper.val), ∀ r : Std.I64, diet_plan_performance calories k lower upper = ok r →
      r.val = ((winCount calories k.val : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, if r > 0 then there exists an index i with 0 <= i < W, where W = len(calories) - k + 1, such that S(i) > upper, where S(i) = Σ_{j=0}^{k-1} calories[i+j].
  Preconditions: Let n = len(calories). 1 <= k <= n <= 10^5. For every i with 0 <= i < n, 0 <= calories[i] <= 20000. 0 <= lower <= upper. All parameters are within the i64 range. -/
theorem spec_8 (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val) :
    ∀ r : Std.I64, diet_plan_performance calories k lower upper = ok r → 0 < r.val →
      ∃ i : Nat, i < winCount calories k.val ∧
        upper.val < windowSum (vals calories) k.val.toNat i := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val), ∀ r : Std.I64, diet_plan_performance calories k lower upper = ok r → 0 < r.val →
      ∃ i : Nat, i < winCount calories k.val ∧
        upper.val < windowSum (vals calories) k.val.toNat i) := by
  sorry

/-- Whenever the function returns a result r, if r < 0 then there exists an index i with 0 <= i < W, where W = len(calories) - k + 1, such that S(i) < lower, where S(i) = Σ_{j=0}^{k-1} calories[i+j].
  Preconditions: Let n = len(calories). 1 <= k <= n <= 10^5. For every i with 0 <= i < n, 0 <= calories[i] <= 20000. 0 <= lower <= upper. All parameters are within the i64 range. -/
theorem spec_9 (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val) :
    ∀ r : Std.I64, diet_plan_performance calories k lower upper = ok r → r.val < 0 →
      ∃ i : Nat, i < winCount calories k.val ∧
        windowSum (vals calories) k.val.toNat i < lower.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val), ∀ r : Std.I64, diet_plan_performance calories k lower upper = ok r → r.val < 0 →
      ∃ i : Nat, i < winCount calories k.val ∧
        windowSum (vals calories) k.val.toNat i < lower.val) := by
  sorry

/-- Whenever diet_plan_performance(calories, k, lower, upper) returns r and diet_plan_performance(calories_shifted, k, lower_shifted, upper_shifted) returns r', where calories_shifted[i] = calories[i] + c for all 0 <= i < n, lower_shifted = lower + k*c, and upper_shifted = upper + k*c, we have r = r'.
  Preconditions: Let n = len(calories). 1 <= k <= n <= 10^5. For every i with 0 <= i < n, 0 <= calories[i] <= 20000. 0 <= lower <= upper. Let c be an integer such that for every i, 0 <= calories[i] + c <= 20000, and 0 <= lower + k*c <= upper + k*c, and all shifted values are within the i64 range. -/
theorem spec_10 (calories calories_shifted : Slice Std.I64)
    (k lower upper lower_shifted upper_shifted : Std.I64) (c : Int)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val)
    (hshift_cal : vals calories_shifted = (vals calories).map (fun v => v + c))
    (hshift_cal_bounds : ∀ v ∈ vals calories, 0 ≤ v + c ∧ v + c ≤ 20000)
    (hshift_lower : lower_shifted.val = lower.val + k.val * c)
    (hshift_upper : upper_shifted.val = upper.val + k.val * c)
    (hshift_bounds : 0 ≤ lower.val + k.val * c ∧ lower.val + k.val * c ≤ upper.val + k.val * c) :
    ∀ r r' : Std.I64,
      diet_plan_performance calories k lower upper = ok r →
      diet_plan_performance calories_shifted k lower_shifted upper_shifted = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (calories calories_shifted : Slice Std.I64)
    (k lower upper lower_shifted upper_shifted : Std.I64) (c : Int)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val)
    (hshift_cal : vals calories_shifted = (vals calories).map (fun v => v + c))
    (hshift_cal_bounds : ∀ v ∈ vals calories, 0 ≤ v + c ∧ v + c ≤ 20000)
    (hshift_lower : lower_shifted.val = lower.val + k.val * c)
    (hshift_upper : upper_shifted.val = upper.val + k.val * c)
    (hshift_bounds : 0 ≤ lower.val + k.val * c ∧ lower.val + k.val * c ≤ upper.val + k.val * c), ∀ r r' : Std.I64,
      diet_plan_performance calories k lower upper = ok r →
      diet_plan_performance calories_shifted k lower_shifted upper_shifted = ok r' →
      r.val = r'.val) := by
  sorry

/-- Whenever diet_plan_performance(calories, k, lower, upper1) returns r1 and diet_plan_performance(calories, k, lower, upper2) returns r2, we have r1 >= r2.
  Preconditions: Let n = len(calories). 1 <= k <= n <= 10^5. For every i with 0 <= i < n, 0 <= calories[i] <= 20000. Let upper1 and upper2 be integers with 0 <= lower <= upper1 <= upper2, and all values within the i64 range. -/
theorem spec_11 (calories : Slice Std.I64) (k lower upper1 upper2 : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hu1 : lower.val ≤ upper1.val)
    (hu12 : upper1.val ≤ upper2.val) :
    ∀ r1 r2 : Std.I64,
      diet_plan_performance calories k lower upper1 = ok r1 →
      diet_plan_performance calories k lower upper2 = ok r2 →
      r2.val ≤ r1.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (calories : Slice Std.I64) (k lower upper1 upper2 : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hu1 : lower.val ≤ upper1.val)
    (hu12 : upper1.val ≤ upper2.val), ∀ r1 r2 : Std.I64,
      diet_plan_performance calories k lower upper1 = ok r1 →
      diet_plan_performance calories k lower upper2 = ok r2 →
      r2.val ≤ r1.val) := by
  sorry

/-- Whenever diet_plan_performance(calories, k, lower1, upper) returns r1 and diet_plan_performance(calories, k, lower2, upper) returns r2, we have r1 >= r2.
  Preconditions: Let n = len(calories). 1 <= k <= n <= 10^5. For every i with 0 <= i < n, 0 <= calories[i] <= 20000. Let lower1 and lower2 be integers with 0 <= lower1 <= lower2 <= upper, and all values within the i64 range. -/
theorem spec_12 (calories : Slice Std.I64) (k lower1 lower2 upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hl1 : 0 ≤ lower1.val)
    (hl12 : lower1.val ≤ lower2.val)
    (hlu : lower2.val ≤ upper.val) :
    ∀ r1 r2 : Std.I64,
      diet_plan_performance calories k lower1 upper = ok r1 →
      diet_plan_performance calories k lower2 upper = ok r2 →
      r2.val ≤ r1.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (calories : Slice Std.I64) (k lower1 lower2 upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hl1 : 0 ≤ lower1.val)
    (hl12 : lower1.val ≤ lower2.val)
    (hlu : lower2.val ≤ upper.val), ∀ r1 r2 : Std.I64,
      diet_plan_performance calories k lower1 upper = ok r1 →
      diet_plan_performance calories k lower2 upper = ok r2 →
      r2.val ≤ r1.val) := by
  sorry

/-- Let W = len(calories) - k + 1 and for 0 <= i < W let S(i) = Σ_{j=0}^{k-1} calories[i+j]. If there exists an integer T such that S(i) = T for every i with 0 <= i < W, then whenever the function returns a result r, r = W * f(T), where f(T) = -1 if T < lower, f(T) = +1 if T > upper, and f(T) = 0 otherwise.
  Preconditions: Let n = len(calories). 1 <= k <= n <= 10^5. For every i with 0 <= i < n, 0 <= calories[i] <= 20000. 0 <= lower <= upper. All parameters are within the i64 range. -/
theorem spec_13 (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val) :
    ∀ T : Int,
      (∀ i : Nat, i < winCount calories k.val →
        windowSum (vals calories) k.val.toNat i = T) →
      ∀ r : Std.I64, diet_plan_performance calories k lower upper = ok r →
        r.val = ((winCount calories k.val : Nat) : Int) * score lower.val upper.val T := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (calories : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val), ∀ T : Int,
      (∀ i : Nat, i < winCount calories k.val →
        windowSum (vals calories) k.val.toNat i = T) →
      ∀ r : Std.I64, diet_plan_performance calories k lower upper = ok r →
        r.val = ((winCount calories k.val : Nat) : Int) * score lower.val upper.val T) := by
  sorry

/-- Let n = len(calories) and define calories_rev[i] = calories[n-1-i] for 0 <= i < n. Whenever diet_plan_performance(calories, k, lower, upper) returns r and diet_plan_performance(calories_rev, k, lower, upper) returns r_rev, we have r = r_rev.
  Preconditions: Let n = len(calories). 1 <= k <= n <= 10^5. For every i with 0 <= i < n, 0 <= calories[i] <= 20000. 0 <= lower <= upper. All parameters are within the i64 range. -/
theorem spec_14 (calories calories_rev : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val)
    (hrev : vals calories_rev = (vals calories).reverse) :
    ∀ r r_rev : Std.I64,
      diet_plan_performance calories k lower upper = ok r →
      diet_plan_performance calories_rev k lower upper = ok r_rev →
      r.val = r_rev.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (calories calories_rev : Slice Std.I64) (k lower upper : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (calories.val.length : Int))
    (hn_le : calories.val.length ≤ 100000)
    (hcal : ∀ x ∈ calories.val, 0 ≤ x.val ∧ x.val ≤ 20000)
    (hlower : 0 ≤ lower.val)
    (hlu : lower.val ≤ upper.val)
    (hrev : vals calories_rev = (vals calories).reverse), ∀ r r_rev : Std.I64,
      diet_plan_performance calories k lower upper = ok r →
      diet_plan_performance calories_rev k lower upper = ok r_rev →
      r.val = r_rev.val) := by
  sorry

end AegisSpec.DietPlanPerformance
