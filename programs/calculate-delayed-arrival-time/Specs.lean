import Aegis.FindDelayedArrivalTime.Code.Funs

/-!
# Specifications of `Aegis.FindDelayedArrivalTime.find_delayed_arrival_time`

LeetCode problem `calculate-delayed-arrival-time`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.FindDelayedArrivalTime (find_delayed_arrival_time)

namespace AegisSpec.FindDelayedArrivalTime

/-- The function returns a result r and does not fail. This r is the unique integer such that 0 <= r < 24 and r is congruent to arrivalTime + delayedTime modulo 24; equivalently, r = (arrivalTime + delayedTime) mod 24 with the remainder taken in {0,1,...,23}.
  Preconditions: arrivalTime and delayedTime are i64 values satisfying 1 <= arrivalTime < 24 and 1 <= delayedTime <= 24. Interpret arrivalTime and delayedTime as ordinary integers for the arithmetic in this statement. -/
theorem spec_1 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24) :
    ∃ r, find_delayed_arrival_time arrivalTime delayedTime = ok r ∧
      0 ≤ r.val ∧ r.val < 24 ∧
      r.val = (arrivalTime.val + delayedTime.val) % 24 ∧
      (24 : ℤ) ∣ r.val - (arrivalTime.val + delayedTime.val) ∧
      (∀ s : ℤ, 0 ≤ s → s < 24 →
        (24 : ℤ) ∣ s - (arrivalTime.val + delayedTime.val) → s = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24), ∃ r, find_delayed_arrival_time arrivalTime delayedTime = ok r ∧
      0 ≤ r.val ∧ r.val < 24 ∧
      r.val = (arrivalTime.val + delayedTime.val) % 24 ∧
      (24 : ℤ) ∣ r.val - (arrivalTime.val + delayedTime.val) ∧
      (∀ s : ℤ, 0 ≤ s → s < 24 →
        (24 : ℤ) ∣ s - (arrivalTime.val + delayedTime.val) → s = r.val)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or go out of bounds on these inputs.
  Preconditions: arrivalTime and delayedTime are i64 values satisfying 1 <= arrivalTime < 24 and 1 <= delayedTime <= 24. -/
theorem spec_2 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24) :
    ∃ r, find_delayed_arrival_time arrivalTime delayedTime = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24), ∃ r, find_delayed_arrival_time arrivalTime delayedTime = ok r) := by
  sorry

/-- Whenever the function returns a result r, one has 0 <= r < 24.
  Preconditions: arrivalTime and delayedTime are i64 values satisfying 1 <= arrivalTime < 24 and 1 <= delayedTime <= 24. -/
theorem spec_3 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24) :
    ∀ r, find_delayed_arrival_time arrivalTime delayedTime = ok r → 0 ≤ r.val ∧ r.val < 24 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24), ∀ r, find_delayed_arrival_time arrivalTime delayedTime = ok r → 0 ≤ r.val ∧ r.val < 24) := by
  sorry

/-- Whenever the function returns a result r, 24 divides r - (arrivalTime + delayedTime); equivalently, r and arrivalTime + delayedTime are congruent modulo 24.
  Preconditions: arrivalTime and delayedTime are i64 values satisfying 1 <= arrivalTime < 24 and 1 <= delayedTime <= 24. -/
theorem spec_4 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24) :
    ∀ r, find_delayed_arrival_time arrivalTime delayedTime = ok r →
      (24 : ℤ) ∣ r.val - (arrivalTime.val + delayedTime.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24), ∀ r, find_delayed_arrival_time arrivalTime delayedTime = ok r →
      (24 : ℤ) ∣ r.val - (arrivalTime.val + delayedTime.val)) := by
  sorry

/-- The function returns a result r and r = arrivalTime + delayedTime.
  Preconditions: arrivalTime and delayedTime are i64 values satisfying 1 <= arrivalTime < 24, 1 <= delayedTime <= 24, and arrivalTime + delayedTime < 24. -/
theorem spec_5 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24)
    (h_sum_lt : arrivalTime.val + delayedTime.val < 24) :
    ∃ r, find_delayed_arrival_time arrivalTime delayedTime = ok r ∧
      r.val = arrivalTime.val + delayedTime.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24)
    (h_sum_lt : arrivalTime.val + delayedTime.val < 24), ∃ r, find_delayed_arrival_time arrivalTime delayedTime = ok r ∧
      r.val = arrivalTime.val + delayedTime.val) := by
  sorry

/-- The function returns a result r and r = 0.
  Preconditions: arrivalTime and delayedTime are i64 values satisfying 1 <= arrivalTime < 24, 1 <= delayedTime <= 24, and arrivalTime + delayedTime = 24. -/
theorem spec_6 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24)
    (h_sum_eq : arrivalTime.val + delayedTime.val = 24) :
    ∃ r, find_delayed_arrival_time arrivalTime delayedTime = ok r ∧ r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24)
    (h_sum_eq : arrivalTime.val + delayedTime.val = 24), ∃ r, find_delayed_arrival_time arrivalTime delayedTime = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r and r = arrivalTime + delayedTime - 24.
  Preconditions: arrivalTime and delayedTime are i64 values satisfying 1 <= arrivalTime < 24, 1 <= delayedTime <= 24, and arrivalTime + delayedTime > 24. -/
theorem spec_7 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24)
    (h_sum_gt : 24 < arrivalTime.val + delayedTime.val) :
    ∃ r, find_delayed_arrival_time arrivalTime delayedTime = ok r ∧
      r.val = arrivalTime.val + delayedTime.val - 24 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24)
    (h_sum_gt : 24 < arrivalTime.val + delayedTime.val), ∃ r, find_delayed_arrival_time arrivalTime delayedTime = ok r ∧
      r.val = arrivalTime.val + delayedTime.val - 24) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if arrivalTime + delayedTime = 24.
  Preconditions: arrivalTime and delayedTime are i64 values satisfying 1 <= arrivalTime < 24 and 1 <= delayedTime <= 24. -/
theorem spec_8 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24) :
    ∀ r, find_delayed_arrival_time arrivalTime delayedTime = ok r →
      (r.val = 0 ↔ arrivalTime.val + delayedTime.val = 24) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24), ∀ r, find_delayed_arrival_time arrivalTime delayedTime = ok r →
      (r.val = 0 ↔ arrivalTime.val + delayedTime.val = 24)) := by
  sorry

/-- Whenever the function returns a result r, r = arrivalTime if and only if delayedTime = 24.
  Preconditions: arrivalTime and delayedTime are i64 values satisfying 1 <= arrivalTime < 24 and 1 <= delayedTime <= 24. -/
theorem spec_9 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24) :
    ∀ r, find_delayed_arrival_time arrivalTime delayedTime = ok r →
      (r.val = arrivalTime.val ↔ delayedTime.val = 24) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24), ∀ r, find_delayed_arrival_time arrivalTime delayedTime = ok r →
      (r.val = arrivalTime.val ↔ delayedTime.val = 24)) := by
  sorry

/-- Whenever the function returns a result r, r < arrivalTime + delayedTime if and only if arrivalTime + delayedTime >= 24.
  Preconditions: arrivalTime and delayedTime are i64 values satisfying 1 <= arrivalTime < 24 and 1 <= delayedTime <= 24. -/
theorem spec_10 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24) :
    ∀ r, find_delayed_arrival_time arrivalTime delayedTime = ok r →
      (r.val < arrivalTime.val + delayedTime.val ↔ 24 ≤ arrivalTime.val + delayedTime.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24), ∀ r, find_delayed_arrival_time arrivalTime delayedTime = ok r →
      (r.val < arrivalTime.val + delayedTime.val ↔ 24 ≤ arrivalTime.val + delayedTime.val)) := by
  sorry

end AegisSpec.FindDelayedArrivalTime
