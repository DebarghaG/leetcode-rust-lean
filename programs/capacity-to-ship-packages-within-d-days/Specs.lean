import Aegis.ShipWithinDays.Code.Funs

/-!
# Specifications of `Aegis.ShipWithinDays.ship_within_days`

LeetCode problem `capacity-to-ship-packages-within-d-days`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ShipWithinDays

namespace AegisSpec.ShipWithinDays

def contents (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def segmentSum (ws : List ℤ) (a b : ℕ) : ℤ := ((ws.drop a).take (b - a)).sum

def totalWeight (ws : List ℤ) : ℤ := ws.sum

def maxWeight (ws : List ℤ) : ℤ := ws.foldr max 0

def ceilDiv (a b : ℤ) : ℤ := (a + b - 1) / b

def Feasible (ws : List ℤ) (d c : ℤ) : Prop :=
  ∃ (k : ℕ) (p : ℕ → ℕ),
    1 ≤ k ∧ (k : ℤ) ≤ d ∧ p 0 = 0 ∧ p k = ws.length ∧
      (∀ j, j < k → p j < p (j + 1)) ∧
      (∀ j, j < k → segmentSum ws (p j) (p (j + 1)) ≤ c)

def InI64Range (c : ℤ) : Prop := Std.I64.min ≤ c ∧ c ≤ Std.I64.max

/-- The function returns a result r. Define an integer capacity c to be feasible if there exist an integer k and indices 0 = p[0] < p[1] < ... < p[k] = len(weights) with 1 <= k <= days such that for every j with 1 <= j <= k, the sum of weights[i] over all i with p[j-1] <= i < p[j] is at most c. Then for every integer c in the range of Std.I64, capacity c is feasible if and only if r <= c.
  Preconditions: 1 <= days <= len(weights) <= 50000, and for every i with 0 <= i < len(weights), 1 <= weights[i] <= 500. -/
theorem spec_1
    (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500) :
    ∃ r : Std.I64,
      ship_within_days weights days = ok r ∧
        ∀ c : ℤ, InI64Range c → (Feasible (contents weights) days.val c ↔ r.val ≤ c) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500), ∃ r : Std.I64,
      ship_within_days weights days = ok r ∧
        ∀ c : ℤ, InI64Range c → (Feasible (contents weights) days.val c ↔ r.val ≤ c)) := by
  sorry

/-- The function returns a result r and does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: 1 <= days <= len(weights) <= 50000, and for every i with 0 <= i < len(weights), 1 <= weights[i] <= 500. -/
theorem spec_2
    (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500) :
    ∃ r : Std.I64, ship_within_days weights days = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500), ∃ r : Std.I64, ship_within_days weights days = ok r) := by
  sorry

/-- Whenever the function returns a result r, capacity r is feasible: there exist an integer k and indices 0 = p[0] < p[1] < ... < p[k] = len(weights) with 1 <= k <= days such that for every j with 1 <= j <= k, the sum of weights[i] over all i with p[j-1] <= i < p[j] is at most r.
  Preconditions: 1 <= days <= len(weights) <= 50000, and for every i with 0 <= i < len(weights), 1 <= weights[i] <= 500. -/
theorem spec_3
    (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r) :
    Feasible (contents weights) days.val r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r), Feasible (contents weights) days.val r.val) := by
  sorry

/-- Whenever the function returns a result r, no smaller capacity is feasible: for every integer c in the range of Std.I64 with c < r, there do not exist an integer k and indices 0 = p[0] < p[1] < ... < p[k] = len(weights) with 1 <= k <= days such that every block sum over p[j-1] <= i < p[j] is at most c.
  Preconditions: 1 <= days <= len(weights) <= 50000, and for every i with 0 <= i < len(weights), 1 <= weights[i] <= 500. -/
theorem spec_4
    (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r)
    (c : ℤ) (hc : InI64Range c) (hlt : c < r.val) :
    ¬ Feasible (contents weights) days.val c := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r)
    (c : ℤ) (hc : InI64Range c) (hlt : c < r.val), ¬ Feasible (contents weights) days.val c) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(weights), weights[i] <= r. Equivalently, r is at least the maximum package weight.
  Preconditions: 1 <= days <= len(weights) <= 50000, and for every i with 0 <= i < len(weights), 1 <= weights[i] <= 500. -/
theorem spec_5
    (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r) :
    ∀ (i : ℕ) (hi : i < weights.val.length), (weights.val[i]).val ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r), ∀ (i : ℕ) (hi : i < weights.val.length), (weights.val[i]).val ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r is at most the sum of all weights[i] for 0 <= i < len(weights).
  Preconditions: 1 <= days <= len(weights) <= 50000, and for every i with 0 <= i < len(weights), 1 <= weights[i] <= 500. -/
theorem spec_6
    (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r) :
    r.val ≤ totalWeight (contents weights) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r), r.val ≤ totalWeight (contents weights)) := by
  sorry

/-- Whenever the function returns a result r, days * r is at least the sum of all weights[i] for 0 <= i < len(weights). Equivalently, r >= ceiling(total_weight / days), where total_weight is the sum of all weights[i].
  Preconditions: 1 <= days <= len(weights) <= 50000, and for every i with 0 <= i < len(weights), 1 <= weights[i] <= 500. -/
theorem spec_7
    (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r) :
    totalWeight (contents weights) ≤ days.val * r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r), totalWeight (contents weights) ≤ days.val * r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= M * ceiling(len(weights) / days), where M is the maximum of weights[i] over 0 <= i < len(weights).
  Preconditions: 1 <= days <= len(weights) <= 50000, and for every i with 0 <= i < len(weights), 1 <= weights[i] <= 500. -/
theorem spec_8
    (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r) :
    r.val ≤ maxWeight (contents weights) *
      ceilDiv (weights.val.length : ℤ) days.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r), r.val ≤ maxWeight (contents weights) *
      ceilDiv (weights.val.length : ℤ) days.val) := by
  sorry

/-- Whenever the function returns a result r and days = 1, r equals the sum of all weights[i] for 0 <= i < len(weights).
  Preconditions: 1 <= days <= len(weights) <= 50000, and for every i with 0 <= i < len(weights), 1 <= weights[i] <= 500. -/
theorem spec_9
    (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r)
    (hdays : days.val = 1) :
    r.val = totalWeight (contents weights) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r)
    (hdays : days.val = 1), r.val = totalWeight (contents weights)) := by
  sorry

/-- Whenever the function returns a result r and days = len(weights), r equals the maximum of weights[i] over 0 <= i < len(weights).
  Preconditions: 1 <= days <= len(weights) <= 50000, and for every i with 0 <= i < len(weights), 1 <= weights[i] <= 500. -/
theorem spec_10
    (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r)
    (hdays : days.val = (weights.val.length : ℤ)) :
    r.val = maxWeight (contents weights) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r)
    (hdays : days.val = (weights.val.length : ℤ)), r.val = maxWeight (contents weights)) := by
  sorry

/-- Whenever the function returns a result r and there is an integer w such that weights[i] = w for every i with 0 <= i < len(weights), then r = w * ceiling(len(weights) / days).
  Preconditions: 1 <= days <= len(weights) <= 50000, and for every i with 0 <= i < len(weights), 1 <= weights[i] <= 500. -/
theorem spec_11
    (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r)
    (w : ℤ) (hwconst : ∀ (i : ℕ) (hi : i < weights.val.length), (weights.val[i]).val = w) :
    r.val = w * ceilDiv (weights.val.length : ℤ) days.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r)
    (w : ℤ) (hwconst : ∀ (i : ℕ) (hi : i < weights.val.length), (weights.val[i]).val = w), r.val = w * ceilDiv (weights.val.length : ℤ) days.val) := by
  sorry

/-- Whenever the function returns a result r, there exist indices a and b with 0 <= a < b <= len(weights) such that r equals the sum of weights[i] over all i with a <= i < b.
  Preconditions: 1 <= days <= len(weights) <= 50000, and for every i with 0 <= i < len(weights), 1 <= weights[i] <= 500. -/
theorem spec_12
    (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r) :
    ∃ a b : ℕ,
      a < b ∧ b ≤ weights.val.length ∧ r.val = segmentSum (contents weights) a b := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (weights : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r : Std.I64) (hr : ship_within_days weights days = ok r), ∃ a b : ℕ,
      a < b ∧ b ≤ weights.val.length ∧ r.val = segmentSum (contents weights) a b) := by
  sorry

/-- Whenever ship_within_days(weights, d1) returns r1 and ship_within_days(weights, d2) returns r2, we have r2 <= r1.
  Preconditions: For every weights and every d1 and d2 such that 1 <= d1 <= d2 <= len(weights) <= 50000, and for every i with 0 <= i < len(weights), 1 <= weights[i] <= 500. -/
theorem spec_13
    (weights : Slice Std.I64) (d1 d2 : Std.I64)
    (hd1_pos : 1 ≤ d1.val)
    (hd12 : d1.val ≤ d2.val)
    (hd2_len : d2.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r1 r2 : Std.I64)
    (hr1 : ship_within_days weights d1 = ok r1)
    (hr2 : ship_within_days weights d2 = ok r2) :
    r2.val ≤ r1.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (weights : Slice Std.I64) (d1 d2 : Std.I64)
    (hd1_pos : 1 ≤ d1.val)
    (hd12 : d1.val ≤ d2.val)
    (hd2_len : d2.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (r1 r2 : Std.I64)
    (hr1 : ship_within_days weights d1 = ok r1)
    (hr2 : ship_within_days weights d2 = ok r2), r2.val ≤ r1.val) := by
  sorry

/-- Whenever ship_within_days(weights, days) returns r and ship_within_days(rev, days) returns r_rev, we have r = r_rev.
  Preconditions: For every weights and days satisfying 1 <= days <= len(weights) <= 50000 and every weights[i] in [1,500]; let rev be the array of length len(weights) with rev[i] = weights[len(weights)-1-i] for 0 <= i < len(weights). -/
theorem spec_14
    (weights weights_rev : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (hrev : weights_rev.val = weights.val.reverse)
    (r r_rev : Std.I64)
    (hr : ship_within_days weights days = ok r)
    (hr_rev : ship_within_days weights_rev days = ok r_rev) :
    r = r_rev := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (weights weights_rev : Slice Std.I64) (days : Std.I64)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (hrev : weights_rev.val = weights.val.reverse)
    (r r_rev : Std.I64)
    (hr : ship_within_days weights days = ok r)
    (hr_rev : ship_within_days weights_rev days = ok r_rev), r = r_rev) := by
  sorry

/-- Whenever ship_within_days(weights, days) returns r and ship_within_days(weights2, days) returns r2, we have r <= r2.
  Preconditions: For every two arrays weights and weights2 of the same length n with 1 <= days <= n <= 50000, all entries of weights and weights2 in [1,500], and weights[i] <= weights2[i] for every i with 0 <= i < n. -/
theorem spec_15
    (weights weights2 : Slice Std.I64) (days : Std.I64)
    (hlen2 : weights2.val.length = weights.val.length)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (hw2 : ∀ (i : ℕ) (hi : i < weights2.val.length),
      1 ≤ (weights2.val[i]).val ∧ (weights2.val[i]).val ≤ 500)
    (hle : ∀ (i : ℕ) (hi : i < weights.val.length) (hi2 : i < weights2.val.length),
      (weights.val[i]).val ≤ (weights2.val[i]).val)
    (r r2 : Std.I64)
    (hr : ship_within_days weights days = ok r)
    (hr2 : ship_within_days weights2 days = ok r2) :
    r.val ≤ r2.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (weights weights2 : Slice Std.I64) (days : Std.I64)
    (hlen2 : weights2.val.length = weights.val.length)
    (hdays_pos : 1 ≤ days.val)
    (hdays_len : days.val ≤ (weights.val.length : ℤ))
    (hlen : weights.val.length ≤ 50000)
    (hw : ∀ (i : ℕ) (hi : i < weights.val.length),
      1 ≤ (weights.val[i]).val ∧ (weights.val[i]).val ≤ 500)
    (hw2 : ∀ (i : ℕ) (hi : i < weights2.val.length),
      1 ≤ (weights2.val[i]).val ∧ (weights2.val[i]).val ≤ 500)
    (hle : ∀ (i : ℕ) (hi : i < weights.val.length) (hi2 : i < weights2.val.length),
      (weights.val[i]).val ≤ (weights2.val[i]).val)
    (r r2 : Std.I64)
    (hr : ship_within_days weights days = ok r)
    (hr2 : ship_within_days weights2 days = ok r2), r.val ≤ r2.val) := by
  sorry

end AegisSpec.ShipWithinDays
