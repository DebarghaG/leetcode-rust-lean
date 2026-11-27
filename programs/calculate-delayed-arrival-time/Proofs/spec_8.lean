import Aegis.FindDelayedArrivalTime.Code.Funs

/-
Proof of `AegisSpec.FindDelayedArrivalTime.spec_8` (calculate-delayed-arrival-time).
Contributor: by-eureka
-/

open Aeneas Aeneas.Std Result
open Aegis.FindDelayedArrivalTime (find_delayed_arrival_time)

/-!
# Specifications for `find_delayed_arrival_time`

The extracted function is

```
def find_delayed_arrival_time (arrivalTime : Std.I64) (delayedTime : Std.I64) : Result Std.I64 := do
  let i ← arrivalTime + delayedTime
  i % 24#i64
```

i.e. it performs a *checked* 64-bit addition followed by a *checked* remainder by `24`.
Both operations are total (return `ok`) precisely when no overflow / division-by-zero
occurs, so "the function returns `r`" is rendered as `f a d = ok r` and "does not fail"
as `∃ r, f a d = ok r`.

Scalar values are viewed as mathematical integers through `x.val : ℤ`; the arithmetic in
the statements below is therefore ordinary integer arithmetic (as the task requires),
not 64-bit arithmetic.
-/

namespace AegisSpec.FindDelayedArrivalTime

/-- Placeholder so the template has a declared theorem; the draft adds the specifications. -/
theorem draft_placeholder : True := by
  sorry

/-- **spec_S1 (MAIN)** [functional]

Under `1 ≤ arrivalTime < 24` and `1 ≤ delayedTime ≤ 24` the function returns a result `r`
without failing, and this `r` is the unique integer in `{0, …, 23}` congruent to
`arrivalTime + delayedTime` modulo `24`; equivalently `r = (arrivalTime + delayedTime) % 24`
with the remainder taken in `{0, …, 23}`. -/
theorem spec_S1 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24) :
    ∃ r, find_delayed_arrival_time arrivalTime delayedTime = ok r ∧
      0 ≤ r.val ∧ r.val < 24 ∧
      r.val = (arrivalTime.val + delayedTime.val) % 24 ∧
      (24 : ℤ) ∣ r.val - (arrivalTime.val + delayedTime.val) ∧
      (∀ s : ℤ, 0 ≤ s → s < 24 →
        (24 : ℤ) ∣ s - (arrivalTime.val + delayedTime.val) → s = r.val) := by
  sorry

/-- **spec_S2** [no_failure]

On the prescribed inputs the function returns a result: it does not fail, panic, overflow,
or go out of bounds. -/
theorem spec_S2 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24) :
    ∃ r, find_delayed_arrival_time arrivalTime delayedTime = ok r := by
  sorry

/-- **spec_S3** [bounds]

Whenever the function returns `r`, one has `0 ≤ r < 24`. -/
theorem spec_S3 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24) :
    ∀ r, find_delayed_arrival_time arrivalTime delayedTime = ok r → 0 ≤ r.val ∧ r.val < 24 := by
  sorry

/-- **spec_S4** [relational]

Whenever the function returns `r`, `24` divides `r - (arrivalTime + delayedTime)`, i.e. `r`
and `arrivalTime + delayedTime` are congruent modulo `24`. -/
theorem spec_S4 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24) :
    ∀ r, find_delayed_arrival_time arrivalTime delayedTime = ok r →
      (24 : ℤ) ∣ r.val - (arrivalTime.val + delayedTime.val) := by
  sorry

/-- **spec_S5** [edge]

If `arrivalTime + delayedTime < 24`, the function returns `r` with `r = arrivalTime + delayedTime`. -/
theorem spec_S5 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24)
    (h_sum_lt : arrivalTime.val + delayedTime.val < 24) :
    ∃ r, find_delayed_arrival_time arrivalTime delayedTime = ok r ∧
      r.val = arrivalTime.val + delayedTime.val := by
  sorry

/-- **spec_S6** [edge]

If `arrivalTime + delayedTime = 24`, the function returns `r = 0`. -/
theorem spec_S6 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24)
    (h_sum_eq : arrivalTime.val + delayedTime.val = 24) :
    ∃ r, find_delayed_arrival_time arrivalTime delayedTime = ok r ∧ r.val = 0 := by
  sorry

/-- **spec_S7** [edge]

If `arrivalTime + delayedTime > 24`, the function returns `r = arrivalTime + delayedTime - 24`. -/
theorem spec_S7 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24)
    (h_sum_gt : 24 < arrivalTime.val + delayedTime.val) :
    ∃ r, find_delayed_arrival_time arrivalTime delayedTime = ok r ∧
      r.val = arrivalTime.val + delayedTime.val - 24 := by
  sorry

/-- **spec_S8** [relational]

Whenever the function returns `r`, `r = 0` if and only if `arrivalTime + delayedTime = 24`. -/
theorem spec_8 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24) :
    ∀ r, find_delayed_arrival_time arrivalTime delayedTime = ok r →
      (r.val = 0 ↔ arrivalTime.val + delayedTime.val = 24) := by
  /- The computation returns `r` with `r.val = (arrivalTime.val + delayedTime.val).tmod 24`.
  Since `1 ≤ arrivalTime < 24` and `1 ≤ delayedTime ≤ 24`, the sum `t` satisfies `2 ≤ t ≤ 47`,
  and the only multiple of `24` in that range is `24` itself. -/
  have hs : find_delayed_arrival_time arrivalTime delayedTime ⦃ fun r =>
      (r.val = 0 ↔ arrivalTime.val + delayedTime.val = 24) ⦄ := by
    simp only [Aegis.FindDelayedArrivalTime.find_delayed_arrival_time]
    step
    step
    rw [r_post, i_post]
    have h0 : (0:ℤ) ≤ arrivalTime.val + delayedTime.val := by omega
    have h1 : arrivalTime.val + delayedTime.val < 48 := by omega
    rw [Int.tmod_eq_emod_of_nonneg h0]
    constructor
    · intro h
      have hd : (24:ℤ) ∣ arrivalTime.val + delayedTime.val := Int.dvd_of_emod_eq_zero h
      obtain ⟨k, hk⟩ := hd
      omega
    · intro h
      rw [h]
      simp
  intro r hr
  rw [hr] at hs
  simpa [Aeneas.Std.WP.spec_ok] using hs

/-- **spec_S9** [invariance]

Whenever the function returns `r`, `r = arrivalTime` if and only if `delayedTime = 24`. -/
theorem spec_S9 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24) :
    ∀ r, find_delayed_arrival_time arrivalTime delayedTime = ok r →
      (r.val = arrivalTime.val ↔ delayedTime.val = 24) := by
  sorry

/-- **spec_S10** [relational]

Whenever the function returns `r`, `r < arrivalTime + delayedTime` if and only if
`arrivalTime + delayedTime ≥ 24`. -/
theorem spec_S10 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24) :
    ∀ r, find_delayed_arrival_time arrivalTime delayedTime = ok r →
      (r.val < arrivalTime.val + delayedTime.val ↔ 24 ≤ arrivalTime.val + delayedTime.val) := by
  sorry

end AegisSpec.FindDelayedArrivalTime
