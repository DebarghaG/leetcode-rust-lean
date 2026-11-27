import Aegis.FindDelayedArrivalTime.Code.Funs

/-
Proof of `AegisSpec.FindDelayedArrivalTime.spec_6` (calculate-delayed-arrival-time).
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

/-- Bridge from the Aeneas wp-form `spec m p` to the existential form used in the
specifications below. -/
theorem spec_exists_ok {α : Type} {m : Std.Result α} {p : Std.WP.Post α}
    (h : Std.WP.spec m p) : ∃ r, m = Std.Result.ok r ∧ p r := by
  cases m using Std.Result.cases with
  | ret r => exact ⟨r, rfl, by simpa using h⟩
  | vis i k => simp at h
  | div => simp at h

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
theorem spec_6 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24)
    (h_sum_eq : arrivalTime.val + delayedTime.val = 24) :
    ∃ r, find_delayed_arrival_time arrivalTime delayedTime = ok r ∧ r.val = 0 := by
  have hwp : find_delayed_arrival_time arrivalTime delayedTime ⦃ r => r.val = 0 ⦄ := by
    unfold find_delayed_arrival_time
    step
    step
    rw [r_post]
    have hi : (↑i : ℤ) = 24 := by rw [i_post, h_sum_eq]
    rw [hi]
    norm_num
  obtain ⟨r, hok, hval⟩ := spec_exists_ok hwp
  exact ⟨r, hok, hval⟩

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
theorem spec_S8 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24) :
    ∀ r, find_delayed_arrival_time arrivalTime delayedTime = ok r →
      (r.val = 0 ↔ arrivalTime.val + delayedTime.val = 24) := by
  sorry

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
