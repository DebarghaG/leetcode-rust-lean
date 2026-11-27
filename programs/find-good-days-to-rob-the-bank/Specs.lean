import Aegis.GoodDaysToRobBank.Code.Funs

/-!
# Specifications of `Aegis.GoodDaysToRobBank.good_days_to_rob_bank`

LeetCode problem `find-good-days-to-rob-the-bank`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.GoodDaysToRobBank

  def valAt (security : Slice I64) (i : ℤ) : ℤ :=
    (security.val.getD i.toNat (default : I64)).val

  def OccursIn (r : alloc.vec.Vec I64) (d : ℤ) : Prop :=
    ∃ (j : ℕ) (h : j < r.val.length), (r.val[j]'h).val = d

  def NoRepeats (r : alloc.vec.Vec I64) : Prop :=
    ∀ (j k : ℕ) (hj : j < r.val.length) (hk : k < r.val.length),
      (r.val[j]'hj).val = (r.val[k]'hk).val → j = k

  def GoodDay (security : Slice I64) (time : I64) (d : ℤ) : Prop :=
    0 ≤ d ∧
    d < (security.val.length : ℤ) ∧
    time.val ≤ d ∧
    d + time.val < (security.val.length : ℤ) ∧
    (∀ k : ℕ, (k : ℤ) < time.val →
      valAt security (d - time.val + (k : ℤ)) ≥ valAt security (d - time.val + (k : ℤ) + 1)) ∧
    (∀ k : ℕ, (k : ℤ) < time.val →
      valAt security (d + (k : ℤ)) ≤ valAt security (d + (k : ℤ) + 1))

  /-- Whenever the function returns a result r, r has no repeated entries, and for every integer d the following are equivalent: (1) there exists j with 0 <= j < len(r) and r[j] = d; (2) 0 <= d < len(security), time <= d, d + time < len(security), for every k with 0 <= k < time, security[d - time + k] >= security[d - time + k + 1], and for every k with 0 <= k < time, security[d + k] <= security[d + k + 1]. The order of the entries of r is irrelevant.
    Preconditions: security is a slice of 64-bit integers with 1 <= len(security) <= 10^5 and 0 <= security[t] <= 10^5 for every 0 <= t < len(security); time is a 64-bit integer with 0 <= time <= 10^5. -/
  theorem spec_1 (security : Slice I64) (time : I64)
      (hlen_ge : 1 ≤ security.val.length)
      (hlen_le : security.val.length ≤ 100000)
      (hsec : ∀ (t : ℕ) (ht : t < security.val.length),
        0 ≤ (security.val[t]'ht).val ∧ (security.val[t]'ht).val ≤ 100000)
      (htime_ge : 0 ≤ time.val)
      (htime_le : time.val ≤ 100000) :
      ∀ r, Aegis.GoodDaysToRobBank.good_days_to_rob_bank security time = ok r →
        NoRepeats r ∧ (∀ d : ℤ, OccursIn r d ↔ GoodDay security time d) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (security : Slice I64) (time : I64)
        (hlen_ge : 1 ≤ security.val.length)
        (hlen_le : security.val.length ≤ 100000)
        (hsec : ∀ (t : ℕ) (ht : t < security.val.length),
          0 ≤ (security.val[t]'ht).val ∧ (security.val[t]'ht).val ≤ 100000)
        (htime_ge : 0 ≤ time.val)
        (htime_le : time.val ≤ 100000), ∀ r, Aegis.GoodDaysToRobBank.good_days_to_rob_bank security time = ok r →
          NoRepeats r ∧ (∀ d : ℤ, OccursIn r d ↔ GoodDay security time d)) := by
    sorry

  /-- The function returns a result r (it does not fail) for every security and time satisfying the preconditions.
    Preconditions: security is a slice of 64-bit integers with 1 <= len(security) <= 10^5 and 0 <= security[t] <= 10^5 for every 0 <= t < len(security); time is a 64-bit integer with 0 <= time <= 10^5. -/
  theorem spec_2 (security : Slice I64) (time : I64)
      (hlen_ge : 1 ≤ security.val.length)
      (hlen_le : security.val.length ≤ 100000)
      (hsec : ∀ (t : ℕ) (ht : t < security.val.length),
        0 ≤ (security.val[t]'ht).val ∧ (security.val[t]'ht).val ≤ 100000)
      (htime_ge : 0 ≤ time.val)
      (htime_le : time.val ≤ 100000) :
      ∃ r, Aegis.GoodDaysToRobBank.good_days_to_rob_bank security time = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (security : Slice I64) (time : I64)
        (hlen_ge : 1 ≤ security.val.length)
        (hlen_le : security.val.length ≤ 100000)
        (hsec : ∀ (t : ℕ) (ht : t < security.val.length),
          0 ≤ (security.val[t]'ht).val ∧ (security.val[t]'ht).val ≤ 100000)
        (htime_ge : 0 ≤ time.val)
        (htime_le : time.val ≤ 100000), ∃ r, Aegis.GoodDaysToRobBank.good_days_to_rob_bank security time = ok r) := by
    sorry

  /-- Whenever the function returns a result r, every entry of r is a good day: for every j with 0 <= j < len(r), if d = r[j], then 0 <= d < len(security), time <= d, d + time < len(security), for every k with 0 <= k < time, security[d - time + k] >= security[d - time + k + 1], and for every k with 0 <= k < time, security[d + k] <= security[d + k + 1].
    Preconditions: security is a slice of 64-bit integers with 1 <= len(security) <= 10^5 and 0 <= security[t] <= 10^5 for every 0 <= t < len(security); time is a 64-bit integer with 0 <= time <= 10^5. -/
  theorem spec_3 (security : Slice I64) (time : I64)
      (hlen_ge : 1 ≤ security.val.length)
      (hlen_le : security.val.length ≤ 100000)
      (hsec : ∀ (t : ℕ) (ht : t < security.val.length),
        0 ≤ (security.val[t]'ht).val ∧ (security.val[t]'ht).val ≤ 100000)
      (htime_ge : 0 ≤ time.val)
      (htime_le : time.val ≤ 100000) :
      ∀ r, Aegis.GoodDaysToRobBank.good_days_to_rob_bank security time = ok r →
        ∀ (j : ℕ) (hj : j < r.val.length), GoodDay security time (r.val[j]'hj).val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (security : Slice I64) (time : I64)
        (hlen_ge : 1 ≤ security.val.length)
        (hlen_le : security.val.length ≤ 100000)
        (hsec : ∀ (t : ℕ) (ht : t < security.val.length),
          0 ≤ (security.val[t]'ht).val ∧ (security.val[t]'ht).val ≤ 100000)
        (htime_ge : 0 ≤ time.val)
        (htime_le : time.val ≤ 100000), ∀ r, Aegis.GoodDaysToRobBank.good_days_to_rob_bank security time = ok r →
          ∀ (j : ℕ) (hj : j < r.val.length), GoodDay security time (r.val[j]'hj).val) := by
    sorry

  /-- Whenever the function returns a result r, every good day appears in r: for every integer d, if 0 <= d < len(security), time <= d, d + time < len(security), for every k with 0 <= k < time, security[d - time + k] >= security[d - time + k + 1], and for every k with 0 <= k < time, security[d + k] <= security[d + k + 1], then there exists j with 0 <= j < len(r) and r[j] = d.
    Preconditions: security is a slice of 64-bit integers with 1 <= len(security) <= 10^5 and 0 <= security[t] <= 10^5 for every 0 <= t < len(security); time is a 64-bit integer with 0 <= time <= 10^5. -/
  theorem spec_4 (security : Slice I64) (time : I64)
      (hlen_ge : 1 ≤ security.val.length)
      (hlen_le : security.val.length ≤ 100000)
      (hsec : ∀ (t : ℕ) (ht : t < security.val.length),
        0 ≤ (security.val[t]'ht).val ∧ (security.val[t]'ht).val ≤ 100000)
      (htime_ge : 0 ≤ time.val)
      (htime_le : time.val ≤ 100000) :
      ∀ r, Aegis.GoodDaysToRobBank.good_days_to_rob_bank security time = ok r →
        ∀ d : ℤ, GoodDay security time d → OccursIn r d := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (security : Slice I64) (time : I64)
        (hlen_ge : 1 ≤ security.val.length)
        (hlen_le : security.val.length ≤ 100000)
        (hsec : ∀ (t : ℕ) (ht : t < security.val.length),
          0 ≤ (security.val[t]'ht).val ∧ (security.val[t]'ht).val ≤ 100000)
        (htime_ge : 0 ≤ time.val)
        (htime_le : time.val ≤ 100000), ∀ r, Aegis.GoodDaysToRobBank.good_days_to_rob_bank security time = ok r →
          ∀ d : ℤ, GoodDay security time d → OccursIn r d) := by
    sorry

  /-- Whenever the function returns a result r, r contains no repeated values: for all j and k with 0 <= j < len(r) and 0 <= k < len(r), if r[j] = r[k], then j = k.
    Preconditions: security is a slice of 64-bit integers with 1 <= len(security) <= 10^5 and 0 <= security[t] <= 10^5 for every 0 <= t < len(security); time is a 64-bit integer with 0 <= time <= 10^5. -/
  theorem spec_5 (security : Slice I64) (time : I64)
      (hlen_ge : 1 ≤ security.val.length)
      (hlen_le : security.val.length ≤ 100000)
      (hsec : ∀ (t : ℕ) (ht : t < security.val.length),
        0 ≤ (security.val[t]'ht).val ∧ (security.val[t]'ht).val ≤ 100000)
      (htime_ge : 0 ≤ time.val)
      (htime_le : time.val ≤ 100000) :
      ∀ r, Aegis.GoodDaysToRobBank.good_days_to_rob_bank security time = ok r →
        NoRepeats r := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (security : Slice I64) (time : I64)
        (hlen_ge : 1 ≤ security.val.length)
        (hlen_le : security.val.length ≤ 100000)
        (hsec : ∀ (t : ℕ) (ht : t < security.val.length),
          0 ≤ (security.val[t]'ht).val ∧ (security.val[t]'ht).val ≤ 100000)
        (htime_ge : 0 ≤ time.val)
        (htime_le : time.val ≤ 100000), ∀ r, Aegis.GoodDaysToRobBank.good_days_to_rob_bank security time = ok r →
          NoRepeats r) := by
    sorry

  /-- Whenever the function returns a result r, every entry d of r satisfies time <= d and d + time < len(security). Consequently 0 <= d < len(security), so there are at least time days before d and at least time days after d.
    Preconditions: security is a slice of 64-bit integers with 1 <= len(security) <= 10^5 and 0 <= security[t] <= 10^5 for every 0 <= t < len(security); time is a 64-bit integer with 0 <= time <= 10^5. -/
  theorem spec_6 (security : Slice I64) (time : I64)
      (hlen_ge : 1 ≤ security.val.length)
      (hlen_le : security.val.length ≤ 100000)
      (hsec : ∀ (t : ℕ) (ht : t < security.val.length),
        0 ≤ (security.val[t]'ht).val ∧ (security.val[t]'ht).val ≤ 100000)
      (htime_ge : 0 ≤ time.val)
      (htime_le : time.val ≤ 100000) :
      ∀ r, Aegis.GoodDaysToRobBank.good_days_to_rob_bank security time = ok r →
        ∀ (j : ℕ) (hj : j < r.val.length),
          time.val ≤ (r.val[j]'hj).val ∧
          (r.val[j]'hj).val + time.val < (security.val.length : ℤ) ∧
          0 ≤ (r.val[j]'hj).val ∧
          (r.val[j]'hj).val < (security.val.length : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (security : Slice I64) (time : I64)
        (hlen_ge : 1 ≤ security.val.length)
        (hlen_le : security.val.length ≤ 100000)
        (hsec : ∀ (t : ℕ) (ht : t < security.val.length),
          0 ≤ (security.val[t]'ht).val ∧ (security.val[t]'ht).val ≤ 100000)
        (htime_ge : 0 ≤ time.val)
        (htime_le : time.val ≤ 100000), ∀ r, Aegis.GoodDaysToRobBank.good_days_to_rob_bank security time = ok r →
          ∀ (j : ℕ) (hj : j < r.val.length),
            time.val ≤ (r.val[j]'hj).val ∧
            (r.val[j]'hj).val + time.val < (security.val.length : ℤ) ∧
            0 ≤ (r.val[j]'hj).val ∧
            (r.val[j]'hj).val < (security.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, len(r) <= max(0, len(security) - 2*time).
    Preconditions: security is a slice of 64-bit integers with 1 <= len(security) <= 10^5 and 0 <= security[t] <= 10^5 for every 0 <= t < len(security); time is a 64-bit integer with 0 <= time <= 10^5. -/
  theorem spec_7 (security : Slice I64) (time : I64)
      (hlen_ge : 1 ≤ security.val.length)
      (hlen_le : security.val.length ≤ 100000)
      (hsec : ∀ (t : ℕ) (ht : t < security.val.length),
        0 ≤ (security.val[t]'ht).val ∧ (security.val[t]'ht).val ≤ 100000)
      (htime_ge : 0 ≤ time.val)
      (htime_le : time.val ≤ 100000) :
      ∀ r, Aegis.GoodDaysToRobBank.good_days_to_rob_bank security time = ok r →
        (r.val.length : ℤ) ≤ max 0 ((security.val.length : ℤ) - 2 * time.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (security : Slice I64) (time : I64)
        (hlen_ge : 1 ≤ security.val.length)
        (hlen_le : security.val.length ≤ 100000)
        (hsec : ∀ (t : ℕ) (ht : t < security.val.length),
          0 ≤ (security.val[t]'ht).val ∧ (security.val[t]'ht).val ≤ 100000)
        (htime_ge : 0 ≤ time.val)
        (htime_le : time.val ≤ 100000), ∀ r, Aegis.GoodDaysToRobBank.good_days_to_rob_bank security time = ok r →
          (r.val.length : ℤ) ≤ max 0 ((security.val.length : ℤ) - 2 * time.val)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(r), letting d = r[j], for every integer t with 0 <= t < len(security) and d - time <= t and t <= d + time, we have security[d] <= security[t].
    Preconditions: security is a slice of 64-bit integers with 1 <= len(security) <= 10^5 and 0 <= security[t] <= 10^5 for every 0 <= t < len(security); time is a 64-bit integer with 0 <= time <= 10^5. -/
  theorem spec_8 (security : Slice I64) (time : I64)
      (hlen_ge : 1 ≤ security.val.length)
      (hlen_le : security.val.length ≤ 100000)
      (hsec : ∀ (t : ℕ) (ht : t < security.val.length),
        0 ≤ (security.val[t]'ht).val ∧ (security.val[t]'ht).val ≤ 100000)
      (htime_ge : 0 ≤ time.val)
      (htime_le : time.val ≤ 100000) :
      ∀ r, Aegis.GoodDaysToRobBank.good_days_to_rob_bank security time = ok r →
        ∀ (j : ℕ) (hj : j < r.val.length), ∀ t : ℤ,
          0 ≤ t → t < (security.val.length : ℤ) →
            (r.val[j]'hj).val - time.val ≤ t → t ≤ (r.val[j]'hj).val + time.val →
            valAt security (r.val[j]'hj).val ≤ valAt security t := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (security : Slice I64) (time : I64)
        (hlen_ge : 1 ≤ security.val.length)
        (hlen_le : security.val.length ≤ 100000)
        (hsec : ∀ (t : ℕ) (ht : t < security.val.length),
          0 ≤ (security.val[t]'ht).val ∧ (security.val[t]'ht).val ≤ 100000)
        (htime_ge : 0 ≤ time.val)
        (htime_le : time.val ≤ 100000), ∀ r, Aegis.GoodDaysToRobBank.good_days_to_rob_bank security time = ok r →
          ∀ (j : ℕ) (hj : j < r.val.length), ∀ t : ℤ,
            0 ≤ t → t < (security.val.length : ℤ) →
              (r.val[j]'hj).val - time.val ≤ t → t ≤ (r.val[j]'hj).val + time.val →
              valAt security (r.val[j]'hj).val ≤ valAt security t) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 0 if and only if there is no integer d such that 0 <= d < len(security), time <= d, d + time < len(security), for every k with 0 <= k < time, security[d - time + k] >= security[d - time + k + 1], and for every k with 0 <= k < time, security[d + k] <= security[d + k + 1].
    Preconditions: security is a slice of 64-bit integers with 1 <= len(security) <= 10^5 and 0 <= security[t] <= 10^5 for every 0 <= t < len(security); time is a 64-bit integer with 0 <= time <= 10^5. -/
  theorem spec_9 (security : Slice I64) (time : I64)
      (hlen_ge : 1 ≤ security.val.length)
      (hlen_le : security.val.length ≤ 100000)
      (hsec : ∀ (t : ℕ) (ht : t < security.val.length),
        0 ≤ (security.val[t]'ht).val ∧ (security.val[t]'ht).val ≤ 100000)
      (htime_ge : 0 ≤ time.val)
      (htime_le : time.val ≤ 100000) :
      ∀ r, Aegis.GoodDaysToRobBank.good_days_to_rob_bank security time = ok r →
        (r.val.length = 0 ↔ ¬ ∃ d : ℤ, GoodDay security time d) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (security : Slice I64) (time : I64)
        (hlen_ge : 1 ≤ security.val.length)
        (hlen_le : security.val.length ≤ 100000)
        (hsec : ∀ (t : ℕ) (ht : t < security.val.length),
          0 ≤ (security.val[t]'ht).val ∧ (security.val[t]'ht).val ≤ 100000)
        (htime_ge : 0 ≤ time.val)
        (htime_le : time.val ≤ 100000), ∀ r, Aegis.GoodDaysToRobBank.good_days_to_rob_bank security time = ok r →
          (r.val.length = 0 ↔ ¬ ∃ d : ℤ, GoodDay security time d)) := by
    sorry

  end AegisSpec.GoodDaysToRobBank
