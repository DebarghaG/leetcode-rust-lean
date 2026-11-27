import Aegis.MaxScoreSightseeingPair.Code.Funs

/-!
# Specifications of `Aegis.MaxScoreSightseeingPair.max_score_sightseeing_pair`

LeetCode problem `best-sightseeing-pair`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxScoreSightseeingPair

  namespace AegisSpec.MaxScoreSightseeingPair

  /-- Whenever the function returns a result r, r is the maximum of the set { values[i] + values[j] + i - j | 0 <= i < j < len(values) }. Equivalently, for every i and j with 0 <= i < j < len(values), values[i] + values[j] + i - j <= r, and there exist i and j with 0 <= i < j < len(values) such that values[i] + values[j] + i - j = r.
    Preconditions: len(values) >= 2 and len(values) <= 50000, and for every i with 0 <= i < len(values), 1 <= values[i] <= 1000. All indices are 0-based. -/
  theorem spec_1 (values : Slice Std.I64)
      (hlen_lo : 2 ≤ values.val.length) (hlen_hi : values.val.length ≤ 50000)
      (hval : ∀ (i : ℕ) (hi : i < values.val.length),
        1 ≤ (values.val[i]'hi).val ∧ (values.val[i]'hi).val ≤ 1000) :
      ∀ r, max_score_sightseeing_pair values = ok r →
        (∀ (i j : ℕ) (hij : i < j) (hj : j < values.val.length),
          (values.val[i]).val + (values.val[j]).val + (i : ℤ) - (j : ℤ) ≤ r) ∧
        (∃ (i j : ℕ) (_hij : i < j) (_hj : j < values.val.length),
          (values.val[i]).val + (values.val[j]).val + (i : ℤ) - (j : ℤ) = r) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (values : Slice Std.I64)
        (hlen_lo : 2 ≤ values.val.length) (hlen_hi : values.val.length ≤ 50000)
        (hval : ∀ (i : ℕ) (hi : i < values.val.length),
          1 ≤ (values.val[i]'hi).val ∧ (values.val[i]'hi).val ≤ 1000), ∀ r, max_score_sightseeing_pair values = ok r →
          (∀ (i j : ℕ) (hij : i < j) (hj : j < values.val.length),
            (values.val[i]).val + (values.val[j]).val + (i : ℤ) - (j : ℤ) ≤ r) ∧
          (∃ (i j : ℕ) (_hij : i < j) (_hj : j < values.val.length),
            (values.val[i]).val + (values.val[j]).val + (i : ℤ) - (j : ℤ) = r)) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not panic, access out of bounds, or overflow.
    Preconditions: len(values) >= 2 and len(values) <= 50000, and for every i with 0 <= i < len(values), 1 <= values[i] <= 1000. -/
  theorem spec_2 (values : Slice Std.I64)
      (hlen_lo : 2 ≤ values.val.length) (hlen_hi : values.val.length ≤ 50000)
      (hval : ∀ (i : ℕ) (hi : i < values.val.length),
        1 ≤ (values.val[i]'hi).val ∧ (values.val[i]'hi).val ≤ 1000) :
      ∃ r, max_score_sightseeing_pair values = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (values : Slice Std.I64)
        (hlen_lo : 2 ≤ values.val.length) (hlen_hi : values.val.length ≤ 50000)
        (hval : ∀ (i : ℕ) (hi : i < values.val.length),
          1 ≤ (values.val[i]'hi).val ∧ (values.val[i]'hi).val ≤ 1000), ∃ r, max_score_sightseeing_pair values = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < j < len(values), values[i] + values[j] + i - j <= r.
    Preconditions: len(values) >= 2 and len(values) <= 50000, and for every i with 0 <= i < len(values), 1 <= values[i] <= 1000. -/
  theorem spec_3 (values : Slice Std.I64)
      (hlen_lo : 2 ≤ values.val.length) (hlen_hi : values.val.length ≤ 50000)
      (hval : ∀ (i : ℕ) (hi : i < values.val.length),
        1 ≤ (values.val[i]'hi).val ∧ (values.val[i]'hi).val ≤ 1000) :
      ∀ r, max_score_sightseeing_pair values = ok r →
        ∀ (i j : ℕ) (hij : i < j) (hj : j < values.val.length),
          (values.val[i]).val + (values.val[j]).val + (i : ℤ) - (j : ℤ) ≤ r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (values : Slice Std.I64)
        (hlen_lo : 2 ≤ values.val.length) (hlen_hi : values.val.length ≤ 50000)
        (hval : ∀ (i : ℕ) (hi : i < values.val.length),
          1 ≤ (values.val[i]'hi).val ∧ (values.val[i]'hi).val ≤ 1000), ∀ r, max_score_sightseeing_pair values = ok r →
          ∀ (i j : ℕ) (hij : i < j) (hj : j < values.val.length),
            (values.val[i]).val + (values.val[j]).val + (i : ℤ) - (j : ℤ) ≤ r) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices i and j with 0 <= i < j < len(values) such that r = values[i] + values[j] + i - j.
    Preconditions: len(values) >= 2 and len(values) <= 50000, and for every i with 0 <= i < len(values), 1 <= values[i] <= 1000. -/
  theorem spec_4 (values : Slice Std.I64)
      (hlen_lo : 2 ≤ values.val.length) (hlen_hi : values.val.length ≤ 50000)
      (hval : ∀ (i : ℕ) (hi : i < values.val.length),
        1 ≤ (values.val[i]'hi).val ∧ (values.val[i]'hi).val ≤ 1000) :
      ∀ r, max_score_sightseeing_pair values = ok r →
        ∃ (i j : ℕ) (_hij : i < j) (_hj : j < values.val.length),
          r = (values.val[i]).val + (values.val[j]).val + (i : ℤ) - (j : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (values : Slice Std.I64)
        (hlen_lo : 2 ≤ values.val.length) (hlen_hi : values.val.length ≤ 50000)
        (hval : ∀ (i : ℕ) (hi : i < values.val.length),
          1 ≤ (values.val[i]'hi).val ∧ (values.val[i]'hi).val ≤ 1000), ∀ r, max_score_sightseeing_pair values = ok r →
          ∃ (i j : ℕ) (_hij : i < j) (_hj : j < values.val.length),
            r = (values.val[i]).val + (values.val[j]).val + (i : ℤ) - (j : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r is the least integer upper bound on the set of pair scores: for every i and j with 0 <= i < j < len(values), values[i] + values[j] + i - j <= r; and for every integer B, if values[i] + values[j] + i - j <= B for every i and j with 0 <= i < j < len(values), then r <= B.
    Preconditions: len(values) >= 2 and len(values) <= 50000, and for every i with 0 <= i < len(values), 1 <= values[i] <= 1000. All indices are 0-based. -/
  theorem spec_5 (values : Slice Std.I64)
      (hlen_lo : 2 ≤ values.val.length) (hlen_hi : values.val.length ≤ 50000)
      (hval : ∀ (i : ℕ) (hi : i < values.val.length),
        1 ≤ (values.val[i]'hi).val ∧ (values.val[i]'hi).val ≤ 1000) :
      ∀ r, max_score_sightseeing_pair values = ok r →
        (∀ (i j : ℕ) (hij : i < j) (hj : j < values.val.length),
          (values.val[i]).val + (values.val[j]).val + (i : ℤ) - (j : ℤ) ≤ r) ∧
        (∀ B : ℤ,
          (∀ (i j : ℕ) (hij : i < j) (hj : j < values.val.length),
            (values.val[i]).val + (values.val[j]).val + (i : ℤ) - (j : ℤ) ≤ B) → r ≤ B) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (values : Slice Std.I64)
        (hlen_lo : 2 ≤ values.val.length) (hlen_hi : values.val.length ≤ 50000)
        (hval : ∀ (i : ℕ) (hi : i < values.val.length),
          1 ≤ (values.val[i]'hi).val ∧ (values.val[i]'hi).val ≤ 1000), ∀ r, max_score_sightseeing_pair values = ok r →
          (∀ (i j : ℕ) (hij : i < j) (hj : j < values.val.length),
            (values.val[i]).val + (values.val[j]).val + (i : ℤ) - (j : ℤ) ≤ r) ∧
          (∀ B : ℤ,
            (∀ (i j : ℕ) (hij : i < j) (hj : j < values.val.length),
              (values.val[i]).val + (values.val[j]).val + (i : ℤ) - (j : ℤ) ≤ B) → r ≤ B)) := by
    sorry

  /-- Whenever the function returns a result r, r <= 2 * M - 1, where M = max { values[i] | 0 <= i < len(values) }.
    Preconditions: len(values) >= 2 and len(values) <= 50000, and for every i with 0 <= i < len(values), 1 <= values[i] <= 1000. -/
  theorem spec_6 (values : Slice Std.I64)
      (hlen_lo : 2 ≤ values.val.length) (hlen_hi : values.val.length ≤ 50000)
      (hval : ∀ (i : ℕ) (hi : i < values.val.length),
        1 ≤ (values.val[i]'hi).val ∧ (values.val[i]'hi).val ≤ 1000) :
      ∀ r, max_score_sightseeing_pair values = ok r → ∀ M : ℤ,
        (∀ (i : ℕ) (hi : i < values.val.length), (values.val[i]'hi).val ≤ M) →
        (∃ (i : ℕ) (hi : i < values.val.length), (values.val[i]'hi).val = M) →
        r ≤ 2 * M - 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (values : Slice Std.I64)
        (hlen_lo : 2 ≤ values.val.length) (hlen_hi : values.val.length ≤ 50000)
        (hval : ∀ (i : ℕ) (hi : i < values.val.length),
          1 ≤ (values.val[i]'hi).val ∧ (values.val[i]'hi).val ≤ 1000), ∀ r, max_score_sightseeing_pair values = ok r → ∀ M : ℤ,
          (∀ (i : ℕ) (hi : i < values.val.length), (values.val[i]'hi).val ≤ M) →
          (∃ (i : ℕ) (hi : i < values.val.length), (values.val[i]'hi).val = M) →
          r ≤ 2 * M - 1) := by
    sorry

  /-- Whenever the function returns a result r, r = values[0] + values[1] - 1.
    Preconditions: len(values) = 2, and 1 <= values[0] <= 1000 and 1 <= values[1] <= 1000. -/
  theorem spec_7 (values : Slice Std.I64)
      (hlen : values.val.length = 2)
      (hval0 : 1 ≤ (values.val[0]).val ∧ (values.val[0]).val ≤ 1000)
      (hval1 : 1 ≤ (values.val[1]).val ∧ (values.val[1]).val ≤ 1000) :
      ∀ r, max_score_sightseeing_pair values = ok r →
        r = (values.val[0]).val + (values.val[1]).val - 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (values : Slice Std.I64)
        (hlen : values.val.length = 2)
        (hval0 : 1 ≤ (values.val[0]).val ∧ (values.val[0]).val ≤ 1000)
        (hval1 : 1 ≤ (values.val[1]).val ∧ (values.val[1]).val ≤ 1000), ∀ r, max_score_sightseeing_pair values = ok r →
          r = (values.val[0]).val + (values.val[1]).val - 1) := by
    sorry

  /-- Whenever the function returns a result r, r = values[len(values)-2] + values[len(values)-1] - 1.
    Preconditions: len(values) >= 2 and len(values) <= 50000, and for every i with 0 <= i < len(values), 1 <= values[i] <= 1000, and for every i with 0 <= i < len(values) - 1, values[i] <= values[i+1]. -/
  theorem spec_8 (values : Slice Std.I64)
      (hlen_lo : 2 ≤ values.val.length) (hlen_hi : values.val.length ≤ 50000)
      (hval : ∀ (i : ℕ) (hi : i < values.val.length),
        1 ≤ (values.val[i]'hi).val ∧ (values.val[i]'hi).val ≤ 1000)
      (hsorted : ∀ (i : ℕ) (hi : i + 1 < values.val.length),
        (values.val[i]'(by omega)).val ≤ (values.val[i + 1]'hi).val) :
      ∀ r, max_score_sightseeing_pair values = ok r →
        r = (values.val[values.val.length - 2]).val
            + (values.val[values.val.length - 1]).val - 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (values : Slice Std.I64)
        (hlen_lo : 2 ≤ values.val.length) (hlen_hi : values.val.length ≤ 50000)
        (hval : ∀ (i : ℕ) (hi : i < values.val.length),
          1 ≤ (values.val[i]'hi).val ∧ (values.val[i]'hi).val ≤ 1000)
        (hsorted : ∀ (i : ℕ) (hi : i + 1 < values.val.length),
          (values.val[i]'(by omega)).val ≤ (values.val[i + 1]'hi).val), ∀ r, max_score_sightseeing_pair values = ok r →
          r = (values.val[values.val.length - 2]).val
              + (values.val[values.val.length - 1]).val - 1) := by
    sorry

  /-- For every array values satisfying the preconditions, define rev by len(rev) = len(values) and rev[k] = values[len(values)-1-k] for every k with 0 <= k < len(values). If the function returns r on values and returns r_rev on rev, then r_rev = r.
    Preconditions: len(values) >= 2 and len(values) <= 50000, and for every i with 0 <= i < len(values), 1 <= values[i] <= 1000. -/
  theorem spec_9 (values rev : Slice Std.I64)
      (hlen_lo : 2 ≤ values.val.length) (hlen_hi : values.val.length ≤ 50000)
      (hval : ∀ (i : ℕ) (hi : i < values.val.length),
        1 ≤ (values.val[i]'hi).val ∧ (values.val[i]'hi).val ≤ 1000)
      (hrev_len : rev.val.length = values.val.length)
      (hrev : ∀ (k : ℕ) (hk : k < values.val.length),
        (rev.val[k]'(by rw [hrev_len]; exact hk)).val
          = (values.val[values.val.length - 1 - k]'(by omega)).val) :
      ∀ r r_rev, max_score_sightseeing_pair values = ok r →
        max_score_sightseeing_pair rev = ok r_rev → r_rev = r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (values rev : Slice Std.I64)
        (hlen_lo : 2 ≤ values.val.length) (hlen_hi : values.val.length ≤ 50000)
        (hval : ∀ (i : ℕ) (hi : i < values.val.length),
          1 ≤ (values.val[i]'hi).val ∧ (values.val[i]'hi).val ≤ 1000)
        (hrev_len : rev.val.length = values.val.length)
        (hrev : ∀ (k : ℕ) (hk : k < values.val.length),
          (rev.val[k]'(by rw [hrev_len]; exact hk)).val
            = (values.val[values.val.length - 1 - k]'(by omega)).val), ∀ r r_rev, max_score_sightseeing_pair values = ok r →
          max_score_sightseeing_pair rev = ok r_rev → r_rev = r) := by
    sorry

  /-- Define shifted by len(shifted) = len(values) and shifted[i] = values[i] + c for every i with 0 <= i < len(values). If the function returns r on values and returns r_c on shifted, then r_c = r + 2*c.
    Preconditions: len(values) >= 2 and len(values) <= 50000, and for every i with 0 <= i < len(values), 1 <= values[i] <= 1000. Also c is an integer such that for every i with 0 <= i < len(values), 1 <= values[i] + c <= 1000. -/
  theorem spec_10 (values shifted : Slice Std.I64) (c : ℤ)
      (hlen_lo : 2 ≤ values.val.length) (hlen_hi : values.val.length ≤ 50000)
      (hval : ∀ (i : ℕ) (hi : i < values.val.length),
        1 ≤ (values.val[i]'hi).val ∧ (values.val[i]'hi).val ≤ 1000)
      (hc : ∀ (i : ℕ) (hi : i < values.val.length),
        1 ≤ (values.val[i]'hi).val + c ∧ (values.val[i]'hi).val + c ≤ 1000)
      (hshifted_len : shifted.val.length = values.val.length)
      (hshifted : ∀ (k : ℕ) (hk : k < values.val.length),
        (shifted.val[k]'(by rw [hshifted_len]; exact hk)).val
          = (values.val[k]'hk).val + c) :
      ∀ r r_c, max_score_sightseeing_pair values = ok r →
        max_score_sightseeing_pair shifted = ok r_c → r_c = r + 2 * c := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (values shifted : Slice Std.I64) (c : ℤ)
        (hlen_lo : 2 ≤ values.val.length) (hlen_hi : values.val.length ≤ 50000)
        (hval : ∀ (i : ℕ) (hi : i < values.val.length),
          1 ≤ (values.val[i]'hi).val ∧ (values.val[i]'hi).val ≤ 1000)
        (hc : ∀ (i : ℕ) (hi : i < values.val.length),
          1 ≤ (values.val[i]'hi).val + c ∧ (values.val[i]'hi).val + c ≤ 1000)
        (hshifted_len : shifted.val.length = values.val.length)
        (hshifted : ∀ (k : ℕ) (hk : k < values.val.length),
          (shifted.val[k]'(by rw [hshifted_len]; exact hk)).val
            = (values.val[k]'hk).val + c), ∀ r r_c, max_score_sightseeing_pair values = ok r →
          max_score_sightseeing_pair shifted = ok r_c → r_c = r + 2 * c) := by
    sorry

  end AegisSpec.MaxScoreSightseeingPair
