import Aegis.CountCompleteDayPairs.Code.Funs

/-!
# Specifications of `Aegis.CountCompleteDayPairs.count_complete_day_pairs`

LeetCode problem `count-pairs-that-form-a-complete-day-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountCompleteDayPairs

  def IsMultipleOf24 (x : Int) : Prop := ∃ k : Int, x = 24 * k

  instance instDecidableIsMultipleOf24 (x : Int) : Decidable (IsMultipleOf24 x) :=
    inferInstanceAs (Decidable ((24 : Int) ∣ x))

  def vals (hours : Slice I64) : List Int := hours.val.map (fun x => x.val)

  def pairCount (l : List Int) : Nat :=
    ((Finset.univ : Finset (Fin l.length × Fin l.length)).filter
      (fun p => p.1 < p.2 ∧ IsMultipleOf24 (l.get p.1 + l.get p.2))).card

  def choose2 (n : Nat) : Nat := n * (n - 1) / 2

  def countMod (l : List Int) (a : Int) : Nat := (l.filter (fun x => x % 24 = a)).length

  def crossPairSum (c : Int → Nat) : Nat :=
    Finset.sum (Finset.range 11) (fun b => c ((b : Int) + 1) * c (24 - ((b : Int) + 1)))

  /-- Let N = len(hours). The function returns a result r and r is exactly the number of index pairs (i,j) such that 0 <= i < j < N and there exists an integer k with hours[i] + hours[j] = 24*k.
    Preconditions: hours is a slice of 64-bit integers with 1 <= len(hours) <= 500000, and for every i with 0 <= i < len(hours), 1 <= hours[i] <= 1000000000. -/
  theorem spec_1 (hours : Slice I64)
      (hlen_lo : 1 ≤ hours.val.length) (hlen_hi : hours.val.length ≤ 500000)
      (hbound : ∀ i : Fin hours.val.length,
        1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000)
      (r : I64) (hr : Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok r) :
      r.val = (pairCount (vals hours) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (hours : Slice I64)
        (hlen_lo : 1 ≤ hours.val.length) (hlen_hi : hours.val.length ≤ 500000)
        (hbound : ∀ i : Fin hours.val.length,
          1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000)
        (r : I64) (hr : Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok r), r.val = (pairCount (vals hours) : Int)) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, overflow, or access out of bounds.
    Preconditions: hours is a slice of 64-bit integers with 1 <= len(hours) <= 500000, and for every i with 0 <= i < len(hours), 1 <= hours[i] <= 1000000000. -/
  theorem spec_2 (hours : Slice I64)
      (hlen_lo : 1 ≤ hours.val.length) (hlen_hi : hours.val.length ≤ 500000)
      (hbound : ∀ i : Fin hours.val.length,
        1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000) :
      ∃ r : I64, Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (hours : Slice I64)
        (hlen_lo : 1 ≤ hours.val.length) (hlen_hi : hours.val.length ≤ 500000)
        (hbound : ∀ i : Fin hours.val.length,
          1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000), ∃ r : I64, Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok r) := by
    sorry

  /-- Let N = len(hours). The function returns a result r and 0 <= r <= N*(N-1)/2.
    Preconditions: hours is a slice of 64-bit integers with 1 <= len(hours) <= 500000, and for every i with 0 <= i < len(hours), 1 <= hours[i] <= 1000000000. -/
  theorem spec_3 (hours : Slice I64)
      (hlen_lo : 1 ≤ hours.val.length) (hlen_hi : hours.val.length ≤ 500000)
      (hbound : ∀ i : Fin hours.val.length,
        1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000) :
      ∃ r : I64, Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok r ∧
        0 ≤ r.val ∧ r.val ≤ (choose2 hours.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (hours : Slice I64)
        (hlen_lo : 1 ≤ hours.val.length) (hlen_hi : hours.val.length ≤ 500000)
        (hbound : ∀ i : Fin hours.val.length,
          1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000), ∃ r : I64, Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok r ∧
          0 ≤ r.val ∧ r.val ≤ (choose2 hours.val.length : Int)) := by
    sorry

  /-- The function returns the result r = 0.
    Preconditions: hours is a slice of 64-bit integers with len(hours) = 1, and 1 <= hours[0] <= 1000000000. -/
  theorem spec_4 (hours : Slice I64)
      (hlen : hours.val.length = 1)
      (hbound : 1 ≤ (hours.val.get ⟨0, by omega⟩).val ∧
        (hours.val.get ⟨0, by omega⟩).val ≤ 1000000000) :
      ∃ r : I64, Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (hours : Slice I64)
        (hlen : hours.val.length = 1)
        (hbound : 1 ≤ (hours.val.get ⟨0, by omega⟩).val ∧
          (hours.val.get ⟨0, by omega⟩).val ≤ 1000000000), ∃ r : I64, Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r, and r = 1 if there exists an integer k with hours[0] + hours[1] = 24*k, and r = 0 otherwise.
    Preconditions: hours is a slice of 64-bit integers with len(hours) = 2, and 1 <= hours[0] <= 1000000000, 1 <= hours[1] <= 1000000000. -/
  theorem spec_5 (hours : Slice I64)
      (hlen : hours.val.length = 2)
      (hbound : ∀ i : Fin hours.val.length,
        1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000) :
      ∃ r : I64, Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok r ∧
        (IsMultipleOf24 ((hours.val.get ⟨0, by omega⟩).val +
            (hours.val.get ⟨1, by omega⟩).val) → r.val = 1) ∧
        (¬ IsMultipleOf24 ((hours.val.get ⟨0, by omega⟩).val +
            (hours.val.get ⟨1, by omega⟩).val) → r.val = 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (hours : Slice I64)
        (hlen : hours.val.length = 2)
        (hbound : ∀ i : Fin hours.val.length,
          1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000), ∃ r : I64, Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok r ∧
          (IsMultipleOf24 ((hours.val.get ⟨0, by omega⟩).val +
              (hours.val.get ⟨1, by omega⟩).val) → r.val = 1) ∧
          (¬ IsMultipleOf24 ((hours.val.get ⟨0, by omega⟩).val +
              (hours.val.get ⟨1, by omega⟩).val) → r.val = 0)) := by
    sorry

  /-- Let N = len(hours). The function returns a result R, and R = N*(N-1)/2 if 2*a is divisible by 24, and R = 0 otherwise.
    Preconditions: hours is a slice of 64-bit integers with 1 <= len(hours) <= 500000, and for every i with 0 <= i < len(hours), 1 <= hours[i] <= 1000000000. Suppose there is an integer a with 0 <= a < 24 such that hours[i] mod 24 = a for every i. -/
  theorem spec_6 (hours : Slice I64)
      (hlen_lo : 1 ≤ hours.val.length) (hlen_hi : hours.val.length ≤ 500000)
      (hbound : ∀ i : Fin hours.val.length,
        1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000)
      (a : Int) (ha_lo : 0 ≤ a) (ha_hi : a < 24)
      (hmod : ∀ i : Fin hours.val.length, (hours.val.get i).val % 24 = a) :
      ∃ R : I64, Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok R ∧
        (IsMultipleOf24 (2 * a) → R.val = (choose2 hours.val.length : Int)) ∧
        (¬ IsMultipleOf24 (2 * a) → R.val = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (hours : Slice I64)
        (hlen_lo : 1 ≤ hours.val.length) (hlen_hi : hours.val.length ≤ 500000)
        (hbound : ∀ i : Fin hours.val.length,
          1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000)
        (a : Int) (ha_lo : 0 ≤ a) (ha_hi : a < 24)
        (hmod : ∀ i : Fin hours.val.length, (hours.val.get i).val % 24 = a), ∃ R : I64, Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok R ∧
          (IsMultipleOf24 (2 * a) → R.val = (choose2 hours.val.length : Int)) ∧
          (¬ IsMultipleOf24 (2 * a) → R.val = 0)) := by
    sorry

  /-- Let N = len(hours). The function returns a result r, and r = 0 if and only if for every pair (i,j) with 0 <= i < j < N, there is no integer k with hours[i] + hours[j] = 24*k.
    Preconditions: hours is a slice of 64-bit integers with 1 <= len(hours) <= 500000, and for every i with 0 <= i < len(hours), 1 <= hours[i] <= 1000000000. -/
  theorem spec_7 (hours : Slice I64)
      (hlen_lo : 1 ≤ hours.val.length) (hlen_hi : hours.val.length ≤ 500000)
      (hbound : ∀ i : Fin hours.val.length,
        1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000) :
      ∃ r : I64, Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok r ∧
        (r.val = 0 ↔ ∀ (i j : Fin hours.val.length), i < j →
          ¬ IsMultipleOf24 ((hours.val.get i).val + (hours.val.get j).val)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (hours : Slice I64)
        (hlen_lo : 1 ≤ hours.val.length) (hlen_hi : hours.val.length ≤ 500000)
        (hbound : ∀ i : Fin hours.val.length,
          1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000), ∃ r : I64, Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok r ∧
          (r.val = 0 ↔ ∀ (i j : Fin hours.val.length), i < j →
            ¬ IsMultipleOf24 ((hours.val.get i).val + (hours.val.get j).val))) := by
    sorry

  /-- Let N = len(hours). For each a with 0 <= a < 24, let c_a be the number of indices i with 0 <= i < N and hours[i] mod 24 = a. The function returns a result R, and R = c_0*(c_0-1)/2 + c_12*(c_12-1)/2 + sum_{a=1}^{11} c_a*c_{24-a}.
    Preconditions: hours is a slice of 64-bit integers with 1 <= len(hours) <= 500000, and for every i with 0 <= i < len(hours), 1 <= hours[i] <= 1000000000. -/
  theorem spec_8 (hours : Slice I64)
      (hlen_lo : 1 ≤ hours.val.length) (hlen_hi : hours.val.length ≤ 500000)
      (hbound : ∀ i : Fin hours.val.length,
        1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000) :
      ∃ R : I64, Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok R ∧
        R.val = ((choose2 (countMod (vals hours) 0) +
            choose2 (countMod (vals hours) 12) +
            crossPairSum (countMod (vals hours)) : Nat) : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (hours : Slice I64)
        (hlen_lo : 1 ≤ hours.val.length) (hlen_hi : hours.val.length ≤ 500000)
        (hbound : ∀ i : Fin hours.val.length,
          1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000), ∃ R : I64, Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok R ∧
          R.val = ((choose2 (countMod (vals hours) 0) +
              choose2 (countMod (vals hours) 12) +
              crossPairSum (countMod (vals hours)) : Nat) : Int)) := by
    sorry

  /-- If the function returns r on hours and r' on hours', then r = r'.
    Preconditions: hours and hours' are slices of 64-bit integers, each satisfying 1 <= len <= 500000 and 1 <= value <= 1000000000 for every element. They have equal length, and hours' is a permutation of hours: there is a bijection p on indices with hours'[i] = hours[p(i)] for every i. -/
  theorem spec_9 (hours hours' : Slice I64)
      (hlen_lo : 1 ≤ hours.val.length) (hlen_hi : hours.val.length ≤ 500000)
      (hbound : ∀ i : Fin hours.val.length,
        1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000)
      (hlen_lo' : 1 ≤ hours'.val.length) (hlen_hi' : hours'.val.length ≤ 500000)
      (hbound' : ∀ i : Fin hours'.val.length,
        1 ≤ (hours'.val.get i).val ∧ (hours'.val.get i).val ≤ 1000000000)
      (hlen : hours'.val.length = hours.val.length)
      (p : Fin hours.val.length → Fin hours.val.length) (hp : Function.Bijective p)
      (hperm : ∀ i : Fin hours'.val.length,
        (hours'.val.get i).val = (hours.val.get (p ⟨i.val, hlen ▸ i.isLt⟩)).val)
      (r r' : I64)
      (hr : Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok r)
      (hr' : Aegis.CountCompleteDayPairs.count_complete_day_pairs hours' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (hours hours' : Slice I64)
        (hlen_lo : 1 ≤ hours.val.length) (hlen_hi : hours.val.length ≤ 500000)
        (hbound : ∀ i : Fin hours.val.length,
          1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000)
        (hlen_lo' : 1 ≤ hours'.val.length) (hlen_hi' : hours'.val.length ≤ 500000)
        (hbound' : ∀ i : Fin hours'.val.length,
          1 ≤ (hours'.val.get i).val ∧ (hours'.val.get i).val ≤ 1000000000)
        (hlen : hours'.val.length = hours.val.length)
        (p : Fin hours.val.length → Fin hours.val.length) (hp : Function.Bijective p)
        (hperm : ∀ i : Fin hours'.val.length,
          (hours'.val.get i).val = (hours.val.get (p ⟨i.val, hlen ▸ i.isLt⟩)).val)
        (r r' : I64)
        (hr : Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok r)
        (hr' : Aegis.CountCompleteDayPairs.count_complete_day_pairs hours' = ok r'), r.val = r'.val) := by
    sorry

  /-- Let N = len(hours), let x = hours[N-1], and let prefix be the slice consisting of the first N-1 entries of hours. If the function returns r on hours and rp on prefix, then r = rp + M, where M is the number of indices j with 0 <= j < N-1 and hours[j] + x divisible by 24 (that is, there exists an integer k with hours[j] + x = 24*k).
    Preconditions: hours is a slice of 64-bit integers with 2 <= len(hours) <= 500000, and for every i with 0 <= i < len(hours), 1 <= hours[i] <= 1000000000. -/
  theorem spec_10 (hours pre : Slice I64)
      (hlen_lo : 2 ≤ hours.val.length) (hlen_hi : hours.val.length ≤ 500000)
      (hbound : ∀ i : Fin hours.val.length,
        1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000)
      (hpre : pre.val = hours.val.take (hours.val.length - 1))
      (r rp : I64)
      (hr : Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok r)
      (hrp : Aegis.CountCompleteDayPairs.count_complete_day_pairs pre = ok rp) :
      r.val = rp.val +
        (((hours.val.take (hours.val.length - 1)).filter
          (fun y => IsMultipleOf24
            (y.val + (hours.val.get ⟨hours.val.length - 1, by omega⟩).val))).length : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (hours pre : Slice I64)
        (hlen_lo : 2 ≤ hours.val.length) (hlen_hi : hours.val.length ≤ 500000)
        (hbound : ∀ i : Fin hours.val.length,
          1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000)
        (hpre : pre.val = hours.val.take (hours.val.length - 1))
        (r rp : I64)
        (hr : Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok r)
        (hrp : Aegis.CountCompleteDayPairs.count_complete_day_pairs pre = ok rp), r.val = rp.val +
          (((hours.val.take (hours.val.length - 1)).filter
            (fun y => IsMultipleOf24
              (y.val + (hours.val.get ⟨hours.val.length - 1, by omega⟩).val))).length : Int)) := by
    sorry

  /-- Let N = len(hours). The function returns a result r, and r = N*(N-1)/2 if and only if for every pair (i,j) with 0 <= i < j < N, there exists an integer k with hours[i] + hours[j] = 24*k.
    Preconditions: hours is a slice of 64-bit integers with 1 <= len(hours) <= 500000, and for every i with 0 <= i < len(hours), 1 <= hours[i] <= 1000000000. -/
  theorem spec_11 (hours : Slice I64)
      (hlen_lo : 1 ≤ hours.val.length) (hlen_hi : hours.val.length ≤ 500000)
      (hbound : ∀ i : Fin hours.val.length,
        1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000) :
      ∃ r : I64, Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok r ∧
        (r.val = (choose2 hours.val.length : Int) ↔
          ∀ (i j : Fin hours.val.length), i < j →
            IsMultipleOf24 ((hours.val.get i).val + (hours.val.get j).val)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (hours : Slice I64)
        (hlen_lo : 1 ≤ hours.val.length) (hlen_hi : hours.val.length ≤ 500000)
        (hbound : ∀ i : Fin hours.val.length,
          1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 1000000000), ∃ r : I64, Aegis.CountCompleteDayPairs.count_complete_day_pairs hours = ok r ∧
          (r.val = (choose2 hours.val.length : Int) ↔
            ∀ (i j : Fin hours.val.length), i < j →
              IsMultipleOf24 ((hours.val.get i).val + (hours.val.get j).val))) := by
    sorry

  end AegisSpec.CountCompleteDayPairs
