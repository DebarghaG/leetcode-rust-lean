import Aegis.FindPoisonedDuration.Code.Funs

/-!
# Specifications of `Aegis.FindPoisonedDuration.find_poisoned_duration`

LeetCode problem `teemo-attacking`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindPoisonedDuration

abbrev find_poisoned_duration (timeSeries : Slice Std.I64) (duration : Std.I64) :
    Result Std.I64 :=
  Aegis.FindPoisonedDuration.find_poisoned_duration timeSeries duration

def vals (timeSeries : Slice Std.I64) : List ℤ := timeSeries.val.map (fun x => x.val)

def length (timeSeries : Slice Std.I64) : ℕ := (vals timeSeries).length

def elemAt (timeSeries : Slice Std.I64) (i : ℕ) : ℤ := (vals timeSeries).getD i 0

def AllInRange (l : List ℤ) (lo hi : ℤ) : Prop := ∀ x ∈ l, lo ≤ x ∧ x ≤ hi

def Nondecreasing (l : List ℤ) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < l.length), l.get ⟨i, Nat.lt_of_succ_lt h⟩ ≤ l.get ⟨i + 1, h⟩

def GapsAtMost (l : List ℤ) (d : ℤ) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < l.length), l.get ⟨i + 1, h⟩ - l.get ⟨i, Nat.lt_of_succ_lt h⟩ ≤ d

def intIco (a d : ℤ) : Finset ℤ :=
  (Finset.range d.toNat).image (fun k : ℕ => a + (k : ℤ))

def poisonedSet (l : List ℤ) (d : ℤ) : Finset ℤ :=
  (l.map (fun a => intIco a d)).foldr (· ∪ ·) ∅

def IsMinOf (s : Finset ℤ) (m : ℤ) : Prop := m ∈ s ∧ ∀ x ∈ s, m ≤ x

def IsMaxOf (s : Finset ℤ) (m : ℤ) : Prop := m ∈ s ∧ ∀ x ∈ s, x ≤ m

def distinctCount (l : List ℤ) : ℕ := l.toFinset.card

def gapSum (l : List ℤ) (d : ℤ) : ℤ :=
  (l.zip (l.drop 1)).foldr (fun p acc => acc + min d (p.2 - p.1)) 0

/-- The function returns a result r, and r equals the number of integers s such that there exists an index i with 0 <= i < len(timeSeries) and timeSeries[i] <= s < timeSeries[i] + duration. Equivalently, r is the cardinality of P = { s in Z | exists i, 0 <= i < len(timeSeries) and timeSeries[i] <= s < timeSeries[i] + duration }.
  Preconditions: 1 <= len(timeSeries) <= 10^4; 0 <= duration <= 10^7; for every i with 0 <= i < len(timeSeries), 0 <= timeSeries[i] <= 10^7; for every i with 0 <= i < len(timeSeries)-1, timeSeries[i] <= timeSeries[i+1]. -/
theorem spec_1 (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries)) :
    ∃ r : Std.I64,
      find_poisoned_duration timeSeries duration = ok r ∧
        r.val = ((poisonedSet (vals timeSeries) duration.val).card : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries)), ∃ r : Std.I64,
      find_poisoned_duration timeSeries duration = ok r ∧
        r.val = ((poisonedSet (vals timeSeries) duration.val).card : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, overflow, or panic.
  Preconditions: 1 <= len(timeSeries) <= 10^4; 0 <= duration <= 10^7; for every i with 0 <= i < len(timeSeries), 0 <= timeSeries[i] <= 10^7; for every i with 0 <= i < len(timeSeries)-1, timeSeries[i] <= timeSeries[i+1]. -/
theorem spec_2 (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries)) :
    ∃ r : Std.I64, find_poisoned_duration timeSeries duration = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries)), ∃ r : Std.I64, find_poisoned_duration timeSeries duration = ok r) := by
  sorry

/-- The function returns a result r and r >= duration.
  Preconditions: 1 <= len(timeSeries) <= 10^4; 0 <= duration <= 10^7; for every i with 0 <= i < len(timeSeries), 0 <= timeSeries[i] <= 10^7; for every i with 0 <= i < len(timeSeries)-1, timeSeries[i] <= timeSeries[i+1]. -/
theorem spec_3 (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries)) :
    ∃ r : Std.I64,
      find_poisoned_duration timeSeries duration = ok r ∧ duration.val ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries)), ∃ r : Std.I64,
      find_poisoned_duration timeSeries duration = ok r ∧ duration.val ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= timeSeries[len(timeSeries)-1] - timeSeries[0] + duration.
  Preconditions: 1 <= len(timeSeries) <= 10^4; 0 <= duration <= 10^7; for every i with 0 <= i < len(timeSeries), 0 <= timeSeries[i] <= 10^7; for every i with 0 <= i < len(timeSeries)-1, timeSeries[i] <= timeSeries[i+1]. -/
theorem spec_4 (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries)) :
    ∃ r : Std.I64,
      find_poisoned_duration timeSeries duration = ok r ∧
        r.val ≤ elemAt timeSeries (length timeSeries - 1) - elemAt timeSeries 0 + duration.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries)), ∃ r : Std.I64,
      find_poisoned_duration timeSeries duration = ok r ∧
        r.val ≤ elemAt timeSeries (length timeSeries - 1) - elemAt timeSeries 0 + duration.val) := by
  sorry

/-- Let D be the number of distinct values appearing in timeSeries, i.e. D = |{ timeSeries[i] | 0 <= i < len(timeSeries) }|. The function returns a result r and r >= D.
  Preconditions: 1 <= len(timeSeries) <= 10^4; 0 <= duration <= 10^7; for every i with 0 <= i < len(timeSeries), 0 <= timeSeries[i] <= 10^7; for every i with 0 <= i < len(timeSeries)-1, timeSeries[i] <= timeSeries[i+1]; duration >= 1. -/
theorem spec_5 (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries))
    (h_dur_pos : 1 ≤ duration.val) :
    ∃ r : Std.I64,
      find_poisoned_duration timeSeries duration = ok r ∧
        (distinctCount (vals timeSeries) : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries))
    (h_dur_pos : 1 ≤ duration.val), ∃ r : Std.I64,
      find_poisoned_duration timeSeries duration = ok r ∧
        (distinctCount (vals timeSeries) : ℤ) ≤ r.val) := by
  sorry

/-- Let D be the number of distinct values appearing in timeSeries, i.e. D = |{ timeSeries[i] | 0 <= i < len(timeSeries) }|. The function returns a result r and r <= D * duration.
  Preconditions: 1 <= len(timeSeries) <= 10^4; 0 <= duration <= 10^7; for every i with 0 <= i < len(timeSeries), 0 <= timeSeries[i] <= 10^7; for every i with 0 <= i < len(timeSeries)-1, timeSeries[i] <= timeSeries[i+1]. -/
theorem spec_6 (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries)) :
    ∃ r : Std.I64,
      find_poisoned_duration timeSeries duration = ok r ∧
        r.val ≤ (distinctCount (vals timeSeries) : ℤ) * duration.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries)), ∃ r : Std.I64,
      find_poisoned_duration timeSeries duration = ok r ∧
        r.val ≤ (distinctCount (vals timeSeries) : ℤ) * duration.val) := by
  sorry

/-- The function returns a result r and r = timeSeries[len(timeSeries)-1] - timeSeries[0] + duration.
  Preconditions: 1 <= len(timeSeries) <= 10^4; 0 <= duration <= 10^7; for every i with 0 <= i < len(timeSeries), 0 <= timeSeries[i] <= 10^7; for every i with 0 <= i < len(timeSeries)-1, timeSeries[i] <= timeSeries[i+1]; for every i with 0 <= i < len(timeSeries)-1, timeSeries[i+1] - timeSeries[i] <= duration. -/
theorem spec_7 (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries))
    (h_gaps : GapsAtMost (vals timeSeries) duration.val) :
    ∃ r : Std.I64,
      find_poisoned_duration timeSeries duration = ok r ∧
        r.val = elemAt timeSeries (length timeSeries - 1) - elemAt timeSeries 0 + duration.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries))
    (h_gaps : GapsAtMost (vals timeSeries) duration.val), ∃ r : Std.I64,
      find_poisoned_duration timeSeries duration = ok r ∧
        r.val = elemAt timeSeries (length timeSeries - 1) - elemAt timeSeries 0 + duration.val) := by
  sorry

/-- For every index i with 0 < i < len(timeSeries) and timeSeries[i] = timeSeries[i-1], let timeSeries' be the slice of length len(timeSeries)-1 obtained by deleting index i, so timeSeries'[j] = timeSeries[j] for j < i and timeSeries'[j] = timeSeries[j+1] for j >= i. Then find_poisoned_duration(timeSeries', duration) returns r' and find_poisoned_duration(timeSeries, duration) returns r, and r' = r.
  Preconditions: 1 <= len(timeSeries) <= 10^4; 0 <= duration <= 10^7; for every i with 0 <= i < len(timeSeries), 0 <= timeSeries[i] <= 10^7; for every i with 0 <= i < len(timeSeries)-1, timeSeries[i] <= timeSeries[i+1]; there exists an index i with 0 < i < len(timeSeries) and timeSeries[i] = timeSeries[i-1]. -/
theorem spec_8 (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries))
    (h_repeat : ∃ i : ℕ, 0 < i ∧ i < length timeSeries ∧
      elemAt timeSeries i = elemAt timeSeries (i - 1)) :
    ∀ (i : ℕ), 0 < i → i < length timeSeries → elemAt timeSeries i = elemAt timeSeries (i - 1) →
      ∀ timeSeries' : Slice Std.I64, vals timeSeries' = (vals timeSeries).eraseIdx i →
        ∃ r r' : Std.I64,
          find_poisoned_duration timeSeries duration = ok r ∧
            find_poisoned_duration timeSeries' duration = ok r' ∧ r' = r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries))
    (h_repeat : ∃ i : ℕ, 0 < i ∧ i < length timeSeries ∧
      elemAt timeSeries i = elemAt timeSeries (i - 1)), ∀ (i : ℕ), 0 < i → i < length timeSeries → elemAt timeSeries i = elemAt timeSeries (i - 1) →
      ∀ timeSeries' : Slice Std.I64, vals timeSeries' = (vals timeSeries).eraseIdx i →
        ∃ r r' : Std.I64,
          find_poisoned_duration timeSeries duration = ok r ∧
            find_poisoned_duration timeSeries' duration = ok r' ∧ r' = r) := by
  sorry

/-- Let timeSeries' be the slice with timeSeries'[j] = timeSeries[j] + c for every j with 0 <= j < len(timeSeries). Then find_poisoned_duration(timeSeries', duration) returns r' and find_poisoned_duration(timeSeries, duration) returns r, and r' = r.
  Preconditions: 1 <= len(timeSeries) <= 10^4; 0 <= duration <= 10^7; for every i with 0 <= i < len(timeSeries), 0 <= timeSeries[i] <= 10^7; for every i with 0 <= i < len(timeSeries)-1, timeSeries[i] <= timeSeries[i+1]; for every integer c such that 0 <= timeSeries[j] + c <= 10^7 for all j with 0 <= j < len(timeSeries). -/
theorem spec_9 (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries)) :
    ∀ c : ℤ, (∀ j : ℕ, j < length timeSeries →
        0 ≤ elemAt timeSeries j + c ∧ elemAt timeSeries j + c ≤ 10000000) →
      ∀ timeSeries' : Slice Std.I64, vals timeSeries' = (vals timeSeries).map (fun x => x + c) →
        ∃ r r' : Std.I64,
          find_poisoned_duration timeSeries duration = ok r ∧
            find_poisoned_duration timeSeries' duration = ok r' ∧ r' = r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries)), ∀ c : ℤ, (∀ j : ℕ, j < length timeSeries →
        0 ≤ elemAt timeSeries j + c ∧ elemAt timeSeries j + c ≤ 10000000) →
      ∀ timeSeries' : Slice Std.I64, vals timeSeries' = (vals timeSeries).map (fun x => x + c) →
        ∃ r r' : Std.I64,
          find_poisoned_duration timeSeries duration = ok r ∧
            find_poisoned_duration timeSeries' duration = ok r' ∧ r' = r) := by
  sorry

/-- For every d1 and d2 with 0 <= d1 <= d2 <= 10^7, find_poisoned_duration(timeSeries, d1) returns r1 and find_poisoned_duration(timeSeries, d2) returns r2, and r1 <= r2.
  Preconditions: 1 <= len(timeSeries) <= 10^4; 0 <= duration <= 10^7; for every i with 0 <= i < len(timeSeries), 0 <= timeSeries[i] <= 10^7; for every i with 0 <= i < len(timeSeries)-1, timeSeries[i] <= timeSeries[i+1]. -/
theorem spec_10 (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries)) :
    ∀ d1 d2 : Std.I64, 0 ≤ d1.val → d1.val ≤ d2.val → d2.val ≤ 10000000 →
      ∃ r1 r2 : Std.I64,
        find_poisoned_duration timeSeries d1 = ok r1 ∧
          find_poisoned_duration timeSeries d2 = ok r2 ∧ r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries)), ∀ d1 d2 : Std.I64, 0 ≤ d1.val → d1.val ≤ d2.val → d2.val ≤ 10000000 →
      ∃ r1 r2 : Std.I64,
        find_poisoned_duration timeSeries d1 = ok r1 ∧
          find_poisoned_duration timeSeries d2 = ok r2 ∧ r1.val ≤ r2.val) := by
  sorry

/-- Let P = { s in Z | exists i, 0 <= i < len(timeSeries) and timeSeries[i] <= s < timeSeries[i] + duration }. The function returns a result r and P has minimum timeSeries[0] and maximum timeSeries[len(timeSeries)-1] + duration - 1.
  Preconditions: 1 <= len(timeSeries) <= 10^4; 0 <= duration <= 10^7; for every i with 0 <= i < len(timeSeries), 0 <= timeSeries[i] <= 10^7; for every i with 0 <= i < len(timeSeries)-1, timeSeries[i] <= timeSeries[i+1]; duration >= 1. -/
theorem spec_11 (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries))
    (h_dur_pos : 1 ≤ duration.val) :
    ∃ r : Std.I64,
      find_poisoned_duration timeSeries duration = ok r ∧
        IsMinOf (poisonedSet (vals timeSeries) duration.val) (elemAt timeSeries 0) ∧
        IsMaxOf (poisonedSet (vals timeSeries) duration.val)
          (elemAt timeSeries (length timeSeries - 1) + duration.val - 1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries))
    (h_dur_pos : 1 ≤ duration.val), ∃ r : Std.I64,
      find_poisoned_duration timeSeries duration = ok r ∧
        IsMinOf (poisonedSet (vals timeSeries) duration.val) (elemAt timeSeries 0) ∧
        IsMaxOf (poisonedSet (vals timeSeries) duration.val)
          (elemAt timeSeries (length timeSeries - 1) + duration.val - 1)) := by
  sorry

/-- Let n = len(timeSeries). The function returns a result r and r = duration + sum_{i=0}^{n-2} min(duration, timeSeries[i+1] - timeSeries[i]). This sum is empty when n = 1.
  Preconditions: 1 <= len(timeSeries) <= 10^4; 0 <= duration <= 10^7; for every i with 0 <= i < len(timeSeries), 0 <= timeSeries[i] <= 10^7; for every i with 0 <= i < len(timeSeries)-1, timeSeries[i] <= timeSeries[i+1]. -/
theorem spec_12 (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries)) :
    ∃ r : Std.I64,
      find_poisoned_duration timeSeries duration = ok r ∧
        r.val = duration.val + gapSum (vals timeSeries) duration.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (timeSeries : Slice Std.I64) (duration : Std.I64)
    (h_len_lower : 1 ≤ length timeSeries)
    (h_len_upper : length timeSeries ≤ 10000)
    (h_dur_lower : 0 ≤ duration.val)
    (h_dur_upper : duration.val ≤ 10000000)
    (h_elems : AllInRange (vals timeSeries) 0 10000000)
    (h_sorted : Nondecreasing (vals timeSeries)), ∃ r : Std.I64,
      find_poisoned_duration timeSeries duration = ok r ∧
        r.val = duration.val + gapSum (vals timeSeries) duration.val) := by
  sorry

end AegisSpec.FindPoisonedDuration
