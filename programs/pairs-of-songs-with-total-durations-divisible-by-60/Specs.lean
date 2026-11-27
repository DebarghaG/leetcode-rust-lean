import Aegis.NumPairsDivisibleBy60.Code.Funs

/-!
# Specifications of `Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60`

LeetCode problem `pairs-of-songs-with-total-durations-divisible-by-60`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumPairsDivisibleBy60

def vals (time : Slice I64) : List ℤ := time.val.map (fun x => x.val)

def len (time : Slice I64) : ℕ := (vals time).length

theorem len_eq (time : Slice I64) : len time = time.val.length := by
  simp [len, vals]

def nthVal (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

def elem (time : Slice I64) (i : ℕ) : ℤ := nthVal (vals time) i

theorem elem_eq_getElem (time : Slice I64) (i : ℕ) (h : i < (vals time).length) :
    elem time i = (vals time)[i] :=
  List.getD_eq_getElem (vals time) 0 h

def divisibleBy60 (x : ℤ) : Prop := ∃ k : ℤ, x = 60 * k

instance (x : ℤ) : Decidable (divisibleBy60 x) :=
  inferInstanceAs (Decidable ((60 : ℤ) ∣ x))

def pairCount (l : List ℤ) : ℕ :=
  List.countP (fun p : ℕ × ℕ => decide (p.1 < p.2 ∧ divisibleBy60 (nthVal l p.1 + nthVal l p.2)))
    ((List.range l.length).product (List.range l.length))

def orderedPairCount (l : List ℤ) : ℕ :=
  List.countP (fun p : ℕ × ℕ => decide (p.1 ≠ p.2 ∧ divisibleBy60 (nthVal l p.1 + nthVal l p.2)))
    ((List.range l.length).product (List.range l.length))

def residueCount (l : List ℤ) (d : ℕ) : ℕ :=
  l.countP (fun x => decide (x % 60 = (d : ℤ)))

/-- The function returns a result r (it does not fail) and r is the number of pairs (i, j) of indices such that 0 <= i < j < len(time) and time[i] + time[j] is divisible by 60 (that is, there exists an integer k with time[i] + time[j] = 60 * k).
  Preconditions: 1 <= len(time) <= 60000 and for every i with 0 <= i < len(time), 1 <= time[i] <= 500. -/
theorem spec_1 (time : Slice I64)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hval : ∀ i, i < len time → 1 ≤ elem time i ∧ elem time i ≤ 500) :
    ∃ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r ∧
      r.val = (pairCount (vals time) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (time : Slice I64)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hval : ∀ i, i < len time → 1 ≤ elem time i ∧ elem time i ≤ 500), ∃ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r ∧
      r.val = (pairCount (vals time) : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns some result r; it does not panic, overflow, or access out of bounds.
  Preconditions: 1 <= len(time) <= 60000 and for every i with 0 <= i < len(time), 1 <= time[i] <= 500. -/
theorem spec_2 (time : Slice I64)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hval : ∀ i, i < len time → 1 ≤ elem time i ∧ elem time i ≤ 500) :
    ∃ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (time : Slice I64)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hval : ∀ i, i < len time → 1 ≤ elem time i ∧ elem time i ≤ 500), ∃ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: 1 <= len(time) <= 60000 and for every i with 0 <= i < len(time), 1 <= time[i] <= 500. -/
theorem spec_3 (time : Slice I64)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hval : ∀ i, i < len time → 1 ≤ elem time i ∧ elem time i ≤ 500) :
    ∀ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (time : Slice I64)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hval : ∀ i, i < len time → 1 ≤ elem time i ∧ elem time i ≤ 500), ∀ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= (len(time) * (len(time) - 1)) / 2.
  Preconditions: 1 <= len(time) <= 60000 and for every i with 0 <= i < len(time), 1 <= time[i] <= 500. -/
theorem spec_4 (time : Slice I64)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hval : ∀ i, i < len time → 1 ≤ elem time i ∧ elem time i ≤ 500) :
    ∀ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r →
      r.val ≤ ((len time : ℤ) * ((len time : ℤ) - 1)) / 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (time : Slice I64)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hval : ∀ i, i < len time → 1 ≤ elem time i ∧ elem time i ≤ 500), ∀ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r →
      r.val ≤ ((len time : ℤ) * ((len time : ℤ) - 1)) / 2) := by
  sorry

/-- The function returns r = 0.
  Preconditions: len(time) = 1 and 1 <= time[0] <= 500. -/
theorem spec_5 (time : Slice I64)
    (hlen : len time = 1)
    (hval0 : 1 ≤ elem time 0 ∧ elem time 0 ≤ 500) :
    ∃ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r ∧ r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (time : Slice I64)
    (hlen : len time = 1)
    (hval0 : 1 ≤ elem time 0 ∧ elem time 0 ≤ 500), ∃ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns r = 1 if time[0] + time[1] is divisible by 60, and r = 0 otherwise.
  Preconditions: len(time) = 2 and 1 <= time[0] <= 500 and 1 <= time[1] <= 500. -/
theorem spec_6 (time : Slice I64)
    (hlen : len time = 2)
    (hval0 : 1 ≤ elem time 0 ∧ elem time 0 ≤ 500)
    (hval1 : 1 ≤ elem time 1 ∧ elem time 1 ≤ 500) :
    ∃ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r ∧
      r.val = (if divisibleBy60 (elem time 0 + elem time 1) then (1 : ℤ) else 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (time : Slice I64)
    (hlen : len time = 2)
    (hval0 : 1 ≤ elem time 0 ∧ elem time 0 ≤ 500)
    (hval1 : 1 ≤ elem time 1 ∧ elem time 1 ≤ 500), ∃ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r ∧
      r.val = (if divisibleBy60 (elem time 0 + elem time 1) then (1 : ℤ) else 0)) := by
  sorry

/-- The function returns r = (len(time) * (len(time) - 1)) / 2.
  Preconditions: 1 <= len(time) <= 60000 and for every i with 0 <= i < len(time), 1 <= time[i] <= 500 and time[i] is divisible by 60. -/
theorem spec_7 (time : Slice I64)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hval : ∀ i, i < len time → 1 ≤ elem time i ∧ elem time i ≤ 500)
    (hdiv : ∀ i, i < len time → divisibleBy60 (elem time i)) :
    ∃ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r ∧
      r.val = ((len time : ℤ) * ((len time : ℤ) - 1)) / 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (time : Slice I64)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hval : ∀ i, i < len time → 1 ≤ elem time i ∧ elem time i ≤ 500)
    (hdiv : ∀ i, i < len time → divisibleBy60 (elem time i)), ∃ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r ∧
      r.val = ((len time : ℤ) * ((len time : ℤ) - 1)) / 2) := by
  sorry

/-- Whenever the function returns a result r with r > 0, there exist indices i and j such that 0 <= i < j < len(time) and time[i] + time[j] is divisible by 60.
  Preconditions: 1 <= len(time) <= 60000 and for every i with 0 <= i < len(time), 1 <= time[i] <= 500. -/
theorem spec_8 (time : Slice I64)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hval : ∀ i, i < len time → 1 ≤ elem time i ∧ elem time i ≤ 500) :
    ∀ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r → 0 < r.val →
      ∃ i j : ℕ, i < j ∧ j < len time ∧ divisibleBy60 (elem time i + elem time j) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (time : Slice I64)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hval : ∀ i, i < len time → 1 ≤ elem time i ∧ elem time i ≤ 500), ∀ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r → 0 < r.val →
      ∃ i j : ℕ, i < j ∧ j < len time ∧ divisibleBy60 (elem time i + elem time j)) := by
  sorry

/-- Let q be the number of ordered pairs (i, j) with 0 <= i < len(time), 0 <= j < len(time), i != j, and time[i] + time[j] divisible by 60. If the function returns r, then q = 2 * r.
  Preconditions: 1 <= len(time) <= 60000 and for every i with 0 <= i < len(time), 1 <= time[i] <= 500. -/
theorem spec_9 (time : Slice I64)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hval : ∀ i, i < len time → 1 ≤ elem time i ∧ elem time i ≤ 500) :
    ∀ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r →
      (orderedPairCount (vals time) : ℤ) = 2 * r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (time : Slice I64)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hval : ∀ i, i < len time → 1 ≤ elem time i ∧ elem time i ≤ 500), ∀ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r →
      (orderedPairCount (vals time) : ℤ) = 2 * r.val) := by
  sorry

/-- For d = 0, ..., 59 let c[d] be the number of indices i with 0 <= i < len(time) and time[i] mod 60 = d. If the function returns r, then r = c[0]*(c[0]-1)/2 + c[30]*(c[30]-1)/2 + sum_{d=1}^{29} c[d]*c[60-d].
  Preconditions: 1 <= len(time) <= 60000 and for every i with 0 <= i < len(time), 1 <= time[i] <= 500. -/
theorem spec_10 (time : Slice I64)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hval : ∀ i, i < len time → 1 ≤ elem time i ∧ elem time i ≤ 500) :
    ∀ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r →
      r.val =
        ((residueCount (vals time) 0 : ℤ) * ((residueCount (vals time) 0 : ℤ) - 1)) / 2 +
          ((residueCount (vals time) 30 : ℤ) * ((residueCount (vals time) 30 : ℤ) - 1)) / 2 +
            ((List.range 29).map (fun d : ℕ =>
              (residueCount (vals time) (d + 1) : ℤ) *
                (residueCount (vals time) (60 - (d + 1)) : ℤ))).sum := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (time : Slice I64)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hval : ∀ i, i < len time → 1 ≤ elem time i ∧ elem time i ≤ 500), ∀ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r →
      r.val =
        ((residueCount (vals time) 0 : ℤ) * ((residueCount (vals time) 0 : ℤ) - 1)) / 2 +
          ((residueCount (vals time) 30 : ℤ) * ((residueCount (vals time) 30 : ℤ) - 1)) / 2 +
            ((List.range 29).map (fun d : ℕ =>
              (residueCount (vals time) (d + 1) : ℤ) *
                (residueCount (vals time) (60 - (d + 1)) : ℤ))).sum) := by
  sorry

/-- The function returns the same result on time and on time': it returns results r and r' with r = r'.
  Preconditions: Let time and time' be two slices with len(time) = len(time') = n, 1 <= n <= 60000, and for every index k with 0 <= k < n, 1 <= time[k] <= 500 and 1 <= time'[k] <= 500. Suppose there is a bijection p from {0, ..., n-1} to itself such that time'[k] = time[p(k)] for every k. -/
theorem spec_11 (time time' : Slice I64) (p : ℕ → ℕ)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hne : len time = len time')
    (hval : ∀ k, k < len time → 1 ≤ elem time k ∧ elem time k ≤ 500)
    (hval' : ∀ k, k < len time' → 1 ≤ elem time' k ∧ elem time' k ≤ 500)
    (hp_mem : ∀ k, k < len time → p k < len time)
    (hp_inj : ∀ k k', k < len time → k' < len time → p k = p k' → k = k')
    (hperm : ∀ k, k < len time → elem time' k = elem time (p k)) :
    ∃ r r', Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r ∧
      Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time' = ok r' ∧
      r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (time time' : Slice I64) (p : ℕ → ℕ)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hne : len time = len time')
    (hval : ∀ k, k < len time → 1 ≤ elem time k ∧ elem time k ≤ 500)
    (hval' : ∀ k, k < len time' → 1 ≤ elem time' k ∧ elem time' k ≤ 500)
    (hp_mem : ∀ k, k < len time → p k < len time)
    (hp_inj : ∀ k k', k < len time → k' < len time → p k = p k' → k = k')
    (hperm : ∀ k, k < len time → elem time' k = elem time (p k)), ∃ r r', Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r ∧
      Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time' = ok r' ∧
      r.val = r'.val) := by
  sorry

/-- If 2*v is divisible by 60, then the function returns r = (len(time) * (len(time) - 1)) / 2; otherwise it returns r = 0.
  Preconditions: 1 <= len(time) <= 60000 and there exists v with 1 <= v <= 500 such that for every i with 0 <= i < len(time), time[i] = v. -/
theorem spec_12 (time : Slice I64) (v : ℤ)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hvlo : 1 ≤ v) (hvhi : v ≤ 500)
    (hconst : ∀ i, i < len time → elem time i = v) :
    ∃ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r ∧
      r.val =
        (if divisibleBy60 (2 * v) then ((len time : ℤ) * ((len time : ℤ) - 1)) / 2
          else 0) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (time : Slice I64) (v : ℤ)
    (hlen : 1 ≤ len time) (hlen' : len time ≤ 60000)
    (hvlo : 1 ≤ v) (hvhi : v ≤ 500)
    (hconst : ∀ i, i < len time → elem time i = v), ∃ r, Aegis.NumPairsDivisibleBy60.num_pairs_divisible_by60 time = ok r ∧
      r.val =
        (if divisibleBy60 (2 * v) then ((len time : ℤ) * ((len time : ℤ) - 1)) / 2
          else 0)) := by
  sorry

end AegisSpec.NumPairsDivisibleBy60
