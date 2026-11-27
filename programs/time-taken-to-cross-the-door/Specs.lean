import Aegis.TimeTaken.Code.Funs

/-!
# Specifications of `Aegis.TimeTaken.time_taken`

LeetCode problem `time-taken-to-cross-the-door`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.TimeTaken

def valueAt (l : List I64) (i : Nat) : Int :=
  (l.getD i 0#i64).val

def inW (arrival r : List I64) (n : Nat) (t : Int) (i : Nat) : Prop :=
  i < n ∧ valueAt arrival i ≤ t ∧ t ≤ valueAt r i

def prevIdx (r : List I64) (t : Int) : Option Nat :=
  (List.range r.length).find? (fun q => decide (valueAt r q = t - 1))

def dprev (state r : List I64) (t : Int) : Int :=
  if t = 0 then 1
  else
    match prevIdx r t with
    | none => 1
    | some q => valueAt state q

/-- The function returns a result r such that len(r) = n and, for every i with 0 <= i < n, arrival[i] <= r[i]. For each integer t >= 0 define W_t = { i | 0 <= i < n, arrival[i] <= t, and r[i] >= t }. For each integer t >= 0 define d_t as follows: d_t = 1 if t = 0 or no i has r[i] = t-1; otherwise d_t = state[q] where q is the unique i with r[i] = t-1. For every integer t >= 0: (a) if W_t is empty, then no i has r[i] = t; (b) if W_t is nonempty, then exactly one i has r[i] = t, and if c is that person, then: if some j in W_t has state[j] = d_t, then state[c] = d_t and c <= j for every j in W_t with state[j] = d_t; if no j in W_t has state[j] = d_t, then c <= j for every j in W_t. These conditions determine r completely.
  Preconditions: Let n = len(arrival). n is an integer with 1 <= n <= 100000, len(arrival) = len(state) = n, arrival is non-decreasing (arrival[i] <= arrival[i+1] for 0 <= i < n-1), 0 <= arrival[i] <= n for every 0 <= i < n, and state[i] is either 0 or 1 for every 0 <= i < n. Here state[i] = 0 means person i wants to enter and state[i] = 1 means person i wants to exit. -/
theorem spec_1 (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1) :
    ∃ r : alloc.vec.Vec I64,
      Aegis.TimeTaken.time_taken arrival state = ok r ∧
      r.val.length = n ∧
      (∀ i : Nat, i < n → valueAt arrival.val i ≤ valueAt r.val i) ∧
      (∀ t : Int, 0 ≤ t →
        ((∀ i : Nat, ¬ inW arrival.val r.val n t i) → ∀ i : Nat, i < n → valueAt r.val i ≠ t) ∧
        ((∃ i : Nat, inW arrival.val r.val n t i) →
          ∃ c : Nat, c < n ∧ valueAt r.val c = t ∧
            (∀ c' : Nat, c' < n → valueAt r.val c' = t → c' = c) ∧
            ((∃ j : Nat, inW arrival.val r.val n t j ∧
                valueAt state.val j = dprev state.val r.val t) →
              valueAt state.val c = dprev state.val r.val t ∧
              (∀ j : Nat, inW arrival.val r.val n t j →
                valueAt state.val j = dprev state.val r.val t → c ≤ j)) ∧
            ((∀ j : Nat, inW arrival.val r.val n t j →
                valueAt state.val j ≠ dprev state.val r.val t) →
              ∀ j : Nat, inW arrival.val r.val n t j → c ≤ j))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1), ∃ r : alloc.vec.Vec I64,
      Aegis.TimeTaken.time_taken arrival state = ok r ∧
      r.val.length = n ∧
      (∀ i : Nat, i < n → valueAt arrival.val i ≤ valueAt r.val i) ∧
      (∀ t : Int, 0 ≤ t →
        ((∀ i : Nat, ¬ inW arrival.val r.val n t i) → ∀ i : Nat, i < n → valueAt r.val i ≠ t) ∧
        ((∃ i : Nat, inW arrival.val r.val n t i) →
          ∃ c : Nat, c < n ∧ valueAt r.val c = t ∧
            (∀ c' : Nat, c' < n → valueAt r.val c' = t → c' = c) ∧
            ((∃ j : Nat, inW arrival.val r.val n t j ∧
                valueAt state.val j = dprev state.val r.val t) →
              valueAt state.val c = dprev state.val r.val t ∧
              (∀ j : Nat, inW arrival.val r.val n t j →
                valueAt state.val j = dprev state.val r.val t → c ≤ j)) ∧
            ((∀ j : Nat, inW arrival.val r.val n t j →
                valueAt state.val j ≠ dprev state.val r.val t) →
              ∀ j : Nat, inW arrival.val r.val n t j → c ≤ j)))) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or perform an out-of-bounds access.
  Preconditions: Let n = len(arrival). n is an integer with 1 <= n <= 100000, len(arrival) = len(state) = n, arrival is non-decreasing, 0 <= arrival[i] <= n for every 0 <= i < n, and state[i] is either 0 or 1 for every 0 <= i < n. -/
theorem spec_2 (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1) :
    ∃ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1), ∃ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = n = len(arrival) = len(state).
  Preconditions: Let n = len(arrival). n is an integer with 1 <= n <= 100000, len(arrival) = len(state) = n, arrival is non-decreasing, 0 <= arrival[i] <= n for every 0 <= i < n, and state[i] is either 0 or 1 for every 0 <= i < n. -/
theorem spec_3 (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1) :
    ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      r.val.length = n ∧ r.val.length = arrival.val.length ∧
        r.val.length = state.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1), ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      r.val.length = n ∧ r.val.length = arrival.val.length ∧
        r.val.length = state.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] >= arrival[i].
  Preconditions: Let n = len(arrival). n is an integer with 1 <= n <= 100000, len(arrival) = len(state) = n, arrival is non-decreasing, 0 <= arrival[i] <= n for every 0 <= i < n, and state[i] is either 0 or 1 for every 0 <= i < n. -/
theorem spec_4 (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1) :
    ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ i : Nat, i < n → valueAt arrival.val i ≤ valueAt r.val i := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1), ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ i : Nat, i < n → valueAt arrival.val i ≤ valueAt r.val i) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] <= arrival[i] + (n - 1).
  Preconditions: Let n = len(arrival). n is an integer with 1 <= n <= 100000, len(arrival) = len(state) = n, arrival is non-decreasing, 0 <= arrival[i] <= n for every 0 <= i < n, and state[i] is either 0 or 1 for every 0 <= i < n. -/
theorem spec_5 (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1) :
    ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ i : Nat, i < n → valueAt r.val i ≤ valueAt arrival.val i + ((n : Int) - 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1), ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ i : Nat, i < n → valueAt r.val i ≤ valueAt arrival.val i + ((n : Int) - 1)) := by
  sorry

/-- Whenever the function returns a result r, for all i,j with 0 <= i < j < n, r[i] != r[j].
  Preconditions: Let n = len(arrival). n is an integer with 1 <= n <= 100000, len(arrival) = len(state) = n, arrival is non-decreasing, 0 <= arrival[i] <= n for every 0 <= i < n, and state[i] is either 0 or 1 for every 0 <= i < n. -/
theorem spec_6 (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1) :
    ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ i j : Nat, i < j → j < n → valueAt r.val i ≠ valueAt r.val j := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1), ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ i j : Nat, i < j → j < n → valueAt r.val i ≠ valueAt r.val j) := by
  sorry

/-- Whenever the function returns a result r, for every integer t >= 0, if there exists i with 0 <= i < n, arrival[i] <= t, and r[i] >= t, then there exists j with 0 <= j < n and r[j] = t.
  Preconditions: Let n = len(arrival). n is an integer with 1 <= n <= 100000, len(arrival) = len(state) = n, arrival is non-decreasing, 0 <= arrival[i] <= n for every 0 <= i < n, and state[i] is either 0 or 1 for every 0 <= i < n. -/
theorem spec_7 (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1) :
    ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ t : Int, 0 ≤ t → (∃ i : Nat, inW arrival.val r.val n t i) →
        ∃ j : Nat, j < n ∧ valueAt r.val j = t := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1), ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ t : Int, 0 ≤ t → (∃ i : Nat, inW arrival.val r.val n t i) →
        ∃ j : Nat, j < n ∧ valueAt r.val j = t) := by
  sorry

/-- Whenever the function returns a result r, for all i,j with 0 <= i < j < n and state[i] = state[j], we have r[i] < r[j].
  Preconditions: Let n = len(arrival). n is an integer with 1 <= n <= 100000, len(arrival) = len(state) = n, arrival is non-decreasing, 0 <= arrival[i] <= n for every 0 <= i < n, and state[i] is either 0 or 1 for every 0 <= i < n. -/
theorem spec_8 (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1) :
    ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ i j : Nat, i < j → j < n → valueAt state.val i = valueAt state.val j →
        valueAt r.val i < valueAt r.val j := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1), ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ i j : Nat, i < j → j < n → valueAt state.val i = valueAt state.val j →
        valueAt r.val i < valueAt r.val j) := by
  sorry

/-- Whenever the function returns a result r, for every integer t >= 1, if there is q with 0 <= q < n and r[q] = t-1, and if there is j with 0 <= j < n, arrival[j] <= t, r[j] >= t, and state[j] = state[q], then there is c with 0 <= c < n, r[c] = t, and state[c] = state[q].
  Preconditions: Let n = len(arrival). n is an integer with 1 <= n <= 100000, len(arrival) = len(state) = n, arrival is non-decreasing, 0 <= arrival[i] <= n for every 0 <= i < n, and state[i] is either 0 or 1 for every 0 <= i < n. -/
theorem spec_9 (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1) :
    ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ t : Int, 1 ≤ t →
        ∀ q : Nat, q < n → valueAt r.val q = t - 1 →
          (∃ j : Nat, inW arrival.val r.val n t j ∧
              valueAt state.val j = valueAt state.val q) →
            ∃ c : Nat, c < n ∧ valueAt r.val c = t ∧
              valueAt state.val c = valueAt state.val q := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1), ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ t : Int, 1 ≤ t →
        ∀ q : Nat, q < n → valueAt r.val q = t - 1 →
          (∃ j : Nat, inW arrival.val r.val n t j ∧
              valueAt state.val j = valueAt state.val q) →
            ∃ c : Nat, c < n ∧ valueAt r.val c = t ∧
              valueAt state.val c = valueAt state.val q) := by
  sorry

/-- Whenever the function returns a result r, for every integer t >= 0 such that t = 0 or no i has r[i] = t-1, if W_t = { i | 0 <= i < n, arrival[i] <= t, r[i] >= t } is nonempty, then there is a unique c with r[c] = t; moreover, if some j in W_t has state[j] = 1 then state[c] = 1, and if no j in W_t has state[j] = 1 then state[c] = 0.
  Preconditions: Let n = len(arrival). n is an integer with 1 <= n <= 100000, len(arrival) = len(state) = n, arrival is non-decreasing, 0 <= arrival[i] <= n for every 0 <= i < n, and state[i] is either 0 or 1 for every 0 <= i < n. -/
theorem spec_10 (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1) :
    ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ t : Int, 0 ≤ t →
        (t = 0 ∨ ∀ i : Nat, i < n → valueAt r.val i ≠ t - 1) →
        (∃ i : Nat, inW arrival.val r.val n t i) →
          ∃ c : Nat, c < n ∧ valueAt r.val c = t ∧
            (∀ c' : Nat, c' < n → valueAt r.val c' = t → c' = c) ∧
            ((∃ j : Nat, inW arrival.val r.val n t j ∧ valueAt state.val j = 1) →
              valueAt state.val c = 1) ∧
            ((∀ j : Nat, inW arrival.val r.val n t j → valueAt state.val j ≠ 1) →
              valueAt state.val c = 0) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1), ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ t : Int, 0 ≤ t →
        (t = 0 ∨ ∀ i : Nat, i < n → valueAt r.val i ≠ t - 1) →
        (∃ i : Nat, inW arrival.val r.val n t i) →
          ∃ c : Nat, c < n ∧ valueAt r.val c = t ∧
            (∀ c' : Nat, c' < n → valueAt r.val c' = t → c' = c) ∧
            ((∃ j : Nat, inW arrival.val r.val n t j ∧ valueAt state.val j = 1) →
              valueAt state.val c = 1) ∧
            ((∀ j : Nat, inW arrival.val r.val n t j → valueAt state.val j ≠ 1) →
              valueAt state.val c = 0)) := by
  sorry

/-- Whenever the function returns a result r, for every integer t >= 0, if W_t = { i | 0 <= i < n, arrival[i] <= t, r[i] >= t } is nonempty and all members of W_t have the same state, then there is a unique c with r[c] = t, and c is the smallest-index member of W_t (that is, c is in W_t and c <= j for every j in W_t).
  Preconditions: Let n = len(arrival). n is an integer with 1 <= n <= 100000, len(arrival) = len(state) = n, arrival is non-decreasing, 0 <= arrival[i] <= n for every 0 <= i < n, and state[i] is either 0 or 1 for every 0 <= i < n. -/
theorem spec_11 (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1) :
    ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ t : Int, 0 ≤ t →
        (∃ i : Nat, inW arrival.val r.val n t i) →
        (∀ i j : Nat, inW arrival.val r.val n t i → inW arrival.val r.val n t j →
            valueAt state.val i = valueAt state.val j) →
          ∃ c : Nat, valueAt r.val c = t ∧
            (∀ c' : Nat, c' < n → valueAt r.val c' = t → c' = c) ∧
            inW arrival.val r.val n t c ∧
            (∀ j : Nat, inW arrival.val r.val n t j → c ≤ j) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1), ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ t : Int, 0 ≤ t →
        (∃ i : Nat, inW arrival.val r.val n t i) →
        (∀ i j : Nat, inW arrival.val r.val n t i → inW arrival.val r.val n t j →
            valueAt state.val i = valueAt state.val j) →
          ∃ c : Nat, valueAt r.val c = t ∧
            (∀ c' : Nat, c' < n → valueAt r.val c' = t → c' = c) ∧
            inW arrival.val r.val n t c ∧
            (∀ j : Nat, inW arrival.val r.val n t j → c ≤ j)) := by
  sorry

/-- Whenever the function returns a result r, for every integer t >= 1, if there is q with r[q] = t-1, and if no j satisfies arrival[j] <= t, r[j] >= t, and state[j] = state[q], and if W_t = { i | 0 <= i < n, arrival[i] <= t, r[i] >= t } is nonempty, then there is a unique c with r[c] = t; moreover state[c] != state[q] and c <= j for every j in W_t.
  Preconditions: Let n = len(arrival). n is an integer with 1 <= n <= 100000, len(arrival) = len(state) = n, arrival is non-decreasing, 0 <= arrival[i] <= n for every 0 <= i < n, and state[i] is either 0 or 1 for every 0 <= i < n. -/
theorem spec_12 (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1) :
    ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ t : Int, 1 ≤ t →
        ∀ q : Nat, q < n → valueAt r.val q = t - 1 →
          (∀ j : Nat, ¬ (j < n ∧ valueAt arrival.val j ≤ t ∧ t ≤ valueAt r.val j ∧
              valueAt state.val j = valueAt state.val q)) →
          (∃ i : Nat, inW arrival.val r.val n t i) →
            ∃ c : Nat, valueAt r.val c = t ∧
              (∀ c' : Nat, c' < n → valueAt r.val c' = t → c' = c) ∧
              valueAt state.val c ≠ valueAt state.val q ∧
              (∀ j : Nat, inW arrival.val r.val n t j → c ≤ j) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1), ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ t : Int, 1 ≤ t →
        ∀ q : Nat, q < n → valueAt r.val q = t - 1 →
          (∀ j : Nat, ¬ (j < n ∧ valueAt arrival.val j ≤ t ∧ t ≤ valueAt r.val j ∧
              valueAt state.val j = valueAt state.val q)) →
          (∃ i : Nat, inW arrival.val r.val n t i) →
            ∃ c : Nat, valueAt r.val c = t ∧
              (∀ c' : Nat, c' < n → valueAt r.val c' = t → c' = c) ∧
              valueAt state.val c ≠ valueAt state.val q ∧
              (∀ j : Nat, inW arrival.val r.val n t j → c ≤ j)) := by
  sorry

/-- Whenever the function returns a result r, for every integer t >= 0 with t = 0 or no i having r[i] = t-1, for every i with state[i] = 0, arrival[i] <= t, r[i] >= t and every j with state[j] = 1, arrival[j] <= t, r[j] >= t, we have r[j] < r[i].
  Preconditions: Let n = len(arrival). n is an integer with 1 <= n <= 100000, len(arrival) = len(state) = n, arrival is non-decreasing, 0 <= arrival[i] <= n for every 0 <= i < n, and state[i] is either 0 or 1 for every 0 <= i < n. -/
theorem spec_13 (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1) :
    ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ t : Int, 0 ≤ t →
        (t = 0 ∨ ∀ i : Nat, i < n → valueAt r.val i ≠ t - 1) →
        ∀ i : Nat, i < n → valueAt state.val i = 0 →
          valueAt arrival.val i ≤ t → t ≤ valueAt r.val i →
          ∀ j : Nat, j < n → valueAt state.val j = 1 →
            valueAt arrival.val j ≤ t → t ≤ valueAt r.val j →
              valueAt r.val j < valueAt r.val i := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (arrival state : Slice I64) (n : Nat)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (h_len_arr : arrival.val.length = n) (h_len_state : state.val.length = n)
    (h_mono : ∀ i : Nat, i + 1 < n → valueAt arrival.val i ≤ valueAt arrival.val (i + 1))
    (h_nonneg : ∀ i : Nat, i < n → 0 ≤ valueAt arrival.val i)
    (h_bound : ∀ i : Nat, i < n → valueAt arrival.val i ≤ (n : Int))
    (h_state01 : ∀ i : Nat, i < n → valueAt state.val i = 0 ∨ valueAt state.val i = 1), ∀ r : alloc.vec.Vec I64, Aegis.TimeTaken.time_taken arrival state = ok r →
      ∀ t : Int, 0 ≤ t →
        (t = 0 ∨ ∀ i : Nat, i < n → valueAt r.val i ≠ t - 1) →
        ∀ i : Nat, i < n → valueAt state.val i = 0 →
          valueAt arrival.val i ≤ t → t ≤ valueAt r.val i →
          ∀ j : Nat, j < n → valueAt state.val j = 1 →
            valueAt arrival.val j ≤ t → t ≤ valueAt r.val j →
              valueAt r.val j < valueAt r.val i) := by
  sorry

end AegisSpec.TimeTaken
