import Aegis.MaxTwoEvents.Code.Funs

/-!
# Specifications of `Aegis.MaxTwoEvents.max_two_events`

LeetCode problem `two-best-non-overlapping-events`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxTwoEvents

  namespace AegisSpec.MaxTwoEvents

  def fields (events : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : List ℤ :=
    match events.val[i]? with
    | some v => v.val.map (fun x => x.val)
    | none => []

  def startOf (events : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    (fields events i).getD 0 0

  def endOf (events : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    (fields events i).getD 1 0

  def valueOf (events : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    (fields events i).getD 2 0

  def Compatible (events : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : Prop :=
    endOf events i < startOf events j ∨ endOf events j < startOf events i

  def Feasible (events : Slice (alloc.vec.Vec Std.I64))
      (T : Finset (Fin events.val.length)) : Prop :=
    T.card ≤ 2 ∧ ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Compatible events (i : ℕ) (j : ℕ)

  def IsFeasibleSum (events : Slice (alloc.vec.Vec Std.I64)) (s : ℤ) : Prop :=
    ∃ T : Finset (Fin events.val.length),
      Feasible events T ∧ s = T.sum (fun i => valueOf events (i : ℕ))

  def IsMaxValue (events : Slice (alloc.vec.Vec Std.I64)) (m : ℤ) : Prop :=
    (∃ i, i < events.val.length ∧ valueOf events i = m) ∧
      ∀ i, i < events.val.length → valueOf events i ≤ m

  def Permuted (events : Slice (alloc.vec.Vec Std.I64))
      (pi : Equiv.Perm (Fin events.val.length)) : List (alloc.vec.Vec Std.I64) :=
    (List.finRange events.val.length).map (fun i => events.val.get (pi i))

  def ValidInput (events : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    2 ≤ events.val.length ∧ events.val.length ≤ 100000 ∧
      ∀ i, i < events.val.length →
        (fields events i).length = 3 ∧
        1 ≤ startOf events i ∧ startOf events i ≤ endOf events i ∧
        endOf events i ≤ 1000000000 ∧
        1 ≤ valueOf events i ∧ valueOf events i ≤ 1000000

  /-- Let n = len(events). For 0 <= i < n write start_i = events[i][0], end_i = events[i][1], value_i = events[i][2]. Call a set T of indices feasible when |T| <= 2 and, for every two distinct i,j in T, either end_i < start_j or end_j < start_i. Define S = { sum_{i in T} value_i | T is feasible }, with the empty sum equal to 0. Then the function returns a result r and r = max(S).
    Preconditions: events has length n with 2 <= n <= 100000. For every i with 0 <= i < n, events[i] has length 3; writing start_i = events[i][0], end_i = events[i][1], value_i = events[i][2], we have 1 <= start_i <= end_i <= 1000000000 and 1 <= value_i <= 1000000. -/
  theorem spec_1 (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events) :
      ∃ r, max_two_events events = ok r ∧ IsFeasibleSum events r.val ∧
        ∀ s, IsFeasibleSum events s → s ≤ r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events), ∃ r, max_two_events events = ok r ∧ IsFeasibleSum events r.val ∧
          ∀ s, IsFeasibleSum events s → s ≤ r.val) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, overflow, panic, or access an out-of-bounds index.
    Preconditions: events has length n with 2 <= n <= 100000. For every i with 0 <= i < n, events[i] has length 3; writing start_i = events[i][0], end_i = events[i][1], value_i = events[i][2], we have 1 <= start_i <= end_i <= 1000000000 and 1 <= value_i <= 1000000. -/
  theorem spec_2 (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events) :
      ∃ r, max_two_events events = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events), ∃ r, max_two_events events = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n we have r >= value_i.
    Preconditions: events has length n with 2 <= n <= 100000. For every i with 0 <= i < n, events[i] has length 3; writing start_i = events[i][0], end_i = events[i][1], value_i = events[i][2], we have 1 <= start_i <= end_i <= 1000000000 and 1 <= value_i <= 1000000. -/
  theorem spec_3 (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events) :
      ∀ r, max_two_events events = ok r →
        ∀ i, i < events.val.length → valueOf events i ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events), ∀ r, max_two_events events = ok r →
          ∀ i, i < events.val.length → valueOf events i ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of distinct indices i,j with 0 <= i < n and 0 <= j < n such that end_i < start_j or end_j < start_i, we have value_i + value_j <= r.
    Preconditions: events has length n with 2 <= n <= 100000. For every i with 0 <= i < n, events[i] has length 3; writing start_i = events[i][0], end_i = events[i][1], value_i = events[i][2], we have 1 <= start_i <= end_i <= 1000000000 and 1 <= value_i <= 1000000. -/
  theorem spec_4 (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events) :
      ∀ r, max_two_events events = ok r →
        ∀ i j, i < events.val.length → j < events.val.length → i ≠ j →
          Compatible events i j → valueOf events i + valueOf events j ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events), ∀ r, max_two_events events = ok r →
          ∀ i j, i < events.val.length → j < events.val.length → i ≠ j →
            Compatible events i j → valueOf events i + valueOf events j ≤ r.val) := by
    sorry

  /-- Let p be an index with 0 <= p < n and value_p = max_{0 <= i < n} value_i. Let q be an index with 0 <= q < n, q != p, and value_q = max_{0 <= i < n, i != p} value_i. Whenever the function returns a result r, r <= value_p + value_q.
    Preconditions: events has length n with 2 <= n <= 100000. For every i with 0 <= i < n, events[i] has length 3; writing start_i = events[i][0], end_i = events[i][1], value_i = events[i][2], we have 1 <= start_i <= end_i <= 1000000000 and 1 <= value_i <= 1000000. -/
  theorem spec_5 (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events)
      (p q : ℕ)
      (hp : p < events.val.length)
      (hpv : ∀ i, i < events.val.length → valueOf events i ≤ valueOf events p)
      (hq : q < events.val.length) (hqp : q ≠ p)
      (hqv : ∀ i, i < events.val.length → i ≠ p → valueOf events i ≤ valueOf events q) :
      ∀ r, max_two_events events = ok r →
        r.val ≤ valueOf events p + valueOf events q := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events)
        (p q : ℕ)
        (hp : p < events.val.length)
        (hpv : ∀ i, i < events.val.length → valueOf events i ≤ valueOf events p)
        (hq : q < events.val.length) (hqp : q ≠ p)
        (hqv : ∀ i, i < events.val.length → i ≠ p → valueOf events i ≤ valueOf events q), ∀ r, max_two_events events = ok r →
          r.val ≤ valueOf events p + valueOf events q) := by
    sorry

  /-- Whenever the function returns a result r, there exists a set T of indices with |T| <= 2 and, for every two distinct i,j in T, either end_i < start_j or end_j < start_i, such that r = sum_{i in T} value_i.
    Preconditions: events has length n with 2 <= n <= 100000. For every i with 0 <= i < n, events[i] has length 3; writing start_i = events[i][0], end_i = events[i][1], value_i = events[i][2], we have 1 <= start_i <= end_i <= 1000000000 and 1 <= value_i <= 1000000. -/
  theorem spec_6 (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events) :
      ∀ r, max_two_events events = ok r → IsFeasibleSum events r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events), ∀ r, max_two_events events = ok r → IsFeasibleSum events r.val) := by
    sorry

  /-- Whenever the function returns a result r, r > 0.
    Preconditions: events has length n with 2 <= n <= 100000. For every i with 0 <= i < n, events[i] has length 3; writing start_i = events[i][0], end_i = events[i][1], value_i = events[i][2], we have 1 <= start_i <= end_i <= 1000000000 and 1 <= value_i <= 1000000. -/
  theorem spec_7 (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events) :
      ∀ r, max_two_events events = ok r → 0 < r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events), ∀ r, max_two_events events = ok r → 0 < r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = max_{0 <= i < n} value_i.
    Preconditions: events has length n with 2 <= n <= 100000. For every i with 0 <= i < n, events[i] has length 3; writing start_i = events[i][0], end_i = events[i][1], value_i = events[i][2], we have 1 <= start_i <= end_i <= 1000000000 and 1 <= value_i <= 1000000. Additionally, for every pair of distinct indices i,j with 0 <= i < n and 0 <= j < n, neither end_i < start_j nor end_j < start_i. -/
  theorem spec_8 (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events)
      (hdisj : ∀ i j, i < events.val.length → j < events.val.length → i ≠ j →
        ¬ Compatible events i j) :
      ∀ r, max_two_events events = ok r → IsMaxValue events r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events)
        (hdisj : ∀ i j, i < events.val.length → j < events.val.length → i ≠ j →
          ¬ Compatible events i j), ∀ r, max_two_events events = ok r → IsMaxValue events r.val) := by
    sorry

  /-- Whenever the function returns a result r, if there exist distinct indices i,j with 0 <= i < n and 0 <= j < n such that end_i < start_j or end_j < start_i, then r = 2*v; otherwise r = v.
    Preconditions: events has length n with 2 <= n <= 100000. For every i with 0 <= i < n, events[i] has length 3; writing start_i = events[i][0], end_i = events[i][1], value_i = events[i][2], we have 1 <= start_i <= end_i <= 1000000000 and 1 <= value_i <= 1000000. Additionally, there exists v such that for every i with 0 <= i < n, value_i = v. -/
  theorem spec_9 (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events)
      (v : ℤ) (hv : ∀ i, i < events.val.length → valueOf events i = v) :
      ∀ r, max_two_events events = ok r →
        ((∃ i j, i < events.val.length ∧ j < events.val.length ∧ i ≠ j ∧
            Compatible events i j) → r.val = 2 * v) ∧
        (¬ (∃ i j, i < events.val.length ∧ j < events.val.length ∧ i ≠ j ∧
            Compatible events i j) → r.val = v) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events)
        (v : ℤ) (hv : ∀ i, i < events.val.length → valueOf events i = v), ∀ r, max_two_events events = ok r →
          ((∃ i j, i < events.val.length ∧ j < events.val.length ∧ i ≠ j ∧
              Compatible events i j) → r.val = 2 * v) ∧
          (¬ (∃ i j, i < events.val.length ∧ j < events.val.length ∧ i ≠ j ∧
              Compatible events i j) → r.val = v)) := by
    sorry

  /-- For every permutation pi of {0,...,n-1}, let events_pi be the list with events_pi[i] = events[pi(i)] for 0 <= i < n. Whenever the function returns r on events and returns r' on events_pi, we have r = r'.
    Preconditions: events has length n with 2 <= n <= 100000. For every i with 0 <= i < n, events[i] has length 3; writing start_i = events[i][0], end_i = events[i][1], value_i = events[i][2], we have 1 <= start_i <= end_i <= 1000000000 and 1 <= value_i <= 1000000. -/
  theorem spec_10 (events events' : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events)
      (pi : Equiv.Perm (Fin events.val.length))
      (hperm : events'.val = Permuted events pi) :
      ∀ r r', max_two_events events = ok r → max_two_events events' = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (events events' : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events)
        (pi : Equiv.Perm (Fin events.val.length))
        (hperm : events'.val = Permuted events pi), ∀ r r', max_two_events events = ok r → max_two_events events' = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Let p be an index with 0 <= p < n and value_p = max_{0 <= i < n} value_i. Let q be an index with 0 <= q < n, q != p, and value_q = max_{0 <= i < n, i != p} value_i. Whenever the function returns a result r, r = value_p + value_q.
    Preconditions: events has length n with 2 <= n <= 100000. For every i with 0 <= i < n, events[i] has length 3; writing start_i = events[i][0], end_i = events[i][1], value_i = events[i][2], we have 1 <= start_i <= end_i <= 1000000000 and 1 <= value_i <= 1000000. Additionally, for every pair of distinct indices i,j with 0 <= i < n and 0 <= j < n, either end_i < start_j or end_j < start_i. -/
  theorem spec_11 (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events)
      (hall : ∀ i j, i < events.val.length → j < events.val.length → i ≠ j →
        Compatible events i j)
      (p q : ℕ)
      (hp : p < events.val.length)
      (hpv : ∀ i, i < events.val.length → valueOf events i ≤ valueOf events p)
      (hq : q < events.val.length) (hqp : q ≠ p)
      (hqv : ∀ i, i < events.val.length → i ≠ p → valueOf events i ≤ valueOf events q) :
      ∀ r, max_two_events events = ok r → r.val = valueOf events p + valueOf events q := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events)
        (hall : ∀ i j, i < events.val.length → j < events.val.length → i ≠ j →
          Compatible events i j)
        (p q : ℕ)
        (hp : p < events.val.length)
        (hpv : ∀ i, i < events.val.length → valueOf events i ≤ valueOf events p)
        (hq : q < events.val.length) (hqp : q ≠ p)
        (hqv : ∀ i, i < events.val.length → i ≠ p → valueOf events i ≤ valueOf events q), ∀ r, max_two_events events = ok r → r.val = valueOf events p + valueOf events q) := by
    sorry

  /-- Whenever the function returns a result r, if end_0 < start_1 or end_1 < start_0 then r = value_0 + value_1; otherwise r = max(value_0, value_1).
    Preconditions: events has length n with 2 <= n <= 100000. For every i with 0 <= i < n, events[i] has length 3; writing start_i = events[i][0], end_i = events[i][1], value_i = events[i][2], we have 1 <= start_i <= end_i <= 1000000000 and 1 <= value_i <= 1000000. Additionally, n = 2. -/
  theorem spec_12 (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events)
      (hlen : events.val.length = 2) :
      ∀ r, max_two_events events = ok r →
        (Compatible events 0 1 → r.val = valueOf events 0 + valueOf events 1) ∧
        (¬ Compatible events 0 1 → r.val = max (valueOf events 0) (valueOf events 1)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (events : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput events)
        (hlen : events.val.length = 2), ∀ r, max_two_events events = ok r →
          (Compatible events 0 1 → r.val = valueOf events 0 + valueOf events 1) ∧
          (¬ Compatible events 0 1 → r.val = max (valueOf events 0) (valueOf events 1))) := by
    sorry

  end AegisSpec.MaxTwoEvents
