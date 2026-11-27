import Aegis.MinProcessingTime.Code.Funs

/-!
# Specifications of `Aegis.MinProcessingTime.min_processing_time`

LeetCode problem `minimum-processing-time`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinProcessingTime

  namespace AegisSpec.MinProcessingTime

  def tasksAt (tasks : Slice I64) (f : Nat → Nat) (p : Nat) : Finset Nat :=
    (Finset.range tasks.val.length).filter (fun j => f j = p)

  def ValidAssignment (processorTime tasks : Slice I64) (f : Nat → Nat) : Prop :=
    (∀ j, j < tasks.val.length → f j < processorTime.val.length) ∧
      ∀ p, p < processorTime.val.length → (tasksAt tasks f p).card = 4

  def maxTaskAt (tasks : Slice I64) (f : Nat → Nat) (p : Nat)
      (h : (tasksAt tasks f p).Nonempty) : Int :=
    (tasksAt tasks f p).attach.sup'
      (h.elim fun j hj => ⟨⟨j, hj⟩, Finset.mem_attach _ _⟩)
      (fun j => (tasks.val.get ⟨j.1, Finset.mem_range.mp (Finset.mem_filter.mp j.2).1⟩).val)

  def completion (processorTime tasks : Slice I64) (f : Nat → Nat)
      (hn : 0 < processorTime.val.length)
      (hne : ∀ p, p < processorTime.val.length → (tasksAt tasks f p).Nonempty) : Int :=
    (Finset.range processorTime.val.length).attach.sup'
      ⟨⟨0, Finset.mem_range.mpr hn⟩, Finset.mem_attach _ _⟩
      (fun p =>
        (processorTime.val.get ⟨p.1, Finset.mem_range.mp p.2⟩).val +
          maxTaskAt tasks f p.1 (hne p.1 (Finset.mem_range.mp p.2)))

  def sliceMax (a : Slice I64) (h : 0 < a.val.length) : Int :=
    (Finset.range a.val.length).attach.sup'
      ⟨⟨0, Finset.mem_range.mpr h⟩, Finset.mem_attach _ _⟩
      (fun i => (a.val.get ⟨i.1, Finset.mem_range.mp i.2⟩).val)

  def sliceMin (a : Slice I64) (h : 0 < a.val.length) : Int :=
    (Finset.range a.val.length).attach.inf'
      ⟨⟨0, Finset.mem_range.mpr h⟩, Finset.mem_attach _ _⟩
      (fun i => (a.val.get ⟨i.1, Finset.mem_range.mp i.2⟩).val)

  def pairedMax (ps ts : Slice I64) (h : 0 < ps.val.length)
      (hlen : ts.val.length = 4 * ps.val.length) : Int :=
    (Finset.range ps.val.length).attach.sup'
      ⟨⟨0, Finset.mem_range.mpr h⟩, Finset.mem_attach _ _⟩
      (fun i =>
        (ps.val.get ⟨i.1, Finset.mem_range.mp i.2⟩).val +
          (ts.val.get ⟨4 * i.1, by
            have hi : i.1 < ps.val.length := Finset.mem_range.mp i.2
            omega⟩).val)

  def SortedNondecreasing (l : List I64) : Prop :=
    l.Pairwise (fun x y => x.val ≤ y.val)

  def SortedNonincreasing (l : List I64) : Prop :=
    l.Pairwise (fun x y => y.val ≤ x.val)

  def IsPermutationOf (b a : Slice I64) : Prop :=
    b.val.Perm a.val

  theorem tasksAt_nonempty_of_valid {processorTime tasks : Slice I64} {f : Nat → Nat}
      (h : ValidAssignment processorTime tasks f) {p : Nat}
      (hp : p < processorTime.val.length) : (tasksAt tasks f p).Nonempty := by
    have hc : 0 < (tasksAt tasks f p).card := by
      rw [h.2 p hp]
      norm_num
    exact Finset.card_pos.mp hc

  /-- Let a = processorTime and t = tasks. A valid assignment is a function f from task indices {0,...,m-1} to processor indices {0,...,n-1} such that for every p with 0 <= p < n, exactly 4 task indices j satisfy f(j)=p. For a valid assignment f define C(f) = max_{0 <= p < n} ( a[p] + max_{0 <= j < m, f(j)=p} t[j] ). The function returns a result r and r = min { C(f) | f is a valid assignment }.
    Preconditions: Let n = len(processorTime) and m = len(tasks). Assume 1 <= n <= 25000, m = 4*n, for every i with 0 <= i < n, 0 <= processorTime[i] <= 10^9, and for every j with 0 <= j < m, 1 <= tasks[j] <= 10^9. -/
  theorem spec_1 (processorTime tasks : Slice I64)
      (hn_pos : 1 ≤ processorTime.val.length)
      (hn_le : processorTime.val.length ≤ 25000)
      (hm_len : tasks.val.length = 4 * processorTime.val.length)
      (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
        0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
      (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
        1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9) :
      ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
        IsLeast {v : Int | ∃ (f : Nat → Nat) (hf : ValidAssignment processorTime tasks f),
          completion processorTime tasks f (by omega)
            (fun p hp => tasksAt_nonempty_of_valid hf hp) = v} r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (processorTime tasks : Slice I64)
        (hn_pos : 1 ≤ processorTime.val.length)
        (hn_le : processorTime.val.length ≤ 25000)
        (hm_len : tasks.val.length = 4 * processorTime.val.length)
        (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
          0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
        (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
          1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9), ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
          IsLeast {v : Int | ∃ (f : Nat → Nat) (hf : ValidAssignment processorTime tasks f),
            completion processorTime tasks f (by omega)
              (fun p hp => tasksAt_nonempty_of_valid hf hp) = v} r.val) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or overflow on any input satisfying the preconditions.
    Preconditions: Let n = len(processorTime) and m = len(tasks). Assume 1 <= n <= 25000, m = 4*n, for every i with 0 <= i < n, 0 <= processorTime[i] <= 10^9, and for every j with 0 <= j < m, 1 <= tasks[j] <= 10^9. -/
  theorem spec_2 (processorTime tasks : Slice I64)
      (hn_pos : 1 ≤ processorTime.val.length)
      (hn_le : processorTime.val.length ≤ 25000)
      (hm_len : tasks.val.length = 4 * processorTime.val.length)
      (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
        0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
      (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
        1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9) :
      ∃ r : I64, min_processing_time processorTime tasks = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (processorTime tasks : Slice I64)
        (hn_pos : 1 ≤ processorTime.val.length)
        (hn_le : processorTime.val.length ≤ 25000)
        (hm_len : tasks.val.length = 4 * processorTime.val.length)
        (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
          0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
        (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
          1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9), ∃ r : I64, min_processing_time processorTime tasks = ok r) := by
    sorry

  /-- Let r be the result. Then r >= (max_{0 <= i < n} processorTime[i]) + (min_{0 <= j < m} tasks[j]).
    Preconditions: Let n = len(processorTime) and m = len(tasks). Assume 1 <= n <= 25000, m = 4*n, for every i with 0 <= i < n, 0 <= processorTime[i] <= 10^9, and for every j with 0 <= j < m, 1 <= tasks[j] <= 10^9. -/
  theorem spec_3 (processorTime tasks : Slice I64)
      (hn_pos : 1 ≤ processorTime.val.length)
      (hn_le : processorTime.val.length ≤ 25000)
      (hm_len : tasks.val.length = 4 * processorTime.val.length)
      (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
        0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
      (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
        1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9) :
      ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
        sliceMax processorTime (by omega) + sliceMin tasks (by omega) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (processorTime tasks : Slice I64)
        (hn_pos : 1 ≤ processorTime.val.length)
        (hn_le : processorTime.val.length ≤ 25000)
        (hm_len : tasks.val.length = 4 * processorTime.val.length)
        (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
          0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
        (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
          1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9), ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
          sliceMax processorTime (by omega) + sliceMin tasks (by omega) ≤ r.val) := by
    sorry

  /-- Let r be the result. Then r >= (min_{0 <= i < n} processorTime[i]) + (max_{0 <= j < m} tasks[j]).
    Preconditions: Let n = len(processorTime) and m = len(tasks). Assume 1 <= n <= 25000, m = 4*n, for every i with 0 <= i < n, 0 <= processorTime[i] <= 10^9, and for every j with 0 <= j < m, 1 <= tasks[j] <= 10^9. -/
  theorem spec_4 (processorTime tasks : Slice I64)
      (hn_pos : 1 ≤ processorTime.val.length)
      (hn_le : processorTime.val.length ≤ 25000)
      (hm_len : tasks.val.length = 4 * processorTime.val.length)
      (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
        0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
      (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
        1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9) :
      ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
        sliceMin processorTime (by omega) + sliceMax tasks (by omega) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (processorTime tasks : Slice I64)
        (hn_pos : 1 ≤ processorTime.val.length)
        (hn_le : processorTime.val.length ≤ 25000)
        (hm_len : tasks.val.length = 4 * processorTime.val.length)
        (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
          0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
        (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
          1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9), ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
          sliceMin processorTime (by omega) + sliceMax tasks (by omega) ≤ r.val) := by
    sorry

  /-- Let r be the result. Then r <= (max_{0 <= i < n} processorTime[i]) + (max_{0 <= j < m} tasks[j]).
    Preconditions: Let n = len(processorTime) and m = len(tasks). Assume 1 <= n <= 25000, m = 4*n, for every i with 0 <= i < n, 0 <= processorTime[i] <= 10^9, and for every j with 0 <= j < m, 1 <= tasks[j] <= 10^9. -/
  theorem spec_5 (processorTime tasks : Slice I64)
      (hn_pos : 1 ≤ processorTime.val.length)
      (hn_le : processorTime.val.length ≤ 25000)
      (hm_len : tasks.val.length = 4 * processorTime.val.length)
      (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
        0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
      (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
        1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9) :
      ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
        r.val ≤ sliceMax processorTime (by omega) + sliceMax tasks (by omega) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (processorTime tasks : Slice I64)
        (hn_pos : 1 ≤ processorTime.val.length)
        (hn_le : processorTime.val.length ≤ 25000)
        (hm_len : tasks.val.length = 4 * processorTime.val.length)
        (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
          0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
        (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
          1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9), ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
          r.val ≤ sliceMax processorTime (by omega) + sliceMax tasks (by omega)) := by
    sorry

  /-- If n = 1, then the result r equals processorTime[0] + (max_{0 <= j < m} tasks[j]).
    Preconditions: Let n = len(processorTime) and m = len(tasks). Assume 1 <= n <= 25000, m = 4*n, for every i with 0 <= i < n, 0 <= processorTime[i] <= 10^9, and for every j with 0 <= j < m, 1 <= tasks[j] <= 10^9. -/
  theorem spec_6 (processorTime tasks : Slice I64)
      (hn_pos : 1 ≤ processorTime.val.length)
      (hn_le : processorTime.val.length ≤ 25000)
      (hm_len : tasks.val.length = 4 * processorTime.val.length)
      (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
        0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
      (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
        1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9)
      (hn : processorTime.val.length = 1) :
      ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
        r.val = (processorTime.val.get ⟨0, by omega⟩).val + sliceMax tasks (by omega) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (processorTime tasks : Slice I64)
        (hn_pos : 1 ≤ processorTime.val.length)
        (hn_le : processorTime.val.length ≤ 25000)
        (hm_len : tasks.val.length = 4 * processorTime.val.length)
        (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
          0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
        (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
          1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9)
        (hn : processorTime.val.length = 1), ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
          r.val = (processorTime.val.get ⟨0, by omega⟩).val + sliceMax tasks (by omega)) := by
    sorry

  /-- If there is an integer c such that tasks[j] = c for every j with 0 <= j < m, then the result r equals (max_{0 <= i < n} processorTime[i]) + c.
    Preconditions: Let n = len(processorTime) and m = len(tasks). Assume 1 <= n <= 25000, m = 4*n, for every i with 0 <= i < n, 0 <= processorTime[i] <= 10^9, and for every j with 0 <= j < m, 1 <= tasks[j] <= 10^9. -/
  theorem spec_7 (processorTime tasks : Slice I64)
      (hn_pos : 1 ≤ processorTime.val.length)
      (hn_le : processorTime.val.length ≤ 25000)
      (hm_len : tasks.val.length = 4 * processorTime.val.length)
      (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
        0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
      (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
        1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9)
      (c : Int) (htc : ∀ (j : Nat) (hj : j < tasks.val.length), (tasks.val[j]).val = c) :
      ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
        r.val = sliceMax processorTime (by omega) + c := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (processorTime tasks : Slice I64)
        (hn_pos : 1 ≤ processorTime.val.length)
        (hn_le : processorTime.val.length ≤ 25000)
        (hm_len : tasks.val.length = 4 * processorTime.val.length)
        (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
          0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
        (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
          1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9)
        (c : Int) (htc : ∀ (j : Nat) (hj : j < tasks.val.length), (tasks.val[j]).val = c), ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
          r.val = sliceMax processorTime (by omega) + c) := by
    sorry

  /-- If there is an integer a such that processorTime[i] = a for every i with 0 <= i < n, then the result r equals a + (max_{0 <= j < m} tasks[j]).
    Preconditions: Let n = len(processorTime) and m = len(tasks). Assume 1 <= n <= 25000, m = 4*n, for every i with 0 <= i < n, 0 <= processorTime[i] <= 10^9, and for every j with 0 <= j < m, 1 <= tasks[j] <= 10^9. -/
  theorem spec_8 (processorTime tasks : Slice I64)
      (hn_pos : 1 ≤ processorTime.val.length)
      (hn_le : processorTime.val.length ≤ 25000)
      (hm_len : tasks.val.length = 4 * processorTime.val.length)
      (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
        0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
      (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
        1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9)
      (a : Int) (hpa : ∀ (i : Nat) (hi : i < processorTime.val.length),
        (processorTime.val[i]).val = a) :
      ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
        r.val = a + sliceMax tasks (by omega) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (processorTime tasks : Slice I64)
        (hn_pos : 1 ≤ processorTime.val.length)
        (hn_le : processorTime.val.length ≤ 25000)
        (hm_len : tasks.val.length = 4 * processorTime.val.length)
        (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
          0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
        (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
          1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9)
        (a : Int) (hpa : ∀ (i : Nat) (hi : i < processorTime.val.length),
          (processorTime.val[i]).val = a), ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
          r.val = a + sliceMax tasks (by omega)) := by
    sorry

  /-- Let r be the result. There exist indices p with 0 <= p < n and j with 0 <= j < m such that r = processorTime[p] + tasks[j].
    Preconditions: Let n = len(processorTime) and m = len(tasks). Assume 1 <= n <= 25000, m = 4*n, for every i with 0 <= i < n, 0 <= processorTime[i] <= 10^9, and for every j with 0 <= j < m, 1 <= tasks[j] <= 10^9. -/
  theorem spec_9 (processorTime tasks : Slice I64)
      (hn_pos : 1 ≤ processorTime.val.length)
      (hn_le : processorTime.val.length ≤ 25000)
      (hm_len : tasks.val.length = 4 * processorTime.val.length)
      (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
        0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
      (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
        1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9) :
      ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
        ∃ (p : Nat) (hp : p < processorTime.val.length)
          (j : Nat) (hj : j < tasks.val.length),
          r.val = (processorTime.val[p]).val + (tasks.val[j]).val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (processorTime tasks : Slice I64)
        (hn_pos : 1 ≤ processorTime.val.length)
        (hn_le : processorTime.val.length ≤ 25000)
        (hm_len : tasks.val.length = 4 * processorTime.val.length)
        (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
          0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
        (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
          1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9), ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
          ∃ (p : Nat) (hp : p < processorTime.val.length)
            (j : Nat) (hj : j < tasks.val.length),
            r.val = (processorTime.val[p]).val + (tasks.val[j]).val) := by
    sorry

  /-- Let r be the result. Define a valid assignment f and its completion C(f) as in spec_1: f maps task indices {0,...,m-1} to processor indices {0,...,n-1} with exactly four task indices mapped to each processor, and C(f) = max_{0 <= p < n} ( processorTime[p] + max_{0 <= j < m, f(j)=p} tasks[j] ). Then there exists a valid assignment f with C(f) = r such that for every p,q with 0 <= p,q < n and processorTime[p] < processorTime[q], and every j,k with 0 <= j,k < m, f(j)=p and f(k)=q imply tasks[j] >= tasks[k].
    Preconditions: Let n = len(processorTime) and m = len(tasks). Assume 1 <= n <= 25000, m = 4*n, for every i with 0 <= i < n, 0 <= processorTime[i] <= 10^9, and for every j with 0 <= j < m, 1 <= tasks[j] <= 10^9. -/
  theorem spec_10 (processorTime tasks : Slice I64)
      (hn_pos : 1 ≤ processorTime.val.length)
      (hn_le : processorTime.val.length ≤ 25000)
      (hm_len : tasks.val.length = 4 * processorTime.val.length)
      (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
        0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
      (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
        1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9) :
      ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
        ∃ (f : Nat → Nat) (hf : ValidAssignment processorTime tasks f),
          completion processorTime tasks f (by omega)
            (fun p hp => tasksAt_nonempty_of_valid hf hp) = r.val ∧
          ∀ (p q : Nat) (hp : p < processorTime.val.length)
            (hq : q < processorTime.val.length),
            (processorTime.val[p]).val < (processorTime.val[q]).val →
            ∀ (j k : Nat) (hj : j < tasks.val.length) (hk : k < tasks.val.length),
              f j = p → f k = q → (tasks.val[k]).val ≤ (tasks.val[j]).val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (processorTime tasks : Slice I64)
        (hn_pos : 1 ≤ processorTime.val.length)
        (hn_le : processorTime.val.length ≤ 25000)
        (hm_len : tasks.val.length = 4 * processorTime.val.length)
        (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
          0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
        (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
          1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9), ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
          ∃ (f : Nat → Nat) (hf : ValidAssignment processorTime tasks f),
            completion processorTime tasks f (by omega)
              (fun p hp => tasksAt_nonempty_of_valid hf hp) = r.val ∧
            ∀ (p q : Nat) (hp : p < processorTime.val.length)
              (hq : q < processorTime.val.length),
              (processorTime.val[p]).val < (processorTime.val[q]).val →
              ∀ (j k : Nat) (hj : j < tasks.val.length) (hk : k < tasks.val.length),
                f j = p → f k = q → (tasks.val[k]).val ≤ (tasks.val[j]).val) := by
    sorry

  /-- Let r be the result on the given input. For every slice b with len(b) = n such that b is a permutation of processorTime (there is a bijection pi on {0,...,n-1} with b[i] = processorTime[pi(i)] for all i), the call min_processing_time(b, tasks) returns the same value r.
    Preconditions: Let n = len(processorTime) and m = len(tasks). Assume 1 <= n <= 25000, m = 4*n, for every i with 0 <= i < n, 0 <= processorTime[i] <= 10^9, and for every j with 0 <= j < m, 1 <= tasks[j] <= 10^9. -/
  theorem spec_11 (processorTime tasks : Slice I64)
      (hn_pos : 1 ≤ processorTime.val.length)
      (hn_le : processorTime.val.length ≤ 25000)
      (hm_len : tasks.val.length = 4 * processorTime.val.length)
      (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
        0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
      (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
        1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9) :
      ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
        ∀ b : Slice I64, b.val.length = processorTime.val.length →
          IsPermutationOf b processorTime → min_processing_time b tasks = ok r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (processorTime tasks : Slice I64)
        (hn_pos : 1 ≤ processorTime.val.length)
        (hn_le : processorTime.val.length ≤ 25000)
        (hm_len : tasks.val.length = 4 * processorTime.val.length)
        (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
          0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
        (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
          1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9), ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
          ∀ b : Slice I64, b.val.length = processorTime.val.length →
            IsPermutationOf b processorTime → min_processing_time b tasks = ok r) := by
    sorry

  /-- Let r be the result on the given input. For every slice c with len(c) = m such that c is a permutation of tasks (there is a bijection pi on {0,...,m-1} with c[j] = tasks[pi(j)] for all j), the call min_processing_time(processorTime, c) returns the same value r.
    Preconditions: Let n = len(processorTime) and m = len(tasks). Assume 1 <= n <= 25000, m = 4*n, for every i with 0 <= i < n, 0 <= processorTime[i] <= 10^9, and for every j with 0 <= j < m, 1 <= tasks[j] <= 10^9. -/
  theorem spec_12 (processorTime tasks : Slice I64)
      (hn_pos : 1 ≤ processorTime.val.length)
      (hn_le : processorTime.val.length ≤ 25000)
      (hm_len : tasks.val.length = 4 * processorTime.val.length)
      (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
        0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
      (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
        1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9) :
      ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
        ∀ c : Slice I64, c.val.length = tasks.val.length →
          IsPermutationOf c tasks → min_processing_time processorTime c = ok r := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (processorTime tasks : Slice I64)
        (hn_pos : 1 ≤ processorTime.val.length)
        (hn_le : processorTime.val.length ≤ 25000)
        (hm_len : tasks.val.length = 4 * processorTime.val.length)
        (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
          0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
        (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
          1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9), ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
          ∀ c : Slice I64, c.val.length = tasks.val.length →
            IsPermutationOf c tasks → min_processing_time processorTime c = ok r) := by
    sorry

  /-- Let r be the result on the given input. For every slice b with len(b) = n satisfying 0 <= b[i] <= 10^9 for all i and b[i] >= processorTime[i] for all i, if r_b is the result of min_processing_time(b, tasks), then r_b >= r.
    Preconditions: Let n = len(processorTime) and m = len(tasks). Assume 1 <= n <= 25000, m = 4*n, for every i with 0 <= i < n, 0 <= processorTime[i] <= 10^9, and for every j with 0 <= j < m, 1 <= tasks[j] <= 10^9. -/
  theorem spec_13 (processorTime tasks : Slice I64)
      (hn_pos : 1 ≤ processorTime.val.length)
      (hn_le : processorTime.val.length ≤ 25000)
      (hm_len : tasks.val.length = 4 * processorTime.val.length)
      (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
        0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
      (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
        1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9) :
      ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
        ∀ (b : Slice I64), b.val.length = processorTime.val.length →
          (∀ (i : Nat) (hi : i < b.val.length),
            0 ≤ (b.val[i]).val ∧ (b.val[i]).val ≤ 10 ^ 9) →
          (∀ (i : Nat) (hi : i < processorTime.val.length) (hi' : i < b.val.length),
            (processorTime.val[i]).val ≤ (b.val[i]).val) →
          ∀ r_b : I64, min_processing_time b tasks = ok r_b → r.val ≤ r_b.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (processorTime tasks : Slice I64)
        (hn_pos : 1 ≤ processorTime.val.length)
        (hn_le : processorTime.val.length ≤ 25000)
        (hm_len : tasks.val.length = 4 * processorTime.val.length)
        (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
          0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
        (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
          1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9), ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
          ∀ (b : Slice I64), b.val.length = processorTime.val.length →
            (∀ (i : Nat) (hi : i < b.val.length),
              0 ≤ (b.val[i]).val ∧ (b.val[i]).val ≤ 10 ^ 9) →
            (∀ (i : Nat) (hi : i < processorTime.val.length) (hi' : i < b.val.length),
              (processorTime.val[i]).val ≤ (b.val[i]).val) →
            ∀ r_b : I64, min_processing_time b tasks = ok r_b → r.val ≤ r_b.val) := by
    sorry

  /-- Let r be the result on the given input. For every slice c with len(c) = m satisfying 1 <= c[j] <= 10^9 for all j and c[j] >= tasks[j] for all j, if r_c is the result of min_processing_time(processorTime, c), then r_c >= r.
    Preconditions: Let n = len(processorTime) and m = len(tasks). Assume 1 <= n <= 25000, m = 4*n, for every i with 0 <= i < n, 0 <= processorTime[i] <= 10^9, and for every j with 0 <= j < m, 1 <= tasks[j] <= 10^9. -/
  theorem spec_14 (processorTime tasks : Slice I64)
      (hn_pos : 1 ≤ processorTime.val.length)
      (hn_le : processorTime.val.length ≤ 25000)
      (hm_len : tasks.val.length = 4 * processorTime.val.length)
      (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
        0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
      (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
        1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9) :
      ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
        ∀ (c : Slice I64), c.val.length = tasks.val.length →
          (∀ (j : Nat) (hj : j < c.val.length),
            1 ≤ (c.val[j]).val ∧ (c.val[j]).val ≤ 10 ^ 9) →
          (∀ (j : Nat) (hj : j < tasks.val.length) (hj' : j < c.val.length),
            (tasks.val[j]).val ≤ (c.val[j]).val) →
          ∀ r_c : I64, min_processing_time processorTime c = ok r_c → r.val ≤ r_c.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (processorTime tasks : Slice I64)
        (hn_pos : 1 ≤ processorTime.val.length)
        (hn_le : processorTime.val.length ≤ 25000)
        (hm_len : tasks.val.length = 4 * processorTime.val.length)
        (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
          0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
        (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
          1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9), ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
          ∀ (c : Slice I64), c.val.length = tasks.val.length →
            (∀ (j : Nat) (hj : j < c.val.length),
              1 ≤ (c.val[j]).val ∧ (c.val[j]).val ≤ 10 ^ 9) →
            (∀ (j : Nat) (hj : j < tasks.val.length) (hj' : j < c.val.length),
              (tasks.val[j]).val ≤ (c.val[j]).val) →
            ∀ r_c : I64, min_processing_time processorTime c = ok r_c → r.val ≤ r_c.val) := by
    sorry

  /-- Let ps be a slice of length n that is a permutation of processorTime and is sorted nondecreasing, and let ts be a slice of length m that is a permutation of tasks and is sorted nonincreasing. Then the result r equals max_{0 <= i < n} (ps[i] + ts[4*i]).
    Preconditions: Let n = len(processorTime) and m = len(tasks). Assume 1 <= n <= 25000, m = 4*n, for every i with 0 <= i < n, 0 <= processorTime[i] <= 10^9, and for every j with 0 <= j < m, 1 <= tasks[j] <= 10^9. -/
  theorem spec_15 (processorTime tasks : Slice I64)
      (hn_pos : 1 ≤ processorTime.val.length)
      (hn_le : processorTime.val.length ≤ 25000)
      (hm_len : tasks.val.length = 4 * processorTime.val.length)
      (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
        0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
      (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
        1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9) :
      ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
        ∀ (ps ts : Slice I64) (hps_len : ps.val.length = processorTime.val.length)
          (hperm_ps : IsPermutationOf ps processorTime) (hsorted_ps : SortedNondecreasing ps.val)
          (hts_len : ts.val.length = tasks.val.length)
          (hperm_ts : IsPermutationOf ts tasks) (hsorted_ts : SortedNonincreasing ts.val),
          r.val = pairedMax ps ts (by omega) (by omega) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (processorTime tasks : Slice I64)
        (hn_pos : 1 ≤ processorTime.val.length)
        (hn_le : processorTime.val.length ≤ 25000)
        (hm_len : tasks.val.length = 4 * processorTime.val.length)
        (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
          0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
        (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
          1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9), ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
          ∀ (ps ts : Slice I64) (hps_len : ps.val.length = processorTime.val.length)
            (hperm_ps : IsPermutationOf ps processorTime) (hsorted_ps : SortedNondecreasing ps.val)
            (hts_len : ts.val.length = tasks.val.length)
            (hperm_ts : IsPermutationOf ts tasks) (hsorted_ts : SortedNonincreasing ts.val),
            r.val = pairedMax ps ts (by omega) (by omega)) := by
    sorry

  /-- Let b be the slice of length n with b[i] = processorTime[i] + c for every i. If r is the result on (processorTime, tasks) and r_b is the result on (b, tasks), then r_b = r + c.
    Preconditions: Let n = len(processorTime) and m = len(tasks). Assume 1 <= n <= 25000, m = 4*n, for every i with 0 <= i < n, 0 <= processorTime[i] <= 10^9, and for every j with 0 <= j < m, 1 <= tasks[j] <= 10^9. Let c be an integer with 0 <= c <= 10^9 - max_{0 <= i < n} processorTime[i]. -/
  theorem spec_16 (processorTime tasks : Slice I64)
      (hn_pos : 1 ≤ processorTime.val.length)
      (hn_le : processorTime.val.length ≤ 25000)
      (hm_len : tasks.val.length = 4 * processorTime.val.length)
      (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
        0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
      (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
        1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9) :
      ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
        ∀ (c : Int), 0 ≤ c → c ≤ 10 ^ 9 - sliceMax processorTime (by omega) →
          ∀ (b : Slice I64), b.val.length = processorTime.val.length →
            (∀ (i : Nat) (hi : i < processorTime.val.length) (hi' : i < b.val.length),
              (b.val[i]).val = (processorTime.val[i]).val + c) →
            ∀ r_b : I64, min_processing_time b tasks = ok r_b → r_b.val = r.val + c := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (processorTime tasks : Slice I64)
        (hn_pos : 1 ≤ processorTime.val.length)
        (hn_le : processorTime.val.length ≤ 25000)
        (hm_len : tasks.val.length = 4 * processorTime.val.length)
        (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
          0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
        (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
          1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9), ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
          ∀ (c : Int), 0 ≤ c → c ≤ 10 ^ 9 - sliceMax processorTime (by omega) →
            ∀ (b : Slice I64), b.val.length = processorTime.val.length →
              (∀ (i : Nat) (hi : i < processorTime.val.length) (hi' : i < b.val.length),
                (b.val[i]).val = (processorTime.val[i]).val + c) →
              ∀ r_b : I64, min_processing_time b tasks = ok r_b → r_b.val = r.val + c) := by
    sorry

  /-- Let d be the slice of length m with d[j] = tasks[j] + c for every j. If r is the result on (processorTime, tasks) and r_d is the result on (processorTime, d), then r_d = r + c.
    Preconditions: Let n = len(processorTime) and m = len(tasks). Assume 1 <= n <= 25000, m = 4*n, for every i with 0 <= i < n, 0 <= processorTime[i] <= 10^9, and for every j with 0 <= j < m, 1 <= tasks[j] <= 10^9. Let c be an integer with 0 <= c <= 10^9 - max_{0 <= j < m} tasks[j]. -/
  theorem spec_17 (processorTime tasks : Slice I64)
      (hn_pos : 1 ≤ processorTime.val.length)
      (hn_le : processorTime.val.length ≤ 25000)
      (hm_len : tasks.val.length = 4 * processorTime.val.length)
      (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
        0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
      (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
        1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9) :
      ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
        ∀ (c : Int), 0 ≤ c → c ≤ 10 ^ 9 - sliceMax tasks (by omega) →
          ∀ (d : Slice I64), d.val.length = tasks.val.length →
            (∀ (j : Nat) (hj : j < tasks.val.length) (hj' : j < d.val.length),
              (d.val[j]).val = (tasks.val[j]).val + c) →
            ∀ r_d : I64, min_processing_time processorTime d = ok r_d →
              r_d.val = r.val + c := by
    sorry

  theorem spec_17_neg :
      ¬ (∀ (processorTime tasks : Slice I64)
        (hn_pos : 1 ≤ processorTime.val.length)
        (hn_le : processorTime.val.length ≤ 25000)
        (hm_len : tasks.val.length = 4 * processorTime.val.length)
        (hproc : ∀ (i : Nat) (hi : i < processorTime.val.length),
          0 ≤ (processorTime.val[i]).val ∧ (processorTime.val[i]).val ≤ 10 ^ 9)
        (htask : ∀ (j : Nat) (hj : j < tasks.val.length),
          1 ≤ (tasks.val[j]).val ∧ (tasks.val[j]).val ≤ 10 ^ 9), ∃ r : I64, min_processing_time processorTime tasks = ok r ∧
          ∀ (c : Int), 0 ≤ c → c ≤ 10 ^ 9 - sliceMax tasks (by omega) →
            ∀ (d : Slice I64), d.val.length = tasks.val.length →
              (∀ (j : Nat) (hj : j < tasks.val.length) (hj' : j < d.val.length),
                (d.val[j]).val = (tasks.val[j]).val + c) →
              ∀ r_d : I64, min_processing_time processorTime d = ok r_d →
                r_d.val = r.val + c) := by
    sorry

  end AegisSpec.MinProcessingTime
