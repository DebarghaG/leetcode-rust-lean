import Aegis.TaskSchedulerIi.Code.Funs

/-!
# Specifications of `Aegis.TaskSchedulerIi.task_scheduler_ii`

LeetCode problem `task-scheduler-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.TaskSchedulerIi

  def taskValue (tasks : List Std.I64) (i : Nat) (hi : i < tasks.length) : Int :=
    (tasks.get ⟨i, hi⟩).val

  def occurrenceCount (tasks : List Std.I64) (v : Int) : Nat :=
    (tasks.filter (fun t => decide (t.val = v))).length

  def maxMultiplicity (tasks : List Std.I64) : Nat :=
    (tasks.map (fun t => occurrenceCount tasks t.val)).foldr max 0

  def adjacentEqualCount (tasks : List Std.I64) : Nat :=
    ((tasks.zip (tasks.drop 1)).filter (fun p => decide (p.1.val = p.2.val))).length

  def IsValidSchedule (tasks : List Std.I64) (space : Int)
      (d : Fin tasks.length → Int) : Prop :=
    (∀ i : Fin tasks.length, 1 ≤ d i) ∧
      (∀ i j : Fin tasks.length, i.val < j.val → d i < d j) ∧
        (∀ i j : Fin tasks.length, i.val < j.val →
          (tasks.get i).val = (tasks.get j).val → space + 1 ≤ d j - d i)

  def lastDay {n : Nat} (d : Fin n → Int) : Int :=
    if h : 0 < n then d ⟨n - 1, by omega⟩ else 0

  def IndexSpacingOk (tasks : List Std.I64) (space : Int) : Prop :=
    ∀ i j : Fin tasks.length, i.val < j.val →
      (tasks.get i).val = (tasks.get j).val → space + 1 ≤ (j.val : Int) - (i.val : Int)

  /-- The function returns a result r, and r is the minimum possible value of d_{n-1} over all valid completion-day assignments (d_0, ..., d_{n-1}) for tasks with spacing space. An assignment is valid when: (1) 1 <= d_0 < d_1 < ... < d_{n-1} (task i is completed on day d_i, one task per day, in the given order); and (2) for every i and j with 0 <= i < j < n and tasks[i] = tasks[j], we have d_j - d_i >= space + 1. Days are 1-based, and unassigned days in a schedule are breaks.
    Preconditions: Let n = len(tasks). The input satisfies 1 <= n <= 100000, 1 <= tasks[i] <= 10^9 for every i with 0 <= i < n, and 1 <= space <= n. -/
  theorem spec_1 (tasks : Slice Std.I64) (space : Std.I64)
      (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
      (hval : ∀ i (hi : i < tasks.val.length),
        1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
      (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int)) :
      ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
        (∃ d : Fin tasks.val.length → Int,
          IsValidSchedule tasks.val space.val d ∧ lastDay d = r.val) ∧
        (∀ d : Fin tasks.val.length → Int,
          IsValidSchedule tasks.val space.val d → r.val ≤ lastDay d) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (tasks : Slice Std.I64) (space : Std.I64)
        (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
        (hval : ∀ i (hi : i < tasks.val.length),
          1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
        (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int)), ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
          (∃ d : Fin tasks.val.length → Int,
            IsValidSchedule tasks.val space.val d ∧ lastDay d = r.val) ∧
          (∀ d : Fin tasks.val.length → Int,
            IsValidSchedule tasks.val space.val d → r.val ≤ lastDay d)) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or overflow for any input satisfying the preconditions.
    Preconditions: Let n = len(tasks). The input satisfies 1 <= n <= 100000, 1 <= tasks[i] <= 10^9 for every i with 0 <= i < n, and 1 <= space <= n. -/
  theorem spec_2 (tasks : Slice Std.I64) (space : Std.I64)
      (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
      (hval : ∀ i (hi : i < tasks.val.length),
        1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
      (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int)) :
      ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (tasks : Slice Std.I64) (space : Std.I64)
        (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
        (hval : ∀ i (hi : i < tasks.val.length),
          1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
        (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int)), ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r) := by
    sorry

  /-- The function returns a result r, and r >= n.
    Preconditions: Let n = len(tasks). The input satisfies 1 <= n <= 100000, 1 <= tasks[i] <= 10^9 for every i with 0 <= i < n, and 1 <= space <= n. -/
  theorem spec_3 (tasks : Slice Std.I64) (space : Std.I64)
      (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
      (hval : ∀ i (hi : i < tasks.val.length),
        1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
      (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int)) :
      ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
        (tasks.val.length : Int) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (tasks : Slice Std.I64) (space : Std.I64)
        (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
        (hval : ∀ i (hi : i < tasks.val.length),
          1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
        (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int)), ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
          (tasks.val.length : Int) ≤ r.val) := by
    sorry

  /-- The function returns a result r, and r <= n + (n - 1) * space.
    Preconditions: Let n = len(tasks). The input satisfies 1 <= n <= 100000, 1 <= tasks[i] <= 10^9 for every i with 0 <= i < n, and 1 <= space <= n. -/
  theorem spec_4 (tasks : Slice Std.I64) (space : Std.I64)
      (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
      (hval : ∀ i (hi : i < tasks.val.length),
        1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
      (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int)) :
      ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
        r.val ≤ (tasks.val.length : Int) + ((tasks.val.length : Int) - 1) * (space.val + 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (tasks : Slice Std.I64) (space : Std.I64)
        (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
        (hval : ∀ i (hi : i < tasks.val.length),
          1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
        (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int)), ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
          r.val ≤ (tasks.val.length : Int) + ((tasks.val.length : Int) - 1) * (space.val + 1)) := by
    sorry

  /-- The function returns a result r, and r >= 1 + (f - 1) * (space + 1), where f is the maximum, over all integer values v, of the number of indices i with 0 <= i < n and tasks[i] = v.
    Preconditions: Let n = len(tasks). The input satisfies 1 <= n <= 100000, 1 <= tasks[i] <= 10^9 for every i with 0 <= i < n, and 1 <= space <= n. -/
  theorem spec_5 (tasks : Slice Std.I64) (space : Std.I64)
      (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
      (hval : ∀ i (hi : i < tasks.val.length),
        1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
      (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int)) :
      ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
        (1 : Int) + ((maxMultiplicity tasks.val : Int) - 1) * (space.val + 1) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (tasks : Slice Std.I64) (space : Std.I64)
        (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
        (hval : ∀ i (hi : i < tasks.val.length),
          1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
        (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int)), ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
          (1 : Int) + ((maxMultiplicity tasks.val : Int) - 1) * (space.val + 1) ≤ r.val) := by
    sorry

  /-- The function returns a result r, and r = n if and only if for every i and j with 0 <= i < j < n and tasks[i] = tasks[j], we have j - i >= space + 1.
    Preconditions: Let n = len(tasks). The input satisfies 1 <= n <= 100000, 1 <= tasks[i] <= 10^9 for every i with 0 <= i < n, and 1 <= space <= n. -/
  theorem spec_6 (tasks : Slice Std.I64) (space : Std.I64)
      (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
      (hval : ∀ i (hi : i < tasks.val.length),
        1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
      (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int)) :
      ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
        (r.val = (tasks.val.length : Int) ↔ IndexSpacingOk tasks.val space.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (tasks : Slice Std.I64) (space : Std.I64)
        (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
        (hval : ∀ i (hi : i < tasks.val.length),
          1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
        (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int)), ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
          (r.val = (tasks.val.length : Int) ↔ IndexSpacingOk tasks.val space.val)) := by
    sorry

  /-- The function returns a result r, and r = 1 + (n - 1) * (space + 1).
    Preconditions: Let n = len(tasks). The input satisfies 1 <= n <= 100000, 1 <= tasks[i] <= 10^9 for every i with 0 <= i < n, 1 <= space <= n, and tasks[i] = tasks[0] for every i with 0 <= i < n. -/
  theorem spec_7 (tasks : Slice Std.I64) (space : Std.I64)
      (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
      (hval : ∀ i (hi : i < tasks.val.length),
        1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
      (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int))
      (hall : ∀ i (hi : i < tasks.val.length),
        taskValue tasks.val i hi = taskValue tasks.val 0 (by omega)) :
      ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
        r.val = 1 + ((tasks.val.length : Int) - 1) * (space.val + 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (tasks : Slice Std.I64) (space : Std.I64)
        (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
        (hval : ∀ i (hi : i < tasks.val.length),
          1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
        (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int))
        (hall : ∀ i (hi : i < tasks.val.length),
          taskValue tasks.val i hi = taskValue tasks.val 0 (by omega)), ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
          r.val = 1 + ((tasks.val.length : Int) - 1) * (space.val + 1)) := by
    sorry

  /-- The function returns a result r, and r = n + C, where C is the number of indices i with 0 <= i < n - 1 and tasks[i] = tasks[i + 1].
    Preconditions: Let n = len(tasks). The input satisfies 1 <= n <= 100000, 1 <= tasks[i] <= 10^9 for every i with 0 <= i < n, and space = 1. -/
  theorem spec_8 (tasks : Slice Std.I64) (space : Std.I64)
      (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
      (hval : ∀ i (hi : i < tasks.val.length),
        1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
      (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int))
      (hspace : space.val = 1) :
      ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
        r.val = (tasks.val.length : Int) + (adjacentEqualCount tasks.val : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (tasks : Slice Std.I64) (space : Std.I64)
        (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
        (hval : ∀ i (hi : i < tasks.val.length),
          1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
        (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int))
        (hspace : space.val = 1), ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
          r.val = (tasks.val.length : Int) + (adjacentEqualCount tasks.val : Int)) := by
    sorry

  /-- Consider two calls on the same tasks, one with space = s1 returning r1 and one with space = s2 returning r2. Both calls return results, and r1 <= r2.
    Preconditions: Let n = len(tasks). The input satisfies 1 <= n <= 100000, 1 <= tasks[i] <= 10^9 for every i with 0 <= i < n, and 1 <= s1 <= s2 <= n. -/
  theorem spec_9 (tasks : Slice Std.I64) (s1 s2 : Std.I64)
      (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
      (hval : ∀ i (hi : i < tasks.val.length),
        1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
      (hs1 : 1 ≤ s1.val) (hs12 : s1.val ≤ s2.val) (hs2 : s2.val ≤ (tasks.val.length : Int)) :
      ∃ r1 r2 : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks s1 = ok r1 ∧
        Aegis.TaskSchedulerIi.task_scheduler_ii tasks s2 = ok r2 ∧ r1.val ≤ r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (tasks : Slice Std.I64) (s1 s2 : Std.I64)
        (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
        (hval : ∀ i (hi : i < tasks.val.length),
          1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
        (hs1 : 1 ≤ s1.val) (hs12 : s1.val ≤ s2.val) (hs2 : s2.val ≤ (tasks.val.length : Int)), ∃ r1 r2 : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks s1 = ok r1 ∧
          Aegis.TaskSchedulerIi.task_scheduler_ii tasks s2 = ok r2 ∧ r1.val ≤ r2.val) := by
    sorry

  /-- The call on tasks with space returns r, the call on tasks' with the same space returns r', and r = r'.
    Preconditions: Let n = len(tasks). The input satisfies 1 <= n <= 100000, 1 <= tasks[i] <= 10^9 for every i with 0 <= i < n, and 1 <= space <= n. Let f be an injective function defined on the values appearing in tasks such that 1 <= f(v) <= 10^9 for each such value, and let tasks'[i] = f(tasks[i]) for 0 <= i < n. -/
  theorem spec_10 (tasks tasks' : Slice Std.I64) (space : Std.I64)
      (g : Std.I64 → Std.I64)
      (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
      (hval : ∀ i (hi : i < tasks.val.length),
        1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
      (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int))
      (hgval : ∀ a, a ∈ tasks.val → 1 ≤ (g a).val ∧ (g a).val ≤ 1000000000)
      (hginj : ∀ a b, a ∈ tasks.val → b ∈ tasks.val → g a = g b → a = b)
      (htasks' : tasks'.val = tasks.val.map g) :
      ∃ r r' : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
        Aegis.TaskSchedulerIi.task_scheduler_ii tasks' space = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (tasks tasks' : Slice Std.I64) (space : Std.I64)
        (g : Std.I64 → Std.I64)
        (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
        (hval : ∀ i (hi : i < tasks.val.length),
          1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
        (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int))
        (hgval : ∀ a, a ∈ tasks.val → 1 ≤ (g a).val ∧ (g a).val ≤ 1000000000)
        (hginj : ∀ a b, a ∈ tasks.val → b ∈ tasks.val → g a = g b → a = b)
        (htasks' : tasks'.val = tasks.val.map g), ∃ r r' : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
          Aegis.TaskSchedulerIi.task_scheduler_ii tasks' space = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- The call on tasks with space returns r, the call on tasks' with the same space returns r', and r' = r + 1.
    Preconditions: Let n = len(tasks). The input satisfies 1 <= n <= 99999, 1 <= tasks[i] <= 10^9 for every i with 0 <= i < n, and 1 <= space <= n. Let v satisfy 1 <= v <= 10^9 and v != tasks[i] for every i with 0 <= i < n. Let tasks' be tasks followed by v, so len(tasks') = n + 1. -/
  theorem spec_11 (tasks tasks' : Slice Std.I64) (space : Std.I64) (v : Std.I64)
      (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 99999)
      (hval : ∀ i (hi : i < tasks.val.length),
        1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
      (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int))
      (hv1 : 1 ≤ v.val) (hv2 : v.val ≤ 1000000000)
      (hfresh : ∀ i (hi : i < tasks.val.length), taskValue tasks.val i hi ≠ v.val)
      (htasks' : tasks'.val = tasks.val ++ [v]) :
      ∃ r r' : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
        Aegis.TaskSchedulerIi.task_scheduler_ii tasks' space = ok r' ∧ r'.val = r.val + 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (tasks tasks' : Slice Std.I64) (space : Std.I64) (v : Std.I64)
        (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 99999)
        (hval : ∀ i (hi : i < tasks.val.length),
          1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
        (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int))
        (hv1 : 1 ≤ v.val) (hv2 : v.val ≤ 1000000000)
        (hfresh : ∀ i (hi : i < tasks.val.length), taskValue tasks.val i hi ≠ v.val)
        (htasks' : tasks'.val = tasks.val ++ [v]), ∃ r r' : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
          Aegis.TaskSchedulerIi.task_scheduler_ii tasks' space = ok r' ∧ r'.val = r.val + 1) := by
    sorry

  /-- The function returns a result r, and there exists a valid completion-day assignment (d_0, ..., d_{n-1}) for tasks with spacing space such that d_{n-1} = r. Here valid means 1 <= d_0 < d_1 < ... < d_{n-1} and, for every i and j with 0 <= i < j < n and tasks[i] = tasks[j], d_j - d_i >= space + 1.
    Preconditions: Let n = len(tasks). The input satisfies 1 <= n <= 100000, 1 <= tasks[i] <= 10^9 for every i with 0 <= i < n, and 1 <= space <= n. -/
  theorem spec_12 (tasks : Slice Std.I64) (space : Std.I64)
      (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
      (hval : ∀ i (hi : i < tasks.val.length),
        1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
      (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int)) :
      ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
        ∃ d : Fin tasks.val.length → Int, IsValidSchedule tasks.val space.val d ∧ lastDay d = r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (tasks : Slice Std.I64) (space : Std.I64)
        (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
        (hval : ∀ i (hi : i < tasks.val.length),
          1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
        (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int)), ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
          ∃ d : Fin tasks.val.length → Int, IsValidSchedule tasks.val space.val d ∧ lastDay d = r.val) := by
    sorry

  /-- The function returns a result r, and for every valid completion-day assignment (d_0, ..., d_{n-1}) for tasks with spacing space, we have d_{n-1} >= r. Here valid means 1 <= d_0 < d_1 < ... < d_{n-1} and, for every i and j with 0 <= i < j < n and tasks[i] = tasks[j], d_j - d_i >= space + 1.
    Preconditions: Let n = len(tasks). The input satisfies 1 <= n <= 100000, 1 <= tasks[i] <= 10^9 for every i with 0 <= i < n, and 1 <= space <= n. -/
  theorem spec_13 (tasks : Slice Std.I64) (space : Std.I64)
      (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
      (hval : ∀ i (hi : i < tasks.val.length),
        1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
      (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int)) :
      ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
        ∀ d : Fin tasks.val.length → Int, IsValidSchedule tasks.val space.val d → r.val ≤ lastDay d := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (tasks : Slice Std.I64) (space : Std.I64)
        (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
        (hval : ∀ i (hi : i < tasks.val.length),
          1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
        (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int)), ∃ r : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
          ∀ d : Fin tasks.val.length → Int, IsValidSchedule tasks.val space.val d → r.val ≤ lastDay d) := by
    sorry

  /-- The call on tasks with space returns r, the call on prefix with the same space returns r_p, and r_p <= r.
    Preconditions: Let n = len(tasks). The input satisfies 1 <= n <= 100000, 1 <= tasks[i] <= 10^9 for every i with 0 <= i < n, and 1 <= space <= n. Let k be an integer with 1 <= k <= n and space <= k, and let prefix be the array consisting of tasks[0], ..., tasks[k-1]. -/
  theorem spec_14 (tasks pref : Slice Std.I64) (space : Std.I64) (k : Nat)
      (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
      (hval : ∀ i (hi : i < tasks.val.length),
        1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
      (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int))
      (hk1 : 1 ≤ k) (hk2 : k ≤ tasks.val.length) (hks : space.val ≤ (k : Int))
      (hpref : pref.val = tasks.val.take k) :
      ∃ r rp : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
        Aegis.TaskSchedulerIi.task_scheduler_ii pref space = ok rp ∧ rp.val ≤ r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (tasks pref : Slice Std.I64) (space : Std.I64) (k : Nat)
        (hn1 : 1 ≤ tasks.val.length) (hn2 : tasks.val.length ≤ 100000)
        (hval : ∀ i (hi : i < tasks.val.length),
          1 ≤ taskValue tasks.val i hi ∧ taskValue tasks.val i hi ≤ 1000000000)
        (hs1 : 1 ≤ space.val) (hs2 : space.val ≤ (tasks.val.length : Int))
        (hk1 : 1 ≤ k) (hk2 : k ≤ tasks.val.length) (hks : space.val ≤ (k : Int))
        (hpref : pref.val = tasks.val.take k), ∃ r rp : Std.I64, Aegis.TaskSchedulerIi.task_scheduler_ii tasks space = ok r ∧
          Aegis.TaskSchedulerIi.task_scheduler_ii pref space = ok rp ∧ rp.val ≤ r.val) := by
    sorry

  end AegisSpec.TaskSchedulerIi
