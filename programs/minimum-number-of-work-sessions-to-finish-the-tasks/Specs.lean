import Aegis.MinSessions.Code.Funs

/-!
# Specifications of `Aegis.MinSessions.min_sessions`

LeetCode problem `minimum-number-of-work-sessions-to-finish-the-tasks`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinSessions

  open scoped BigOperators

  def durations (tasks : Slice Std.I64) : List ℤ := tasks.val.map (fun t => t.val)

  def taskAt (ts : List ℤ) (i : ℕ) : ℤ := ts.getD i 0

  def totalWork (ts : List ℤ) : ℤ := ts.sum

  def load (ts : List ℤ) {k : ℕ} (g : Fin ts.length → Fin k) (j : Fin k) : ℤ :=
    ∑ i : Fin ts.length, if g i = j then ts.get i else 0

  def Feasible (ts : List ℤ) (st : ℤ) (k : ℕ) : Prop :=
    ∃ g : Fin ts.length → Fin k, Function.Surjective g ∧ ∀ j : Fin k, load ts g j ≤ st

  def IsMinSessions (ts : List ℤ) (st : ℤ) (k : ℕ) : Prop :=
    1 ≤ k ∧ Feasible ts st k ∧ ∀ k' : ℕ, 1 ≤ k' → k' < k → ¬ Feasible ts st k'

  /-- The function returns a result r, and r is the minimum integer k >= 1 such that there exist nonempty sets S_1, ..., S_k satisfying: (a) the sets S_1, ..., S_k are pairwise disjoint and their union is {0, 1, ..., len(tasks)-1}; and (b) for every j with 1 <= j <= k, sum_{i in S_j} tasks[i] <= sessionTime. Equivalently, r is the smallest number of work sessions needed to finish all tasks, where tasks may be grouped in any order, no task is split between sessions, and the total time in each session is at most sessionTime.
    Preconditions: 1 <= len(tasks) <= 14; for every i with 0 <= i < len(tasks), 1 <= tasks[i] <= 10 and tasks[i] <= sessionTime; and sessionTime <= 15. -/
  theorem spec_1 (tasks : Slice Std.I64) (sessionTime : Std.I64)
      (hlen : 1 ≤ (durations tasks).length)
      (hlen14 : (durations tasks).length ≤ 14)
      (htasks : ∀ i : ℕ, i < (durations tasks).length →
        1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
      (hfit : ∀ i : ℕ, i < (durations tasks).length →
        taskAt (durations tasks) i ≤ sessionTime.val)
      (hst : sessionTime.val ≤ 15) :
      ∃ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r ∧
        IsMinSessions (durations tasks) sessionTime.val r.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (tasks : Slice Std.I64) (sessionTime : Std.I64)
        (hlen : 1 ≤ (durations tasks).length)
        (hlen14 : (durations tasks).length ≤ 14)
        (htasks : ∀ i : ℕ, i < (durations tasks).length →
          1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
        (hfit : ∀ i : ℕ, i < (durations tasks).length →
          taskAt (durations tasks) i ≤ sessionTime.val)
        (hst : sessionTime.val ≤ 15), ∃ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r ∧
          IsMinSessions (durations tasks) sessionTime.val r.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r.
    Preconditions: 1 <= len(tasks) <= 14; for every i with 0 <= i < len(tasks), 1 <= tasks[i] <= 10 and tasks[i] <= sessionTime; and sessionTime <= 15. -/
  theorem spec_2 (tasks : Slice Std.I64) (sessionTime : Std.I64)
      (hlen : 1 ≤ (durations tasks).length)
      (hlen14 : (durations tasks).length ≤ 14)
      (htasks : ∀ i : ℕ, i < (durations tasks).length →
        1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
      (hfit : ∀ i : ℕ, i < (durations tasks).length →
        taskAt (durations tasks) i ≤ sessionTime.val)
      (hst : sessionTime.val ≤ 15) :
      ∀ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r → 1 ≤ r.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (tasks : Slice Std.I64) (sessionTime : Std.I64)
        (hlen : 1 ≤ (durations tasks).length)
        (hlen14 : (durations tasks).length ≤ 14)
        (htasks : ∀ i : ℕ, i < (durations tasks).length →
          1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
        (hfit : ∀ i : ℕ, i < (durations tasks).length →
          taskAt (durations tasks) i ≤ sessionTime.val)
        (hst : sessionTime.val ≤ 15), ∀ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r → 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= len(tasks).
    Preconditions: 1 <= len(tasks) <= 14; for every i with 0 <= i < len(tasks), 1 <= tasks[i] <= 10 and tasks[i] <= sessionTime; and sessionTime <= 15. -/
  theorem spec_3 (tasks : Slice Std.I64) (sessionTime : Std.I64)
      (hlen : 1 ≤ (durations tasks).length)
      (hlen14 : (durations tasks).length ≤ 14)
      (htasks : ∀ i : ℕ, i < (durations tasks).length →
        1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
      (hfit : ∀ i : ℕ, i < (durations tasks).length →
        taskAt (durations tasks) i ≤ sessionTime.val)
      (hst : sessionTime.val ≤ 15) :
      ∀ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r →
        r.val ≤ ((durations tasks).length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (tasks : Slice Std.I64) (sessionTime : Std.I64)
        (hlen : 1 ≤ (durations tasks).length)
        (hlen14 : (durations tasks).length ≤ 14)
        (htasks : ∀ i : ℕ, i < (durations tasks).length →
          1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
        (hfit : ∀ i : ℕ, i < (durations tasks).length →
          taskAt (durations tasks) i ≤ sessionTime.val)
        (hst : sessionTime.val ≤ 15), ∀ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r →
          r.val ≤ ((durations tasks).length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r * sessionTime >= sum_{i=0}^{len(tasks)-1} tasks[i].
    Preconditions: 1 <= len(tasks) <= 14; for every i with 0 <= i < len(tasks), 1 <= tasks[i] <= 10 and tasks[i] <= sessionTime; and sessionTime <= 15. -/
  theorem spec_4 (tasks : Slice Std.I64) (sessionTime : Std.I64)
      (hlen : 1 ≤ (durations tasks).length)
      (hlen14 : (durations tasks).length ≤ 14)
      (htasks : ∀ i : ℕ, i < (durations tasks).length →
        1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
      (hfit : ∀ i : ℕ, i < (durations tasks).length →
        taskAt (durations tasks) i ≤ sessionTime.val)
      (hst : sessionTime.val ≤ 15) :
      ∀ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r →
        r.val * sessionTime.val ≥ totalWork (durations tasks) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (tasks : Slice Std.I64) (sessionTime : Std.I64)
        (hlen : 1 ≤ (durations tasks).length)
        (hlen14 : (durations tasks).length ≤ 14)
        (htasks : ∀ i : ℕ, i < (durations tasks).length →
          1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
        (hfit : ∀ i : ℕ, i < (durations tasks).length →
          taskAt (durations tasks) i ≤ sessionTime.val)
        (hst : sessionTime.val ≤ 15), ∀ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r →
          r.val * sessionTime.val ≥ totalWork (durations tasks)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if sum_{i=0}^{len(tasks)-1} tasks[i] <= sessionTime.
    Preconditions: 1 <= len(tasks) <= 14; for every i with 0 <= i < len(tasks), 1 <= tasks[i] <= 10 and tasks[i] <= sessionTime; and sessionTime <= 15. -/
  theorem spec_5 (tasks : Slice Std.I64) (sessionTime : Std.I64)
      (hlen : 1 ≤ (durations tasks).length)
      (hlen14 : (durations tasks).length ≤ 14)
      (htasks : ∀ i : ℕ, i < (durations tasks).length →
        1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
      (hfit : ∀ i : ℕ, i < (durations tasks).length →
        taskAt (durations tasks) i ≤ sessionTime.val)
      (hst : sessionTime.val ≤ 15) :
      ∀ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r →
        (r.val = 1 ↔ totalWork (durations tasks) ≤ sessionTime.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (tasks : Slice Std.I64) (sessionTime : Std.I64)
        (hlen : 1 ≤ (durations tasks).length)
        (hlen14 : (durations tasks).length ≤ 14)
        (htasks : ∀ i : ℕ, i < (durations tasks).length →
          1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
        (hfit : ∀ i : ℕ, i < (durations tasks).length →
          taskAt (durations tasks) i ≤ sessionTime.val)
        (hst : sessionTime.val ≤ 15), ∀ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r →
          (r.val = 1 ↔ totalWork (durations tasks) ≤ sessionTime.val)) := by
    sorry

  /-- Whenever the function returns a result r, if tasks[i] = sessionTime for every i with 0 <= i < len(tasks), then r = len(tasks).
    Preconditions: 1 <= len(tasks) <= 14; for every i with 0 <= i < len(tasks), 1 <= tasks[i] <= 10 and tasks[i] <= sessionTime; and sessionTime <= 15. -/
  theorem spec_6 (tasks : Slice Std.I64) (sessionTime : Std.I64)
      (hlen : 1 ≤ (durations tasks).length)
      (hlen14 : (durations tasks).length ≤ 14)
      (htasks : ∀ i : ℕ, i < (durations tasks).length →
        1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
      (hfit : ∀ i : ℕ, i < (durations tasks).length →
        taskAt (durations tasks) i ≤ sessionTime.val)
      (hst : sessionTime.val ≤ 15) :
      ∀ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r →
        (∀ i : ℕ, i < (durations tasks).length →
          taskAt (durations tasks) i = sessionTime.val) →
        r.val = ((durations tasks).length : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (tasks : Slice Std.I64) (sessionTime : Std.I64)
        (hlen : 1 ≤ (durations tasks).length)
        (hlen14 : (durations tasks).length ≤ 14)
        (htasks : ∀ i : ℕ, i < (durations tasks).length →
          1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
        (hfit : ∀ i : ℕ, i < (durations tasks).length →
          taskAt (durations tasks) i ≤ sessionTime.val)
        (hst : sessionTime.val ≤ 15), ∀ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r →
          (∀ i : ℕ, i < (durations tasks).length →
            taskAt (durations tasks) i = sessionTime.val) →
          r.val = ((durations tasks).length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r >= |{ i | 0 <= i < len(tasks) and 2 * tasks[i] > sessionTime }|.
    Preconditions: 1 <= len(tasks) <= 14; for every i with 0 <= i < len(tasks), 1 <= tasks[i] <= 10 and tasks[i] <= sessionTime; and sessionTime <= 15. -/
  theorem spec_7 (tasks : Slice Std.I64) (sessionTime : Std.I64)
      (hlen : 1 ≤ (durations tasks).length)
      (hlen14 : (durations tasks).length ≤ 14)
      (htasks : ∀ i : ℕ, i < (durations tasks).length →
        1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
      (hfit : ∀ i : ℕ, i < (durations tasks).length →
        taskAt (durations tasks) i ≤ sessionTime.val)
      (hst : sessionTime.val ≤ 15) :
      ∀ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r →
        ((durations tasks).filter (fun t => 2 * t > sessionTime.val)).length ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (tasks : Slice Std.I64) (sessionTime : Std.I64)
        (hlen : 1 ≤ (durations tasks).length)
        (hlen14 : (durations tasks).length ≤ 14)
        (htasks : ∀ i : ℕ, i < (durations tasks).length →
          1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
        (hfit : ∀ i : ℕ, i < (durations tasks).length →
          taskAt (durations tasks) i ≤ sessionTime.val)
        (hst : sessionTime.val ≤ 15), ∀ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r →
          ((durations tasks).filter (fun t => 2 * t > sessionTime.val)).length ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = len(tasks) if and only if for every pair of indices i, j with 0 <= i < j < len(tasks), tasks[i] + tasks[j] > sessionTime.
    Preconditions: 1 <= len(tasks) <= 14; for every i with 0 <= i < len(tasks), 1 <= tasks[i] <= 10 and tasks[i] <= sessionTime; and sessionTime <= 15. -/
  theorem spec_8 (tasks : Slice Std.I64) (sessionTime : Std.I64)
      (hlen : 1 ≤ (durations tasks).length)
      (hlen14 : (durations tasks).length ≤ 14)
      (htasks : ∀ i : ℕ, i < (durations tasks).length →
        1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
      (hfit : ∀ i : ℕ, i < (durations tasks).length →
        taskAt (durations tasks) i ≤ sessionTime.val)
      (hst : sessionTime.val ≤ 15) :
      ∀ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r →
        (r.val = ((durations tasks).length : ℤ) ↔
          ∀ i j : ℕ, i < j → j < (durations tasks).length →
            taskAt (durations tasks) i + taskAt (durations tasks) j > sessionTime.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (tasks : Slice Std.I64) (sessionTime : Std.I64)
        (hlen : 1 ≤ (durations tasks).length)
        (hlen14 : (durations tasks).length ≤ 14)
        (htasks : ∀ i : ℕ, i < (durations tasks).length →
          1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
        (hfit : ∀ i : ℕ, i < (durations tasks).length →
          taskAt (durations tasks) i ≤ sessionTime.val)
        (hst : sessionTime.val ≤ 15), ∀ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r →
          (r.val = ((durations tasks).length : ℤ) ↔
            ∀ i j : ℕ, i < j → j < (durations tasks).length →
              taskAt (durations tasks) i + taskAt (durations tasks) j > sessionTime.val)) := by
    sorry

  /-- For any two inputs (tasks, sessionTime) and (tasks', sessionTime') satisfying the preconditions, if sessionTime' = sessionTime and tasks' is a permutation of tasks (that is, len(tasks') = len(tasks) and there exists a bijection pi on {0, ..., len(tasks)-1} such that tasks'[i] = tasks[pi(i)] for every i), then whenever min_sessions(tasks, sessionTime) returns r and min_sessions(tasks', sessionTime') returns r', we have r = r'.
    Preconditions: For both calls considered: each input satisfies 1 <= len(tasks) <= 14; for every index i, 1 <= tasks[i] <= 10 and tasks[i] <= sessionTime; and sessionTime <= 15. -/
  theorem spec_9 (tasks tasks' : Slice Std.I64) (sessionTime sessionTime' : Std.I64)
      (hlen : 1 ≤ (durations tasks).length)
      (hlen14 : (durations tasks).length ≤ 14)
      (htasks : ∀ i : ℕ, i < (durations tasks).length →
        1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
      (hfit : ∀ i : ℕ, i < (durations tasks).length →
        taskAt (durations tasks) i ≤ sessionTime.val)
      (hst : sessionTime.val ≤ 15)
      (hlen' : 1 ≤ (durations tasks').length)
      (hlen14' : (durations tasks').length ≤ 14)
      (htasks' : ∀ i : ℕ, i < (durations tasks').length →
        1 ≤ taskAt (durations tasks') i ∧ taskAt (durations tasks') i ≤ 10)
      (hfit' : ∀ i : ℕ, i < (durations tasks').length →
        taskAt (durations tasks') i ≤ sessionTime'.val)
      (hst' : sessionTime'.val ≤ 15)
      (hst_eq : sessionTime'.val = sessionTime.val)
      (hperm : (durations tasks').Perm (durations tasks)) :
      ∀ r r' : Std.I64,
        Aegis.MinSessions.min_sessions tasks sessionTime = ok r →
        Aegis.MinSessions.min_sessions tasks' sessionTime' = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (tasks tasks' : Slice Std.I64) (sessionTime sessionTime' : Std.I64)
        (hlen : 1 ≤ (durations tasks).length)
        (hlen14 : (durations tasks).length ≤ 14)
        (htasks : ∀ i : ℕ, i < (durations tasks).length →
          1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
        (hfit : ∀ i : ℕ, i < (durations tasks).length →
          taskAt (durations tasks) i ≤ sessionTime.val)
        (hst : sessionTime.val ≤ 15)
        (hlen' : 1 ≤ (durations tasks').length)
        (hlen14' : (durations tasks').length ≤ 14)
        (htasks' : ∀ i : ℕ, i < (durations tasks').length →
          1 ≤ taskAt (durations tasks') i ∧ taskAt (durations tasks') i ≤ 10)
        (hfit' : ∀ i : ℕ, i < (durations tasks').length →
          taskAt (durations tasks') i ≤ sessionTime'.val)
        (hst' : sessionTime'.val ≤ 15)
        (hst_eq : sessionTime'.val = sessionTime.val)
        (hperm : (durations tasks').Perm (durations tasks)), ∀ r r' : Std.I64,
          Aegis.MinSessions.min_sessions tasks sessionTime = ok r →
          Aegis.MinSessions.min_sessions tasks' sessionTime' = ok r' →
          r.val = r'.val) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; in particular, it does not fail by arithmetic overflow, out-of-bounds indexing, or panic.
    Preconditions: 1 <= len(tasks) <= 14; for every i with 0 <= i < len(tasks), 1 <= tasks[i] <= 10 and tasks[i] <= sessionTime; and sessionTime <= 15. -/
  theorem spec_10 (tasks : Slice Std.I64) (sessionTime : Std.I64)
      (hlen : 1 ≤ (durations tasks).length)
      (hlen14 : (durations tasks).length ≤ 14)
      (htasks : ∀ i : ℕ, i < (durations tasks).length →
        1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
      (hfit : ∀ i : ℕ, i < (durations tasks).length →
        taskAt (durations tasks) i ≤ sessionTime.val)
      (hst : sessionTime.val ≤ 15) :
      ∃ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (tasks : Slice Std.I64) (sessionTime : Std.I64)
        (hlen : 1 ≤ (durations tasks).length)
        (hlen14 : (durations tasks).length ≤ 14)
        (htasks : ∀ i : ℕ, i < (durations tasks).length →
          1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
        (hfit : ∀ i : ℕ, i < (durations tasks).length →
          taskAt (durations tasks) i ≤ sessionTime.val)
        (hst : sessionTime.val ≤ 15), ∃ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r) := by
    sorry

  /-- Whenever the function returns a result r, there exist nonempty sets S_1, ..., S_r such that (a) they are pairwise disjoint and their union is {0, 1, ..., len(tasks)-1}; and (b) for every j with 1 <= j <= r, sum_{i in S_j} tasks[i] <= sessionTime.
    Preconditions: 1 <= len(tasks) <= 14; for every i with 0 <= i < len(tasks), 1 <= tasks[i] <= 10 and tasks[i] <= sessionTime; and sessionTime <= 15. -/
  theorem spec_11 (tasks : Slice Std.I64) (sessionTime : Std.I64)
      (hlen : 1 ≤ (durations tasks).length)
      (hlen14 : (durations tasks).length ≤ 14)
      (htasks : ∀ i : ℕ, i < (durations tasks).length →
        1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
      (hfit : ∀ i : ℕ, i < (durations tasks).length →
        taskAt (durations tasks) i ≤ sessionTime.val)
      (hst : sessionTime.val ≤ 15) :
      ∀ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r →
        Feasible (durations tasks) sessionTime.val r.val.toNat := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (tasks : Slice Std.I64) (sessionTime : Std.I64)
        (hlen : 1 ≤ (durations tasks).length)
        (hlen14 : (durations tasks).length ≤ 14)
        (htasks : ∀ i : ℕ, i < (durations tasks).length →
          1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
        (hfit : ∀ i : ℕ, i < (durations tasks).length →
          taskAt (durations tasks) i ≤ sessionTime.val)
        (hst : sessionTime.val ≤ 15), ∀ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r →
          Feasible (durations tasks) sessionTime.val r.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k with 1 <= k < r, there do not exist nonempty sets S_1, ..., S_k satisfying: (a) they are pairwise disjoint and their union is {0, 1, ..., len(tasks)-1}; and (b) for every j with 1 <= j <= k, sum_{i in S_j} tasks[i] <= sessionTime.
    Preconditions: 1 <= len(tasks) <= 14; for every i with 0 <= i < len(tasks), 1 <= tasks[i] <= 10 and tasks[i] <= sessionTime; and sessionTime <= 15. -/
  theorem spec_12 (tasks : Slice Std.I64) (sessionTime : Std.I64)
      (hlen : 1 ≤ (durations tasks).length)
      (hlen14 : (durations tasks).length ≤ 14)
      (htasks : ∀ i : ℕ, i < (durations tasks).length →
        1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
      (hfit : ∀ i : ℕ, i < (durations tasks).length →
        taskAt (durations tasks) i ≤ sessionTime.val)
      (hst : sessionTime.val ≤ 15) :
      ∀ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r →
        ∀ k : ℕ, 1 ≤ k → (k : ℤ) < r.val → ¬ Feasible (durations tasks) sessionTime.val k := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (tasks : Slice Std.I64) (sessionTime : Std.I64)
        (hlen : 1 ≤ (durations tasks).length)
        (hlen14 : (durations tasks).length ≤ 14)
        (htasks : ∀ i : ℕ, i < (durations tasks).length →
          1 ≤ taskAt (durations tasks) i ∧ taskAt (durations tasks) i ≤ 10)
        (hfit : ∀ i : ℕ, i < (durations tasks).length →
          taskAt (durations tasks) i ≤ sessionTime.val)
        (hst : sessionTime.val ≤ 15), ∀ r : Std.I64, Aegis.MinSessions.min_sessions tasks sessionTime = ok r →
          ∀ k : ℕ, 1 ≤ k → (k : ℤ) < r.val → ¬ Feasible (durations tasks) sessionTime.val k) := by
    sorry

end AegisSpec.MinSessions
