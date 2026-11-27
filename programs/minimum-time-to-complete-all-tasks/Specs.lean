import Aegis.FindMinimumTime.Code.Funs

/-!
# Specifications of `Aegis.FindMinimumTime.find_minimum_time`

LeetCode problem `minimum-time-to-complete-all-tasks`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.FindMinimumTime

  namespace AegisSpec.FindMinimumTime

  def taskRow (tasks : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : List ℤ :=
    ((tasks.val[i]?).map (fun v => v.val.map (fun x => x.val))).getD []

  def startOf (tasks : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    (taskRow tasks i).getD 0 0

  def endOf (tasks : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    (taskRow tasks i).getD 1 0

  def durOf (tasks : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    (taskRow tasks i).getD 2 0

  def maxEnd (tasks : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    ((List.range tasks.val.length).map (endOf tasks)).max?.getD 0

  def minStart (tasks : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    ((List.range tasks.val.length).map (startOf tasks)).min?.getD 0

  def maxDur (tasks : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    ((List.range tasks.val.length).map (durOf tasks)).max?.getD 0

  def ValidInput (tasks : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    1 ≤ tasks.val.length ∧ tasks.val.length ≤ 2000 ∧
      (∀ i, i < tasks.val.length →
        (taskRow tasks i).length = 3 ∧
          1 ≤ startOf tasks i ∧ startOf tasks i ≤ 2000 ∧
          1 ≤ endOf tasks i ∧ endOf tasks i ≤ 2000 ∧
          1 ≤ durOf tasks i ∧ durOf tasks i ≤ endOf tasks i - startOf tasks i + 1)

  def CoversTask (tasks : Slice (alloc.vec.Vec Std.I64)) (T : Finset ℤ) (i : ℕ) : Prop :=
    durOf tasks i ≤ ((T.filter (fun t => startOf tasks i ≤ t ∧ t ≤ endOf tasks i)).card : ℤ)

  def Feasible (tasks : Slice (alloc.vec.Vec Std.I64)) (T : Finset ℤ) : Prop :=
    ∀ i, i < tasks.val.length → CoversTask tasks T i

  def Permuted (tasks tasks' : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∃ π : Equiv.Perm ℕ, ∃ hπ : ∀ i, i < tasks.val.length → π i < tasks.val.length,
      tasks'.val = List.ofFn (fun i : Fin tasks.val.length => tasks.val.get ⟨π i, hπ i i.isLt⟩)

  def DeletedAt (tasks tasks' : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : Prop :=
    tasks'.val = tasks.val.eraseIdx i

  /-- Whenever find_minimum_time(tasks) returns a result r, r is equal to the minimum of |T| over all finite sets T of integers such that, for every i with 0 ≤ i < n, the number of elements t of T with s_i ≤ t ≤ e_i is at least d_i.
    Preconditions: Let n = len(tasks). 1 ≤ n ≤ 2000. For every i with 0 ≤ i < n, tasks[i] has length 3; writing s_i = tasks[i][0], e_i = tasks[i][1], d_i = tasks[i][2], we have 1 ≤ s_i ≤ 2000, 1 ≤ e_i ≤ 2000, and 1 ≤ d_i ≤ e_i - s_i + 1 (so s_i ≤ e_i). -/
  theorem spec_1 (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
      (r : Std.I64) (hres : find_minimum_time tasks = .ok r) :
      (∃ T : Finset ℤ, Feasible tasks T ∧ (T.card : ℤ) = r.val) ∧
        ∀ T : Finset ℤ, Feasible tasks T → r.val ≤ (T.card : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
        (r : Std.I64) (hres : find_minimum_time tasks = Result.ok r), (∃ T : Finset ℤ, Feasible tasks T ∧ (T.card : ℤ) = r.val) ∧
          ∀ T : Finset ℤ, Feasible tasks T → r.val ≤ (T.card : ℤ)) := by
    sorry

  /-- Whenever find_minimum_time(tasks) returns a result r, there exists a finite set T of integers with |T| = r such that (a) for every i with 0 ≤ i < n, the number of t ∈ T with s_i ≤ t ≤ e_i is at least d_i, and (b) every t ∈ T lies in at least one of the intervals [s_j, e_j] with 0 ≤ j < n.
    Preconditions: Same as spec_1: n = len(tasks) with 1 ≤ n ≤ 2000, and each tasks[i] = [s_i, e_i, d_i] satisfies 1 ≤ s_i ≤ 2000, 1 ≤ e_i ≤ 2000, 1 ≤ d_i ≤ e_i - s_i + 1. -/
  theorem spec_2 (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
      (r : Std.I64) (hres : find_minimum_time tasks = .ok r) :
      ∃ T : Finset ℤ, (T.card : ℤ) = r.val ∧ Feasible tasks T ∧
        ∀ t ∈ T, ∃ j, j < tasks.val.length ∧ startOf tasks j ≤ t ∧ t ≤ endOf tasks j := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
        (r : Std.I64) (hres : find_minimum_time tasks = Result.ok r), ∃ T : Finset ℤ, (T.card : ℤ) = r.val ∧ Feasible tasks T ∧
          ∀ t ∈ T, ∃ j, j < tasks.val.length ∧ startOf tasks j ≤ t ∧ t ≤ endOf tasks j) := by
    sorry

  /-- Whenever find_minimum_time(tasks) returns a result r, every finite set T of integers satisfying |{t ∈ T : s_i ≤ t ≤ e_i}| ≥ d_i for all i with 0 ≤ i < n has |T| ≥ r.
    Preconditions: Same as spec_1. -/
  theorem spec_3 (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
      (r : Std.I64) (hres : find_minimum_time tasks = .ok r) :
      ∀ T : Finset ℤ, Feasible tasks T → r.val ≤ (T.card : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
        (r : Std.I64) (hres : find_minimum_time tasks = Result.ok r), ∀ T : Finset ℤ, Feasible tasks T → r.val ≤ (T.card : ℤ)) := by
    sorry

  /-- Whenever find_minimum_time(tasks) returns a result r, for every set J ⊆ {0, 1, ..., n-1} of indices whose intervals [s_j, e_j] are pairwise disjoint (that is, for all distinct j, k ∈ J, either e_j < s_k or e_k < s_j) we have r ≥ Σ_{j ∈ J} d_j.
    Preconditions: Same as spec_1. -/
  theorem spec_4 (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
      (r : Std.I64) (hres : find_minimum_time tasks = .ok r) :
      ∀ J : Finset ℕ, (∀ j ∈ J, j < tasks.val.length) →
        (∀ j ∈ J, ∀ k ∈ J, j ≠ k →
          endOf tasks j < startOf tasks k ∨ endOf tasks k < startOf tasks j) →
        (∑ j ∈ J, durOf tasks j) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
        (r : Std.I64) (hres : find_minimum_time tasks = Result.ok r), ∀ J : Finset ℕ, (∀ j ∈ J, j < tasks.val.length) →
          (∀ j ∈ J, ∀ k ∈ J, j ≠ k →
            endOf tasks j < startOf tasks k ∨ endOf tasks k < startOf tasks j) →
          (∑ j ∈ J, durOf tasks j) ≤ r.val) := by
    sorry

  /-- Whenever find_minimum_time(tasks) returns a result r, r ≤ (max_{0 ≤ i < n} e_i) - (min_{0 ≤ i < n} s_i) + 1.
    Preconditions: Same as spec_1. -/
  theorem spec_5 (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
      (r : Std.I64) (hres : find_minimum_time tasks = .ok r) :
      r.val ≤ maxEnd tasks - minStart tasks + 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
        (r : Std.I64) (hres : find_minimum_time tasks = Result.ok r), r.val ≤ maxEnd tasks - minStart tasks + 1) := by
    sorry

  /-- Whenever find_minimum_time(tasks) returns a result r, r ≤ Σ_{i=0}^{n-1} d_i.
    Preconditions: Same as spec_1. -/
  theorem spec_6 (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
      (r : Std.I64) (hres : find_minimum_time tasks = .ok r) :
      r.val ≤ ∑ i ∈ Finset.range tasks.val.length, durOf tasks i := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
        (r : Std.I64) (hres : find_minimum_time tasks = Result.ok r), r.val ≤ ∑ i ∈ Finset.range tasks.val.length, durOf tasks i) := by
    sorry

  /-- Whenever the intervals [s_i, e_i] for 0 ≤ i < n are pairwise disjoint (for all distinct i, j, either e_i < s_j or e_j < s_i) and find_minimum_time(tasks) returns a result r, we have r = Σ_{i=0}^{n-1} d_i.
    Preconditions: Same as spec_1. -/
  theorem spec_7 (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
      (r : Std.I64) (hres : find_minimum_time tasks = .ok r)
      (hdisj : ∀ i, i < tasks.val.length → ∀ j, j < tasks.val.length → i ≠ j →
        endOf tasks i < startOf tasks j ∨ endOf tasks j < startOf tasks i) :
      r.val = ∑ i ∈ Finset.range tasks.val.length, durOf tasks i := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
        (r : Std.I64) (hres : find_minimum_time tasks = Result.ok r)
        (hdisj : ∀ i, i < tasks.val.length → ∀ j, j < tasks.val.length → i ≠ j →
          endOf tasks i < startOf tasks j ∨ endOf tasks j < startOf tasks i), r.val = ∑ i ∈ Finset.range tasks.val.length, durOf tasks i) := by
    sorry

  /-- Whenever there exist integers a ≤ b such that s_i = a and e_i = b for every i with 0 ≤ i < n, and find_minimum_time(tasks) returns a result r, we have r = max_{0 ≤ i < n} d_i.
    Preconditions: Same as spec_1. -/
  theorem spec_8 (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
      (r : Std.I64) (hres : find_minimum_time tasks = .ok r)
      (hsame : ∃ a b : ℤ, a ≤ b ∧ ∀ i, i < tasks.val.length →
        startOf tasks i = a ∧ endOf tasks i = b) :
      r.val = maxDur tasks := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
        (r : Std.I64) (hres : find_minimum_time tasks = Result.ok r)
        (hsame : ∃ a b : ℤ, a ≤ b ∧ ∀ i, i < tasks.val.length →
          startOf tasks i = a ∧ endOf tasks i = b), r.val = maxDur tasks) := by
    sorry

  /-- Whenever d_i = e_i - s_i + 1 for every i with 0 ≤ i < n, and find_minimum_time(tasks) returns a result r, r equals the number of integers t for which there exists some i with 0 ≤ i < n and s_i ≤ t ≤ e_i.
    Preconditions: Same as spec_1. -/
  theorem spec_9 (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
      (r : Std.I64) (hres : find_minimum_time tasks = .ok r)
      (hfull : ∀ i, i < tasks.val.length →
        durOf tasks i = endOf tasks i - startOf tasks i + 1) :
      ∃ U : Finset ℤ, (∀ t : ℤ, t ∈ U ↔ ∃ i, i < tasks.val.length ∧
        startOf tasks i ≤ t ∧ t ≤ endOf tasks i) ∧ (U.card : ℤ) = r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
        (r : Std.I64) (hres : find_minimum_time tasks = Result.ok r)
        (hfull : ∀ i, i < tasks.val.length →
          durOf tasks i = endOf tasks i - startOf tasks i + 1), ∃ U : Finset ℤ, (∀ t : ℤ, t ∈ U ↔ ∃ i, i < tasks.val.length ∧
          startOf tasks i ≤ t ∧ t ≤ endOf tasks i) ∧ (U.card : ℤ) = r.val) := by
    sorry

  /-- For every input tasks satisfying the preconditions, find_minimum_time(tasks) returns a result (the computation does not fail, overflow, or panic).
    Preconditions: Same as spec_1. -/
  theorem spec_10 (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks) :
      ∃ r, find_minimum_time tasks = .ok r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks), ∃ r, find_minimum_time tasks = Result.ok r) := by
    sorry

  /-- For every bijection π : {0, 1, ..., n-1} → {0, 1, ..., n-1}, let tasks' be the slice of length n defined by tasks'[i] = tasks[π(i)] for all i. Whenever find_minimum_time(tasks) returns r and find_minimum_time(tasks') returns r', we have r = r'.
    Preconditions: Same as spec_1. -/
  theorem spec_11 (tasks tasks' : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
      (hperm : Permuted tasks tasks')
      (r r' : Std.I64) (hres : find_minimum_time tasks = .ok r)
      (hres' : find_minimum_time tasks' = .ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (tasks tasks' : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
        (hperm : Permuted tasks tasks')
        (r r' : Std.I64) (hres : find_minimum_time tasks = Result.ok r)
        (hres' : find_minimum_time tasks' = Result.ok r'), r.val = r'.val) := by
    sorry

  /-- For each i with 0 ≤ i < n, let tasks^(i) be the slice of length n-1 obtained by deleting tasks[i] (tasks^(i)[k] = tasks[k] for k < i, and tasks^(i)[k] = tasks[k+1] for k ≥ i). Whenever find_minimum_time(tasks) returns r and find_minimum_time(tasks^(i)) returns r_i, we have r_i ≤ r ≤ r_i + d_i.
    Preconditions: Same as spec_1, and additionally n ≥ 2. -/
  theorem spec_12 (tasks tasksi : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
      (hn : 2 ≤ tasks.val.length) (i : ℕ) (hi : i < tasks.val.length)
      (hdel : DeletedAt tasks tasksi i)
      (r ri : Std.I64) (hres : find_minimum_time tasks = .ok r)
      (hresi : find_minimum_time tasksi = .ok ri) :
      ri.val ≤ r.val ∧ r.val ≤ ri.val + durOf tasks i := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (tasks tasksi : Slice (alloc.vec.Vec Std.I64)) (hvalid : ValidInput tasks)
        (hn : 2 ≤ tasks.val.length) (i : ℕ) (hi : i < tasks.val.length)
        (hdel : DeletedAt tasks tasksi i)
        (r ri : Std.I64) (hres : find_minimum_time tasks = Result.ok r)
        (hresi : find_minimum_time tasksi = Result.ok ri), ri.val ≤ r.val ∧ r.val ≤ ri.val + durOf tasks i) := by
    sorry

  end AegisSpec.FindMinimumTime
