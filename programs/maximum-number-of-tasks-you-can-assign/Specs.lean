import Aegis.MaxTaskAssign.Code.Funs

/-!
# Specifications of `Aegis.MaxTaskAssign.max_task_assign`

LeetCode problem `maximum-number-of-tasks-you-can-assign`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxTaskAssign

  def taskVals (tasks : Slice Std.I64) : List Int := tasks.val.map (fun t => t.val)

  def workerVals (workers : Slice Std.I64) : List Int := workers.val.map (fun w => w.val)

  def taskAt (tasks : List Int) (i : Nat) : Int := tasks.getD i 0

  def workerAt (workers : List Int) (j : Nat) : Int := workers.getD j 0

  def AssignsTasks (tasks workers : List Int) (pills : Nat) (strength : Int) (k : Nat)
      (S : Finset Nat) (f : Nat → Nat) (P : Finset Nat) : Prop :=
    S.card = k ∧
    (∀ i ∈ S, i < tasks.length) ∧
    (∀ i ∈ S, f i < workers.length) ∧
    (∀ i ∈ S, ∀ i' ∈ S, f i = f i' → i = i') ∧
    P ⊆ S ∧
    P.card ≤ pills ∧
    ∀ i ∈ S, workerAt workers (f i) + (if i ∈ P then strength else 0) ≥ taskAt tasks i

  def HasValidAssignment (tasks workers : List Int) (pills : Nat) (strength : Int)
      (k : Nat) : Prop :=
    ∃ S f P, AssignsTasks tasks workers pills strength k S f P

  def IsMaxValidSize (tasks workers : List Int) (pills : Nat) (strength : Int)
      (K : Nat) : Prop :=
    K ≤ min tasks.length workers.length ∧
    HasValidAssignment tasks workers pills strength K ∧
    ∀ k, k ≤ min tasks.length workers.length →
      HasValidAssignment tasks workers pills strength k → k ≤ K

  def HasPlainMatching (tasks workers : List Int) (k : Nat) : Prop :=
    ∃ (S : Finset Nat) (f : Nat → Nat),
      S.card = k ∧
      (∀ i ∈ S, i < tasks.length) ∧
      (∀ i ∈ S, f i < workers.length) ∧
      (∀ i ∈ S, ∀ i' ∈ S, f i = f i' → i = i') ∧
      ∀ i ∈ S, workerAt workers (f i) ≥ taskAt tasks i

  def IsMaxPlainMatching (tasks workers : List Int) (K : Nat) : Prop :=
    K ≤ min tasks.length workers.length ∧
    HasPlainMatching tasks workers K ∧
    ∀ k, k ≤ min tasks.length workers.length → HasPlainMatching tasks workers k → k ≤ K

  def HasBoostedMatching (tasks workers : List Int) (strength : Int) (k : Nat) : Prop :=
    ∃ (S : Finset Nat) (f : Nat → Nat),
      S.card = k ∧
      (∀ i ∈ S, i < tasks.length) ∧
      (∀ i ∈ S, f i < workers.length) ∧
      (∀ i ∈ S, ∀ i' ∈ S, f i = f i' → i = i') ∧
      ∀ i ∈ S, workerAt workers (f i) + strength ≥ taskAt tasks i

  def IsMaxBoostedMatching (tasks workers : List Int) (strength : Int) (K : Nat) : Prop :=
    K ≤ min tasks.length workers.length ∧
    HasBoostedMatching tasks workers strength K ∧
    ∀ k, k ≤ min tasks.length workers.length →
      HasBoostedMatching tasks workers strength k → k ≤ K

  noncomputable def coverableTasks (tasks workers : List Int) (strength : Int) : Finset Nat := by
    classical
    exact (Finset.range tasks.length).filter
      (fun i => ∃ j ∈ Finset.range workers.length, workerAt workers j + strength ≥ taskAt tasks i)

  noncomputable def coverableWorkers (tasks workers : List Int) (strength : Int) : Finset Nat := by
    classical
    exact (Finset.range workers.length).filter
      (fun j => ∃ i ∈ Finset.range tasks.length, workerAt workers j + strength ≥ taskAt tasks i)

  def IsTopTasks (tasks : List Int) (k : Nat) (T : Finset Nat) : Prop :=
    T.card = k ∧
    (∀ i ∈ T, i < tasks.length) ∧
    ∀ i ∈ T, ∀ j, j < tasks.length → j ∉ T → taskAt tasks i ≤ taskAt tasks j

  def IsTopWorkers (workers : List Int) (k : Nat) (W : Finset Nat) : Prop :=
    W.card = k ∧
    (∀ j ∈ W, j < workers.length) ∧
    ∀ j ∈ W, ∀ l, l < workers.length → l ∉ W → workerAt workers j ≥ workerAt workers l

  /-- The function returns a result r, and r is the largest integer k such that 0 <= k <= min(n, m) and there exists a valid assignment of k tasks. A valid assignment of k tasks is a triple (S, f, P) where S is a subset of {0,...,n-1} with |S| = k, f: S -> {0,...,m-1} is injective, and P is a subset of S with |P| <= pills, such that for every i in S, workers[f(i)] + (if i is in P then strength else 0) >= tasks[i].
    Preconditions: n = len(tasks), m = len(workers), 1 <= n <= 5*10^4, 1 <= m <= 5*10^4, 0 <= pills <= m, for all i with 0 <= i < n, 0 <= tasks[i] <= 10^9, for all j with 0 <= j < m, 0 <= workers[j] <= 10^9, and 0 <= strength <= 10^9. -/
  theorem spec_1 (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
      (hn : n = tasks.val.length) (hm : m = workers.val.length)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
      (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
      (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
      (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
      (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
      (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
        0 ≤ r.val ∧
        r.val ≤ ((min n m : Nat) : Int) ∧
        IsMaxValidSize (taskVals tasks) (workerVals workers) pills.val.toNat strength.val r.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
        (hn : n = tasks.val.length) (hm : m = workers.val.length)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
        (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
        (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
        (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
        (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
        (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
          0 ≤ r.val ∧
          r.val ≤ ((min n m : Nat) : Int) ∧
          IsMaxValidSize (taskVals tasks) (workerVals workers) pills.val.toNat strength.val r.val.toNat) := by
    sorry

  /-- The function returns a result r with 0 <= r <= min(n, m).
    Preconditions: n = len(tasks), m = len(workers), 1 <= n <= 5*10^4, 1 <= m <= 5*10^4, 0 <= pills <= m, for all i with 0 <= i < n, 0 <= tasks[i] <= 10^9, for all j with 0 <= j < m, 0 <= workers[j] <= 10^9, and 0 <= strength <= 10^9. -/
  theorem spec_2 (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
      (hn : n = tasks.val.length) (hm : m = workers.val.length)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
      (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
      (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
      (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
      (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
      (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
        0 ≤ r.val ∧
        r.val ≤ ((min n m : Nat) : Int) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
        (hn : n = tasks.val.length) (hm : m = workers.val.length)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
        (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
        (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
        (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
        (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
        (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
          0 ≤ r.val ∧
          r.val ≤ ((min n m : Nat) : Int)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow).
    Preconditions: n = len(tasks), m = len(workers), 1 <= n <= 5*10^4, 1 <= m <= 5*10^4, 0 <= pills <= m, for all i with 0 <= i < n, 0 <= tasks[i] <= 10^9, for all j with 0 <= j < m, 0 <= workers[j] <= 10^9, and 0 <= strength <= 10^9. -/
  theorem spec_3 (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
      (hn : n = tasks.val.length) (hm : m = workers.val.length)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
      (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
      (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
      (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
      (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
      (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000) :
      ∃ r : Std.I64, Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
        (hn : n = tasks.val.length) (hm : m = workers.val.length)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
        (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
        (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
        (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
        (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
        (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000), ∃ r : Std.I64, Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r) := by
    sorry

  /-- The function returns a result r and there exists a valid assignment of r tasks (as defined in spec_1).
    Preconditions: n = len(tasks), m = len(workers), 1 <= n <= 5*10^4, 1 <= m <= 5*10^4, 0 <= pills <= m, for all i with 0 <= i < n, 0 <= tasks[i] <= 10^9, for all j with 0 <= j < m, 0 <= workers[j] <= 10^9, and 0 <= strength <= 10^9. -/
  theorem spec_4 (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
      (hn : n = tasks.val.length) (hm : m = workers.val.length)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
      (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
      (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
      (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
      (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
      (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
        HasValidAssignment (taskVals tasks) (workerVals workers) pills.val.toNat strength.val r.val.toNat := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
        (hn : n = tasks.val.length) (hm : m = workers.val.length)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
        (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
        (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
        (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
        (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
        (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
          HasValidAssignment (taskVals tasks) (workerVals workers) pills.val.toNat strength.val r.val.toNat) := by
    sorry

  /-- The function returns a result r and for every integer k with r < k <= min(n, m), there does not exist a valid assignment of k tasks (as defined in spec_1).
    Preconditions: n = len(tasks), m = len(workers), 1 <= n <= 5*10^4, 1 <= m <= 5*10^4, 0 <= pills <= m, for all i with 0 <= i < n, 0 <= tasks[i] <= 10^9, for all j with 0 <= j < m, 0 <= workers[j] <= 10^9, and 0 <= strength <= 10^9. -/
  theorem spec_5 (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
      (hn : n = tasks.val.length) (hm : m = workers.val.length)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
      (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
      (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
      (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
      (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
      (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
        ∀ k : Nat, r.val.toNat < k → k ≤ min n m →
          ¬ HasValidAssignment (taskVals tasks) (workerVals workers) pills.val.toNat strength.val k := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
        (hn : n = tasks.val.length) (hm : m = workers.val.length)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
        (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
        (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
        (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
        (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
        (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
          ∀ k : Nat, r.val.toNat < k → k ≤ min n m →
            ¬ HasValidAssignment (taskVals tasks) (workerVals workers) pills.val.toNat strength.val k) := by
    sorry

  /-- The function returns a result r and r <= |{ i in {0,...,n-1} : there exists j in {0,...,m-1} such that workers[j] + strength >= tasks[i] }|.
    Preconditions: n = len(tasks), m = len(workers), 1 <= n <= 5*10^4, 1 <= m <= 5*10^4, 0 <= pills <= m, for all i with 0 <= i < n, 0 <= tasks[i] <= 10^9, for all j with 0 <= j < m, 0 <= workers[j] <= 10^9, and 0 <= strength <= 10^9. -/
  theorem spec_6 (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
      (hn : n = tasks.val.length) (hm : m = workers.val.length)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
      (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
      (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
      (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
      (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
      (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
        r.val ≤ ((coverableTasks (taskVals tasks) (workerVals workers) strength.val).card : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
        (hn : n = tasks.val.length) (hm : m = workers.val.length)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
        (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
        (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
        (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
        (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
        (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
          r.val ≤ ((coverableTasks (taskVals tasks) (workerVals workers) strength.val).card : Int)) := by
    sorry

  /-- The function returns a result r and r <= |{ j in {0,...,m-1} : there exists i in {0,...,n-1} such that workers[j] + strength >= tasks[i] }|.
    Preconditions: n = len(tasks), m = len(workers), 1 <= n <= 5*10^4, 1 <= m <= 5*10^4, 0 <= pills <= m, for all i with 0 <= i < n, 0 <= tasks[i] <= 10^9, for all j with 0 <= j < m, 0 <= workers[j] <= 10^9, and 0 <= strength <= 10^9. -/
  theorem spec_7 (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
      (hn : n = tasks.val.length) (hm : m = workers.val.length)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
      (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
      (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
      (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
      (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
      (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
        r.val ≤ ((coverableWorkers (taskVals tasks) (workerVals workers) strength.val).card : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
        (hn : n = tasks.val.length) (hm : m = workers.val.length)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
        (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
        (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
        (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
        (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
        (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
          r.val ≤ ((coverableWorkers (taskVals tasks) (workerVals workers) strength.val).card : Int)) := by
    sorry

  /-- The function returns a result r and r >= max{ k : 0 <= k <= min(n, m) and there exist k tasks and k distinct workers such that each matched task i is assigned to a worker j with workers[j] >= tasks[i] }.
    Preconditions: n = len(tasks), m = len(workers), 1 <= n <= 5*10^4, 1 <= m <= 5*10^4, 0 <= pills <= m, for all i with 0 <= i < n, 0 <= tasks[i] <= 10^9, for all j with 0 <= j < m, 0 <= workers[j] <= 10^9, and 0 <= strength <= 10^9. -/
  theorem spec_8 (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
      (hn : n = tasks.val.length) (hm : m = workers.val.length)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
      (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
      (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
      (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
      (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
      (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
        ∃ K : Nat,
          IsMaxPlainMatching (taskVals tasks) (workerVals workers) K ∧ (K : Int) ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
        (hn : n = tasks.val.length) (hm : m = workers.val.length)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
        (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
        (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
        (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
        (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
        (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
          ∃ K : Nat,
            IsMaxPlainMatching (taskVals tasks) (workerVals workers) K ∧ (K : Int) ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= max{ k : 0 <= k <= min(n, m) and there exist k tasks and k distinct workers such that each matched task i is assigned to a worker j with workers[j] + strength >= tasks[i] }.
    Preconditions: n = len(tasks), m = len(workers), 1 <= n <= 5*10^4, 1 <= m <= 5*10^4, 0 <= pills <= m, for all i with 0 <= i < n, 0 <= tasks[i] <= 10^9, for all j with 0 <= j < m, 0 <= workers[j] <= 10^9, and 0 <= strength <= 10^9. -/
  theorem spec_9 (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
      (hn : n = tasks.val.length) (hm : m = workers.val.length)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
      (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
      (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
      (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
      (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
      (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
        ∃ K : Nat,
          IsMaxBoostedMatching (taskVals tasks) (workerVals workers) strength.val K ∧
            r.val ≤ (K : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
        (hn : n = tasks.val.length) (hm : m = workers.val.length)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
        (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
        (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
        (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
        (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
        (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
          ∃ K : Nat,
            IsMaxBoostedMatching (taskVals tasks) (workerVals workers) strength.val K ∧
              r.val ≤ (K : Int)) := by
    sorry

  /-- The function returns a result r, and r = 0 if and only if for all i in {0,...,n-1} and all j in {0,...,m-1}, workers[j] + strength < tasks[i].
    Preconditions: n = len(tasks), m = len(workers), 1 <= n <= 5*10^4, 1 <= m <= 5*10^4, 0 <= pills <= m, pills >= 1, for all i with 0 <= i < n, 0 <= tasks[i] <= 10^9, for all j with 0 <= j < m, 0 <= workers[j] <= 10^9, and 0 <= strength <= 10^9. -/
  theorem spec_10 (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
      (hn : n = tasks.val.length) (hm : m = workers.val.length)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
      (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
      (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
      (hpills_pos : 1 ≤ pills.val)
      (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
      (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
      (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
        (r.val = 0 ↔
          ∀ i : Nat, i < n → ∀ j : Nat, j < m →
            workerAt (workerVals workers) j + strength.val < taskAt (taskVals tasks) i) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
        (hn : n = tasks.val.length) (hm : m = workers.val.length)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
        (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
        (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
        (hpills_pos : 1 ≤ pills.val)
        (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
        (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
        (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
          (r.val = 0 ↔
            ∀ i : Nat, i < n → ∀ j : Nat, j < m →
              workerAt (workerVals workers) j + strength.val < taskAt (taskVals tasks) i)) := by
    sorry

  /-- The function returns a result r and r = max{ k : 0 <= k <= min(n, m) and there exist k tasks and k distinct workers such that each matched task i is assigned to a worker j with workers[j] >= tasks[i] }.
    Preconditions: n = len(tasks), m = len(workers), 1 <= n <= 5*10^4, 1 <= m <= 5*10^4, 0 <= pills <= m, pills = 0, for all i with 0 <= i < n, 0 <= tasks[i] <= 10^9, for all j with 0 <= j < m, 0 <= workers[j] <= 10^9, and 0 <= strength <= 10^9. -/
  theorem spec_11 (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
      (hn : n = tasks.val.length) (hm : m = workers.val.length)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
      (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
      (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
      (hpills_zero : pills.val = 0)
      (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
      (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
      (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
        IsMaxPlainMatching (taskVals tasks) (workerVals workers) r.val.toNat := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
        (hn : n = tasks.val.length) (hm : m = workers.val.length)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
        (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
        (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
        (hpills_zero : pills.val = 0)
        (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
        (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
        (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
          IsMaxPlainMatching (taskVals tasks) (workerVals workers) r.val.toNat) := by
    sorry

  /-- The function returns a result r and r = max{ k : 0 <= k <= min(n, m) and there exist k tasks and k distinct workers such that each matched task i is assigned to a worker j with workers[j] + strength >= tasks[i] }.
    Preconditions: n = len(tasks), m = len(workers), 1 <= n <= 5*10^4, 1 <= m <= 5*10^4, 0 <= pills <= m, pills >= m, for all i with 0 <= i < n, 0 <= tasks[i] <= 10^9, for all j with 0 <= j < m, 0 <= workers[j] <= 10^9, and 0 <= strength <= 10^9. -/
  theorem spec_12 (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
      (hn : n = tasks.val.length) (hm : m = workers.val.length)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
      (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
      (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
      (hpills_ge : (m : Int) ≤ pills.val)
      (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
      (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
      (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
        IsMaxBoostedMatching (taskVals tasks) (workerVals workers) strength.val r.val.toNat := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
        (hn : n = tasks.val.length) (hm : m = workers.val.length)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
        (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
        (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
        (hpills_ge : (m : Int) ≤ pills.val)
        (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
        (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
        (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
          IsMaxBoostedMatching (taskVals tasks) (workerVals workers) strength.val r.val.toNat) := by
    sorry

  /-- The function returns a result r and r = min(n, m).
    Preconditions: n = len(tasks), m = len(workers), 1 <= n <= 5*10^4, 1 <= m <= 5*10^4, 0 <= pills <= m, for all i with 0 <= i < n, 0 <= tasks[i] <= 10^9, for all j with 0 <= j < m, 0 <= workers[j] <= 10^9, 0 <= strength <= 10^9, and for all i with 0 <= i < n and j with 0 <= j < m, tasks[i] <= workers[j]. -/
  theorem spec_13 (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
      (hn : n = tasks.val.length) (hm : m = workers.val.length)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
      (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
      (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
      (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
      (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
      (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000)
      (htask_le_worker : ∀ i : Nat, i < n → ∀ j : Nat, j < m →
        taskAt (taskVals tasks) i ≤ workerAt (workerVals workers) j) :
      ∃ r : Std.I64,
        Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
        r.val = ((min n m : Nat) : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (tasks workers : Slice Std.I64) (pills strength : Std.I64) (n m : Nat)
        (hn : n = tasks.val.length) (hm : m = workers.val.length)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 50000)
        (hm_pos : 1 ≤ m) (hm_max : m ≤ 50000)
        (hpills_nonneg : 0 ≤ pills.val) (hpills_le : pills.val ≤ (m : Int))
        (htasks : ∀ i : Nat, i < n → 0 ≤ taskAt (taskVals tasks) i ∧ taskAt (taskVals tasks) i ≤ 1000000000)
        (hworkers : ∀ j : Nat, j < m → 0 ≤ workerAt (workerVals workers) j ∧ workerAt (workerVals workers) j ≤ 1000000000)
        (hstrength_nonneg : 0 ≤ strength.val) (hstrength_max : strength.val ≤ 1000000000)
        (htask_le_worker : ∀ i : Nat, i < n → ∀ j : Nat, j < m →
          taskAt (taskVals tasks) i ≤ workerAt (workerVals workers) j), ∃ r : Std.I64,
          Aegis.MaxTaskAssign.max_task_assign tasks workers pills strength = ok r ∧
          r.val = ((min n m : Nat) : Int)) := by
    sorry

  end AegisSpec.MaxTaskAssign
