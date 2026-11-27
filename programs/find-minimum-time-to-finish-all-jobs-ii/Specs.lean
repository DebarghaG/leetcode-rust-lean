import Aegis.MinimumTime.Code.Funs

/-!
# Specifications of `Aegis.MinimumTime.minimum_time`

LeetCode problem `find-minimum-time-to-finish-all-jobs-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumTime

def valAt (xs : Slice Std.I64) (n : Nat) (h : xs.val.length = n) (i : Fin n) : Int :=
  (xs.val.get (Fin.cast h.symm i)).val

def listValAt (xs : List Int) (n : Nat) (h : xs.length = n) (i : Fin n) : Int :=
  xs.get (Fin.cast h.symm i)

def listMax : List Int → Int
  | [] => 0
  | x :: xs => xs.foldr max x

def listMin : List Int → Int
  | [] => 0
  | x :: xs => xs.foldr min x

def sliceMax (xs : Slice Std.I64) : Int := listMax (xs.val.map (fun x => x.val))

def sliceMin (xs : Slice Std.I64) : Int := listMin (xs.val.map (fun x => x.val))

def ceilDiv (a b : Int) : Int := (a + b - 1) / b

def makespan (jobs workers : Slice Std.I64) (n : Nat) (h_jobs : jobs.val.length = n)
    (h_workers : workers.val.length = n) (p : Equiv.Perm (Fin n)) : Int :=
  listMax (List.ofFn (fun i : Fin n =>
    ceilDiv (valAt jobs n h_jobs i) (valAt workers n h_workers (p i))))

def Feasible (jobs workers : Slice Std.I64) (n : Nat) (h_jobs : jobs.val.length = n)
    (h_workers : workers.val.length = n) (D : Int) : Prop :=
  ∃ p : Equiv.Perm (Fin n), ∀ i : Fin n,
    valAt jobs n h_jobs i ≤ D * valAt workers n h_workers (p i)

def SortedPerm (xs ys : List Int) : Prop := xs.Perm ys ∧ xs.Pairwise (· ≤ ·)

def sortedFormula (js ws : List Int) (n : Nat) (h_js : js.length = n) (h_ws : ws.length = n) :
    Int :=
  listMax (List.ofFn (fun i : Fin n => ceilDiv (listValAt js n h_js i) (listValAt ws n h_ws i)))

/-- The function returns a result r, and r is the minimum, over all bijections p from {0,...,n-1} to {0,...,n-1}, of the maximum over i with 0 <= i < n of ceil(jobs[i] / workers[p(i)]), where ceil(a/b) is the least integer d such that d * b >= a. Equivalently, r is the least integer D >= 0 for which there exists a bijection p from {0,...,n-1} to {0,...,n-1} such that jobs[i] <= D * workers[p(i)] for every i with 0 <= i < n.
  Preconditions: Let n = len(jobs) = len(workers). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= jobs[i] <= 100000 and 1 <= workers[i] <= 100000. -/
theorem spec_1
    (jobs workers : Slice Std.I64) (n : Nat)
    (h_jobs : jobs.val.length = n) (h_workers : workers.val.length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_jobs_bounds : ∀ i : Fin n, 1 ≤ valAt jobs n h_jobs i ∧ valAt jobs n h_jobs i ≤ 100000)
    (h_workers_bounds : ∀ j : Fin n,
      1 ≤ valAt workers n h_workers j ∧ valAt workers n h_workers j ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MinimumTime.minimum_time jobs workers = ok r ∧

      (∀ p : Equiv.Perm (Fin n), r.val ≤ makespan jobs workers n h_jobs h_workers p) ∧
      (∃ p : Equiv.Perm (Fin n), makespan jobs workers n h_jobs h_workers p = r.val) ∧

      Feasible jobs workers n h_jobs h_workers r.val ∧
      (∀ D : Int, 0 ≤ D → Feasible jobs workers n h_jobs h_workers D → r.val ≤ D) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (jobs workers : Slice Std.I64) (n : Nat)
    (h_jobs : jobs.val.length = n) (h_workers : workers.val.length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_jobs_bounds : ∀ i : Fin n, 1 ≤ valAt jobs n h_jobs i ∧ valAt jobs n h_jobs i ≤ 100000)
    (h_workers_bounds : ∀ j : Fin n,
      1 ≤ valAt workers n h_workers j ∧ valAt workers n h_workers j ≤ 100000), ∃ r : Std.I64,
      Aegis.MinimumTime.minimum_time jobs workers = ok r ∧

      (∀ p : Equiv.Perm (Fin n), r.val ≤ makespan jobs workers n h_jobs h_workers p) ∧
      (∃ p : Equiv.Perm (Fin n), makespan jobs workers n h_jobs h_workers p = r.val) ∧

      Feasible jobs workers n h_jobs h_workers r.val ∧
      (∀ D : Int, 0 ≤ D → Feasible jobs workers n h_jobs h_workers D → r.val ≤ D)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, overflow, panic, or go out of bounds.
  Preconditions: Let n = len(jobs) = len(workers). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= jobs[i] <= 100000 and 1 <= workers[i] <= 100000. -/
theorem spec_2
    (jobs workers : Slice Std.I64) (n : Nat)
    (h_jobs : jobs.val.length = n) (h_workers : workers.val.length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_jobs_bounds : ∀ i : Fin n, 1 ≤ valAt jobs n h_jobs i ∧ valAt jobs n h_jobs i ≤ 100000)
    (h_workers_bounds : ∀ j : Fin n,
      1 ≤ valAt workers n h_workers j ∧ valAt workers n h_workers j ≤ 100000) :
    ∃ r : Std.I64, Aegis.MinimumTime.minimum_time jobs workers = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (jobs workers : Slice Std.I64) (n : Nat)
    (h_jobs : jobs.val.length = n) (h_workers : workers.val.length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_jobs_bounds : ∀ i : Fin n, 1 ≤ valAt jobs n h_jobs i ∧ valAt jobs n h_jobs i ≤ 100000)
    (h_workers_bounds : ∀ j : Fin n,
      1 ≤ valAt workers n h_workers j ∧ valAt workers n h_workers j ≤ 100000), ∃ r : Std.I64, Aegis.MinimumTime.minimum_time jobs workers = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= ceil( (max_{0 <= i < n} jobs[i]) / (max_{0 <= j < n} workers[j]) ), where ceil(a/b) is the least integer d with d * b >= a.
  Preconditions: Let n = len(jobs) = len(workers). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= jobs[i] <= 100000 and 1 <= workers[i] <= 100000. -/
theorem spec_3
    (jobs workers : Slice Std.I64) (n : Nat)
    (h_jobs : jobs.val.length = n) (h_workers : workers.val.length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_jobs_bounds : ∀ i : Fin n, 1 ≤ valAt jobs n h_jobs i ∧ valAt jobs n h_jobs i ≤ 100000)
    (h_workers_bounds : ∀ j : Fin n,
      1 ≤ valAt workers n h_workers j ∧ valAt workers n h_workers j ≤ 100000)
    (r : Std.I64) :
    Aegis.MinimumTime.minimum_time jobs workers = ok r →
      ceilDiv (sliceMax jobs) (sliceMax workers) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (jobs workers : Slice Std.I64) (n : Nat)
    (h_jobs : jobs.val.length = n) (h_workers : workers.val.length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_jobs_bounds : ∀ i : Fin n, 1 ≤ valAt jobs n h_jobs i ∧ valAt jobs n h_jobs i ≤ 100000)
    (h_workers_bounds : ∀ j : Fin n,
      1 ≤ valAt workers n h_workers j ∧ valAt workers n h_workers j ≤ 100000)
    (r : Std.I64), Aegis.MinimumTime.minimum_time jobs workers = ok r →
      ceilDiv (sliceMax jobs) (sliceMax workers) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= ceil( (max_{0 <= i < n} jobs[i]) / (min_{0 <= j < n} workers[j]) ), where ceil(a/b) is the least integer d with d * b >= a.
  Preconditions: Let n = len(jobs) = len(workers). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= jobs[i] <= 100000 and 1 <= workers[i] <= 100000. -/
theorem spec_4
    (jobs workers : Slice Std.I64) (n : Nat)
    (h_jobs : jobs.val.length = n) (h_workers : workers.val.length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_jobs_bounds : ∀ i : Fin n, 1 ≤ valAt jobs n h_jobs i ∧ valAt jobs n h_jobs i ≤ 100000)
    (h_workers_bounds : ∀ j : Fin n,
      1 ≤ valAt workers n h_workers j ∧ valAt workers n h_workers j ≤ 100000)
    (r : Std.I64) :
    Aegis.MinimumTime.minimum_time jobs workers = ok r →
      r.val ≤ ceilDiv (sliceMax jobs) (sliceMin workers) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (jobs workers : Slice Std.I64) (n : Nat)
    (h_jobs : jobs.val.length = n) (h_workers : workers.val.length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_jobs_bounds : ∀ i : Fin n, 1 ≤ valAt jobs n h_jobs i ∧ valAt jobs n h_jobs i ≤ 100000)
    (h_workers_bounds : ∀ j : Fin n,
      1 ≤ valAt workers n h_workers j ∧ valAt workers n h_workers j ≤ 100000)
    (r : Std.I64), Aegis.MinimumTime.minimum_time jobs workers = ok r →
      r.val ≤ ceilDiv (sliceMax jobs) (sliceMin workers)) := by
  sorry

/-- Whenever minimum_time(jobs, workers) returns r and minimum_time(jobs', workers') returns r', we have r = r'.
  Preconditions: Let n = len(jobs) = len(workers). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= jobs[i] <= 100000 and 1 <= workers[i] <= 100000. Let σ and τ be permutations of {0,...,n-1}. Define jobs'[i] = jobs[σ(i)] and workers'[j] = workers[τ(j)] for all 0 <= i,j < n. -/
theorem spec_5
    (jobs workers jobs' workers' : Slice Std.I64) (n : Nat)
    (h_jobs : jobs.val.length = n) (h_workers : workers.val.length = n)
    (h_jobs_len' : jobs'.val.length = n) (h_workers_len' : workers'.val.length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_jobs_bounds : ∀ i : Fin n, 1 ≤ valAt jobs n h_jobs i ∧ valAt jobs n h_jobs i ≤ 100000)
    (h_workers_bounds : ∀ j : Fin n,
      1 ≤ valAt workers n h_workers j ∧ valAt workers n h_workers j ≤ 100000)
    (σ τ : Equiv.Perm (Fin n))
    (h_jobs_perm : ∀ i : Fin n, valAt jobs' n h_jobs_len' i = valAt jobs n h_jobs (σ i))
    (h_workers_perm : ∀ j : Fin n,
      valAt workers' n h_workers_len' j = valAt workers n h_workers (τ j))
    (r r' : Std.I64) :
    Aegis.MinimumTime.minimum_time jobs workers = ok r →
      Aegis.MinimumTime.minimum_time jobs' workers' = ok r' → r.val = r'.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (jobs workers jobs' workers' : Slice Std.I64) (n : Nat)
    (h_jobs : jobs.val.length = n) (h_workers : workers.val.length = n)
    (h_jobs_len' : jobs'.val.length = n) (h_workers_len' : workers'.val.length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_jobs_bounds : ∀ i : Fin n, 1 ≤ valAt jobs n h_jobs i ∧ valAt jobs n h_jobs i ≤ 100000)
    (h_workers_bounds : ∀ j : Fin n,
      1 ≤ valAt workers n h_workers j ∧ valAt workers n h_workers j ≤ 100000)
    (σ τ : Equiv.Perm (Fin n))
    (h_jobs_perm : ∀ i : Fin n, valAt jobs' n h_jobs_len' i = valAt jobs n h_jobs (σ i))
    (h_workers_perm : ∀ j : Fin n,
      valAt workers' n h_workers_len' j = valAt workers n h_workers (τ j))
    (r r' : Std.I64), Aegis.MinimumTime.minimum_time jobs workers = ok r →
      Aegis.MinimumTime.minimum_time jobs' workers' = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever minimum_time(jobs, workers) returns r and minimum_time(jobs2, workers) returns r2, we have r <= r2.
  Preconditions: Let n = len(jobs) = len(workers) = len(jobs2). Assume 1 <= n <= 100000, all entries of jobs, jobs2, and workers are between 1 and 100000, and jobs[i] <= jobs2[i] for every i with 0 <= i < n. -/
theorem spec_6
    (jobs jobs2 workers : Slice Std.I64) (n : Nat)
    (h_jobs : jobs.val.length = n) (h_jobs2 : jobs2.val.length = n)
    (h_workers : workers.val.length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_jobs_bounds : ∀ i : Fin n, 1 ≤ valAt jobs n h_jobs i ∧ valAt jobs n h_jobs i ≤ 100000)
    (h_jobs2_bounds : ∀ i : Fin n,
      1 ≤ valAt jobs2 n h_jobs2 i ∧ valAt jobs2 n h_jobs2 i ≤ 100000)
    (h_workers_bounds : ∀ j : Fin n,
      1 ≤ valAt workers n h_workers j ∧ valAt workers n h_workers j ≤ 100000)
    (h_mono : ∀ i : Fin n, valAt jobs n h_jobs i ≤ valAt jobs2 n h_jobs2 i)
    (r r2 : Std.I64) :
    Aegis.MinimumTime.minimum_time jobs workers = ok r →
      Aegis.MinimumTime.minimum_time jobs2 workers = ok r2 → r.val ≤ r2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (jobs jobs2 workers : Slice Std.I64) (n : Nat)
    (h_jobs : jobs.val.length = n) (h_jobs2 : jobs2.val.length = n)
    (h_workers : workers.val.length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_jobs_bounds : ∀ i : Fin n, 1 ≤ valAt jobs n h_jobs i ∧ valAt jobs n h_jobs i ≤ 100000)
    (h_jobs2_bounds : ∀ i : Fin n,
      1 ≤ valAt jobs2 n h_jobs2 i ∧ valAt jobs2 n h_jobs2 i ≤ 100000)
    (h_workers_bounds : ∀ j : Fin n,
      1 ≤ valAt workers n h_workers j ∧ valAt workers n h_workers j ≤ 100000)
    (h_mono : ∀ i : Fin n, valAt jobs n h_jobs i ≤ valAt jobs2 n h_jobs2 i)
    (r r2 : Std.I64), Aegis.MinimumTime.minimum_time jobs workers = ok r →
      Aegis.MinimumTime.minimum_time jobs2 workers = ok r2 → r.val ≤ r2.val) := by
  sorry

/-- Whenever minimum_time(jobs, workers) returns r and minimum_time(jobs, workers2) returns r2, we have r2 <= r.
  Preconditions: Let n = len(jobs) = len(workers) = len(workers2). Assume 1 <= n <= 100000, all entries of jobs, workers, and workers2 are between 1 and 100000, and workers[j] <= workers2[j] for every j with 0 <= j < n. -/
theorem spec_7
    (jobs workers workers2 : Slice Std.I64) (n : Nat)
    (h_jobs : jobs.val.length = n)
    (h_workers : workers.val.length = n) (h_workers2 : workers2.val.length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_jobs_bounds : ∀ i : Fin n, 1 ≤ valAt jobs n h_jobs i ∧ valAt jobs n h_jobs i ≤ 100000)
    (h_workers_bounds : ∀ j : Fin n,
      1 ≤ valAt workers n h_workers j ∧ valAt workers n h_workers j ≤ 100000)
    (h_workers2_bounds : ∀ j : Fin n,
      1 ≤ valAt workers2 n h_workers2 j ∧ valAt workers2 n h_workers2 j ≤ 100000)
    (h_mono : ∀ j : Fin n, valAt workers n h_workers j ≤ valAt workers2 n h_workers2 j)
    (r r2 : Std.I64) :
    Aegis.MinimumTime.minimum_time jobs workers = ok r →
      Aegis.MinimumTime.minimum_time jobs workers2 = ok r2 → r2.val ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (jobs workers workers2 : Slice Std.I64) (n : Nat)
    (h_jobs : jobs.val.length = n)
    (h_workers : workers.val.length = n) (h_workers2 : workers2.val.length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_jobs_bounds : ∀ i : Fin n, 1 ≤ valAt jobs n h_jobs i ∧ valAt jobs n h_jobs i ≤ 100000)
    (h_workers_bounds : ∀ j : Fin n,
      1 ≤ valAt workers n h_workers j ∧ valAt workers n h_workers j ≤ 100000)
    (h_workers2_bounds : ∀ j : Fin n,
      1 ≤ valAt workers2 n h_workers2 j ∧ valAt workers2 n h_workers2 j ≤ 100000)
    (h_mono : ∀ j : Fin n, valAt workers n h_workers j ≤ valAt workers2 n h_workers2 j)
    (r r2 : Std.I64), Aegis.MinimumTime.minimum_time jobs workers = ok r →
      Aegis.MinimumTime.minimum_time jobs workers2 = ok r2 → r2.val ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists a bijection p from {0,...,n-1} to {0,...,n-1} such that for every i with 0 <= i < n, jobs[i] <= r * workers[p(i)]; equivalently, ceil(jobs[i] / workers[p(i)]) <= r, where ceil(a/b) is the least integer d with d * b >= a.
  Preconditions: Let n = len(jobs) = len(workers). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= jobs[i] <= 100000 and 1 <= workers[i] <= 100000. -/
theorem spec_8
    (jobs workers : Slice Std.I64) (n : Nat)
    (h_jobs : jobs.val.length = n) (h_workers : workers.val.length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_jobs_bounds : ∀ i : Fin n, 1 ≤ valAt jobs n h_jobs i ∧ valAt jobs n h_jobs i ≤ 100000)
    (h_workers_bounds : ∀ j : Fin n,
      1 ≤ valAt workers n h_workers j ∧ valAt workers n h_workers j ≤ 100000)
    (r : Std.I64) :
    Aegis.MinimumTime.minimum_time jobs workers = ok r →
      ∃ p : Equiv.Perm (Fin n), ∀ i : Fin n,
        valAt jobs n h_jobs i ≤ r.val * valAt workers n h_workers (p i) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (jobs workers : Slice Std.I64) (n : Nat)
    (h_jobs : jobs.val.length = n) (h_workers : workers.val.length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_jobs_bounds : ∀ i : Fin n, 1 ≤ valAt jobs n h_jobs i ∧ valAt jobs n h_jobs i ≤ 100000)
    (h_workers_bounds : ∀ j : Fin n,
      1 ≤ valAt workers n h_workers j ∧ valAt workers n h_workers j ≤ 100000)
    (r : Std.I64), Aegis.MinimumTime.minimum_time jobs workers = ok r →
      ∃ p : Equiv.Perm (Fin n), ∀ i : Fin n,
        valAt jobs n h_jobs i ≤ r.val * valAt workers n h_workers (p i)) := by
  sorry

/-- Whenever the function returns a result r, r = max_{0 <= i < n} ceil(js[i] / ws[i]), where ceil(a/b) is the least integer d with d * b >= a.
  Preconditions: Let n = len(jobs) = len(workers). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= jobs[i] <= 100000 and 1 <= workers[i] <= 100000. Let js be jobs sorted in nondecreasing order, and let ws be workers sorted in nondecreasing order. -/
theorem spec_9
    (jobs workers : Slice Std.I64) (n : Nat)
    (h_jobs : jobs.val.length = n) (h_workers : workers.val.length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_jobs_bounds : ∀ i : Fin n, 1 ≤ valAt jobs n h_jobs i ∧ valAt jobs n h_jobs i ≤ 100000)
    (h_workers_bounds : ∀ j : Fin n,
      1 ≤ valAt workers n h_workers j ∧ valAt workers n h_workers j ≤ 100000)
    (js ws : List Int)
    (h_js : js.length = n) (h_ws : ws.length = n)
    (h_js_sorted : SortedPerm js (jobs.val.map (fun x => x.val)))
    (h_ws_sorted : SortedPerm ws (workers.val.map (fun x => x.val)))
    (r : Std.I64) :
    Aegis.MinimumTime.minimum_time jobs workers = ok r →
      r.val = sortedFormula js ws n h_js h_ws := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (jobs workers : Slice Std.I64) (n : Nat)
    (h_jobs : jobs.val.length = n) (h_workers : workers.val.length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_jobs_bounds : ∀ i : Fin n, 1 ≤ valAt jobs n h_jobs i ∧ valAt jobs n h_jobs i ≤ 100000)
    (h_workers_bounds : ∀ j : Fin n,
      1 ≤ valAt workers n h_workers j ∧ valAt workers n h_workers j ≤ 100000)
    (js ws : List Int)
    (h_js : js.length = n) (h_ws : ws.length = n)
    (h_js_sorted : SortedPerm js (jobs.val.map (fun x => x.val)))
    (h_ws_sorted : SortedPerm ws (workers.val.map (fun x => x.val)))
    (r : Std.I64), Aegis.MinimumTime.minimum_time jobs workers = ok r →
      r.val = sortedFormula js ws n h_js h_ws) := by
  sorry

end AegisSpec.MinimumTime
