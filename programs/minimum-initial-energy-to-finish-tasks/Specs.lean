import Aegis.MinimumEffort.Code.Funs

/-!
# Specifications of `Aegis.MinimumEffort.minimum_effort`

LeetCode problem `minimum-initial-energy-to-finish-tasks`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.MinimumEffort (minimum_effort)

namespace AegisSpec.MinimumEffort

def vecScalars (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map (fun x => x.val)

def taskScalars (tasks : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : Option (List ℤ) :=
  (tasks.val[i]?).map vecScalars

def sumOver (f : ℕ → ℤ) (n : ℕ) : ℤ := ((List.range n).map f).sum

def maxOver (f : ℕ → ℤ) (n : ℕ) : ℤ := ((List.range n).map f).max?.getD 0

def minOver (f : ℕ → ℤ) (n : ℕ) : ℤ := ((List.range n).map f).min?.getD 0

def prefixWork (a : ℕ → ℤ) (p : ℕ → ℕ) (k : ℕ) : ℤ := sumOver (fun j => a (p j)) k

def totalWork (a : ℕ → ℤ) (n : ℕ) : ℤ := sumOver a n

def scheduleNeed (a m : ℕ → ℤ) (n : ℕ) (p : ℕ → ℕ) : ℤ :=
  maxOver (fun k => m (p k) + prefixWork a p k) n

def IsPermOn (n : ℕ) (p : ℕ → ℕ) : Prop :=
  (∀ k, k < n → p k < n) ∧ ∀ k l, k < n → l < n → p k = p l → k = l

structure ValidTasks (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ) : Prop where

  len_eq : n = tasks.val.length

  n_pos : 1 ≤ n

  n_le : n ≤ 100000

  shape : ∀ i, i < n → taskScalars tasks i = some [a i, m i]

  a_pos : ∀ i, i < n → 1 ≤ a i

  a_le_m : ∀ i, i < n → a i ≤ m i

  m_le : ∀ i, i < n → m i ≤ 10000

/-- Whenever minimum_effort(tasks) returns r, for every integer E the following two conditions are equivalent: (1) there exists a permutation p of {0,...,n-1} such that for every k with 0 <= k < n, E >= m_{p(k)} + (sum of a_{p(j)} for 0 <= j < k); (2) E >= r. Thus r is exactly the least integer initial energy that permits finishing all tasks in some order.
  Preconditions: Let n = len(tasks). Assume 1 <= n <= 100000. For every i with 0 <= i < n, assume len(tasks[i]) = 2. Write a_i = tasks[i][0] and m_i = tasks[i][1]; assume 1 <= a_i <= m_i <= 10000. -/
theorem spec_1 (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m) :
    ∀ r : I64, minimum_effort tasks = ok r → ∀ E : ℤ,
      ((∃ p : ℕ → ℕ, IsPermOn n p ∧ ∀ k, k < n → E ≥ m (p k) + prefixWork a p k)
        ↔ E ≥ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m), ∀ r : I64, minimum_effort tasks = ok r → ∀ E : ℤ,
      ((∃ p : ℕ → ℕ, IsPermOn n p ∧ ∀ k, k < n → E ≥ m (p k) + prefixWork a p k)
        ↔ E ≥ r.val)) := by
  sorry

/-- The function minimum_effort(tasks) returns a result: there exists r such that the Lean result is Result.ok r. It does not fail, overflow, or panic.
  Preconditions: Let n = len(tasks). Assume 1 <= n <= 100000. For every i with 0 <= i < n, assume len(tasks[i]) = 2. Write a_i = tasks[i][0] and m_i = tasks[i][1]; assume 1 <= a_i <= m_i <= 10000. -/
theorem spec_2 (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m) :
    ∃ r : I64, minimum_effort tasks = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m), ∃ r : I64, minimum_effort tasks = ok r) := by
  sorry

/-- Whenever minimum_effort(tasks) returns r, for every i with 0 <= i < n we have r >= m_i; equivalently r >= max_{0 <= i < n} m_i.
  Preconditions: Let n = len(tasks). Assume 1 <= n <= 100000. For every i with 0 <= i < n, assume len(tasks[i]) = 2. Write a_i = tasks[i][0] and m_i = tasks[i][1]; assume 1 <= a_i <= m_i <= 10000. -/
theorem spec_3 (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m) :
    ∀ r : I64, minimum_effort tasks = ok r → ∀ i, i < n → r.val ≥ m i := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m), ∀ r : I64, minimum_effort tasks = ok r → ∀ i, i < n → r.val ≥ m i) := by
  sorry

/-- Whenever minimum_effort(tasks) returns r, r >= (sum_{i=0}^{n-1} a_i) + min_{0 <= i < n} (m_i - a_i).
  Preconditions: Let n = len(tasks). Assume 1 <= n <= 100000. For every i with 0 <= i < n, assume len(tasks[i]) = 2. Write a_i = tasks[i][0] and m_i = tasks[i][1]; assume 1 <= a_i <= m_i <= 10000. -/
theorem spec_4 (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m) :
    ∀ r : I64, minimum_effort tasks = ok r →
      r.val ≥ totalWork a n + minOver (fun i => m i - a i) n := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m), ∀ r : I64, minimum_effort tasks = ok r →
      r.val ≥ totalWork a n + minOver (fun i => m i - a i) n) := by
  sorry

/-- Whenever minimum_effort(tasks) returns r, r <= (sum_{i=0}^{n-1} a_i) + max_{0 <= i < n} (m_i - a_i).
  Preconditions: Let n = len(tasks). Assume 1 <= n <= 100000. For every i with 0 <= i < n, assume len(tasks[i]) = 2. Write a_i = tasks[i][0] and m_i = tasks[i][1]; assume 1 <= a_i <= m_i <= 10000. -/
theorem spec_5 (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m) :
    ∀ r : I64, minimum_effort tasks = ok r →
      r.val ≤ totalWork a n + maxOver (fun i => m i - a i) n := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m), ∀ r : I64, minimum_effort tasks = ok r →
      r.val ≤ totalWork a n + maxOver (fun i => m i - a i) n) := by
  sorry

/-- Whenever minimum_effort(tasks) returns r, for every permutation p of {0,...,n-1}, r <= max_{0 <= k < n} (m_{p(k)} + (sum of a_{p(j)} for 0 <= j < k)).
  Preconditions: Let n = len(tasks). Assume 1 <= n <= 100000. For every i with 0 <= i < n, assume len(tasks[i]) = 2. Write a_i = tasks[i][0] and m_i = tasks[i][1]; assume 1 <= a_i <= m_i <= 10000. -/
theorem spec_6 (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m) :
    ∀ r : I64, minimum_effort tasks = ok r →
      ∀ p : ℕ → ℕ, IsPermOn n p → r.val ≤ scheduleNeed a m n p := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m), ∀ r : I64, minimum_effort tasks = ok r →
      ∀ p : ℕ → ℕ, IsPermOn n p → r.val ≤ scheduleNeed a m n p) := by
  sorry

/-- Whenever minimum_effort(tasks) returns r, r = (sum_{i=0}^{n-1} a_i) + D.
  Preconditions: Let n = len(tasks). Assume 1 <= n <= 100000. For every i with 0 <= i < n, assume len(tasks[i]) = 2. Write a_i = tasks[i][0] and m_i = tasks[i][1]; assume 1 <= a_i <= m_i <= 10000. Assume additionally that there exists an integer D such that m_i - a_i = D for every i with 0 <= i < n. -/
theorem spec_7 (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m) (D : ℤ) (hD : ∀ i, i < n → m i - a i = D) :
    ∀ r : I64, minimum_effort tasks = ok r → r.val = totalWork a n + D := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m) (D : ℤ) (hD : ∀ i, i < n → m i - a i = D), ∀ r : I64, minimum_effort tasks = ok r → r.val = totalWork a n + D) := by
  sorry

/-- Whenever minimum_effort(tasks) returns r, r = M + (sum_{i=0}^{n-1} a_i) - max_{0 <= i < n} a_i.
  Preconditions: Let n = len(tasks). Assume 1 <= n <= 100000. For every i with 0 <= i < n, assume len(tasks[i]) = 2. Write a_i = tasks[i][0] and m_i = tasks[i][1]; assume 1 <= a_i <= m_i <= 10000. Assume additionally that there exists an integer M such that m_i = M for every i with 0 <= i < n. -/
theorem spec_8 (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m) (M : ℤ) (hM : ∀ i, i < n → m i = M) :
    ∀ r : I64, minimum_effort tasks = ok r → r.val = M + totalWork a n - maxOver a n := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m) (M : ℤ) (hM : ∀ i, i < n → m i = M), ∀ r : I64, minimum_effort tasks = ok r → r.val = M + totalWork a n - maxOver a n) := by
  sorry

/-- Whenever minimum_effort(tasks) returns r and minimum_effort(tasks') returns r', we have r = r'.
  Preconditions: Let n = len(tasks). Assume 1 <= n <= 100000. For every i with 0 <= i < n, assume len(tasks[i]) = 2. Write a_i = tasks[i][0] and m_i = tasks[i][1]; assume 1 <= a_i <= m_i <= 10000. Let tasks' be a valid task list under the same constraints with len(tasks') = n, and assume there is a permutation q of {0,...,n-1} such that tasks'[i] = tasks[q(i)] for every i with 0 <= i < n. -/
theorem spec_9 (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m)
    (tasks' : Slice (alloc.vec.Vec Std.I64)) (a' m' : ℕ → ℤ) (h' : ValidTasks tasks' n a' m')
    (q : ℕ → ℕ) (hq : IsPermOn n q)
    (hqt : ∀ i, i < n → taskScalars tasks' i = taskScalars tasks (q i)) :
    ∀ r r' : I64, minimum_effort tasks = ok r → minimum_effort tasks' = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m)
    (tasks' : Slice (alloc.vec.Vec Std.I64)) (a' m' : ℕ → ℤ) (h' : ValidTasks tasks' n a' m')
    (q : ℕ → ℕ) (hq : IsPermOn n q)
    (hqt : ∀ i, i < n → taskScalars tasks' i = taskScalars tasks (q i)), ∀ r r' : I64, minimum_effort tasks = ok r → minimum_effort tasks' = ok r' →
      r.val = r'.val) := by
  sorry

/-- Whenever minimum_effort(tasks) returns r and minimum_effort(tasks') returns r', we have r <= r'.
  Preconditions: Let n = len(tasks) = len(tasks'). Assume both tasks and tasks' are valid task lists: for every i with 0 <= i < n, len(tasks[i]) = len(tasks'[i]) = 2, and writing a_i = tasks[i][0], m_i = tasks[i][1], a'_i = tasks'[i][0], m'_i = tasks'[i][1], we have 1 <= a_i <= m_i <= 10000 and 1 <= a'_i <= m'_i <= 10000. Assume moreover a_i <= a'_i and m_i <= m'_i for every i with 0 <= i < n. -/
theorem spec_10 (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m)
    (tasks' : Slice (alloc.vec.Vec Std.I64)) (a' m' : ℕ → ℤ) (h' : ValidTasks tasks' n a' m')
    (hmono : ∀ i, i < n → a i ≤ a' i ∧ m i ≤ m' i) :
    ∀ r r' : I64, minimum_effort tasks = ok r → minimum_effort tasks' = ok r' →
      r.val ≤ r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m)
    (tasks' : Slice (alloc.vec.Vec Std.I64)) (a' m' : ℕ → ℤ) (h' : ValidTasks tasks' n a' m')
    (hmono : ∀ i, i < n → a i ≤ a' i ∧ m i ≤ m' i), ∀ r r' : I64, minimum_effort tasks = ok r → minimum_effort tasks' = ok r' →
      r.val ≤ r'.val) := by
  sorry

/-- Whenever minimum_effort(tasks) returns r, if p is a permutation of {0,...,n-1} such that d_{p(0)} >= d_{p(1)} >= ... >= d_{p(n-1)}, then r = max_{0 <= k < n} (m_{p(k)} + (sum of a_{p(j)} for 0 <= j < k)).
  Preconditions: Let n = len(tasks). Assume 1 <= n <= 100000. For every i with 0 <= i < n, assume len(tasks[i]) = 2. Write a_i = tasks[i][0] and m_i = tasks[i][1]; assume 1 <= a_i <= m_i <= 10000. Let d_i = m_i - a_i. -/
theorem spec_11 (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m) (p : ℕ → ℕ) (hp : IsPermOn n p)
    (hdesc : ∀ k, k + 1 < n →
      m (p k) - a (p k) ≥ m (p (k + 1)) - a (p (k + 1))) :
    ∀ r : I64, minimum_effort tasks = ok r → r.val = scheduleNeed a m n p := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) (a m : ℕ → ℤ)
    (h : ValidTasks tasks n a m) (p : ℕ → ℕ) (hp : IsPermOn n p)
    (hdesc : ∀ k, k + 1 < n →
      m (p k) - a (p k) ≥ m (p (k + 1)) - a (p (k + 1))), ∀ r : I64, minimum_effort tasks = ok r → r.val = scheduleNeed a m n p) := by
  sorry

end AegisSpec.MinimumEffort
