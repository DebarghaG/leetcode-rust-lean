import Aegis.MinimumRounds.Code.Funs

/-!
# Specifications of `Aegis.MinimumRounds.minimum_rounds`

LeetCode problem `minimum-rounds-to-complete-all-tasks`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.MinimumRounds (minimum_rounds)

namespace AegisSpec.MinimumRounds

def countOcc (tasks : Slice Std.I64) (v : ℤ) : ℕ :=
  (tasks.val.filter (fun x => x.val = v)).length

def distinctVals (tasks : Slice Std.I64) : Finset ℤ :=
  (tasks.val.map (fun x => x.val)).toFinset

def Occurs (tasks : Slice Std.I64) (v : ℤ) : Prop :=
  v ∈ distinctVals tasks

def ceilDiv3 (x : ℕ) : ℕ := (x + 2) / 3

def numDistinct (tasks : Slice Std.I64) : ℕ :=
  (distinctVals tasks).card

def countMultiset (tasks : Slice Std.I64) : Multiset ℕ :=
  (distinctVals tasks).val.map (countOcc tasks)

def totalRounds (tasks : Slice Std.I64) : ℤ :=
  ∑ v ∈ distinctVals tasks, (ceilDiv3 (countOcc tasks v) : ℤ)

def HasSingleton (tasks : Slice Std.I64) : Prop :=
  ∃ v : ℤ, Occurs tasks v ∧ countOcc tasks v = 1

theorem len_val (tasks : Slice Std.I64) : (Slice.len tasks).val = tasks.val.length := rfl

theorem ceilDiv3_spec (x : ℕ) :
    x ≤ 3 * ceilDiv3 x ∧ ∀ q : ℕ, x ≤ 3 * q → ceilDiv3 x ≤ q := by
  constructor
  · show x ≤ 3 * ((x + 2) / 3)
    omega
  · intro q hq
    show (x + 2) / 3 ≤ q
    omega

theorem mem_distinctVals (tasks : Slice Std.I64) (v : ℤ) :
    Occurs tasks v ↔ ∃ x : Std.I64, x ∈ tasks.val ∧ x.val = v := by
  unfold Occurs distinctVals
  simp [List.mem_toFinset, List.mem_map]

theorem countOcc_pos (tasks : Slice Std.I64) (v : ℤ) :
    0 < countOcc tasks v ↔ Occurs tasks v := by
  unfold Occurs distinctVals countOcc
  simp [List.mem_toFinset, List.mem_map, List.length_pos_iff_exists_mem]

theorem hasSingleton_of_length_one (tasks : Slice Std.I64) (h : tasks.val.length = 1) :
    HasSingleton tasks := by
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 h
  refine ⟨x.val, ?_, ?_⟩
  · rw [mem_distinctVals]
    exact ⟨x, by rw [hx]; simp, rfl⟩
  · unfold countOcc
    rw [hx]
    simp

/-- Whenever minimum_rounds(tasks) returns Ok r, r is determined as follows. If there exists v in D with c(v) = 1, then r = -1. Otherwise r = sum over v in D of ceil(c(v)/3), where ceil(x/3) is the least integer q with 3*q >= x.
  Preconditions: tasks is an i64 slice satisfying the problem constraints: n = len(tasks), 1 <= n <= 100000, and 1 <= tasks[i] <= 1000000000 for every i with 0 <= i < n. For an integer v, c(v) is the number of indices i with 0 <= i < n and tasks[i] = v, and D = {tasks[i] | 0 <= i < n}. -/
theorem spec_1 (tasks : Slice Std.I64)
    (hn_pos : 1 ≤ tasks.val.length) (hn_le : tasks.val.length ≤ 100000)
    (hentries : ∀ i (h : i < tasks.val.length),
      1 ≤ (tasks.val[i]'h).val ∧ (tasks.val[i]'h).val ≤ 1000000000)
    (r : Std.I64) (hr : minimum_rounds tasks = ok r) :
    (HasSingleton tasks → r.val = -1) ∧
      (¬ HasSingleton tasks → r.val = totalRounds tasks) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (tasks : Slice Std.I64)
    (hn_pos : 1 ≤ tasks.val.length) (hn_le : tasks.val.length ≤ 100000)
    (hentries : ∀ i (h : i < tasks.val.length),
      1 ≤ (tasks.val[i]'h).val ∧ (tasks.val[i]'h).val ≤ 1000000000)
    (r : Std.I64) (hr : minimum_rounds tasks = ok r), (HasSingleton tasks → r.val = -1) ∧
      (¬ HasSingleton tasks → r.val = totalRounds tasks)) := by
  sorry

/-- For every tasks satisfying the preconditions, minimum_rounds(tasks) returns Ok r for some i64 r; it never returns Err. In particular, no overflow, out-of-bounds access, or panic is used to signal the impossible case; that case is returned as Ok(-1).
  Preconditions: tasks is an i64 slice satisfying the problem constraints: n = len(tasks), 1 <= n <= 100000, and 1 <= tasks[i] <= 1000000000 for every i with 0 <= i < n. For an integer v, c(v) is the number of indices i with 0 <= i < n and tasks[i] = v, and D = {tasks[i] | 0 <= i < n}. -/
theorem spec_2 (tasks : Slice Std.I64)
    (hn_pos : 1 ≤ tasks.val.length) (hn_le : tasks.val.length ≤ 100000)
    (hentries : ∀ i (h : i < tasks.val.length),
      1 ≤ (tasks.val[i]'h).val ∧ (tasks.val[i]'h).val ≤ 1000000000) :
    ∃ r : Std.I64, minimum_rounds tasks = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (tasks : Slice Std.I64)
    (hn_pos : 1 ≤ tasks.val.length) (hn_le : tasks.val.length ≤ 100000)
    (hentries : ∀ i (h : i < tasks.val.length),
      1 ≤ (tasks.val[i]'h).val ∧ (tasks.val[i]'h).val ≤ 1000000000), ∃ r : Std.I64, minimum_rounds tasks = ok r) := by
  sorry

/-- Whenever minimum_rounds(tasks) returns Ok r, either r = -1 or 1 <= r <= 50000.
  Preconditions: tasks is an i64 slice satisfying the problem constraints: n = len(tasks), 1 <= n <= 100000, and 1 <= tasks[i] <= 1000000000 for every i with 0 <= i < n. For an integer v, c(v) is the number of indices i with 0 <= i < n and tasks[i] = v, and D = {tasks[i] | 0 <= i < n}. -/
theorem spec_3 (tasks : Slice Std.I64)
    (hn_pos : 1 ≤ tasks.val.length) (hn_le : tasks.val.length ≤ 100000)
    (hentries : ∀ i (h : i < tasks.val.length),
      1 ≤ (tasks.val[i]'h).val ∧ (tasks.val[i]'h).val ≤ 1000000000)
    (r : Std.I64) (hr : minimum_rounds tasks = ok r) :
    r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ 50000) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (tasks : Slice Std.I64)
    (hn_pos : 1 ≤ tasks.val.length) (hn_le : tasks.val.length ≤ 100000)
    (hentries : ∀ i (h : i < tasks.val.length),
      1 ≤ (tasks.val[i]'h).val ∧ (tasks.val[i]'h).val ≤ 1000000000)
    (r : Std.I64) (hr : minimum_rounds tasks = ok r), r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ 50000)) := by
  sorry

/-- Whenever minimum_rounds(tasks) returns Ok r and r != -1, r >= |D|, where |D| is the number of distinct difficulty values occurring in tasks.
  Preconditions: tasks is an i64 slice satisfying the problem constraints: n = len(tasks), 1 <= n <= 100000, and 1 <= tasks[i] <= 1000000000 for every i with 0 <= i < n. For an integer v, c(v) is the number of indices i with 0 <= i < n and tasks[i] = v, and D = {tasks[i] | 0 <= i < n}. -/
theorem spec_4 (tasks : Slice Std.I64)
    (hn_pos : 1 ≤ tasks.val.length) (hn_le : tasks.val.length ≤ 100000)
    (hentries : ∀ i (h : i < tasks.val.length),
      1 ≤ (tasks.val[i]'h).val ∧ (tasks.val[i]'h).val ≤ 1000000000)
    (r : Std.I64) (hr : minimum_rounds tasks = ok r) (hne : r.val ≠ -1) :
    (numDistinct tasks : ℤ) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (tasks : Slice Std.I64)
    (hn_pos : 1 ≤ tasks.val.length) (hn_le : tasks.val.length ≤ 100000)
    (hentries : ∀ i (h : i < tasks.val.length),
      1 ≤ (tasks.val[i]'h).val ∧ (tasks.val[i]'h).val ≤ 1000000000)
    (r : Std.I64) (hr : minimum_rounds tasks = ok r) (hne : r.val ≠ -1), (numDistinct tasks : ℤ) ≤ r.val) := by
  sorry

/-- Whenever minimum_rounds(tasks) returns Ok r and r != -1, 2*r <= n = len(tasks).
  Preconditions: tasks is an i64 slice satisfying the problem constraints: n = len(tasks), 1 <= n <= 100000, and 1 <= tasks[i] <= 1000000000 for every i with 0 <= i < n. For an integer v, c(v) is the number of indices i with 0 <= i < n and tasks[i] = v, and D = {tasks[i] | 0 <= i < n}. -/
theorem spec_5 (tasks : Slice Std.I64)
    (hn_pos : 1 ≤ tasks.val.length) (hn_le : tasks.val.length ≤ 100000)
    (hentries : ∀ i (h : i < tasks.val.length),
      1 ≤ (tasks.val[i]'h).val ∧ (tasks.val[i]'h).val ≤ 1000000000)
    (r : Std.I64) (hr : minimum_rounds tasks = ok r) (hne : r.val ≠ -1) :
    2 * r.val ≤ (tasks.val.length : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (tasks : Slice Std.I64)
    (hn_pos : 1 ≤ tasks.val.length) (hn_le : tasks.val.length ≤ 100000)
    (hentries : ∀ i (h : i < tasks.val.length),
      1 ≤ (tasks.val[i]'h).val ∧ (tasks.val[i]'h).val ≤ 1000000000)
    (r : Std.I64) (hr : minimum_rounds tasks = ok r) (hne : r.val ≠ -1), 2 * r.val ≤ (tasks.val.length : ℤ)) := by
  sorry

/-- Let M(tasks) be the multiset of positive integers {c(v) | v in D}. For any two slices tasks and tasks' satisfying the preconditions, if M(tasks) = M(tasks'), then whenever minimum_rounds(tasks) returns Ok r and minimum_rounds(tasks') returns Ok r', we have r = r'.
  Preconditions: For each slice, let n = len(tasks), c(v) be the number of indices i with 0 <= i < n and tasks[i] = v, and D = {tasks[i] | 0 <= i < n}; the same definitions apply to tasks' with its own length and entries. Both tasks and tasks' satisfy the problem constraints: lengths between 1 and 100000 and all entries between 1 and 1000000000. -/
theorem spec_6 (tasks tasks' : Slice Std.I64)
    (hn_pos : 1 ≤ tasks.val.length) (hn_le : tasks.val.length ≤ 100000)
    (hentries : ∀ i (h : i < tasks.val.length),
      1 ≤ (tasks.val[i]'h).val ∧ (tasks.val[i]'h).val ≤ 1000000000)
    (hn_pos' : 1 ≤ tasks'.val.length) (hn_le' : tasks'.val.length ≤ 100000)
    (hentries' : ∀ i (h : i < tasks'.val.length),
      1 ≤ (tasks'.val[i]'h).val ∧ (tasks'.val[i]'h).val ≤ 1000000000)
    (hM : countMultiset tasks = countMultiset tasks')
    (r r' : Std.I64) (hr : minimum_rounds tasks = ok r) (hr' : minimum_rounds tasks' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (tasks tasks' : Slice Std.I64)
    (hn_pos : 1 ≤ tasks.val.length) (hn_le : tasks.val.length ≤ 100000)
    (hentries : ∀ i (h : i < tasks.val.length),
      1 ≤ (tasks.val[i]'h).val ∧ (tasks.val[i]'h).val ≤ 1000000000)
    (hn_pos' : 1 ≤ tasks'.val.length) (hn_le' : tasks'.val.length ≤ 100000)
    (hentries' : ∀ i (h : i < tasks'.val.length),
      1 ≤ (tasks'.val[i]'h).val ∧ (tasks'.val[i]'h).val ≤ 1000000000)
    (hM : countMultiset tasks = countMultiset tasks')
    (r r' : Std.I64) (hr : minimum_rounds tasks = ok r) (hr' : minimum_rounds tasks' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever minimum_rounds(tasks) returns Ok r with r != -1, there exists a family of nonnegative integers (a_v, b_v) for v in D such that for every v in D, 2*a_v + 3*b_v = c(v), and r = sum over v in D of (a_v + b_v).
  Preconditions: tasks is an i64 slice satisfying the problem constraints: n = len(tasks), 1 <= n <= 100000, and 1 <= tasks[i] <= 1000000000 for every i with 0 <= i < n. For an integer v, c(v) is the number of indices i with 0 <= i < n and tasks[i] = v, and D = {tasks[i] | 0 <= i < n}. -/
theorem spec_7 (tasks : Slice Std.I64)
    (hn_pos : 1 ≤ tasks.val.length) (hn_le : tasks.val.length ≤ 100000)
    (hentries : ∀ i (h : i < tasks.val.length),
      1 ≤ (tasks.val[i]'h).val ∧ (tasks.val[i]'h).val ≤ 1000000000)
    (r : Std.I64) (hr : minimum_rounds tasks = ok r) (hne : r.val ≠ -1) :
    ∃ a b : ℤ → ℕ,
      (∀ v : ℤ, Occurs tasks v → 2 * (a v : ℤ) + 3 * (b v : ℤ) = (countOcc tasks v : ℤ)) ∧
        r.val = ∑ v ∈ distinctVals tasks, ((a v : ℤ) + (b v : ℤ)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (tasks : Slice Std.I64)
    (hn_pos : 1 ≤ tasks.val.length) (hn_le : tasks.val.length ≤ 100000)
    (hentries : ∀ i (h : i < tasks.val.length),
      1 ≤ (tasks.val[i]'h).val ∧ (tasks.val[i]'h).val ≤ 1000000000)
    (r : Std.I64) (hr : minimum_rounds tasks = ok r) (hne : r.val ≠ -1), ∃ a b : ℤ → ℕ,
      (∀ v : ℤ, Occurs tasks v → 2 * (a v : ℤ) + 3 * (b v : ℤ) = (countOcc tasks v : ℤ)) ∧
        r.val = ∑ v ∈ distinctVals tasks, ((a v : ℤ) + (b v : ℤ))) := by
  sorry

/-- Whenever minimum_rounds(tasks) returns Ok r with r != -1, for every family of nonnegative integers (a_v, b_v) for v in D satisfying 2*a_v + 3*b_v = c(v) for every v in D, we have sum over v in D of (a_v + b_v) >= r.
  Preconditions: tasks is an i64 slice satisfying the problem constraints: n = len(tasks), 1 <= n <= 100000, and 1 <= tasks[i] <= 1000000000 for every i with 0 <= i < n. For an integer v, c(v) is the number of indices i with 0 <= i < n and tasks[i] = v, and D = {tasks[i] | 0 <= i < n}. -/
theorem spec_8 (tasks : Slice Std.I64)
    (hn_pos : 1 ≤ tasks.val.length) (hn_le : tasks.val.length ≤ 100000)
    (hentries : ∀ i (h : i < tasks.val.length),
      1 ≤ (tasks.val[i]'h).val ∧ (tasks.val[i]'h).val ≤ 1000000000)
    (r : Std.I64) (hr : minimum_rounds tasks = ok r) (hne : r.val ≠ -1) :
    ∀ a b : ℤ → ℕ,
      (∀ v : ℤ, Occurs tasks v → 2 * (a v : ℤ) + 3 * (b v : ℤ) = (countOcc tasks v : ℤ)) →
        r.val ≤ ∑ v ∈ distinctVals tasks, ((a v : ℤ) + (b v : ℤ)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (tasks : Slice Std.I64)
    (hn_pos : 1 ≤ tasks.val.length) (hn_le : tasks.val.length ≤ 100000)
    (hentries : ∀ i (h : i < tasks.val.length),
      1 ≤ (tasks.val[i]'h).val ∧ (tasks.val[i]'h).val ≤ 1000000000)
    (r : Std.I64) (hr : minimum_rounds tasks = ok r) (hne : r.val ≠ -1), ∀ a b : ℤ → ℕ,
      (∀ v : ℤ, Occurs tasks v → 2 * (a v : ℤ) + 3 * (b v : ℤ) = (countOcc tasks v : ℤ)) →
        r.val ≤ ∑ v ∈ distinctVals tasks, ((a v : ℤ) + (b v : ℤ))) := by
  sorry

end AegisSpec.MinimumRounds
