import Aegis.HardestWorker.Code.Funs

/-!
# Specifications of `Aegis.HardestWorker.hardest_worker`

LeetCode problem `the-employee-that-worked-on-the-longest-task`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.HardestWorker

  def vecInts (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map (fun x => x.val)

  def logsInts (logs : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    logs.val.map vecInts

  def logCount (logs : Slice (alloc.vec.Vec Std.I64)) : ℕ := (logsInts logs).length

  def logEntry (logs : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : List ℤ :=
    (logsInts logs).getD i []

  def empId (logs : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    (logEntry logs i).getD 0 0

  def leaveTime (logs : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    (logEntry logs i).getD 1 0

  def dur (logs : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    leaveTime logs i - (if i = 0 then 0 else leaveTime logs (i - 1))

  def durList (logs : Slice (alloc.vec.Vec Std.I64)) : List ℤ :=
    (List.range (logCount logs)).map (dur logs)

  def maxDur (logs : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    (durList logs).max?.getD 0

  /-- Define dur(i) = logs[i][1] - (if i = 0 then 0 else logs[i-1][1]) for 0 <= i < m, and let M = max { dur(i) | 0 <= i < m }. The function returns a result r and: (a) 0 <= r < n; (b) there exists i with 0 <= i < m such that logs[i][0] = r and dur(i) = M; (c) for every i with 0 <= i < m and dur(i) = M, we have r <= logs[i][0].
    Preconditions: Let m = len(logs). We assume 2 <= n <= 500, 1 <= m <= 500, for every i with 0 <= i < m the vector logs[i] has length 2, 0 <= logs[i][0] <= n-1, and 1 <= logs[i][1] <= 500, for every i with 1 <= i < m we have logs[i-1][1] < logs[i][1], and for every i with 0 <= i < m-1 we have logs[i][0] != logs[i+1][0]. -/
  theorem spec_1 (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 500)
      (hm_lo : 1 ≤ logCount logs) (hm_hi : logCount logs ≤ 500)
      (h_shape : ∀ (i : ℕ), i < logCount logs → (logEntry logs i).length = 2)
      (h_id_lo : ∀ (i : ℕ), i < logCount logs → 0 ≤ empId logs i)
      (h_id_hi : ∀ (i : ℕ), i < logCount logs → empId logs i ≤ n.val - 1)
      (h_time_lo : ∀ (i : ℕ), i < logCount logs → 1 ≤ leaveTime logs i)
      (h_time_hi : ∀ (i : ℕ), i < logCount logs → leaveTime logs i ≤ 500)
      (h_time_lt : ∀ (i : ℕ), 1 ≤ i → i < logCount logs →
        leaveTime logs (i - 1) < leaveTime logs i)
      (h_id_ne : ∀ (i : ℕ), i < logCount logs - 1 → empId logs i ≠ empId logs (i + 1)) :
      ∃ r : Std.I64,
        Aegis.HardestWorker.hardest_worker n logs = Result.ok r ∧
          0 ≤ r.val ∧ r.val < n.val ∧
          (∃ (i : ℕ), i < logCount logs ∧ empId logs i = r.val ∧ dur logs i = maxDur logs) ∧
          (∀ (i : ℕ), i < logCount logs → dur logs i = maxDur logs → r.val ≤ empId logs i) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 500)
        (hm_lo : 1 ≤ logCount logs) (hm_hi : logCount logs ≤ 500)
        (h_shape : ∀ (i : ℕ), i < logCount logs → (logEntry logs i).length = 2)
        (h_id_lo : ∀ (i : ℕ), i < logCount logs → 0 ≤ empId logs i)
        (h_id_hi : ∀ (i : ℕ), i < logCount logs → empId logs i ≤ n.val - 1)
        (h_time_lo : ∀ (i : ℕ), i < logCount logs → 1 ≤ leaveTime logs i)
        (h_time_hi : ∀ (i : ℕ), i < logCount logs → leaveTime logs i ≤ 500)
        (h_time_lt : ∀ (i : ℕ), 1 ≤ i → i < logCount logs →
          leaveTime logs (i - 1) < leaveTime logs i)
        (h_id_ne : ∀ (i : ℕ), i < logCount logs - 1 → empId logs i ≠ empId logs (i + 1)), ∃ r : Std.I64,
          Aegis.HardestWorker.hardest_worker n logs = Result.ok r ∧
            0 ≤ r.val ∧ r.val < n.val ∧
            (∃ (i : ℕ), i < logCount logs ∧ empId logs i = r.val ∧ dur logs i = maxDur logs) ∧
            (∀ (i : ℕ), i < logCount logs → dur logs i = maxDur logs → r.val ≤ empId logs i)) := by
    sorry

  /-- Under the preconditions, the function returns a result r; it does not fail, overflow, go out of bounds, or panic.
    Preconditions: Let m = len(logs). We assume 2 <= n <= 500, 1 <= m <= 500, for every i with 0 <= i < m the vector logs[i] has length 2, 0 <= logs[i][0] <= n-1, and 1 <= logs[i][1] <= 500, for every i with 1 <= i < m we have logs[i-1][1] < logs[i][1], and for every i with 0 <= i < m-1 we have logs[i][0] != logs[i+1][0]. -/
  theorem spec_2 (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 500)
      (hm_lo : 1 ≤ logCount logs) (hm_hi : logCount logs ≤ 500)
      (h_shape : ∀ (i : ℕ), i < logCount logs → (logEntry logs i).length = 2)
      (h_id_lo : ∀ (i : ℕ), i < logCount logs → 0 ≤ empId logs i)
      (h_id_hi : ∀ (i : ℕ), i < logCount logs → empId logs i ≤ n.val - 1)
      (h_time_lo : ∀ (i : ℕ), i < logCount logs → 1 ≤ leaveTime logs i)
      (h_time_hi : ∀ (i : ℕ), i < logCount logs → leaveTime logs i ≤ 500)
      (h_time_lt : ∀ (i : ℕ), 1 ≤ i → i < logCount logs →
        leaveTime logs (i - 1) < leaveTime logs i)
      (h_id_ne : ∀ (i : ℕ), i < logCount logs - 1 → empId logs i ≠ empId logs (i + 1)) :
      ∃ r : Std.I64, Aegis.HardestWorker.hardest_worker n logs = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 500)
        (hm_lo : 1 ≤ logCount logs) (hm_hi : logCount logs ≤ 500)
        (h_shape : ∀ (i : ℕ), i < logCount logs → (logEntry logs i).length = 2)
        (h_id_lo : ∀ (i : ℕ), i < logCount logs → 0 ≤ empId logs i)
        (h_id_hi : ∀ (i : ℕ), i < logCount logs → empId logs i ≤ n.val - 1)
        (h_time_lo : ∀ (i : ℕ), i < logCount logs → 1 ≤ leaveTime logs i)
        (h_time_hi : ∀ (i : ℕ), i < logCount logs → leaveTime logs i ≤ 500)
        (h_time_lt : ∀ (i : ℕ), 1 ≤ i → i < logCount logs →
          leaveTime logs (i - 1) < leaveTime logs i)
        (h_id_ne : ∀ (i : ℕ), i < logCount logs - 1 → empId logs i ≠ empId logs (i + 1)), ∃ r : Std.I64, Aegis.HardestWorker.hardest_worker n logs = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < n.
    Preconditions: Let m = len(logs). We assume 2 <= n <= 500, 1 <= m <= 500, for every i with 0 <= i < m the vector logs[i] has length 2, 0 <= logs[i][0] <= n-1, and 1 <= logs[i][1] <= 500, for every i with 1 <= i < m we have logs[i-1][1] < logs[i][1], and for every i with 0 <= i < m-1 we have logs[i][0] != logs[i+1][0]. -/
  theorem spec_3 (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 500)
      (hm_lo : 1 ≤ logCount logs) (hm_hi : logCount logs ≤ 500)
      (h_shape : ∀ (i : ℕ), i < logCount logs → (logEntry logs i).length = 2)
      (h_id_lo : ∀ (i : ℕ), i < logCount logs → 0 ≤ empId logs i)
      (h_id_hi : ∀ (i : ℕ), i < logCount logs → empId logs i ≤ n.val - 1)
      (h_time_lo : ∀ (i : ℕ), i < logCount logs → 1 ≤ leaveTime logs i)
      (h_time_hi : ∀ (i : ℕ), i < logCount logs → leaveTime logs i ≤ 500)
      (h_time_lt : ∀ (i : ℕ), 1 ≤ i → i < logCount logs →
        leaveTime logs (i - 1) < leaveTime logs i)
      (h_id_ne : ∀ (i : ℕ), i < logCount logs - 1 → empId logs i ≠ empId logs (i + 1)) :
      ∀ r : Std.I64, Aegis.HardestWorker.hardest_worker n logs = Result.ok r →
        0 ≤ r.val ∧ r.val < n.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 500)
        (hm_lo : 1 ≤ logCount logs) (hm_hi : logCount logs ≤ 500)
        (h_shape : ∀ (i : ℕ), i < logCount logs → (logEntry logs i).length = 2)
        (h_id_lo : ∀ (i : ℕ), i < logCount logs → 0 ≤ empId logs i)
        (h_id_hi : ∀ (i : ℕ), i < logCount logs → empId logs i ≤ n.val - 1)
        (h_time_lo : ∀ (i : ℕ), i < logCount logs → 1 ≤ leaveTime logs i)
        (h_time_hi : ∀ (i : ℕ), i < logCount logs → leaveTime logs i ≤ 500)
        (h_time_lt : ∀ (i : ℕ), 1 ≤ i → i < logCount logs →
          leaveTime logs (i - 1) < leaveTime logs i)
        (h_id_ne : ∀ (i : ℕ), i < logCount logs - 1 → empId logs i ≠ empId logs (i + 1)), ∀ r : Std.I64, Aegis.HardestWorker.hardest_worker n logs = Result.ok r →
          0 ≤ r.val ∧ r.val < n.val) := by
    sorry

  /-- Define dur(i) = logs[i][1] - (if i = 0 then 0 else logs[i-1][1]) for 0 <= i < m, and let M = max { dur(i) | 0 <= i < m }. Whenever the function returns a result r, there exists i with 0 <= i < m such that logs[i][0] = r and dur(i) = M.
    Preconditions: Let m = len(logs). We assume 2 <= n <= 500, 1 <= m <= 500, for every i with 0 <= i < m the vector logs[i] has length 2, 0 <= logs[i][0] <= n-1, and 1 <= logs[i][1] <= 500, for every i with 1 <= i < m we have logs[i-1][1] < logs[i][1], and for every i with 0 <= i < m-1 we have logs[i][0] != logs[i+1][0]. -/
  theorem spec_4 (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 500)
      (hm_lo : 1 ≤ logCount logs) (hm_hi : logCount logs ≤ 500)
      (h_shape : ∀ (i : ℕ), i < logCount logs → (logEntry logs i).length = 2)
      (h_id_lo : ∀ (i : ℕ), i < logCount logs → 0 ≤ empId logs i)
      (h_id_hi : ∀ (i : ℕ), i < logCount logs → empId logs i ≤ n.val - 1)
      (h_time_lo : ∀ (i : ℕ), i < logCount logs → 1 ≤ leaveTime logs i)
      (h_time_hi : ∀ (i : ℕ), i < logCount logs → leaveTime logs i ≤ 500)
      (h_time_lt : ∀ (i : ℕ), 1 ≤ i → i < logCount logs →
        leaveTime logs (i - 1) < leaveTime logs i)
      (h_id_ne : ∀ (i : ℕ), i < logCount logs - 1 → empId logs i ≠ empId logs (i + 1)) :
      ∀ r : Std.I64, Aegis.HardestWorker.hardest_worker n logs = Result.ok r →
        ∃ (i : ℕ), i < logCount logs ∧ empId logs i = r.val ∧ dur logs i = maxDur logs := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 500)
        (hm_lo : 1 ≤ logCount logs) (hm_hi : logCount logs ≤ 500)
        (h_shape : ∀ (i : ℕ), i < logCount logs → (logEntry logs i).length = 2)
        (h_id_lo : ∀ (i : ℕ), i < logCount logs → 0 ≤ empId logs i)
        (h_id_hi : ∀ (i : ℕ), i < logCount logs → empId logs i ≤ n.val - 1)
        (h_time_lo : ∀ (i : ℕ), i < logCount logs → 1 ≤ leaveTime logs i)
        (h_time_hi : ∀ (i : ℕ), i < logCount logs → leaveTime logs i ≤ 500)
        (h_time_lt : ∀ (i : ℕ), 1 ≤ i → i < logCount logs →
          leaveTime logs (i - 1) < leaveTime logs i)
        (h_id_ne : ∀ (i : ℕ), i < logCount logs - 1 → empId logs i ≠ empId logs (i + 1)), ∀ r : Std.I64, Aegis.HardestWorker.hardest_worker n logs = Result.ok r →
          ∃ (i : ℕ), i < logCount logs ∧ empId logs i = r.val ∧ dur logs i = maxDur logs) := by
    sorry

  /-- Define dur(i) = logs[i][1] - (if i = 0 then 0 else logs[i-1][1]) for 0 <= i < m, and let M = max { dur(i) | 0 <= i < m }. Whenever the function returns a result r, for every i with 0 <= i < m and dur(i) = M, we have r <= logs[i][0].
    Preconditions: Let m = len(logs). We assume 2 <= n <= 500, 1 <= m <= 500, for every i with 0 <= i < m the vector logs[i] has length 2, 0 <= logs[i][0] <= n-1, and 1 <= logs[i][1] <= 500, for every i with 1 <= i < m we have logs[i-1][1] < logs[i][1], and for every i with 0 <= i < m-1 we have logs[i][0] != logs[i+1][0]. -/
  theorem spec_5 (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 500)
      (hm_lo : 1 ≤ logCount logs) (hm_hi : logCount logs ≤ 500)
      (h_shape : ∀ (i : ℕ), i < logCount logs → (logEntry logs i).length = 2)
      (h_id_lo : ∀ (i : ℕ), i < logCount logs → 0 ≤ empId logs i)
      (h_id_hi : ∀ (i : ℕ), i < logCount logs → empId logs i ≤ n.val - 1)
      (h_time_lo : ∀ (i : ℕ), i < logCount logs → 1 ≤ leaveTime logs i)
      (h_time_hi : ∀ (i : ℕ), i < logCount logs → leaveTime logs i ≤ 500)
      (h_time_lt : ∀ (i : ℕ), 1 ≤ i → i < logCount logs →
        leaveTime logs (i - 1) < leaveTime logs i)
      (h_id_ne : ∀ (i : ℕ), i < logCount logs - 1 → empId logs i ≠ empId logs (i + 1)) :
      ∀ r : Std.I64, Aegis.HardestWorker.hardest_worker n logs = Result.ok r →
        ∀ (i : ℕ), i < logCount logs → dur logs i = maxDur logs → r.val ≤ empId logs i := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 500)
        (hm_lo : 1 ≤ logCount logs) (hm_hi : logCount logs ≤ 500)
        (h_shape : ∀ (i : ℕ), i < logCount logs → (logEntry logs i).length = 2)
        (h_id_lo : ∀ (i : ℕ), i < logCount logs → 0 ≤ empId logs i)
        (h_id_hi : ∀ (i : ℕ), i < logCount logs → empId logs i ≤ n.val - 1)
        (h_time_lo : ∀ (i : ℕ), i < logCount logs → 1 ≤ leaveTime logs i)
        (h_time_hi : ∀ (i : ℕ), i < logCount logs → leaveTime logs i ≤ 500)
        (h_time_lt : ∀ (i : ℕ), 1 ≤ i → i < logCount logs →
          leaveTime logs (i - 1) < leaveTime logs i)
        (h_id_ne : ∀ (i : ℕ), i < logCount logs - 1 → empId logs i ≠ empId logs (i + 1)), ∀ r : Std.I64, Aegis.HardestWorker.hardest_worker n logs = Result.ok r →
          ∀ (i : ℕ), i < logCount logs → dur logs i = maxDur logs → r.val ≤ empId logs i) := by
    sorry

  /-- For any two inputs with the same logs and with bounds n1 and n2 that both satisfy the preconditions together with this logs, if the function returns r1 on the first input and r2 on the second input, then r1 = r2.
    Preconditions: Let m = len(logs). We assume 2 <= n <= 500, 1 <= m <= 500, for every i with 0 <= i < m the vector logs[i] has length 2, 0 <= logs[i][0] <= n-1, and 1 <= logs[i][1] <= 500, for every i with 1 <= i < m we have logs[i-1][1] < logs[i][1], and for every i with 0 <= i < m-1 we have logs[i][0] != logs[i+1][0]. -/
  theorem spec_6 (n1 : Std.I64) (n2 : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64))
      (hn1_lo : 2 ≤ n1.val) (hn1_hi : n1.val ≤ 500)
      (hn2_lo : 2 ≤ n2.val) (hn2_hi : n2.val ≤ 500)
      (hm1_lo : 1 ≤ logCount logs) (hm1_hi : logCount logs ≤ 500)
      (hm2_lo : 1 ≤ logCount logs) (hm2_hi : logCount logs ≤ 500)
      (h_shape1 : ∀ (i : ℕ), i < logCount logs → (logEntry logs i).length = 2)
      (h_shape2 : ∀ (i : ℕ), i < logCount logs → (logEntry logs i).length = 2)
      (h_id_lo1 : ∀ (i : ℕ), i < logCount logs → 0 ≤ empId logs i)
      (h_id_lo2 : ∀ (i : ℕ), i < logCount logs → 0 ≤ empId logs i)
      (h_id_hi1 : ∀ (i : ℕ), i < logCount logs → empId logs i ≤ n1.val - 1)
      (h_id_hi2 : ∀ (i : ℕ), i < logCount logs → empId logs i ≤ n2.val - 1)
      (h_time_lo1 : ∀ (i : ℕ), i < logCount logs → 1 ≤ leaveTime logs i)
      (h_time_lo2 : ∀ (i : ℕ), i < logCount logs → 1 ≤ leaveTime logs i)
      (h_time_hi1 : ∀ (i : ℕ), i < logCount logs → leaveTime logs i ≤ 500)
      (h_time_hi2 : ∀ (i : ℕ), i < logCount logs → leaveTime logs i ≤ 500)
      (h_time_lt1 : ∀ (i : ℕ), 1 ≤ i → i < logCount logs →
        leaveTime logs (i - 1) < leaveTime logs i)
      (h_time_lt2 : ∀ (i : ℕ), 1 ≤ i → i < logCount logs →
        leaveTime logs (i - 1) < leaveTime logs i)
      (h_id_ne1 : ∀ (i : ℕ), i < logCount logs - 1 → empId logs i ≠ empId logs (i + 1))
      (h_id_ne2 : ∀ (i : ℕ), i < logCount logs - 1 → empId logs i ≠ empId logs (i + 1)) :
      ∀ r1 : Std.I64, Aegis.HardestWorker.hardest_worker n1 logs = Result.ok r1 →
        ∀ r2 : Std.I64, Aegis.HardestWorker.hardest_worker n2 logs = Result.ok r2 → r1 = r2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n1 : Std.I64) (n2 : Std.I64) (logs : Slice (alloc.vec.Vec Std.I64))
        (hn1_lo : 2 ≤ n1.val) (hn1_hi : n1.val ≤ 500)
        (hn2_lo : 2 ≤ n2.val) (hn2_hi : n2.val ≤ 500)
        (hm1_lo : 1 ≤ logCount logs) (hm1_hi : logCount logs ≤ 500)
        (hm2_lo : 1 ≤ logCount logs) (hm2_hi : logCount logs ≤ 500)
        (h_shape1 : ∀ (i : ℕ), i < logCount logs → (logEntry logs i).length = 2)
        (h_shape2 : ∀ (i : ℕ), i < logCount logs → (logEntry logs i).length = 2)
        (h_id_lo1 : ∀ (i : ℕ), i < logCount logs → 0 ≤ empId logs i)
        (h_id_lo2 : ∀ (i : ℕ), i < logCount logs → 0 ≤ empId logs i)
        (h_id_hi1 : ∀ (i : ℕ), i < logCount logs → empId logs i ≤ n1.val - 1)
        (h_id_hi2 : ∀ (i : ℕ), i < logCount logs → empId logs i ≤ n2.val - 1)
        (h_time_lo1 : ∀ (i : ℕ), i < logCount logs → 1 ≤ leaveTime logs i)
        (h_time_lo2 : ∀ (i : ℕ), i < logCount logs → 1 ≤ leaveTime logs i)
        (h_time_hi1 : ∀ (i : ℕ), i < logCount logs → leaveTime logs i ≤ 500)
        (h_time_hi2 : ∀ (i : ℕ), i < logCount logs → leaveTime logs i ≤ 500)
        (h_time_lt1 : ∀ (i : ℕ), 1 ≤ i → i < logCount logs →
          leaveTime logs (i - 1) < leaveTime logs i)
        (h_time_lt2 : ∀ (i : ℕ), 1 ≤ i → i < logCount logs →
          leaveTime logs (i - 1) < leaveTime logs i)
        (h_id_ne1 : ∀ (i : ℕ), i < logCount logs - 1 → empId logs i ≠ empId logs (i + 1))
        (h_id_ne2 : ∀ (i : ℕ), i < logCount logs - 1 → empId logs i ≠ empId logs (i + 1)), ∀ r1 : Std.I64, Aegis.HardestWorker.hardest_worker n1 logs = Result.ok r1 →
          ∀ r2 : Std.I64, Aegis.HardestWorker.hardest_worker n2 logs = Result.ok r2 → r1 = r2) := by
    sorry

  end AegisSpec.HardestWorker
