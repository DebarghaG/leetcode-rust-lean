import Aegis.BusyStudent.Code.Funs

/-!
# Specifications of `Aegis.BusyStudent.busy_student`

LeetCode problem `number-of-students-doing-homework-at-a-given-time`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.BusyStudent

  abbrev containsQuery (s e q : ℤ) : Prop := s ≤ q ∧ q ≤ e

  def countContaining (startTime endTime : List ℤ) (queryTime : ℤ) : ℕ :=
    (startTime.zip endTime).countP fun p => decide (containsQuery p.1 p.2 queryTime)

  /-- Whenever busy_student(startTime, endTime, queryTime) returns a result r, r is the number of indices i with 0 <= i < n and startTime[i] <= queryTime and queryTime <= endTime[i]; equivalently, r is the number of students whose closed interval [startTime[i], endTime[i]] contains queryTime.
    Preconditions: Let n = len(startTime). Assume len(endTime) = n, 1 <= n <= 100, 1 <= queryTime <= 1000, and for every i with 0 <= i < n, 1 <= startTime[i] <= endTime[i] <= 1000. -/
  theorem spec_1 (startTime endTime : Slice Std.I64) (queryTime : Std.I64)
      (h_len : endTime.val.length = startTime.val.length)
      (h_n_pos : 1 ≤ startTime.val.length)
      (h_n_bound : startTime.val.length ≤ 100)
      (h_query_lower : 1 ≤ queryTime.val)
      (h_query_upper : queryTime.val ≤ 1000)
      (h_bounds : ∀ (i : ℕ) (hi : i < startTime.val.length),
        1 ≤ (startTime.val[i]'hi).val ∧
          (startTime.val[i]'hi).val ≤ (endTime.val[i]'(by omega)).val ∧
          (endTime.val[i]'(by omega)).val ≤ 1000) :
      ∀ r : Std.I64,
        Aegis.BusyStudent.busy_student startTime endTime queryTime = Result.ok r →
          r.val = (countContaining (startTime.val.map (·.val)) (endTime.val.map (·.val))
            queryTime.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (startTime endTime : Slice Std.I64) (queryTime : Std.I64)
        (h_len : endTime.val.length = startTime.val.length)
        (h_n_pos : 1 ≤ startTime.val.length)
        (h_n_bound : startTime.val.length ≤ 100)
        (h_query_lower : 1 ≤ queryTime.val)
        (h_query_upper : queryTime.val ≤ 1000)
        (h_bounds : ∀ (i : ℕ) (hi : i < startTime.val.length),
          1 ≤ (startTime.val[i]'hi).val ∧
            (startTime.val[i]'hi).val ≤ (endTime.val[i]'(by omega)).val ∧
            (endTime.val[i]'(by omega)).val ≤ 1000), ∀ r : Std.I64,
          Aegis.BusyStudent.busy_student startTime endTime queryTime = Result.ok r →
            r.val = (countContaining (startTime.val.map (·.val)) (endTime.val.map (·.val))
              queryTime.val : ℤ)) := by
    sorry

  /-- busy_student(startTime, endTime, queryTime) returns a result r; it does not fail (no out-of-bounds access or arithmetic overflow) for every input satisfying the preconditions.
    Preconditions: Let n = len(startTime). Assume len(endTime) = n, 1 <= n <= 100, 1 <= queryTime <= 1000, and for every i with 0 <= i < n, 1 <= startTime[i] <= endTime[i] <= 1000. -/
  theorem spec_2 (startTime endTime : Slice Std.I64) (queryTime : Std.I64)
      (h_len : endTime.val.length = startTime.val.length)
      (h_n_pos : 1 ≤ startTime.val.length)
      (h_n_bound : startTime.val.length ≤ 100)
      (h_query_lower : 1 ≤ queryTime.val)
      (h_query_upper : queryTime.val ≤ 1000)
      (h_bounds : ∀ (i : ℕ) (hi : i < startTime.val.length),
        1 ≤ (startTime.val[i]'hi).val ∧
          (startTime.val[i]'hi).val ≤ (endTime.val[i]'(by omega)).val ∧
          (endTime.val[i]'(by omega)).val ≤ 1000) :
      ∃ r : Std.I64,
        Aegis.BusyStudent.busy_student startTime endTime queryTime = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (startTime endTime : Slice Std.I64) (queryTime : Std.I64)
        (h_len : endTime.val.length = startTime.val.length)
        (h_n_pos : 1 ≤ startTime.val.length)
        (h_n_bound : startTime.val.length ≤ 100)
        (h_query_lower : 1 ≤ queryTime.val)
        (h_query_upper : queryTime.val ≤ 1000)
        (h_bounds : ∀ (i : ℕ) (hi : i < startTime.val.length),
          1 ≤ (startTime.val[i]'hi).val ∧
            (startTime.val[i]'hi).val ≤ (endTime.val[i]'(by omega)).val ∧
            (endTime.val[i]'(by omega)).val ≤ 1000), ∃ r : Std.I64,
          Aegis.BusyStudent.busy_student startTime endTime queryTime = Result.ok r) := by
    sorry

  end AegisSpec.BusyStudent
