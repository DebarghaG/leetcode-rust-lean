import Aegis.MaxStudentsOnBench.Code.Funs

/-!
# Specifications of `Aegis.MaxStudentsOnBench.max_students_on_bench`

LeetCode problem `maximum-students-on-a-single-bench`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxStudentsOnBench

def rowVals (row : alloc.vec.Vec Std.I64) : List ℤ := row.val.map (fun x => x.val)

def RowOK (row : alloc.vec.Vec Std.I64) : Prop :=
  ∃ s b : ℤ, rowVals row = [s, b] ∧ 1 ≤ s ∧ s ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100

def idOf (row : alloc.vec.Vec Std.I64) : Option ℤ := (rowVals row)[0]?

def benchOf (row : alloc.vec.Vec Std.I64) : Option ℤ := (rowVals row)[1]?

def benchCount (students : Slice (alloc.vec.Vec Std.I64)) (b : ℤ) : ℕ :=
  ((students.val.filterMap fun row =>
      match rowVals row with
      | [x, y] => if y = b then some x else none
      | _ => none).dedup).length

def maxBenchCount (students : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
  (Finset.Icc 1 100).sup fun b : ℕ => benchCount students (b : ℤ)

def sameBench (students : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∃ b : ℤ, ∀ i : Fin students.val.length, benchOf (students.val.get i) = some b

def distinctIds (students : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∀ i j : Fin students.val.length, i ≠ j →
    idOf (students.val.get i) ≠ idOf (students.val.get j)

/-- The function returns a result r and does not fail. For each integer b with 1 <= b <= 100, let D(b) be the number of distinct integers x such that some row i with 0 <= i < len(students) has students[i][0] = x and students[i][1] = b. Then r = max over 1 <= b <= 100 of D(b). Equivalently, r is the maximum number of distinct student ids sitting on any single bench, with r = 0 when students is empty.
  Preconditions: students has length at most 100; for every i with 0 <= i < len(students), students[i] has length exactly 2, with 1 <= students[i][0] <= 100 and 1 <= students[i][1] <= 100. -/
theorem spec_1 (students : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i)) :
    ∃ r : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        r.val = (maxBenchCount students : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (students : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i)), ∃ r : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        r.val = (maxBenchCount students : ℤ)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or access a row out of bounds.
  Preconditions: students has length at most 100; for every i with 0 <= i < len(students), students[i] has length exactly 2, with 1 <= students[i][0] <= 100 and 1 <= students[i][1] <= 100. -/
theorem spec_2 (students : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i)) :
    ∃ r : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (students : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i)), ∃ r : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r) := by
  sorry

/-- The function returns a result r and 0 <= r <= len(students).
  Preconditions: students has length at most 100; for every i with 0 <= i < len(students), students[i] has length exactly 2, with 1 <= students[i][0] <= 100 and 1 <= students[i][1] <= 100. -/
theorem spec_3 (students : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i)) :
    ∃ r : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        0 ≤ r.val ∧ r.val ≤ (students.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (students : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i)), ∃ r : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        0 ≤ r.val ∧ r.val ≤ (students.val.length : ℤ)) := by
  sorry

/-- The function returns a result r and 1 <= r.
  Preconditions: students has length at most 100; for every i with 0 <= i < len(students), students[i] has length exactly 2, with 1 <= students[i][0] <= 100 and 1 <= students[i][1] <= 100; and len(students) > 0. -/
theorem spec_4 (students : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i))
    (h_pos : 0 < students.val.length) :
    ∃ r : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (students : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i))
    (h_pos : 0 < students.val.length), ∃ r : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧ 1 ≤ r.val) := by
  sorry

/-- The function returns a result r, and r = 0 if and only if len(students) = 0.
  Preconditions: students has length at most 100; for every i with 0 <= i < len(students), students[i] has length exactly 2, with 1 <= students[i][0] <= 100 and 1 <= students[i][1] <= 100. -/
theorem spec_5 (students : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i)) :
    ∃ r : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        (r.val = 0 ↔ students.val.length = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (students : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i)), ∃ r : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        (r.val = 0 ↔ students.val.length = 0)) := by
  sorry

/-- The function returns a result r and, for every integer b with 1 <= b <= 100, let D(b) be the number of distinct integers x such that some row i has students[i][0] = x and students[i][1] = b; then D(b) <= r.
  Preconditions: students has length at most 100; for every i with 0 <= i < len(students), students[i] has length exactly 2, with 1 <= students[i][0] <= 100 and 1 <= students[i][1] <= 100. -/
theorem spec_6 (students : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i)) :
    ∃ r : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        ∀ b : ℤ, 1 ≤ b → b ≤ 100 → (benchCount students b : ℤ) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (students : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i)), ∃ r : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        ∀ b : ℤ, 1 ≤ b → b ≤ 100 → (benchCount students b : ℤ) ≤ r.val) := by
  sorry

/-- The function returns a result r and there exists an integer b with 1 <= b <= 100 such that some input row has bench_id b and D(b) = r, where D(b) is the number of distinct integers x such that some row i has students[i][0] = x and students[i][1] = b.
  Preconditions: students has length at most 100; for every i with 0 <= i < len(students), students[i] has length exactly 2, with 1 <= students[i][0] <= 100 and 1 <= students[i][1] <= 100; and len(students) > 0. -/
theorem spec_7 (students : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i))
    (h_pos : 0 < students.val.length) :
    ∃ r : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        ∃ b : ℤ, 1 ≤ b ∧ b ≤ 100 ∧
          (∃ i : Fin students.val.length, ∃ s : ℤ, rowVals (students.val.get i) = [s, b]) ∧
          (benchCount students b : ℤ) = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (students : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i))
    (h_pos : 0 < students.val.length), ∃ r : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        ∃ b : ℤ, 1 ≤ b ∧ b ≤ 100 ∧
          (∃ i : Fin students.val.length, ∃ s : ℤ, rowVals (students.val.get i) = [s, b]) ∧
          (benchCount students b : ℤ) = r.val) := by
  sorry

/-- The function returns r on students and r' on students', and r = r'.
  Preconditions: students has length at most 100; for every i with 0 <= i < len(students), students[i] has length exactly 2, with 1 <= students[i][0] <= 100 and 1 <= students[i][1] <= 100. students' is any slice or vector whose rows are a permutation of the rows of students. -/
theorem spec_8 (students students' : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i))
    (h_perm : students'.val.Perm students.val) :
    ∃ r r' : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        Aegis.MaxStudentsOnBench.max_students_on_bench students' = ok r' ∧
          r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (students students' : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i))
    (h_perm : students'.val.Perm students.val), ∃ r r' : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        Aegis.MaxStudentsOnBench.max_students_on_bench students' = ok r' ∧
          r.val = r'.val) := by
  sorry

/-- The function returns r on students and r' on students', and r' >= r.
  Preconditions: students has length at most 100; for every i with 0 <= i < len(students), students[i] has length exactly 2, with 1 <= students[i][0] <= 100 and 1 <= students[i][1] <= 100; len(students) < 100; and (s,b) is any pair with 1 <= s <= 100 and 1 <= b <= 100. Let students' be students with the row [s,b] appended. -/
theorem spec_9 (students students' : Slice (alloc.vec.Vec Std.I64)) (s b : ℤ)
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i))
    (h_lt : students.val.length < 100)
    (h_s1 : 1 ≤ s) (h_s2 : s ≤ 100) (h_b1 : 1 ≤ b) (h_b2 : b ≤ 100)
    (h_append : students'.val.map rowVals = students.val.map rowVals ++ [[s, b]]) :
    ∃ r r' : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        Aegis.MaxStudentsOnBench.max_students_on_bench students' = ok r' ∧
          r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (students students' : Slice (alloc.vec.Vec Std.I64)) (s b : ℤ)
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i))
    (h_lt : students.val.length < 100)
    (h_s1 : 1 ≤ s) (h_s2 : s ≤ 100) (h_b1 : 1 ≤ b) (h_b2 : b ≤ 100)
    (h_append : students'.val.map rowVals = students.val.map rowVals ++ [[s, b]]), ∃ r r' : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        Aegis.MaxStudentsOnBench.max_students_on_bench students' = ok r' ∧
          r.val ≤ r'.val) := by
  sorry

/-- The function returns a result r, and r = 1 if and only if len(students) > 0 and for every integer b with 1 <= b <= 100, D(b) <= 1, where D(b) is the number of distinct integers x such that some row i has students[i][0] = x and students[i][1] = b.
  Preconditions: students has length at most 100; for every i with 0 <= i < len(students), students[i] has length exactly 2, with 1 <= students[i][0] <= 100 and 1 <= students[i][1] <= 100. -/
theorem spec_10 (students : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i)) :
    ∃ r : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        (r.val = 1 ↔
          0 < students.val.length ∧ ∀ b : ℤ, 1 ≤ b → b ≤ 100 → benchCount students b ≤ 1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (students : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i)), ∃ r : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        (r.val = 1 ↔
          0 < students.val.length ∧ ∀ b : ℤ, 1 ≤ b → b ≤ 100 → benchCount students b ≤ 1)) := by
  sorry

/-- The function returns a result r, and r = len(students) if and only if all rows have the same bench_id and no two distinct indices i and j with 0 <= i < len(students), 0 <= j < len(students), and i != j satisfy students[i][0] = students[j][0].
  Preconditions: students has length at most 100; for every i with 0 <= i < len(students), students[i] has length exactly 2, with 1 <= students[i][0] <= 100 and 1 <= students[i][1] <= 100. -/
theorem spec_11 (students : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i)) :
    ∃ r : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        (r.val = (students.val.length : ℤ) ↔ sameBench students ∧ distinctIds students) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (students : Slice (alloc.vec.Vec Std.I64))
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i)), ∃ r : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        (r.val = (students.val.length : ℤ) ↔ sameBench students ∧ distinctIds students)) := by
  sorry

/-- The function returns r on students and r' on students', and r' = max(r, D(b) + 1).
  Preconditions: students has length at most 100; for every i with 0 <= i < len(students), students[i] has length exactly 2, with 1 <= students[i][0] <= 100 and 1 <= students[i][1] <= 100; len(students) < 100; and (s,b) is a pair with 1 <= s <= 100 and 1 <= b <= 100 such that no row i satisfies students[i][0] = s and students[i][1] = b. Let students' be students with the row [s,b] appended, and let D(b) be the number of distinct integers x such that some row i has students[i][0] = x and students[i][1] = b. -/
theorem spec_12 (students students' : Slice (alloc.vec.Vec Std.I64)) (s b : ℤ)
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i))
    (h_lt : students.val.length < 100)
    (h_s1 : 1 ≤ s) (h_s2 : s ≤ 100) (h_b1 : 1 ≤ b) (h_b2 : b ≤ 100)
    (h_fresh : ∀ i : Fin students.val.length, rowVals (students.val.get i) ≠ [s, b])
    (h_append : students'.val.map rowVals = students.val.map rowVals ++ [[s, b]]) :
    ∃ r r' : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        Aegis.MaxStudentsOnBench.max_students_on_bench students' = ok r' ∧
          r'.val = max r.val ((benchCount students b : ℤ) + 1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (students students' : Slice (alloc.vec.Vec Std.I64)) (s b : ℤ)
    (h_len : students.val.length ≤ 100)
    (h_rows : ∀ i : Fin students.val.length, RowOK (students.val.get i))
    (h_lt : students.val.length < 100)
    (h_s1 : 1 ≤ s) (h_s2 : s ≤ 100) (h_b1 : 1 ≤ b) (h_b2 : b ≤ 100)
    (h_fresh : ∀ i : Fin students.val.length, rowVals (students.val.get i) ≠ [s, b])
    (h_append : students'.val.map rowVals = students.val.map rowVals ++ [[s, b]]), ∃ r r' : Std.I64,
      Aegis.MaxStudentsOnBench.max_students_on_bench students = ok r ∧
        Aegis.MaxStudentsOnBench.max_students_on_bench students' = ok r' ∧
          r'.val = max r.val ((benchCount students b : ℤ) + 1)) := by
  sorry

end AegisSpec.MaxStudentsOnBench
