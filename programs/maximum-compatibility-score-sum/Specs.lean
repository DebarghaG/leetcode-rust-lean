import Aegis.MaxCompatibilitySum.Code.Funs

/-!
# Specifications of `Aegis.MaxCompatibilitySum.max_compatibility_sum`

LeetCode problem `maximum-compatibility-score-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxCompatibilitySum

def toRows (students : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  students.val.map (fun row => row.val.map (fun x => x.val))

def rowOf (students : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
  (toRows students).getD i []

def entry (A : List (List Int)) (i k : Nat) : Int :=
  (A.getD i []).getD k 0

def entryOf (students : Slice (alloc.vec.Vec Std.I64)) (i k : Nat) : Int :=
  entry (toRows students) i k

def comp (A B : List (List Int)) (n i j : Nat) : Int :=
  (((List.range n).filter (fun k => entry A i k = entry B j k)).length : Int)

def sumRange (m : Nat) (f : Nat → Int) : Int :=
  ((List.range m).map f).sum

def IsPermList (p : List Nat) (m : Nat) : Prop :=
  p.Perm (List.range m)

def permScore (A B : List (List Int)) (n m : Nat) (p : List Nat) : Int :=
  sumRange m (fun i => comp A B n i (p.getD i 0))

def IsMaxCompSum (A B : List (List Int)) (n m : Nat) (r : Int) : Prop :=
  (∃ p, IsPermList p m ∧ permScore A B n m p = r) ∧
    ∀ p, IsPermList p m → permScore A B n m p ≤ r

def countEntry (A : List (List Int)) (m k : Nat) (v : Int) : Int :=
  (((List.range m).filter (fun i => entry A i k = v)).length : Int)

def permuteRows (A : List (List Int)) (σ : List Nat) (m : Nat) : List (List Int) :=
  (List.range m).map (fun i => A.getD (σ.getD i 0) [])

def permuteCols (A : List (List Int)) (τ : List Nat) (m n : Nat) : List (List Int) :=
  (List.range m).map (fun i => (List.range n).map (fun k => entry A i (τ.getD k 0)))

def flipCol (A : List (List Int)) (c m n : Nat) : List (List Int) :=
  (List.range m).map
    (fun i => (List.range n).map (fun k => if k = c then 1 - entry A i c else entry A i k))

/-- For 0 <= i,j < m define comp(i,j) = the number of indices k with 0 <= k < n such that students[i][k] = mentors[j][k]. The function returns a result r, and r = max { sum_{i=0}^{m-1} comp(i, p(i)) | p is a permutation of {0,...,m-1} }.
  Preconditions: Let m = len(students). There is an integer n such that len(students) = len(mentors) = m, 1 <= m <= 8, 1 <= n <= 8, for every i with 0 <= i < m we have len(students[i]) = n and len(mentors[i]) = n, and for every i,j,k with 0 <= i,j < m and 0 <= k < n, students[i][k] is 0 or 1 and mentors[j][k] is 0 or 1. -/
theorem spec_1 (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1) :
    ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        IsMaxCompSum (toRows students) (toRows mentors) n m r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1), ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        IsMaxCompSum (toRows students) (toRows mentors) n m r.val) := by
  sorry

/-- The function returns a result r; it does not fail on any input satisfying the preconditions.
  Preconditions: Let m = len(students). There is an integer n such that len(students) = len(mentors) = m, 1 <= m <= 8, 1 <= n <= 8, for every i with 0 <= i < m we have len(students[i]) = n and len(mentors[i]) = n, and for every i,j,k with 0 <= i,j < m and 0 <= k < n, students[i][k] is 0 or 1 and mentors[j][k] is 0 or 1. -/
theorem spec_2 (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1) :
    ∃ r, Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1), ∃ r, Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r) := by
  sorry

/-- The function returns a result r and 0 <= r <= m * n.
  Preconditions: Let m = len(students). There is an integer n such that len(students) = len(mentors) = m, 1 <= m <= 8, 1 <= n <= 8, for every i with 0 <= i < m we have len(students[i]) = n and len(mentors[i]) = n, and for every i,j,k with 0 <= i,j < m and 0 <= k < n, students[i][k] is 0 or 1 and mentors[j][k] is 0 or 1. -/
theorem spec_3 (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1) :
    ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        0 ≤ r.val ∧ r.val ≤ (m : Int) * (n : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1), ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        0 ≤ r.val ∧ r.val ≤ (m : Int) * (n : Int)) := by
  sorry

/-- For 0 <= i,j < m define comp(i,j) = the number of indices k with 0 <= k < n such that students[i][k] = mentors[j][k]. The function returns a result r, and there exists a permutation p of {0,...,m-1} such that r = sum_{i=0}^{m-1} comp(i, p(i)).
  Preconditions: Let m = len(students). There is an integer n such that len(students) = len(mentors) = m, 1 <= m <= 8, 1 <= n <= 8, for every i with 0 <= i < m we have len(students[i]) = n and len(mentors[i]) = n, and for every i,j,k with 0 <= i,j < m and 0 <= k < n, students[i][k] is 0 or 1 and mentors[j][k] is 0 or 1. -/
theorem spec_4 (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1) :
    ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        ∃ p, IsPermList p m ∧ permScore (toRows students) (toRows mentors) n m p = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1), ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        ∃ p, IsPermList p m ∧ permScore (toRows students) (toRows mentors) n m p = r.val) := by
  sorry

/-- For 0 <= i,j < m define comp(i,j) = the number of indices k with 0 <= k < n such that students[i][k] = mentors[j][k]. The function returns a result r, and for every permutation p of {0,...,m-1} we have r >= sum_{i=0}^{m-1} comp(i, p(i)).
  Preconditions: Let m = len(students). There is an integer n such that len(students) = len(mentors) = m, 1 <= m <= 8, 1 <= n <= 8, for every i with 0 <= i < m we have len(students[i]) = n and len(mentors[i]) = n, and for every i,j,k with 0 <= i,j < m and 0 <= k < n, students[i][k] is 0 or 1 and mentors[j][k] is 0 or 1. -/
theorem spec_5 (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1) :
    ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        ∀ p, IsPermList p m →
          permScore (toRows students) (toRows mentors) n m p ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1), ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        ∀ p, IsPermList p m →
          permScore (toRows students) (toRows mentors) n m p ≤ r.val) := by
  sorry

/-- Let a0 be the number of i with 0 <= i < m and students[i][0] = 0, let a1 be the number of i with 0 <= i < m and students[i][0] = 1, let b0 be the number of j with 0 <= j < m and mentors[j][0] = 0, and let b1 be the number of j with 0 <= j < m and mentors[j][0] = 1. The function returns a result r, and r = min(a0, b0) + min(a1, b1).
  Preconditions: Let m = len(students). There is an integer n such that len(students) = len(mentors) = m, 1 <= m <= 8, n = 1, for every i with 0 <= i < m we have len(students[i]) = 1 and len(mentors[i]) = 1, and for every i,j,k with 0 <= i,j < m and 0 <= k < 1, students[i][k] is 0 or 1 and mentors[j][k] is 0 or 1. -/
theorem spec_6 (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_eq : n = 1)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1) :
    ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        r.val =
          min (countEntry (toRows students) m 0 0) (countEntry (toRows mentors) m 0 0) +
            min (countEntry (toRows students) m 0 1) (countEntry (toRows mentors) m 0 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_eq : n = 1)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1), ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        r.val =
          min (countEntry (toRows students) m 0 0) (countEntry (toRows mentors) m 0 0) +
            min (countEntry (toRows students) m 0 1) (countEntry (toRows mentors) m 0 1)) := by
  sorry

/-- Let r be the result returned on (students, mentors). For every permutation sigma of {0,...,m-1}, let students_sigma be the slice defined by students_sigma[i] = students[sigma(i)] for every 0 <= i < m. Then the function returns the same value r on (students_sigma, mentors).
  Preconditions: Let m = len(students). There is an integer n such that len(students) = len(mentors) = m, 1 <= m <= 8, 1 <= n <= 8, for every i with 0 <= i < m we have len(students[i]) = n and len(mentors[i]) = n, and for every i,j,k with 0 <= i,j < m and 0 <= k < n, students[i][k] is 0 or 1 and mentors[j][k] is 0 or 1. -/
theorem spec_7 (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1) :
    ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        ∀ (σ : List Nat), IsPermList σ m →
          ∀ students' : Slice (alloc.vec.Vec Std.I64),
            toRows students' = permuteRows (toRows students) σ m →
              Aegis.MaxCompatibilitySum.max_compatibility_sum students' mentors = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1), ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        ∀ (σ : List Nat), IsPermList σ m →
          ∀ students' : Slice (alloc.vec.Vec Std.I64),
            toRows students' = permuteRows (toRows students) σ m →
              Aegis.MaxCompatibilitySum.max_compatibility_sum students' mentors = ok r) := by
  sorry

/-- Let r be the result returned on (students, mentors). For every permutation tau of {0,...,m-1}, let mentors_tau be the slice defined by mentors_tau[j] = mentors[tau(j)] for every 0 <= j < m. Then the function returns the same value r on (students, mentors_tau).
  Preconditions: Let m = len(students). There is an integer n such that len(students) = len(mentors) = m, 1 <= m <= 8, 1 <= n <= 8, for every i with 0 <= i < m we have len(students[i]) = n and len(mentors[i]) = n, and for every i,j,k with 0 <= i,j < m and 0 <= k < n, students[i][k] is 0 or 1 and mentors[j][k] is 0 or 1. -/
theorem spec_8 (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1) :
    ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        ∀ (τ : List Nat), IsPermList τ m →
          ∀ mentors' : Slice (alloc.vec.Vec Std.I64),
            toRows mentors' = permuteRows (toRows mentors) τ m →
              Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors' = ok r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1), ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        ∀ (τ : List Nat), IsPermList τ m →
          ∀ mentors' : Slice (alloc.vec.Vec Std.I64),
            toRows mentors' = permuteRows (toRows mentors) τ m →
              Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors' = ok r) := by
  sorry

/-- Let r be the result returned on (students, mentors). For every permutation tau of {0,...,n-1}, define students_tau[i][k] = students[i][tau(k)] and mentors_tau[j][k] = mentors[j][tau(k)] for all 0 <= i,j < m and 0 <= k < n. Then the function returns the same value r on (students_tau, mentors_tau).
  Preconditions: Let m = len(students). There is an integer n such that len(students) = len(mentors) = m, 1 <= m <= 8, 1 <= n <= 8, for every i with 0 <= i < m we have len(students[i]) = n and len(mentors[i]) = n, and for every i,j,k with 0 <= i,j < m and 0 <= k < n, students[i][k] is 0 or 1 and mentors[j][k] is 0 or 1. -/
theorem spec_9 (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1) :
    ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        ∀ (τ : List Nat), IsPermList τ n →
          ∀ students' mentors' : Slice (alloc.vec.Vec Std.I64),
            toRows students' = permuteCols (toRows students) τ m n →
              toRows mentors' = permuteCols (toRows mentors) τ m n →
                Aegis.MaxCompatibilitySum.max_compatibility_sum students' mentors' = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1), ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        ∀ (τ : List Nat), IsPermList τ n →
          ∀ students' mentors' : Slice (alloc.vec.Vec Std.I64),
            toRows students' = permuteCols (toRows students) τ m n →
              toRows mentors' = permuteCols (toRows mentors) τ m n →
                Aegis.MaxCompatibilitySum.max_compatibility_sum students' mentors' = ok r) := by
  sorry

/-- Let r be the result returned on (students, mentors). For every c with 0 <= c < n, define students_c[i][k] = (1 - students[i][c]) if k = c else students[i][k], and mentors_c[j][k] = (1 - mentors[j][c]) if k = c else mentors[j][k], for all 0 <= i,j < m and 0 <= k < n. Then the function returns the same value r on (students_c, mentors_c).
  Preconditions: Let m = len(students). There is an integer n such that len(students) = len(mentors) = m, 1 <= m <= 8, 1 <= n <= 8, for every i with 0 <= i < m we have len(students[i]) = n and len(mentors[i]) = n, and for every i,j,k with 0 <= i,j < m and 0 <= k < n, students[i][k] is 0 or 1 and mentors[j][k] is 0 or 1. -/
theorem spec_10 (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1) :
    ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        ∀ c, c < n →
          ∀ students' mentors' : Slice (alloc.vec.Vec Std.I64),
            toRows students' = flipCol (toRows students) c m n →
              toRows mentors' = flipCol (toRows mentors) c m n →
                Aegis.MaxCompatibilitySum.max_compatibility_sum students' mentors' = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1), ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        ∀ c, c < n →
          ∀ students' mentors' : Slice (alloc.vec.Vec Std.I64),
            toRows students' = flipCol (toRows students) c m n →
              toRows mentors' = flipCol (toRows mentors) c m n →
                Aegis.MaxCompatibilitySum.max_compatibility_sum students' mentors' = ok r) := by
  sorry

/-- For 0 <= i,j < m define comp(i,j) = the number of indices k with 0 <= k < n such that students[i][k] = mentors[j][k]. The function returns a result r, and r = sum_{j=0}^{m-1} comp(0, j).
  Preconditions: Let m = len(students). There is an integer n such that len(students) = len(mentors) = m, 1 <= m <= 8, 1 <= n <= 8, for every i with 0 <= i < m we have len(students[i]) = n and len(mentors[i]) = n, for every i,j,k with 0 <= i,j < m and 0 <= k < n, students[i][k] is 0 or 1 and mentors[j][k] is 0 or 1, and for every i,k with 0 <= i < m and 0 <= k < n, students[i][k] = students[0][k]. -/
theorem spec_11 (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1)
    (hstud_const : ∀ i k, i < m → k < n → entryOf students i k = entryOf students 0 k) :
    ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        r.val = sumRange m (fun j => comp (toRows students) (toRows mentors) n 0 j) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1)
    (hstud_const : ∀ i k, i < m → k < n → entryOf students i k = entryOf students 0 k), ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        r.val = sumRange m (fun j => comp (toRows students) (toRows mentors) n 0 j)) := by
  sorry

/-- For 0 <= i,j < m define comp(i,j) = the number of indices k with 0 <= k < n such that students[i][k] = mentors[j][k]. Let r be the result returned on (students, mentors) and let r' be the result returned on (mentors, students). Then r = r'.
  Preconditions: Let m = len(students). There is an integer n such that len(students) = len(mentors) = m, 1 <= m <= 8, 1 <= n <= 8, for every i with 0 <= i < m we have len(students[i]) = n and len(mentors[i]) = n, and for every i,j,k with 0 <= i,j < m and 0 <= k < n, students[i][k] is 0 or 1 and mentors[j][k] is 0 or 1. -/
theorem spec_12 (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1) :
    ∃ r r',
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        Aegis.MaxCompatibilitySum.max_compatibility_sum mentors students = ok r' ∧ r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1), ∃ r r',
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        Aegis.MaxCompatibilitySum.max_compatibility_sum mentors students = ok r' ∧ r = r') := by
  sorry

/-- For 0 <= i,j < m define comp(i,j) = the number of indices k with 0 <= k < n such that students[i][k] = mentors[j][k]. The function returns a result r, and r = sum_{i=0}^{m-1} comp(i, 0).
  Preconditions: Let m = len(students). There is an integer n such that len(students) = len(mentors) = m, 1 <= m <= 8, 1 <= n <= 8, for every i with 0 <= i < m we have len(students[i]) = n and len(mentors[i]) = n, for every i,j,k with 0 <= i,j < m and 0 <= k < n, students[i][k] is 0 or 1 and mentors[j][k] is 0 or 1, and for every j with 0 <= j < m and every k with 0 <= k < n, mentors[j][k] = mentors[0][k]. -/
theorem spec_13 (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1)
    (hment_const : ∀ j k, j < m → k < n → entryOf mentors j k = entryOf mentors 0 k) :
    ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        r.val = sumRange m (fun i => comp (toRows students) (toRows mentors) n i 0) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1)
    (hment_const : ∀ j k, j < m → k < n → entryOf mentors j k = entryOf mentors 0 k), ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        r.val = sumRange m (fun i => comp (toRows students) (toRows mentors) n i 0)) := by
  sorry

/-- The function returns a result r, and r = m * n.
  Preconditions: Let m = len(students). There is an integer n such that len(students) = len(mentors) = m, 1 <= m <= 8, 1 <= n <= 8, for every i with 0 <= i < m we have len(students[i]) = n and len(mentors[i]) = n, for every i,j,k with 0 <= i,j < m and 0 <= k < n, students[i][k] is 0 or 1 and mentors[j][k] is 0 or 1, and for every i with 0 <= i < m and every k with 0 <= k < n, students[i][k] = mentors[i][k]. -/
theorem spec_14 (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1)
    (hagree : ∀ i k, i < m → k < n → entryOf students i k = entryOf mentors i k) :
    ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        r.val = (m : Int) * (n : Int) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (students mentors : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hstud_len : (Slice.len students).val = m)
    (hment_len : (Slice.len mentors).val = m)
    (hm_pos : 1 ≤ m) (hm_le : m ≤ 8) (hn_pos : 1 ≤ n) (hn_le : n ≤ 8)
    (hstud_rows : ∀ i, i < m → (rowOf students i).length = n)
    (hment_rows : ∀ i, i < m → (rowOf mentors i).length = n)
    (hstud_bits : ∀ i k, i < m → k < n → entryOf students i k = 0 ∨ entryOf students i k = 1)
    (hment_bits : ∀ i k, i < m → k < n → entryOf mentors i k = 0 ∨ entryOf mentors i k = 1)
    (hagree : ∀ i k, i < m → k < n → entryOf students i k = entryOf mentors i k), ∃ r,
      Aegis.MaxCompatibilitySum.max_compatibility_sum students mentors = ok r ∧
        r.val = (m : Int) * (n : Int)) := by
  sorry

end AegisSpec.MaxCompatibilitySum
