import Aegis.ScheduleCourse.Code.Funs

/-!
# Specifications of `Aegis.ScheduleCourse.schedule_course`

LeetCode problem `course-schedule-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ScheduleCourse

abbrev CourseSlice := Slice (alloc.vec.Vec Std.I64)

def courseAt (c : CourseSlice) (i : ℕ) : List Std.I64 :=
  match c.val[i]? with
  | some v => v.val
  | none => []

def innerLen (c : CourseSlice) (i : ℕ) : ℕ := (courseAt c i).length

def dur (c : CourseSlice) (i : ℕ) : ℤ :=
  match courseAt c i with
  | [] => 0
  | d :: _ => d.val

def lastDay (c : CourseSlice) (i : ℕ) : ℤ :=
  match courseAt c i with
  | [] => 0
  | _ :: [] => 0
  | _ :: l :: _ => l.val

def Pre (c : CourseSlice) : Prop :=
  1 ≤ c.val.length ∧ c.val.length ≤ 10000 ∧
    (∀ i, i < c.val.length → innerLen c i = 2) ∧
    (∀ i, i < c.val.length →
      1 ≤ dur c i ∧ dur c i ≤ 10000 ∧ 1 ≤ lastDay c i ∧ lastDay c i ≤ 10000)

def sumDur (c : CourseSlice) (idx : List ℕ) : ℤ := (idx.map (dur c)).sum

def AllPrefixOk (c : CourseSlice) (idx : List ℕ) : Prop :=
  ∀ p, p < idx.length → sumDur c (idx.take (p + 1)) ≤ lastDay c (idx.getD p 0)

def Feasible (c : CourseSlice) (idx : List ℕ) : Prop :=
  idx.Nodup ∧ (∀ i ∈ idx, i < c.val.length) ∧ AllPrefixOk c idx

def MaxLenOf (P : List ℕ → Prop) (k : ℕ) : Prop :=
  (∃ idx, P idx ∧ idx.length = k) ∧ ∀ idx, P idx → idx.length ≤ k

def IsPermOf (n : ℕ) (σ : List ℕ) : Prop :=
  σ.Nodup ∧ σ.length = n ∧ ∀ i ∈ σ, i < n

def SortedByLastDay (c : CourseSlice) (σ : List ℕ) : Prop :=
  ∀ p q, p ≤ q → q < σ.length → lastDay c (σ.getD p 0) ≤ lastDay c (σ.getD q 0)

def countShort (c : CourseSlice) : ℕ :=
  ((Finset.range c.val.length).filter (fun i => dur c i ≤ lastDay c i)).card

/-- Let n = len(courses), and for each valid i let d_i = courses[i][0] and l_i = courses[i][1]. Whenever schedule_course(courses) returns a result r, r is the maximum length k of a sequence of distinct indices i_1, ..., i_k from {0, ..., n-1} such that for every j with 1 <= j <= k, sum_{m=1}^j d_{i_m} <= l_{i_j}. The empty sequence with k = 0 is allowed.
  Preconditions: len(courses) is between 1 and 10000 inclusive; for every i with 0 <= i < len(courses), len(courses[i]) = 2; and for every such i, 1 <= courses[i][0] <= 10000 and 1 <= courses[i][1] <= 10000. -/
theorem spec_1 (courses : CourseSlice) (h : Pre courses) :
    ∀ r, Aegis.ScheduleCourse.schedule_course courses = ok r →
      ∃ k : ℕ, MaxLenOf (Feasible courses) k ∧ r.val = (k : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (courses : CourseSlice) (h : Pre courses), ∀ r, Aegis.ScheduleCourse.schedule_course courses = ok r →
      ∃ k : ℕ, MaxLenOf (Feasible courses) k ∧ r.val = (k : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, schedule_course(courses) returns a result r and does not fail; in particular, there is no arithmetic overflow and no out-of-bounds access to a course pair.
  Preconditions: len(courses) is between 1 and 10000 inclusive; for every i with 0 <= i < len(courses), len(courses[i]) = 2; and for every such i, 1 <= courses[i][0] <= 10000 and 1 <= courses[i][1] <= 10000. -/
theorem spec_2 (courses : CourseSlice) (h : Pre courses) :
    ∃ r, Aegis.ScheduleCourse.schedule_course courses = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (courses : CourseSlice) (h : Pre courses), ∃ r, Aegis.ScheduleCourse.schedule_course courses = ok r) := by
  sorry

/-- Whenever schedule_course(courses) returns a result r, 0 <= r <= len(courses).
  Preconditions: len(courses) is between 1 and 10000 inclusive; for every i with 0 <= i < len(courses), len(courses[i]) = 2; and for every such i, 1 <= courses[i][0] <= 10000 and 1 <= courses[i][1] <= 10000. -/
theorem spec_3 (courses : CourseSlice) (h : Pre courses) :
    ∀ r, Aegis.ScheduleCourse.schedule_course courses = ok r →
      0 ≤ r.val ∧ r.val ≤ (courses.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (courses : CourseSlice) (h : Pre courses), ∀ r, Aegis.ScheduleCourse.schedule_course courses = ok r →
      0 ≤ r.val ∧ r.val ≤ (courses.val.length : ℤ)) := by
  sorry

/-- Whenever schedule_course(courses) returns a result r, r is at most the number of indices i with 0 <= i < len(courses) and courses[i][0] <= courses[i][1].
  Preconditions: len(courses) is between 1 and 10000 inclusive; for every i with 0 <= i < len(courses), len(courses[i]) = 2; and for every such i, 1 <= courses[i][0] <= 10000 and 1 <= courses[i][1] <= 10000. -/
theorem spec_4 (courses : CourseSlice) (h : Pre courses) :
    ∀ r, Aegis.ScheduleCourse.schedule_course courses = ok r →
      r.val ≤ (countShort courses : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (courses : CourseSlice) (h : Pre courses), ∀ r, Aegis.ScheduleCourse.schedule_course courses = ok r →
      r.val ≤ (countShort courses : ℤ)) := by
  sorry

/-- Let n = len(courses), and for each valid i let d_i = courses[i][0] and l_i = courses[i][1]. Whenever schedule_course(courses) returns a result r, there exist r distinct indices i_1, ..., i_r from {0, ..., n-1} (the empty sequence if r = 0) such that for every j with 1 <= j <= r, sum_{m=1}^j d_{i_m} <= l_{i_j}.
  Preconditions: len(courses) is between 1 and 10000 inclusive; for every i with 0 <= i < len(courses), len(courses[i]) = 2; and for every such i, 1 <= courses[i][0] <= 10000 and 1 <= courses[i][1] <= 10000. -/
theorem spec_5 (courses : CourseSlice) (h : Pre courses) :
    ∀ r, Aegis.ScheduleCourse.schedule_course courses = ok r →
      ∃ k : ℕ, r.val = (k : ℤ) ∧ ∃ idx : List ℕ, Feasible courses idx ∧ idx.length = k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (courses : CourseSlice) (h : Pre courses), ∀ r, Aegis.ScheduleCourse.schedule_course courses = ok r →
      ∃ k : ℕ, r.val = (k : ℤ) ∧ ∃ idx : List ℕ, Feasible courses idx ∧ idx.length = k) := by
  sorry

/-- Let n = len(courses), and for each valid i let d_i = courses[i][0] and l_i = courses[i][1]. Whenever schedule_course(courses) returns a result r, for every k and every sequence of k distinct indices i_1, ..., i_k from {0, ..., n-1}, if for every j with 1 <= j <= k we have sum_{m=1}^j d_{i_m} <= l_{i_j}, then k <= r.
  Preconditions: len(courses) is between 1 and 10000 inclusive; for every i with 0 <= i < len(courses), len(courses[i]) = 2; and for every such i, 1 <= courses[i][0] <= 10000 and 1 <= courses[i][1] <= 10000. -/
theorem spec_6 (courses : CourseSlice) (h : Pre courses) :
    ∀ r, Aegis.ScheduleCourse.schedule_course courses = ok r →
      ∀ idx : List ℕ, Feasible courses idx → (idx.length : ℤ) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (courses : CourseSlice) (h : Pre courses), ∀ r, Aegis.ScheduleCourse.schedule_course courses = ok r →
      ∀ idx : List ℕ, Feasible courses idx → (idx.length : ℤ) ≤ r.val) := by
  sorry

/-- Let n = len(courses), and for each valid i let d_i = courses[i][0] and l_i = courses[i][1]. Whenever schedule_course(courses) returns a result r, r = 0 if and only if for every i with 0 <= i < n, d_i > l_i.
  Preconditions: len(courses) is between 1 and 10000 inclusive; for every i with 0 <= i < len(courses), len(courses[i]) = 2; and for every such i, 1 <= courses[i][0] <= 10000 and 1 <= courses[i][1] <= 10000. -/
theorem spec_7 (courses : CourseSlice) (h : Pre courses) :
    ∀ r, Aegis.ScheduleCourse.schedule_course courses = ok r →
      (r.val = 0 ↔ ∀ i, i < courses.val.length → lastDay courses i < dur courses i) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (courses : CourseSlice) (h : Pre courses), ∀ r, Aegis.ScheduleCourse.schedule_course courses = ok r →
      (r.val = 0 ↔ ∀ i, i < courses.val.length → lastDay courses i < dur courses i)) := by
  sorry

/-- Let n = len(courses), and for each valid i let d_i = courses[i][0] and l_i = courses[i][1]. Whenever schedule_course(courses) returns a result r, r = n if and only if, for every permutation sigma of {0, ..., n-1} with l_{sigma(1)} <= ... <= l_{sigma(n)} (using 1-based positions in the sorted order), the inequality sum_{j=1}^k d_{sigma(j)} <= l_{sigma(k)} holds for every k with 1 <= k <= n.
  Preconditions: len(courses) is between 1 and 10000 inclusive; for every i with 0 <= i < len(courses), len(courses[i]) = 2; and for every such i, 1 <= courses[i][0] <= 10000 and 1 <= courses[i][1] <= 10000. -/
theorem spec_8 (courses : CourseSlice) (h : Pre courses) :
    ∀ r, Aegis.ScheduleCourse.schedule_course courses = ok r →
      (r.val = (courses.val.length : ℤ) ↔
        ∀ σ : List ℕ, IsPermOf courses.val.length σ → SortedByLastDay courses σ →
          AllPrefixOk courses σ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (courses : CourseSlice) (h : Pre courses), ∀ r, Aegis.ScheduleCourse.schedule_course courses = ok r →
      (r.val = (courses.val.length : ℤ) ↔
        ∀ σ : List ℕ, IsPermOf courses.val.length σ → SortedByLastDay courses σ →
          AllPrefixOk courses σ)) := by
  sorry

/-- Let n = len(courses), and for each valid j let d_j = courses[j][0] and l_j = courses[j][1]. Whenever schedule_course(courses) returns a result r, r equals the maximum length of a sequence of distinct indices from {0, ..., n-1} that does not include i and whose prefix sums satisfy sum_{m=1}^p d_{j_m} <= l_{j_p} for all p.
  Preconditions: len(courses) is between 1 and 10000 inclusive; for every i with 0 <= i < len(courses), len(courses[i]) = 2; and for every such i, 1 <= courses[i][0] <= 10000 and 1 <= courses[i][1] <= 10000. Fix an index i with 0 <= i < len(courses) and courses[i][0] > courses[i][1]. -/
theorem spec_9 (courses : CourseSlice) (h : Pre courses) (i : ℕ)
    (hi : i < courses.val.length) (hbad : lastDay courses i < dur courses i) :
    ∀ r, Aegis.ScheduleCourse.schedule_course courses = ok r →
      ∃ k : ℕ, MaxLenOf (fun idx => Feasible courses idx ∧ i ∉ idx) k ∧ r.val = (k : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (courses : CourseSlice) (h : Pre courses) (i : ℕ)
    (hi : i < courses.val.length) (hbad : lastDay courses i < dur courses i), ∀ r, Aegis.ScheduleCourse.schedule_course courses = ok r →
      ∃ k : ℕ, MaxLenOf (fun idx => Feasible courses idx ∧ i ∉ idx) k ∧ r.val = (k : ℤ)) := by
  sorry

/-- Let n = len(courses). For any permutation pi of {0, ..., n-1}, let courses' be the array of length n with courses'[j] = courses[pi(j)] for every j with 0 <= j < n. Whenever schedule_course(courses) returns a result r and schedule_course(courses') returns a result r', we have r = r'.
  Preconditions: len(courses) is between 1 and 10000 inclusive; for every i with 0 <= i < len(courses), len(courses[i]) = 2; and for every such i, 1 <= courses[i][0] <= 10000 and 1 <= courses[i][1] <= 10000. -/
theorem spec_10 (courses courses' : CourseSlice) (h : Pre courses) (π : List ℕ)
    (hπ : IsPermOf courses.val.length π)
    (hlen : courses'.val.length = courses.val.length)
    (hentries : ∀ j, j < courses.val.length → courses'.val[j]? = courses.val[π.getD j 0]?) :
    ∀ r r', Aegis.ScheduleCourse.schedule_course courses = ok r →
      Aegis.ScheduleCourse.schedule_course courses' = ok r' → r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (courses courses' : CourseSlice) (h : Pre courses) (π : List ℕ)
    (hπ : IsPermOf courses.val.length π)
    (hlen : courses'.val.length = courses.val.length)
    (hentries : ∀ j, j < courses.val.length → courses'.val[j]? = courses.val[π.getD j 0]?), ∀ r r', Aegis.ScheduleCourse.schedule_course courses = ok r →
      Aegis.ScheduleCourse.schedule_course courses' = ok r' → r = r') := by
  sorry

/-- Whenever schedule_course(courses) returns a result r and schedule_course(courses') returns a result r', we have r' >= r.
  Preconditions: Both courses and courses' satisfy the common preconditions: len is between 1 and 10000 inclusive, every inner vector has length 2, and every duration and last day is between 1 and 10000 inclusive. Also len(courses) = len(courses'), and for every i with 0 <= i < len(courses), courses'[i][0] = courses[i][0] and courses'[i][1] >= courses[i][1]. -/
theorem spec_11 (courses courses' : CourseSlice) (h : Pre courses) (h' : Pre courses')
    (hlen : courses'.val.length = courses.val.length)
    (hdur : ∀ i, i < courses.val.length → dur courses' i = dur courses i)
    (hlast : ∀ i, i < courses.val.length → lastDay courses i ≤ lastDay courses' i) :
    ∀ r r', Aegis.ScheduleCourse.schedule_course courses = ok r →
      Aegis.ScheduleCourse.schedule_course courses' = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (courses courses' : CourseSlice) (h : Pre courses) (h' : Pre courses')
    (hlen : courses'.val.length = courses.val.length)
    (hdur : ∀ i, i < courses.val.length → dur courses' i = dur courses i)
    (hlast : ∀ i, i < courses.val.length → lastDay courses i ≤ lastDay courses' i), ∀ r r', Aegis.ScheduleCourse.schedule_course courses = ok r →
      Aegis.ScheduleCourse.schedule_course courses' = ok r' → r.val ≤ r'.val) := by
  sorry

/-- Let n = len(courses), and for each valid i let d_i = courses[i][0] and l_i = courses[i][1]. Whenever schedule_course(courses) returns a result r, there exist r distinct indices i_1, ..., i_r from {0, ..., n-1} (the empty sequence if r = 0) such that l_{i_1} <= ... <= l_{i_r} and for every j with 1 <= j <= r, sum_{m=1}^j d_{i_m} <= l_{i_j}.
  Preconditions: len(courses) is between 1 and 10000 inclusive; for every i with 0 <= i < len(courses), len(courses[i]) = 2; and for every such i, 1 <= courses[i][0] <= 10000 and 1 <= courses[i][1] <= 10000. -/
theorem spec_12 (courses : CourseSlice) (h : Pre courses) :
    ∀ r, Aegis.ScheduleCourse.schedule_course courses = ok r →
      ∃ k : ℕ, r.val = (k : ℤ) ∧
        ∃ idx : List ℕ, idx.length = k ∧ Feasible courses idx ∧ SortedByLastDay courses idx := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (courses : CourseSlice) (h : Pre courses), ∀ r, Aegis.ScheduleCourse.schedule_course courses = ok r →
      ∃ k : ℕ, r.val = (k : ℤ) ∧
        ∃ idx : List ℕ, idx.length = k ∧ Feasible courses idx ∧ SortedByLastDay courses idx) := by
  sorry

end AegisSpec.ScheduleCourse
