import Aegis.EraseOverlapIntervals.Code.Funs

/-!
# Specifications of `Aegis.EraseOverlapIntervals.erase_overlap_intervals`

LeetCode problem `non-overlapping-intervals`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.EraseOverlapIntervals

abbrev IntervalList := Slice (alloc.vec.Vec Std.I64)

def endpointsAt (intervals : IntervalList) (i : Nat) : Option (Int × Int) :=
  match intervals.val[i]? with
  | none => none
  | some iv =>
    match iv.val with
    | [s, e] => some (s.val, e.val)
    | _ => none

def startOf (intervals : IntervalList) (i : Nat) : Int :=
  (endpointsAt intervals i).map Prod.fst |>.getD 0

def endOf (intervals : IntervalList) (i : Nat) : Int :=
  (endpointsAt intervals i).map Prod.snd |>.getD 0

def InputOk (intervals : IntervalList) : Prop :=
  1 ≤ intervals.val.length ∧ intervals.val.length ≤ 100000 ∧
    ∀ i, i < intervals.val.length →
      ∃ s e, endpointsAt intervals i = some (s, e) ∧ -50000 ≤ s ∧ s < e ∧ e ≤ 50000

def NonOverlapping (intervals : IntervalList) (S : Finset Nat) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
    endOf intervals i ≤ startOf intervals j ∨ endOf intervals j ≤ startOf intervals i

def HasOverlapPair (intervals : IntervalList) (n : Nat) : Prop :=
  ∃ i j, i < j ∧ j < n ∧
    ¬ (endOf intervals i ≤ startOf intervals j) ∧ ¬ (endOf intervals j ≤ startOf intervals i)

noncomputable def maxKept (intervals : IntervalList) (n : Nat) : Nat :=
  by
    classical
    exact ((Finset.range n).powerset.filter (fun S => NonOverlapping intervals S)).sup
      (fun S => S.card)

/-- Whenever the function returns a result r, r = n - M, where M = max { |S| : S is a subset of {0,1,...,n-1} such that for every two distinct indices i,j in S, end_i <= start_j or end_j <= start_i }. In words, n - r is the maximum number of given intervals that can be kept so that no two kept intervals overlap in more than a shared endpoint, and r is the minimum number of intervals that must be removed.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 100000; for every i with 0 <= i < n, len(intervals[i]) = 2; and with start_i = intervals[i][0] and end_i = intervals[i][1], assume -50000 <= start_i < end_i <= 50000. -/
theorem spec_1 (intervals : IntervalList) (h : InputOk intervals) :
    ∀ r : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals intervals = ok r →
      r.val = (intervals.val.length : Int) -
        (maxKept intervals intervals.val.length : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (intervals : IntervalList) (h : InputOk intervals), ∀ r : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals intervals = ok r →
      r.val = (intervals.val.length : Int) -
        (maxKept intervals intervals.val.length : Int)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; in particular, it does not fail, panic, overflow, or access an interval out of bounds.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 100000; for every i with 0 <= i < n, len(intervals[i]) = 2; and with start_i = intervals[i][0] and end_i = intervals[i][1], assume -50000 <= start_i < end_i <= 50000. -/
theorem spec_2 (intervals : IntervalList) (h : InputOk intervals) :
    ∃ r : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals intervals = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (intervals : IntervalList) (h : InputOk intervals), ∃ r : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals intervals = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 100000; for every i with 0 <= i < n, len(intervals[i]) = 2; and with start_i = intervals[i][0] and end_i = intervals[i][1], assume -50000 <= start_i < end_i <= 50000. -/
theorem spec_3 (intervals : IntervalList) (h : InputOk intervals) :
    ∀ r : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals intervals = ok r →
      0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (intervals : IntervalList) (h : InputOk intervals), ∀ r : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals intervals = ok r →
      0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= n - 1.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 100000; for every i with 0 <= i < n, len(intervals[i]) = 2; and with start_i = intervals[i][0] and end_i = intervals[i][1], assume -50000 <= start_i < end_i <= 50000. -/
theorem spec_4 (intervals : IntervalList) (h : InputOk intervals) :
    ∀ r : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals intervals = ok r →
      r.val ≤ (intervals.val.length : Int) - 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (intervals : IntervalList) (h : InputOk intervals), ∀ r : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals intervals = ok r →
      r.val ≤ (intervals.val.length : Int) - 1) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every pair of indices i,j with 0 <= i < j < n, end_i <= start_j or end_j <= start_i.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 100000; for every i with 0 <= i < n, len(intervals[i]) = 2; and with start_i = intervals[i][0] and end_i = intervals[i][1], assume -50000 <= start_i < end_i <= 50000. -/
theorem spec_5 (intervals : IntervalList) (h : InputOk intervals) :
    ∀ r : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals intervals = ok r →
      (r.val = 0 ↔
        ∀ i j, i < j → j < intervals.val.length →
          endOf intervals i ≤ startOf intervals j ∨
            endOf intervals j ≤ startOf intervals i) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (intervals : IntervalList) (h : InputOk intervals), ∀ r : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals intervals = ok r →
      (r.val = 0 ↔
        ∀ i j, i < j → j < intervals.val.length →
          endOf intervals i ≤ startOf intervals j ∨
            endOf intervals j ≤ startOf intervals i)) := by
  sorry

/-- Whenever the function returns a result r, there exists a subset S of {0,1,...,n-1} such that |S| = n - r and for every two distinct indices i,j in S, end_i <= start_j or end_j <= start_i.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 100000; for every i with 0 <= i < n, len(intervals[i]) = 2; and with start_i = intervals[i][0] and end_i = intervals[i][1], assume -50000 <= start_i < end_i <= 50000. -/
theorem spec_6 (intervals : IntervalList) (h : InputOk intervals) :
    ∀ r : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals intervals = ok r →
      ∃ S : Finset Nat, (∀ i ∈ S, i < intervals.val.length) ∧
        NonOverlapping intervals S ∧
        (S.card : Int) = (intervals.val.length : Int) - r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (intervals : IntervalList) (h : InputOk intervals), ∀ r : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals intervals = ok r →
      ∃ S : Finset Nat, (∀ i ∈ S, i < intervals.val.length) ∧
        NonOverlapping intervals S ∧
        (S.card : Int) = (intervals.val.length : Int) - r.val) := by
  sorry

/-- Whenever the function returns a result r, for every subset S of {0,1,...,n-1} with the property that for all distinct i,j in S, end_i <= start_j or end_j <= start_i, we have |S| <= n - r.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 100000; for every i with 0 <= i < n, len(intervals[i]) = 2; and with start_i = intervals[i][0] and end_i = intervals[i][1], assume -50000 <= start_i < end_i <= 50000. -/
theorem spec_7 (intervals : IntervalList) (h : InputOk intervals) :
    ∀ r : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals intervals = ok r →
      ∀ S : Finset Nat, (∀ i ∈ S, i < intervals.val.length) →
        NonOverlapping intervals S →
        (S.card : Int) ≤ (intervals.val.length : Int) - r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (intervals : IntervalList) (h : InputOk intervals), ∀ r : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals intervals = ok r →
      ∀ S : Finset Nat, (∀ i ∈ S, i < intervals.val.length) →
        NonOverlapping intervals S →
        (S.card : Int) ≤ (intervals.val.length : Int) - r.val) := by
  sorry

/-- Whenever the function returns a result r, r = n - 1 if and only if for every pair of indices i,j with 0 <= i < j < n, neither end_i <= start_j nor end_j <= start_i (equivalently start_i < end_j and start_j < end_i).
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 100000; for every i with 0 <= i < n, len(intervals[i]) = 2; and with start_i = intervals[i][0] and end_i = intervals[i][1], assume -50000 <= start_i < end_i <= 50000. -/
theorem spec_8 (intervals : IntervalList) (h : InputOk intervals) :
    ∀ r : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals intervals = ok r →
      (r.val = (intervals.val.length : Int) - 1 ↔
        ∀ i j, i < j → j < intervals.val.length →
          ¬ (endOf intervals i ≤ startOf intervals j) ∧
            ¬ (endOf intervals j ≤ startOf intervals i)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (intervals : IntervalList) (h : InputOk intervals), ∀ r : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals intervals = ok r →
      (r.val = (intervals.val.length : Int) - 1 ↔
        ∀ i j, i < j → j < intervals.val.length →
          ¬ (endOf intervals i ≤ startOf intervals j) ∧
            ¬ (endOf intervals j ≤ startOf intervals i))) := by
  sorry

/-- For any two inputs A and B satisfying the preconditions with len(A) = len(B) = n, and any permutation π of {0,1,...,n-1} such that B[i][0] = A[π(i)][0] and B[i][1] = A[π(i)][1] for every i with 0 <= i < n, if r_A is a result returned by the function on A and r_B is a result returned by the function on B, then r_A = r_B.
  Preconditions: Both A and B are interval lists satisfying the input conditions: for X in {A,B}, letting n_X = len(X), we have 1 <= n_X <= 100000, len(X[i]) = 2 for every 0 <= i < n_X, and -50000 <= X[i][0] < X[i][1] <= 50000 for every 0 <= i < n_X. -/
theorem spec_9 (A B : IntervalList) (n : Nat) (hA : InputOk A) (hB : InputOk B)
    (hAn : A.val.length = n) (hBn : B.val.length = n) (π : Equiv.Perm (Fin n))
    (hπ : ∀ (i : Nat) (hi : i < n),
      startOf B i = startOf A (π ⟨i, hi⟩).val ∧ endOf B i = endOf A (π ⟨i, hi⟩).val) :
    ∀ rA rB : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals A = ok rA →
      Aegis.EraseOverlapIntervals.erase_overlap_intervals B = ok rB → rA.val = rB.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (A B : IntervalList) (n : Nat) (hA : InputOk A) (hB : InputOk B)
    (hAn : A.val.length = n) (hBn : B.val.length = n) (π : Equiv.Perm (Fin n))
    (hπ : ∀ (i : Nat) (hi : i < n),
      startOf B i = startOf A (π ⟨i, hi⟩).val ∧ endOf B i = endOf A (π ⟨i, hi⟩).val), ∀ rA rB : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals A = ok rA →
      Aegis.EraseOverlapIntervals.erase_overlap_intervals B = ok rB → rA.val = rB.val) := by
  sorry

/-- For any two inputs A and B satisfying the preconditions with len(A) = len(B) = n and any integer c such that for every i with 0 <= i < n, B[i][0] = A[i][0] + c and B[i][1] = A[i][1] + c, if r_A is a result returned by the function on A and r_B is a result returned by the function on B, then r_A = r_B.
  Preconditions: Both A and B are interval lists satisfying the input conditions: for X in {A,B}, letting n_X = len(X), we have 1 <= n_X <= 100000, len(X[i]) = 2 for every 0 <= i < n_X, and -50000 <= X[i][0] < X[i][1] <= 50000 for every 0 <= i < n_X. -/
theorem spec_10 (A B : IntervalList) (n : Nat) (c : Int) (hA : InputOk A) (hB : InputOk B)
    (hAn : A.val.length = n) (hBn : B.val.length = n)
    (hc : ∀ i, i < n →
      startOf B i = startOf A i + c ∧ endOf B i = endOf A i + c) :
    ∀ rA rB : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals A = ok rA →
      Aegis.EraseOverlapIntervals.erase_overlap_intervals B = ok rB → rA.val = rB.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (A B : IntervalList) (n : Nat) (c : Int) (hA : InputOk A) (hB : InputOk B)
    (hAn : A.val.length = n) (hBn : B.val.length = n)
    (hc : ∀ i, i < n →
      startOf B i = startOf A i + c ∧ endOf B i = endOf A i + c), ∀ rA rB : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals A = ok rA →
      Aegis.EraseOverlapIntervals.erase_overlap_intervals B = ok rB → rA.val = rB.val) := by
  sorry

/-- For any two inputs A and B satisfying the preconditions with len(A) = len(B) = n and for every i with 0 <= i < n, B[i][0] = -A[i][1] and B[i][1] = -A[i][0], if r_A is a result returned by the function on A and r_B is a result returned by the function on B, then r_A = r_B.
  Preconditions: Both A and B are interval lists satisfying the input conditions: for X in {A,B}, letting n_X = len(X), we have 1 <= n_X <= 100000, len(X[i]) = 2 for every 0 <= i < n_X, and -50000 <= X[i][0] < X[i][1] <= 50000 for every 0 <= i < n_X. -/
theorem spec_11 (A B : IntervalList) (n : Nat) (hA : InputOk A) (hB : InputOk B)
    (hAn : A.val.length = n) (hBn : B.val.length = n)
    (hc : ∀ i, i < n → startOf B i = - endOf A i ∧ endOf B i = - startOf A i) :
    ∀ rA rB : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals A = ok rA →
      Aegis.EraseOverlapIntervals.erase_overlap_intervals B = ok rB → rA.val = rB.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (A B : IntervalList) (n : Nat) (hA : InputOk A) (hB : InputOk B)
    (hAn : A.val.length = n) (hBn : B.val.length = n)
    (hc : ∀ i, i < n → startOf B i = - endOf A i ∧ endOf B i = - startOf A i), ∀ rA rB : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals A = ok rA →
      Aegis.EraseOverlapIntervals.erase_overlap_intervals B = ok rB → rA.val = rB.val) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if there exists an index k with 0 <= k < n such that (i) for every two distinct indices i,j in {0,1,...,n-1} \ {k}, end_i <= start_j or end_j <= start_i, and (ii) the whole set {0,1,...,n-1} is not pairwise non-overlapping, meaning there exist i,j with 0 <= i < j < n such that neither end_i <= start_j nor end_j <= start_i.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 100000; for every i with 0 <= i < n, len(intervals[i]) = 2; and with start_i = intervals[i][0] and end_i = intervals[i][1], assume -50000 <= start_i < end_i <= 50000. -/
theorem spec_12 (intervals : IntervalList) (h : InputOk intervals) :
    ∀ r : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals intervals = ok r →
      (r.val = 1 ↔
        ∃ k, k < intervals.val.length ∧
          NonOverlapping intervals ((Finset.range intervals.val.length).erase k) ∧
          HasOverlapPair intervals intervals.val.length) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (intervals : IntervalList) (h : InputOk intervals), ∀ r : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals intervals = ok r →
      (r.val = 1 ↔
        ∃ k, k < intervals.val.length ∧
          NonOverlapping intervals ((Finset.range intervals.val.length).erase k) ∧
          HasOverlapPair intervals intervals.val.length)) := by
  sorry

/-- Let n = len(A). Assume len(B) = n + 1, B[i] = A[i] for every 0 <= i < n, and the last interval B[n] is non-overlapping with every A[i], i.e. for every i with 0 <= i < n, A[i][1] <= B[n][0] or B[n][1] <= A[i][0]. If r_A is a result returned by the function on A and r_B is a result returned by the function on B, then r_A = r_B.
  Preconditions: Both A and B are interval lists satisfying the input conditions: for X in {A,B}, letting n_X = len(X), we have 1 <= n_X <= 100000, len(X[i]) = 2 for every 0 <= i < n_X, and -50000 <= X[i][0] < X[i][1] <= 50000 for every 0 <= i < n_X. -/
theorem spec_13 (A B : IntervalList) (n : Nat) (hA : InputOk A) (hB : InputOk B)
    (hAn : A.val.length = n) (hBn : B.val.length = n + 1)
    (hpre : ∀ i, i < n → endpointsAt B i = endpointsAt A i)
    (hlast : ∀ i, i < n → endOf A i ≤ startOf B n ∨ endOf B n ≤ startOf A i) :
    ∀ rA rB : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals A = ok rA →
      Aegis.EraseOverlapIntervals.erase_overlap_intervals B = ok rB → rA.val = rB.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (A B : IntervalList) (n : Nat) (hA : InputOk A) (hB : InputOk B)
    (hAn : A.val.length = n) (hBn : B.val.length = n + 1)
    (hpre : ∀ i, i < n → endpointsAt B i = endpointsAt A i)
    (hlast : ∀ i, i < n → endOf A i ≤ startOf B n ∨ endOf B n ≤ startOf A i), ∀ rA rB : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals A = ok rA →
      Aegis.EraseOverlapIntervals.erase_overlap_intervals B = ok rB → rA.val = rB.val) := by
  sorry

/-- If r_A is a result returned by the function on A and r_B is a result returned by the function on B, then r_A <= r_B <= r_A + 1. In words, adding one interval can never decrease the minimum number of removals and can increase it by at most one.
  Preconditions: Both A and B are interval lists satisfying the input conditions: for X in {A,B}, letting n_X = len(X), we have 1 <= n_X <= 100000, len(X[i]) = 2 for every 0 <= i < n_X, and -50000 <= X[i][0] < X[i][1] <= 50000 for every 0 <= i < n_X. Let n = len(A). Assume len(B) = n + 1, B[i] = A[i] for every 0 <= i < n, and B[n] is any interval satisfying len(B[n]) = 2 and -50000 <= B[n][0] < B[n][1] <= 50000 (i.e. B is A with one extra interval appended). -/
theorem spec_14 (A B : IntervalList) (n : Nat) (hA : InputOk A) (hB : InputOk B)
    (hAn : A.val.length = n) (hBn : B.val.length = n + 1)
    (hpre : ∀ i, i < n → endpointsAt B i = endpointsAt A i) :
    ∀ rA rB : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals A = ok rA →
      Aegis.EraseOverlapIntervals.erase_overlap_intervals B = ok rB →
      rA.val ≤ rB.val ∧ rB.val ≤ rA.val + 1 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (A B : IntervalList) (n : Nat) (hA : InputOk A) (hB : InputOk B)
    (hAn : A.val.length = n) (hBn : B.val.length = n + 1)
    (hpre : ∀ i, i < n → endpointsAt B i = endpointsAt A i), ∀ rA rB : Std.I64, Aegis.EraseOverlapIntervals.erase_overlap_intervals A = ok rA →
      Aegis.EraseOverlapIntervals.erase_overlap_intervals B = ok rB →
      rA.val ≤ rB.val ∧ rB.val ≤ rA.val + 1) := by
  sorry

end AegisSpec.EraseOverlapIntervals
