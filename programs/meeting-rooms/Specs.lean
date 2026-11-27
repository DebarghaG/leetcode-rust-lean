import Aegis.CanAttendMeetings.Code.Funs

/-!
# Specifications of `Aegis.CanAttendMeetings.can_attend_meetings`

LeetCode problem `meeting-rooms`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CanAttendMeetings

def rows (intervals : Slice (alloc.vec.Vec I64)) : List (List Int) :=
  intervals.val.map (fun row => row.val.map (fun x => x.val))

def n (intervals : Slice (alloc.vec.Vec I64)) : Nat := intervals.val.length

def row (intervals : Slice (alloc.vec.Vec I64)) (i : Nat) : List Int :=
  (rows intervals).getD i []

def start (intervals : Slice (alloc.vec.Vec I64)) (i : Nat) : Int :=
  (row intervals i).getD 0 0

def stop (intervals : Slice (alloc.vec.Vec I64)) (i : Nat) : Int :=
  (row intervals i).getD 1 0

def Wf (intervals : Slice (alloc.vec.Vec I64)) : Prop :=
  n intervals ≤ 10 ^ 4 ∧
    ∀ i : Nat, i < n intervals →
      (row intervals i).length = 2 ∧
        0 ≤ start intervals i ∧
          start intervals i < stop intervals i ∧ stop intervals i ≤ 10 ^ 6

def Overlap (intervals : Slice (alloc.vec.Vec I64)) (i j : Nat) : Prop :=
  start intervals i < stop intervals j ∧ start intervals j < stop intervals i

def Disjoint (intervals : Slice (alloc.vec.Vec I64)) (i j : Nat) : Prop :=
  stop intervals i ≤ start intervals j ∨ stop intervals j ≤ start intervals i

def IsPerm (n : Nat) (pi piInv : Nat → Nat) : Prop :=
  (∀ k : Nat, k < n → pi k < n) ∧
    (∀ k : Nat, k < n → piInv k < n) ∧
      (∀ k : Nat, k < n → piInv (pi k) = k) ∧
        (∀ k : Nat, k < n → pi (piInv k) = k)

def StrictlyIncreasingBelow (n m : Nat) (j : Nat → Nat) : Prop :=
  (∀ k : Nat, k < m → j k < n) ∧ ∀ k l : Nat, k < l → l < m → j k < j l

def IsSubarray (intervals sub : Slice (alloc.vec.Vec I64)) (m : Nat) (j : Nat → Nat) : Prop :=
  n sub = m ∧ ∀ k : Nat, k < m → row sub k = row intervals (j k)

def IsTranslated (intervals shifted : Slice (alloc.vec.Vec I64)) (c : Int) : Prop :=
  n shifted = n intervals ∧
    ∀ i : Nat, i < n intervals →
      start shifted i = start intervals i + c ∧ stop shifted i = stop intervals i + c

def IsScaled (intervals scaled : Slice (alloc.vec.Vec I64)) (k : Int) : Prop :=
  n scaled = n intervals ∧
    ∀ i : Nat, i < n intervals →
      start scaled i = k * start intervals i ∧ stop scaled i = k * stop intervals i

def AdjacentSeparated (intervals : Slice (alloc.vec.Vec I64)) : Prop :=
  ∀ i : Nat, i + 1 < n intervals → stop intervals i ≤ start intervals (i + 1)

def SortedByStart (intervals : Slice (alloc.vec.Vec I64)) : Prop :=
  ∀ i : Nat, i + 1 < n intervals → start intervals i ≤ start intervals (i + 1)

/-- Whenever can_attend_meetings(intervals) returns a result r, r = true if and only if for every pair of indices i and j with 0 <= i < j < n, either e_i <= s_j or e_j <= s_i. Equivalently, r = false if and only if there exist 0 <= i < j < n with s_i < e_j and s_j < e_i; meetings that only touch at an endpoint, with e_i = s_j or e_j = s_i, do not conflict.
  Preconditions: Let n = len(intervals). Assume 0 <= n <= 10^4. For every i with 0 <= i < n, intervals[i] has length exactly 2, and 0 <= intervals[i][0] < intervals[i][1] <= 10^6. All indices are 0-based. Write s_i = intervals[i][0] and e_i = intervals[i][1]. -/
theorem spec_1 (intervals : Slice (alloc.vec.Vec I64)) (h : Wf intervals) :
    (∀ r : Bool,
        Aegis.CanAttendMeetings.can_attend_meetings intervals = ok r →
          (r = true ↔
              ∀ i j : Nat, i < j → j < n intervals → Disjoint intervals i j) ∧
            (r = false ↔
              ∃ i j : Nat, i < j ∧ j < n intervals ∧ Overlap intervals i j)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (h : Wf intervals), (∀ r : Bool,
        Aegis.CanAttendMeetings.can_attend_meetings intervals = ok r →
          (r = true ↔
              ∀ i j : Nat, i < j → j < n intervals → Disjoint intervals i j) ∧
            (r = false ↔
              ∃ i j : Nat, i < j ∧ j < n intervals ∧ Overlap intervals i j))) := by
  sorry

/-- For every intervals satisfying the preconditions, can_attend_meetings(intervals) returns a result r (a Bool) and does not fail: there is no panic, no out-of-bounds access, and no arithmetic overflow.
  Preconditions: Let n = len(intervals). Assume 0 <= n <= 10^4. For every i with 0 <= i < n, intervals[i] has length exactly 2, and 0 <= intervals[i][0] < intervals[i][1] <= 10^6. All indices are 0-based. -/
theorem spec_2 (intervals : Slice (alloc.vec.Vec I64)) (h : Wf intervals) :
    ∃ r : Bool, Aegis.CanAttendMeetings.can_attend_meetings intervals = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (h : Wf intervals), ∃ r : Bool, Aegis.CanAttendMeetings.can_attend_meetings intervals = ok r) := by
  sorry

/-- Whenever the function returns r = false, there exist indices i and j with 0 <= i < j < n such that s_i < e_j and s_j < e_i. Equivalently, some two distinct meetings have a common time t with s_i <= t < e_i and s_j <= t < e_j.
  Preconditions: Let n = len(intervals). Assume 0 <= n <= 10^4. For every i with 0 <= i < n, intervals[i] has length exactly 2, and 0 <= intervals[i][0] < intervals[i][1] <= 10^6. All indices are 0-based. Write s_i = intervals[i][0] and e_i = intervals[i][1]. -/
theorem spec_3 (intervals : Slice (alloc.vec.Vec I64)) (h : Wf intervals)
    (hfalse : Aegis.CanAttendMeetings.can_attend_meetings intervals = ok false) :
    (∃ i j : Nat, i < j ∧ j < n intervals ∧ Overlap intervals i j) ∧
      ∃ i j : Nat,
        i < j ∧ j < n intervals ∧
          ∃ t : Int,
            start intervals i ≤ t ∧ t < stop intervals i ∧
              start intervals j ≤ t ∧ t < stop intervals j := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (h : Wf intervals)
    (hfalse : Aegis.CanAttendMeetings.can_attend_meetings intervals = ok false), (∃ i j : Nat, i < j ∧ j < n intervals ∧ Overlap intervals i j) ∧
      ∃ i j : Nat,
        i < j ∧ j < n intervals ∧
          ∃ t : Int,
            start intervals i ≤ t ∧ t < stop intervals i ∧
              start intervals j ≤ t ∧ t < stop intervals j) := by
  sorry

/-- If there exist distinct indices i and j with s_i = s_j and e_i = e_j, then whenever the function returns r, r = false.
  Preconditions: Let n = len(intervals). Assume 0 <= n <= 10^4. For every i with 0 <= i < n, intervals[i] has length exactly 2, and 0 <= intervals[i][0] < intervals[i][1] <= 10^6. All indices are 0-based. Write s_i = intervals[i][0] and e_i = intervals[i][1]. -/
theorem spec_4 (intervals : Slice (alloc.vec.Vec I64)) (h : Wf intervals)
    (hdup : ∃ i j : Nat,
      i < n intervals ∧ j < n intervals ∧ i ≠ j ∧
        start intervals i = start intervals j ∧ stop intervals i = stop intervals j) :
    ∀ r : Bool, Aegis.CanAttendMeetings.can_attend_meetings intervals = ok r → r = false := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (h : Wf intervals)
    (hdup : ∃ i j : Nat,
      i < n intervals ∧ j < n intervals ∧ i ≠ j ∧
        start intervals i = start intervals j ∧ stop intervals i = stop intervals j), ∀ r : Bool, Aegis.CanAttendMeetings.can_attend_meetings intervals = ok r → r = false) := by
  sorry

/-- If there exist distinct indices i and j such that s_i <= s_j and e_j <= e_i, then whenever the function returns r, r = false.
  Preconditions: Let n = len(intervals). Assume 0 <= n <= 10^4. For every i with 0 <= i < n, intervals[i] has length exactly 2, and 0 <= intervals[i][0] < intervals[i][1] <= 10^6. All indices are 0-based. Write s_i = intervals[i][0] and e_i = intervals[i][1]. -/
theorem spec_5 (intervals : Slice (alloc.vec.Vec I64)) (h : Wf intervals)
    (hnest : ∃ i j : Nat,
      i < n intervals ∧ j < n intervals ∧ i ≠ j ∧
        start intervals i ≤ start intervals j ∧ stop intervals j ≤ stop intervals i) :
    ∀ r : Bool, Aegis.CanAttendMeetings.can_attend_meetings intervals = ok r → r = false := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (h : Wf intervals)
    (hnest : ∃ i j : Nat,
      i < n intervals ∧ j < n intervals ∧ i ≠ j ∧
        start intervals i ≤ start intervals j ∧ stop intervals j ≤ stop intervals i), ∀ r : Bool, Aegis.CanAttendMeetings.can_attend_meetings intervals = ok r → r = false) := by
  sorry

/-- If n >= 2 and there exists an integer t such that s_i <= t < e_i for every i with 0 <= i < n, then whenever the function returns r, r = false.
  Preconditions: Let n = len(intervals). Assume 0 <= n <= 10^4. For every i with 0 <= i < n, intervals[i] has length exactly 2, and 0 <= intervals[i][0] < intervals[i][1] <= 10^6. All indices are 0-based. Write s_i = intervals[i][0] and e_i = intervals[i][1]. -/
theorem spec_6 (intervals : Slice (alloc.vec.Vec I64)) (h : Wf intervals)
    (hn : 2 ≤ n intervals)
    (hcommon : ∃ t : Int, ∀ i : Nat, i < n intervals →
      start intervals i ≤ t ∧ t < stop intervals i) :
    ∀ r : Bool, Aegis.CanAttendMeetings.can_attend_meetings intervals = ok r → r = false := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (h : Wf intervals)
    (hn : 2 ≤ n intervals)
    (hcommon : ∃ t : Int, ∀ i : Nat, i < n intervals →
      start intervals i ≤ t ∧ t < stop intervals i), ∀ r : Bool, Aegis.CanAttendMeetings.can_attend_meetings intervals = ok r → r = false) := by
  sorry

/-- For any permutation pi of the index set {0, 1, ..., n-1}, define intervals_pi by intervals_pi[k] = intervals[pi(k)] for 0 <= k < n. Whenever can_attend_meetings(intervals) returns r and can_attend_meetings(intervals_pi) returns r_pi, we have r = r_pi.
  Preconditions: Let n = len(intervals). Assume 0 <= n <= 10^4. For every i with 0 <= i < n, intervals[i] has length exactly 2, and 0 <= intervals[i][0] < intervals[i][1] <= 10^6. All indices are 0-based. -/
theorem spec_7 (intervals intervals_pi : Slice (alloc.vec.Vec I64))
    (pi piInv : Nat → Nat)
    (h : Wf intervals) (hpi : Wf intervals_pi)
    (hperm : IsPerm (n intervals) pi piInv)
    (hrows : n intervals_pi = n intervals ∧
      ∀ k : Nat, k < n intervals → row intervals_pi k = row intervals (pi k)) :
    ∀ r r_pi : Bool,
      Aegis.CanAttendMeetings.can_attend_meetings intervals = ok r →
        Aegis.CanAttendMeetings.can_attend_meetings intervals_pi = ok r_pi → r = r_pi := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (intervals intervals_pi : Slice (alloc.vec.Vec I64))
    (pi piInv : Nat → Nat)
    (h : Wf intervals) (hpi : Wf intervals_pi)
    (hperm : IsPerm (n intervals) pi piInv)
    (hrows : n intervals_pi = n intervals ∧
      ∀ k : Nat, k < n intervals → row intervals_pi k = row intervals (pi k)), ∀ r r_pi : Bool,
      Aegis.CanAttendMeetings.can_attend_meetings intervals = ok r →
        Aegis.CanAttendMeetings.can_attend_meetings intervals_pi = ok r_pi → r = r_pi) := by
  sorry

/-- For every strictly increasing sequence of indices 0 <= j_0 < j_1 < ... < j_{m-1} < n, let sub be the length-m array with sub[k] = intervals[j_k] for 0 <= k < m. Whenever can_attend_meetings(intervals) returns true, can_attend_meetings(sub) returns true.
  Preconditions: Let n = len(intervals). Assume 0 <= n <= 10^4. For every i with 0 <= i < n, intervals[i] has length exactly 2, and 0 <= intervals[i][0] < intervals[i][1] <= 10^6. All indices are 0-based. -/
theorem spec_8 (intervals sub : Slice (alloc.vec.Vec I64)) (m : Nat) (j : Nat → Nat)
    (h : Wf intervals) (hsub : Wf sub)
    (hj : StrictlyIncreasingBelow (n intervals) m j)
    (hrows : IsSubarray intervals sub m j) :
    Aegis.CanAttendMeetings.can_attend_meetings intervals = ok true →
      Aegis.CanAttendMeetings.can_attend_meetings sub = ok true := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (intervals sub : Slice (alloc.vec.Vec I64)) (m : Nat) (j : Nat → Nat)
    (h : Wf intervals) (hsub : Wf sub)
    (hj : StrictlyIncreasingBelow (n intervals) m j)
    (hrows : IsSubarray intervals sub m j), Aegis.CanAttendMeetings.can_attend_meetings intervals = ok true →
      Aegis.CanAttendMeetings.can_attend_meetings sub = ok true) := by
  sorry

/-- For every array intervals_ext satisfying the same preconditions such that intervals is a subsequence of intervals_ext, if can_attend_meetings(intervals) returns false, then can_attend_meetings(intervals_ext) returns false.
  Preconditions: Let n = len(intervals). Assume 0 <= n <= 10^4. For every i with 0 <= i < n, intervals[i] has length exactly 2, and 0 <= intervals[i][0] < intervals[i][1] <= 10^6. All indices are 0-based. -/
theorem spec_9 (intervals intervals_ext : Slice (alloc.vec.Vec I64))
    (h : Wf intervals) (hext : Wf intervals_ext)
    (hsub : List.Sublist (rows intervals) (rows intervals_ext)) :
    Aegis.CanAttendMeetings.can_attend_meetings intervals = ok false →
      Aegis.CanAttendMeetings.can_attend_meetings intervals_ext = ok false := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (intervals intervals_ext : Slice (alloc.vec.Vec I64))
    (h : Wf intervals) (hext : Wf intervals_ext)
    (hsub : List.Sublist (rows intervals) (rows intervals_ext)), Aegis.CanAttendMeetings.can_attend_meetings intervals = ok false →
      Aegis.CanAttendMeetings.can_attend_meetings intervals_ext = ok false) := by
  sorry

/-- For every integer c such that the translated endpoints satisfy 0 <= s_i + c < e_i + c <= 10^6 for every i, define intervals_c by intervals_c[i][0] = s_i + c and intervals_c[i][1] = e_i + c for all i. Whenever can_attend_meetings(intervals) returns r and can_attend_meetings(intervals_c) returns r_c, we have r = r_c.
  Preconditions: Let n = len(intervals). Assume 0 <= n <= 10^4. For every i with 0 <= i < n, intervals[i] has length exactly 2, and 0 <= intervals[i][0] < intervals[i][1] <= 10^6. All indices are 0-based. Write s_i = intervals[i][0] and e_i = intervals[i][1]. -/
theorem spec_10 (intervals shifted : Slice (alloc.vec.Vec I64)) (c : Int)
    (h : Wf intervals) (hshifted : Wf shifted)
    (hrange : ∀ i : Nat, i < n intervals →
      0 ≤ start intervals i + c ∧ start intervals i + c < stop intervals i + c ∧
        stop intervals i + c ≤ 10 ^ 6)
    (hrows : IsTranslated intervals shifted c) :
    ∀ r r_c : Bool,
      Aegis.CanAttendMeetings.can_attend_meetings intervals = ok r →
        Aegis.CanAttendMeetings.can_attend_meetings shifted = ok r_c → r = r_c := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (intervals shifted : Slice (alloc.vec.Vec I64)) (c : Int)
    (h : Wf intervals) (hshifted : Wf shifted)
    (hrange : ∀ i : Nat, i < n intervals →
      0 ≤ start intervals i + c ∧ start intervals i + c < stop intervals i + c ∧
        stop intervals i + c ≤ 10 ^ 6)
    (hrows : IsTranslated intervals shifted c), ∀ r r_c : Bool,
      Aegis.CanAttendMeetings.can_attend_meetings intervals = ok r →
        Aegis.CanAttendMeetings.can_attend_meetings shifted = ok r_c → r = r_c) := by
  sorry

/-- For every positive integer k such that 0 <= k*s_i < k*e_i <= 10^6 for every i, define intervals_k by intervals_k[i][0] = k*s_i and intervals_k[i][1] = k*e_i. Whenever can_attend_meetings(intervals) returns r and can_attend_meetings(intervals_k) returns r_k, we have r = r_k.
  Preconditions: Let n = len(intervals). Assume 0 <= n <= 10^4. For every i with 0 <= i < n, intervals[i] has length exactly 2, and 0 <= intervals[i][0] < intervals[i][1] <= 10^6. All indices are 0-based. Write s_i = intervals[i][0] and e_i = intervals[i][1]. -/
theorem spec_11 (intervals scaled : Slice (alloc.vec.Vec I64)) (k : Int)
    (h : Wf intervals) (hscaled : Wf scaled) (hkpos : 0 < k)
    (hrange : ∀ i : Nat, i < n intervals →
      0 ≤ k * start intervals i ∧ k * start intervals i < k * stop intervals i ∧
        k * stop intervals i ≤ 10 ^ 6)
    (hrows : IsScaled intervals scaled k) :
    ∀ r r_k : Bool,
      Aegis.CanAttendMeetings.can_attend_meetings intervals = ok r →
        Aegis.CanAttendMeetings.can_attend_meetings scaled = ok r_k → r = r_k := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (intervals scaled : Slice (alloc.vec.Vec I64)) (k : Int)
    (h : Wf intervals) (hscaled : Wf scaled) (hkpos : 0 < k)
    (hrange : ∀ i : Nat, i < n intervals →
      0 ≤ k * start intervals i ∧ k * start intervals i < k * stop intervals i ∧
        k * stop intervals i ≤ 10 ^ 6)
    (hrows : IsScaled intervals scaled k), ∀ r r_k : Bool,
      Aegis.CanAttendMeetings.can_attend_meetings intervals = ok r →
        Aegis.CanAttendMeetings.can_attend_meetings scaled = ok r_k → r = r_k) := by
  sorry

/-- If the meetings are listed in nondecreasing start order, meaning s_i <= s_{i+1} for all 0 <= i < n-1, and every consecutive pair is separated, meaning e_i <= s_{i+1} for all 0 <= i < n-1, then the function returns true.
  Preconditions: Let n = len(intervals). Assume 0 <= n <= 10^4. For every i with 0 <= i < n, intervals[i] has length exactly 2, and 0 <= intervals[i][0] < intervals[i][1] <= 10^6. All indices are 0-based. Write s_i = intervals[i][0] and e_i = intervals[i][1]. -/
theorem spec_12 (intervals : Slice (alloc.vec.Vec I64)) (h : Wf intervals)
    (hsorted : SortedByStart intervals) (hsep : AdjacentSeparated intervals) :
    Aegis.CanAttendMeetings.can_attend_meetings intervals = ok true := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (h : Wf intervals)
    (hsorted : SortedByStart intervals) (hsep : AdjacentSeparated intervals), Aegis.CanAttendMeetings.can_attend_meetings intervals = ok true) := by
  sorry

/-- If the meetings are sorted by nondecreasing start, meaning s_i <= s_{i+1} for all 0 <= i < n-1, then whenever can_attend_meetings(intervals) returns r, r = true if and only if e_i <= s_{i+1} for every 0 <= i < n-1. This is the converse completion of spec_12: under sorted starts, checking only adjacent separated pairs is necessary and sufficient.
  Preconditions: Let n = len(intervals). Assume 0 <= n <= 10^4. For every i with 0 <= i < n, intervals[i] has length exactly 2, and 0 <= intervals[i][0] < intervals[i][1] <= 10^6. All indices are 0-based. Write s_i = intervals[i][0] and e_i = intervals[i][1]. -/
theorem spec_13 (intervals : Slice (alloc.vec.Vec I64)) (h : Wf intervals)
    (hsorted : SortedByStart intervals) :
    ∀ r : Bool,
      Aegis.CanAttendMeetings.can_attend_meetings intervals = ok r →
        (r = true ↔ AdjacentSeparated intervals) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (h : Wf intervals)
    (hsorted : SortedByStart intervals), ∀ r : Bool,
      Aegis.CanAttendMeetings.can_attend_meetings intervals = ok r →
        (r = true ↔ AdjacentSeparated intervals)) := by
  sorry

end AegisSpec.CanAttendMeetings
