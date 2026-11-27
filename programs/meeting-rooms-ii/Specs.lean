import Aegis.MinMeetingRooms.Code.Funs
import Mathlib.Data.Real.Basic

/-!
# Specifications of `Aegis.MinMeetingRooms.min_meeting_rooms`

LeetCode problem `meeting-rooms-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinMeetingRooms

def vecStart (v : alloc.vec.Vec Std.I64) : Int :=
  match v.val with
  | [] => 0
  | x :: _ => x.val

def vecEnd (v : alloc.vec.Vec Std.I64) : Int :=
  match v.val with
  | _ :: y :: _ => y.val
  | _ => 0

def ValidInput (intervals : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  1 ≤ intervals.val.length ∧
    intervals.val.length ≤ 10000 ∧
      (∀ (i : Nat) (hi : i < intervals.val.length), (intervals.val[i]).val.length = 2) ∧
        ∀ (i : Nat) (hi : i < intervals.val.length),
          0 ≤ vecStart (intervals.val[i]) ∧
            vecStart (intervals.val[i]) < vecEnd (intervals.val[i]) ∧
              vecEnd (intervals.val[i]) ≤ 1000000

noncomputable def activeAt (intervals : Slice (alloc.vec.Vec Std.I64)) (t : ℝ) : Nat :=
  intervals.val.countP (fun v => decide ((vecStart v : ℝ) ≤ t ∧ t < (vecEnd v : ℝ)))

def IsMaxActive (intervals : Slice (alloc.vec.Vec Std.I64)) (r : Nat) : Prop :=
  (∀ t : ℝ, activeAt intervals t ≤ r) ∧ ∃ t : ℝ, activeAt intervals t = r

noncomputable def startLoad (intervals : Slice (alloc.vec.Vec Std.I64))
    (i : Fin intervals.val.length) : Nat :=
  activeAt intervals ((vecStart (intervals.val.get i) : ℝ))

noncomputable def maxStartLoad (intervals : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  (List.finRange intervals.val.length).foldr (fun i acc => max (startLoad intervals i) acc) 0

def RoomAssignable (intervals : Slice (alloc.vec.Vec Std.I64)) (R : Nat) : Prop :=
  ∃ room : Fin intervals.val.length → Fin R,
    ∀ i j : Fin intervals.val.length,
      room i = room j →
        i = j ∨
          vecEnd (intervals.val.get i) ≤ vecStart (intervals.val.get j) ∨
            vecEnd (intervals.val.get j) ≤ vecStart (intervals.val.get i)

def IsLeastRoomCount (intervals : Slice (alloc.vec.Vec Std.I64)) (r : Nat) : Prop :=
  RoomAssignable intervals r ∧ ∀ R : Nat, RoomAssignable intervals R → r ≤ R

/-- Whenever min_meeting_rooms returns a result r, r is the minimum number of conference rooms required for the meetings in intervals. Equivalently, for every real number t define C(t) to be the number of indices i with 0 <= i < len(intervals) and s_i <= t < e_i; then r is the maximum value of C(t) over all real t. Intervals are half-open, so an interval ending at t and an interval starting at t do not overlap.
  Preconditions: intervals is a slice of vectors such that 1 <= len(intervals) <= 10000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2; writing s_i = intervals[i][0] and e_i = intervals[i][1], we have 0 <= s_i < e_i <= 1000000 for every i. -/
theorem spec_1 (intervals : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput intervals) :
    ∀ r : Std.I64,
      Aegis.MinMeetingRooms.min_meeting_rooms intervals = ok r → IsMaxActive intervals r.val.toNat := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput intervals), ∀ r : Std.I64,
      Aegis.MinMeetingRooms.min_meeting_rooms intervals = ok r → IsMaxActive intervals r.val.toNat) := by
  sorry

/-- For every intervals satisfying the preconditions, min_meeting_rooms returns a result r; it does not panic, access out of bounds, or overflow.
  Preconditions: intervals is a slice of vectors such that 1 <= len(intervals) <= 10000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2; writing s_i = intervals[i][0] and e_i = intervals[i][1], we have 0 <= s_i < e_i <= 1000000 for every i. -/
theorem spec_2 (intervals : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput intervals) :
    ∃ r : Std.I64, Aegis.MinMeetingRooms.min_meeting_rooms intervals = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput intervals), ∃ r : Std.I64, Aegis.MinMeetingRooms.min_meeting_rooms intervals = ok r) := by
  sorry

/-- Whenever min_meeting_rooms returns a result r, r >= 1.
  Preconditions: intervals is a slice of vectors such that 1 <= len(intervals) <= 10000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2; writing s_i = intervals[i][0] and e_i = intervals[i][1], we have 0 <= s_i < e_i <= 1000000 for every i. -/
theorem spec_3 (intervals : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput intervals) :
    ∀ r : Std.I64, Aegis.MinMeetingRooms.min_meeting_rooms intervals = ok r → 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput intervals), ∀ r : Std.I64, Aegis.MinMeetingRooms.min_meeting_rooms intervals = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever min_meeting_rooms returns a result r, r <= len(intervals).
  Preconditions: intervals is a slice of vectors such that 1 <= len(intervals) <= 10000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2; writing s_i = intervals[i][0] and e_i = intervals[i][1], we have 0 <= s_i < e_i <= 1000000 for every i. -/
theorem spec_4 (intervals : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput intervals) :
    ∀ r : Std.I64,
      Aegis.MinMeetingRooms.min_meeting_rooms intervals = ok r →
        r.val ≤ (intervals.val.length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput intervals), ∀ r : Std.I64,
      Aegis.MinMeetingRooms.min_meeting_rooms intervals = ok r →
        r.val ≤ (intervals.val.length : Int)) := by
  sorry

/-- Whenever min_meeting_rooms returns a result r, for each i let A_i be the number of indices j with 0 <= j < len(intervals) and s_j <= s_i < e_j. Then r = max over 0 <= i < len(intervals) of A_i.
  Preconditions: intervals is a slice of vectors such that 1 <= len(intervals) <= 10000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2; writing s_i = intervals[i][0] and e_i = intervals[i][1], we have 0 <= s_i < e_i <= 1000000 for every i. -/
theorem spec_5 (intervals : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput intervals) :
    ∀ r : Std.I64,
      Aegis.MinMeetingRooms.min_meeting_rooms intervals = ok r →
        r.val.toNat = maxStartLoad intervals := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput intervals), ∀ r : Std.I64,
      Aegis.MinMeetingRooms.min_meeting_rooms intervals = ok r →
        r.val.toNat = maxStartLoad intervals) := by
  sorry

/-- Whenever min_meeting_rooms returns a result r, r is the least integer R >= 0 for which there exists a function room from the index set {i | 0 <= i < len(intervals)} to {0, 1, ..., R-1} such that for all indices i and j with room(i) = room(j), either i = j or e_i <= s_j or e_j <= s_i. Equivalently, r is the minimum number of pairwise non-overlapping groups into which the intervals can be partitioned, where empty groups are allowed.
  Preconditions: intervals is a slice of vectors such that 1 <= len(intervals) <= 10000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2; writing s_i = intervals[i][0] and e_i = intervals[i][1], we have 0 <= s_i < e_i <= 1000000 for every i. -/
theorem spec_6 (intervals : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput intervals) :
    ∀ r : Std.I64,
      Aegis.MinMeetingRooms.min_meeting_rooms intervals = ok r →
        IsLeastRoomCount intervals r.val.toNat := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput intervals), ∀ r : Std.I64,
      Aegis.MinMeetingRooms.min_meeting_rooms intervals = ok r →
        IsLeastRoomCount intervals r.val.toNat) := by
  sorry

/-- Whenever min_meeting_rooms returns a result r, there exists a real number t such that exactly r indices i satisfy 0 <= i < len(intervals) and s_i <= t < e_i.
  Preconditions: intervals is a slice of vectors such that 1 <= len(intervals) <= 10000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2; writing s_i = intervals[i][0] and e_i = intervals[i][1], we have 0 <= s_i < e_i <= 1000000 for every i. -/
theorem spec_7 (intervals : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput intervals) :
    ∀ r : Std.I64,
      Aegis.MinMeetingRooms.min_meeting_rooms intervals = ok r →
        ∃ t : ℝ, activeAt intervals t = r.val.toNat := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput intervals), ∀ r : Std.I64,
      Aegis.MinMeetingRooms.min_meeting_rooms intervals = ok r →
        ∃ t : ℝ, activeAt intervals t = r.val.toNat) := by
  sorry

/-- Whenever min_meeting_rooms returns a result r, for every real number t, the number of indices i with 0 <= i < len(intervals) and s_i <= t < e_i is at most r.
  Preconditions: intervals is a slice of vectors such that 1 <= len(intervals) <= 10000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2; writing s_i = intervals[i][0] and e_i = intervals[i][1], we have 0 <= s_i < e_i <= 1000000 for every i. -/
theorem spec_8 (intervals : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput intervals) :
    ∀ r : Std.I64,
      Aegis.MinMeetingRooms.min_meeting_rooms intervals = ok r →
        ∀ t : ℝ, activeAt intervals t ≤ r.val.toNat := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput intervals), ∀ r : Std.I64,
      Aegis.MinMeetingRooms.min_meeting_rooms intervals = ok r →
        ∀ t : ℝ, activeAt intervals t ≤ r.val.toNat) := by
  sorry

/-- Whenever min_meeting_rooms intervals returns r and min_meeting_rooms intervals2 returns r2, r = r2.
  Preconditions: intervals and intervals2 are slices of vectors each satisfying 1 <= len <= 10000, each inner vector has length 2, and for every index the endpoints satisfy 0 <= start < end <= 1000000. Write s_i, e_i for intervals and s2_i, e2_i for intervals2. There exists a bijection pi from {0, ..., len(intervals)-1} to {0, ..., len(intervals2)-1} such that for every i, s2_i = s_{pi(i)} and e2_i = e_{pi(i)}. -/
theorem spec_9 (intervals intervals2 : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput intervals) (h2 : ValidInput intervals2)
    (e : Fin intervals.val.length ≃ Fin intervals2.val.length)
    (he : ∀ i : Fin intervals.val.length,
      vecStart (intervals2.val.get (e i)) = vecStart (intervals.val.get i) ∧
        vecEnd (intervals2.val.get (e i)) = vecEnd (intervals.val.get i)) :
    ∀ r r2 : Std.I64,
      Aegis.MinMeetingRooms.min_meeting_rooms intervals = ok r →
        Aegis.MinMeetingRooms.min_meeting_rooms intervals2 = ok r2 → r.val = r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (intervals intervals2 : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput intervals) (h2 : ValidInput intervals2)
    (e : Fin intervals.val.length ≃ Fin intervals2.val.length)
    (he : ∀ i : Fin intervals.val.length,
      vecStart (intervals2.val.get (e i)) = vecStart (intervals.val.get i) ∧
        vecEnd (intervals2.val.get (e i)) = vecEnd (intervals.val.get i)), ∀ r r2 : Std.I64,
      Aegis.MinMeetingRooms.min_meeting_rooms intervals = ok r →
        Aegis.MinMeetingRooms.min_meeting_rooms intervals2 = ok r2 → r.val = r2.val) := by
  sorry

end AegisSpec.MinMeetingRooms
