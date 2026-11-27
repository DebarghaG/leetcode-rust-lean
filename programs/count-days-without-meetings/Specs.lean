import Aegis.CountDays.Code.Funs

/-!
# Specifications of `Aegis.CountDays.count_days`

LeetCode problem `count-days-without-meetings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountDays

def meetingVal (v : alloc.vec.Vec Aeneas.Std.I64) : List Int := v.val.map (fun x => x.val)

def meetingsVal (meetings : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64)) :
    List (List Int) :=
  meetings.val.map meetingVal

def startOf (iv : List Int) : Int := match iv with
  | s :: _ => s
  | [] => 0

def endOf (iv : List Int) : Int := match iv with
  | _ :: e :: _ => e
  | _ => 0

abbrev covered (ms : List (List Int)) (d : Int) : Prop :=
  ∃ iv ∈ ms, startOf iv ≤ d ∧ d ≤ endOf iv

def allCovered (D : Int) (ms : List (List Int)) : Prop :=
  ∀ d : Int, 1 ≤ d → d ≤ D → covered ms d

def pairwiseDisjoint (ms : List (List Int)) : Prop :=
  ∀ (i j : Nat) (hi : i < ms.length) (hj : j < ms.length), i < j →
    endOf (ms[i]'hi) < startOf (ms[j]'hj) ∨ endOf (ms[j]'hj) < startOf (ms[i]'hi)

def ivlSize (iv : List Int) : Int := match iv with
  | [s, e] => e - s + 1
  | _ => 0

def intsUpto (lo hi : Int) : Finset Int :=
  (Finset.range (hi + 1 - lo).toNat).image (fun k : Nat => lo + (k : Int))

def uncoveredCount (D : Int) (ms : List (List Int)) : Int :=
  (((intsUpto 1 D).filter (fun d => ¬ covered ms d)).card : Int)

def listMin : List Int → Int
  | [] => 0
  | x :: xs => xs.foldr min x

def listMax : List Int → Int
  | [] => 0
  | x :: xs => xs.foldr max x

def totalMeetingLength (ms : List (List Int)) : Int := (ms.map ivlSize).sum

def minStart (ms : List (List Int)) : Int := listMin (ms.map startOf)

def maxEnd (ms : List (List Int)) : Int := listMax (ms.map endOf)

def maxMeetingLength (ms : List (List Int)) : Int := listMax (ms.map ivlSize)

/-- Define a day d to be covered by meetings if there exists an index i with 0 <= i < len(meetings) and s_i <= d <= e_i. The function returns a result r (it does not fail) and the integer value R of r equals the number of integers d such that 1 <= d <= D and d is not covered by meetings.
  Preconditions: Let D be the integer value of days. Assume 1 <= D <= 10^9, 1 <= len(meetings) <= 10^5, and for every i with 0 <= i < len(meetings), len(meetings[i]) = 2 and 1 <= meetings[i][0] <= meetings[i][1] <= D. Write s_i = meetings[i][0] and e_i = meetings[i][1] for each such i. -/
theorem spec_1
    (days : Aeneas.Std.I64) (meetings : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D) :
    ∃ r : Aeneas.Std.I64,
      Aegis.CountDays.count_days days meetings = ok r ∧
      r.val = uncoveredCount D (meetingsVal meetings) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (days : Aeneas.Std.I64) (meetings : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D), ∃ r : Aeneas.Std.I64,
      Aegis.CountDays.count_days days meetings = ok r ∧
      r.val = uncoveredCount D (meetingsVal meetings)) := by
  sorry

/-- The function returns a result r (it does not fail) and its integer value R satisfies 0 <= R <= D.
  Preconditions: Let D be the integer value of days. Assume 1 <= D <= 10^9, 1 <= len(meetings) <= 10^5, and for every i with 0 <= i < len(meetings), len(meetings[i]) = 2 and 1 <= meetings[i][0] <= meetings[i][1] <= D. Write s_i = meetings[i][0] and e_i = meetings[i][1] for each such i. -/
theorem spec_2
    (days : Aeneas.Std.I64) (meetings : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D) :
    ∃ r : Aeneas.Std.I64,
      Aegis.CountDays.count_days days meetings = ok r ∧
      0 ≤ r.val ∧ r.val ≤ D := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (days : Aeneas.Std.I64) (meetings : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D), ∃ r : Aeneas.Std.I64,
      Aegis.CountDays.count_days days meetings = ok r ∧
      0 ≤ r.val ∧ r.val ≤ D) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result (it does not fail, overflow, panic, or go out of bounds).
  Preconditions: Let D be the integer value of days. Assume 1 <= D <= 10^9, 1 <= len(meetings) <= 10^5, and for every i with 0 <= i < len(meetings), len(meetings[i]) = 2 and 1 <= meetings[i][0] <= meetings[i][1] <= D. Write s_i = meetings[i][0] and e_i = meetings[i][1] for each such i. -/
theorem spec_3
    (days : Aeneas.Std.I64) (meetings : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D) :
    ∃ r : Aeneas.Std.I64, Aegis.CountDays.count_days days meetings = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (days : Aeneas.Std.I64) (meetings : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D), ∃ r : Aeneas.Std.I64, Aegis.CountDays.count_days days meetings = ok r) := by
  sorry

/-- The function returns a result r and its integer value R equals D - Σ_{i=0}^{len(meetings)-1} (e_i - s_i + 1).
  Preconditions: Let D be the integer value of days. Assume 1 <= D <= 10^9, 1 <= len(meetings) <= 10^5, and for every i with 0 <= i < len(meetings), len(meetings[i]) = 2 and 1 <= meetings[i][0] <= meetings[i][1] <= D. Write s_i = meetings[i][0] and e_i = meetings[i][1] for each such i. Assume that for every pair of indices i,j with 0 <= i < j < len(meetings), the intervals [s_i,e_i] and [s_j,e_j] are disjoint, i.e., e_i < s_j or e_j < s_i. -/
theorem spec_4
    (days : Aeneas.Std.I64) (meetings : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D)
    (hdisj : pairwiseDisjoint (meetingsVal meetings)) :
    ∃ r : Aeneas.Std.I64,
      Aegis.CountDays.count_days days meetings = ok r ∧
      r.val = D - totalMeetingLength (meetingsVal meetings) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (days : Aeneas.Std.I64) (meetings : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D)
    (hdisj : pairwiseDisjoint (meetingsVal meetings)), ∃ r : Aeneas.Std.I64,
      Aegis.CountDays.count_days days meetings = ok r ∧
      r.val = D - totalMeetingLength (meetingsVal meetings)) := by
  sorry

/-- Whenever the call count_days(days, meetings) returns a result r and the call count_days(days, meetings') returns a result r', the integer values R and R' are equal.
  Preconditions: Let D be the integer value of days. Assume 1 <= D <= 10^9. Assume meetings and meetings' are two meeting lists, each satisfying: 1 <= len(meetings), len(meetings') <= 10^5, and for every index in the appropriate range, the inner vector has length 2 and 1 <= start <= end <= D. Write s_i,e_i for meetings and s'_j,e'_j for meetings'. Suppose that for every integer d with 1 <= d <= D, d is covered by meetings if and only if d is covered by meetings', i.e., (∃i, s_i <= d <= e_i) iff (∃j, s'_j <= d <= e'_j). -/
theorem spec_5
    (days : Aeneas.Std.I64)
    (meetings meetings' : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hlen_lb' : 1 ≤ (meetingsVal meetings').length)
    (hlen_ub' : (meetingsVal meetings').length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D)
    (hwf' : ∀ iv ∈ meetingsVal meetings', ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D)
    (hsame : ∀ d : Int, 1 ≤ d → d ≤ D →
      (covered (meetingsVal meetings) d ↔ covered (meetingsVal meetings') d)) :
    ∀ r r' : Aeneas.Std.I64,
      Aegis.CountDays.count_days days meetings = ok r →
      Aegis.CountDays.count_days days meetings' = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (days : Aeneas.Std.I64)
    (meetings meetings' : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hlen_lb' : 1 ≤ (meetingsVal meetings').length)
    (hlen_ub' : (meetingsVal meetings').length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D)
    (hwf' : ∀ iv ∈ meetingsVal meetings', ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D)
    (hsame : ∀ d : Int, 1 ≤ d → d ≤ D →
      (covered (meetingsVal meetings) d ↔ covered (meetingsVal meetings') d)), ∀ r r' : Aeneas.Std.I64,
      Aegis.CountDays.count_days days meetings = ok r →
      Aegis.CountDays.count_days days meetings' = ok r' →
      r.val = r'.val) := by
  sorry

/-- Whenever both calls count_days(days, meetings) and count_days(days, meetings') return results r and r', their integer values satisfy R' <= R.
  Preconditions: Let D be the integer value of days. Assume 1 <= D <= 10^9. Assume meetings and meetings' are two meeting lists, each satisfying: 1 <= len(meetings), len(meetings') <= 10^5, and for every index in the appropriate range, the inner vector has length 2 and 1 <= start <= end <= D. Write s_i,e_i for meetings and s'_j,e'_j for meetings'. Suppose that for every integer d with 1 <= d <= D, if d is covered by meetings then d is covered by meetings', i.e., (∃i, s_i <= d <= e_i) implies (∃j, s'_j <= d <= e'_j). -/
theorem spec_6
    (days : Aeneas.Std.I64)
    (meetings meetings' : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hlen_lb' : 1 ≤ (meetingsVal meetings').length)
    (hlen_ub' : (meetingsVal meetings').length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D)
    (hwf' : ∀ iv ∈ meetingsVal meetings', ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D)
    (hmono : ∀ d : Int, 1 ≤ d → d ≤ D →
      (covered (meetingsVal meetings) d → covered (meetingsVal meetings') d)) :
    ∀ r r' : Aeneas.Std.I64,
      Aegis.CountDays.count_days days meetings = ok r →
      Aegis.CountDays.count_days days meetings' = ok r' →
      r'.val ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (days : Aeneas.Std.I64)
    (meetings meetings' : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hlen_lb' : 1 ≤ (meetingsVal meetings').length)
    (hlen_ub' : (meetingsVal meetings').length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D)
    (hwf' : ∀ iv ∈ meetingsVal meetings', ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D)
    (hmono : ∀ d : Int, 1 ≤ d → d ≤ D →
      (covered (meetingsVal meetings) d → covered (meetingsVal meetings') d)), ∀ r r' : Aeneas.Std.I64,
      Aegis.CountDays.count_days days meetings = ok r →
      Aegis.CountDays.count_days days meetings' = ok r' →
      r'.val ≤ r.val) := by
  sorry

/-- The function returns a result r with integer value R = 0 if and only if for every integer d with 1 <= d <= D there exists an index i with 0 <= i < len(meetings) and s_i <= d <= e_i.
  Preconditions: Let D be the integer value of days. Assume 1 <= D <= 10^9, 1 <= len(meetings) <= 10^5, and for every i with 0 <= i < len(meetings), len(meetings[i]) = 2 and 1 <= meetings[i][0] <= meetings[i][1] <= D. Write s_i = meetings[i][0] and e_i = meetings[i][1] for each such i. -/
theorem spec_7
    (days : Aeneas.Std.I64) (meetings : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D) :
    ∃ r : Aeneas.Std.I64,
      Aegis.CountDays.count_days days meetings = ok r ∧
      (r.val = 0 ↔ allCovered D (meetingsVal meetings)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (days : Aeneas.Std.I64) (meetings : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D), ∃ r : Aeneas.Std.I64,
      Aegis.CountDays.count_days days meetings = ok r ∧
      (r.val = 0 ↔ allCovered D (meetingsVal meetings))) := by
  sorry

/-- The function returns a result r and its integer value R equals (a - 1) + (D - b).
  Preconditions: Let D be the integer value of days. Assume 1 <= D <= 10^9, 1 <= len(meetings) <= 10^5, and for every i with 0 <= i < len(meetings), len(meetings[i]) = 2 and 1 <= meetings[i][0] <= meetings[i][1] <= D. Write s_i = meetings[i][0] and e_i = meetings[i][1] for each such i. Assume there exist integers a and b with 1 <= a <= b <= D such that for every integer d with 1 <= d <= D, there exists an index i with 0 <= i < len(meetings) and s_i <= d <= e_i if and only if a <= d <= b. -/
theorem spec_8
    (days : Aeneas.Std.I64) (meetings : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D)
    (a b : Int) (ha_lb : 1 ≤ a) (hab : a ≤ b) (hb_ub : b ≤ D)
    (hcover : ∀ d : Int, 1 ≤ d → d ≤ D →
      (covered (meetingsVal meetings) d ↔ a ≤ d ∧ d ≤ b)) :
    ∃ r : Aeneas.Std.I64,
      Aegis.CountDays.count_days days meetings = ok r ∧
      r.val = (a - 1) + (D - b) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (days : Aeneas.Std.I64) (meetings : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D)
    (a b : Int) (ha_lb : 1 ≤ a) (hab : a ≤ b) (hb_ub : b ≤ D)
    (hcover : ∀ d : Int, 1 ≤ d → d ≤ D →
      (covered (meetingsVal meetings) d ↔ a ≤ d ∧ d ≤ b)), ∃ r : Aeneas.Std.I64,
      Aegis.CountDays.count_days days meetings = ok r ∧
      r.val = (a - 1) + (D - b)) := by
  sorry

/-- The function returns a result r and its integer value R satisfies R >= (s_min - 1) + (D - e_max).
  Preconditions: Let D be the integer value of days. Assume 1 <= D <= 10^9, 1 <= len(meetings) <= 10^5, and for every i with 0 <= i < len(meetings), len(meetings[i]) = 2 and 1 <= meetings[i][0] <= meetings[i][1] <= D. Write s_i = meetings[i][0] and e_i = meetings[i][1] for each such i. Let s_min = min_{0<=i<len(meetings)} s_i and e_max = max_{0<=i<len(meetings)} e_i. -/
theorem spec_9
    (days : Aeneas.Std.I64) (meetings : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D) :
    ∃ r : Aeneas.Std.I64,
      Aegis.CountDays.count_days days meetings = ok r ∧
      r.val ≥ (minStart (meetingsVal meetings) - 1) + (D - maxEnd (meetingsVal meetings)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (days : Aeneas.Std.I64) (meetings : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D), ∃ r : Aeneas.Std.I64,
      Aegis.CountDays.count_days days meetings = ok r ∧
      r.val ≥ (minStart (meetingsVal meetings) - 1) + (D - maxEnd (meetingsVal meetings))) := by
  sorry

/-- The function returns a result r and its integer value R satisfies R <= D - L.
  Preconditions: Let D be the integer value of days. Assume 1 <= D <= 10^9, 1 <= len(meetings) <= 10^5, and for every i with 0 <= i < len(meetings), len(meetings[i]) = 2 and 1 <= meetings[i][0] <= meetings[i][1] <= D. Write s_i = meetings[i][0] and e_i = meetings[i][1] for each such i. Let L = max_{0<=i<len(meetings)} (e_i - s_i + 1). -/
theorem spec_10
    (days : Aeneas.Std.I64) (meetings : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D) :
    ∃ r : Aeneas.Std.I64,
      Aegis.CountDays.count_days days meetings = ok r ∧
      r.val ≤ D - maxMeetingLength (meetingsVal meetings) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (days : Aeneas.Std.I64) (meetings : Aeneas.Std.Slice (alloc.vec.Vec Aeneas.Std.I64))
    (D : Int) (hdays : days.val = D)
    (hD_lb : 1 ≤ D) (hD_ub : D ≤ 10 ^ 9)
    (hlen_lb : 1 ≤ (meetingsVal meetings).length)
    (hlen_ub : (meetingsVal meetings).length ≤ 10 ^ 5)
    (hwf : ∀ iv ∈ meetingsVal meetings, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ D), ∃ r : Aeneas.Std.I64,
      Aegis.CountDays.count_days days meetings = ok r ∧
      r.val ≤ D - maxMeetingLength (meetingsVal meetings)) := by
  sorry

end AegisSpec.CountDays
