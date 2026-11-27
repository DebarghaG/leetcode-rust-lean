import Aegis.MaxFreeTime.Code.Funs

/-!
# Specifications of `Aegis.MaxFreeTime.max_free_time`

LeetCode problem `reschedule-meetings-for-maximum-free-time-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxFreeTime

def idx (s : Slice I64) (i : Nat) : Int := (s.val[i]!).val

def dur (startTime endTime : Slice I64) (i : Nat) : Int :=
  idx endTime i - idx startTime i

def gap (eventTime : I64) (startTime endTime : Slice I64) (n : Nat) (j : Nat) : Int :=
  if j = 0 then idx startTime 0
  else if j = n then eventTime.val - idx endTime (n - 1)
  else idx startTime j - idx endTime (j - 1)

def totalDur (startTime endTime : Slice I64) (n : Nat) : Int :=
  ((List.range n).map (fun i => dur startTime endTime i)).sum

def supRange (n : Nat) (f : Nat → Int) : Int :=
  ((List.range n).map f).foldr max (f 0)

def CanMove (eventTime : I64) (startTime endTime : Slice I64) (n i : Nat) : Prop :=
  ∃ j, j ≤ n ∧ j ≠ i ∧ j ≠ i + 1 ∧ dur startTime endTime i ≤ gap eventTime startTime endTime n j

def canMoveB (eventTime : I64) (startTime endTime : Slice I64) (n i : Nat) : Bool :=
  ((List.range (n + 1)).any fun j =>
    (j != i) && (j != i + 1) && decide (dur startTime endTime i ≤ gap eventTime startTime endTime n j))

def closedForm (eventTime : I64) (startTime endTime : Slice I64) (n : Nat) : Int :=
  (((List.range n).filter (canMoveB eventTime startTime endTime n)).map
      (fun i => gap eventTime startTime endTime n i + dur startTime endTime i
        + gap eventTime startTime endTime n (i + 1))).foldr max
    (supRange n (fun i => gap eventTime startTime endTime n i
      + gap eventTime startTime endTime n (i + 1)))

def NonOverlap (p q : Int × Int) : Prop := p.2 ≤ q.1 ∨ q.2 ≤ p.1

def meetings (startTime endTime : Slice I64) (n : Nat) : List (Int × Int) :=
  (List.range n).map (fun i => (idx startTime i, idx endTime i))

def reschedule (startTime endTime : Slice I64) (n k : Nat) (x : Int) : List (Int × Int) :=
  (List.range n).map fun i =>
    if i = k then (x, x + dur startTime endTime i) else (idx startTime i, idx endTime i)

def IsReschedule (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (ivs : List (Int × Int)) : Prop :=
  ivs = meetings startTime endTime n ∨
    ∃ (k : Nat) (x : Int), k < n ∧ 0 ≤ x ∧ x + dur startTime endTime k ≤ eventTime.val ∧
      ivs = reschedule startTime endTime n k x

def Feasible (eventTime : I64) (ivs : List (Int × Int)) : Prop :=
  (∀ p ∈ ivs, 0 ≤ p.1 ∧ p.2 ≤ eventTime.val) ∧ List.Pairwise NonOverlap ivs

def FeasibleReschedule (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (ivs : List (Int × Int)) : Prop :=
  IsReschedule eventTime startTime endTime n ivs ∧ Feasible eventTime ivs

def sortByStart (ivs : List (Int × Int)) : List (Int × Int) :=
  ivs.insertionSort (fun p q => p.1 ≤ q.1)

def freeTimesFrom (eventTime : Int) (prev : Int) : List (Int × Int) → List Int
  | [] => [eventTime - prev]
  | p :: rest => (p.1 - prev) :: freeTimesFrom eventTime p.2 rest

def freeTimes (eventTime : Int) (ivs : List (Int × Int)) : List Int :=
  freeTimesFrom eventTime 0 (sortByStart ivs)

def longestFreeTime (eventTime : Int) (ivs : List (Int × Int)) : Int :=
  (freeTimes eventTime ivs).foldr max 0

/-- Consider every feasible reschedule of at most one meeting: choose either no meeting, or an index k with 0 <= k < n and an integer x such that 0 <= x and x + (endTime[k]-startTime[k]) <= eventTime, and replace only meeting k by [x, x + (endTime[k]-startTime[k])], leaving all other meetings [startTime[i], endTime[i]] unchanged. The reschedule is feasible only if all resulting meetings lie in [0,eventTime] and any two resulting meetings are non-overlapping, meaning for intervals [a,b] and [c,d] either b <= c or d <= a. For any feasible resulting set, sort its meetings by start time; define its longest free time as the maximum of: the first start time, nextStart - previousEnd for each consecutive pair in sorted order, and eventTime - the last end time. The function returns a result r, and r is exactly the maximum of this longest free time over all feasible reschedules, including changing no meeting.
  Preconditions: Let n = len(startTime) = len(endTime). Assume 1 <= eventTime <= 10^9, 2 <= n <= 10^5, for every i with 0 <= i < n we have 0 <= startTime[i] < endTime[i] <= eventTime, and for every i with 0 <= i < n-1 we have endTime[i] <= startTime[i+1]. -/
theorem spec_1
    (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)) :
    ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      (∀ ivs, FeasibleReschedule eventTime startTime endTime n ivs →
        longestFreeTime eventTime.val ivs ≤ r.val) ∧
      (∃ ivs, FeasibleReschedule eventTime startTime endTime n ivs ∧
        longestFreeTime eventTime.val ivs = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)), ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      (∀ ivs, FeasibleReschedule eventTime startTime endTime n ivs →
        longestFreeTime eventTime.val ivs ≤ r.val) ∧
      (∃ ivs, FeasibleReschedule eventTime startTime endTime n ivs ∧
        longestFreeTime eventTime.val ivs = r.val)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail by overflow, out-of-bounds indexing, or panic.
  Preconditions: Let n = len(startTime) = len(endTime). Assume 1 <= eventTime <= 10^9, 2 <= n <= 10^5, for every i with 0 <= i < n we have 0 <= startTime[i] < endTime[i] <= eventTime, and for every i with 0 <= i < n-1 we have endTime[i] <= startTime[i+1]. -/
theorem spec_2
    (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)) :
    ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)), ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r) := by
  sorry

/-- For every input satisfying the preconditions, the returned value r satisfies r >= 0.
  Preconditions: Let n = len(startTime) = len(endTime). Assume 1 <= eventTime <= 10^9, 2 <= n <= 10^5, for every i with 0 <= i < n we have 0 <= startTime[i] < endTime[i] <= eventTime, and for every i with 0 <= i < n-1 we have endTime[i] <= startTime[i+1]. -/
theorem spec_3
    (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)) :
    ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)), ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- For every input satisfying the preconditions, let d_i = endTime[i]-startTime[i] for 0 <= i < n. Then r <= eventTime - (sum_{i=0}^{n-1} d_i).
  Preconditions: Let n = len(startTime) = len(endTime). Assume 1 <= eventTime <= 10^9, 2 <= n <= 10^5, for every i with 0 <= i < n we have 0 <= startTime[i] < endTime[i] <= eventTime, and for every i with 0 <= i < n-1 we have endTime[i] <= startTime[i+1]. -/
theorem spec_4
    (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)) :
    ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      r.val ≤ eventTime.val - totalDur startTime endTime n := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)), ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      r.val ≤ eventTime.val - totalDur startTime endTime n) := by
  sorry

/-- For every input satisfying the preconditions and every i with 0 <= i < n, define L_i = startTime[0] if i=0, otherwise startTime[i]-endTime[i-1], and R_i = eventTime-endTime[n-1] if i=n-1, otherwise startTime[i+1]-endTime[i]. Then r >= L_i + R_i.
  Preconditions: Let n = len(startTime) = len(endTime). Assume 1 <= eventTime <= 10^9, 2 <= n <= 10^5, for every i with 0 <= i < n we have 0 <= startTime[i] < endTime[i] <= eventTime, and for every i with 0 <= i < n-1 we have endTime[i] <= startTime[i+1]. -/
theorem spec_5
    (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)) :
    ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      ∀ i, i < n →
        gap eventTime startTime endTime n i + gap eventTime startTime endTime n (i + 1) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)), ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      ∀ i, i < n →
        gap eventTime startTime endTime n i + gap eventTime startTime endTime n (i + 1) ≤ r.val) := by
  sorry

/-- For every input satisfying the preconditions, define g_0 = startTime[0], g_j = startTime[j]-endTime[j-1] for 1 <= j <= n-1, and g_n = eventTime-endTime[n-1]; also d_i = endTime[i]-startTime[i]. For every i with 0 <= i < n, if there exists j with 0 <= j <= n, j != i and j != i+1, and g_j >= d_i, then r >= g_i + d_i + g_{i+1}.
  Preconditions: Let n = len(startTime) = len(endTime). Assume 1 <= eventTime <= 10^9, 2 <= n <= 10^5, for every i with 0 <= i < n we have 0 <= startTime[i] < endTime[i] <= eventTime, and for every i with 0 <= i < n-1 we have endTime[i] <= startTime[i+1]. -/
theorem spec_6
    (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)) :
    ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      ∀ i, i < n → CanMove eventTime startTime endTime n i →
        gap eventTime startTime endTime n i + dur startTime endTime i
          + gap eventTime startTime endTime n (i + 1) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)), ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      ∀ i, i < n → CanMove eventTime startTime endTime n i →
        gap eventTime startTime endTime n i + dur startTime endTime i
          + gap eventTime startTime endTime n (i + 1) ≤ r.val) := by
  sorry

/-- For every input satisfying the preconditions, define g_0 = startTime[0], g_j = startTime[j]-endTime[j-1] for 1 <= j <= n-1, and g_n = eventTime-endTime[n-1]; also d_i = endTime[i]-startTime[i]. Then r <= max_{0 <= i < n} (g_i + d_i + g_{i+1}).
  Preconditions: Let n = len(startTime) = len(endTime). Assume 1 <= eventTime <= 10^9, 2 <= n <= 10^5, for every i with 0 <= i < n we have 0 <= startTime[i] < endTime[i] <= eventTime, and for every i with 0 <= i < n-1 we have endTime[i] <= startTime[i+1]. -/
theorem spec_7
    (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)) :
    ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      r.val ≤ supRange n (fun i => gap eventTime startTime endTime n i
        + dur startTime endTime i + gap eventTime startTime endTime n (i + 1)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)), ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      r.val ≤ supRange n (fun i => gap eventTime startTime endTime n i
        + dur startTime endTime i + gap eventTime startTime endTime n (i + 1))) := by
  sorry

/-- For every input satisfying the preconditions, let d_i = endTime[i]-startTime[i]. Then r = 0 if and only if sum_{i=0}^{n-1} d_i = eventTime.
  Preconditions: Let n = len(startTime) = len(endTime). Assume 1 <= eventTime <= 10^9, 2 <= n <= 10^5, for every i with 0 <= i < n we have 0 <= startTime[i] < endTime[i] <= eventTime, and for every i with 0 <= i < n-1 we have endTime[i] <= startTime[i+1]. -/
theorem spec_8
    (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)) :
    ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      (r.val = 0 ↔ totalDur startTime endTime n = eventTime.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)), ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      (r.val = 0 ↔ totalDur startTime endTime n = eventTime.val)) := by
  sorry

/-- For every input satisfying the preconditions, define g_0 = startTime[0], g_j = startTime[j]-endTime[j-1] for 1 <= j <= n-1, and g_n = eventTime-endTime[n-1]; also d_i = endTime[i]-startTime[i]. If for every i with 0 <= i < n and every j with 0 <= j <= n such that j != i and j != i+1 we have g_j < d_i, then r = max_{0 <= i < n} (g_i + g_{i+1}).
  Preconditions: Let n = len(startTime) = len(endTime). Assume 1 <= eventTime <= 10^9, 2 <= n <= 10^5, for every i with 0 <= i < n we have 0 <= startTime[i] < endTime[i] <= eventTime, and for every i with 0 <= i < n-1 we have endTime[i] <= startTime[i+1]. -/
theorem spec_9
    (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)) :
    ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      ((∀ i, i < n → ∀ j, j ≤ n → j ≠ i → j ≠ i + 1 →
        gap eventTime startTime endTime n j < dur startTime endTime i) →
      r.val = supRange n (fun i => gap eventTime startTime endTime n i
        + gap eventTime startTime endTime n (i + 1))) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)), ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      ((∀ i, i < n → ∀ j, j ≤ n → j ≠ i → j ≠ i + 1 →
        gap eventTime startTime endTime n j < dur startTime endTime i) →
      r.val = supRange n (fun i => gap eventTime startTime endTime n i
        + gap eventTime startTime endTime n (i + 1)))) := by
  sorry

/-- For every input satisfying the preconditions, define g_0 = startTime[0], g_j = startTime[j]-endTime[j-1] for 1 <= j <= n-1, and g_n = eventTime-endTime[n-1]; also d_i = endTime[i]-startTime[i]. There exists an index i with 0 <= i < n such that either (a) r = g_i + g_{i+1}, or (b) r = g_i + d_i + g_{i+1} and there exists j with 0 <= j <= n, j != i and j != i+1, and g_j >= d_i.
  Preconditions: Let n = len(startTime) = len(endTime). Assume 1 <= eventTime <= 10^9, 2 <= n <= 10^5, for every i with 0 <= i < n we have 0 <= startTime[i] < endTime[i] <= eventTime, and for every i with 0 <= i < n-1 we have endTime[i] <= startTime[i+1]. -/
theorem spec_10
    (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)) :
    ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      ∃ i, i < n ∧
        (r.val = gap eventTime startTime endTime n i
            + gap eventTime startTime endTime n (i + 1) ∨
          (r.val = gap eventTime startTime endTime n i + dur startTime endTime i
              + gap eventTime startTime endTime n (i + 1) ∧
            CanMove eventTime startTime endTime n i)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)), ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      ∃ i, i < n ∧
        (r.val = gap eventTime startTime endTime n i
            + gap eventTime startTime endTime n (i + 1) ∨
          (r.val = gap eventTime startTime endTime n i + dur startTime endTime i
              + gap eventTime startTime endTime n (i + 1) ∧
            CanMove eventTime startTime endTime n i))) := by
  sorry

/-- For every input satisfying the preconditions, define the reflected input by start'_i = eventTime - endTime[n-1-i] and end'_i = eventTime - startTime[n-1-i] for 0 <= i < n. Let r be the value returned for (eventTime, startTime, endTime) and let r' be the value returned for (eventTime, start', end'). Then r = r'.
  Preconditions: Let n = len(startTime) = len(endTime). Assume 1 <= eventTime <= 10^9, 2 <= n <= 10^5, for every i with 0 <= i < n we have 0 <= startTime[i] < endTime[i] <= eventTime, and for every i with 0 <= i < n-1 we have endTime[i] <= startTime[i+1]. -/
theorem spec_11
    (eventTime : I64) (startTime endTime startTime' endTime' : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1))
    (hlen_s' : startTime'.val.length = n) (hlen_e' : endTime'.val.length = n)
    (hrefl_s : ∀ i, i < n → idx startTime' i = eventTime.val - idx endTime (n - 1 - i))
    (hrefl_e : ∀ i, i < n → idx endTime' i = eventTime.val - idx startTime (n - 1 - i)) :
    ∃ r r', Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      Aegis.MaxFreeTime.max_free_time eventTime startTime' endTime' = ok r' ∧
      r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (eventTime : I64) (startTime endTime startTime' endTime' : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1))
    (hlen_s' : startTime'.val.length = n) (hlen_e' : endTime'.val.length = n)
    (hrefl_s : ∀ i, i < n → idx startTime' i = eventTime.val - idx endTime (n - 1 - i))
    (hrefl_e : ∀ i, i < n → idx endTime' i = eventTime.val - idx startTime (n - 1 - i)), ∃ r r', Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      Aegis.MaxFreeTime.max_free_time eventTime startTime' endTime' = ok r' ∧
      r.val = r'.val) := by
  sorry

/-- For every input satisfying the preconditions and every integer eventTime' with eventTime <= eventTime' <= 10^9, let r be the value returned for (eventTime, startTime, endTime) and let r' be the value returned for (eventTime', startTime, endTime). Then r <= r'.
  Preconditions: Let n = len(startTime) = len(endTime). Assume 1 <= eventTime <= 10^9, 2 <= n <= 10^5, for every i with 0 <= i < n we have 0 <= startTime[i] < endTime[i] <= eventTime, and for every i with 0 <= i < n-1 we have endTime[i] <= startTime[i+1]. -/
theorem spec_12
    (eventTime eventTime' : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1))
    (het'_lo : eventTime.val ≤ eventTime'.val) (het'_hi : eventTime'.val ≤ 10 ^ 9) :
    ∃ r r', Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      Aegis.MaxFreeTime.max_free_time eventTime' startTime endTime = ok r' ∧
      r.val ≤ r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (eventTime eventTime' : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1))
    (het'_lo : eventTime.val ≤ eventTime'.val) (het'_hi : eventTime'.val ≤ 10 ^ 9), ∃ r r', Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      Aegis.MaxFreeTime.max_free_time eventTime' startTime endTime = ok r' ∧
      r.val ≤ r'.val) := by
  sorry

/-- For every input satisfying the preconditions, define g_0 = startTime[0], g_j = startTime[j]-endTime[j-1] for 1 <= j <= n-1, g_n = eventTime-endTime[n-1], and d_i = endTime[i]-startTime[i]. Let E = { i | 0 <= i < n and there exists j with 0 <= j <= n, j != i, j != i+1, and g_j >= d_i }. Then r = max( max_{0 <= i < n} (g_i + g_{i+1}), max_{i in E} (g_i + d_i + g_{i+1}) ), with the second maximum omitted when E is empty. This is the exact closed-form value of the optimum.
  Preconditions: Let n = len(startTime) = len(endTime). Assume 1 <= eventTime <= 10^9, 2 <= n <= 10^5, for every i with 0 <= i < n we have 0 <= startTime[i] < endTime[i] <= eventTime, and for every i with 0 <= i < n-1 we have endTime[i] <= startTime[i+1]. -/
theorem spec_13
    (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)) :
    ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      r.val = closedForm eventTime startTime endTime n := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (eventTime : I64) (startTime endTime : Slice I64) (n : Nat)
    (hlen_s : startTime.val.length = n) (hlen_e : endTime.val.length = n)
    (het_lo : 1 ≤ eventTime.val) (het_hi : eventTime.val ≤ 10 ^ 9)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 10 ^ 5)
    (hiv : ∀ i, i < n → 0 ≤ idx startTime i ∧ idx startTime i < idx endTime i ∧
      idx endTime i ≤ eventTime.val)
    (hsep : ∀ i, i + 1 < n → idx endTime i ≤ idx startTime (i + 1)), ∃ r, Aegis.MaxFreeTime.max_free_time eventTime startTime endTime = ok r ∧
      r.val = closedForm eventTime startTime endTime n) := by
  sorry

end AegisSpec.MaxFreeTime
