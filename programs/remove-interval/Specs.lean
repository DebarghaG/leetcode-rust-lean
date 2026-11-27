import Aegis.RemoveInterval.Code.Funs

/-!
# Specifications of `Aegis.RemoveInterval.remove_interval`

LeetCode problem `remove-interval`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.RemoveInterval

def vvals (v : alloc.vec.Vec Std.I64) : List Int := v.val.map (fun x => x.val)

def ivals (intervals : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  intervals.val.map vvals

def rvals (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : List (List Int) :=
  r.val.map vvals

def inAt (intervals : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Option (List Int) :=
  (intervals.val[i]?).map vvals

def resAt (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (j : Nat) : Option (List Int) :=
  (r.val[j]?).map vvals

def piece (s e a b : Int) : List (List Int) :=
  if b ≤ s ∨ e ≤ a then [[s, e]]
  else (if s < a then [[s, a]] else []) ++ (if b < e then [[b, e]] else [])

def expected (n : Nat) (s e : Nat → Int) (a b : Int) : List (List Int) :=
  (List.range n).flatMap (fun i => piece (s i) (e i) a b)

def endpoints (n : Nat) (s e : Nat → Int) (a b : Int) : List Int :=
  (List.range n).map s ++ (List.range n).map e ++ [a, b]

/-- Whenever remove_interval returns a result r, r is exactly the following concatenation, in increasing i for i = 0,1,...,n-1, of piece lists P_i. If b <= s_i or a >= e_i, then P_i is the single interval [s_i,e_i]. Otherwise P_i is the concatenation of [s_i,a] (included exactly when s_i < a) followed by [b,e_i] (included exactly when b < e_i). Empty P_i contributes nothing. Every interval [u,v) is represented by the two-element vector [u,v]. Thus the represented set is the input set with toBeRemoved removed; additionally, if a = b lies strictly inside some input interval [s_i,e_i), that interval is split at a into [s_i,a) and [a,e_i), matching the stated empty-removal case.
  Preconditions: Let n = len(intervals). intervals has n >= 1 elements; every intervals[i] has length exactly 2, and with s_i = intervals[i][0], e_i = intervals[i][1] we have -10^9 <= s_i < e_i <= 10^9 for 0 <= i < n, and e_i <= s_{i+1} for 0 <= i < n-1 (sorted disjoint half-open intervals). toBeRemoved has length exactly 2; with a = toBeRemoved[0], b = toBeRemoved[1], we have a <= b. -/
theorem spec_1
    (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b) :
    ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      rvals r = expected n s e a b := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b), ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      rvals r = expected n s e a b) := by
  sorry

/-- Under the preconditions, remove_interval returns a result r and does not fail: it does not panic, index out of bounds, overflow, or otherwise abort.
  Preconditions: Let n = len(intervals). intervals has n >= 1 elements; every intervals[i] has length exactly 2, and with s_i = intervals[i][0], e_i = intervals[i][1] we have -10^9 <= s_i < e_i <= 10^9 for 0 <= i < n, and e_i <= s_{i+1} for 0 <= i < n-1. toBeRemoved has length exactly 2; with a = toBeRemoved[0], b = toBeRemoved[1], we have a <= b. -/
theorem spec_2
    (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b) :
    ∃ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b), ∃ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r) := by
  sorry

/-- Whenever remove_interval returns a result r, for every j with 0 <= j < len(r), the vector r[j] has length exactly 2.
  Preconditions: Let n = len(intervals). intervals has n >= 1 elements; every intervals[i] has length exactly 2, and with s_i = intervals[i][0], e_i = intervals[i][1] we have -10^9 <= s_i < e_i <= 10^9 for 0 <= i < n, and e_i <= s_{i+1} for 0 <= i < n-1. toBeRemoved has length exactly 2; with a = toBeRemoved[0], b = toBeRemoved[1], we have a <= b. -/
theorem spec_3
    (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b) :
    ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ (j : Nat) (hj : j < r.val.length), (r.val[j]).val.length = 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b), ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ (j : Nat) (hj : j < r.val.length), (r.val[j]).val.length = 2) := by
  sorry

/-- Whenever remove_interval returns a result r, for every j with 0 <= j < len(r), r[j][0] < r[j][1]. Thus every returned interval [r[j][0], r[j][1]) is non-empty.
  Preconditions: Let n = len(intervals). intervals has n >= 1 elements; every intervals[i] has length exactly 2, and with s_i = intervals[i][0], e_i = intervals[i][1] we have -10^9 <= s_i < e_i <= 10^9 for 0 <= i < n, and e_i <= s_{i+1} for 0 <= i < n-1. toBeRemoved has length exactly 2; with a = toBeRemoved[0], b = toBeRemoved[1], we have a <= b. -/
theorem spec_4
    (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b) :
    ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ j, j < r.val.length → ∀ c d : Int, resAt r j = some [c, d] → c < d := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b), ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ j, j < r.val.length → ∀ c d : Int, resAt r j = some [c, d] → c < d) := by
  sorry

/-- Whenever remove_interval returns a result r, for every j with 0 <= j < len(r)-1, r[j][0] < r[j+1][0]. Thus the returned intervals are sorted by strictly increasing left endpoint.
  Preconditions: Let n = len(intervals). intervals has n >= 1 elements; every intervals[i] has length exactly 2, and with s_i = intervals[i][0], e_i = intervals[i][1] we have -10^9 <= s_i < e_i <= 10^9 for 0 <= i < n, and e_i <= s_{i+1} for 0 <= i < n-1. toBeRemoved has length exactly 2; with a = toBeRemoved[0], b = toBeRemoved[1], we have a <= b. -/
theorem spec_5
    (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b) :
    ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ j, j + 1 < r.val.length →
        ∀ c d c' d' : Int,
          resAt r j = some [c, d] → resAt r (j + 1) = some [c', d'] → c < c' := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b), ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ j, j + 1 < r.val.length →
        ∀ c d c' d' : Int,
          resAt r j = some [c, d] → resAt r (j + 1) = some [c', d'] → c < c') := by
  sorry

/-- Whenever remove_interval returns a result r, for every j with 0 <= j < len(r)-1, r[j][1] <= r[j+1][0]. Thus adjacent returned half-open intervals do not overlap.
  Preconditions: Let n = len(intervals). intervals has n >= 1 elements; every intervals[i] has length exactly 2, and with s_i = intervals[i][0], e_i = intervals[i][1] we have -10^9 <= s_i < e_i <= 10^9 for 0 <= i < n, and e_i <= s_{i+1} for 0 <= i < n-1. toBeRemoved has length exactly 2; with a = toBeRemoved[0], b = toBeRemoved[1], we have a <= b. -/
theorem spec_6
    (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b) :
    ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ j, j + 1 < r.val.length →
        ∀ c d c' d' : Int,
          resAt r j = some [c, d] → resAt r (j + 1) = some [c', d'] → d ≤ c' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b), ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ j, j + 1 < r.val.length →
        ∀ c d c' d' : Int,
          resAt r j = some [c, d] → resAt r (j + 1) = some [c', d'] → d ≤ c') := by
  sorry

/-- Whenever remove_interval returns a result r, every real number represented by r is represented by an input interval and is not in toBeRemoved. Explicitly, for every j with 0 <= j < len(r) and every real x with r[j][0] <= x < r[j][1], there exists i with 0 <= i < n and s_i <= x < e_i, and also not (a <= x < b).
  Preconditions: Let n = len(intervals). intervals has n >= 1 elements; every intervals[i] has length exactly 2, and with s_i = intervals[i][0], e_i = intervals[i][1] we have -10^9 <= s_i < e_i <= 10^9 for 0 <= i < n, and e_i <= s_{i+1} for 0 <= i < n-1. toBeRemoved has length exactly 2; with a = toBeRemoved[0], b = toBeRemoved[1], we have a <= b. -/
theorem spec_7
    (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b) :
    ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ j, j < r.val.length → ∀ c d : Int, resAt r j = some [c, d] →
        ∀ x : Int, c ≤ x → x < d →
          (∃ i, i < n ∧ s i ≤ x ∧ x < e i) ∧ ¬ (a ≤ x ∧ x < b) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b), ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ j, j < r.val.length → ∀ c d : Int, resAt r j = some [c, d] →
        ∀ x : Int, c ≤ x → x < d →
          (∃ i, i < n ∧ s i ≤ x ∧ x < e i) ∧ ¬ (a ≤ x ∧ x < b)) := by
  sorry

/-- Whenever remove_interval returns a result r, every real number that is in some input interval but not in toBeRemoved is represented by r. Explicitly, for every real x such that (exists i with 0 <= i < n and s_i <= x < e_i) and not (a <= x < b), there exists j with 0 <= j < len(r) and r[j][0] <= x < r[j][1].
  Preconditions: Let n = len(intervals). intervals has n >= 1 elements; every intervals[i] has length exactly 2, and with s_i = intervals[i][0], e_i = intervals[i][1] we have -10^9 <= s_i < e_i <= 10^9 for 0 <= i < n, and e_i <= s_{i+1} for 0 <= i < n-1. toBeRemoved has length exactly 2; with a = toBeRemoved[0], b = toBeRemoved[1], we have a <= b. -/
theorem spec_8
    (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b) :
    ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ x : Int, (∃ i, i < n ∧ s i ≤ x ∧ x < e i) → ¬ (a ≤ x ∧ x < b) →
        ∃ j, j < r.val.length ∧ ∃ c d : Int, resAt r j = some [c, d] ∧ c ≤ x ∧ x < d := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b), ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ x : Int, (∃ i, i < n ∧ s i ≤ x ∧ x < e i) → ¬ (a ≤ x ∧ x < b) →
        ∃ j, j < r.val.length ∧ ∃ c d : Int, resAt r j = some [c, d] ∧ c ≤ x ∧ x < d) := by
  sorry

/-- Whenever remove_interval returns a result r, every coordinate of every returned interval lies within the envelope of the input intervals. Explicitly, for every j with 0 <= j < len(r), intervals[0][0] <= r[j][0] and r[j][1] <= intervals[n-1][1].
  Preconditions: Let n = len(intervals). intervals has n >= 1 elements; every intervals[i] has length exactly 2, and with s_i = intervals[i][0], e_i = intervals[i][1] we have -10^9 <= s_i < e_i <= 10^9 for 0 <= i < n, and e_i <= s_{i+1} for 0 <= i < n-1. toBeRemoved has length exactly 2; with a = toBeRemoved[0], b = toBeRemoved[1], we have a <= b. -/
theorem spec_9
    (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b) :
    ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ j, j < r.val.length → ∀ c d : Int, resAt r j = some [c, d] →
        s 0 ≤ c ∧ d ≤ e (n - 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b), ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ j, j < r.val.length → ∀ c d : Int, resAt r j = some [c, d] →
        s 0 ≤ c ∧ d ≤ e (n - 1)) := by
  sorry

/-- Whenever remove_interval returns a result r, len(r) <= 2 * len(intervals).
  Preconditions: Let n = len(intervals). intervals has n >= 1 elements; every intervals[i] has length exactly 2, and with s_i = intervals[i][0], e_i = intervals[i][1] we have -10^9 <= s_i < e_i <= 10^9 for 0 <= i < n, and e_i <= s_{i+1} for 0 <= i < n-1. toBeRemoved has length exactly 2; with a = toBeRemoved[0], b = toBeRemoved[1], we have a <= b. -/
theorem spec_10
    (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b) :
    ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      r.val.length ≤ 2 * n := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b), ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      r.val.length ≤ 2 * n) := by
  sorry

/-- Whenever remove_interval returns a result r, every endpoint of every returned interval is either an original input endpoint or an endpoint of toBeRemoved. Explicitly, for every j with 0 <= j < len(r), both numbers r[j][0] and r[j][1] belong to the finite set {s_i | 0 <= i < n} union {e_i | 0 <= i < n} union {a,b}.
  Preconditions: Let n = len(intervals). intervals has n >= 1 elements; every intervals[i] has length exactly 2, and with s_i = intervals[i][0], e_i = intervals[i][1] we have -10^9 <= s_i < e_i <= 10^9 for 0 <= i < n, and e_i <= s_{i+1} for 0 <= i < n-1. toBeRemoved has length exactly 2; with a = toBeRemoved[0], b = toBeRemoved[1], we have a <= b. -/
theorem spec_11
    (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b) :
    ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ j, j < r.val.length → ∀ c d : Int, resAt r j = some [c, d] →
        c ∈ endpoints n s e a b ∧ d ∈ endpoints n s e a b := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b), ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ j, j < r.val.length → ∀ c d : Int, resAt r j = some [c, d] →
        c ∈ endpoints n s e a b ∧ d ∈ endpoints n s e a b) := by
  sorry

/-- Whenever remove_interval returns a result r, every input interval lying entirely before or entirely after the removed interval is returned unchanged. Explicitly, for every i with 0 <= i < n such that e_i <= a or s_i >= b, there exists j with 0 <= j < len(r) such that r[j][0] = s_i and r[j][1] = e_i.
  Preconditions: Let n = len(intervals). intervals has n >= 1 elements; every intervals[i] has length exactly 2, and with s_i = intervals[i][0], e_i = intervals[i][1] we have -10^9 <= s_i < e_i <= 10^9 for 0 <= i < n, and e_i <= s_{i+1} for 0 <= i < n-1. toBeRemoved has length exactly 2; with a = toBeRemoved[0], b = toBeRemoved[1], we have a <= b. -/
theorem spec_12
    (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b) :
    ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ i, i < n → e i ≤ a ∨ b ≤ s i →
        ∃ j, j < r.val.length ∧ resAt r j = some [s i, e i] := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b), ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ i, i < n → e i ≤ a ∨ b ≤ s i →
        ∃ j, j < r.val.length ∧ resAt r j = some [s i, e i]) := by
  sorry

/-- Whenever remove_interval returns a result r, if a <= intervals[0][0] and intervals[n-1][1] <= b, then the result is empty: len(r) = 0.
  Preconditions: Let n = len(intervals). intervals has n >= 1 elements; every intervals[i] has length exactly 2, and with s_i = intervals[i][0], e_i = intervals[i][1] we have -10^9 <= s_i < e_i <= 10^9 for 0 <= i < n, and e_i <= s_{i+1} for 0 <= i < n-1. toBeRemoved has length exactly 2; with a = toBeRemoved[0], b = toBeRemoved[1], we have a <= b. -/
theorem spec_13
    (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b) :
    ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      a ≤ s 0 → e (n - 1) ≤ b → r.val.length = 0 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b), ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      a ≤ s 0 → e (n - 1) ≤ b → r.val.length = 0) := by
  sorry

/-- Whenever remove_interval returns a result r, if a < b and for every i with 0 <= i < n we have b <= s_i or a >= e_i, then r is exactly the input list: len(r) = n and for every i with 0 <= i < n, r[i][0] = s_i and r[i][1] = e_i.
  Preconditions: Let n = len(intervals). intervals has n >= 1 elements; every intervals[i] has length exactly 2, and with s_i = intervals[i][0], e_i = intervals[i][1] we have -10^9 <= s_i < e_i <= 10^9 for 0 <= i < n, and e_i <= s_{i+1} for 0 <= i < n-1. toBeRemoved has length exactly 2; with a = toBeRemoved[0], b = toBeRemoved[1], we have a <= b. -/
theorem spec_14
    (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b) :
    ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      a < b → (∀ i, i < n → b ≤ s i ∨ e i ≤ a) →
        r.val.length = n ∧ ∀ i, i < n → resAt r i = some [s i, e i] := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b), ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      a < b → (∀ i, i < n → b ≤ s i ∨ e i ≤ a) →
        r.val.length = n ∧ ∀ i, i < n → resAt r i = some [s i, e i]) := by
  sorry

/-- Whenever remove_interval returns a result r, every returned interval has one of three origins. For every j with 0 <= j < len(r), writing c = r[j][0] and d = r[j][1], there exists i with 0 <= i < n such that at least one of the following holds: (i) c = s_i, d = e_i, and (b <= s_i or a >= e_i); (ii) c = s_i, d = a, and s_i < a < e_i; (iii) c = b, d = e_i, and s_i < b < e_i.
  Preconditions: Let n = len(intervals). intervals has n >= 1 elements; every intervals[i] has length exactly 2, and with s_i = intervals[i][0], e_i = intervals[i][1] we have -10^9 <= s_i < e_i <= 10^9 for 0 <= i < n, and e_i <= s_{i+1} for 0 <= i < n-1. toBeRemoved has length exactly 2; with a = toBeRemoved[0], b = toBeRemoved[1], we have a <= b. -/
theorem spec_15
    (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b) :
    ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ j, j < r.val.length → ∀ c d : Int, resAt r j = some [c, d] →
        ∃ i, i < n ∧
          ((c = s i ∧ d = e i ∧ (b ≤ s i ∨ e i ≤ a)) ∨
           (c = s i ∧ d = a ∧ s i < a ∧ a < e i) ∨
           (c = b ∧ d = e i ∧ s i < b ∧ b < e i)) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (toBeRemoved : Slice Std.I64)
    (n : Nat) (s e : Nat → Int) (a b : Int)
    (hn : n = intervals.val.length)
    (hn1 : 1 ≤ n)
    (hiv : ∀ i, i < n → inAt intervals i = some [s i, e i])
    (hrange : ∀ i, i < n → -1000000000 ≤ s i ∧ s i < e i ∧ e i ≤ 1000000000)
    (hsrt : ∀ i, i + 1 < n → e i ≤ s (i + 1))
    (hrm : toBeRemoved.val.map (fun x => x.val) = [a, b])
    (hab : a ≤ b), ∀ r, Aegis.RemoveInterval.remove_interval intervals toBeRemoved = ok r →
      ∀ j, j < r.val.length → ∀ c d : Int, resAt r j = some [c, d] →
        ∃ i, i < n ∧
          ((c = s i ∧ d = e i ∧ (b ≤ s i ∨ e i ≤ a)) ∨
           (c = s i ∧ d = a ∧ s i < a ∧ a < e i) ∨
           (c = b ∧ d = e i ∧ s i < b ∧ b < e i))) := by
  sorry

end AegisSpec.RemoveInterval
