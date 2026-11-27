import Aegis.Insert.Code.Funs
import Mathlib.Data.Real.Basic

/-!
# Specifications of `Aegis.Insert.insert`

LeetCode problem `insert-interval`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aeneas.Std.Result

namespace AegisSpec.Insert

def lower (l : List I64) : ℤ :=
  match l with
  | x :: _ => x.val
  | [] => 0

def upper (l : List I64) : ℤ :=
  match l with
  | _ :: y :: _ => y.val
  | _ => 0

def WellFormed (l : List I64) : Prop :=
  l.length = 2 ∧ 0 ≤ lower l ∧ lower l ≤ upper l ∧ upper l ≤ 100000

def memInterval (l : List I64) (x : ℝ) : Prop :=
  (lower l : ℝ) ≤ x ∧ x ≤ (upper l : ℝ)

def InInputs (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64) (x : ℝ) : Prop :=
  memInterval newInterval.val x ∨
    ∃ i, ∃ (hi : i < intervals.val.length), memInterval (intervals.val[i]'hi).val x

def InOutput (r : alloc.vec.Vec (alloc.vec.Vec I64)) (x : ℝ) : Prop :=
  ∃ j, ∃ (hj : j < r.val.length), memInterval (r.val[j]'hj).val x

def IsEndpoint (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64) (a : ℤ) : Prop :=
  a = lower newInterval.val ∨ a = upper newInterval.val ∨
    ∃ i, ∃ (hi : i < intervals.val.length),
      a = lower (intervals.val[i]'hi).val ∨ a = upper (intervals.val[i]'hi).val

structure Pre (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64) : Prop where

  len_le : intervals.val.length ≤ 10000

  newInterval_wellFormed : WellFormed newInterval.val

  input_wellFormed : ∀ i, ∀ (_ : i < intervals.val.length), WellFormed (intervals.val[i]).val

  sorted : ∀ i, ∀ (_ : i + 1 < intervals.val.length),
    upper (intervals.val[i]'(by omega)).val < lower (intervals.val[i + 1]'(by omega)).val

def intersectCount (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64) : ℕ :=
  (Finset.univ.filter (fun i : Fin intervals.val.length =>
    lower (intervals.val[i.val]'i.isLt).val ≤ upper newInterval.val ∧
      lower newInterval.val ≤ upper (intervals.val[i.val]'i.isLt).val)).card

/-- Let n = len(intervals), s = newInterval[0], e = newInterval[1], and let U = {x ∈ ℝ | (s ≤ x ≤ e) or (there exists i with 0 ≤ i < n and intervals[i][0] ≤ x ≤ intervals[i][1])}. The function returns a result r (it does not fail) such that, writing m = len(r) and r[j] = [a_j, b_j] for each 0 ≤ j < m, the following hold: m ≥ 1; every r[j] has length 2 and a_j ≤ b_j; for every 0 ≤ j < m-1, b_j < a_{j+1}; and for every real x, x ∈ U iff there exists j with 0 ≤ j < m and a_j ≤ x ≤ b_j. Thus r is exactly the sorted list of the connected components of U.
  Preconditions: len(intervals) <= 10000; len(newInterval) = 2; 0 <= newInterval[0] <= newInterval[1] <= 100000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 100000; and for every i with 0 <= i < len(intervals)-1, intervals[i][1] < intervals[i+1][0]. -/
theorem spec_1 (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval) :
    ∃ r, Aegis.Insert.insert intervals newInterval = ok r ∧
      1 ≤ r.val.length ∧
      (∀ j, ∀ (hj : j < r.val.length),
        (r.val[j]'hj).val.length = 2 ∧ lower (r.val[j]'hj).val ≤ upper (r.val[j]'hj).val) ∧
      (∀ j, ∀ (hj : j + 1 < r.val.length),
        upper (r.val[j]'(by omega)).val < lower (r.val[j + 1]'(by omega)).val) ∧
      (∀ x : ℝ, InInputs intervals newInterval x ↔ InOutput r x) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval), ∃ r, Aegis.Insert.insert intervals newInterval = ok r ∧
      1 ≤ r.val.length ∧
      (∀ j, ∀ (hj : j < r.val.length),
        (r.val[j]'hj).val.length = 2 ∧ lower (r.val[j]'hj).val ≤ upper (r.val[j]'hj).val) ∧
      (∀ j, ∀ (hj : j + 1 < r.val.length),
        upper (r.val[j]'(by omega)).val < lower (r.val[j + 1]'(by omega)).val) ∧
      (∀ x : ℝ, InInputs intervals newInterval x ↔ InOutput r x)) := by
  sorry

/-- The function returns a result r (i.e., it does not fail, overflow, panic, or go out of bounds) for every input satisfying the preconditions.
  Preconditions: len(intervals) <= 10000; len(newInterval) = 2; 0 <= newInterval[0] <= newInterval[1] <= 100000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 100000; and for every i with 0 <= i < len(intervals)-1, intervals[i][1] < intervals[i+1][0]. -/
theorem spec_2 (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval) :
    ∃ r, Aegis.Insert.insert intervals newInterval = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval), ∃ r, Aegis.Insert.insert intervals newInterval = ok r) := by
  sorry

/-- Whenever the function returns a result r, every element of r is a pair: for every j with 0 ≤ j < len(r), len(r[j]) = 2.
  Preconditions: len(intervals) <= 10000; len(newInterval) = 2; 0 <= newInterval[0] <= newInterval[1] <= 100000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 100000; and for every i with 0 <= i < len(intervals)-1, intervals[i][1] < intervals[i+1][0]. -/
theorem spec_3 (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval) :
    ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      ∀ j, ∀ (hj : j < r.val.length), (r.val[j]'hj).val.length = 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval), ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      ∀ j, ∀ (hj : j < r.val.length), (r.val[j]'hj).val.length = 2) := by
  sorry

/-- Whenever the function returns a result r, every element of r denotes a nonempty closed interval: for every j with 0 ≤ j < len(r), writing r[j] = [a_j, b_j], we have a_j ≤ b_j.
  Preconditions: len(intervals) <= 10000; len(newInterval) = 2; 0 <= newInterval[0] <= newInterval[1] <= 100000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 100000; and for every i with 0 <= i < len(intervals)-1, intervals[i][1] < intervals[i+1][0]. -/
theorem spec_4 (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval) :
    ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      ∀ j, ∀ (hj : j < r.val.length), lower (r.val[j]'hj).val ≤ upper (r.val[j]'hj).val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval), ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      ∀ j, ∀ (hj : j < r.val.length), lower (r.val[j]'hj).val ≤ upper (r.val[j]'hj).val) := by
  sorry

/-- Whenever the function returns a result r, every endpoint of every output interval lies in the allowed numeric range: for every j with 0 ≤ j < len(r), writing r[j] = [a_j, b_j], we have 0 ≤ a_j ≤ b_j ≤ 100000.
  Preconditions: len(intervals) <= 10000; len(newInterval) = 2; 0 <= newInterval[0] <= newInterval[1] <= 100000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 100000; and for every i with 0 <= i < len(intervals)-1, intervals[i][1] < intervals[i+1][0]. -/
theorem spec_5 (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval) :
    ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      ∀ j, ∀ (hj : j < r.val.length),
        0 ≤ lower (r.val[j]'hj).val ∧ lower (r.val[j]'hj).val ≤ upper (r.val[j]'hj).val ∧
          upper (r.val[j]'hj).val ≤ 100000 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval), ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      ∀ j, ∀ (hj : j < r.val.length),
        0 ≤ lower (r.val[j]'hj).val ∧ lower (r.val[j]'hj).val ≤ upper (r.val[j]'hj).val ∧
          upper (r.val[j]'hj).val ≤ 100000) := by
  sorry

/-- Whenever the function returns a result r, the output intervals are strictly ordered and pairwise non-overlapping: for every j with 0 ≤ j < len(r)-1, writing r[j] = [a_j, b_j] and r[j+1] = [a_{j+1}, b_{j+1}], we have b_j < a_{j+1}. Consequently a_j < a_{j+1} for all such j.
  Preconditions: len(intervals) <= 10000; len(newInterval) = 2; 0 <= newInterval[0] <= newInterval[1] <= 100000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 100000; and for every i with 0 <= i < len(intervals)-1, intervals[i][1] < intervals[i+1][0]. -/
theorem spec_6 (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval) :
    ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      ∀ j, ∀ (hj : j + 1 < r.val.length),
        upper (r.val[j]'(by omega)).val < lower (r.val[j + 1]'(by omega)).val ∧
          lower (r.val[j]'(by omega)).val < lower (r.val[j + 1]'(by omega)).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval), ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      ∀ j, ∀ (hj : j + 1 < r.val.length),
        upper (r.val[j]'(by omega)).val < lower (r.val[j + 1]'(by omega)).val ∧
          lower (r.val[j]'(by omega)).val < lower (r.val[j + 1]'(by omega)).val) := by
  sorry

/-- Whenever the function returns a result r, no point of the input intervals or of newInterval is lost: for every real x, if (newInterval[0] ≤ x ≤ newInterval[1]) or (there exists i with 0 ≤ i < len(intervals) and intervals[i][0] ≤ x ≤ intervals[i][1]), then there exists j with 0 ≤ j < len(r) such that r[j][0] ≤ x ≤ r[j][1].
  Preconditions: len(intervals) <= 10000; len(newInterval) = 2; 0 <= newInterval[0] <= newInterval[1] <= 100000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 100000; and for every i with 0 <= i < len(intervals)-1, intervals[i][1] < intervals[i+1][0]. -/
theorem spec_7 (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval) :
    ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      ∀ x : ℝ, InInputs intervals newInterval x → InOutput r x := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval), ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      ∀ x : ℝ, InInputs intervals newInterval x → InOutput r x) := by
  sorry

/-- Whenever the function returns a result r, the output covers no points other than those in the input intervals or newInterval: for every real x, if there exists j with 0 ≤ j < len(r) such that r[j][0] ≤ x ≤ r[j][1], then (newInterval[0] ≤ x ≤ newInterval[1]) or (there exists i with 0 ≤ i < len(intervals) and intervals[i][0] ≤ x ≤ intervals[i][1]).
  Preconditions: len(intervals) <= 10000; len(newInterval) = 2; 0 <= newInterval[0] <= newInterval[1] <= 100000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 100000; and for every i with 0 <= i < len(intervals)-1, intervals[i][1] < intervals[i+1][0]. -/
theorem spec_8 (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval) :
    ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      ∀ x : ℝ, InOutput r x → InInputs intervals newInterval x := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval), ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      ∀ x : ℝ, InOutput r x → InInputs intervals newInterval x) := by
  sorry

/-- Whenever the function returns a result r, every endpoint of every output interval is an original endpoint: for every j with 0 ≤ j < len(r) and every k ∈ {0,1}, the value r[j][k] is equal either to newInterval[0], to newInterval[1], or to intervals[i][q] for some i with 0 ≤ i < len(intervals) and q ∈ {0,1}.
  Preconditions: len(intervals) <= 10000; len(newInterval) = 2; 0 <= newInterval[0] <= newInterval[1] <= 100000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 100000; and for every i with 0 <= i < len(intervals)-1, intervals[i][1] < intervals[i+1][0]. -/
theorem spec_9 (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval) :
    ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      ∀ j, ∀ (hj : j < r.val.length),
        IsEndpoint intervals newInterval (lower (r.val[j]'hj).val) ∧
          IsEndpoint intervals newInterval (upper (r.val[j]'hj).val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval), ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      ∀ j, ∀ (hj : j < r.val.length),
        IsEndpoint intervals newInterval (lower (r.val[j]'hj).val) ∧
          IsEndpoint intervals newInterval (upper (r.val[j]'hj).val)) := by
  sorry

/-- Whenever the function returns a result r, any input interval that does not intersect newInterval appears unchanged in r. More formally, for every i with 0 ≤ i < len(intervals), if intervals[i][1] < newInterval[0] or newInterval[1] < intervals[i][0], then there exists j with 0 ≤ j < len(r) such that r[j][0] = intervals[i][0] and r[j][1] = intervals[i][1].
  Preconditions: len(intervals) <= 10000; len(newInterval) = 2; 0 <= newInterval[0] <= newInterval[1] <= 100000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 100000; and for every i with 0 <= i < len(intervals)-1, intervals[i][1] < intervals[i+1][0]. -/
theorem spec_10 (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval) :
    ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      ∀ i, ∀ (hi : i < intervals.val.length),
        upper (intervals.val[i]'hi).val < lower newInterval.val ∨
            upper newInterval.val < lower (intervals.val[i]'hi).val →
          ∃ j, ∃ (hj : j < r.val.length),
            lower (r.val[j]'hj).val = lower (intervals.val[i]'hi).val ∧
              upper (r.val[j]'hj).val = upper (intervals.val[i]'hi).val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval), ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      ∀ i, ∀ (hi : i < intervals.val.length),
        upper (intervals.val[i]'hi).val < lower newInterval.val ∨
            upper newInterval.val < lower (intervals.val[i]'hi).val →
          ∃ j, ∃ (hj : j < r.val.length),
            lower (r.val[j]'hj).val = lower (intervals.val[i]'hi).val ∧
              upper (r.val[j]'hj).val = upper (intervals.val[i]'hi).val) := by
  sorry

/-- Whenever the function returns a result r, the whole newInterval is contained in exactly one output interval. That is, there exists j with 0 ≤ j < len(r) such that r[j][0] ≤ newInterval[0] and newInterval[1] ≤ r[j][1]; and for every k with 0 ≤ k < len(r) and k ≠ j, the interval r[k] does not intersect [newInterval[0], newInterval[1]] (i.e., r[k][1] < newInterval[0] or newInterval[1] < r[k][0]).
  Preconditions: len(intervals) <= 10000; len(newInterval) = 2; 0 <= newInterval[0] <= newInterval[1] <= 100000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 100000; and for every i with 0 <= i < len(intervals)-1, intervals[i][1] < intervals[i+1][0]. -/
theorem spec_11 (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval) :
    ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      ∃ j, ∃ (hj : j < r.val.length),
        lower (r.val[j]'hj).val ≤ lower newInterval.val ∧
          upper newInterval.val ≤ upper (r.val[j]'hj).val ∧
          ∀ k, ∀ (hk : k < r.val.length), k ≠ j →
            upper (r.val[k]'hk).val < lower newInterval.val ∨
              upper newInterval.val < lower (r.val[k]'hk).val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval), ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      ∃ j, ∃ (hj : j < r.val.length),
        lower (r.val[j]'hj).val ≤ lower newInterval.val ∧
          upper newInterval.val ≤ upper (r.val[j]'hj).val ∧
          ∀ k, ∀ (hk : k < r.val.length), k ≠ j →
            upper (r.val[k]'hk).val < lower newInterval.val ∨
              upper newInterval.val < lower (r.val[k]'hk).val) := by
  sorry

/-- Whenever the function returns a result r, its length is len(intervals) - k + 1, where k is the number of input intervals that intersect newInterval as closed intervals: k = #{ i | 0 ≤ i < len(intervals) and intervals[i][0] ≤ newInterval[1] and newInterval[0] ≤ intervals[i][1] }.
  Preconditions: len(intervals) <= 10000; len(newInterval) = 2; 0 <= newInterval[0] <= newInterval[1] <= 100000; for every i with 0 <= i < len(intervals), len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 100000; and for every i with 0 <= i < len(intervals)-1, intervals[i][1] < intervals[i+1][0]. -/
theorem spec_12 (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval) :
    ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      r.val.length = intervals.val.length - intersectCount intervals newInterval + 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (newInterval : Slice I64)
    (hpre : Pre intervals newInterval), ∀ r, Aegis.Insert.insert intervals newInterval = ok r →
      r.val.length = intervals.val.length - intersectCount intervals newInterval + 1) := by
  sorry

end AegisSpec.Insert
