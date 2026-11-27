import Aegis.Merge.Code.Funs
import Mathlib.Basic.Real.Basic

/-!
# Specifications of `Aegis.Merge.merge`

LeetCode problem `merge-intervals`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.Merge

def rowOf (v : alloc.vec.Vec Std.I64) : Option (Int × Int) :=
  match v.val with
  | [a, b] => some (a.val, b.val)
  | _ => none

def inRow (intervals : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Option (Int × Int) :=
  (intervals.val[i]?).bind rowOf

def outRow (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (j : Nat) : Option (Int × Int) :=
  (r.val[j]?).bind rowOf

def outRowLen (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (j : Nat) : Nat :=
  (r.val[j]?.map (fun v => v.val.length)).getD 0

def InUnion (rows : Nat → Option (Int × Int)) (n : Nat) (x : ℝ) : Prop :=
  ∃ i, i < n ∧ ∃ a b : Int, rows i = some (a, b) ∧ (a : ℝ) ≤ x ∧ x ≤ (b : ℝ)

def InputRowOK (intervals : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Prop :=
  ∃ a b : Int, inRow intervals i = some (a, b) ∧ 0 ≤ a ∧ a ≤ b ∧ b ≤ 10000

/-- Whenever the function returns a result r, let m = len(r). Then: (1) for every j with 0 <= j < m, len(r[j]) = 2 and r[j][0] <= r[j][1]; (2) for every j, k with 0 <= j < k < m, r[j][1] < r[k][0]; (3) for every real number x, there exists i with 0 <= i < n and intervals[i][0] <= x <= intervals[i][1] if and only if there exists j with 0 <= j < m and r[j][0] <= x <= r[j][1].
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 10^4. For every i with 0 <= i < n, len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 10^4. -/
theorem spec_1
    (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r) :
    (∀ j, j < r.val.length → ∃ a b : Int, outRow r j = some (a, b) ∧ a ≤ b) ∧
      (∀ j k, j < k → k < r.val.length → ∀ a b c d : Int,
        outRow r j = some (a, b) → outRow r k = some (c, d) → b < c) ∧
      (∀ x : ℝ,
        InUnion (inRow intervals) intervals.val.length x ↔
          InUnion (outRow r) r.val.length x) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r), (∀ j, j < r.val.length → ∃ a b : Int, outRow r j = some (a, b) ∧ a ≤ b) ∧
      (∀ j k, j < k → k < r.val.length → ∀ a b c d : Int,
        outRow r j = some (a, b) → outRow r k = some (c, d) → b < c) ∧
      (∀ x : ℝ,
        InUnion (inRow intervals) intervals.val.length x ↔
          InUnion (outRow r) r.val.length x)) := by
  sorry

/-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 10^4. For every i with 0 <= i < n, len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 10^4. -/
theorem spec_2
    (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      _root_.Aegis.Merge.merge intervals = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      _root_.Aegis.Merge.merge intervals = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r), len(r[j]) = 2.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 10^4. For every i with 0 <= i < n, len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 10^4. -/
theorem spec_3
    (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r) :
    ∀ j, j < r.val.length → outRowLen r j = 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r), ∀ j, j < r.val.length → outRowLen r j = 2) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r), r[j][0] <= r[j][1].
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 10^4. For every i with 0 <= i < n, len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 10^4. -/
theorem spec_4
    (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r) :
    ∀ j, j < r.val.length → ∃ a b : Int, outRow r j = some (a, b) ∧ a ≤ b := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r), ∀ j, j < r.val.length → ∃ a b : Int, outRow r j = some (a, b) ∧ a ≤ b) := by
  sorry

/-- Whenever the function returns a result r, for every j, k with 0 <= j < k < len(r), it is not the case that r[j][0] <= r[k][1] and r[k][0] <= r[j][1].
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 10^4. For every i with 0 <= i < n, len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 10^4. -/
theorem spec_5
    (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r) :
    ∀ j k, j < k → k < r.val.length → ∀ a b c d : Int,
      outRow r j = some (a, b) → outRow r k = some (c, d) → ¬ (a ≤ d ∧ c ≤ b) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r), ∀ j k, j < k → k < r.val.length → ∀ a b c d : Int,
      outRow r j = some (a, b) → outRow r k = some (c, d) → ¬ (a ≤ d ∧ c ≤ b)) := by
  sorry

/-- Whenever the function returns a result r, for every j, k with 0 <= j < k < len(r), r[j][0] <= r[k][0].
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 10^4. For every i with 0 <= i < n, len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 10^4. -/
theorem spec_6
    (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r) :
    ∀ j k, j < k → k < r.val.length → ∀ a b c d : Int,
      outRow r j = some (a, b) → outRow r k = some (c, d) → a ≤ c := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r), ∀ j k, j < k → k < r.val.length → ∀ a b c d : Int,
      outRow r j = some (a, b) → outRow r k = some (c, d) → a ≤ c) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(intervals) and every real number x with intervals[i][0] <= x <= intervals[i][1], there exists j with 0 <= j < len(r) such that r[j][0] <= x <= r[j][1].
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 10^4. For every i with 0 <= i < n, len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 10^4. -/
theorem spec_7
    (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r) :
    ∀ i, i < intervals.val.length → ∀ a b : Int, inRow intervals i = some (a, b) →
      ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ (b : ℝ) →
        ∃ j, j < r.val.length ∧ ∃ c d : Int,
          outRow r j = some (c, d) ∧ (c : ℝ) ≤ x ∧ x ≤ (d : ℝ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r), ∀ i, i < intervals.val.length → ∀ a b : Int, inRow intervals i = some (a, b) →
      ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ (b : ℝ) →
        ∃ j, j < r.val.length ∧ ∃ c d : Int,
          outRow r j = some (c, d) ∧ (c : ℝ) ≤ x ∧ x ≤ (d : ℝ)) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r) and every real number x with r[j][0] <= x <= r[j][1], there exists i with 0 <= i < len(intervals) such that intervals[i][0] <= x <= intervals[i][1].
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 10^4. For every i with 0 <= i < n, len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 10^4. -/
theorem spec_8
    (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r) :
    ∀ j, j < r.val.length → ∀ a b : Int, outRow r j = some (a, b) →
      ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ (b : ℝ) →
        ∃ i, i < intervals.val.length ∧ ∃ c d : Int,
          inRow intervals i = some (c, d) ∧ (c : ℝ) ≤ x ∧ x ≤ (d : ℝ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r), ∀ j, j < r.val.length → ∀ a b : Int, outRow r j = some (a, b) →
      ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ (b : ℝ) →
        ∃ i, i < intervals.val.length ∧ ∃ c d : Int,
          inRow intervals i = some (c, d) ∧ (c : ℝ) ≤ x ∧ x ≤ (d : ℝ)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(intervals), there exists j with 0 <= j < len(r) such that r[j][0] <= intervals[i][0] and intervals[i][1] <= r[j][1].
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 10^4. For every i with 0 <= i < n, len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 10^4. -/
theorem spec_9
    (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r) :
    ∀ i, i < intervals.val.length → ∀ a b : Int, inRow intervals i = some (a, b) →
      ∃ j, j < r.val.length ∧ ∃ c d : Int,
        outRow r j = some (c, d) ∧ c ≤ a ∧ b ≤ d := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r), ∀ i, i < intervals.val.length → ∀ a b : Int, inRow intervals i = some (a, b) →
      ∃ j, j < r.val.length ∧ ∃ c d : Int,
        outRow r j = some (c, d) ∧ c ≤ a ∧ b ≤ d) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r), the interval r[j] is a maximal interval contained in the union U = ∪_{i=0}^{n-1} [intervals[i][0], intervals[i][1]]; that is, r[j] ⊆ U, and there is no interval [a,b] with (a < r[j][0] or b > r[j][1]) such that r[j] ⊆ [a,b] ⊆ U.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 10^4. For every i with 0 <= i < n, len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 10^4. -/
theorem spec_10
    (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r) :
    ∀ j, j < r.val.length → ∀ a b : Int, outRow r j = some (a, b) →
      (∀ x : ℝ, (a : ℝ) ≤ x → x ≤ (b : ℝ) →
          InUnion (inRow intervals) intervals.val.length x) ∧
        ¬ ∃ a' b' : ℝ,
            (a' < (a : ℝ) ∨ (b : ℝ) < b') ∧
              (∀ x : ℝ, (a : ℝ) ≤ x → x ≤ (b : ℝ) → a' ≤ x ∧ x ≤ b') ∧
              (∀ x : ℝ, a' ≤ x → x ≤ b' →
                InUnion (inRow intervals) intervals.val.length x) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r), ∀ j, j < r.val.length → ∀ a b : Int, outRow r j = some (a, b) →
      (∀ x : ℝ, (a : ℝ) ≤ x → x ≤ (b : ℝ) →
          InUnion (inRow intervals) intervals.val.length x) ∧
        ¬ ∃ a' b' : ℝ,
            (a' < (a : ℝ) ∨ (b : ℝ) < b') ∧
              (∀ x : ℝ, (a : ℝ) ≤ x → x ≤ (b : ℝ) → a' ≤ x ∧ x ≤ b') ∧
              (∀ x : ℝ, a' ≤ x → x ≤ b' →
                InUnion (inRow intervals) intervals.val.length x)) := by
  sorry

/-- Whenever the function returns a result r, len(r) >= 1 and r[0][0] = min_{0 <= i < len(intervals)} intervals[i][0].
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 10^4. For every i with 0 <= i < n, len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 10^4. -/
theorem spec_11
    (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r) :
    1 ≤ r.val.length ∧
      ∀ a b : Int, outRow r 0 = some (a, b) →
        (∀ i, i < intervals.val.length → ∀ c d : Int, inRow intervals i = some (c, d) → a ≤ c) ∧
          (∃ i, i < intervals.val.length ∧ ∃ c d : Int,
            inRow intervals i = some (c, d) ∧ a = c) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r), 1 ≤ r.val.length ∧
      ∀ a b : Int, outRow r 0 = some (a, b) →
        (∀ i, i < intervals.val.length → ∀ c d : Int, inRow intervals i = some (c, d) → a ≤ c) ∧
          (∃ i, i < intervals.val.length ∧ ∃ c d : Int,
            inRow intervals i = some (c, d) ∧ a = c)) := by
  sorry

/-- Whenever the function returns a result r, len(r) >= 1 and r[len(r)-1][1] = max_{0 <= i < len(intervals)} intervals[i][1].
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 10^4. For every i with 0 <= i < n, len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 10^4. -/
theorem spec_12
    (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r) :
    1 ≤ r.val.length ∧
      ∀ a b : Int, outRow r (r.val.length - 1) = some (a, b) →
        (∀ i, i < intervals.val.length → ∀ c d : Int, inRow intervals i = some (c, d) → d ≤ b) ∧
          (∃ i, i < intervals.val.length ∧ ∃ c d : Int,
            inRow intervals i = some (c, d) ∧ b = d) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r), 1 ≤ r.val.length ∧
      ∀ a b : Int, outRow r (r.val.length - 1) = some (a, b) →
        (∀ i, i < intervals.val.length → ∀ c d : Int, inRow intervals i = some (c, d) → d ≤ b) ∧
          (∃ i, i < intervals.val.length ∧ ∃ c d : Int,
            inRow intervals i = some (c, d) ∧ b = d)) := by
  sorry

/-- Whenever the function returns a result r, 1 <= len(r) <= len(intervals).
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 10^4. For every i with 0 <= i < n, len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 10^4. -/
theorem spec_13
    (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r) :
    1 ≤ r.val.length ∧ r.val.length ≤ intervals.val.length := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r), 1 ≤ r.val.length ∧ r.val.length ≤ intervals.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r), there exists i with 0 <= i < len(intervals) such that r[j][0] = intervals[i][0], and there exists k with 0 <= k < len(intervals) such that r[j][1] = intervals[k][1].
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 10^4. For every i with 0 <= i < n, len(intervals[i]) = 2 and 0 <= intervals[i][0] <= intervals[i][1] <= 10^4. -/
theorem spec_14
    (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r) :
    ∀ j, j < r.val.length → ∀ a b : Int, outRow r j = some (a, b) →
      (∃ i, i < intervals.val.length ∧ ∃ b' : Int, inRow intervals i = some (a, b')) ∧
        (∃ k, k < intervals.val.length ∧ ∃ a' : Int, inRow intervals k = some (a', b)) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ intervals.val.length)
    (hn2 : intervals.val.length ≤ 10000)
    (hpre : ∀ i, i < intervals.val.length → InputRowOK intervals i)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : _root_.Aegis.Merge.merge intervals = ok r), ∀ j, j < r.val.length → ∀ a b : Int, outRow r j = some (a, b) →
      (∃ i, i < intervals.val.length ∧ ∃ b' : Int, inRow intervals i = some (a, b')) ∧
        (∃ k, k < intervals.val.length ∧ ∃ a' : Int, inRow intervals k = some (a', b))) := by
  sorry

end AegisSpec.Merge
