import Aegis.FindRightInterval.Code.Funs

/-!
# Specifications of `Aegis.FindRightInterval.find_right_interval`

LeetCode problem `find-right-interval`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindRightInterval

open Aegis.FindRightInterval

abbrev Input := Slice (alloc.vec.Vec Std.I64)

def n (intervals : Input) : Nat := intervals.val.length

def iv (intervals : Input) (i : Nat) : List Std.I64 :=
  ((intervals.val[i]?).map (fun v => v.val)).getD []

def s (intervals : Input) (i : Nat) : Int :=
  (((iv intervals i)[0]?).map (fun v => v.val)).getD 0

def e (intervals : Input) (i : Nat) : Int :=
  (((iv intervals i)[1]?).map (fun v => v.val)).getD 0

def ans (out : alloc.vec.Vec Std.I64) (i : Nat) : Int :=
  ((out.val[i]?).map (fun v => v.val)).getD 0

def IsMaxStart (intervals : Input) (m : Int) : Prop :=
  (∃ j, j < n intervals ∧ s intervals j = m) ∧ ∀ j, j < n intervals → s intervals j ≤ m

def IsMinStart (intervals : Input) (m : Int) : Prop :=
  (∃ j, j < n intervals ∧ s intervals j = m) ∧ ∀ j, j < n intervals → m ≤ s intervals j

/-- Whenever the function returns a result r, len(r) = n and for every i with 0 <= i < n: if there exists j with 0 <= j < n such that s_j >= e_i, then r[i] is an index j with 0 <= j < n such that s_j >= e_i and for every k with 0 <= k < n and s_k >= e_i, s_j <= s_k; otherwise r[i] = -1.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 20000. For every i with 0 <= i < n, intervals[i] has length exactly 2; write s_i = intervals[i][0] and e_i = intervals[i][1]. Assume -1000000 <= s_i <= e_i <= 1000000 for every i. Assume the starts are pairwise distinct: for all i, j with 0 <= i < j < n, s_i != s_j. -/
theorem spec_1 (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r) :
    r.val.length = n intervals ∧
      ∀ i, i < n intervals →
        ((∃ j, j < n intervals ∧ e intervals i ≤ s intervals j) →
            ∃ j, j < n intervals ∧ e intervals i ≤ s intervals j ∧ ans r i = (j : Int) ∧
              ∀ k, k < n intervals → e intervals i ≤ s intervals k → s intervals j ≤ s intervals k) ∧
        ((¬ ∃ j, j < n intervals ∧ e intervals i ≤ s intervals j) →
            ans r i = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r), r.val.length = n intervals ∧
      ∀ i, i < n intervals →
        ((∃ j, j < n intervals ∧ e intervals i ≤ s intervals j) →
            ∃ j, j < n intervals ∧ e intervals i ≤ s intervals j ∧ ans r i = (j : Int) ∧
              ∀ k, k < n intervals → e intervals i ≤ s intervals k → s intervals j ≤ s intervals k) ∧
        ((¬ ∃ j, j < n intervals ∧ e intervals i ≤ s intervals j) →
            ans r i = -1)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, overflow, or access an index out of bounds.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 20000. For every i with 0 <= i < n, intervals[i] has length exactly 2; write s_i = intervals[i][0] and e_i = intervals[i][1]. Assume -1000000 <= s_i <= e_i <= 1000000 for every i. Assume the starts are pairwise distinct: for all i, j with 0 <= i < j < n, s_i != s_j. -/
theorem spec_2 (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j) :
    ∃ r, find_right_interval intervals = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j), ∃ r, find_right_interval intervals = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = n.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 20000. For every i with 0 <= i < n, intervals[i] has length exactly 2; write s_i = intervals[i][0] and e_i = intervals[i][1]. Assume -1000000 <= s_i <= e_i <= 1000000 for every i. Assume the starts are pairwise distinct: for all i, j with 0 <= i < j < n, s_i != s_j. -/
theorem spec_3 (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r) :
    r.val.length = n intervals := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r), r.val.length = n intervals) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, either r[i] = -1 or 0 <= r[i] < n.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 20000. For every i with 0 <= i < n, intervals[i] has length exactly 2; write s_i = intervals[i][0] and e_i = intervals[i][1]. Assume -1000000 <= s_i <= e_i <= 1000000 for every i. Assume the starts are pairwise distinct: for all i, j with 0 <= i < j < n, s_i != s_j. -/
theorem spec_4 (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r) :
    ∀ i, i < n intervals →
      ans r i = -1 ∨ (0 ≤ ans r i ∧ ans r i < (n intervals : Int)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r), ∀ i, i < n intervals →
      ans r i = -1 ∨ (0 ≤ ans r i ∧ ans r i < (n intervals : Int))) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] = -1 if and only if for every j with 0 <= j < n, s_j < e_i.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 20000. For every i with 0 <= i < n, intervals[i] has length exactly 2; write s_i = intervals[i][0] and e_i = intervals[i][1]. Assume -1000000 <= s_i <= e_i <= 1000000 for every i. Assume the starts are pairwise distinct: for all i, j with 0 <= i < j < n, s_i != s_j. -/
theorem spec_5 (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r) :
    ∀ i, i < n intervals →
      (ans r i = -1 ↔ ∀ j, j < n intervals → s intervals j < e intervals i) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r), ∀ i, i < n intervals →
      (ans r i = -1 ↔ ∀ j, j < n intervals → s intervals j < e intervals i)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, if r[i] != -1 then 0 <= r[i] < n and s_{r[i]} >= e_i.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 20000. For every i with 0 <= i < n, intervals[i] has length exactly 2; write s_i = intervals[i][0] and e_i = intervals[i][1]. Assume -1000000 <= s_i <= e_i <= 1000000 for every i. Assume the starts are pairwise distinct: for all i, j with 0 <= i < j < n, s_i != s_j. -/
theorem spec_6 (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r) :
    ∀ i, i < n intervals → ans r i ≠ -1 →
      0 ≤ ans r i ∧ ans r i < (n intervals : Int) ∧
        e intervals i ≤ s intervals (ans r i).toNat := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r), ∀ i, i < n intervals → ans r i ≠ -1 →
      0 ≤ ans r i ∧ ans r i < (n intervals : Int) ∧
        e intervals i ≤ s intervals (ans r i).toNat) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, if r[i] != -1 then 0 <= r[i] < n and for every k with 0 <= k < n and s_k >= e_i, s_{r[i]} <= s_k.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 20000. For every i with 0 <= i < n, intervals[i] has length exactly 2; write s_i = intervals[i][0] and e_i = intervals[i][1]. Assume -1000000 <= s_i <= e_i <= 1000000 for every i. Assume the starts are pairwise distinct: for all i, j with 0 <= i < j < n, s_i != s_j. -/
theorem spec_7 (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r) :
    ∀ i, i < n intervals → ans r i ≠ -1 →
      0 ≤ ans r i ∧ ans r i < (n intervals : Int) ∧
        ∀ k, k < n intervals → e intervals i ≤ s intervals k →
          s intervals (ans r i).toNat ≤ s intervals k := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r), ∀ i, i < n intervals → ans r i ≠ -1 →
      0 ≤ ans r i ∧ ans r i < (n intervals : Int) ∧
        ∀ k, k < n intervals → e intervals i ≤ s intervals k →
          s intervals (ans r i).toNat ≤ s intervals k) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, if e_i > max{s_j | 0 <= j < n}, then r[i] = -1.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 20000. For every i with 0 <= i < n, intervals[i] has length exactly 2; write s_i = intervals[i][0] and e_i = intervals[i][1]. Assume -1000000 <= s_i <= e_i <= 1000000 for every i. Assume the starts are pairwise distinct: for all i, j with 0 <= i < j < n, s_i != s_j. -/
theorem spec_8 (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r) :
    ∀ i, i < n intervals → ∀ m, IsMaxStart intervals m → m < e intervals i → ans r i = -1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r), ∀ i, i < n intervals → ∀ m, IsMaxStart intervals m → m < e intervals i → ans r i = -1) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, if e_i <= min{s_j | 0 <= j < n}, then r[i] is the unique index j0 with s_{j0} = min{s_j | 0 <= j < n}.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 20000. For every i with 0 <= i < n, intervals[i] has length exactly 2; write s_i = intervals[i][0] and e_i = intervals[i][1]. Assume -1000000 <= s_i <= e_i <= 1000000 for every i. Assume the starts are pairwise distinct: for all i, j with 0 <= i < j < n, s_i != s_j. -/
theorem spec_9 (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r) :
    ∀ i, i < n intervals → ∀ m, IsMinStart intervals m → e intervals i ≤ m →
      ∃ j0, j0 < n intervals ∧ s intervals j0 = m ∧ ans r i = (j0 : Int) ∧
        ∀ j, j < n intervals → s intervals j = m → j = j0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r), ∀ i, i < n intervals → ∀ m, IsMinStart intervals m → e intervals i ≤ m →
      ∃ j0, j0 < n intervals ∧ s intervals j0 = m ∧ ans r i = (j0 : Int) ∧
        ∀ j, j < n intervals → s intervals j = m → j = j0) := by
  sorry

/-- Whenever the function returns a result r, for every i, j with 0 <= i < n and 0 <= j < n, if e_i = s_j, then r[i] = j.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 20000. For every i with 0 <= i < n, intervals[i] has length exactly 2; write s_i = intervals[i][0] and e_i = intervals[i][1]. Assume -1000000 <= s_i <= e_i <= 1000000 for every i. Assume the starts are pairwise distinct: for all i, j with 0 <= i < j < n, s_i != s_j. -/
theorem spec_10 (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r) :
    ∀ i j, i < n intervals → j < n intervals → e intervals i = s intervals j →
      ans r i = (j : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r), ∀ i j, i < n intervals → j < n intervals → e intervals i = s intervals j →
      ans r i = (j : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every i, k with 0 <= i < n and 0 <= k < n, if e_i = e_k, then r[i] = r[k].
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 20000. For every i with 0 <= i < n, intervals[i] has length exactly 2; write s_i = intervals[i][0] and e_i = intervals[i][1]. Assume -1000000 <= s_i <= e_i <= 1000000 for every i. Assume the starts are pairwise distinct: for all i, j with 0 <= i < j < n, s_i != s_j. -/
theorem spec_11 (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r) :
    ∀ i k, i < n intervals → k < n intervals → e intervals i = e intervals k →
      ans r i = ans r k := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r), ∀ i k, i < n intervals → k < n intervals → e intervals i = e intervals k →
      ans r i = ans r k) := by
  sorry

/-- Whenever the function returns a result r, for every i, k with 0 <= i < n and 0 <= k < n, if 0 <= r[i] < n, 0 <= r[k] < n, and e_i <= e_k, then s_{r[i]} <= s_{r[k]}.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 20000. For every i with 0 <= i < n, intervals[i] has length exactly 2; write s_i = intervals[i][0] and e_i = intervals[i][1]. Assume -1000000 <= s_i <= e_i <= 1000000 for every i. Assume the starts are pairwise distinct: for all i, j with 0 <= i < j < n, s_i != s_j. -/
theorem spec_12 (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r) :
    ∀ i k, i < n intervals → k < n intervals →
      0 ≤ ans r i → ans r i < (n intervals : Int) →
      0 ≤ ans r k → ans r k < (n intervals : Int) →
      e intervals i ≤ e intervals k →
      s intervals (ans r i).toNat ≤ s intervals (ans r k).toNat := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r), ∀ i k, i < n intervals → k < n intervals →
      0 ≤ ans r i → ans r i < (n intervals : Int) →
      0 ≤ ans r k → ans r k < (n intervals : Int) →
      e intervals i ≤ e intervals k →
      s intervals (ans r i).toNat ≤ s intervals (ans r k).toNat) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] = i if and only if s_i = e_i.
  Preconditions: Let n = len(intervals). Assume 1 <= n <= 20000. For every i with 0 <= i < n, intervals[i] has length exactly 2; write s_i = intervals[i][0] and e_i = intervals[i][1]. Assume -1000000 <= s_i <= e_i <= 1000000 for every i. Assume the starts are pairwise distinct: for all i, j with 0 <= i < j < n, s_i != s_j. -/
theorem spec_13 (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r) :
    ∀ i, i < n intervals → (ans r i = (i : Int) ↔ s intervals i = e intervals i) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (intervals : Input)
    (hn_lo : 1 ≤ n intervals) (hn_hi : n intervals ≤ 20000)
    (hlen : ∀ i, i < n intervals → (iv intervals i).length = 2)
    (hrange : ∀ i, i < n intervals →
      -1000000 ≤ s intervals i ∧ s intervals i ≤ e intervals i ∧ e intervals i ≤ 1000000)
    (hdistinct : ∀ i j, i < j → j < n intervals → s intervals i ≠ s intervals j)
    (r : alloc.vec.Vec Std.I64)
    (hr : find_right_interval intervals = ok r), ∀ i, i < n intervals → (ans r i = (i : Int) ↔ s intervals i = e intervals i)) := by
  sorry

end AegisSpec.FindRightInterval
