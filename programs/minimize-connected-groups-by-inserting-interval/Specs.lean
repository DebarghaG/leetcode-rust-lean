import Aegis.MinConnectedGroups.Code.Funs

/-!
# Specifications of `Aegis.MinConnectedGroups.min_connected_groups`

LeetCode problem `minimize-connected-groups-by-inserting-interval`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinConnectedGroups (min_connected_groups)

namespace AegisSpec.MinConnectedGroups

def LIMIT : Int := 1000000000000

def entries (intervals : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  intervals.val.map (fun v => v.val.map (fun x => x.val))

def WellFormed (ivs : List (List Int)) : Prop :=
  (∀ iv ∈ ivs, iv.length = 2) ∧
    ∀ iv ∈ ivs, ∃ s e : Int, iv = [s, e] ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ LIMIT

def InputBounds (intervals : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  1 ≤ (entries intervals).length ∧ (entries intervals).length ≤ 100000 ∧
    WellFormed (entries intervals)

def KBound (k : Std.I64) : Prop := 0 ≤ k.val ∧ k.val ≤ LIMIT

def Pre (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) : Prop :=
  InputBounds intervals ∧ KBound k

def pairsOf (ivs : List (List Int)) : List (Int × Int) :=
  ivs.filterMap fun iv =>
    match iv with
    | [s, e] => some (s, e)
    | _ => none

def insertPair (p : Int × Int) : List (Int × Int) → List (Int × Int)
  | [] => [p]
  | q :: qs =>
    if p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2) then p :: q :: qs else q :: insertPair p qs

def sortPairs (ps : List (Int × Int)) : List (Int × Int) :=
  ps.foldr (fun p acc => insertPair p acc) []

def mergeStep (acc : List (Int × Int)) (p : Int × Int) : List (Int × Int) :=
  match acc with
  | [] => [p]
  | (s, e) :: rest => if p.1 ≤ e then (s, max e p.2) :: rest else p :: acc

def groupsOf (ivs : List (List Int)) : List (Int × Int) :=
  ((sortPairs (pairsOf ivs)).foldl mergeStep []).reverse

def groups (intervals : Slice (alloc.vec.Vec Std.I64)) : List (Int × Int) :=
  groupsOf (entries intervals)

def numGroups (intervals : Slice (alloc.vec.Vec Std.I64)) : Nat := (groups intervals).length

def startAt (gs : List (Int × Int)) (i : Nat) : Int := (gs.getD i (0, 0)).1

def endAt (gs : List (Int × Int)) (i : Nat) : Int := (gs.getD i (0, 0)).2

def maxSpan (gs : List (Int × Int)) (k : Int) : Nat :=
  ((Finset.range gs.length).product (Finset.range gs.length)).filter
      (fun p => p.1 ≤ p.2 ∧ startAt gs p.2 - endAt gs p.1 ≤ k)
    |>.sup (fun p => p.2 - p.1)

def insertInterval (ivs : List (List Int)) (s e : Int) : List (List Int) := [s, e] :: ivs

def numGroupsInserted (intervals : Slice (alloc.vec.Vec Std.I64)) (s e : Int) : Nat :=
  (groupsOf (insertInterval (entries intervals) s e)).length

def overlapSet (gs : List (Int × Int)) (s e : Int) : Finset Nat :=
  (Finset.range gs.length).filter (fun i => startAt gs i ≤ e ∧ s ≤ endAt gs i)

def DuplicateOne (intervals intervals' : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∃ (iv : alloc.vec.Vec Std.I64) (l₁ l₂ : List (alloc.vec.Vec Std.I64)),
    intervals.val = l₁ ++ iv :: l₂ ∧ intervals'.val = l₁ ++ iv :: iv :: l₂

/-- Let G_0,...,G_{m-1} be the connected groups of intervals, ordered by increasing left endpoint, and let L_i and R_i be the minimum and maximum endpoints occurring in G_i. Put D = max { b-a | 0 <= a <= b < m and L_b - R_a <= k }. The function returns a result r and r = m - D.
  Preconditions: 1 <= len(intervals) <= 100000; every intervals[i] has length 2; writing intervals[i] = [start_i, end_i], 1 <= start_i <= end_i <= 10^12; 0 <= k <= 10^12. These bounds include the problem's stated constraints and the supplied examples. -/
theorem spec_1 (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k) :
    ∃ r : Std.I64, min_connected_groups intervals k = ok r ∧
      r.val = (numGroups intervals : Int) - ((maxSpan (groups intervals) k.val : Nat) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k), ∃ r : Std.I64, min_connected_groups intervals k = ok r ∧
      r.val = (numGroups intervals : Int) - ((maxSpan (groups intervals) k.val : Nat) : Int)) := by
  sorry

/-- The function returns a result r and does not fail (no overflow, out-of-bounds access, or panic) on every input satisfying the preconditions.
  Preconditions: 1 <= len(intervals) <= 100000; every intervals[i] has length 2; writing intervals[i] = [start_i, end_i], 1 <= start_i <= end_i <= 10^12; 0 <= k <= 10^12. These bounds include the problem's stated constraints and the supplied examples. -/
theorem spec_2 (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k) :
    ∃ r : Std.I64, min_connected_groups intervals k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k), ∃ r : Std.I64, min_connected_groups intervals k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: 1 <= len(intervals) <= 100000; every intervals[i] has length 2; writing intervals[i] = [start_i, end_i], 1 <= start_i <= end_i <= 10^12; 0 <= k <= 10^12. These bounds include the problem's stated constraints and the supplied examples. -/
theorem spec_3 (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k) (r : Std.I64)
    (hr : min_connected_groups intervals k = ok r) :
    1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k) (r : Std.I64)
    (hr : min_connected_groups intervals k = ok r), 1 ≤ r.val) := by
  sorry

/-- Let m be the number of connected groups of the original intervals. Whenever the function returns a result r, r <= m.
  Preconditions: 1 <= len(intervals) <= 100000; every intervals[i] has length 2; writing intervals[i] = [start_i, end_i], 1 <= start_i <= end_i <= 10^12; 0 <= k <= 10^12. These bounds include the problem's stated constraints and the supplied examples. -/
theorem spec_4 (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k) (r : Std.I64)
    (hr : min_connected_groups intervals k = ok r) :
    r.val ≤ (numGroups intervals : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k) (r : Std.I64)
    (hr : min_connected_groups intervals k = ok r), r.val ≤ (numGroups intervals : Int)) := by
  sorry

/-- Let m be the number of connected groups of the original intervals. If m = 1, then the function returns r = 1.
  Preconditions: 1 <= len(intervals) <= 100000; every intervals[i] has length 2; writing intervals[i] = [start_i, end_i], 1 <= start_i <= end_i <= 10^12; 0 <= k <= 10^12. These bounds include the problem's stated constraints and the supplied examples. -/
theorem spec_5 (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k) (hm : numGroups intervals = 1) :
    ∃ r : Std.I64, min_connected_groups intervals k = ok r ∧ r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k) (hm : numGroups intervals = 1), ∃ r : Std.I64, min_connected_groups intervals k = ok r ∧ r.val = 1) := by
  sorry

/-- Let m be the number of connected groups of the original intervals. If k = 0, then the function returns r = m.
  Preconditions: 1 <= len(intervals) <= 100000; every intervals[i] has length 2; writing intervals[i] = [start_i, end_i], 1 <= start_i <= end_i <= 10^12; 0 <= k <= 10^12. These bounds include the problem's stated constraints and the supplied examples. -/
theorem spec_6 (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k) (hk : k.val = 0) :
    ∃ r : Std.I64,
      min_connected_groups intervals k = ok r ∧ r.val = (numGroups intervals : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k) (hk : k.val = 0), ∃ r : Std.I64,
      min_connected_groups intervals k = ok r ∧ r.val = (numGroups intervals : Int)) := by
  sorry

/-- Let G_0,...,G_{m-1} be the connected groups of intervals ordered left to right, and let L_i and R_i be the minimum and maximum endpoints in G_i. The function returns r = 1 if and only if L_{m-1} - R_0 <= k.
  Preconditions: 1 <= len(intervals) <= 100000; every intervals[i] has length 2; writing intervals[i] = [start_i, end_i], 1 <= start_i <= end_i <= 10^12; 0 <= k <= 10^12. These bounds include the problem's stated constraints and the supplied examples. -/
theorem spec_7 (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k) (r : Std.I64)
    (hr : min_connected_groups intervals k = ok r) :
    (r.val = 1 ↔
      startAt (groups intervals) (numGroups intervals - 1) - endAt (groups intervals) 0 ≤ k.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k) (r : Std.I64)
    (hr : min_connected_groups intervals k = ok r), (r.val = 1 ↔
      startAt (groups intervals) (numGroups intervals - 1) - endAt (groups intervals) 0 ≤ k.val)) := by
  sorry

/-- Let r be the value returned. There exist integers s and e with s <= e and e-s <= k such that inserting [s,e] into intervals produces exactly r connected groups.
  Preconditions: 1 <= len(intervals) <= 100000; every intervals[i] has length 2; writing intervals[i] = [start_i, end_i], 1 <= start_i <= end_i <= 10^12; 0 <= k <= 10^12. These bounds include the problem's stated constraints and the supplied examples. -/
theorem spec_8 (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k) :
    ∃ r : Std.I64, min_connected_groups intervals k = ok r ∧
      ∃ s e : Int, s ≤ e ∧ e - s ≤ k.val ∧ r.val = (numGroupsInserted intervals s e : Nat) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k), ∃ r : Std.I64, min_connected_groups intervals k = ok r ∧
      ∃ s e : Int, s ≤ e ∧ e - s ≤ k.val ∧ r.val = (numGroupsInserted intervals s e : Nat)) := by
  sorry

/-- Let r be the value returned. For every integer interval [s,e] with s <= e and e-s <= k, if n(s,e) is the number of connected groups after inserting [s,e] into intervals, then n(s,e) >= r.
  Preconditions: 1 <= len(intervals) <= 100000; every intervals[i] has length 2; writing intervals[i] = [start_i, end_i], 1 <= start_i <= end_i <= 10^12; 0 <= k <= 10^12. These bounds include the problem's stated constraints and the supplied examples. -/
theorem spec_9 (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k) :
    ∃ r : Std.I64, min_connected_groups intervals k = ok r ∧
      ∀ s e : Int, s ≤ e → e - s ≤ k.val →
        r.val ≤ (numGroupsInserted intervals s e : Nat) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k), ∃ r : Std.I64, min_connected_groups intervals k = ok r ∧
      ∀ s e : Int, s ≤ e → e - s ≤ k.val →
        r.val ≤ (numGroupsInserted intervals s e : Nat)) := by
  sorry

/-- Let r1 be the value returned by min_connected_groups(intervals,k1) and r2 the value returned by min_connected_groups(intervals,k2). Then r1 >= r2.
  Preconditions: intervals satisfies: 1 <= len(intervals) <= 100000; every intervals[i] has length 2; writing intervals[i] = [start_i, end_i], 1 <= start_i <= end_i <= 10^12. Also k1 and k2 are integers with 0 <= k1 <= k2 <= 10^12. -/
theorem spec_10 (intervals : Slice (alloc.vec.Vec Std.I64)) (k1 k2 : Std.I64)
    (hpre : InputBounds intervals) (h1 : 0 ≤ k1.val) (h12 : k1.val ≤ k2.val)
    (h2 : k2.val ≤ LIMIT) (r1 r2 : Std.I64)
    (hr1 : min_connected_groups intervals k1 = ok r1)
    (hr2 : min_connected_groups intervals k2 = ok r2) :
    r2.val ≤ r1.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (k1 k2 : Std.I64)
    (hpre : InputBounds intervals) (h1 : 0 ≤ k1.val) (h12 : k1.val ≤ k2.val)
    (h2 : k2.val ≤ LIMIT) (r1 r2 : Std.I64)
    (hr1 : min_connected_groups intervals k1 = ok r1)
    (hr2 : min_connected_groups intervals k2 = ok r2), r2.val ≤ r1.val) := by
  sorry

/-- The value returned by min_connected_groups(intervals',k) equals the value returned by min_connected_groups(intervals,k).
  Preconditions: intervals satisfies: 1 <= len(intervals) <= 100000; every intervals[i] has length 2; writing intervals[i] = [start_i, end_i], 1 <= start_i <= end_i <= 10^12; 0 <= k <= 10^12. intervals' is any reordering of intervals with the same length and the same entries in a possibly different order. -/
theorem spec_11 (intervals intervals' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : InputBounds intervals) (hk : KBound k)
    (hperm : intervals'.val.Perm intervals.val) (r r' : Std.I64)
    (hr' : min_connected_groups intervals' k = ok r')
    (hr : min_connected_groups intervals k = ok r) :
    r'.val = r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (intervals intervals' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : InputBounds intervals) (hk : KBound k)
    (hperm : intervals'.val.Perm intervals.val) (r r' : Std.I64)
    (hr' : min_connected_groups intervals' k = ok r')
    (hr : min_connected_groups intervals k = ok r), r'.val = r.val) := by
  sorry

/-- Let G_0,...,G_{m-1} be the connected groups of intervals ordered left to right, let L_i and R_i be their minimum and maximum endpoints, and let r be the value returned. For all 0 <= a < b < m with L_b - R_a <= k, we have b-a <= m-r.
  Preconditions: 1 <= len(intervals) <= 100000; every intervals[i] has length 2; writing intervals[i] = [start_i, end_i], 1 <= start_i <= end_i <= 10^12; 0 <= k <= 10^12. These bounds include the problem's stated constraints and the supplied examples. -/
theorem spec_12 (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k) (r : Std.I64)
    (hr : min_connected_groups intervals k = ok r) (a b : Nat)
    (ha : a < b) (hb : b < numGroups intervals)
    (hk : startAt (groups intervals) b - endAt (groups intervals) a ≤ k.val) :
    (b : Int) - (a : Int) ≤ (numGroups intervals : Int) - r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k) (r : Std.I64)
    (hr : min_connected_groups intervals k = ok r) (a b : Nat)
    (ha : a < b) (hb : b < numGroups intervals)
    (hk : startAt (groups intervals) b - endAt (groups intervals) a ≤ k.val), (b : Int) - (a : Int) ≤ (numGroups intervals : Int) - r.val) := by
  sorry

/-- Let G_0,...,G_{m-1} be the connected groups of intervals ordered left to right, let L_i and R_i be their minimum and maximum endpoints, and let r be the value returned. There exist indices a,b with 0 <= a <= b < m such that L_b - R_a <= k and b-a = m-r.
  Preconditions: 1 <= len(intervals) <= 100000; every intervals[i] has length 2; writing intervals[i] = [start_i, end_i], 1 <= start_i <= end_i <= 10^12; 0 <= k <= 10^12. These bounds include the problem's stated constraints and the supplied examples. -/
theorem spec_13 (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k) (r : Std.I64)
    (hr : min_connected_groups intervals k = ok r) :
    ∃ a b : Nat, a ≤ b ∧ b < numGroups intervals ∧
      startAt (groups intervals) b - endAt (groups intervals) a ≤ k.val ∧
      (b : Int) - (a : Int) = (numGroups intervals : Int) - r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : Pre intervals k) (r : Std.I64)
    (hr : min_connected_groups intervals k = ok r), ∃ a b : Nat, a ≤ b ∧ b < numGroups intervals ∧
      startAt (groups intervals) b - endAt (groups intervals) a ≤ k.val ∧
      (b : Int) - (a : Int) = (numGroups intervals : Int) - r.val) := by
  sorry

/-- Let intervals' be obtained from intervals by inserting one extra copy of any one of its entries, so len(intervals') = len(intervals)+1. Then the minimum number of connected groups returned for intervals' with the same k equals the value returned for intervals with k.
  Preconditions: intervals satisfies: 1 <= len(intervals) < 100000; every intervals[i] has length 2; writing intervals[i] = [start_i, end_i], 1 <= start_i <= end_i <= 10^12; 0 <= k <= 10^12. -/
theorem spec_14 (intervals intervals' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : 1 ≤ (entries intervals).length ∧ (entries intervals).length < 100000 ∧
      WellFormed (entries intervals))
    (hk : KBound k) (hdup : DuplicateOne intervals intervals') (r r' : Std.I64)
    (hr' : min_connected_groups intervals' k = ok r')
    (hr : min_connected_groups intervals k = ok r) :
    r'.val = r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (intervals intervals' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hpre : 1 ≤ (entries intervals).length ∧ (entries intervals).length < 100000 ∧
      WellFormed (entries intervals))
    (hk : KBound k) (hdup : DuplicateOne intervals intervals') (r r' : Std.I64)
    (hr' : min_connected_groups intervals' k = ok r')
    (hr : min_connected_groups intervals k = ok r), r'.val = r.val) := by
  sorry

end AegisSpec.MinConnectedGroups
