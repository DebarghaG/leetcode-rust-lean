import Aegis.AddRungs.Code.Funs

/-!
# Specifications of `Aegis.AddRungs.add_rungs`

LeetCode problem `add-minimum-number-of-rungs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.AddRungs

open Aegis.AddRungs (add_rungs)

def vals (rungs : Slice Std.I64) : List ℤ := rungs.val.map (fun x => x.val)

def rungAt (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

def gaps (l : List ℤ) : List ℤ := ((0 :: l).zip l).map (fun p => p.2 - p.1)

def StrictlyIncreasing (l : List ℤ) : Prop := l.Pairwise (· < ·)

def Climbable (l : List ℤ) (d : ℤ) : Prop := ∀ g ∈ gaps l, g ≤ d

noncomputable def sortedUnion (S : Finset ℤ) (l : List ℤ) : List ℤ :=
  (S.val.toList ++ l).mergeSort (fun a b => decide (a ≤ b))

/-- The function returns a result r and r = (rungs[0] - 1) / dist + sum_{i=1}^{len(rungs)-1} ((rungs[i] - rungs[i-1] - 1) / dist), where / denotes integer division (floor for nonnegative operands).
  Preconditions: len(rungs) >= 1; for every i with 0 <= i < len(rungs), 1 <= rungs[i] <= 1000000000; rungs is strictly increasing (rungs[i] < rungs[i+1] for 0 <= i < len(rungs)-1); 1 <= dist <= 1000000000. -/
theorem spec_1 (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000) :
    ∃ r : Std.I64, add_rungs rungs dist = ok r ∧
      r.val = (rungAt (vals rungs) 0 - 1) / dist.val
        + ∑ i ∈ Finset.range (rungs.val.length - 1),
            ((rungAt (vals rungs) (i + 1) - rungAt (vals rungs) i - 1) / dist.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000), ∃ r : Std.I64, add_rungs rungs dist = ok r ∧
      r.val = (rungAt (vals rungs) 0 - 1) / dist.val
        + ∑ i ∈ Finset.range (rungs.val.length - 1),
            ((rungAt (vals rungs) (i + 1) - rungAt (vals rungs) i - 1) / dist.val)) := by
  sorry

/-- The function returns a result r and 0 <= r <= rungs[len(rungs)-1] - len(rungs).
  Preconditions: len(rungs) >= 1; for every i with 0 <= i < len(rungs), 1 <= rungs[i] <= 1000000000; rungs is strictly increasing; 1 <= dist <= 1000000000. -/
theorem spec_2 (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000) :
    ∃ r : Std.I64, add_rungs rungs dist = ok r ∧
      0 ≤ r.val ∧
      r.val ≤ rungAt (vals rungs) (rungs.val.length - 1) - (rungs.val.length : ℤ) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000), ∃ r : Std.I64, add_rungs rungs dist = ok r ∧
      0 ≤ r.val ∧
      r.val ≤ rungAt (vals rungs) (rungs.val.length - 1) - (rungs.val.length : ℤ)) := by
  sorry

/-- The function returns a result r and r = (rungs[0] - 1) / dist, where / denotes integer division.
  Preconditions: len(rungs) = 1; 1 <= rungs[0] <= 1000000000; 1 <= dist <= 1000000000. -/
theorem spec_3 (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : rungs.val.length = 1)
    (hbounds : 1 ≤ rungAt (vals rungs) 0 ∧ rungAt (vals rungs) 0 ≤ 1000000000)
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000) :
    ∃ r : Std.I64, add_rungs rungs dist = ok r ∧
      r.val = (rungAt (vals rungs) 0 - 1) / dist.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : rungs.val.length = 1)
    (hbounds : 1 ≤ rungAt (vals rungs) 0 ∧ rungAt (vals rungs) 0 ≤ 1000000000)
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000), ∃ r : Std.I64, add_rungs rungs dist = ok r ∧
      r.val = (rungAt (vals rungs) 0 - 1) / dist.val) := by
  sorry

/-- The function returns a result r and r = rungs[len(rungs)-1] - len(rungs).
  Preconditions: len(rungs) >= 1; for every i with 0 <= i < len(rungs), 1 <= rungs[i] <= 1000000000; rungs is strictly increasing; dist = 1. -/
theorem spec_4 (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : dist.val = 1) :
    ∃ r : Std.I64, add_rungs rungs dist = ok r ∧
      r.val = rungAt (vals rungs) (rungs.val.length - 1) - (rungs.val.length : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : dist.val = 1), ∃ r : Std.I64, add_rungs rungs dist = ok r ∧
      r.val = rungAt (vals rungs) (rungs.val.length - 1) - (rungs.val.length : ℤ)) := by
  sorry

/-- The function returns a result r and r = 0 if and only if rungs[0] <= dist and for every i with 1 <= i < len(rungs), rungs[i] - rungs[i-1] <= dist.
  Preconditions: len(rungs) >= 1; for every i with 0 <= i < len(rungs), 1 <= rungs[i] <= 1000000000; rungs is strictly increasing; 1 <= dist <= 1000000000. -/
theorem spec_5 (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000) :
    ∃ r : Std.I64, add_rungs rungs dist = ok r ∧
      (r.val = 0 ↔
        (rungAt (vals rungs) 0 ≤ dist.val ∧
          ∀ i, 1 ≤ i → i < rungs.val.length →
            rungAt (vals rungs) i - rungAt (vals rungs) (i - 1) ≤ dist.val)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000), ∃ r : Std.I64, add_rungs rungs dist = ok r ∧
      (r.val = 0 ↔
        (rungAt (vals rungs) 0 ≤ dist.val ∧
          ∀ i, 1 ≤ i → i < rungs.val.length →
            rungAt (vals rungs) i - rungAt (vals rungs) (i - 1) ≤ dist.val))) := by
  sorry

/-- The function returns a result r and there exists a finite set S of positive integers such that S is disjoint from {rungs[0], ..., rungs[len(rungs)-1]}, |S| = r, and if L is the sorted list of the union of S and the rungs, then L[0] <= dist and every adjacent difference L[j+1] - L[j] <= dist for 0 <= j < len(L)-1.
  Preconditions: len(rungs) >= 1; for every i with 0 <= i < len(rungs), 1 <= rungs[i] <= 1000000000; rungs is strictly increasing; 1 <= dist <= 1000000000. -/
theorem spec_6 (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000) :
    ∃ r : Std.I64, add_rungs rungs dist = ok r ∧
      ∃ S : Finset ℤ, (∀ x ∈ S, 0 < x) ∧
        (∀ x ∈ S, x ∉ vals rungs) ∧
        (S.card : ℤ) = r.val ∧
        Climbable (sortedUnion S (vals rungs)) dist.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000), ∃ r : Std.I64, add_rungs rungs dist = ok r ∧
      ∃ S : Finset ℤ, (∀ x ∈ S, 0 < x) ∧
        (∀ x ∈ S, x ∉ vals rungs) ∧
        (S.card : ℤ) = r.val ∧
        Climbable (sortedUnion S (vals rungs)) dist.val) := by
  sorry

/-- The function returns a result r and for every finite set S of positive integers disjoint from the rungs, if inserting S makes the ladder climbable (i.e., in the sorted union L, L[0] <= dist and every adjacent difference L[j+1] - L[j] <= dist), then |S| >= r.
  Preconditions: len(rungs) >= 1; for every i with 0 <= i < len(rungs), 1 <= rungs[i] <= 1000000000; rungs is strictly increasing; 1 <= dist <= 1000000000. -/
theorem spec_7 (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000) :
    ∃ r : Std.I64, add_rungs rungs dist = ok r ∧
      ∀ S : Finset ℤ, (∀ x ∈ S, 0 < x) → (∀ x ∈ S, x ∉ vals rungs) →
        Climbable (sortedUnion S (vals rungs)) dist.val → r.val ≤ (S.card : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000), ∃ r : Std.I64, add_rungs rungs dist = ok r ∧
      ∀ S : Finset ℤ, (∀ x ∈ S, 0 < x) → (∀ x ∈ S, x ∉ vals rungs) →
        Climbable (sortedUnion S (vals rungs)) dist.val → r.val ≤ (S.card : ℤ)) := by
  sorry

/-- The function returns a result r (it does not overflow, panic, or go out of bounds).
  Preconditions: len(rungs) >= 1; for every i with 0 <= i < len(rungs), 1 <= rungs[i] <= 1000000000; rungs is strictly increasing; 1 <= dist <= 1000000000. -/
theorem spec_8 (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000) :
    ∃ r : Std.I64, add_rungs rungs dist = ok r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000), ∃ r : Std.I64, add_rungs rungs dist = ok r) := by
  sorry

/-- If the function returns r1 for (rungs, dist1) and r2 for (rungs, dist2), then r2 <= r1.
  Preconditions: len(rungs) >= 1; for every i with 0 <= i < len(rungs), 1 <= rungs[i] <= 1000000000; rungs is strictly increasing; let dist1 and dist2 be integers with 1 <= dist1 <= dist2 <= 1000000000. -/
theorem spec_9 (rungs : Slice Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (dist1 dist2 : Std.I64)
    (h1 : 1 ≤ dist1.val) (h12 : dist1.val ≤ dist2.val) (h2 : dist2.val ≤ 1000000000)
    (r1 r2 : Std.I64)
    (hr1 : add_rungs rungs dist1 = ok r1) (hr2 : add_rungs rungs dist2 = ok r2) :
    r2.val ≤ r1.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (rungs : Slice Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (dist1 dist2 : Std.I64)
    (h1 : 1 ≤ dist1.val) (h12 : dist1.val ≤ dist2.val) (h2 : dist2.val ≤ 1000000000)
    (r1 r2 : Std.I64)
    (hr1 : add_rungs rungs dist1 = ok r1) (hr2 : add_rungs rungs dist2 = ok r2), r2.val ≤ r1.val) := by
  sorry

/-- Let rungs' = rungs ++ [h]. If the function returns r for (rungs, dist) and r' for (rungs', dist), then r' = r.
  Preconditions: len(rungs) >= 1; for every i with 0 <= i < len(rungs), 1 <= rungs[i] <= 1000000000; rungs is strictly increasing; 1 <= dist <= 1000000000; let h be an integer with rungs[len(rungs)-1] < h <= rungs[len(rungs)-1] + dist and h <= 1000000000. -/
theorem spec_10 (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000)
    (h : Std.I64)
    (h1 : rungAt (vals rungs) (rungs.val.length - 1) < h.val)
    (h2 : h.val ≤ rungAt (vals rungs) (rungs.val.length - 1) + dist.val)
    (h3 : h.val ≤ 1000000000)
    (rungs' : Slice Std.I64)
    (hrungs' : rungs'.val = rungs.val ++ [h])
    (r r' : Std.I64)
    (hr : add_rungs rungs dist = ok r) (hr' : add_rungs rungs' dist = ok r') :
    r'.val = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000)
    (h : Std.I64)
    (h1 : rungAt (vals rungs) (rungs.val.length - 1) < h.val)
    (h2 : h.val ≤ rungAt (vals rungs) (rungs.val.length - 1) + dist.val)
    (h3 : h.val ≤ 1000000000)
    (rungs' : Slice Std.I64)
    (hrungs' : rungs'.val = rungs.val ++ [h])
    (r r' : Std.I64)
    (hr : add_rungs rungs dist = ok r) (hr' : add_rungs rungs' dist = ok r'), r'.val = r.val) := by
  sorry

/-- Let rungs' be a strictly increasing array of positive integers, each at most 1000000000, such that every element of rungs occurs in rungs' and rungs'[len(rungs')-1] = rungs[len(rungs)-1]. If the function returns r for (rungs, dist) and r' for (rungs', dist), then r' <= r.
  Preconditions: len(rungs) >= 1; for every i with 0 <= i < len(rungs), 1 <= rungs[i] <= 1000000000; rungs is strictly increasing; 1 <= dist <= 1000000000; rungs' is strictly increasing; every element of rungs' is a positive integer <= 1000000000; rungs is a subsequence of rungs'; and rungs'[len(rungs')-1] = rungs[len(rungs)-1]. -/
theorem spec_11 (rungs rungs' : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000)
    (hinc' : StrictlyIncreasing (vals rungs'))
    (hbounds' : ∀ x ∈ vals rungs', 0 < x ∧ x ≤ 1000000000)
    (hsub : (vals rungs).Sublist (vals rungs'))
    (hlast : rungAt (vals rungs') (rungs'.val.length - 1)
      = rungAt (vals rungs) (rungs.val.length - 1))
    (r r' : Std.I64)
    (hr : add_rungs rungs dist = ok r) (hr' : add_rungs rungs' dist = ok r') :
    r'.val ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (rungs rungs' : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000)
    (hinc' : StrictlyIncreasing (vals rungs'))
    (hbounds' : ∀ x ∈ vals rungs', 0 < x ∧ x ≤ 1000000000)
    (hsub : (vals rungs).Sublist (vals rungs'))
    (hlast : rungAt (vals rungs') (rungs'.val.length - 1)
      = rungAt (vals rungs) (rungs.val.length - 1))
    (r r' : Std.I64)
    (hr : add_rungs rungs dist = ok r) (hr' : add_rungs rungs' dist = ok r'), r'.val ≤ r.val) := by
  sorry

/-- The function returns a result r and r >= the number of indices i with 0 <= i < len(rungs) such that g_i > dist, where g_0 = rungs[0] and g_i = rungs[i] - rungs[i-1] for 1 <= i < len(rungs).
  Preconditions: len(rungs) >= 1; for every i with 0 <= i < len(rungs), 1 <= rungs[i] <= 1000000000; rungs is strictly increasing; 1 <= dist <= 1000000000. -/
theorem spec_12 (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000) :
    ∃ r : Std.I64, add_rungs rungs dist = ok r ∧
      (((Finset.range rungs.val.length).filter
          (fun i => dist.val < rungAt (gaps (vals rungs)) i)).card : ℤ) ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (rungs : Slice Std.I64) (dist : Std.I64)
    (hlen : 1 ≤ rungs.val.length)
    (hbounds : ∀ i, i < rungs.val.length →
      1 ≤ rungAt (vals rungs) i ∧ rungAt (vals rungs) i ≤ 1000000000)
    (hinc : StrictlyIncreasing (vals rungs))
    (hdist : 1 ≤ dist.val ∧ dist.val ≤ 1000000000), ∃ r : Std.I64, add_rungs rungs dist = ok r ∧
      (((Finset.range rungs.val.length).filter
          (fun i => dist.val < rungAt (gaps (vals rungs)) i)).card : ℤ) ≤ r.val) := by
  sorry

end AegisSpec.AddRungs
