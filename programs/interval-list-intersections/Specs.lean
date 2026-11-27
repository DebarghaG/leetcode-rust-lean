import Mathlib
import Aegis.IntervalIntersection.Code.Funs

/-!
# Specifications of `Aegis.IntervalIntersection.interval_intersection`

LeetCode problem `interval-list-intersections`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IntervalIntersection

  abbrev I64Vec : Type := alloc.vec.Vec Std.I64

  abbrev I64VecVec : Type := alloc.vec.Vec (alloc.vec.Vec Std.I64)

  abbrev I64VecSlice : Type := Slice (alloc.vec.Vec Std.I64)

  def lo (v : I64Vec) : Int := v.val[0]!.val

  def hi (v : I64Vec) : Int := v.val[1]!.val

  def WellFormedInterval (v : I64Vec) : Prop :=
    v.val.length = 2 ∧ 0 ≤ lo v ∧ lo v ≤ hi v ∧ hi v ≤ 1000000000

  def WellFormed (l : I64VecSlice) : Prop :=
    ∀ v ∈ l.val, WellFormedInterval v

  def SortedDisjoint (l : I64VecSlice) : Prop :=
    ∀ i : Nat, i + 1 < l.val.length → hi (l.val[i]!) < lo (l.val[i+1]!)

  /-- Let r be the result returned by the function. Then: (1) for every k with 0 <= k < len(r), len(r[k])=2 and r[k][0] <= r[k][1]; (2) for every k with 0 <= k < len(r), there exist i,j with 0 <= i < len(firstList) and 0 <= j < len(secondList) such that r[k][0] = max(firstList[i][0], secondList[j][0]) and r[k][1] = min(firstList[i][1], secondList[j][1]); (3) for every i,j with 0 <= i < len(firstList), 0 <= j < len(secondList), and max(firstList[i][0], secondList[j][0]) <= min(firstList[i][1], secondList[j][1]), there is exactly one k with 0 <= k < len(r) such that r[k][0] = max(firstList[i][0], secondList[j][0]) and r[k][1] = min(firstList[i][1], secondList[j][1]); (4) for every k with 0 <= k+1 < len(r), r[k][1] < r[k+1][0].
    Preconditions: Every vector v occurring in firstList or secondList has len(v)=2 and 0 <= v[0] <= v[1] <= 1000000000; len(firstList) <= 1000, len(secondList) <= 1000, and len(firstList)+len(secondList) >= 1; each list is strictly sorted and pairwise disjoint: for every i with 0 <= i+1 < len(firstList), firstList[i][1] < firstList[i+1][0], and for every j with 0 <= j+1 < len(secondList), secondList[j][1] < secondList[j+1][0]. -/
  theorem spec_1 (firstList secondList : I64VecSlice)
      (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
      (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
      (hne : 1 ≤ firstList.val.length + secondList.val.length)
      (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList) :
      ∃ r : I64VecVec,
        Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧

        (∀ k : Nat, k < r.val.length →
          (r.val[k]!).val.length = 2 ∧ lo (r.val[k]!) ≤ hi (r.val[k]!)) ∧

        (∀ k : Nat, k < r.val.length →
          ∃ i j : Nat,
            i < firstList.val.length ∧ j < secondList.val.length ∧
            lo (r.val[k]!) = max (lo (firstList.val[i]!)) (lo (secondList.val[j]!)) ∧
            hi (r.val[k]!) = min (hi (firstList.val[i]!)) (hi (secondList.val[j]!))) ∧

        (∀ i j : Nat, i < firstList.val.length → j < secondList.val.length →
          max (lo (firstList.val[i]!)) (lo (secondList.val[j]!)) ≤
            min (hi (firstList.val[i]!)) (hi (secondList.val[j]!)) →
          ∃! k : Nat,
            k < r.val.length ∧
            lo (r.val[k]!) = max (lo (firstList.val[i]!)) (lo (secondList.val[j]!)) ∧
            hi (r.val[k]!) = min (hi (firstList.val[i]!)) (hi (secondList.val[j]!))) ∧

        (∀ k : Nat, k + 1 < r.val.length → hi (r.val[k]!) < lo (r.val[k+1]!)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (firstList secondList : I64VecSlice)
        (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
        (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
        (hne : 1 ≤ firstList.val.length + secondList.val.length)
        (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList), ∃ r : I64VecVec,
          Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧

          (∀ k : Nat, k < r.val.length →
            (r.val[k]!).val.length = 2 ∧ lo (r.val[k]!) ≤ hi (r.val[k]!)) ∧

          (∀ k : Nat, k < r.val.length →
            ∃ i j : Nat,
              i < firstList.val.length ∧ j < secondList.val.length ∧
              lo (r.val[k]!) = max (lo (firstList.val[i]!)) (lo (secondList.val[j]!)) ∧
              hi (r.val[k]!) = min (hi (firstList.val[i]!)) (hi (secondList.val[j]!))) ∧

          (∀ i j : Nat, i < firstList.val.length → j < secondList.val.length →
            max (lo (firstList.val[i]!)) (lo (secondList.val[j]!)) ≤
              min (hi (firstList.val[i]!)) (hi (secondList.val[j]!)) →
            ∃! k : Nat,
              k < r.val.length ∧
              lo (r.val[k]!) = max (lo (firstList.val[i]!)) (lo (secondList.val[j]!)) ∧
              hi (r.val[k]!) = min (hi (firstList.val[i]!)) (hi (secondList.val[j]!))) ∧

          (∀ k : Nat, k + 1 < r.val.length → hi (r.val[k]!) < lo (r.val[k+1]!))) := by
    sorry

  /-- Let r be the result returned by the function. For every k with 0 <= k < len(r), len(r[k])=2 and r[k][0] <= r[k][1].
    Preconditions: Every vector v occurring in firstList or secondList has len(v)=2 and 0 <= v[0] <= v[1] <= 1000000000; len(firstList) <= 1000, len(secondList) <= 1000, and len(firstList)+len(secondList) >= 1; each list is strictly sorted and pairwise disjoint: for every i with 0 <= i+1 < len(firstList), firstList[i][1] < firstList[i+1][0], and for every j with 0 <= j+1 < len(secondList), secondList[j][1] < secondList[j+1][0]. -/
  theorem spec_2 (firstList secondList : I64VecSlice)
      (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
      (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
      (hne : 1 ≤ firstList.val.length + secondList.val.length)
      (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList) :
      ∃ r : I64VecVec,
        Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
        (∀ k : Nat, k < r.val.length →
          (r.val[k]!).val.length = 2 ∧ lo (r.val[k]!) ≤ hi (r.val[k]!)) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (firstList secondList : I64VecSlice)
        (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
        (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
        (hne : 1 ≤ firstList.val.length + secondList.val.length)
        (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList), ∃ r : I64VecVec,
          Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
          (∀ k : Nat, k < r.val.length →
            (r.val[k]!).val.length = 2 ∧ lo (r.val[k]!) ≤ hi (r.val[k]!))) := by
    sorry

  /-- Let r be the result returned by the function. For every k with 0 <= k < len(r), 0 <= r[k][0] <= r[k][1] <= 1000000000.
    Preconditions: Every vector v occurring in firstList or secondList has len(v)=2 and 0 <= v[0] <= v[1] <= 1000000000; len(firstList) <= 1000, len(secondList) <= 1000, and len(firstList)+len(secondList) >= 1; each list is strictly sorted and pairwise disjoint: for every i with 0 <= i+1 < len(firstList), firstList[i][1] < firstList[i+1][0], and for every j with 0 <= j+1 < len(secondList), secondList[j][1] < secondList[j+1][0]. -/
  theorem spec_3 (firstList secondList : I64VecSlice)
      (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
      (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
      (hne : 1 ≤ firstList.val.length + secondList.val.length)
      (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList) :
      ∃ r : I64VecVec,
        Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
        (∀ k : Nat, k < r.val.length →
          0 ≤ lo (r.val[k]!) ∧ lo (r.val[k]!) ≤ hi (r.val[k]!) ∧
            hi (r.val[k]!) ≤ 1000000000) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (firstList secondList : I64VecSlice)
        (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
        (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
        (hne : 1 ≤ firstList.val.length + secondList.val.length)
        (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList), ∃ r : I64VecVec,
          Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
          (∀ k : Nat, k < r.val.length →
            0 ≤ lo (r.val[k]!) ∧ lo (r.val[k]!) ≤ hi (r.val[k]!) ∧
              hi (r.val[k]!) ≤ 1000000000)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; in particular, it does not overflow, panic, or access an out-of-bounds index.
    Preconditions: Every vector v occurring in firstList or secondList has len(v)=2 and 0 <= v[0] <= v[1] <= 1000000000; len(firstList) <= 1000, len(secondList) <= 1000, and len(firstList)+len(secondList) >= 1; each list is strictly sorted and pairwise disjoint: for every i with 0 <= i+1 < len(firstList), firstList[i][1] < firstList[i+1][0], and for every j with 0 <= j+1 < len(secondList), secondList[j][1] < secondList[j+1][0]. -/
  theorem spec_4 (firstList secondList : I64VecSlice)
      (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
      (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
      (hne : 1 ≤ firstList.val.length + secondList.val.length)
      (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList) :
      ∃ r : I64VecVec,
        Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (firstList secondList : I64VecSlice)
        (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
        (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
        (hne : 1 ≤ firstList.val.length + secondList.val.length)
        (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList), ∃ r : I64VecVec,
          Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r) := by
    sorry

  /-- Let r be the result returned by the function. For every k with 0 <= k < len(r), there exist i,j with 0 <= i < len(firstList) and 0 <= j < len(secondList) such that max(firstList[i][0], secondList[j][0]) <= min(firstList[i][1], secondList[j][1]), r[k][0] = max(firstList[i][0], secondList[j][0]), and r[k][1] = min(firstList[i][1], secondList[j][1]).
    Preconditions: Every vector v occurring in firstList or secondList has len(v)=2 and 0 <= v[0] <= v[1] <= 1000000000; len(firstList) <= 1000, len(secondList) <= 1000, and len(firstList)+len(secondList) >= 1; each list is strictly sorted and pairwise disjoint: for every i with 0 <= i+1 < len(firstList), firstList[i][1] < firstList[i+1][0], and for every j with 0 <= j+1 < len(secondList), secondList[j][1] < secondList[j+1][0]. -/
  theorem spec_5 (firstList secondList : I64VecSlice)
      (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
      (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
      (hne : 1 ≤ firstList.val.length + secondList.val.length)
      (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList) :
      ∃ r : I64VecVec,
        Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
        (∀ k : Nat, k < r.val.length →
          ∃ i j : Nat,
            i < firstList.val.length ∧ j < secondList.val.length ∧
            max (lo (firstList.val[i]!)) (lo (secondList.val[j]!)) ≤
              min (hi (firstList.val[i]!)) (hi (secondList.val[j]!)) ∧
            lo (r.val[k]!) = max (lo (firstList.val[i]!)) (lo (secondList.val[j]!)) ∧
            hi (r.val[k]!) = min (hi (firstList.val[i]!)) (hi (secondList.val[j]!))) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (firstList secondList : I64VecSlice)
        (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
        (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
        (hne : 1 ≤ firstList.val.length + secondList.val.length)
        (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList), ∃ r : I64VecVec,
          Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
          (∀ k : Nat, k < r.val.length →
            ∃ i j : Nat,
              i < firstList.val.length ∧ j < secondList.val.length ∧
              max (lo (firstList.val[i]!)) (lo (secondList.val[j]!)) ≤
                min (hi (firstList.val[i]!)) (hi (secondList.val[j]!)) ∧
              lo (r.val[k]!) = max (lo (firstList.val[i]!)) (lo (secondList.val[j]!)) ∧
              hi (r.val[k]!) = min (hi (firstList.val[i]!)) (hi (secondList.val[j]!)))) := by
    sorry

  /-- Let r be the result returned by the function. For every i,j with 0 <= i < len(firstList), 0 <= j < len(secondList), and max(firstList[i][0], secondList[j][0]) <= min(firstList[i][1], secondList[j][1]), there exists k with 0 <= k < len(r) such that r[k][0] = max(firstList[i][0], secondList[j][0]) and r[k][1] = min(firstList[i][1], secondList[j][1]).
    Preconditions: Every vector v occurring in firstList or secondList has len(v)=2 and 0 <= v[0] <= v[1] <= 1000000000; len(firstList) <= 1000, len(secondList) <= 1000, and len(firstList)+len(secondList) >= 1; each list is strictly sorted and pairwise disjoint: for every i with 0 <= i+1 < len(firstList), firstList[i][1] < firstList[i+1][0], and for every j with 0 <= j+1 < len(secondList), secondList[j][1] < secondList[j+1][0]. -/
  theorem spec_6 (firstList secondList : I64VecSlice)
      (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
      (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
      (hne : 1 ≤ firstList.val.length + secondList.val.length)
      (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList) :
      ∃ r : I64VecVec,
        Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
        (∀ i j : Nat, i < firstList.val.length → j < secondList.val.length →
          max (lo (firstList.val[i]!)) (lo (secondList.val[j]!)) ≤
            min (hi (firstList.val[i]!)) (hi (secondList.val[j]!)) →
          ∃ k : Nat,
            k < r.val.length ∧
            lo (r.val[k]!) = max (lo (firstList.val[i]!)) (lo (secondList.val[j]!)) ∧
            hi (r.val[k]!) = min (hi (firstList.val[i]!)) (hi (secondList.val[j]!))) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (firstList secondList : I64VecSlice)
        (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
        (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
        (hne : 1 ≤ firstList.val.length + secondList.val.length)
        (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList), ∃ r : I64VecVec,
          Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
          (∀ i j : Nat, i < firstList.val.length → j < secondList.val.length →
            max (lo (firstList.val[i]!)) (lo (secondList.val[j]!)) ≤
              min (hi (firstList.val[i]!)) (hi (secondList.val[j]!)) →
            ∃ k : Nat,
              k < r.val.length ∧
              lo (r.val[k]!) = max (lo (firstList.val[i]!)) (lo (secondList.val[j]!)) ∧
              hi (r.val[k]!) = min (hi (firstList.val[i]!)) (hi (secondList.val[j]!)))) := by
    sorry

  /-- Let r be the result returned by the function. For every k with 0 <= k+1 < len(r), r[k][1] < r[k+1][0].
    Preconditions: Every vector v occurring in firstList or secondList has len(v)=2 and 0 <= v[0] <= v[1] <= 1000000000; len(firstList) <= 1000, len(secondList) <= 1000, and len(firstList)+len(secondList) >= 1; each list is strictly sorted and pairwise disjoint: for every i with 0 <= i+1 < len(firstList), firstList[i][1] < firstList[i+1][0], and for every j with 0 <= j+1 < len(secondList), secondList[j][1] < secondList[j+1][0]. -/
  theorem spec_7 (firstList secondList : I64VecSlice)
      (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
      (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
      (hne : 1 ≤ firstList.val.length + secondList.val.length)
      (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList) :
      ∃ r : I64VecVec,
        Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
        (∀ k : Nat, k + 1 < r.val.length → hi (r.val[k]!) < lo (r.val[k+1]!)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (firstList secondList : I64VecSlice)
        (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
        (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
        (hne : 1 ≤ firstList.val.length + secondList.val.length)
        (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList), ∃ r : I64VecVec,
          Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
          (∀ k : Nat, k + 1 < r.val.length → hi (r.val[k]!) < lo (r.val[k+1]!))) := by
    sorry

  /-- Let r be the result returned by the function. For every real number x, x belongs to at least one returned closed interval [r[k][0], r[k][1]] with 0 <= k < len(r) if and only if there exist i,j with 0 <= i < len(firstList) and 0 <= j < len(secondList) such that firstList[i][0] <= x <= firstList[i][1] and secondList[j][0] <= x <= secondList[j][1].
    Preconditions: Every vector v occurring in firstList or secondList has len(v)=2 and 0 <= v[0] <= v[1] <= 1000000000; len(firstList) <= 1000, len(secondList) <= 1000, and len(firstList)+len(secondList) >= 1; each list is strictly sorted and pairwise disjoint: for every i with 0 <= i+1 < len(firstList), firstList[i][1] < firstList[i+1][0], and for every j with 0 <= j+1 < len(secondList), secondList[j][1] < secondList[j+1][0]. -/
  theorem spec_8 (firstList secondList : I64VecSlice)
      (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
      (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
      (hne : 1 ≤ firstList.val.length + secondList.val.length)
      (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList) :
      ∃ r : I64VecVec,
        Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
        (∀ x : ℝ,
          (∃ k : Nat,
              k < r.val.length ∧ (lo (r.val[k]!) : ℝ) ≤ x ∧ x ≤ (hi (r.val[k]!) : ℝ)) ↔
          (∃ i j : Nat,
            i < firstList.val.length ∧ j < secondList.val.length ∧
            (lo (firstList.val[i]!) : ℝ) ≤ x ∧ x ≤ (hi (firstList.val[i]!) : ℝ) ∧
            (lo (secondList.val[j]!) : ℝ) ≤ x ∧ x ≤ (hi (secondList.val[j]!) : ℝ))) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (firstList secondList : I64VecSlice)
        (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
        (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
        (hne : 1 ≤ firstList.val.length + secondList.val.length)
        (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList), ∃ r : I64VecVec,
          Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
          (∀ x : ℝ,
            (∃ k : Nat,
                k < r.val.length ∧ (lo (r.val[k]!) : ℝ) ≤ x ∧ x ≤ (hi (r.val[k]!) : ℝ)) ↔
            (∃ i j : Nat,
              i < firstList.val.length ∧ j < secondList.val.length ∧
              (lo (firstList.val[i]!) : ℝ) ≤ x ∧ x ≤ (hi (firstList.val[i]!) : ℝ) ∧
              (lo (secondList.val[j]!) : ℝ) ≤ x ∧ x ≤ (hi (secondList.val[j]!) : ℝ)))) := by
    sorry

  /-- Let r be the result returned by the function. Then len(r) <= len(firstList)+len(secondList).
    Preconditions: Every vector v occurring in firstList or secondList has len(v)=2 and 0 <= v[0] <= v[1] <= 1000000000; len(firstList) <= 1000, len(secondList) <= 1000, and len(firstList)+len(secondList) >= 1; each list is strictly sorted and pairwise disjoint: for every i with 0 <= i+1 < len(firstList), firstList[i][1] < firstList[i+1][0], and for every j with 0 <= j+1 < len(secondList), secondList[j][1] < secondList[j+1][0]. -/
  theorem spec_9 (firstList secondList : I64VecSlice)
      (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
      (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
      (hne : 1 ≤ firstList.val.length + secondList.val.length)
      (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList) :
      ∃ r : I64VecVec,
        Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
        r.val.length ≤ firstList.val.length + secondList.val.length := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (firstList secondList : I64VecSlice)
        (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
        (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
        (hne : 1 ≤ firstList.val.length + secondList.val.length)
        (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList), ∃ r : I64VecVec,
          Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
          r.val.length ≤ firstList.val.length + secondList.val.length) := by
    sorry

  /-- Let r be the result returned by the function. Then len(r)=0 if and only if for every i,j with 0 <= i < len(firstList) and 0 <= j < len(secondList), max(firstList[i][0], secondList[j][0]) > min(firstList[i][1], secondList[j][1]).
    Preconditions: Every vector v occurring in firstList or secondList has len(v)=2 and 0 <= v[0] <= v[1] <= 1000000000; len(firstList) <= 1000, len(secondList) <= 1000, and len(firstList)+len(secondList) >= 1; each list is strictly sorted and pairwise disjoint: for every i with 0 <= i+1 < len(firstList), firstList[i][1] < firstList[i+1][0], and for every j with 0 <= j+1 < len(secondList), secondList[j][1] < secondList[j+1][0]. -/
  theorem spec_10 (firstList secondList : I64VecSlice)
      (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
      (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
      (hne : 1 ≤ firstList.val.length + secondList.val.length)
      (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList) :
      ∃ r : I64VecVec,
        Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
        (r.val.length = 0 ↔
          ∀ i j : Nat, i < firstList.val.length → j < secondList.val.length →
            max (lo (firstList.val[i]!)) (lo (secondList.val[j]!)) >
              min (hi (firstList.val[i]!)) (hi (secondList.val[j]!))) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (firstList secondList : I64VecSlice)
        (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
        (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
        (hne : 1 ≤ firstList.val.length + secondList.val.length)
        (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList), ∃ r : I64VecVec,
          Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
          (r.val.length = 0 ↔
            ∀ i j : Nat, i < firstList.val.length → j < secondList.val.length →
              max (lo (firstList.val[i]!)) (lo (secondList.val[j]!)) >
                min (hi (firstList.val[i]!)) (hi (secondList.val[j]!)))) := by
    sorry

  /-- Let r be the result returned by the function. For every k with 0 <= k < len(r), there exist i,j with 0 <= i < len(firstList) and 0 <= j < len(secondList) such that firstList[i][0] <= r[k][0] <= r[k][1] <= firstList[i][1] and secondList[j][0] <= r[k][0] <= r[k][1] <= secondList[j][1].
    Preconditions: Every vector v occurring in firstList or secondList has len(v)=2 and 0 <= v[0] <= v[1] <= 1000000000; len(firstList) <= 1000, len(secondList) <= 1000, and len(firstList)+len(secondList) >= 1; each list is strictly sorted and pairwise disjoint: for every i with 0 <= i+1 < len(firstList), firstList[i][1] < firstList[i+1][0], and for every j with 0 <= j+1 < len(secondList), secondList[j][1] < secondList[j+1][0]. -/
  theorem spec_11 (firstList secondList : I64VecSlice)
      (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
      (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
      (hne : 1 ≤ firstList.val.length + secondList.val.length)
      (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList) :
      ∃ r : I64VecVec,
        Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
        (∀ k : Nat, k < r.val.length →
          ∃ i j : Nat,
            i < firstList.val.length ∧ j < secondList.val.length ∧
            lo (firstList.val[i]!) ≤ lo (r.val[k]!) ∧
            lo (r.val[k]!) ≤ hi (r.val[k]!) ∧
            hi (r.val[k]!) ≤ hi (firstList.val[i]!) ∧
            lo (secondList.val[j]!) ≤ lo (r.val[k]!) ∧
            lo (r.val[k]!) ≤ hi (r.val[k]!) ∧
            hi (r.val[k]!) ≤ hi (secondList.val[j]!)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (firstList secondList : I64VecSlice)
        (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
        (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
        (hne : 1 ≤ firstList.val.length + secondList.val.length)
        (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList), ∃ r : I64VecVec,
          Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
          (∀ k : Nat, k < r.val.length →
            ∃ i j : Nat,
              i < firstList.val.length ∧ j < secondList.val.length ∧
              lo (firstList.val[i]!) ≤ lo (r.val[k]!) ∧
              lo (r.val[k]!) ≤ hi (r.val[k]!) ∧
              hi (r.val[k]!) ≤ hi (firstList.val[i]!) ∧
              lo (secondList.val[j]!) ≤ lo (r.val[k]!) ∧
              lo (r.val[k]!) ≤ hi (r.val[k]!) ∧
              hi (r.val[k]!) ≤ hi (secondList.val[j]!))) := by
    sorry

  /-- Let r1 be the result of interval_intersection(firstList, secondList) and let r2 be the result of interval_intersection(secondList, firstList). Both calls return results; moreover len(r1)=len(r2), and for every k with 0 <= k < len(r1), r1[k][0]=r2[k][0] and r1[k][1]=r2[k][1].
    Preconditions: Every vector v occurring in firstList or secondList has len(v)=2 and 0 <= v[0] <= v[1] <= 1000000000; len(firstList) <= 1000, len(secondList) <= 1000, and len(firstList)+len(secondList) >= 1; each list is strictly sorted and pairwise disjoint: for every i with 0 <= i+1 < len(firstList), firstList[i][1] < firstList[i+1][0], and for every j with 0 <= j+1 < len(secondList), secondList[j][1] < secondList[j+1][0]. -/
  theorem spec_12 (firstList secondList : I64VecSlice)
      (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
      (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
      (hne : 1 ≤ firstList.val.length + secondList.val.length)
      (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList) :
      ∃ r1 r2 : I64VecVec,
        Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r1 ∧
        Aegis.IntervalIntersection.interval_intersection secondList firstList = ok r2 ∧
        r1.val.length = r2.val.length ∧
        (∀ k : Nat, k < r1.val.length →
          lo (r1.val[k]!) = lo (r2.val[k]!) ∧ hi (r1.val[k]!) = hi (r2.val[k]!)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (firstList secondList : I64VecSlice)
        (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
        (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
        (hne : 1 ≤ firstList.val.length + secondList.val.length)
        (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList), ∃ r1 r2 : I64VecVec,
          Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r1 ∧
          Aegis.IntervalIntersection.interval_intersection secondList firstList = ok r2 ∧
          r1.val.length = r2.val.length ∧
          (∀ k : Nat, k < r1.val.length →
            lo (r1.val[k]!) = lo (r2.val[k]!) ∧ hi (r1.val[k]!) = hi (r2.val[k]!))) := by
    sorry

  /-- Let r be the result returned by the function. Then len(r) <= len(firstList)+len(secondList)-1.
    Preconditions: Every vector v occurring in firstList or secondList has len(v)=2 and 0 <= v[0] <= v[1] <= 1000000000; len(firstList) <= 1000, len(secondList) <= 1000, and len(firstList)+len(secondList) >= 1; each list is strictly sorted and pairwise disjoint: for every i with 0 <= i+1 < len(firstList), firstList[i][1] < firstList[i+1][0], and for every j with 0 <= j+1 < len(secondList), secondList[j][1] < secondList[j+1][0]. -/
  theorem spec_13 (firstList secondList : I64VecSlice)
      (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
      (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
      (hne : 1 ≤ firstList.val.length + secondList.val.length)
      (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList) :
      ∃ r : I64VecVec,
        Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
        r.val.length ≤ firstList.val.length + secondList.val.length - 1 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (firstList secondList : I64VecSlice)
        (hWF1 : WellFormed firstList) (hWF2 : WellFormed secondList)
        (hlen1 : firstList.val.length ≤ 1000) (hlen2 : secondList.val.length ≤ 1000)
        (hne : 1 ≤ firstList.val.length + secondList.val.length)
        (hsorted1 : SortedDisjoint firstList) (hsorted2 : SortedDisjoint secondList), ∃ r : I64VecVec,
          Aegis.IntervalIntersection.interval_intersection firstList secondList = ok r ∧
          r.val.length ≤ firstList.val.length + secondList.val.length - 1) := by
    sorry

  end AegisSpec.IntervalIntersection
