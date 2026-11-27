import Aegis.RemoveCoveredIntervals.Code.Funs

/-!
# Specifications of `Aegis.RemoveCoveredIntervals.remove_covered_intervals`

LeetCode problem `remove-covered-intervals`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.RemoveCoveredIntervals

  namespace AegisSpec.RemoveCoveredIntervals

  def content (intervals : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    intervals.val.map (fun v => v.val.map (fun x => x.val))

  def ivs (intervals : Slice (alloc.vec.Vec Std.I64)) : List (ℤ × ℤ) :=
    (content intervals).map (fun l => (l.getD 0 0, l.getD 1 0))

  def WellFormed (intervals : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ l ∈ content intervals, l.length = 2

  def EndpointsInRange (L : List (ℤ × ℤ)) : Prop :=
    ∀ p ∈ L, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 100000

  def PairwiseDistinct (L : List (ℤ × ℤ)) : Prop := L.Nodup

  def ValidInput (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) : Prop :=
    intervals.val.length = n ∧ WellFormed intervals ∧ 1 ≤ n ∧ n ≤ 1000 ∧
      EndpointsInRange (ivs intervals) ∧ PairwiseDistinct (ivs intervals)

  def Covers (a b : ℤ × ℤ) : Prop := a.1 ≤ b.1 ∧ b.2 ≤ a.2

  def coversB (a b : ℤ × ℤ) : Bool := a.1 ≤ b.1 && b.2 ≤ a.2

  lemma coversB_eq_true (a b : ℤ × ℤ) : coversB a b = true ↔ Covers a b := by
    simp [coversB, Covers]

  def Covered (L : List (ℤ × ℤ)) (i : ℕ) : Prop :=
    ∃ j ∈ List.range L.length, j ≠ i ∧ Covers (L.getD j (0, 0)) (L.getD i (0, 0))

  def coveredB (L : List (ℤ × ℤ)) (i : ℕ) : Bool :=
    (List.range L.length).any
      (fun j => decide (j ≠ i) && coversB (L.getD j (0, 0)) (L.getD i (0, 0)))

  lemma coveredB_eq_true (L : List (ℤ × ℤ)) (i : ℕ) : coveredB L i = true ↔ Covered L i := by
    unfold coveredB Covered
    rw [List.any_eq_true]
    constructor
    · rintro ⟨j, hj, hp⟩
      rw [Bool.and_eq_true, coversB_eq_true] at hp
      exact ⟨j, hj, decide_eq_true_iff.mp hp.1, hp.2⟩
    · rintro ⟨j, hj, hne, hcov⟩
      refine ⟨j, hj, ?_⟩
      rw [Bool.and_eq_true, coversB_eq_true]
      exact ⟨decide_eq_true_iff.mpr hne, hcov⟩

  def uncoveredCount (L : List (ℤ × ℤ)) : ℕ :=
    (List.range L.length).countP (fun i => coveredB L i == false)

  def numDistinctLeft (L : List (ℤ × ℤ)) : ℕ := (L.map (fun p => p.1)).dedup.length

  def numDistinctRight (L : List (ℤ × ℤ)) : ℕ := (L.map (fun p => p.2)).dedup.length

  def CoversAllOthers (L : List (ℤ × ℤ)) (i : ℕ) : Prop :=
    ∀ j ∈ List.range L.length, j ≠ i → Covers (L.getD i (0, 0)) (L.getD j (0, 0))

  def newlyCoveredCount (L : List (ℤ × ℤ)) (p : ℤ × ℤ) : ℕ :=
    (List.range L.length).countP
      (fun i => (coveredB L i == false) && coversB p (L.getD i (0, 0)))

  /-- Write covered(i) to mean: there exists j with 0 <= j < n, j != i, such that l_j <= l_i and r_i <= r_j. The function returns a result r, and r = |{ i | 0 <= i < n and not covered(i) }|, i.e., r is exactly the number of intervals that are not covered by any other interval in the list.
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 1000. For each i with 0 <= i < n, write l_i = intervals[i][0] and r_i = intervals[i][1]; assume len(intervals[i]) = 2, 0 <= l_i < r_i <= 100000. Also assume the intervals are pairwise distinct: for i != j, (l_i, r_i) != (l_j, r_j). -/
  theorem spec_1 (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (h : ValidInput intervals n) :
      ∃ r : Std.I64, remove_covered_intervals intervals = ok r ∧
        r.val = (uncoveredCount (ivs intervals) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (h : ValidInput intervals n), ∃ r : Std.I64, remove_covered_intervals intervals = ok r ∧
          r.val = (uncoveredCount (ivs intervals) : ℤ)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or get stuck).
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 1000. For each i with 0 <= i < n, write l_i = intervals[i][0] and r_i = intervals[i][1]; assume len(intervals[i]) = 2, 0 <= l_i < r_i <= 100000. Also assume the intervals are pairwise distinct: for i != j, (l_i, r_i) != (l_j, r_j). -/
  theorem spec_2 (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (h : ValidInput intervals n) :
      ∃ r : Std.I64, remove_covered_intervals intervals = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (h : ValidInput intervals n), ∃ r : Std.I64, remove_covered_intervals intervals = ok r) := by
    sorry

  /-- The function returns a result r, and 1 <= r <= n.
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 1000. For each i with 0 <= i < n, write l_i = intervals[i][0] and r_i = intervals[i][1]; assume len(intervals[i]) = 2, 0 <= l_i < r_i <= 100000. Also assume the intervals are pairwise distinct: for i != j, (l_i, r_i) != (l_j, r_j). -/
  theorem spec_3 (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (h : ValidInput intervals n) :
      ∃ r : Std.I64, remove_covered_intervals intervals = ok r ∧
        1 ≤ r.val ∧ r.val ≤ (n : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (h : ValidInput intervals n), ∃ r : Std.I64, remove_covered_intervals intervals = ok r ∧
          1 ≤ r.val ∧ r.val ≤ (n : ℤ)) := by
    sorry

  /-- Let D_L = |{ l_i | 0 <= i < n }| be the number of distinct left endpoints among the intervals. The function returns a result r with r <= D_L.
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 1000. For each i with 0 <= i < n, write l_i = intervals[i][0] and r_i = intervals[i][1]; assume len(intervals[i]) = 2, 0 <= l_i < r_i <= 100000. Also assume the intervals are pairwise distinct: for i != j, (l_i, r_i) != (l_j, r_j). -/
  theorem spec_4 (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (h : ValidInput intervals n) :
      ∃ r : Std.I64, remove_covered_intervals intervals = ok r ∧
        r.val ≤ (numDistinctLeft (ivs intervals) : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (h : ValidInput intervals n), ∃ r : Std.I64, remove_covered_intervals intervals = ok r ∧
          r.val ≤ (numDistinctLeft (ivs intervals) : ℤ)) := by
    sorry

  /-- Let D_R = |{ r_i | 0 <= i < n }| be the number of distinct right endpoints among the intervals. The function returns a result r with r <= D_R.
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 1000. For each i with 0 <= i < n, write l_i = intervals[i][0] and r_i = intervals[i][1]; assume len(intervals[i]) = 2, 0 <= l_i < r_i <= 100000. Also assume the intervals are pairwise distinct: for i != j, (l_i, r_i) != (l_j, r_j). -/
  theorem spec_5 (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (h : ValidInput intervals n) :
      ∃ r : Std.I64, remove_covered_intervals intervals = ok r ∧
        r.val ≤ (numDistinctRight (ivs intervals) : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (h : ValidInput intervals n), ∃ r : Std.I64, remove_covered_intervals intervals = ok r ∧
          r.val ≤ (numDistinctRight (ivs intervals) : ℤ)) := by
    sorry

  /-- If the function returns r on intervals and r' on intervals', then r = r'.
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 1000. For each i with 0 <= i < n, write l_i = intervals[i][0] and r_i = intervals[i][1]; assume len(intervals[i]) = 2, 0 <= l_i < r_i <= 100000. Also assume the intervals are pairwise distinct: for i != j, (l_i, r_i) != (l_j, r_j). Let intervals' be another input with len(intervals') = n satisfying the same preconditions, and suppose there exists a bijection p from {0,...,n-1} to {0,...,n-1} such that for every i, intervals'[p(i)][0] = l_i and intervals'[p(i)][1] = r_i. -/
  theorem spec_6 (intervals intervals' : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (h : ValidInput intervals n) (h' : ValidInput intervals' n)
      (p : Fin n ≃ Fin n)
      (hp : ∀ i : Fin n,
        (ivs intervals').getD (p i).val (0, 0) = (ivs intervals).getD i.val (0, 0))
      {r r' : Std.I64} (hr : remove_covered_intervals intervals = ok r)
      (hr' : remove_covered_intervals intervals' = ok r') :
      r = r' := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (intervals intervals' : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (h : ValidInput intervals n) (h' : ValidInput intervals' n)
        (p : Fin n ≃ Fin n)
        (hp : ∀ i : Fin n,
          (ivs intervals').getD (p i).val (0, 0) = (ivs intervals).getD i.val (0, 0))
        {r r' : Std.I64} (hr : remove_covered_intervals intervals = ok r)
        (hr' : remove_covered_intervals intervals' = ok r'), r = r') := by
    sorry

  /-- The function returns a result r. Then r = 1 if and only if there exists an index i with 0 <= i < n such that for every j with 0 <= j < n and j != i, l_i <= l_j and r_j <= r_i (i.e., interval i covers every other interval).
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 1000. For each i with 0 <= i < n, write l_i = intervals[i][0] and r_i = intervals[i][1]; assume len(intervals[i]) = 2, 0 <= l_i < r_i <= 100000. Also assume the intervals are pairwise distinct: for i != j, (l_i, r_i) != (l_j, r_j). -/
  theorem spec_7 (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (h : ValidInput intervals n) {r : Std.I64}
      (hr : remove_covered_intervals intervals = ok r) :
      (r.val = 1 ↔ ∃ i ∈ List.range n, CoversAllOthers (ivs intervals) i) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (h : ValidInput intervals n) {r : Std.I64}
        (hr : remove_covered_intervals intervals = ok r), (r.val = 1 ↔ ∃ i ∈ List.range n, CoversAllOthers (ivs intervals) i)) := by
    sorry

  /-- If the function returns r on intervals and r' on intervals', then r' = r + 1.
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 999. For each i with 0 <= i < n, write l_i = intervals[i][0] and r_i = intervals[i][1]; assume len(intervals[i]) = 2, 0 <= l_i < r_i <= 100000. Also assume the intervals are pairwise distinct: for i != j, (l_i, r_i) != (l_j, r_j). Let a, b be integers with 0 <= a < b <= 100000. Suppose for all i, not (a <= l_i and r_i <= b) and not (l_i <= a and b <= r_i). Also suppose (a,b) is distinct from all existing intervals. Let intervals' be any slice of length n+1 satisfying the preconditions (so 1 <= n+1 <= 1000, endpoints in range, pairwise distinct) that contains exactly the n original intervals plus (a,b). -/
  theorem spec_8 (intervals intervals' : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (h : ValidInput intervals n) (hn : n ≤ 999)
      (a b : ℤ) (hab : 0 ≤ a ∧ a < b ∧ b ≤ 100000)
      (hfresh : ∀ i ∈ List.range n, (ivs intervals).getD i (0, 0) ≠ (a, b))
      (hincomp : ∀ i ∈ List.range n,
        ¬ Covers (a, b) ((ivs intervals).getD i (0, 0)) ∧
          ¬ Covers ((ivs intervals).getD i (0, 0)) (a, b))
      (h' : ValidInput intervals' (n + 1))
      (hperm : (ivs intervals').Perm ((a, b) :: ivs intervals))
      {r r' : Std.I64} (hr : remove_covered_intervals intervals = ok r)
      (hr' : remove_covered_intervals intervals' = ok r') :
      r'.val = r.val + 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (intervals intervals' : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (h : ValidInput intervals n) (hn : n ≤ 999)
        (a b : ℤ) (hab : 0 ≤ a ∧ a < b ∧ b ≤ 100000)
        (hfresh : ∀ i ∈ List.range n, (ivs intervals).getD i (0, 0) ≠ (a, b))
        (hincomp : ∀ i ∈ List.range n,
          ¬ Covers (a, b) ((ivs intervals).getD i (0, 0)) ∧
            ¬ Covers ((ivs intervals).getD i (0, 0)) (a, b))
        (h' : ValidInput intervals' (n + 1))
        (hperm : (ivs intervals').Perm ((a, b) :: ivs intervals))
        {r r' : Std.I64} (hr : remove_covered_intervals intervals = ok r)
        (hr' : remove_covered_intervals intervals' = ok r'), r'.val = r.val + 1) := by
    sorry

  /-- If the function returns r on intervals and r' on intervals', then r' = r + 1 - |C|. This gives the exact insertion effect when the new interval is uncovered and may cover some previously uncovered existing intervals.
    Preconditions: Let n = len(intervals). Assume 1 <= n <= 999. For each i with 0 <= i < n, write l_i = intervals[i][0] and r_i = intervals[i][1]; assume len(intervals[i]) = 2, 0 <= l_i < r_i <= 100000. Also assume the intervals are pairwise distinct: for i != j, (l_i, r_i) != (l_j, r_j). Let a, b be integers with 0 <= a < b <= 100000, with (a,b) distinct from all existing intervals, and suppose no existing interval covers (a,b): for all i, not (l_i <= a and b <= r_i). Let C = { i | 0 <= i < n, interval i is not covered by any other original interval, and a <= l_i and r_i <= b }. Let intervals' be any slice of length n+1 satisfying the preconditions that contains exactly the n original intervals plus (a,b). -/
  theorem spec_9 (intervals intervals' : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (h : ValidInput intervals n) (hn : n ≤ 999)
      (a b : ℤ) (hab : 0 ≤ a ∧ a < b ∧ b ≤ 100000)
      (hfresh : ∀ i ∈ List.range n, (ivs intervals).getD i (0, 0) ≠ (a, b))
      (huncovered : ∀ i ∈ List.range n,
        ¬ Covers ((ivs intervals).getD i (0, 0)) (a, b))
      (h' : ValidInput intervals' (n + 1))
      (hperm : (ivs intervals').Perm ((a, b) :: ivs intervals))
      {r r' : Std.I64} (hr : remove_covered_intervals intervals = ok r)
      (hr' : remove_covered_intervals intervals' = ok r') :
      r'.val = r.val + 1 - (newlyCoveredCount (ivs intervals) (a, b) : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (intervals intervals' : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (h : ValidInput intervals n) (hn : n ≤ 999)
        (a b : ℤ) (hab : 0 ≤ a ∧ a < b ∧ b ≤ 100000)
        (hfresh : ∀ i ∈ List.range n, (ivs intervals).getD i (0, 0) ≠ (a, b))
        (huncovered : ∀ i ∈ List.range n,
          ¬ Covers ((ivs intervals).getD i (0, 0)) (a, b))
        (h' : ValidInput intervals' (n + 1))
        (hperm : (ivs intervals').Perm ((a, b) :: ivs intervals))
        {r r' : Std.I64} (hr : remove_covered_intervals intervals = ok r)
        (hr' : remove_covered_intervals intervals' = ok r'), r'.val = r.val + 1 - (newlyCoveredCount (ivs intervals) (a, b) : ℤ)) := by
    sorry

  end AegisSpec.RemoveCoveredIntervals
