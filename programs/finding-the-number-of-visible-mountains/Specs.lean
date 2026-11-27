import Aegis.VisibleMountains.Code.Funs

/-!
# Specifications of `Aegis.VisibleMountains.visible_mountains`

LeetCode problem `finding-the-number-of-visible-mountains`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.VisibleMountains

  open Aegis.VisibleMountains

  attribute [local instance] Classical.propDecidable

  def ivals (v : alloc.vec.Vec Std.I64) : List Int := v.val.map (fun z => z.val)

  def points (peaks : Slice (alloc.vec.Vec Std.I64)) : List (Int × Int) :=
    (peaks.val.map ivals).map (fun l => (l.getD 0 0, l.getD 1 0))

  def numPeaks (peaks : Slice (alloc.vec.Vec Std.I64)) : Nat := (points peaks).length

  def pt (peaks : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int × Int :=
    (points peaks).getD i (0, 0)

  def peakX (peaks : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int := (pt peaks i).1

  def peakY (peaks : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int := (pt peaks i).2

  def ValidInput (peaks : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    1 ≤ numPeaks peaks ∧ numPeaks peaks ≤ 100000 ∧
    (∀ v ∈ peaks.val, v.val.length = 2) ∧
    (∀ i, i < numPeaks peaks →
      1 ≤ peakX peaks i ∧ peakX peaks i ≤ 100000 ∧
      1 ≤ peakY peaks i ∧ peakY peaks i ≤ 100000)

  def Visible (peaks : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Prop :=
    ∀ j, j < numPeaks peaks → j ≠ i →
      |peakX peaks i - peakX peaks j| + peakY peaks i > peakY peaks j

  noncomputable def visibleIndices (peaks : Slice (alloc.vec.Vec Std.I64)) : List Nat :=
    (List.range (numPeaks peaks)).filter (fun i => decide (Visible peaks i))

  def maxHeight (peaks : Slice (alloc.vec.Vec Std.I64)) : Int :=
    ((List.range (numPeaks peaks)).map (fun i => peakY peaks i)).foldl max (-1)

  def IsMaxIndex (peaks : Slice (alloc.vec.Vec Std.I64)) (m : Nat) : Prop :=
    m < numPeaks peaks ∧ peakY peaks m = maxHeight peaks

  def UniqueMaxIndex (peaks : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∃ m, IsMaxIndex peaks m ∧ ∀ m', IsMaxIndex peaks m' → m' = m

  def OccursOnce (peaks : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Prop :=
    ∀ j, j < numPeaks peaks → j ≠ i → pt peaks j ≠ pt peaks i

  theorem pt_eq_of_length_two (peaks : Slice (alloc.vec.Vec Std.I64)) (i : Nat)
      (hi : i < peaks.val.length) (h2 : (peaks.val[i]).val.length = 2) :
      ∃ a b : Std.I64, peaks.val[i] = [a, b] ∧ pt peaks i = (a.val, b.val) := by
    obtain ⟨a, b, hab⟩ : ∃ a b : Std.I64, peaks.val[i] = [a, b] :=
      List.length_eq_two.mp h2
    refine ⟨a, b, hab, ?_⟩
    have hd := List.getD_map (peaks.val.map ivals) ([] : List Int) (n := i)
      (f := fun l => (l.getD 0 0, l.getD 1 0))
    have hiv : ivals (peaks.val[i]) = [a.val, b.val] := by simp [ivals, hab]
    have hget : (List.map ivals (peaks.val)).getD i [] = [a.val, b.val] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi),
        List.getElem_map]
      simpa using hiv
    simp only [pt, points]
    change (((List.map ivals (peaks.val)).map
      (fun l => (l.getD 0 0, l.getD 1 0))).getD i
      (([].getD 0 0 : Int), ([].getD 1 0 : Int))) = _
    rw [hd, hget]
    simp

  /-- Whenever the function returns a result r, r is exactly the number of indices i with 0 <= i < n such that for every j with 0 <= j < n and j != i, |peaks[i][0] - peaks[j][0]| + peaks[i][1] > peaks[j][1]. In other words, r is the number of mountains whose peak does not lie inside or on the border of any other mountain.
    Preconditions: Let n = len(peaks). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, len(peaks[i]) = 2 and 1 <= peaks[i][0] <= 100000 and 1 <= peaks[i][1] <= 100000. All indices are 0-based and all arithmetic is exact integer arithmetic. -/
  theorem spec_1 (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks) :
      ∀ r : Std.I64, visible_mountains peaks = ok r →
        r.val = (((List.range (numPeaks peaks)).filter
          (fun i => decide (∀ j, j < numPeaks peaks → j ≠ i →
            |peakX peaks i - peakX peaks j| + peakY peaks i > peakY peaks j))).length : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks), ∀ r : Std.I64, visible_mountains peaks = ok r →
          r.val = (((List.range (numPeaks peaks)).filter
            (fun i => decide (∀ j, j < numPeaks peaks → j ≠ i →
              |peakX peaks i - peakX peaks j| + peakY peaks i > peakY peaks j))).length : Int)) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail due to overflow, out-of-bounds access, or panic.
    Preconditions: Let n = len(peaks). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, len(peaks[i]) = 2 and 1 <= peaks[i][0] <= 100000 and 1 <= peaks[i][1] <= 100000. All indices are 0-based. -/
  theorem spec_2 (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks) :
      ∃ r : Std.I64, visible_mountains peaks = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks), ∃ r : Std.I64, visible_mountains peaks = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= len(peaks).
    Preconditions: Let n = len(peaks). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, len(peaks[i]) = 2 and 1 <= peaks[i][0] <= 100000 and 1 <= peaks[i][1] <= 100000. All indices are 0-based. -/
  theorem spec_3 (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks) :
      ∀ r : Std.I64, visible_mountains peaks = ok r →
        0 ≤ r.val ∧ r.val ≤ (numPeaks peaks : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks), ∀ r : Std.I64, visible_mountains peaks = ok r →
          0 ≤ r.val ∧ r.val ≤ (numPeaks peaks : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1.
    Preconditions: Let n = len(peaks). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, len(peaks[i]) = 2 and 1 <= peaks[i][0] <= 100000 and 1 <= peaks[i][1] <= 100000. Additionally, n = 1. -/
  theorem spec_4 (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks)
      (hn : numPeaks peaks = 1) :
      ∀ r : Std.I64, visible_mountains peaks = ok r → r.val = 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks)
        (hn : numPeaks peaks = 1), ∀ r : Std.I64, visible_mountains peaks = ok r → r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if there is exactly one index m with 0 <= m < n such that peaks[m][1] = max_{0 <= i < n} peaks[i][1]; otherwise r = 0.
    Preconditions: Let n = len(peaks). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, len(peaks[i]) = 2 and 1 <= peaks[i][0] <= 100000 and 1 <= peaks[i][1] <= 100000. Additionally, there is an integer c such that peaks[i][0] = c for every i with 0 <= i < n. -/
  theorem spec_5 (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks)
      (hx : ∃ c : Int, ∀ i, i < numPeaks peaks → peakX peaks i = c) :
      ∀ r : Std.I64, visible_mountains peaks = ok r →
        (UniqueMaxIndex peaks → r.val = 1) ∧ (¬ UniqueMaxIndex peaks → r.val = 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks)
        (hx : ∃ c : Int, ∀ i, i < numPeaks peaks → peakX peaks i = c), ∀ r : Std.I64, visible_mountains peaks = ok r →
          (UniqueMaxIndex peaks → r.val = 1) ∧ (¬ UniqueMaxIndex peaks → r.val = 0)) := by
    sorry

  /-- Whenever the function returns a result r, r is at most the number of indices i with 0 <= i < n for which peaks[i] != peaks[j] for every j with 0 <= j < n and j != i. Equivalently, only mountains whose peak coordinate occurs exactly once can be counted as visible.
    Preconditions: Let n = len(peaks). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, len(peaks[i]) = 2 and 1 <= peaks[i][0] <= 100000 and 1 <= peaks[i][1] <= 100000. All indices are 0-based. -/
  theorem spec_6 (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks) :
      ∀ r : Std.I64, visible_mountains peaks = ok r →
        r.val ≤ (((List.range (numPeaks peaks)).filter
          (fun i => decide (∀ j, j < numPeaks peaks → j ≠ i →
            pt peaks j ≠ pt peaks i))).length : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks), ∀ r : Std.I64, visible_mountains peaks = ok r →
          r.val ≤ (((List.range (numPeaks peaks)).filter
            (fun i => decide (∀ j, j < numPeaks peaks → j ≠ i →
              pt peaks j ≠ pt peaks i))).length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, the index m satisfies the visibility condition for every k with 0 <= k < n and k != m, |peaks[m][0] - peaks[k][0]| + peaks[m][1] > peaks[k][1], and therefore m is counted in r; in particular r >= 1.
    Preconditions: Let n = len(peaks). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, len(peaks[i]) = 2 and 1 <= peaks[i][0] <= 100000 and 1 <= peaks[i][1] <= 100000. Additionally, there is exactly one index m with 0 <= m < n such that peaks[m][1] >= peaks[i][1] for every i with 0 <= i < n. -/
  theorem spec_7 (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks)
      (hm : UniqueMaxIndex peaks) :
      ∀ r : Std.I64, visible_mountains peaks = ok r →
        ∀ m, IsMaxIndex peaks m → Visible peaks m ∧ 1 ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks)
        (hm : UniqueMaxIndex peaks), ∀ r : Std.I64, visible_mountains peaks = ok r →
          ∀ m, IsMaxIndex peaks m → Visible peaks m ∧ 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = n.
    Preconditions: Let n = len(peaks). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, len(peaks[i]) = 2 and 1 <= peaks[i][0] <= 100000 and 1 <= peaks[i][1] <= 100000. Additionally, for every i and j with 0 <= i < n, 0 <= j < n, and i != j, |peaks[i][0] - peaks[j][0]| + peaks[i][1] > peaks[j][1]. -/
  theorem spec_8 (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks)
      (hall : ∀ i j, i < numPeaks peaks → j < numPeaks peaks → i ≠ j →
        |peakX peaks i - peakX peaks j| + peakY peaks i > peakY peaks j) :
      ∀ r : Std.I64, visible_mountains peaks = ok r → r.val = (numPeaks peaks : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks)
        (hall : ∀ i j, i < numPeaks peaks → j < numPeaks peaks → i ≠ j →
          |peakX peaks i - peakX peaks j| + peakY peaks i > peakY peaks j), ∀ r : Std.I64, visible_mountains peaks = ok r → r.val = (numPeaks peaks : Int)) := by
    sorry

  /-- Whenever the function returns a result r: r = 0 if a = b; r = 1 if a != b and exactly one of |a[0] - b[0]| + a[1] <= b[1] and |b[0] - a[0]| + b[1] <= a[1] holds; and r = 2 if a != b and neither of those two inequalities holds.
    Preconditions: Let n = len(peaks). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, len(peaks[i]) = 2 and 1 <= peaks[i][0] <= 100000 and 1 <= peaks[i][1] <= 100000. Additionally, n = 2. Write a = peaks[0] and b = peaks[1]. -/
  theorem spec_9 (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks)
      (hn : numPeaks peaks = 2) :
      ∀ r : Std.I64, visible_mountains peaks = ok r →
        (pt peaks 0 = pt peaks 1 → r.val = 0) ∧
        (pt peaks 0 ≠ pt peaks 1 →
          (((|peakX peaks 0 - peakX peaks 1| + peakY peaks 0 ≤ peakY peaks 1) ∧
            ¬ (|peakX peaks 1 - peakX peaks 0| + peakY peaks 1 ≤ peakY peaks 0)) ∨
           (¬ (|peakX peaks 0 - peakX peaks 1| + peakY peaks 0 ≤ peakY peaks 1) ∧
            (|peakX peaks 1 - peakX peaks 0| + peakY peaks 1 ≤ peakY peaks 0))) →
          r.val = 1) ∧
        (pt peaks 0 ≠ pt peaks 1 →
          ¬ (|peakX peaks 0 - peakX peaks 1| + peakY peaks 0 ≤ peakY peaks 1) →
          ¬ (|peakX peaks 1 - peakX peaks 0| + peakY peaks 1 ≤ peakY peaks 0) →
          r.val = 2) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks)
        (hn : numPeaks peaks = 2), ∀ r : Std.I64, visible_mountains peaks = ok r →
          (pt peaks 0 = pt peaks 1 → r.val = 0) ∧
          (pt peaks 0 ≠ pt peaks 1 →
            (((|peakX peaks 0 - peakX peaks 1| + peakY peaks 0 ≤ peakY peaks 1) ∧
              ¬ (|peakX peaks 1 - peakX peaks 0| + peakY peaks 1 ≤ peakY peaks 0)) ∨
             (¬ (|peakX peaks 0 - peakX peaks 1| + peakY peaks 0 ≤ peakY peaks 1) ∧
              (|peakX peaks 1 - peakX peaks 0| + peakY peaks 1 ≤ peakY peaks 0))) →
            r.val = 1) ∧
          (pt peaks 0 ≠ pt peaks 1 →
            ¬ (|peakX peaks 0 - peakX peaks 1| + peakY peaks 0 ≤ peakY peaks 1) →
            ¬ (|peakX peaks 1 - peakX peaks 0| + peakY peaks 1 ≤ peakY peaks 0) →
            r.val = 2)) := by
    sorry

  /-- Whenever visible_mountains(peaks) returns r and visible_mountains(peaks2) returns r2, r = r2.
    Preconditions: Let n = len(peaks) = len(peaks2). Assume 1 <= n <= 100000; for every i with 0 <= i < n, len(peaks[i]) = len(peaks2[i]) = 2, 1 <= peaks[i][0] <= 100000, 1 <= peaks[i][1] <= 100000, 1 <= peaks2[i][0] <= 100000, and 1 <= peaks2[i][1] <= 100000. Assume peaks2 is a permutation of peaks: the multiset of inner vectors of peaks2 equals that of peaks, counting multiplicities. -/
  theorem spec_10 (peaks peaks2 : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput peaks) (h2 : ValidInput peaks2)
      (hlen : numPeaks peaks = numPeaks peaks2)
      (hperm : List.Perm peaks2.val peaks.val) :
      ∀ r r2 : Std.I64, visible_mountains peaks = ok r →
        visible_mountains peaks2 = ok r2 → r = r2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (peaks peaks2 : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput peaks) (h2 : ValidInput peaks2)
        (hlen : numPeaks peaks = numPeaks peaks2)
        (hperm : List.Perm peaks2.val peaks.val), ∀ r r2 : Std.I64, visible_mountains peaks = ok r →
          visible_mountains peaks2 = ok r2 → r = r2) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: Let n = len(peaks). Assume 1 <= n <= 100000, and for every i with 0 <= i < n, len(peaks[i]) = 2 and 1 <= peaks[i][0] <= 100000 and 1 <= peaks[i][1] <= 100000. Additionally, n >= 2 and peaks[i] = peaks[0] for every i with 0 <= i < n. -/
  theorem spec_11 (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks)
      (hn : 2 ≤ numPeaks peaks)
      (hall : ∀ i, i < numPeaks peaks → pt peaks i = pt peaks 0) :
      ∀ r : Std.I64, visible_mountains peaks = ok r → r.val = 0 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (peaks : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput peaks)
        (hn : 2 ≤ numPeaks peaks)
        (hall : ∀ i, i < numPeaks peaks → pt peaks i = pt peaks 0), ∀ r : Std.I64, visible_mountains peaks = ok r → r.val = 0) := by
    sorry

  end AegisSpec.VisibleMountains
