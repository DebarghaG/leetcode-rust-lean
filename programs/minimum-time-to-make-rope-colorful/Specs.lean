import Aegis.MinCost.Code.Funs

/-!
# Specifications of `Aegis.MinCost.min_cost`

LeetCode problem `minimum-time-to-make-rope-colorful`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinCost

  def colorAt (colors : List Std.U8) (i : ℕ) : ℕ := (colors.getD i 0#u8).val

  def timeAt (neededTime : List Std.I64) (i : ℕ) : ℤ := (neededTime.getD i 0#i64).val

  def segIndices (a b : ℕ) : List ℕ := (List.range (b + 1)).filter (fun i => a ≤ i)

  def segSum (neededTime : List Std.I64) (a b : ℕ) : ℤ :=
    ((segIndices a b).map (fun i => timeAt neededTime i)).sum

  def segMax (neededTime : List Std.I64) (a b : ℕ) : ℤ :=
    ((segIndices a b).map (fun i => timeAt neededTime i)).foldr max 0

  def IsMaximalBlock (colors : List Std.U8) (a b : ℕ) : Prop :=
    a ≤ b ∧ b < colors.length ∧
      (∀ i, a ≤ i → i < b → colorAt colors i = colorAt colors (i + 1)) ∧
      (a = 0 ∨ colorAt colors (a - 1) ≠ colorAt colors a) ∧
      (b = colors.length - 1 ∨ colorAt colors b ≠ colorAt colors (b + 1))

  def blockCost (neededTime : List Std.I64) (a b : ℕ) : ℤ :=
    segSum neededTime a b - segMax neededTime a b

  noncomputable def totalCost (colors : List Std.U8) (neededTime : List Std.I64) : ℤ := by
    classical
    exact
      ((Finset.product (Finset.range colors.length) (Finset.range colors.length)).filter
          (fun p : ℕ × ℕ => IsMaximalBlock colors p.1 p.2)).sum
        (fun p : ℕ × ℕ => blockCost neededTime p.1 p.2)

  def totalSum (neededTime : List Std.I64) : ℤ := (neededTime.map (fun x => x.val)).sum

  def maxAll (neededTime : List Std.I64) : ℤ :=
    (neededTime.map (fun x => x.val)).foldr max 0

  def remainingIndices (n : ℕ) (R : Finset ℕ) : List ℕ :=
    (List.range n).filter (fun i => i ∉ R)

  def ColorfulAfterRemoving (colors : List Std.U8) (n : ℕ) (R : Finset ℕ) : Prop :=
    ∀ (j : ℕ) (h : j + 1 < (remainingIndices n R).length),
      colorAt colors ((remainingIndices n R).get ⟨j, Nat.lt_of_succ_lt h⟩) ≠
        colorAt colors ((remainingIndices n R).get ⟨j + 1, h⟩)

  def NoAdjacentEqualUpTo (colors : List Std.U8) (n : ℕ) : Prop :=
    ∀ i, i < n - 1 → colorAt colors i ≠ colorAt colors (i + 1)

  def finsetSum (neededTime : List Std.I64) (R : Finset ℕ) : ℤ :=
    R.sum (fun i => timeAt neededTime i)

  def blockMultiset (neededTime : List Std.I64) (a b : ℕ) : Multiset ℤ :=
    ((segIndices a b).map (fun i => timeAt neededTime i) : Multiset ℤ)

  noncomputable def chosenRemainder (colors : List Std.U8) (choice : ℕ → ℕ → ℕ) :
      Finset ℕ := by
    classical
    exact (Finset.range colors.length).filter
      (fun i => ∃ a b, IsMaximalBlock colors a b ∧ a ≤ i ∧ i ≤ b ∧ i ≠ choice a b)

  /-- The function returns a result r (it does not fail), and r is computed as follows. For each maximal contiguous block of equal colors, i.e. each interval [a,b] with 0 <= a <= b < n such that for every i with a <= i < b, colors[i] = colors[i+1], and also a = 0 or colors[a-1] != colors[a], and b = n-1 or colors[b+1] != colors[b], let S(a,b) = sum_{i=a}^{b} neededTime[i] and M(a,b) = max_{a <= i <= b} neededTime[i]. Then r = sum over all such intervals [a,b] of (S(a,b) - M(a,b)).
    Preconditions: Let n = len(colors). len(colors) = len(neededTime) = n; 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= neededTime[i] <= 10000 and colors[i] is an ASCII lowercase letter (97 <= colors[i] <= 122). -/
  theorem spec_1 (colors : Slice Std.U8) (neededTime : Slice Std.I64) (n : ℕ)
      (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (htime_bounds : ∀ i, i < n →
        1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
      (hcolors_bounds : ∀ i, i < n →
        97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122) :
      ∃ r, Aegis.MinCost.min_cost colors neededTime = ok r ∧
        r.val = totalCost colors.val neededTime.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (colors : Slice Std.U8) (neededTime : Slice Std.I64) (n : ℕ)
        (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (htime_bounds : ∀ i, i < n →
          1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
        (hcolors_bounds : ∀ i, i < n →
          97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122), ∃ r, Aegis.MinCost.min_cost colors neededTime = ok r ∧
          r.val = totalCost colors.val neededTime.val) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail (no arithmetic overflow, no out-of-bounds access, and no panic).
    Preconditions: Let n = len(colors). len(colors) = len(neededTime) = n; 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= neededTime[i] <= 10000 and colors[i] is an ASCII lowercase letter (97 <= colors[i] <= 122). -/
  theorem spec_2 (colors : Slice Std.U8) (neededTime : Slice Std.I64) (n : ℕ)
      (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (htime_bounds : ∀ i, i < n →
        1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
      (hcolors_bounds : ∀ i, i < n →
        97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122) :
      ∃ r, Aegis.MinCost.min_cost colors neededTime = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (colors : Slice Std.U8) (neededTime : Slice Std.I64) (n : ℕ)
        (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (htime_bounds : ∀ i, i < n →
          1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
        (hcolors_bounds : ∀ i, i < n →
          97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122), ∃ r, Aegis.MinCost.min_cost colors neededTime = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= sum_{i=0}^{n-1} neededTime[i].
    Preconditions: Let n = len(colors). len(colors) = len(neededTime) = n; 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= neededTime[i] <= 10000 and colors[i] is an ASCII lowercase letter (97 <= colors[i] <= 122). -/
  theorem spec_3 (colors : Slice Std.U8) (neededTime : Slice Std.I64) (n : ℕ)
      (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (htime_bounds : ∀ i, i < n →
        1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
      (hcolors_bounds : ∀ i, i < n →
        97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122) :
      ∀ r, Aegis.MinCost.min_cost colors neededTime = ok r →
        0 ≤ r.val ∧ r.val ≤ totalSum neededTime.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (colors : Slice Std.U8) (neededTime : Slice Std.I64) (n : ℕ)
        (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (htime_bounds : ∀ i, i < n →
          1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
        (hcolors_bounds : ∀ i, i < n →
          97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122), ∀ r, Aegis.MinCost.min_cost colors neededTime = ok r →
          0 ≤ r.val ∧ r.val ≤ totalSum neededTime.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < n-1, colors[i] != colors[i+1].
    Preconditions: Let n = len(colors). len(colors) = len(neededTime) = n; 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= neededTime[i] <= 10000 and colors[i] is an ASCII lowercase letter (97 <= colors[i] <= 122). -/
  theorem spec_4 (colors : Slice Std.U8) (neededTime : Slice Std.I64) (n : ℕ)
      (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (htime_bounds : ∀ i, i < n →
        1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
      (hcolors_bounds : ∀ i, i < n →
        97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122) :
      ∀ r, Aegis.MinCost.min_cost colors neededTime = ok r →
        (r.val = 0 ↔ NoAdjacentEqualUpTo colors.val n) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (colors : Slice Std.U8) (neededTime : Slice Std.I64) (n : ℕ)
        (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (htime_bounds : ∀ i, i < n →
          1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
        (hcolors_bounds : ∀ i, i < n →
          97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122), ∀ r, Aegis.MinCost.min_cost colors neededTime = ok r →
          (r.val = 0 ↔ NoAdjacentEqualUpTo colors.val n)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a set R of indices with 0 <= i < n such that (1) sum_{i in R} neededTime[i] = r, and (2) after removing exactly the balloons with indices in R, the remaining balloons, read in increasing index order, have no two consecutive balloons of the same color. Formally, for the increasing list K of indices not in R, for every j with 0 <= j < len(K)-1, colors[K[j]] != colors[K[j+1]].
    Preconditions: Let n = len(colors). len(colors) = len(neededTime) = n; 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= neededTime[i] <= 10000 and colors[i] is an ASCII lowercase letter (97 <= colors[i] <= 122). -/
  theorem spec_5 (colors : Slice Std.U8) (neededTime : Slice Std.I64) (n : ℕ)
      (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (htime_bounds : ∀ i, i < n →
        1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
      (hcolors_bounds : ∀ i, i < n →
        97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122) :
      ∀ r, Aegis.MinCost.min_cost colors neededTime = ok r →
        ∃ R : Finset ℕ, (∀ i ∈ R, i < n) ∧
          finsetSum neededTime.val R = r.val ∧
          ColorfulAfterRemoving colors.val n R := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (colors : Slice Std.U8) (neededTime : Slice Std.I64) (n : ℕ)
        (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (htime_bounds : ∀ i, i < n →
          1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
        (hcolors_bounds : ∀ i, i < n →
          97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122), ∀ r, Aegis.MinCost.min_cost colors neededTime = ok r →
          ∃ R : Finset ℕ, (∀ i ∈ R, i < n) ∧
            finsetSum neededTime.val R = r.val ∧
            ColorfulAfterRemoving colors.val n R) := by
    sorry

  /-- Whenever the function returns a result r, for every set R of indices with 0 <= i < n such that after removing exactly the balloons with indices in R the remaining balloons have no two consecutive balloons of the same color (formally, for the increasing list K of indices not in R, for every j with 0 <= j < len(K)-1, colors[K[j]] != colors[K[j+1]]), it holds that sum_{i in R} neededTime[i] >= r.
    Preconditions: Let n = len(colors). len(colors) = len(neededTime) = n; 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= neededTime[i] <= 10000 and colors[i] is an ASCII lowercase letter (97 <= colors[i] <= 122). -/
  theorem spec_6 (colors : Slice Std.U8) (neededTime : Slice Std.I64) (n : ℕ)
      (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (htime_bounds : ∀ i, i < n →
        1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
      (hcolors_bounds : ∀ i, i < n →
        97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122) :
      ∀ r, Aegis.MinCost.min_cost colors neededTime = ok r →
        ∀ R : Finset ℕ, (∀ i ∈ R, i < n) → ColorfulAfterRemoving colors.val n R →
          r.val ≤ finsetSum neededTime.val R := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (colors : Slice Std.U8) (neededTime : Slice Std.I64) (n : ℕ)
        (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (htime_bounds : ∀ i, i < n →
          1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
        (hcolors_bounds : ∀ i, i < n →
          97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122), ∀ r, Aegis.MinCost.min_cost colors neededTime = ok r →
          ∀ R : Finset ℕ, (∀ i ∈ R, i < n) → ColorfulAfterRemoving colors.val n R →
            r.val ≤ finsetSum neededTime.val R) := by
    sorry

  /-- The result of the function on (colors, neededTime) equals the result of the function on (colors2, neededTime).
    Preconditions: Let n = len(colors). len(colors) = len(neededTime) = n; 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= neededTime[i] <= 10000 and colors[i] is an ASCII lowercase letter (97 <= colors[i] <= 122). Let colors2 be any byte array of length n such that colors2[i] is an ASCII lowercase letter for every i with 0 <= i < n, and for every i with 0 <= i < n-1, colors[i] = colors[i+1] if and only if colors2[i] = colors2[i+1]. -/
  theorem spec_7 (colors colors2 : Slice Std.U8) (neededTime : Slice Std.I64) (n : ℕ)
      (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (htime_bounds : ∀ i, i < n →
        1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
      (hcolors_bounds : ∀ i, i < n →
        97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122)
      (hcolors2_len : colors2.val.length = n)
      (hcolors2_bounds : ∀ i, i < n →
        97 ≤ colorAt colors2.val i ∧ colorAt colors2.val i ≤ 122)
      (hpattern : ∀ i, i < n - 1 →
        (colorAt colors.val i = colorAt colors.val (i + 1) ↔
          colorAt colors2.val i = colorAt colors2.val (i + 1))) :
      ∀ r, Aegis.MinCost.min_cost colors neededTime = ok r →
        Aegis.MinCost.min_cost colors2 neededTime = ok r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (colors colors2 : Slice Std.U8) (neededTime : Slice Std.I64) (n : ℕ)
        (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (htime_bounds : ∀ i, i < n →
          1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
        (hcolors_bounds : ∀ i, i < n →
          97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122)
        (hcolors2_len : colors2.val.length = n)
        (hcolors2_bounds : ∀ i, i < n →
          97 ≤ colorAt colors2.val i ∧ colorAt colors2.val i ≤ 122)
        (hpattern : ∀ i, i < n - 1 →
          (colorAt colors.val i = colorAt colors.val (i + 1) ↔
            colorAt colors2.val i = colorAt colors2.val (i + 1))), ∀ r, Aegis.MinCost.min_cost colors neededTime = ok r →
          Aegis.MinCost.min_cost colors2 neededTime = ok r) := by
    sorry

  /-- The result of the function on (colors, neededTime) equals the result of the function on (colors, neededTime2).
    Preconditions: Let n = len(colors). len(colors) = len(neededTime) = n; 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= neededTime[i] <= 10000 and colors[i] is an ASCII lowercase letter (97 <= colors[i] <= 122). Let neededTime2 be another integer array of length n satisfying 1 <= neededTime2[i] <= 10000 for every i with 0 <= i < n, such that for every maximal equal-color block B of colors (an interval [a,b] as defined in the main specification), the multiset of values {neededTime[i] : i in B} equals the multiset {neededTime2[i] : i in B}. -/
  theorem spec_8 (colors : Slice Std.U8) (neededTime neededTime2 : Slice Std.I64) (n : ℕ)
      (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (htime_bounds : ∀ i, i < n →
        1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
      (hcolors_bounds : ∀ i, i < n →
        97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122)
      (htime2_len : neededTime2.val.length = n)
      (htime2_bounds : ∀ i, i < n →
        1 ≤ timeAt neededTime2.val i ∧ timeAt neededTime2.val i ≤ 10000)
      (hmultiset : ∀ a b, IsMaximalBlock colors.val a b →
        blockMultiset neededTime.val a b = blockMultiset neededTime2.val a b) :
      ∀ r, Aegis.MinCost.min_cost colors neededTime = ok r →
        Aegis.MinCost.min_cost colors neededTime2 = ok r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (colors : Slice Std.U8) (neededTime neededTime2 : Slice Std.I64) (n : ℕ)
        (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (htime_bounds : ∀ i, i < n →
          1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
        (hcolors_bounds : ∀ i, i < n →
          97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122)
        (htime2_len : neededTime2.val.length = n)
        (htime2_bounds : ∀ i, i < n →
          1 ≤ timeAt neededTime2.val i ∧ timeAt neededTime2.val i ≤ 10000)
        (hmultiset : ∀ a b, IsMaximalBlock colors.val a b →
          blockMultiset neededTime.val a b = blockMultiset neededTime2.val a b), ∀ r, Aegis.MinCost.min_cost colors neededTime = ok r →
          Aegis.MinCost.min_cost colors neededTime2 = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r <= (sum_{i=0}^{n-1} neededTime[i]) - (max_{0 <= i < n} neededTime[i]).
    Preconditions: Let n = len(colors). len(colors) = len(neededTime) = n; 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= neededTime[i] <= 10000 and colors[i] is an ASCII lowercase letter (97 <= colors[i] <= 122). -/
  theorem spec_9 (colors : Slice Std.U8) (neededTime : Slice Std.I64) (n : ℕ)
      (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (htime_bounds : ∀ i, i < n →
        1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
      (hcolors_bounds : ∀ i, i < n →
        97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122) :
      ∀ r, Aegis.MinCost.min_cost colors neededTime = ok r →
        r.val ≤ totalSum neededTime.val - maxAll neededTime.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (colors : Slice Std.U8) (neededTime : Slice Std.I64) (n : ℕ)
        (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (htime_bounds : ∀ i, i < n →
          1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
        (hcolors_bounds : ∀ i, i < n →
          97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122), ∀ r, Aegis.MinCost.min_cost colors neededTime = ok r →
          r.val ≤ totalSum neededTime.val - maxAll neededTime.val) := by
    sorry

  /-- If r is the result of the function on (colors, neededTime) and r2 is the result on (colors, neededTime2), then r2 <= r.
    Preconditions: Let n = len(colors). len(colors) = len(neededTime) = n; 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= neededTime[i] <= 10000 and colors[i] is an ASCII lowercase letter (97 <= colors[i] <= 122). Let neededTime2 be another integer array of length n satisfying 1 <= neededTime2[i] <= 10000 for every i, and neededTime2[i] <= neededTime[i] for every i. -/
  theorem spec_10 (colors : Slice Std.U8) (neededTime neededTime2 : Slice Std.I64) (n : ℕ)
      (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (htime_bounds : ∀ i, i < n →
        1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
      (hcolors_bounds : ∀ i, i < n →
        97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122)
      (htime2_len : neededTime2.val.length = n)
      (htime2_bounds : ∀ i, i < n →
        1 ≤ timeAt neededTime2.val i ∧ timeAt neededTime2.val i ≤ 10000)
      (hle : ∀ i, i < n → timeAt neededTime2.val i ≤ timeAt neededTime.val i) :
      ∀ r r2, Aegis.MinCost.min_cost colors neededTime = ok r →
        Aegis.MinCost.min_cost colors neededTime2 = ok r2 → r2.val ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (colors : Slice Std.U8) (neededTime neededTime2 : Slice Std.I64) (n : ℕ)
        (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (htime_bounds : ∀ i, i < n →
          1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
        (hcolors_bounds : ∀ i, i < n →
          97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122)
        (htime2_len : neededTime2.val.length = n)
        (htime2_bounds : ∀ i, i < n →
          1 ≤ timeAt neededTime2.val i ∧ timeAt neededTime2.val i ≤ 10000)
        (hle : ∀ i, i < n → timeAt neededTime2.val i ≤ timeAt neededTime.val i), ∀ r r2, Aegis.MinCost.min_cost colors neededTime = ok r →
          Aegis.MinCost.min_cost colors neededTime2 = ok r2 → r2.val ≤ r.val) := by
    sorry

  /-- For each maximal equal-color block [a,b], choose an index m in [a,b] with neededTime[m] = max_{a <= i <= b} neededTime[i], and let R be the set of all indices in such blocks except the chosen m. Then sum_{i in R} neededTime[i] = r, and removing exactly the balloons in R makes the rope colorful.
    Preconditions: Let n = len(colors). len(colors) = len(neededTime) = n; 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= neededTime[i] <= 10000 and colors[i] is an ASCII lowercase letter (97 <= colors[i] <= 122). -/
  theorem spec_11 (colors : Slice Std.U8) (neededTime : Slice Std.I64) (n : ℕ)
      (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
      (htime_bounds : ∀ i, i < n →
        1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
      (hcolors_bounds : ∀ i, i < n →
        97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122) :
      ∀ r, Aegis.MinCost.min_cost colors neededTime = ok r →
        ∃ choice : ℕ → ℕ → ℕ,
          (∀ a b, IsMaximalBlock colors.val a b →
            a ≤ choice a b ∧ choice a b ≤ b ∧
              timeAt neededTime.val (choice a b) = segMax neededTime.val a b) ∧
          finsetSum neededTime.val (chosenRemainder colors.val choice) = r.val ∧
          ColorfulAfterRemoving colors.val n (chosenRemainder colors.val choice) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (colors : Slice Std.U8) (neededTime : Slice Std.I64) (n : ℕ)
        (hcolors_len : colors.val.length = n) (htime_len : neededTime.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
        (htime_bounds : ∀ i, i < n →
          1 ≤ timeAt neededTime.val i ∧ timeAt neededTime.val i ≤ 10000)
        (hcolors_bounds : ∀ i, i < n →
          97 ≤ colorAt colors.val i ∧ colorAt colors.val i ≤ 122), ∀ r, Aegis.MinCost.min_cost colors neededTime = ok r →
          ∃ choice : ℕ → ℕ → ℕ,
            (∀ a b, IsMaximalBlock colors.val a b →
              a ≤ choice a b ∧ choice a b ≤ b ∧
                timeAt neededTime.val (choice a b) = segMax neededTime.val a b) ∧
            finsetSum neededTime.val (chosenRemainder colors.val choice) = r.val ∧
            ColorfulAfterRemoving colors.val n (chosenRemainder colors.val choice)) := by
    sorry

  end AegisSpec.MinCost
