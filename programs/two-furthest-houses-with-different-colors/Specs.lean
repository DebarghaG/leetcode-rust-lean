import Aegis.MaxDistance.Code.Funs

/-!
# Specifications of `Aegis.MaxDistance.max_distance`

LeetCode problem `two-furthest-houses-with-different-colors`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxDistance

  def colAt (colors : Slice Std.I64) (i : ℕ) : ℤ :=
    match colors.val[i]? with
    | some c => c.val
    | none => 0

  def idxDist (i j : ℕ) : ℤ :=
    |(i : ℤ) - (j : ℤ)|

  def indicesDiffering (colors : Slice Std.I64) (j : ℕ) : List ℕ :=
    (List.range colors.val.length).filter (fun i => colAt colors i ≠ colAt colors j)

  def maxDifferingFromStart (colors : Slice Std.I64) : ℕ :=
    (indicesDiffering colors 0).max?.getD 0

  def maxDifferingFromEnd (colors : Slice Std.I64) : ℕ :=
    ((indicesDiffering colors (colors.val.length - 1)).map
        (fun i => colors.val.length - 1 - i)).max?.getD 0

  def IsMaxDistance (colors : Slice Std.I64) (r : ℤ) : Prop :=
    (∃ i j : ℕ, i < colors.val.length ∧ j < colors.val.length ∧
        colAt colors i ≠ colAt colors j ∧ r = idxDist i j) ∧
      ∀ i j : ℕ, i < colors.val.length → j < colors.val.length →
        colAt colors i ≠ colAt colors j → idxDist i j ≤ r

  /-- The function returns a result r, and r is the maximum distance between two houses of different colors: there exist indices i and j such that 0 <= i < n, 0 <= j < n, colors[i] != colors[j], and r = abs(i - j); and for every i and j with 0 <= i < n, 0 <= j < n, and colors[i] != colors[j], we have abs(i - j) <= r.
    Preconditions: Let n = len(colors). 2 <= n <= 100. For every i with 0 <= i < n, 0 <= colors[i] <= 100. There exist i and j with 0 <= i < n and 0 <= j < n such that colors[i] != colors[j]. -/
  theorem spec_1 (colors : Slice Std.I64)
      (h_len_ge : 2 ≤ colors.val.length)
      (h_len_le : colors.val.length ≤ 100)
      (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
      (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
        colAt colors i ≠ colAt colors j) :
      ∃ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r ∧ IsMaxDistance colors r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (colors : Slice Std.I64)
        (h_len_ge : 2 ≤ colors.val.length)
        (h_len_le : colors.val.length ≤ 100)
        (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
        (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
          colAt colors i ≠ colAt colors j), ∃ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r ∧ IsMaxDistance colors r.val) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= n - 1.
    Preconditions: Let n = len(colors). 2 <= n <= 100. For every i with 0 <= i < n, 0 <= colors[i] <= 100. There exist i and j with 0 <= i < n and 0 <= j < n such that colors[i] != colors[j]. -/
  theorem spec_2 (colors : Slice Std.I64)
      (h_len_ge : 2 ≤ colors.val.length)
      (h_len_le : colors.val.length ≤ 100)
      (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
      (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
        colAt colors i ≠ colAt colors j) :
      ∀ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r →
        1 ≤ r.val ∧ r.val ≤ (colors.val.length : ℤ) - 1 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (colors : Slice Std.I64)
        (h_len_ge : 2 ≤ colors.val.length)
        (h_len_le : colors.val.length ≤ 100)
        (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
        (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
          colAt colors i ≠ colAt colors j), ∀ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r →
          1 ≤ r.val ∧ r.val ≤ (colors.val.length : ℤ) - 1) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow).
    Preconditions: Let n = len(colors). 2 <= n <= 100. For every i with 0 <= i < n, 0 <= colors[i] <= 100. There exist i and j with 0 <= i < n and 0 <= j < n such that colors[i] != colors[j]. -/
  theorem spec_3 (colors : Slice Std.I64)
      (h_len_ge : 2 ≤ colors.val.length)
      (h_len_le : colors.val.length ≤ 100)
      (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
      (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
        colAt colors i ≠ colAt colors j) :
      ∃ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (colors : Slice Std.I64)
        (h_len_ge : 2 ≤ colors.val.length)
        (h_len_le : colors.val.length ≤ 100)
        (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
        (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
          colAt colors i ≠ colAt colors j), ∃ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices i and j such that 0 <= i < n, 0 <= j < n, colors[i] != colors[j], and r = abs(i - j).
    Preconditions: Let n = len(colors). 2 <= n <= 100. For every i with 0 <= i < n, 0 <= colors[i] <= 100. There exist i and j with 0 <= i < n and 0 <= j < n such that colors[i] != colors[j]. -/
  theorem spec_4 (colors : Slice Std.I64)
      (h_len_ge : 2 ≤ colors.val.length)
      (h_len_le : colors.val.length ≤ 100)
      (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
      (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
        colAt colors i ≠ colAt colors j) :
      ∀ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r →
        ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
          colAt colors i ≠ colAt colors j ∧ r.val = idxDist i j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (colors : Slice Std.I64)
        (h_len_ge : 2 ≤ colors.val.length)
        (h_len_le : colors.val.length ≤ 100)
        (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
        (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
          colAt colors i ≠ colAt colors j), ∀ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r →
          ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
            colAt colors i ≠ colAt colors j ∧ r.val = idxDist i j) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < n, 0 <= j < n, and colors[i] != colors[j], we have abs(i - j) <= r.
    Preconditions: Let n = len(colors). 2 <= n <= 100. For every i with 0 <= i < n, 0 <= colors[i] <= 100. There exist i and j with 0 <= i < n and 0 <= j < n such that colors[i] != colors[j]. -/
  theorem spec_5 (colors : Slice Std.I64)
      (h_len_ge : 2 ≤ colors.val.length)
      (h_len_le : colors.val.length ≤ 100)
      (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
      (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
        colAt colors i ≠ colAt colors j) :
      ∀ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r →
        ∀ (i j : ℕ), i < colors.val.length → j < colors.val.length →
          colAt colors i ≠ colAt colors j → idxDist i j ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (colors : Slice Std.I64)
        (h_len_ge : 2 ≤ colors.val.length)
        (h_len_le : colors.val.length ≤ 100)
        (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
        (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
          colAt colors i ≠ colAt colors j), ∀ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r →
          ∀ (i j : ℕ), i < colors.val.length → j < colors.val.length →
            colAt colors i ≠ colAt colors j → idxDist i j ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices i and j such that 0 <= i < n, 0 <= j < n, colors[i] != colors[j], r = abs(i - j), and (i = 0 or j = n - 1).
    Preconditions: Let n = len(colors). 2 <= n <= 100. For every i with 0 <= i < n, 0 <= colors[i] <= 100. There exist i and j with 0 <= i < n and 0 <= j < n such that colors[i] != colors[j]. -/
  theorem spec_6 (colors : Slice Std.I64)
      (h_len_ge : 2 ≤ colors.val.length)
      (h_len_le : colors.val.length ≤ 100)
      (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
      (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
        colAt colors i ≠ colAt colors j) :
      ∀ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r →
        ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
          colAt colors i ≠ colAt colors j ∧ r.val = idxDist i j ∧
          (i = 0 ∨ j = colors.val.length - 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (colors : Slice Std.I64)
        (h_len_ge : 2 ≤ colors.val.length)
        (h_len_le : colors.val.length ≤ 100)
        (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
        (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
          colAt colors i ≠ colAt colors j), ∀ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r →
          ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
            colAt colors i ≠ colAt colors j ∧ r.val = idxDist i j ∧
            (i = 0 ∨ j = colors.val.length - 1)) := by
    sorry

  /-- Whenever the function returns a result r, r = max( max{ j | 0 <= j < n and colors[j] != colors[0] }, max{ n - 1 - i | 0 <= i < n and colors[i] != colors[n - 1] } ).
    Preconditions: Let n = len(colors). 2 <= n <= 100. For every i with 0 <= i < n, 0 <= colors[i] <= 100. There exist i and j with 0 <= i < n and 0 <= j < n such that colors[i] != colors[j]. -/
  theorem spec_7 (colors : Slice Std.I64)
      (h_len_ge : 2 ≤ colors.val.length)
      (h_len_le : colors.val.length ≤ 100)
      (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
      (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
        colAt colors i ≠ colAt colors j) :
      ∀ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r →
        r.val = max ((maxDifferingFromStart colors : ℕ) : ℤ)
          ((maxDifferingFromEnd colors : ℕ) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (colors : Slice Std.I64)
        (h_len_ge : 2 ≤ colors.val.length)
        (h_len_le : colors.val.length ≤ 100)
        (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
        (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
          colAt colors i ≠ colAt colors j), ∀ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r →
          r.val = max ((maxDifferingFromStart colors : ℕ) : ℤ)
            ((maxDifferingFromEnd colors : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = n - 1 if and only if colors[0] != colors[n - 1].
    Preconditions: Let n = len(colors). 2 <= n <= 100. For every i with 0 <= i < n, 0 <= colors[i] <= 100. There exist i and j with 0 <= i < n and 0 <= j < n such that colors[i] != colors[j]. -/
  theorem spec_8 (colors : Slice Std.I64)
      (h_len_ge : 2 ≤ colors.val.length)
      (h_len_le : colors.val.length ≤ 100)
      (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
      (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
        colAt colors i ≠ colAt colors j) :
      ∀ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r →
        (r.val = (colors.val.length : ℤ) - 1 ↔
          colAt colors 0 ≠ colAt colors (colors.val.length - 1)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (colors : Slice Std.I64)
        (h_len_ge : 2 ≤ colors.val.length)
        (h_len_le : colors.val.length ≤ 100)
        (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
        (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
          colAt colors i ≠ colAt colors j), ∀ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r →
          (r.val = (colors.val.length : ℤ) - 1 ↔
            colAt colors 0 ≠ colAt colors (colors.val.length - 1))) := by
    sorry

  /-- Whenever the function returns a result r, r >= floor(n / 2).
    Preconditions: Let n = len(colors). 2 <= n <= 100. For every i with 0 <= i < n, 0 <= colors[i] <= 100. There exist i and j with 0 <= i < n and 0 <= j < n such that colors[i] != colors[j]. -/
  theorem spec_9 (colors : Slice Std.I64)
      (h_len_ge : 2 ≤ colors.val.length)
      (h_len_le : colors.val.length ≤ 100)
      (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
      (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
        colAt colors i ≠ colAt colors j) :
      ∀ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r →
        r.val ≥ ((colors.val.length / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (colors : Slice Std.I64)
        (h_len_ge : 2 ≤ colors.val.length)
        (h_len_le : colors.val.length ≤ 100)
        (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
        (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
          colAt colors i ≠ colAt colors j), ∀ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r →
          r.val ≥ ((colors.val.length / 2 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices i and j such that 0 <= i < j < n, colors[i] != colors[j], r = j - i, i is the smallest index with color colors[i] (i.e., for all k with 0 <= k < i, colors[k] != colors[i]), and j is the largest index with color colors[j] (i.e., for all k with j < k < n, colors[k] != colors[j]).
    Preconditions: Let n = len(colors). 2 <= n <= 100. For every i with 0 <= i < n, 0 <= colors[i] <= 100. There exist i and j with 0 <= i < n and 0 <= j < n such that colors[i] != colors[j]. -/
  theorem spec_10 (colors : Slice Std.I64)
      (h_len_ge : 2 ≤ colors.val.length)
      (h_len_le : colors.val.length ≤ 100)
      (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
      (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
        colAt colors i ≠ colAt colors j) :
      ∀ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r →
        ∃ (i j : ℕ), i < j ∧ j < colors.val.length ∧
          colAt colors i ≠ colAt colors j ∧ r.val = (j : ℤ) - (i : ℤ) ∧
          (∀ (k : ℕ), k < i → colAt colors k ≠ colAt colors i) ∧
          (∀ (k : ℕ), j < k → k < colors.val.length → colAt colors k ≠ colAt colors j) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (colors : Slice Std.I64)
        (h_len_ge : 2 ≤ colors.val.length)
        (h_len_le : colors.val.length ≤ 100)
        (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
        (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
          colAt colors i ≠ colAt colors j), ∀ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r →
          ∃ (i j : ℕ), i < j ∧ j < colors.val.length ∧
            colAt colors i ≠ colAt colors j ∧ r.val = (j : ℤ) - (i : ℤ) ∧
            (∀ (k : ℕ), k < i → colAt colors k ≠ colAt colors i) ∧
            (∀ (k : ℕ), j < k → k < colors.val.length → colAt colors k ≠ colAt colors j)) := by
    sorry

  /-- Whenever the function returns a result r, for every array colors' of length n such that for all i and j with 0 <= i < n and 0 <= j < n, colors'[i] = colors'[j] if and only if colors[i] = colors[j], the maximum distance between two houses of different colors in colors' is also r.
    Preconditions: Let n = len(colors). 2 <= n <= 100. For every i with 0 <= i < n, 0 <= colors[i] <= 100. There exist i and j with 0 <= i < n and 0 <= j < n such that colors[i] != colors[j]. -/
  theorem spec_11 (colors : Slice Std.I64)
      (h_len_ge : 2 ≤ colors.val.length)
      (h_len_le : colors.val.length ≤ 100)
      (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
      (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
        colAt colors i ≠ colAt colors j) :
      ∀ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r →
        ∀ (colors' : Slice Std.I64), colors'.val.length = colors.val.length →
          (∀ (i j : ℕ), i < colors.val.length → j < colors.val.length →
            (colAt colors' i = colAt colors' j ↔ colAt colors i = colAt colors j)) →
          IsMaxDistance colors' r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (colors : Slice Std.I64)
        (h_len_ge : 2 ≤ colors.val.length)
        (h_len_le : colors.val.length ≤ 100)
        (h_colors : ∀ (i : ℕ), i < colors.val.length → 0 ≤ colAt colors i ∧ colAt colors i ≤ 100)
        (h_two_colors : ∃ (i j : ℕ), i < colors.val.length ∧ j < colors.val.length ∧
          colAt colors i ≠ colAt colors j), ∀ (r : Std.I64), Aegis.MaxDistance.max_distance colors = ok r →
          ∀ (colors' : Slice Std.I64), colors'.val.length = colors.val.length →
            (∀ (i j : ℕ), i < colors.val.length → j < colors.val.length →
              (colAt colors' i = colAt colors' j ↔ colAt colors i = colAt colors j)) →
            IsMaxDistance colors' r.val) := by
    sorry

  end AegisSpec.MaxDistance
