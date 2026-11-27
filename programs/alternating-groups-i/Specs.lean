import Aegis.NumberOfAlternatingGroups.Code.Funs

/-!
# Specifications of `Aegis.NumberOfAlternatingGroups.number_of_alternating_groups`

LeetCode problem `alternating-groups-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumberOfAlternatingGroups

  attribute [local instance] Classical.propDecidable

  def lenOf (colors : Slice Std.I64) : ℕ := colors.val.length

  def colorAt (colors : Slice Std.I64) (i : ℕ) : ℤ := (colors.val.getD i 0#i64).val

  def entriesAreBits (colors : Slice Std.I64) : Prop :=
    ∀ i, i < lenOf colors → colorAt colors i = 0 ∨ colorAt colors i = 1

  def isAlternatingCenter (colors : Slice Std.I64) (i : ℕ) : Prop :=
    colorAt colors i ≠ colorAt colors ((i + lenOf colors - 1) % lenOf colors) ∧
      colorAt colors i ≠ colorAt colors ((i + 1) % lenOf colors)

  noncomputable def alternatingCount (colors : Slice Std.I64) : ℕ :=
    ((List.range (lenOf colors)).filter (fun i => decide (isAlternatingCenter colors i))).length

  def allColorsEqual (colors : Slice Std.I64) : Prop :=
    ∃ c : ℤ, (c = 0 ∨ c = 1) ∧ ∀ i, i < lenOf colors → colorAt colors i = c

  def isRunStart (colors : Slice Std.I64) (i : ℕ) : Prop :=
    colorAt colors i ≠ colorAt colors ((i + lenOf colors - 1) % lenOf colors)

  noncomputable def runLen (colors : Slice Std.I64) (i : ℕ) : ℕ :=
    ((List.range (lenOf colors + 1)).find?
          (fun k => decide (0 < k ∧ colorAt colors ((i + k) % lenOf colors) ≠ colorAt colors i))).getD
      (lenOf colors)

  noncomputable def numRuns (colors : Slice Std.I64) : ℕ :=
    if allColorsEqual colors then 1
    else ((List.range (lenOf colors)).filter (fun i => decide (isRunStart colors i))).length

  noncomputable def runsOfLength (colors : Slice Std.I64) (k : ℕ) : ℕ :=
    ((List.range (lenOf colors)).filter
        (fun i => decide (isRunStart colors i ∧ runLen colors i = k))).length

  /-- The function returns a result r (it does not fail), and r equals the number of indices i with 0 <= i < n such that colors[i] != colors[(i + n - 1) mod n] and colors[i] != colors[(i + 1) mod n]. Equivalently, r counts the alternating groups, taking the tile with index i as the middle tile of the three contiguous circular tiles (i-1, i, i+1).
    Preconditions: Let n = len(colors). 3 <= n <= 100, and for every i with 0 <= i < n, colors[i] is either 0 or 1. -/
  theorem spec_1 (colors : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
      (h_le : lenOf colors ≤ 100) (h_bits : entriesAreBits colors) :
      ∃ r : Std.I64,
        Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r ∧
          r.val = (alternatingCount colors : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (colors : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
        (h_le : lenOf colors ≤ 100) (h_bits : entriesAreBits colors), ∃ r : Std.I64,
          Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r ∧
            r.val = (alternatingCount colors : ℤ)) := by
    sorry

  /-- The function returns a result (it does not fail or panic) for every input satisfying the preconditions.
    Preconditions: Let n = len(colors). 3 <= n <= 100, and for every i with 0 <= i < n, colors[i] is either 0 or 1. -/
  theorem spec_2 (colors : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
      (h_le : lenOf colors ≤ 100) (h_bits : entriesAreBits colors) :
      ∃ r : Std.I64,
        Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (colors : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
        (h_le : lenOf colors ≤ 100) (h_bits : entriesAreBits colors), ∃ r : Std.I64,
          Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= len(colors).
    Preconditions: Let n = len(colors). 3 <= n <= 100, and for every i with 0 <= i < n, colors[i] is either 0 or 1. -/
  theorem spec_3 (colors : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
      (h_le : lenOf colors ≤ 100) (h_bits : entriesAreBits colors) :
      ∀ r : Std.I64,
        Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r →
          0 ≤ r.val ∧ r.val ≤ (lenOf colors : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (colors : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
        (h_le : lenOf colors ≤ 100) (h_bits : entriesAreBits colors), ∀ r : Std.I64,
          Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r →
            0 ≤ r.val ∧ r.val ≤ (lenOf colors : ℤ)) := by
    sorry

  /-- The function returns a result r, and r = 0.
    Preconditions: Let n = len(colors). 3 <= n <= 100, every colors[i] is either 0 or 1, and there is a value c in {0,1} such that colors[i] = c for every i with 0 <= i < n. -/
  theorem spec_4 (colors : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
      (h_le : lenOf colors ≤ 100) (h_bits : entriesAreBits colors)
      (h_const : allColorsEqual colors) :
      ∃ r : Std.I64,
        Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (colors : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
        (h_le : lenOf colors ≤ 100) (h_bits : entriesAreBits colors)
        (h_const : allColorsEqual colors), ∃ r : Std.I64,
          Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r, and r = 1.
    Preconditions: Let n = len(colors) = 3, every colors[i] is either 0 or 1, and the colors are not all equal, i.e. there exist indices i and j with colors[i] != colors[j]. -/
  theorem spec_5 (colors : Slice Std.I64) (h_len : lenOf colors = 3)
      (h_bits : entriesAreBits colors)
      (h_ne : ∃ i j : ℕ, i < lenOf colors ∧ j < lenOf colors ∧ colorAt colors i ≠ colorAt colors j) :
      ∃ r : Std.I64,
        Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (colors : Slice Std.I64) (h_len : lenOf colors = 3)
        (h_bits : entriesAreBits colors)
        (h_ne : ∃ i j : ℕ, i < lenOf colors ∧ j < lenOf colors ∧ colorAt colors i ≠ colorAt colors j), ∃ r : Std.I64,
          Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns a result r, and r = len(colors).
    Preconditions: Let n = len(colors). 3 <= n <= 100, n is even, every colors[i] is either 0 or 1, and for every i with 0 <= i < n, colors[i] != colors[(i + 1) mod n]. -/
  theorem spec_6 (colors : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
      (h_le : lenOf colors ≤ 100) (h_even : lenOf colors % 2 = 0) (h_bits : entriesAreBits colors)
      (h_alt : ∀ i, i < lenOf colors → colorAt colors i ≠ colorAt colors ((i + 1) % lenOf colors)) :
      ∃ r : Std.I64,
        Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r ∧
          r.val = (lenOf colors : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (colors : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
        (h_le : lenOf colors ≤ 100) (h_even : lenOf colors % 2 = 0) (h_bits : entriesAreBits colors)
        (h_alt : ∀ i, i < lenOf colors → colorAt colors i ≠ colorAt colors ((i + 1) % lenOf colors)), ∃ r : Std.I64,
          Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r ∧
            r.val = (lenOf colors : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r and r = len(colors), then len(colors) is even and for every i with 0 <= i < len(colors), colors[i] != colors[(i + 1) mod len(colors)].
    Preconditions: Let n = len(colors). 3 <= n <= 100, and for every i with 0 <= i < n, colors[i] is either 0 or 1. -/
  theorem spec_7 (colors : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
      (h_le : lenOf colors ≤ 100) (h_bits : entriesAreBits colors) :
      ∀ r : Std.I64,
        Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r →
          r.val = (lenOf colors : ℤ) →
            lenOf colors % 2 = 0 ∧
              ∀ i, i < lenOf colors →
                colorAt colors i ≠ colorAt colors ((i + 1) % lenOf colors) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (colors : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
        (h_le : lenOf colors ≤ 100) (h_bits : entriesAreBits colors), ∀ r : Std.I64,
          Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r →
            r.val = (lenOf colors : ℤ) →
              lenOf colors % 2 = 0 ∧
                ∀ i, i < lenOf colors →
                  colorAt colors i ≠ colorAt colors ((i + 1) % lenOf colors)) := by
    sorry

  /-- Whenever number_of_alternating_groups colors returns r and number_of_alternating_groups colors2 returns r2, r = r2.
    Preconditions: Let n = len(colors). Both colors and colors2 have length n, 3 <= n <= 100, every entry of both is either 0 or 1, and for every i with 0 <= i < n, colors2[i] = 1 - colors[i]. -/
  theorem spec_8 (colors colors2 : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
      (h_le : lenOf colors ≤ 100) (h_len2 : lenOf colors2 = lenOf colors)
      (h_bits : entriesAreBits colors) (h_bits2 : entriesAreBits colors2)
      (h_compl : ∀ i, i < lenOf colors → colorAt colors2 i = 1 - colorAt colors i) :
      ∀ r r2 : Std.I64,
        Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r →
          Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors2 = ok r2 →
            r.val = r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (colors colors2 : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
        (h_le : lenOf colors ≤ 100) (h_len2 : lenOf colors2 = lenOf colors)
        (h_bits : entriesAreBits colors) (h_bits2 : entriesAreBits colors2)
        (h_compl : ∀ i, i < lenOf colors → colorAt colors2 i = 1 - colorAt colors i), ∀ r r2 : Std.I64,
          Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r →
            Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors2 = ok r2 →
              r.val = r2.val) := by
    sorry

  /-- Whenever the function returns a result r, r equals the number of circular runs of colors whose length is exactly 1. Here a circular run is a maximal set of consecutive indices modulo n on which colors is constant; if all tiles have the same color, the whole circle is one circular run of length n.
    Preconditions: Let n = len(colors). 3 <= n <= 100, and for every i with 0 <= i < n, colors[i] is either 0 or 1. -/
  theorem spec_9 (colors : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
      (h_le : lenOf colors ≤ 100) (h_bits : entriesAreBits colors) :
      ∀ r : Std.I64,
        Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r →
          r.val = (runsOfLength colors 1 : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (colors : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
        (h_le : lenOf colors ≤ 100) (h_bits : entriesAreBits colors), ∀ r : Std.I64,
          Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r →
            r.val = (runsOfLength colors 1 : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if every circular run of colors has length at least 2.
    Preconditions: Let n = len(colors). 3 <= n <= 100, every colors[i] is either 0 or 1, and not all colors are equal. -/
  theorem spec_10 (colors : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
      (h_le : lenOf colors ≤ 100) (h_bits : entriesAreBits colors)
      (h_ne : ¬ allColorsEqual colors) :
      ∀ r : Std.I64,
        Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r →
          (r.val = 0 ↔
            ∀ i, i < lenOf colors → isRunStart colors i → 2 ≤ runLen colors i) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (colors : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
        (h_le : lenOf colors ≤ 100) (h_bits : entriesAreBits colors)
        (h_ne : ¬ allColorsEqual colors), ∀ r : Std.I64,
          Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r →
            (r.val = 0 ↔
              ∀ i, i < lenOf colors → isRunStart colors i → 2 ≤ runLen colors i)) := by
    sorry

  /-- Whenever the function returns a result r, r > 0 if and only if there exists an index i with 0 <= i < n such that colors[i] != colors[(i + n - 1) mod n] and colors[i] != colors[(i + 1) mod n].
    Preconditions: Let n = len(colors). 3 <= n <= 100, and for every i with 0 <= i < n, colors[i] is either 0 or 1. -/
  theorem spec_11 (colors : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
      (h_le : lenOf colors ≤ 100) (h_bits : entriesAreBits colors) :
      ∀ r : Std.I64,
        Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r →
          (0 < r.val ↔ ∃ i, i < lenOf colors ∧ isAlternatingCenter colors i) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (colors : Slice Std.I64) (h_ge : 3 ≤ lenOf colors)
        (h_le : lenOf colors ≤ 100) (h_bits : entriesAreBits colors), ∀ r : Std.I64,
          Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors = ok r →
            (0 < r.val ↔ ∃ i, i < lenOf colors ∧ isAlternatingCenter colors i)) := by
    sorry

  end AegisSpec.NumberOfAlternatingGroups
