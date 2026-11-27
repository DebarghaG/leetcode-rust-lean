import Aegis.NumberOfAlternatingGroups.Code.Funs

/-!
# Specifications of `Aegis.NumberOfAlternatingGroups.number_of_alternating_groups`

LeetCode problem `alternating-groups-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumberOfAlternatingGroups

  def colorAt (colors : Slice I64) (i : Nat) : Int :=
    match colors.val[i]? with
    | some x => x.val
    | none => 0

  def colorAtZ (colors : Slice I64) (i : Int) : Int :=
    colorAt colors (i % (colors.length : Int)).toNat

  def IsAlternatingWindow (colors : Slice I64) (k : Nat) (s : Nat) : Prop :=
    ∀ j ∈ Finset.range (k - 1),
      colorAt colors ((s + j) % colors.length) ≠
        colorAt colors ((s + j + 1) % colors.length)

  instance decidableIsAlternatingWindow (colors : Slice I64) (k s : Nat) :
      Decidable (IsAlternatingWindow colors k s) := by
    unfold IsAlternatingWindow
    infer_instance

  def alternatingStarts (colors : Slice I64) (k : Nat) : Finset Nat :=
    (Finset.range colors.length).filter (fun s => IsAlternatingWindow colors k s)

  def numAlternating (colors : Slice I64) (k : Nat) : Nat :=
    (alternatingStarts colors k).card

  /-- Whenever number_of_alternating_groups(colors, k) returns a result r, with n = len(colors), r equals the number of integers s with 0 <= s < n such that for every integer j with 0 <= j <= k-2, colors[(s+j) mod n] != colors[(s+j+1) mod n]. Equivalently, r is the number of starting positions of k contiguous tiles in the circle whose colors alternate throughout the whole block.
    Preconditions: Let n = len(colors). n >= 3; for every i with 0 <= i < n, colors[i] is either 0 or 1; k is an integer with 3 <= k <= n. All cyclic indices are taken modulo n. -/
  theorem spec_1 (colors : Slice I64) (k : I64)
      (hlen : 3 ≤ colors.length)
      (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
      (hk : 3 ≤ k.val ∧ k.val ≤ (colors.length : Int)) :
      ∀ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
        r.val = (numAlternating colors k.val.toNat : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (colors : Slice I64) (k : I64)
        (hlen : 3 ≤ colors.length)
        (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
        (hk : 3 ≤ k.val ∧ k.val ≤ (colors.length : Int)), ∀ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
          r.val = (numAlternating colors k.val.toNat : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, number_of_alternating_groups(colors, k) returns a result r; it does not fail, panic, overflow, or access memory out of bounds.
    Preconditions: Let n = len(colors). n >= 3; for every i with 0 <= i < n, colors[i] is either 0 or 1; k is an integer with 3 <= k <= n. All cyclic indices are taken modulo n. -/
  theorem spec_2 (colors : Slice I64) (k : I64)
      (hlen : 3 ≤ colors.length)
      (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
      (hk : 3 ≤ k.val ∧ k.val ≤ (colors.length : Int)) :
      ∃ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (colors : Slice I64) (k : I64)
        (hlen : 3 ≤ colors.length)
        (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
        (hk : 3 ≤ k.val ∧ k.val ≤ (colors.length : Int)), ∃ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r) := by
    sorry

  /-- Whenever number_of_alternating_groups(colors, k) returns r, then 0 <= r <= len(colors).
    Preconditions: Let n = len(colors). n >= 3; for every i with 0 <= i < n, colors[i] is either 0 or 1; k is an integer with 3 <= k <= n. All cyclic indices are taken modulo n. -/
  theorem spec_3 (colors : Slice I64) (k : I64)
      (hlen : 3 ≤ colors.length)
      (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
      (hk : 3 ≤ k.val ∧ k.val ≤ (colors.length : Int)) :
      ∀ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
        0 ≤ r.val ∧ r.val ≤ (colors.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (colors : Slice I64) (k : I64)
        (hlen : 3 ≤ colors.length)
        (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
        (hk : 3 ≤ k.val ∧ k.val ≤ (colors.length : Int)), ∀ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
          0 ≤ r.val ∧ r.val ≤ (colors.length : Int)) := by
    sorry

  /-- Whenever number_of_alternating_groups(colors, k) returns r, r = len(colors) if and only if for every i with 0 <= i < len(colors), colors[i] != colors[(i+1) mod len(colors)].
    Preconditions: Let n = len(colors). n >= 3; for every i with 0 <= i < n, colors[i] is either 0 or 1; k is an integer with 3 <= k <= n. All cyclic indices are taken modulo n. -/
  theorem spec_4 (colors : Slice I64) (k : I64)
      (hlen : 3 ≤ colors.length)
      (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
      (hk : 3 ≤ k.val ∧ k.val ≤ (colors.length : Int)) :
      ∀ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
        (r.val = (colors.length : Int) ↔
          ∀ i, i < colors.length →
            colorAt colors i ≠ colorAt colors ((i + 1) % colors.length)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (colors : Slice I64) (k : I64)
        (hlen : 3 ≤ colors.length)
        (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
        (hk : 3 ≤ k.val ∧ k.val ≤ (colors.length : Int)), ∀ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
          (r.val = (colors.length : Int) ↔
            ∀ i, i < colors.length →
              colorAt colors i ≠ colorAt colors ((i + 1) % colors.length))) := by
    sorry

  /-- If colors[i] = colors[0] for every i with 0 <= i < len(colors), then whenever number_of_alternating_groups(colors, k) returns r, r = 0.
    Preconditions: Let n = len(colors). n >= 3; for every i with 0 <= i < n, colors[i] is either 0 or 1; k is an integer with 3 <= k <= n. All cyclic indices are taken modulo n. -/
  theorem spec_5 (colors : Slice I64) (k : I64)
      (hlen : 3 ≤ colors.length)
      (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
      (hk : 3 ≤ k.val ∧ k.val ≤ (colors.length : Int))
      (hconst : ∀ i, i < colors.length → colorAt colors i = colorAt colors 0) :
      ∀ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
        r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (colors : Slice I64) (k : I64)
        (hlen : 3 ≤ colors.length)
        (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
        (hk : 3 ≤ k.val ∧ k.val ≤ (colors.length : Int))
        (hconst : ∀ i, i < colors.length → colorAt colors i = colorAt colors 0), ∀ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
          r.val = 0) := by
    sorry

  /-- Whenever number_of_alternating_groups(colors, k) returns r, r = 1.
    Preconditions: Let n = len(colors). n >= 3; for every i with 0 <= i < n, colors[i] is either 0 or 1; k = len(colors); and there is exactly one integer i with 0 <= i < len(colors) and colors[i] = colors[(i+1) mod len(colors)]. All cyclic indices are taken modulo n. -/
  theorem spec_6 (colors : Slice I64) (k : I64)
      (hlen : 3 ≤ colors.length)
      (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
      (hk : k.val = (colors.length : Int))
      (hunique : ∃! i, i < colors.length ∧
        colorAt colors i = colorAt colors ((i + 1) % colors.length)) :
      ∀ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
        r.val = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (colors : Slice I64) (k : I64)
        (hlen : 3 ≤ colors.length)
        (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
        (hk : k.val = (colors.length : Int))
        (hunique : ∃! i, i < colors.length ∧
          colorAt colors i = colorAt colors ((i + 1) % colors.length)), ∀ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
          r.val = 1) := by
    sorry

  /-- Whenever number_of_alternating_groups(colors, k) returns r, r = 0.
    Preconditions: Let n = len(colors). n >= 3; for every i with 0 <= i < n, colors[i] is either 0 or 1; k = len(colors); and there exist distinct integers i and j with 0 <= i < len(colors), 0 <= j < len(colors), i != j, colors[i] = colors[(i+1) mod len(colors)] and colors[j] = colors[(j+1) mod len(colors)]. All cyclic indices are taken modulo n. -/
  theorem spec_7 (colors : Slice I64) (k : I64)
      (hlen : 3 ≤ colors.length)
      (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
      (hk : k.val = (colors.length : Int))
      (hpair : ∃ i j, i < colors.length ∧ j < colors.length ∧ i ≠ j ∧
        colorAt colors i = colorAt colors ((i + 1) % colors.length) ∧
        colorAt colors j = colorAt colors ((j + 1) % colors.length)) :
      ∀ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
        r.val = 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (colors : Slice I64) (k : I64)
        (hlen : 3 ≤ colors.length)
        (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
        (hk : k.val = (colors.length : Int))
        (hpair : ∃ i j, i < colors.length ∧ j < colors.length ∧ i ≠ j ∧
          colorAt colors i = colorAt colors ((i + 1) % colors.length) ∧
          colorAt colors j = colorAt colors ((j + 1) % colors.length)), ∀ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
          r.val = 0) := by
    sorry

  /-- Whenever number_of_alternating_groups(colors, k) returns r, 0 <= r <= 1.
    Preconditions: Let n = len(colors). n >= 3; for every i with 0 <= i < n, colors[i] is either 0 or 1; len(colors) is odd; k = len(colors). All cyclic indices are taken modulo n. -/
  theorem spec_8 (colors : Slice I64) (k : I64)
      (hlen : 3 ≤ colors.length)
      (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
      (hodd : colors.length % 2 = 1)
      (hk : k.val = (colors.length : Int)) :
      ∀ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
        0 ≤ r.val ∧ r.val ≤ 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (colors : Slice I64) (k : I64)
        (hlen : 3 ≤ colors.length)
        (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
        (hodd : colors.length % 2 = 1)
        (hk : k.val = (colors.length : Int)), ∀ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
          0 ≤ r.val ∧ r.val ≤ 1) := by
    sorry

  /-- Let t be any integer and define an array colors' of the same length by colors'[i] = colors[(i+t) mod n] for 0 <= i < n. If number_of_alternating_groups(colors, k) returns r and number_of_alternating_groups(colors', k) returns r', then r = r'.
    Preconditions: Let n = len(colors). n >= 3; for every i with 0 <= i < n, colors[i] is either 0 or 1; k is an integer with 3 <= k <= n. All cyclic indices are taken modulo n. -/
  theorem spec_9 (colors colors' : Slice I64) (k : I64) (t : Int)
      (hlen : 3 ≤ colors.length)
      (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
      (hk : 3 ≤ k.val ∧ k.val ≤ (colors.length : Int))
      (hlen' : colors'.length = colors.length)
      (hshift : ∀ i, i < colors.length → colorAt colors' i = colorAtZ colors ((i : Int) + t)) :
      ∀ r r', Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
        Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors' k = ok r' →
          r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (colors colors' : Slice I64) (k : I64) (t : Int)
        (hlen : 3 ≤ colors.length)
        (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
        (hk : 3 ≤ k.val ∧ k.val ≤ (colors.length : Int))
        (hlen' : colors'.length = colors.length)
        (hshift : ∀ i, i < colors.length → colorAt colors' i = colorAtZ colors ((i : Int) + t)), ∀ r r', Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
          Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors' k = ok r' →
            r.val = r'.val) := by
    sorry

  /-- Define colors' of length n by colors'[i] = colors[(n-1-i) mod n] for 0 <= i < n. If number_of_alternating_groups(colors, k) returns r and number_of_alternating_groups(colors', k) returns r', then r = r'.
    Preconditions: Let n = len(colors). n >= 3; for every i with 0 <= i < n, colors[i] is either 0 or 1; k is an integer with 3 <= k <= n. All cyclic indices are taken modulo n. -/
  theorem spec_10 (colors colors' : Slice I64) (k : I64)
      (hlen : 3 ≤ colors.length)
      (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
      (hk : 3 ≤ k.val ∧ k.val ≤ (colors.length : Int))
      (hlen' : colors'.length = colors.length)
      (hreflect : ∀ i, i < colors.length →
        colorAt colors' i = colorAt colors ((colors.length - 1 - i) % colors.length)) :
      ∀ r r', Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
        Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors' k = ok r' →
          r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (colors colors' : Slice I64) (k : I64)
        (hlen : 3 ≤ colors.length)
        (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
        (hk : 3 ≤ k.val ∧ k.val ≤ (colors.length : Int))
        (hlen' : colors'.length = colors.length)
        (hreflect : ∀ i, i < colors.length →
          colorAt colors' i = colorAt colors ((colors.length - 1 - i) % colors.length)), ∀ r r', Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
          Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors' k = ok r' →
            r.val = r'.val) := by
    sorry

  /-- If number_of_alternating_groups(colors, k) returns r and number_of_alternating_groups(colors', k) returns r', then r = r'.
    Preconditions: Let n = len(colors). n >= 3; for every i with 0 <= i < n, colors[i] is either 0 or 1; k is an integer with 3 <= k <= n. colors' is an array of length n with entries in {0,1}, and for every i with 0 <= i < n, colors[i] = colors[(i+1) mod n] if and only if colors'[i] = colors'[(i+1) mod n]. All cyclic indices are taken modulo n. -/
  theorem spec_11 (colors colors' : Slice I64) (k : I64)
      (hlen : 3 ≤ colors.length)
      (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
      (hk : 3 ≤ k.val ∧ k.val ≤ (colors.length : Int))
      (hlen' : colors'.length = colors.length)
      (hbin' : ∀ i, i < colors'.length → colorAt colors' i = 0 ∨ colorAt colors' i = 1)
      (hedges : ∀ i, i < colors.length →
        (colorAt colors i = colorAt colors ((i + 1) % colors.length) ↔
          colorAt colors' i = colorAt colors' ((i + 1) % colors'.length))) :
      ∀ r r', Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
        Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors' k = ok r' →
          r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (colors colors' : Slice I64) (k : I64)
        (hlen : 3 ≤ colors.length)
        (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
        (hk : 3 ≤ k.val ∧ k.val ≤ (colors.length : Int))
        (hlen' : colors'.length = colors.length)
        (hbin' : ∀ i, i < colors'.length → colorAt colors' i = 0 ∨ colorAt colors' i = 1)
        (hedges : ∀ i, i < colors.length →
          (colorAt colors i = colorAt colors ((i + 1) % colors.length) ↔
            colorAt colors' i = colorAt colors' ((i + 1) % colors'.length))), ∀ r r', Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
          Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors' k = ok r' →
            r.val = r'.val) := by
    sorry

  /-- Whenever number_of_alternating_groups(colors, k) returns r, r > 0 if and only if there exists an integer s with 0 <= s < n such that for every j with 0 <= j <= k-2, colors[(s+j) mod n] != colors[(s+j+1) mod n].
    Preconditions: Let n = len(colors). n >= 3; for every i with 0 <= i < n, colors[i] is either 0 or 1; k is an integer with 3 <= k <= n. All cyclic indices are taken modulo n. -/
  theorem spec_12 (colors : Slice I64) (k : I64)
      (hlen : 3 ≤ colors.length)
      (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
      (hk : 3 ≤ k.val ∧ k.val ≤ (colors.length : Int)) :
      ∀ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
        (0 < r.val ↔ ∃ s, s < colors.length ∧ IsAlternatingWindow colors k.val.toNat s) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (colors : Slice I64) (k : I64)
        (hlen : 3 ≤ colors.length)
        (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
        (hk : 3 ≤ k.val ∧ k.val ≤ (colors.length : Int)), ∀ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
          (0 < r.val ↔ ∃ s, s < colors.length ∧ IsAlternatingWindow colors k.val.toNat s)) := by
    sorry

  /-- If number_of_alternating_groups(colors, k1) returns r1 and number_of_alternating_groups(colors, k2) returns r2, then r2 <= r1.
    Preconditions: Let n = len(colors). n >= 3; for every i with 0 <= i < n, colors[i] is either 0 or 1; k1 and k2 are integers with 3 <= k1 <= k2 <= n. All cyclic indices are taken modulo n. -/
  theorem spec_13 (colors : Slice I64) (k1 k2 : I64)
      (hlen : 3 ≤ colors.length)
      (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
      (hk : 3 ≤ k1.val ∧ k1.val ≤ k2.val ∧ k2.val ≤ (colors.length : Int)) :
      ∀ r1 r2, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k1 = ok r1 →
        Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k2 = ok r2 →
          r2.val ≤ r1.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (colors : Slice I64) (k1 k2 : I64)
        (hlen : 3 ≤ colors.length)
        (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
        (hk : 3 ≤ k1.val ∧ k1.val ≤ k2.val ∧ k2.val ≤ (colors.length : Int)), ∀ r1 r2, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k1 = ok r1 →
          Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k2 = ok r2 →
            r2.val ≤ r1.val) := by
    sorry

  /-- Whenever number_of_alternating_groups(colors, k) returns r, r = 0 or r = len(colors).
    Preconditions: Let n = len(colors). n >= 3; for every i with 0 <= i < n, colors[i] is either 0 or 1; len(colors) is even; k = len(colors). All cyclic indices are taken modulo n. -/
  theorem spec_14 (colors : Slice I64) (k : I64)
      (hlen : 3 ≤ colors.length)
      (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
      (heven : colors.length % 2 = 0)
      (hk : k.val = (colors.length : Int)) :
      ∀ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
        r.val = 0 ∨ r.val = (colors.length : Int) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (colors : Slice I64) (k : I64)
        (hlen : 3 ≤ colors.length)
        (hbin : ∀ i, i < colors.length → colorAt colors i = 0 ∨ colorAt colors i = 1)
        (heven : colors.length % 2 = 0)
        (hk : k.val = (colors.length : Int)), ∀ r, Aegis.NumberOfAlternatingGroups.number_of_alternating_groups colors k = ok r →
          r.val = 0 ∨ r.val = (colors.length : Int)) := by
    sorry

  end AegisSpec.NumberOfAlternatingGroups
