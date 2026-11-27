import Aegis.BinaryGap.Code.Funs

/-!
# Specifications of `Aegis.BinaryGap.binary_gap`

LeetCode problem `binary-gap`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.BinaryGap

  def IsOneBit (N k : ℕ) : Prop := N.testBit k = true

  def oneBitPositions (N : ℕ) : List ℕ := (List.range (N + 1)).filter (fun k => N.testBit k)

  def popCount (N : ℕ) : ℕ := (oneBitPositions N).length

  def adjacentGaps (ps : List ℕ) : List ℕ := (ps.zip (ps.drop 1)).map (fun q => q.2 - q.1)

  def maxGap (ps : List ℕ) : ℕ := (adjacentGaps ps).foldr max 0

  def specGap (N : ℕ) : ℕ := maxGap (oneBitPositions N)

  def IsLeastOneBit (N l : ℕ) : Prop := IsOneBit N l ∧ ∀ k, IsOneBit N k → l ≤ k

  def IsGreatestOneBit (N h : ℕ) : Prop := IsOneBit N h ∧ ∀ k, IsOneBit N k → k ≤ h

  /-- Let p_0 < p_1 < ... < p_{m-1} be the zero-based positions of the 1-bits in the binary representation of n, where position 0 is the least significant bit. Whenever the function returns a result r, the following holds: if m <= 1 then r = 0; if m >= 2 then r = max over 0 <= t < m-1 of (p_{t+1} - p_t).
    Preconditions: 1 <= n <= 1000000000. -/
  theorem spec_1 (n r : Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
      (hr : Aegis.BinaryGap.binary_gap n = ok r) :
      (popCount n.val.toNat ≤ 1 → r.val = 0) ∧
        (2 ≤ popCount n.val.toNat → r.val = (specGap n.val.toNat : ℤ)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n r : Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
        (hr : Aegis.BinaryGap.binary_gap n = ok r), (popCount n.val.toNat ≤ 1 → r.val = 0) ∧
          (2 ≤ popCount n.val.toNat → r.val = (specGap n.val.toNat : ℤ))) := by
    sorry

  /-- The function returns a result r; it does not overflow, panic, or perform an out-of-bounds access.
    Preconditions: 1 <= n <= 1000000000. -/
  theorem spec_2 (n : Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 1000000000) :
      ∃ r : Std.I64, Aegis.BinaryGap.binary_gap n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 1000000000), ∃ r : Std.I64, Aegis.BinaryGap.binary_gap n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= 29.
    Preconditions: 1 <= n <= 1000000000. -/
  theorem spec_3 (n r : Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
      (hr : Aegis.BinaryGap.binary_gap n = ok r) :
      0 ≤ r.val ∧ r.val ≤ 29 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n r : Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
        (hr : Aegis.BinaryGap.binary_gap n = ok r), 0 ≤ r.val ∧ r.val ≤ 29) := by
    sorry

  /-- Whenever the function returns a result r, r > 0.
    Preconditions: 1 <= n <= 1000000000 and the binary representation of n contains at least two digits 1. -/
  theorem spec_4 (n r : Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
      (hpop : 2 ≤ popCount n.val.toNat)
      (hr : Aegis.BinaryGap.binary_gap n = ok r) :
      0 < r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n r : Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
        (hpop : 2 ≤ popCount n.val.toNat)
        (hr : Aegis.BinaryGap.binary_gap n = ok r), 0 < r.val) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, there exist zero-based 1-bit positions i < j such that no 1-bit position k satisfies i < k < j, and r = j - i.
    Preconditions: 1 <= n <= 1000000000. -/
  theorem spec_5 (n r : Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
      (hr : Aegis.BinaryGap.binary_gap n = ok r) (hpos : 0 < r.val) :
      ∃ i j : ℕ, IsOneBit n.val.toNat i ∧ IsOneBit n.val.toNat j ∧ i < j ∧
        (∀ k : ℕ, i < k → k < j → ¬ IsOneBit n.val.toNat k) ∧
        r.val = (j : ℤ) - (i : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n r : Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
        (hr : Aegis.BinaryGap.binary_gap n = ok r) (hpos : 0 < r.val), ∃ i j : ℕ, IsOneBit n.val.toNat i ∧ IsOneBit n.val.toNat j ∧ i < j ∧
          (∀ k : ℕ, i < k → k < j → ¬ IsOneBit n.val.toNat k) ∧
          r.val = (j : ℤ) - (i : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of zero-based 1-bit positions i < j with no 1-bit position k satisfying i < k < j, we have j - i <= r.
    Preconditions: 1 <= n <= 1000000000. -/
  theorem spec_6 (n r : Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
      (hr : Aegis.BinaryGap.binary_gap n = ok r) :
      ∀ i j : ℕ, IsOneBit n.val.toNat i → IsOneBit n.val.toNat j → i < j →
        (∀ k : ℕ, i < k → k < j → ¬ IsOneBit n.val.toNat k) →
        (j : ℤ) - (i : ℤ) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n r : Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
        (hr : Aegis.BinaryGap.binary_gap n = ok r), ∀ i j : ℕ, IsOneBit n.val.toNat i → IsOneBit n.val.toNat j → i < j →
          (∀ k : ℕ, i < k → k < j → ¬ IsOneBit n.val.toNat k) →
          (j : ℤ) - (i : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, if l is the smallest zero-based 1-bit position and h is the largest zero-based 1-bit position, then r <= h - l.
    Preconditions: 1 <= n <= 1000000000 and the binary representation of n contains at least two digits 1. -/
  theorem spec_7 (n r : Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
      (hpop : 2 ≤ popCount n.val.toNat)
      (hr : Aegis.BinaryGap.binary_gap n = ok r)
      (l h : ℕ) (hl : IsLeastOneBit n.val.toNat l) (hh : IsGreatestOneBit n.val.toNat h) :
      r.val ≤ (h : ℤ) - (l : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n r : Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 1000000000)
        (hpop : 2 ≤ popCount n.val.toNat)
        (hr : Aegis.BinaryGap.binary_gap n = ok r)
        (l h : ℕ) (hl : IsLeastOneBit n.val.toNat l) (hh : IsGreatestOneBit n.val.toNat h), r.val ≤ (h : ℤ) - (l : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r on input n and returns a result s on input 2*n, we have r = s.
    Preconditions: 1 <= n <= 500000000. -/
  theorem spec_8 (n n2 r s : Std.I64)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 500000000)
      (hdouble : n2.val = 2 * n.val)
      (hr : Aegis.BinaryGap.binary_gap n = ok r)
      (hs : Aegis.BinaryGap.binary_gap n2 = ok s) :
      r = s := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n n2 r s : Std.I64)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 500000000)
        (hdouble : n2.val = 2 * n.val)
        (hr : Aegis.BinaryGap.binary_gap n = ok r)
        (hs : Aegis.BinaryGap.binary_gap n2 = ok s), r = s) := by
    sorry

  end AegisSpec.BinaryGap
