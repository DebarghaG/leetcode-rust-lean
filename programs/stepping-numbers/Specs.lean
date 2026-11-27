import Aegis.CountSteppingNumbers.Code.Funs

/-!
# Specifications of `Aegis.CountSteppingNumbers.count_stepping_numbers`

LeetCode problem `stepping-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountSteppingNumbers

  namespace AegisSpec.CountSteppingNumbers

  private def digitsGo : Nat → List Nat → List Nat
    | 0, acc => acc
    | (n + 1), acc => digitsGo ((n + 1) / 10) ((n + 1) % 10 :: acc)
  termination_by n _ => n
  decreasing_by exact Nat.div_lt_self (by omega) (by omega)

  def decDigits (n : Nat) : List Nat := if n = 0 then [0] else digitsGo n []

  def AdjacentDigitsStep : List Nat → Prop
    | [] => True
    | [_] => True
    | a :: b :: rest => (a + 1 = b ∨ b + 1 = a) ∧ AdjacentDigitsStep (b :: rest)

  def IsStepping (x : Int) : Prop := 0 ≤ x ∧ AdjacentDigitsStep (decDigits x.toNat)

  def Occurs (r : alloc.vec.Vec Std.I64) (x : Int) : Prop :=
    ∃ i : Nat, i < r.val.length ∧ (r.val[i]!).val = x

  noncomputable def steppingCountIco (lo hi : Int) : Nat := by
    classical
    exact ((Finset.range (hi - lo).toNat).filter (fun k : Nat => IsStepping (lo + (k : Int)))).card

  noncomputable def steppingCountIcc (lo hi : Int) : Nat := steppingCountIco lo (hi + 1)

  /-- The function returns a result vector r such that: (1) for every i with 0 <= i < len(r), r[i] is a stepping number and low <= r[i] <= high, where a nonnegative integer n is stepping iff, in its base-10 representation without leading zeros (with n = 0 written as the single digit 0), every pair of adjacent digits has absolute difference exactly 1; (2) for every integer x, x occurs in r if and only if low <= x <= high and x is stepping; (3) for every i, j with 0 <= i < j < len(r), r[i] <= r[j]; (4) for every i, j with 0 <= i < len(r), 0 <= j < len(r), and i != j, r[i] != r[j].
    Preconditions: The arguments low and high, viewed as mathematical integers, satisfy 0 <= low <= high <= 2000000000. -/
  theorem spec_1 (low high : Std.I64)
      (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
      (h_high : high.val ≤ 2000000000) :
      ∃ r : alloc.vec.Vec Std.I64,
        count_stepping_numbers low high = ok r ∧
        (∀ i : Nat, i < r.val.length →
            IsStepping (r.val[i]!).val ∧
              low.val ≤ (r.val[i]!).val ∧ (r.val[i]!).val ≤ high.val) ∧
        (∀ x : Int, Occurs r x ↔ low.val ≤ x ∧ x ≤ high.val ∧ IsStepping x) ∧
        (∀ i j : Nat, i < j → j < r.val.length → (r.val[i]!).val ≤ (r.val[j]!).val) ∧
        (∀ i j : Nat, i < r.val.length → j < r.val.length → i ≠ j →
            (r.val[i]!).val ≠ (r.val[j]!).val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (low high : Std.I64)
        (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
        (h_high : high.val ≤ 2000000000), ∃ r : alloc.vec.Vec Std.I64,
          count_stepping_numbers low high = ok r ∧
          (∀ i : Nat, i < r.val.length →
              IsStepping (r.val[i]!).val ∧
                low.val ≤ (r.val[i]!).val ∧ (r.val[i]!).val ≤ high.val) ∧
          (∀ x : Int, Occurs r x ↔ low.val ≤ x ∧ x ≤ high.val ∧ IsStepping x) ∧
          (∀ i j : Nat, i < j → j < r.val.length → (r.val[i]!).val ≤ (r.val[j]!).val) ∧
          (∀ i j : Nat, i < r.val.length → j < r.val.length → i ≠ j →
              (r.val[i]!).val ≠ (r.val[j]!).val)) := by
    sorry

  /-- The function returns a result r; it does not fail, overflow, panic, or access memory out of bounds.
    Preconditions: The arguments low and high, viewed as mathematical integers, satisfy 0 <= low <= high <= 2000000000. -/
  theorem spec_2 (low high : Std.I64)
      (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
      (h_high : high.val ≤ 2000000000) :
      ∃ r : alloc.vec.Vec Std.I64, count_stepping_numbers low high = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (low high : Std.I64)
        (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
        (h_high : high.val ≤ 2000000000), ∃ r : alloc.vec.Vec Std.I64, count_stepping_numbers low high = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i, j with 0 <= i < j < len(r), r[i] <= r[j].
    Preconditions: The arguments low and high, viewed as mathematical integers, satisfy 0 <= low <= high <= 2000000000. -/
  theorem spec_3 (low high : Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
      (h_high : high.val ≤ 2000000000)
      (hr : count_stepping_numbers low high = ok r) :
      ∀ i j : Nat, i < j → j < r.val.length → (r.val[i]!).val ≤ (r.val[j]!).val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (low high : Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
        (h_high : high.val ≤ 2000000000)
        (hr : count_stepping_numbers low high = ok r), ∀ i j : Nat, i < j → j < r.val.length → (r.val[i]!).val ≤ (r.val[j]!).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i, j with 0 <= i < len(r), 0 <= j < len(r), and i != j, r[i] != r[j].
    Preconditions: The arguments low and high, viewed as mathematical integers, satisfy 0 <= low <= high <= 2000000000. -/
  theorem spec_4 (low high : Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
      (h_high : high.val ≤ 2000000000)
      (hr : count_stepping_numbers low high = ok r) :
      ∀ i j : Nat, i < r.val.length → j < r.val.length → i ≠ j →
        (r.val[i]!).val ≠ (r.val[j]!).val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (low high : Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
        (h_high : high.val ≤ 2000000000)
        (hr : count_stepping_numbers low high = ok r), ∀ i j : Nat, i < r.val.length → j < r.val.length → i ≠ j →
          (r.val[i]!).val ≠ (r.val[j]!).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), low <= r[i] <= high.
    Preconditions: The arguments low and high, viewed as mathematical integers, satisfy 0 <= low <= high <= 2000000000. -/
  theorem spec_5 (low high : Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
      (h_high : high.val ≤ 2000000000)
      (hr : count_stepping_numbers low high = ok r) :
      ∀ i : Nat, i < r.val.length →
        low.val ≤ (r.val[i]!).val ∧ (r.val[i]!).val ≤ high.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (low high : Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
        (h_high : high.val ≤ 2000000000)
        (hr : count_stepping_numbers low high = ok r), ∀ i : Nat, i < r.val.length →
          low.val ≤ (r.val[i]!).val ∧ (r.val[i]!).val ≤ high.val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), r[i] is a stepping number, where a nonnegative integer n is stepping iff, in its base-10 representation without leading zeros (with n = 0 written as the single digit 0), every pair of adjacent digits has absolute difference exactly 1.
    Preconditions: The arguments low and high, viewed as mathematical integers, satisfy 0 <= low <= high <= 2000000000. -/
  theorem spec_6 (low high : Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
      (h_high : high.val ≤ 2000000000)
      (hr : count_stepping_numbers low high = ok r) :
      ∀ i : Nat, i < r.val.length → IsStepping (r.val[i]!).val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (low high : Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
        (h_high : high.val ≤ 2000000000)
        (hr : count_stepping_numbers low high = ok r), ∀ i : Nat, i < r.val.length → IsStepping (r.val[i]!).val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer x such that low <= x <= high and x is a stepping number, there exists an index i with 0 <= i < len(r) and r[i] = x.
    Preconditions: The arguments low and high, viewed as mathematical integers, satisfy 0 <= low <= high <= 2000000000. -/
  theorem spec_7 (low high : Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
      (h_high : high.val ≤ 2000000000)
      (hr : count_stepping_numbers low high = ok r) :
      ∀ x : Int, low.val ≤ x → x ≤ high.val → IsStepping x → Occurs r x := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (low high : Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
        (h_high : high.val ≤ 2000000000)
        (hr : count_stepping_numbers low high = ok r), ∀ x : Int, low.val ≤ x → x ≤ high.val → IsStepping x → Occurs r x) := by
    sorry

  /-- Whenever the function returns a result r, len(r) equals the number of integers x such that low <= x <= high and x is a stepping number.
    Preconditions: The arguments low and high, viewed as mathematical integers, satisfy 0 <= low <= high <= 2000000000. -/
  theorem spec_8 (low high : Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
      (h_high : high.val ≤ 2000000000)
      (hr : count_stepping_numbers low high = ok r) :
      r.val.length = steppingCountIcc low.val high.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (low high : Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
        (h_high : high.val ≤ 2000000000)
        (hr : count_stepping_numbers low high = ok r), r.val.length = steppingCountIcc low.val high.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer x, there exists an index i with 0 <= i < len(r) and r[i] = x if and only if low <= x <= high and x is a stepping number.
    Preconditions: The arguments low and high, viewed as mathematical integers, satisfy 0 <= low <= high <= 2000000000, and a nonnegative integer n is stepping iff its base-10 representation without leading zeros (with n = 0 written as the single digit 0) has every pair of adjacent digits differing by exactly 1. -/
  theorem spec_9 (low high : Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
      (h_high : high.val ≤ 2000000000)
      (h_stepping : ∀ x : Int, 0 ≤ x → (IsStepping x ↔ AdjacentDigitsStep (decDigits x.toNat)))
      (hr : count_stepping_numbers low high = ok r) :
      ∀ x : Int, Occurs r x ↔ low.val ≤ x ∧ x ≤ high.val ∧ IsStepping x := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (low high : Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
        (h_high : high.val ≤ 2000000000)
        (h_stepping : ∀ x : Int, 0 ≤ x → (IsStepping x ↔ AdjacentDigitsStep (decDigits x.toNat)))
        (hr : count_stepping_numbers low high = ok r), ∀ x : Int, Occurs r x ↔ low.val ≤ x ∧ x ≤ high.val ∧ IsStepping x) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), the number of stepping integers y such that low <= y < r[i] is exactly i.
    Preconditions: The arguments low and high, viewed as mathematical integers, satisfy 0 <= low <= high <= 2000000000, and a nonnegative integer n is stepping iff its base-10 representation without leading zeros (with n = 0 written as the single digit 0) has every pair of adjacent digits differing by exactly 1. -/
  theorem spec_10 (low high : Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
      (h_high : high.val ≤ 2000000000)
      (h_stepping : ∀ x : Int, 0 ≤ x → (IsStepping x ↔ AdjacentDigitsStep (decDigits x.toNat)))
      (hr : count_stepping_numbers low high = ok r) :
      ∀ i : Nat, i < r.val.length → steppingCountIco low.val (r.val[i]!).val = i := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (low high : Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_low : 0 ≤ low.val) (h_low_high : low.val ≤ high.val)
        (h_high : high.val ≤ 2000000000)
        (h_stepping : ∀ x : Int, 0 ≤ x → (IsStepping x ↔ AdjacentDigitsStep (decDigits x.toNat)))
        (hr : count_stepping_numbers low high = ok r), ∀ i : Nat, i < r.val.length → steppingCountIco low.val (r.val[i]!).val = i) := by
    sorry

  end AegisSpec.CountSteppingNumbers
