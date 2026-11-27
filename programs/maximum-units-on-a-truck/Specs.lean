import Aegis.MaximumUnits.Code.Funs

/-!
# Specifications of `Aegis.MaximumUnits.maximum_units`

LeetCode problem `maximum-units-on-a-truck`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaximumUnits

namespace AegisSpec.MaximumUnits

abbrev BoxTypes := Slice (alloc.vec.Vec Std.I64)

def i64ToInt (x : I64) : Int := x.val

def bAt (bt : BoxTypes) (i : Nat) : Int :=
  match bt.val[i]? with
  | some row => ((row.val[0]?).map i64ToInt).getD 0
  | none => 0

def uAt (bt : BoxTypes) (i : Nat) : Int :=
  match bt.val[i]? with
  | some row => ((row.val[1]?).map i64ToInt).getD 0
  | none => 0

def unitsList (bt : BoxTypes) (n : Nat) : List Int :=
  (List.range n).map (uAt bt)

def maxU (bt : BoxTypes) (n : Nat) : Int :=
  match unitsList bt n with
  | [] => 0
  | x :: xs => xs.foldr max x

def minU (bt : BoxTypes) (n : Nat) : Int :=
  match unitsList bt n with
  | [] => 0
  | x :: xs => xs.foldr min x

def totalBoxes (bt : BoxTypes) (n : Nat) : Int :=
  ∑ i ∈ Finset.range n, bAt bt i

def fullValue (bt : BoxTypes) (n : Nat) : Int :=
  ∑ i ∈ Finset.range n, bAt bt i * uAt bt i

def expanded (bt : BoxTypes) (n : Nat) : List Int :=
  (List.range n).flatMap (fun i => List.replicate (bAt bt i).toNat (uAt bt i))

def ValidSelection (bt : BoxTypes) (n : Nat) (truck : Int) (k : Nat → Int) : Prop :=
  (∀ i, i < n → 0 ≤ k i ∧ k i ≤ bAt bt i) ∧
    (∑ i ∈ Finset.range n, k i) ≤ truck

def selectionValue (bt : BoxTypes) (n : Nat) (k : Nat → Int) : Int :=
  ∑ i ∈ Finset.range n, k i * uAt bt i

def IsSortedDesc (s : List Int) : Prop :=
  s.Pairwise (fun a b => a ≥ b)

def sumTop (s : List Int) (m : Nat) : Int :=
  ∑ j ∈ Finset.range m, s.getD j 0

structure InputOK (bt : BoxTypes) (n : Nat) (truck : Int) : Prop where

  hn_pos : 1 ≤ n

  hn_le : n ≤ 1000

  hn_len : bt.val.length = n

  hrow : ∀ i, i < n → (bt.val[i]?).map (fun r => r.val.length) = some 2

  hb_pos : ∀ i, i < n → 1 ≤ bAt bt i

  hb_le : ∀ i, i < n → bAt bt i ≤ 1000

  hu_pos : ∀ i, i < n → 1 ≤ uAt bt i

  hu_le : ∀ i, i < n → uAt bt i ≤ 1000

  ht_pos : 1 ≤ truck

  ht_le : truck ≤ 1000000

/-- The function returns a result r and r is the maximum, over all selections (k_0,...,k_{n-1}) of whole boxes with 0 ≤ k_i ≤ b_i for every i and Σ_i k_i ≤ truckSize, of Σ_i k_i * u_i. Equivalently, r equals the largest total number of units that can be put on the truck by choosing at most truckSize boxes from the given types, taking k_i boxes of type i.
  Preconditions: Let n = len(boxTypes). Assume 1 ≤ n ≤ 1000; for every i with 0 ≤ i < n, len(boxTypes[i]) = 2, and if b_i = boxTypes[i][0] and u_i = boxTypes[i][1], then 1 ≤ b_i ≤ 1000 and 1 ≤ u_i ≤ 1000; and 1 ≤ truckSize ≤ 1,000,000. All arithmetic in the statements is mathematical integer arithmetic; under these bounds all sums and products mentioned lie within the 64-bit signed range. -/
theorem spec_1 (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val) :
    ∃ r, maximum_units bt truck = ok r ∧
      (∃ k, ValidSelection bt n truck.val k ∧ selectionValue bt n k = r.val) ∧
      (∀ k, ValidSelection bt n truck.val k → selectionValue bt n k ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val), ∃ r, maximum_units bt truck = ok r ∧
      (∃ k, ValidSelection bt n truck.val k ∧ selectionValue bt n k = r.val) ∧
      (∀ k, ValidSelection bt n truck.val k → selectionValue bt n k ≤ r.val)) := by
  sorry

/-- The function returns a result r and there exists a selection (k_0,...,k_{n-1}) of whole boxes such that 0 ≤ k_i ≤ b_i for every i, Σ_i k_i = min(truckSize, Σ_i b_i), and r = Σ_i k_i * u_i.
  Preconditions: Let n = len(boxTypes). Assume 1 ≤ n ≤ 1000; for every i with 0 ≤ i < n, len(boxTypes[i]) = 2, and if b_i = boxTypes[i][0] and u_i = boxTypes[i][1], then 1 ≤ b_i ≤ 1000 and 1 ≤ u_i ≤ 1000; and 1 ≤ truckSize ≤ 1,000,000. All arithmetic in the statements is mathematical integer arithmetic; under these bounds all sums and products mentioned lie within the 64-bit signed range. -/
theorem spec_2 (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val) :
    ∃ r, maximum_units bt truck = ok r ∧
      ∃ k, ValidSelection bt n truck.val k ∧
        (∑ i ∈ Finset.range n, k i) = min truck.val (totalBoxes bt n) ∧
        r.val = selectionValue bt n k := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val), ∃ r, maximum_units bt truck = ok r ∧
      ∃ k, ValidSelection bt n truck.val k ∧
        (∑ i ∈ Finset.range n, k i) = min truck.val (totalBoxes bt n) ∧
        r.val = selectionValue bt n k) := by
  sorry

/-- The function returns a result r and for every selection (k_0,...,k_{n-1}) of whole boxes with 0 ≤ k_i ≤ b_i for every i and Σ_i k_i ≤ truckSize, we have Σ_i k_i * u_i ≤ r.
  Preconditions: Let n = len(boxTypes). Assume 1 ≤ n ≤ 1000; for every i with 0 ≤ i < n, len(boxTypes[i]) = 2, and if b_i = boxTypes[i][0] and u_i = boxTypes[i][1], then 1 ≤ b_i ≤ 1000 and 1 ≤ u_i ≤ 1000; and 1 ≤ truckSize ≤ 1,000,000. All arithmetic in the statements is mathematical integer arithmetic; under these bounds all sums and products mentioned lie within the 64-bit signed range. -/
theorem spec_3 (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val) :
    ∃ r, maximum_units bt truck = ok r ∧
      ∀ k, ValidSelection bt n truck.val k → selectionValue bt n k ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val), ∃ r, maximum_units bt truck = ok r ∧
      ∀ k, ValidSelection bt n truck.val k → selectionValue bt n k ≤ r.val) := by
  sorry

/-- The function returns a result r and r ≥ max_{0 ≤ i < n} u_i.
  Preconditions: Let n = len(boxTypes). Assume 1 ≤ n ≤ 1000; for every i with 0 ≤ i < n, len(boxTypes[i]) = 2, and if b_i = boxTypes[i][0] and u_i = boxTypes[i][1], then 1 ≤ b_i ≤ 1000 and 1 ≤ u_i ≤ 1000; and 1 ≤ truckSize ≤ 1,000,000. All arithmetic in the statements is mathematical integer arithmetic; under these bounds all sums and products mentioned lie within the 64-bit signed range. -/
theorem spec_4 (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val) :
    ∃ r, maximum_units bt truck = ok r ∧ maxU bt n ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val), ∃ r, maximum_units bt truck = ok r ∧ maxU bt n ≤ r.val) := by
  sorry

/-- The function returns a result r and r ≤ truckSize * (max_{0 ≤ i < n} u_i).
  Preconditions: Let n = len(boxTypes). Assume 1 ≤ n ≤ 1000; for every i with 0 ≤ i < n, len(boxTypes[i]) = 2, and if b_i = boxTypes[i][0] and u_i = boxTypes[i][1], then 1 ≤ b_i ≤ 1000 and 1 ≤ u_i ≤ 1000; and 1 ≤ truckSize ≤ 1,000,000. All arithmetic in the statements is mathematical integer arithmetic; under these bounds all sums and products mentioned lie within the 64-bit signed range. -/
theorem spec_5 (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val) :
    ∃ r, maximum_units bt truck = ok r ∧ r.val ≤ truck.val * maxU bt n := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val), ∃ r, maximum_units bt truck = ok r ∧ r.val ≤ truck.val * maxU bt n) := by
  sorry

/-- The function returns a result r and r ≤ Σ_{i=0}^{n-1} b_i * u_i.
  Preconditions: Let n = len(boxTypes). Assume 1 ≤ n ≤ 1000; for every i with 0 ≤ i < n, len(boxTypes[i]) = 2, and if b_i = boxTypes[i][0] and u_i = boxTypes[i][1], then 1 ≤ b_i ≤ 1000 and 1 ≤ u_i ≤ 1000; and 1 ≤ truckSize ≤ 1,000,000. All arithmetic in the statements is mathematical integer arithmetic; under these bounds all sums and products mentioned lie within the 64-bit signed range. -/
theorem spec_6 (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val) :
    ∃ r, maximum_units bt truck = ok r ∧ r.val ≤ fullValue bt n := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val), ∃ r, maximum_units bt truck = ok r ∧ r.val ≤ fullValue bt n) := by
  sorry

/-- The function returns a result r and r ≥ min(truckSize, Σ_{i=0}^{n-1} b_i) * (min_{0 ≤ i < n} u_i).
  Preconditions: Let n = len(boxTypes). Assume 1 ≤ n ≤ 1000; for every i with 0 ≤ i < n, len(boxTypes[i]) = 2, and if b_i = boxTypes[i][0] and u_i = boxTypes[i][1], then 1 ≤ b_i ≤ 1000 and 1 ≤ u_i ≤ 1000; and 1 ≤ truckSize ≤ 1,000,000. All arithmetic in the statements is mathematical integer arithmetic; under these bounds all sums and products mentioned lie within the 64-bit signed range. -/
theorem spec_7 (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val) :
    ∃ r, maximum_units bt truck = ok r ∧
      min truck.val (totalBoxes bt n) * minU bt n ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val), ∃ r, maximum_units bt truck = ok r ∧
      min truck.val (totalBoxes bt n) * minU bt n ≤ r.val) := by
  sorry

/-- The function returns a result r and, if Σ_{i=0}^{n-1} b_i ≤ truckSize, then r = Σ_{i=0}^{n-1} b_i * u_i.
  Preconditions: Let n = len(boxTypes). Assume 1 ≤ n ≤ 1000; for every i with 0 ≤ i < n, len(boxTypes[i]) = 2, and if b_i = boxTypes[i][0] and u_i = boxTypes[i][1], then 1 ≤ b_i ≤ 1000 and 1 ≤ u_i ≤ 1000; and 1 ≤ truckSize ≤ 1,000,000. All arithmetic in the statements is mathematical integer arithmetic; under these bounds all sums and products mentioned lie within the 64-bit signed range. -/
theorem spec_8 (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val) :
    ∃ r, maximum_units bt truck = ok r ∧
      (totalBoxes bt n ≤ truck.val → r.val = fullValue bt n) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val), ∃ r, maximum_units bt truck = ok r ∧
      (totalBoxes bt n ≤ truck.val → r.val = fullValue bt n)) := by
  sorry

/-- The function returns a result r and, if truckSize = 1, then r = max_{0 ≤ i < n} u_i.
  Preconditions: Let n = len(boxTypes). Assume 1 ≤ n ≤ 1000; for every i with 0 ≤ i < n, len(boxTypes[i]) = 2, and if b_i = boxTypes[i][0] and u_i = boxTypes[i][1], then 1 ≤ b_i ≤ 1000 and 1 ≤ u_i ≤ 1000; and 1 ≤ truckSize ≤ 1,000,000. All arithmetic in the statements is mathematical integer arithmetic; under these bounds all sums and products mentioned lie within the 64-bit signed range. -/
theorem spec_9 (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val) :
    ∃ r, maximum_units bt truck = ok r ∧ (truck.val = 1 → r.val = maxU bt n) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val), ∃ r, maximum_units bt truck = ok r ∧ (truck.val = 1 → r.val = maxU bt n)) := by
  sorry

/-- The function returns a result r and, if there is an integer c such that u_i = c for every i with 0 ≤ i < n, then r = min(truckSize, Σ_{i=0}^{n-1} b_i) * c.
  Preconditions: Let n = len(boxTypes). Assume 1 ≤ n ≤ 1000; for every i with 0 ≤ i < n, len(boxTypes[i]) = 2, and if b_i = boxTypes[i][0] and u_i = boxTypes[i][1], then 1 ≤ b_i ≤ 1000 and 1 ≤ u_i ≤ 1000; and 1 ≤ truckSize ≤ 1,000,000. All arithmetic in the statements is mathematical integer arithmetic; under these bounds all sums and products mentioned lie within the 64-bit signed range. -/
theorem spec_10 (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val) :
    ∃ r, maximum_units bt truck = ok r ∧
      (∀ c, (∀ i, i < n → uAt bt i = c) →
        r.val = min truck.val (totalBoxes bt n) * c) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val), ∃ r, maximum_units bt truck = ok r ∧
      (∀ c, (∀ i, i < n → uAt bt i = c) →
        r.val = min truck.val (totalBoxes bt n) * c)) := by
  sorry

/-- The function returns a result r and, if b_i = 1 for every i with 0 ≤ i < n, then r = Σ_{j=1}^{M} u_{(j)}, where M = min(truckSize, n) and u_{(1)} ≥ u_{(2)} ≥ ... ≥ u_{(n)} is the list of the n values u_i sorted in nonincreasing order.
  Preconditions: Let n = len(boxTypes). Assume 1 ≤ n ≤ 1000; for every i with 0 ≤ i < n, len(boxTypes[i]) = 2, and if b_i = boxTypes[i][0] and u_i = boxTypes[i][1], then 1 ≤ b_i ≤ 1000 and 1 ≤ u_i ≤ 1000; and 1 ≤ truckSize ≤ 1,000,000. All arithmetic in the statements is mathematical integer arithmetic; under these bounds all sums and products mentioned lie within the 64-bit signed range. -/
theorem spec_11 (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val) :
    ∃ r, maximum_units bt truck = ok r ∧
      ((∀ i, i < n → bAt bt i = 1) →
        ∀ s : List Int, s.length = n → s.Perm (unitsList bt n) → IsSortedDesc s →
          r.val = sumTop s (min truck.val.toNat n)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val), ∃ r, maximum_units bt truck = ok r ∧
      ((∀ i, i < n → bAt bt i = 1) →
        ∀ s : List Int, s.length = n → s.Perm (unitsList bt n) → IsSortedDesc s →
          r.val = sumTop s (min truck.val.toNat n))) := by
  sorry

/-- The function returns a result r and, for every bijection π on {0,...,n-1}, if boxTypes' is a slice of length n with boxTypes'[i] = boxTypes[π(i)] for every i, and if maximum_units boxTypes' truckSize returns r', then r' = r.
  Preconditions: Let n = len(boxTypes). Assume 1 ≤ n ≤ 1000; for every i with 0 ≤ i < n, len(boxTypes[i]) = 2, and if b_i = boxTypes[i][0] and u_i = boxTypes[i][1], then 1 ≤ b_i ≤ 1000 and 1 ≤ u_i ≤ 1000; and 1 ≤ truckSize ≤ 1,000,000. All arithmetic in the statements is mathematical integer arithmetic; under these bounds all sums and products mentioned lie within the 64-bit signed range. -/
theorem spec_12 (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val) :
    ∃ r, maximum_units bt truck = ok r ∧
      ∀ (π : Equiv.Perm (Fin n)) (bt' : BoxTypes),
        bt'.val.length = n →
        (∀ i : Fin n, bt'.val[(i : Nat)]? = bt.val[((π i : Fin n) : Nat)]?) →
        ∀ r', maximum_units bt' truck = ok r' → r'.val = r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val), ∃ r, maximum_units bt truck = ok r ∧
      ∀ (π : Equiv.Perm (Fin n)) (bt' : BoxTypes),
        bt'.val.length = n →
        (∀ i : Fin n, bt'.val[(i : Nat)]? = bt.val[((π i : Fin n) : Nat)]?) →
        ∀ r', maximum_units bt' truck = ok r' → r'.val = r.val) := by
  sorry

/-- The function returns a result r and, for every integer s with 1 ≤ s ≤ truckSize, whenever maximum_units boxTypes s returns a result r_s, we have r_s ≤ r.
  Preconditions: Let n = len(boxTypes). Assume 1 ≤ n ≤ 1000; for every i with 0 ≤ i < n, len(boxTypes[i]) = 2, and if b_i = boxTypes[i][0] and u_i = boxTypes[i][1], then 1 ≤ b_i ≤ 1000 and 1 ≤ u_i ≤ 1000; and 1 ≤ truckSize ≤ 1,000,000. All arithmetic in the statements is mathematical integer arithmetic; under these bounds all sums and products mentioned lie within the 64-bit signed range. -/
theorem spec_13 (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val) :
    ∃ r, maximum_units bt truck = ok r ∧
      ∀ (s : I64) (r_s : I64), 1 ≤ s.val → s.val ≤ truck.val →
        maximum_units bt s = ok r_s → r_s.val ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val), ∃ r, maximum_units bt truck = ok r ∧
      ∀ (s : I64) (r_s : I64), 1 ≤ s.val → s.val ≤ truck.val →
        maximum_units bt s = ok r_s → r_s.val ≤ r.val) := by
  sorry

/-- The function returns a result r and, if maximum_units boxTypes' truckSize returns r', then r' ≥ r.
  Preconditions: Let n = len(boxTypes). Assume 1 ≤ n ≤ 1000; for every i with 0 ≤ i < n, len(boxTypes[i]) = 2, and if b_i = boxTypes[i][0] and u_i = boxTypes[i][1], then 1 ≤ b_i ≤ 1000 and 1 ≤ u_i ≤ 1000; and 1 ≤ truckSize ≤ 1,000,000. In addition, let boxTypes' be any slice of length n such that for every i with 0 ≤ i < n, len(boxTypes'[i]) = 2, and if b'_i = boxTypes'[i][0] and u'_i = boxTypes'[i][1], then 1 ≤ b'_i ≤ 1000, u'_i = u_i, and b'_i ≥ b_i. All arithmetic in the statements is mathematical integer arithmetic; under these bounds all sums and products mentioned lie within the 64-bit signed range. -/
theorem spec_14 (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val)
    (bt' : BoxTypes)
    (hbt' : bt'.val.length = n)
    (hrow' : ∀ i, i < n → (bt'.val[i]?).map (fun r => r.val.length) = some 2)
    (hb' : ∀ i, i < n →
      1 ≤ bAt bt' i ∧ bAt bt' i ≤ 1000 ∧ bAt bt i ≤ bAt bt' i)
    (hu' : ∀ i, i < n → uAt bt' i = uAt bt i) :
    ∃ r, maximum_units bt truck = ok r ∧
      ∀ r', maximum_units bt' truck = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val)
    (bt' : BoxTypes)
    (hbt' : bt'.val.length = n)
    (hrow' : ∀ i, i < n → (bt'.val[i]?).map (fun r => r.val.length) = some 2)
    (hb' : ∀ i, i < n →
      1 ≤ bAt bt' i ∧ bAt bt' i ≤ 1000 ∧ bAt bt i ≤ bAt bt' i)
    (hu' : ∀ i, i < n → uAt bt' i = uAt bt i), ∃ r, maximum_units bt truck = ok r ∧
      ∀ r', maximum_units bt' truck = ok r' → r.val ≤ r'.val) := by
  sorry

/-- The function returns a result r and does not fail: no arithmetic overflow, no out-of-bounds access to boxTypes or to any boxTypes[i], and no panic occurs.
  Preconditions: Let n = len(boxTypes). Assume 1 ≤ n ≤ 1000; for every i with 0 ≤ i < n, len(boxTypes[i]) = 2, and if b_i = boxTypes[i][0] and u_i = boxTypes[i][1], then 1 ≤ b_i ≤ 1000 and 1 ≤ u_i ≤ 1000; and 1 ≤ truckSize ≤ 1,000,000. All arithmetic in the statements is mathematical integer arithmetic; under these bounds all sums and products mentioned lie within the 64-bit signed range. -/
theorem spec_15 (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val) :
    ∃ r, maximum_units bt truck = ok r := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val), ∃ r, maximum_units bt truck = ok r) := by
  sorry

/-- Let T = Σ_{i=0}^{n-1} b_i and let v_1 ≥ v_2 ≥ ... ≥ v_T be the multiset in which each u_i occurs exactly b_i times. Then the function returns a result r and r = Σ_{j=1}^{min(truckSize,T)} v_j.
  Preconditions: Let n = len(boxTypes). Assume 1 ≤ n ≤ 1000; for every i with 0 ≤ i < n, len(boxTypes[i]) = 2, and if b_i = boxTypes[i][0] and u_i = boxTypes[i][1], then 1 ≤ b_i ≤ 1000 and 1 ≤ u_i ≤ 1000; and 1 ≤ truckSize ≤ 1,000,000. All arithmetic in the statements is mathematical integer arithmetic; under these bounds all sums and products mentioned lie within the 64-bit signed range. -/
theorem spec_16 (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val) :
    ∃ r, maximum_units bt truck = ok r ∧
      ∀ s : List Int, s.length = (expanded bt n).length →
        s.Perm (expanded bt n) → IsSortedDesc s →
          r.val = sumTop s (min truck.val.toNat (expanded bt n).length) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (bt : BoxTypes) (n : Nat) (truck : I64) (h : InputOK bt n truck.val), ∃ r, maximum_units bt truck = ok r ∧
      ∀ s : List Int, s.length = (expanded bt n).length →
        s.Perm (expanded bt n) → IsSortedDesc s →
          r.val = sumTop s (min truck.val.toNat (expanded bt n).length)) := by
  sorry

end AegisSpec.MaximumUnits
