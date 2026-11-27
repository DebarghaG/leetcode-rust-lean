import Aegis.CountPairs.Code.Funs

/-!
# Specifications of `Aegis.CountPairs.count_pairs`

LeetCode problem `count-pairs-of-points-with-distance-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountPairs

def rows (coordinates : Slice (alloc.vec.Vec I64)) : List (List Int) :=
  coordinates.val.map fun v => v.val.map fun x => x.val

def xor64 (a b : Int) : Int := (BitVec.ofInt 64 a ^^^ BitVec.ofInt 64 b).toInt

def rowAt (cs : List (List Int)) (i : Nat) : Option (List Int) := cs[i]?

def coordAt (cs : List (List Int)) (c : Nat) (i : Nat) : Option Int :=
  (rowAt cs i).bind fun p => p[c]?

def coordXor (cs : List (List Int)) (c : Nat) (i j : Nat) : Option Int :=
  (coordAt cs c i).bind fun a => (coordAt cs c j).map fun b => xor64 a b

def dist? : List Int → List Int → Option Int
  | [x1, y1], [x2, y2] => some (xor64 x1 x2 + xor64 y1 y2)
  | _, _ => none

def distAt (cs : List (List Int)) (i j : Nat) : Option Int :=
  (rowAt cs i).bind fun p => (rowAt cs j).bind fun q => dist? p q

def pairsUpto (n : Nat) : Finset (Nat × Nat) :=
  ((Finset.range n).product (Finset.range n)).filter fun p => p.1 < p.2

def pairSet (cs : List (List Int)) (k : Int) : Finset (Nat × Nat) :=
  (pairsUpto cs.length).filter fun p => distAt cs p.1 p.2 = some k

def eqPairSet (cs : List (List Int)) : Finset (Nat × Nat) :=
  (pairsUpto cs.length).filter fun p => rowAt cs p.1 = rowAt cs p.2

def axisPairSet (cs : List (List Int)) (c : Nat) (k : Int) : Finset (Nat × Nat) :=
  (pairsUpto cs.length).filter fun p => coordXor cs c p.1 p.2 = some k

def nPairs (n : Nat) : Nat := n * (n - 1) / 2

def SliceLengthOK (cs : List (List Int)) : Prop :=
  2 ≤ cs.length ∧ cs.length ≤ 50000

def CoordBounds (cs : List (List Int)) : Prop :=
  ∀ i, i < cs.length →
    ∃ a b, cs[i]? = some [a, b] ∧ 0 ≤ a ∧ a ≤ 1000000 ∧ 0 ≤ b ∧ b ≤ 1000000

def ParamBounds (k : I64) : Prop :=
  0 ≤ k.val ∧ k.val ≤ 100

/-- Whenever count_pairs(coordinates, k) returns a result r, r is the cardinality of the set of index pairs { (i,j) | 0 <= i < j < n and (coordinates[i][0] XOR coordinates[j][0]) + (coordinates[i][1] XOR coordinates[j][1]) = k }, where XOR is bitwise exclusive-or on the 64-bit integer values. In words, r is exactly the number of unordered pairs of distinct indices whose two points have distance k under the problem's definition.
  Preconditions: Let n = len(coordinates). Base preconditions: 2 <= n <= 50000; for every i with 0 <= i < n, len(coordinates[i]) = 2, 0 <= coordinates[i][0] <= 1000000, and 0 <= coordinates[i][1] <= 1000000; and 0 <= k <= 100. -/
theorem spec_1 (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k) :
    ∀ r, Aegis.CountPairs.count_pairs coordinates k = ok r →
      r.val = ((pairSet (rows coordinates) k.val).card : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k), ∀ r, Aegis.CountPairs.count_pairs coordinates k = ok r →
      r.val = ((pairSet (rows coordinates) k.val).card : Int)) := by
  sorry

/-- For every coordinates and k satisfying the base preconditions, count_pairs(coordinates, k) returns a successful result r; it does not fail, panic, go out of bounds, or overflow. In particular, the XOR sums and the pair count fit in 64-bit integers under the stated bounds.
  Preconditions: Let n = len(coordinates). Base preconditions: 2 <= n <= 50000; for every i with 0 <= i < n, len(coordinates[i]) = 2, 0 <= coordinates[i][0] <= 1000000, and 0 <= coordinates[i][1] <= 1000000; and 0 <= k <= 100. -/
theorem spec_2 (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k) :
    ∃ r, Aegis.CountPairs.count_pairs coordinates k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k), ∃ r, Aegis.CountPairs.count_pairs coordinates k = ok r) := by
  sorry

/-- Whenever count_pairs(coordinates, k) returns a result r, 0 <= r <= n*(n-1)/2, where n = len(coordinates).
  Preconditions: Let n = len(coordinates). Base preconditions: 2 <= n <= 50000; for every i with 0 <= i < n, len(coordinates[i]) = 2, 0 <= coordinates[i][0] <= 1000000, and 0 <= coordinates[i][1] <= 1000000; and 0 <= k <= 100. -/
theorem spec_3 (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k) :
    ∀ r, Aegis.CountPairs.count_pairs coordinates k = ok r →
      0 ≤ r.val ∧ r.val ≤ (nPairs (rows coordinates).length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k), ∀ r, Aegis.CountPairs.count_pairs coordinates k = ok r →
      0 ≤ r.val ∧ r.val ≤ (nPairs (rows coordinates).length : Int)) := by
  sorry

/-- Whenever count_pairs(coordinates, k) returns a result r, r equals the number of pairs (i,j) with 0 <= i < j < n such that coordinates[i][0] = coordinates[j][0] and coordinates[i][1] = coordinates[j][1].
  Preconditions: Let n = len(coordinates). Base preconditions: 2 <= n <= 50000; for every i with 0 <= i < n, len(coordinates[i]) = 2, 0 <= coordinates[i][0] <= 1000000, and 0 <= coordinates[i][1] <= 1000000; and k = 0. -/
theorem spec_4 (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk0 : k.val = 0) :
    ∀ r, Aegis.CountPairs.count_pairs coordinates k = ok r →
      r.val = ((eqPairSet (rows coordinates)).card : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk0 : k.val = 0), ∀ r, Aegis.CountPairs.count_pairs coordinates k = ok r →
      r.val = ((eqPairSet (rows coordinates)).card : Int)) := by
  sorry

/-- Whenever count_pairs(coordinates, k) returns a result r, if k = 0 then r = n*(n-1)/2, and if k > 0 then r = 0.
  Preconditions: Let n = len(coordinates). Base preconditions: 2 <= n <= 50000; for every i with 0 <= i < n, len(coordinates[i]) = 2, 0 <= coordinates[i][0] <= 1000000, and 0 <= coordinates[i][1] <= 1000000; 0 <= k <= 100; and for every i with 0 <= i < n, coordinates[i] = coordinates[0]. -/
theorem spec_5 (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k)
    (hall : ∀ i, i < (rows coordinates).length →
      rowAt (rows coordinates) i = rowAt (rows coordinates) 0) :
    ∀ r, Aegis.CountPairs.count_pairs coordinates k = ok r →
      (k.val = 0 → r.val = (nPairs (rows coordinates).length : Int)) ∧
      (0 < k.val → r.val = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k)
    (hall : ∀ i, i < (rows coordinates).length →
      rowAt (rows coordinates) i = rowAt (rows coordinates) 0), ∀ r, Aegis.CountPairs.count_pairs coordinates k = ok r →
      (k.val = 0 → r.val = (nPairs (rows coordinates).length : Int)) ∧
      (0 < k.val → r.val = 0)) := by
  sorry

/-- Whenever count_pairs(coordinates, k) returns a result r, r = 1 if (coordinates[0][0] XOR coordinates[1][0]) + (coordinates[0][1] XOR coordinates[1][1]) = k, and r = 0 otherwise.
  Preconditions: Let n = len(coordinates). Base preconditions: 2 <= n <= 50000; for every i with 0 <= i < n, len(coordinates[i]) = 2, 0 <= coordinates[i][0] <= 1000000, and 0 <= coordinates[i][1] <= 1000000; 0 <= k <= 100; and n = 2. -/
theorem spec_6 (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k)
    (h2 : (rows coordinates).length = 2) :
    ∀ r, Aegis.CountPairs.count_pairs coordinates k = ok r →
      r.val = (if distAt (rows coordinates) 0 1 = some k.val then (1 : Int) else 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k)
    (h2 : (rows coordinates).length = 2), ∀ r, Aegis.CountPairs.count_pairs coordinates k = ok r →
      r.val = (if distAt (rows coordinates) 0 1 = some k.val then (1 : Int) else 0)) := by
  sorry

/-- Whenever count_pairs(coordinates, k) returns a result r, r equals the number of pairs (i,j) with 0 <= i < j < n such that (coordinates[i][0] XOR coordinates[j][0]) = k.
  Preconditions: Let n = len(coordinates). Base preconditions: 2 <= n <= 50000; for every i with 0 <= i < n, len(coordinates[i]) = 2, 0 <= coordinates[i][0] <= 1000000, and 0 <= coordinates[i][1] <= 1000000; 0 <= k <= 100; and for every i with 0 <= i < n, coordinates[i][1] = coordinates[0][1]. -/
theorem spec_7 (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k)
    (hall : ∀ i, i < (rows coordinates).length →
      coordAt (rows coordinates) 1 i = coordAt (rows coordinates) 1 0) :
    ∀ r, Aegis.CountPairs.count_pairs coordinates k = ok r →
      r.val = ((axisPairSet (rows coordinates) 0 k.val).card : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k)
    (hall : ∀ i, i < (rows coordinates).length →
      coordAt (rows coordinates) 1 i = coordAt (rows coordinates) 1 0), ∀ r, Aegis.CountPairs.count_pairs coordinates k = ok r →
      r.val = ((axisPairSet (rows coordinates) 0 k.val).card : Int)) := by
  sorry

/-- Whenever count_pairs(coordinates, k) returns a result r, r equals the number of pairs (i,j) with 0 <= i < j < n such that (coordinates[i][1] XOR coordinates[j][1]) = k.
  Preconditions: Let n = len(coordinates). Base preconditions: 2 <= n <= 50000; for every i with 0 <= i < n, len(coordinates[i]) = 2, 0 <= coordinates[i][0] <= 1000000, and 0 <= coordinates[i][1] <= 1000000; 0 <= k <= 100; and for every i with 0 <= i < n, coordinates[i][0] = coordinates[0][0]. -/
theorem spec_8 (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k)
    (hall : ∀ i, i < (rows coordinates).length →
      coordAt (rows coordinates) 0 i = coordAt (rows coordinates) 0 0) :
    ∀ r, Aegis.CountPairs.count_pairs coordinates k = ok r →
      r.val = ((axisPairSet (rows coordinates) 1 k.val).card : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k)
    (hall : ∀ i, i < (rows coordinates).length →
      coordAt (rows coordinates) 0 i = coordAt (rows coordinates) 0 0), ∀ r, Aegis.CountPairs.count_pairs coordinates k = ok r →
      r.val = ((axisPairSet (rows coordinates) 1 k.val).card : Int)) := by
  sorry

/-- Whenever count_pairs(coordinates, k) returns r and count_pairs(coordinates', k) returns r', we have r' = r.
  Preconditions: Let n = len(coordinates). Base preconditions for coordinates and k: 2 <= n <= 50000; for every i with 0 <= i < n, len(coordinates[i]) = 2, 0 <= coordinates[i][0] <= 1000000, and 0 <= coordinates[i][1] <= 1000000; 0 <= k <= 100. Let coordinates' be any slice of length n for which there exists a bijection pi on {0,...,n-1} such that coordinates'[i] = coordinates[pi(i)] for every i with 0 <= i < n. -/
theorem spec_9 (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k)
    (coordinates' : Slice (alloc.vec.Vec I64))
    (pi : Equiv.Perm Nat)
    (hlen' : (rows coordinates').length = (rows coordinates).length)
    (hmaps : ∀ i, i < (rows coordinates).length → pi i < (rows coordinates).length)
    (hsurj : ∀ j, j < (rows coordinates).length →
      ∃ i, i < (rows coordinates).length ∧ pi i = j)
    (hperm : ∀ i, i < (rows coordinates).length →
      rowAt (rows coordinates') i = rowAt (rows coordinates) (pi i)) :
    ∀ r r', Aegis.CountPairs.count_pairs coordinates k = ok r →
      Aegis.CountPairs.count_pairs coordinates' k = ok r' → r' = r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k)
    (coordinates' : Slice (alloc.vec.Vec I64))
    (pi : Equiv.Perm Nat)
    (hlen' : (rows coordinates').length = (rows coordinates).length)
    (hmaps : ∀ i, i < (rows coordinates).length → pi i < (rows coordinates).length)
    (hsurj : ∀ j, j < (rows coordinates).length →
      ∃ i, i < (rows coordinates).length ∧ pi i = j)
    (hperm : ∀ i, i < (rows coordinates).length →
      rowAt (rows coordinates') i = rowAt (rows coordinates) (pi i)), ∀ r r', Aegis.CountPairs.count_pairs coordinates k = ok r →
      Aegis.CountPairs.count_pairs coordinates' k = ok r' → r' = r) := by
  sorry

/-- Whenever count_pairs(coordinates, k) returns r and count_pairs(swapped, k) returns r', we have r' = r.
  Preconditions: Let n = len(coordinates). Base preconditions: 2 <= n <= 50000; for every i with 0 <= i < n, len(coordinates[i]) = 2, 0 <= coordinates[i][0] <= 1000000, and 0 <= coordinates[i][1] <= 1000000; 0 <= k <= 100. Define the swapped slice by swapped[i][0] = coordinates[i][1] and swapped[i][1] = coordinates[i][0] for every i. -/
theorem spec_10 (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k)
    (coordinates' : Slice (alloc.vec.Vec I64))
    (hswap : rows coordinates' = (rows coordinates).map List.reverse) :
    ∀ r r', Aegis.CountPairs.count_pairs coordinates k = ok r →
      Aegis.CountPairs.count_pairs coordinates' k = ok r' → r' = r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k)
    (coordinates' : Slice (alloc.vec.Vec I64))
    (hswap : rows coordinates' = (rows coordinates).map List.reverse), ∀ r r', Aegis.CountPairs.count_pairs coordinates k = ok r →
      Aegis.CountPairs.count_pairs coordinates' k = ok r' → r' = r) := by
  sorry

/-- Whenever count_pairs(coordinates, k) returns a result r, if there exist indices i,j with 0 <= i < j < n and (coordinates[i][0] XOR coordinates[j][0]) + (coordinates[i][1] XOR coordinates[j][1]) = k, then r >= 1.
  Preconditions: Let n = len(coordinates). Base preconditions: 2 <= n <= 50000; for every i with 0 <= i < n, len(coordinates[i]) = 2, 0 <= coordinates[i][0] <= 1000000, and 0 <= coordinates[i][1] <= 1000000; and 0 <= k <= 100. -/
theorem spec_11 (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k) :
    ∀ r, Aegis.CountPairs.count_pairs coordinates k = ok r →
      (∃ i j, i < j ∧ j < (rows coordinates).length ∧
        distAt (rows coordinates) i j = some k.val) →
      1 ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k), ∀ r, Aegis.CountPairs.count_pairs coordinates k = ok r →
      (∃ i j, i < j ∧ j < (rows coordinates).length ∧
        distAt (rows coordinates) i j = some k.val) →
      1 ≤ r.val) := by
  sorry

/-- Whenever count_pairs(coordinates, k) returns a result r, if for every pair i,j with 0 <= i < j < n we have (coordinates[i][0] XOR coordinates[j][0]) + (coordinates[i][1] XOR coordinates[j][1]) != k, then r = 0.
  Preconditions: Let n = len(coordinates). Base preconditions: 2 <= n <= 50000; for every i with 0 <= i < n, len(coordinates[i]) = 2, 0 <= coordinates[i][0] <= 1000000, and 0 <= coordinates[i][1] <= 1000000; and 0 <= k <= 100. -/
theorem spec_12 (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k)
    (hno : ∀ i j, i < j → j < (rows coordinates).length →
      distAt (rows coordinates) i j ≠ some k.val) :
    ∀ r, Aegis.CountPairs.count_pairs coordinates k = ok r → r.val = 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64)
    (hlen : SliceLengthOK (rows coordinates))
    (hcoord : CoordBounds (rows coordinates))
    (hk : ParamBounds k)
    (hno : ∀ i j, i < j → j < (rows coordinates).length →
      distAt (rows coordinates) i j ≠ some k.val), ∀ r, Aegis.CountPairs.count_pairs coordinates k = ok r → r.val = 0) := by
  sorry

end AegisSpec.CountPairs
