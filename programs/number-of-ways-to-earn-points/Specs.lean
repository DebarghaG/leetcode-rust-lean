import Aegis.WaysToReachTarget.Code.Funs

/-!
# Specifications of `Aegis.WaysToReachTarget.ways_to_reach_target`

LeetCode problem `number-of-ways-to-earn-points`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.WaysToReachTarget

  namespace AegisSpec.WaysToReachTarget

  def vecEntry (v : alloc.vec.Vec Std.I64) (i : Nat) : Int :=
    (v.val.getD i 0#i64).val

  def entries (types : Slice (alloc.vec.Vec Std.I64)) : List (Int × Int) :=
    types.val.map (fun v => (vecEntry v 0, vecEntry v 1))

  def countAt (types : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    ((entries types).getD i (0, 0)).1

  def marksAt (types : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
    ((entries types).getD i (0, 0)).2

  def ValidInput (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    1 ≤ target.val ∧ target.val ≤ 1000 ∧
    1 ≤ (entries types).length ∧ (entries types).length ≤ 50 ∧
    (∀ v ∈ types.val, v.val.length = 2) ∧
    (∀ p ∈ entries types, 1 ≤ p.1 ∧ p.1 ≤ 50 ∧ 1 ≤ p.2 ∧ p.2 ≤ 50)

  def totalCapacity (es : List (Int × Int)) : Int :=
    (es.map (fun p => p.1 * p.2)).sum

  def gcdMarks (es : List (Int × Int)) : Nat :=
    es.foldr (fun p acc => Nat.gcd p.2.natAbs acc) 0

  def waysNumber : List (Int × Int) → Int → Nat
    | [], t => if t = 0 then 1 else 0
    | (c, m) :: rest, t =>
        (Finset.range (c.toNat + 1)).sum (fun k => waysNumber rest (t - (k : Int) * m))

  def IsSolution (es : List (Int × Int)) (ks : List Int) (t : Int) : Prop :=
    List.Forall₂ (fun k p => 0 ≤ k ∧ k ≤ p.1) ks es ∧
    (List.zipWith (fun k p => k * p.2) ks es).sum = t

  def dividesWithin (target mark count : Int) : Prop :=
    ∃ k : Int, 0 ≤ k ∧ k ≤ count ∧ target = k * mark

  def ModEq (a b M : Int) : Prop :=
    ∃ q : Int, a = b + q * M

  /-- The function returns a result r (it does not fail), and r, interpreted as an integer, is the unique integer in [0, 1000000007) congruent modulo 1000000007 to the number of choices of integers k_i, one for each 0 <= i < len(types), such that 0 <= k_i <= types[i][0] for every i and sum_{i=0}^{len(types)-1} k_i * types[i][1] = target. Equivalently, if W is that number of choices and M = 1000000007, then 0 <= r < M and r is congruent to W modulo M.
    Preconditions: target is an i64 and types is a slice of i64 vectors. The input satisfies the problem constraints: 1 <= target <= 1000; 1 <= len(types) <= 50; for every i with 0 <= i < len(types), len(types[i]) = 2, 1 <= types[i][0] <= 50, and 1 <= types[i][1] <= 50. Types[i][0] is count_i and types[i][1] is marks_i; all values are interpreted as mathematical integers within these ranges. -/
  theorem spec_1 (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput target types) :
      ∃ r : Std.I64,
        ways_to_reach_target target types = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007 ∧
        ModEq (waysNumber (entries types) target.val) r.val 1000000007 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput target types), ∃ r : Std.I64,
          ways_to_reach_target target types = ok r ∧
          0 ≤ r.val ∧ r.val < 1000000007 ∧
          ModEq (waysNumber (entries types) target.val) r.val 1000000007) := by
    sorry

  /-- For every input satisfying the preconditions, ways_to_reach_target returns a result (an ok value): there is no failure from arithmetic overflow, out-of-bounds indexing, or panic.
    Preconditions: target is an i64 and types is a slice of i64 vectors. The input satisfies: 1 <= target <= 1000; 1 <= len(types) <= 50; for every i with 0 <= i < len(types), len(types[i]) = 2, 1 <= types[i][0] <= 50, and 1 <= types[i][1] <= 50. -/
  theorem spec_2 (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput target types) :
      ∃ r : Std.I64, ways_to_reach_target target types = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput target types), ∃ r : Std.I64, ways_to_reach_target target types = ok r) := by
    sorry

  /-- Whenever ways_to_reach_target returns a result r, the integer value of r satisfies 0 <= r < 1000000007.
    Preconditions: target is an i64 and types is a slice of i64 vectors. The input satisfies: 1 <= target <= 1000; 1 <= len(types) <= 50; for every i with 0 <= i < len(types), len(types[i]) = 2, 1 <= types[i][0] <= 50, and 1 <= types[i][1] <= 50. -/
  theorem spec_3 (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput target types) :
      ∀ r : Std.I64,
        ways_to_reach_target target types = ok r → 0 ≤ r.val ∧ r.val < 1000000007 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput target types), ∀ r : Std.I64,
          ways_to_reach_target target types = ok r → 0 ≤ r.val ∧ r.val < 1000000007) := by
    sorry

  /-- If target > sum_{i=0}^{len(types)-1} types[i][0] * types[i][1], then the function returns 0.
    Preconditions: target is an i64 and types is a slice of i64 vectors. The input satisfies: 1 <= target <= 1000; 1 <= len(types) <= 50; for every i with 0 <= i < len(types), len(types[i]) = 2, 1 <= types[i][0] <= 50, and 1 <= types[i][1] <= 50. -/
  theorem spec_4 (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput target types)
      (hgt : totalCapacity (entries types) < target.val) :
      ways_to_reach_target target types = ok 0#i64 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput target types)
        (hgt : totalCapacity (entries types) < target.val), ways_to_reach_target target types = ok 0#i64) := by
    sorry

  /-- Let g = gcd(types[0][1], types[1][1], ..., types[len(types)-1][1]). If g does not divide target, then the function returns 0.
    Preconditions: target is an i64 and types is a slice of i64 vectors. The input satisfies: 1 <= target <= 1000; 1 <= len(types) <= 50; for every i with 0 <= i < len(types), len(types[i]) = 2, 1 <= types[i][0] <= 50, and 1 <= types[i][1] <= 50. -/
  theorem spec_5 (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput target types)
      (hg : ¬ ∃ k : Int, target.val = (gcdMarks (entries types) : Int) * k) :
      ways_to_reach_target target types = ok 0#i64 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput target types)
        (hg : ¬ ∃ k : Int, target.val = (gcdMarks (entries types) : Int) * k), ways_to_reach_target target types = ok 0#i64) := by
    sorry

  /-- If types[i][1] > target for every i with 0 <= i < len(types), then the function returns 0.
    Preconditions: target is an i64 and types is a slice of i64 vectors. The input satisfies: 1 <= target <= 1000; 1 <= len(types) <= 50; for every i with 0 <= i < len(types), len(types[i]) = 2, 1 <= types[i][0] <= 50, and 1 <= types[i][1] <= 50. -/
  theorem spec_6 (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput target types)
      (hmarks : ∀ p ∈ entries types, target.val < p.2) :
      ways_to_reach_target target types = ok 0#i64 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput target types)
        (hmarks : ∀ p ∈ entries types, target.val < p.2), ways_to_reach_target target types = ok 0#i64) := by
    sorry

  /-- If target = sum_{i=0}^{len(types)-1} types[i][0] * types[i][1], then the function returns 1.
    Preconditions: target is an i64 and types is a slice of i64 vectors. The input satisfies: 1 <= target <= 1000; 1 <= len(types) <= 50; for every i with 0 <= i < len(types), len(types[i]) = 2, 1 <= types[i][0] <= 50, and 1 <= types[i][1] <= 50. -/
  theorem spec_7 (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput target types)
      (heq : target.val = totalCapacity (entries types)) :
      ways_to_reach_target target types = ok 1#i64 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput target types)
        (heq : target.val = totalCapacity (entries types)), ways_to_reach_target target types = ok 1#i64) := by
    sorry

  /-- If len(types) = 1, let count0 = types[0][0] and mark0 = types[0][1]. Then the function returns 1 if mark0 divides target and target / mark0 <= count0, and returns 0 otherwise.
    Preconditions: target is an i64 and types is a slice of i64 vectors. The input satisfies: 1 <= target <= 1000; 1 <= len(types) <= 50; for every i with 0 <= i < len(types), len(types[i]) = 2, 1 <= types[i][0] <= 50, and 1 <= types[i][1] <= 50. -/
  theorem spec_8 (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput target types) (hlen : (entries types).length = 1) :
      (dividesWithin target.val (marksAt types 0) (countAt types 0) →
          ways_to_reach_target target types = ok 1#i64) ∧
      (¬ dividesWithin target.val (marksAt types 0) (countAt types 0) →
          ways_to_reach_target target types = ok 0#i64) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput target types) (hlen : (entries types).length = 1), (dividesWithin target.val (marksAt types 0) (countAt types 0) →
            ways_to_reach_target target types = ok 1#i64) ∧
        (¬ dividesWithin target.val (marksAt types 0) (countAt types 0) →
            ways_to_reach_target target types = ok 0#i64)) := by
    sorry

  /-- If target = 1, then the function returns the number of indices i with 0 <= i < len(types) and types[i][1] = 1.
    Preconditions: target is an i64 and types is a slice of i64 vectors. The input satisfies: 1 <= target <= 1000; 1 <= len(types) <= 50; for every i with 0 <= i < len(types), len(types[i]) = 2, 1 <= types[i][0] <= 50, and 1 <= types[i][1] <= 50. -/
  theorem spec_9 (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput target types) (ht : target.val = 1) :
      ∃ r : Std.I64,
        ways_to_reach_target target types = ok r ∧
        r.val = (((entries types).filter (fun p => p.2 = 1)).length : Nat) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput target types) (ht : target.val = 1), ∃ r : Std.I64,
          ways_to_reach_target target types = ok r ∧
          r.val = (((entries types).filter (fun p => p.2 = 1)).length : Nat)) := by
    sorry

  /-- Suppose len(types) >= 2 and for some index j with 0 <= j < len(types), types[j][1] > target. Let types' be the slice obtained by deleting the j-th entry of types. Then ways_to_reach_target target types and ways_to_reach_target target types' return the same result.
    Preconditions: target is an i64 and types is a slice of i64 vectors. The input satisfies: 1 <= target <= 1000; 1 <= len(types) <= 50; for every i with 0 <= i < len(types), len(types[i]) = 2, 1 <= types[i][0] <= 50, and 1 <= types[i][1] <= 50. -/
  theorem spec_10 (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput target types)
      (hlen : 2 ≤ (entries types).length)
      (j : Nat) (hj : j < (entries types).length) (hjmarks : target.val < marksAt types j)
      (types' : Slice (alloc.vec.Vec Std.I64))
      (htypes' : entries types' = (entries types).eraseIdx j) :
      ∃ r : Std.I64,
        ways_to_reach_target target types = ok r ∧
        ways_to_reach_target target types' = ok r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput target types)
        (hlen : 2 ≤ (entries types).length)
        (j : Nat) (hj : j < (entries types).length) (hjmarks : target.val < marksAt types j)
        (types' : Slice (alloc.vec.Vec Std.I64))
        (htypes' : entries types' = (entries types).eraseIdx j), ∃ r : Std.I64,
          ways_to_reach_target target types = ok r ∧
          ways_to_reach_target target types' = ok r) := by
    sorry

  /-- Assume types[i][1] <= target for every i with 0 <= i < len(types). For each i let c_i = floor(target / types[i][1]), and let types' be obtained from types by replacing types[i][0] with min(types[i][0], c_i), leaving all marks unchanged. Then ways_to_reach_target target types and ways_to_reach_target target types' return the same result.
    Preconditions: target is an i64 and types is a slice of i64 vectors. The input satisfies: 1 <= target <= 1000; 1 <= len(types) <= 50; for every i with 0 <= i < len(types), len(types[i]) = 2, 1 <= types[i][0] <= 50, and 1 <= types[i][1] <= 50. -/
  theorem spec_11 (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput target types)
      (hmarks : ∀ p ∈ entries types, p.2 ≤ target.val)
      (types' : Slice (alloc.vec.Vec Std.I64))
      (htypes' : entries types' =
        (entries types).map (fun p => (min p.1 (target.val / p.2), p.2))) :
      ∃ r : Std.I64,
        ways_to_reach_target target types = ok r ∧
        ways_to_reach_target target types' = ok r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput target types)
        (hmarks : ∀ p ∈ entries types, p.2 ≤ target.val)
        (types' : Slice (alloc.vec.Vec Std.I64))
        (htypes' : entries types' =
          (entries types).map (fun p => (min p.1 (target.val / p.2), p.2))), ∃ r : Std.I64,
          ways_to_reach_target target types = ok r ∧
          ways_to_reach_target target types' = ok r) := by
    sorry

  /-- For every slice types' that is a permutation of the entries of types (same length and same multiset of [count, marks] vectors), the function returns the same result on (target, types) and on (target, types').
    Preconditions: target is an i64 and types is a slice of i64 vectors. The input satisfies: 1 <= target <= 1000; 1 <= len(types) <= 50; for every i with 0 <= i < len(types), len(types[i]) = 2, 1 <= types[i][0] <= 50, and 1 <= types[i][1] <= 50. -/
  theorem spec_12 (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput target types)
      (types' : Slice (alloc.vec.Vec Std.I64))
      (htypes' : (entries types').Perm (entries types)) :
      ∃ r : Std.I64,
        ways_to_reach_target target types = ok r ∧
        ways_to_reach_target target types' = ok r := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput target types)
        (types' : Slice (alloc.vec.Vec Std.I64))
        (htypes' : (entries types').Perm (entries types)), ∃ r : Std.I64,
          ways_to_reach_target target types = ok r ∧
          ways_to_reach_target target types' = ok r) := by
    sorry

  /-- Whenever the function returns a nonzero result r, there exists at least one choice of integers k_i, one for each 0 <= i < len(types), such that 0 <= k_i <= types[i][0] for every i and sum_{i=0}^{len(types)-1} k_i * types[i][1] = target.
    Preconditions: target is an i64 and types is a slice of i64 vectors. The input satisfies: 1 <= target <= 1000; 1 <= len(types) <= 50; for every i with 0 <= i < len(types), len(types[i]) = 2, 1 <= types[i][0] <= 50, and 1 <= types[i][1] <= 50. -/
  theorem spec_13 (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput target types) :
      ∀ r : Std.I64,
        ways_to_reach_target target types = ok r → r.val ≠ 0 →
          ∃ ks : List Int, IsSolution (entries types) ks target.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput target types), ∀ r : Std.I64,
          ways_to_reach_target target types = ok r → r.val ≠ 0 →
            ∃ ks : List Int, IsSolution (entries types) ks target.val) := by
    sorry

  /-- Let W be the number of choices of integers k_i, one for each 0 <= i < len(types), such that 0 <= k_i <= types[i][0] for every i and sum_{i=0}^{len(types)-1} k_i * types[i][1] = target. If W < 1000000007, then the returned result r equals W as an integer.
    Preconditions: target is an i64 and types is a slice of i64 vectors. The input satisfies: 1 <= target <= 1000; 1 <= len(types) <= 50; for every i with 0 <= i < len(types), len(types[i]) = 2, 1 <= types[i][0] <= 50, and 1 <= types[i][1] <= 50. -/
  theorem spec_14 (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
      (h : ValidInput target types)
      (hW : waysNumber (entries types) target.val < 1000000007) :
      ∀ r : Std.I64,
        ways_to_reach_target target types = ok r →
          r.val = ((waysNumber (entries types) target.val : Nat) : Int) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (target : Std.I64) (types : Slice (alloc.vec.Vec Std.I64))
        (h : ValidInput target types)
        (hW : waysNumber (entries types) target.val < 1000000007), ∀ r : Std.I64,
          ways_to_reach_target target types = ok r →
            r.val = ((waysNumber (entries types) target.val : Nat) : Int)) := by
    sorry

  end AegisSpec.WaysToReachTarget
