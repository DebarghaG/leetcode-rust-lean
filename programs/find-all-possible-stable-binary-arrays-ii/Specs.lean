import Aegis.NumberOfStableArrays.Code.Funs

/-!
# Specifications of `Aegis.NumberOfStableArrays.number_of_stable_arrays`

LeetCode problem `find-all-possible-stable-binary-arrays-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberOfStableArrays

open Aegis.NumberOfStableArrays (number_of_stable_arrays)

def WindowConstant (arr : List Bool) (i j : Nat) : Prop :=
  ∀ k k', i ≤ k → k < j → i ≤ k' → k' < j → arr[k]? = arr[k']?

def AllBlocksShort (arr : List Bool) (limit : Nat) : Prop :=
  ∀ i j, i ≤ j → j ≤ arr.length → limit < j - i → ¬ WindowConstant arr i j

noncomputable def C (z o l : Nat) : Nat := by
  classical
  exact ((Finset.univ : Finset (Fin (z + o) → Bool)).filter (fun f =>
    (List.ofFn f).count false = z ∧ (List.ofFn f).count true = o ∧
      AllBlocksShort (List.ofFn f) l)).card

/-- For every input satisfying the preconditions, whenever number_of_stable_arrays returns a result r, the integer value of r equals C(zero, one, limit) mod 1000000007, where C(zero, one, limit) is the number of binary arrays arr (sequences over {0,1}) such that arr has length zero+one, contains exactly zero occurrences of 0 and exactly one occurrences of 1, and every maximal contiguous block of equal entries of arr has length at most limit (equivalently, every contiguous subarray of arr of length greater than limit contains both a 0 and a 1); x mod 1000000007 denotes the unique integer in {0,...,1000000006} congruent to x modulo 1000000007.
  Preconditions: The integer values of the Std.I64 arguments zero, one, and limit satisfy 1 <= zero <= 1000, 1 <= one <= 1000, and 1 <= limit <= 1000. -/
theorem spec_1 (zero one limit : Std.I64)
    (hzero_lb : 1 ≤ zero.val) (hzero_ub : zero.val ≤ 1000)
    (hone_lb : 1 ≤ one.val) (hone_ub : one.val ≤ 1000)
    (hlimit_lb : 1 ≤ limit.val) (hlimit_ub : limit.val ≤ 1000) :
    ∀ r, number_of_stable_arrays zero one limit = ok r →
      r.val =
        ((C zero.val.toNat one.val.toNat limit.val.toNat % 1000000007 : Nat) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (zero one limit : Std.I64)
    (hzero_lb : 1 ≤ zero.val) (hzero_ub : zero.val ≤ 1000)
    (hone_lb : 1 ≤ one.val) (hone_ub : one.val ≤ 1000)
    (hlimit_lb : 1 ≤ limit.val) (hlimit_ub : limit.val ≤ 1000), ∀ r, number_of_stable_arrays zero one limit = ok r →
      r.val =
        ((C zero.val.toNat one.val.toNat limit.val.toNat % 1000000007 : Nat) : Int)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: The integer values of the Std.I64 arguments zero, one, and limit satisfy 1 <= zero <= 1000, 1 <= one <= 1000, and 1 <= limit <= 1000. -/
theorem spec_2 (zero one limit : Std.I64)
    (hzero_lb : 1 ≤ zero.val) (hzero_ub : zero.val ≤ 1000)
    (hone_lb : 1 ≤ one.val) (hone_ub : one.val ≤ 1000)
    (hlimit_lb : 1 ≤ limit.val) (hlimit_ub : limit.val ≤ 1000) :
    ∃ r, number_of_stable_arrays zero one limit = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (zero one limit : Std.I64)
    (hzero_lb : 1 ≤ zero.val) (hzero_ub : zero.val ≤ 1000)
    (hone_lb : 1 ≤ one.val) (hone_ub : one.val ≤ 1000)
    (hlimit_lb : 1 ≤ limit.val) (hlimit_ub : limit.val ≤ 1000), ∃ r, number_of_stable_arrays zero one limit = ok r) := by
  sorry

/-- For every input satisfying the preconditions, whenever the function returns a result r, the integer value of r satisfies 0 <= r <= 1000000006.
  Preconditions: The integer values of the Std.I64 arguments zero, one, and limit satisfy 1 <= zero <= 1000, 1 <= one <= 1000, and 1 <= limit <= 1000. -/
theorem spec_3 (zero one limit : Std.I64)
    (hzero_lb : 1 ≤ zero.val) (hzero_ub : zero.val ≤ 1000)
    (hone_lb : 1 ≤ one.val) (hone_ub : one.val ≤ 1000)
    (hlimit_lb : 1 ≤ limit.val) (hlimit_ub : limit.val ≤ 1000) :
    ∀ r, number_of_stable_arrays zero one limit = ok r →
      0 ≤ r.val ∧ r.val ≤ 1000000006 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (zero one limit : Std.I64)
    (hzero_lb : 1 ≤ zero.val) (hzero_ub : zero.val ≤ 1000)
    (hone_lb : 1 ≤ one.val) (hone_ub : one.val ≤ 1000)
    (hlimit_lb : 1 ≤ limit.val) (hlimit_ub : limit.val ≤ 1000), ∀ r, number_of_stable_arrays zero one limit = ok r →
      0 ≤ r.val ∧ r.val ≤ 1000000006) := by
  sorry

/-- For every input satisfying the preconditions, whenever the function returns a result r, the integer value of r is congruent modulo 1000000007 to the number of binary arrays that contain exactly one occurrences of 0 and exactly zero occurrences of 1 and whose every maximal contiguous block of equal entries has length at most limit.
  Preconditions: The integer values of the Std.I64 arguments zero, one, and limit satisfy 1 <= zero <= 1000, 1 <= one <= 1000, and 1 <= limit <= 1000. -/
theorem spec_4 (zero one limit : Std.I64)
    (hzero_lb : 1 ≤ zero.val) (hzero_ub : zero.val ≤ 1000)
    (hone_lb : 1 ≤ one.val) (hone_ub : one.val ≤ 1000)
    (hlimit_lb : 1 ≤ limit.val) (hlimit_ub : limit.val ≤ 1000) :
    ∀ r, number_of_stable_arrays zero one limit = ok r →
      Int.ModEq 1000000007 r.val
        ((C one.val.toNat zero.val.toNat limit.val.toNat : Nat) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (zero one limit : Std.I64)
    (hzero_lb : 1 ≤ zero.val) (hzero_ub : zero.val ≤ 1000)
    (hone_lb : 1 ≤ one.val) (hone_ub : one.val ≤ 1000)
    (hlimit_lb : 1 ≤ limit.val) (hlimit_ub : limit.val ≤ 1000), ∀ r, number_of_stable_arrays zero one limit = ok r →
      Int.ModEq 1000000007 r.val
        ((C one.val.toNat zero.val.toNat limit.val.toNat : Nat) : Int)) := by
  sorry

/-- For every input satisfying the preconditions, whenever the function returns a result r, the integer value of r equals binomial(zero+one, zero) mod 1000000007, where binomial(n,k) is n!/(k!(n-k)!) and the result is the unique integer in {0,...,1000000006} congruent to that binomial coefficient.
  Preconditions: The integer values of zero, one, and limit satisfy 1 <= zero <= 1000, 1 <= one <= 1000, 1 <= limit <= 1000, and limit >= zero and limit >= one. -/
theorem spec_5 (zero one limit : Std.I64)
    (hzero_lb : 1 ≤ zero.val) (hzero_ub : zero.val ≤ 1000)
    (hone_lb : 1 ≤ one.val) (hone_ub : one.val ≤ 1000)
    (hlimit_lb : 1 ≤ limit.val) (hlimit_ub : limit.val ≤ 1000)
    (hlimit_zero : zero.val ≤ limit.val) (hlimit_one : one.val ≤ limit.val) :
    ∀ r, number_of_stable_arrays zero one limit = ok r →
      r.val =
        ((Nat.choose (zero.val.toNat + one.val.toNat) zero.val.toNat % 1000000007 : Nat) :
          Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (zero one limit : Std.I64)
    (hzero_lb : 1 ≤ zero.val) (hzero_ub : zero.val ≤ 1000)
    (hone_lb : 1 ≤ one.val) (hone_ub : one.val ≤ 1000)
    (hlimit_lb : 1 ≤ limit.val) (hlimit_ub : limit.val ≤ 1000)
    (hlimit_zero : zero.val ≤ limit.val) (hlimit_one : one.val ≤ limit.val), ∀ r, number_of_stable_arrays zero one limit = ok r →
      r.val =
        ((Nat.choose (zero.val.toNat + one.val.toNat) zero.val.toNat % 1000000007 : Nat) :
          Int)) := by
  sorry

/-- For every input satisfying the preconditions, whenever the function returns a result r, the integer value of r is 2 if zero = one, is 1 if |zero - one| = 1, and is 0 if |zero - one| >= 2.
  Preconditions: The integer values of zero, one, and limit satisfy 1 <= zero <= 1000, 1 <= one <= 1000, and limit = 1. -/
theorem spec_6 (zero one limit : Std.I64)
    (hzero_lb : 1 ≤ zero.val) (hzero_ub : zero.val ≤ 1000)
    (hone_lb : 1 ≤ one.val) (hone_ub : one.val ≤ 1000)
    (hlimit : limit.val = 1) :
    ∀ r, number_of_stable_arrays zero one limit = ok r →
      (zero.val = one.val → r.val = 2) ∧
      (Int.natAbs (zero.val - one.val) = 1 → r.val = 1) ∧
      (2 ≤ Int.natAbs (zero.val - one.val) → r.val = 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (zero one limit : Std.I64)
    (hzero_lb : 1 ≤ zero.val) (hzero_ub : zero.val ≤ 1000)
    (hone_lb : 1 ≤ one.val) (hone_ub : one.val ≤ 1000)
    (hlimit : limit.val = 1), ∀ r, number_of_stable_arrays zero one limit = ok r →
      (zero.val = one.val → r.val = 2) ∧
      (Int.natAbs (zero.val - one.val) = 1 → r.val = 1) ∧
      (2 ≤ Int.natAbs (zero.val - one.val) → r.val = 0)) := by
  sorry

/-- For every input satisfying the preconditions, whenever the function returns a result r, the integer value of r equals max(0, min(zero, limit) - max(0, zero - limit) + 1).
  Preconditions: The integer values of zero, one, and limit satisfy 1 <= zero <= 1000, one = 1, and 1 <= limit <= 1000. -/
theorem spec_7 (zero one limit : Std.I64)
    (hzero_lb : 1 ≤ zero.val) (hzero_ub : zero.val ≤ 1000)
    (hone : one.val = 1)
    (hlimit_lb : 1 ≤ limit.val) (hlimit_ub : limit.val ≤ 1000) :
    ∀ r, number_of_stable_arrays zero one limit = ok r →
      r.val = max 0 (min zero.val limit.val - max 0 (zero.val - limit.val) + 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (zero one limit : Std.I64)
    (hzero_lb : 1 ≤ zero.val) (hzero_ub : zero.val ≤ 1000)
    (hone : one.val = 1)
    (hlimit_lb : 1 ≤ limit.val) (hlimit_ub : limit.val ≤ 1000), ∀ r, number_of_stable_arrays zero one limit = ok r →
      r.val = max 0 (min zero.val limit.val - max 0 (zero.val - limit.val) + 1)) := by
  sorry

/-- For every input satisfying the preconditions, whenever the function returns a result r, the integer value of r equals max(0, min(one, limit) - max(0, one - limit) + 1).
  Preconditions: The integer values of zero, one, and limit satisfy zero = 1, 1 <= one <= 1000, and 1 <= limit <= 1000. -/
theorem spec_8 (zero one limit : Std.I64)
    (hzero : zero.val = 1)
    (hone_lb : 1 ≤ one.val) (hone_ub : one.val ≤ 1000)
    (hlimit_lb : 1 ≤ limit.val) (hlimit_ub : limit.val ≤ 1000) :
    ∀ r, number_of_stable_arrays zero one limit = ok r →
      r.val = max 0 (min one.val limit.val - max 0 (one.val - limit.val) + 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (zero one limit : Std.I64)
    (hzero : zero.val = 1)
    (hone_lb : 1 ≤ one.val) (hone_ub : one.val ≤ 1000)
    (hlimit_lb : 1 ≤ limit.val) (hlimit_ub : limit.val ≤ 1000), ∀ r, number_of_stable_arrays zero one limit = ok r →
      r.val = max 0 (min one.val limit.val - max 0 (one.val - limit.val) + 1)) := by
  sorry

/-- For every input satisfying the preconditions, whenever the function returns a result r, the integer value of r is 0.
  Preconditions: The integer values of zero, one, and limit satisfy 1 <= zero <= 1000, 1 <= one <= 1000, 1 <= limit <= 1000, and either zero > limit*(one+1) or one > limit*(zero+1). -/
theorem spec_9 (zero one limit : Std.I64)
    (hzero_lb : 1 ≤ zero.val) (hzero_ub : zero.val ≤ 1000)
    (hone_lb : 1 ≤ one.val) (hone_ub : one.val ≤ 1000)
    (hlimit_lb : 1 ≤ limit.val) (hlimit_ub : limit.val ≤ 1000)
    (hbig : limit.val * (one.val + 1) < zero.val ∨
      limit.val * (zero.val + 1) < one.val) :
    ∀ r, number_of_stable_arrays zero one limit = ok r → r.val = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (zero one limit : Std.I64)
    (hzero_lb : 1 ≤ zero.val) (hzero_ub : zero.val ≤ 1000)
    (hone_lb : 1 ≤ one.val) (hone_ub : one.val ≤ 1000)
    (hlimit_lb : 1 ≤ limit.val) (hlimit_ub : limit.val ≤ 1000)
    (hbig : limit.val * (one.val + 1) < zero.val ∨
      limit.val * (zero.val + 1) < one.val), ∀ r, number_of_stable_arrays zero one limit = ok r → r.val = 0) := by
  sorry

/-- If the call number_of_stable_arrays(zero, one, L1) returns r1 and the call number_of_stable_arrays(zero, one, L2) returns r2, then the integer values of r1 and r2 are equal.
  Preconditions: The integer values zero and one satisfy 1 <= zero <= 1000 and 1 <= one <= 1000, and L1 and L2 are integers with max(zero, one) <= L1 <= 1000 and max(zero, one) <= L2 <= 1000. -/
theorem spec_10 (zero one L1 L2 : Std.I64)
    (hzero_lb : 1 ≤ zero.val) (hzero_ub : zero.val ≤ 1000)
    (hone_lb : 1 ≤ one.val) (hone_ub : one.val ≤ 1000)
    (hL1_lb : max zero.val one.val ≤ L1.val) (hL1_ub : L1.val ≤ 1000)
    (hL2_lb : max zero.val one.val ≤ L2.val) (hL2_ub : L2.val ≤ 1000) :
    ∀ r1 r2, number_of_stable_arrays zero one L1 = ok r1 →
      number_of_stable_arrays zero one L2 = ok r2 → r1.val = r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (zero one L1 L2 : Std.I64)
    (hzero_lb : 1 ≤ zero.val) (hzero_ub : zero.val ≤ 1000)
    (hone_lb : 1 ≤ one.val) (hone_ub : one.val ≤ 1000)
    (hL1_lb : max zero.val one.val ≤ L1.val) (hL1_ub : L1.val ≤ 1000)
    (hL2_lb : max zero.val one.val ≤ L2.val) (hL2_ub : L2.val ≤ 1000), ∀ r1 r2, number_of_stable_arrays zero one L1 = ok r1 →
      number_of_stable_arrays zero one L2 = ok r2 → r1.val = r2.val) := by
  sorry

end AegisSpec.NumberOfStableArrays
