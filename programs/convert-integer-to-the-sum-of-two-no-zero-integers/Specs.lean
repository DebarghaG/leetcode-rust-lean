import Aegis.GetNoZeroIntegers.Code.Funs

/-!
# Specifications of `Aegis.GetNoZeroIntegers.get_no_zero_integers`

LeetCode problem `convert-integer-to-the-sum-of-two-no-zero-integers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetNoZeroIntegers

def digit (x : Int) (k : Nat) : Int := x / 10 ^ k % 10

def NoZeroInt (x : Int) : Prop :=
  0 < x ∧ ∀ k : Nat, 10 ^ k ≤ x → digit x k ≠ 0

def at? (r : alloc.vec.Vec Std.I64) (i : Nat) : Option Int := (r.val[i]?).map (fun x => x.val)

/-- The function returns a result r (it does not fail) such that len(r) = 2, r[0] and r[1] are No-Zero integers, and r[0] + r[1] = n.
  Preconditions: n is an integer with 2 <= n <= 10000 (10^4). A No-Zero integer is a positive integer whose standard base-10 representation (without leading zeros) contains no digit 0; equivalently, x > 0 and for every integer k with 0 <= k and 10^k <= x, floor(x / 10^k) mod 10 != 0. The problem guarantees that at least one pair of No-Zero integers sums to n. -/
theorem spec_1 (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000) :
    ∃ r : alloc.vec.Vec Std.I64, ∃ a b : Int,
      Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r ∧
        r.val.length = 2 ∧
        at? r 0 = some a ∧ at? r 1 = some b ∧
        NoZeroInt a ∧ NoZeroInt b ∧ a + b = n.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000), ∃ r : alloc.vec.Vec Std.I64, ∃ a b : Int,
      Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r ∧
        r.val.length = 2 ∧
        at? r 0 = some a ∧ at? r 1 = some b ∧
        NoZeroInt a ∧ NoZeroInt b ∧ a + b = n.val) := by
  sorry

/-- Whenever the function returns a result r, len(r) = 2.
  Preconditions: n is an integer with 2 <= n <= 10000. -/
theorem spec_2 (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r) :
    r.val.length = 2 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r), r.val.length = 2) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r[0] <= n - 1 and 1 <= r[1] <= n - 1.
  Preconditions: n is an integer with 2 <= n <= 10000. -/
theorem spec_3 (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r) :
    ∃ a b : Int,
      at? r 0 = some a ∧ at? r 1 = some b ∧
        1 ≤ a ∧ a ≤ n.val - 1 ∧ 1 ≤ b ∧ b ≤ n.val - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r), ∃ a b : Int,
      at? r 0 = some a ∧ at? r 1 = some b ∧
        1 ≤ a ∧ a ≤ n.val - 1 ∧ 1 ≤ b ∧ b ≤ n.val - 1) := by
  sorry

/-- The function returns a result r for every such n; in particular, evaluation does not fail with arithmetic overflow, out-of-bounds access, or panic.
  Preconditions: n is an integer with 2 <= n <= 10000; the problem guarantees a valid No-Zero decomposition exists. -/
theorem spec_4 (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, r[0] is a No-Zero integer, i.e. r[0] > 0 and every decimal digit in the standard base-10 representation of r[0] is nonzero.
  Preconditions: n is an integer with 2 <= n <= 10000. -/
theorem spec_5 (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r) :
    ∃ a : Int, at? r 0 = some a ∧ NoZeroInt a := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r), ∃ a : Int, at? r 0 = some a ∧ NoZeroInt a) := by
  sorry

/-- Whenever the function returns a result r, r[1] is a No-Zero integer, i.e. r[1] > 0 and every decimal digit in the standard base-10 representation of r[1] is nonzero.
  Preconditions: n is an integer with 2 <= n <= 10000. -/
theorem spec_6 (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r) :
    ∃ b : Int, at? r 1 = some b ∧ NoZeroInt b := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r), ∃ b : Int, at? r 1 = some b ∧ NoZeroInt b) := by
  sorry

/-- Whenever the function returns a result r, r[0] + r[1] = n.
  Preconditions: n is an integer with 2 <= n <= 10000. -/
theorem spec_7 (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r) :
    ∃ a b : Int, at? r 0 = some a ∧ at? r 1 = some b ∧ a + b = n.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r), ∃ a b : Int, at? r 0 = some a ∧ at? r 1 = some b ∧ a + b = n.val) := by
  sorry

/-- Whenever the function returns a result r, r[0] > 0 and r[1] > 0.
  Preconditions: n is an integer with 2 <= n <= 10000. -/
theorem spec_8 (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r) :
    ∃ a b : Int, at? r 0 = some a ∧ at? r 1 = some b ∧ 0 < a ∧ 0 < b := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r), ∃ a b : Int, at? r 0 = some a ∧ at? r 1 = some b ∧ 0 < a ∧ 0 < b) := by
  sorry

/-- Whenever the function returns a result r, for every integer k with 0 <= k and 10^k <= r[0], the k-th decimal digit of r[0], namely floor(r[0] / 10^k) mod 10, is nonzero.
  Preconditions: n is an integer with 2 <= n <= 10000. -/
theorem spec_9 (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r) :
    ∃ a : Int, at? r 0 = some a ∧ ∀ k : Nat, 10 ^ k ≤ a → digit a k ≠ 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r), ∃ a : Int, at? r 0 = some a ∧ ∀ k : Nat, 10 ^ k ≤ a → digit a k ≠ 0) := by
  sorry

/-- Whenever the function returns a result r, for every integer k with 0 <= k and 10^k <= r[1], the k-th decimal digit of r[1], namely floor(r[1] / 10^k) mod 10, is nonzero.
  Preconditions: n is an integer with 2 <= n <= 10000. -/
theorem spec_10 (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r) :
    ∃ b : Int, at? r 1 = some b ∧ ∀ k : Nat, 10 ^ k ≤ b → digit b k ≠ 0 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r), ∃ b : Int, at? r 1 = some b ∧ ∀ k : Nat, 10 ^ k ≤ b → digit b k ≠ 0) := by
  sorry

/-- The function returns a result r with r[0] = 1 and r[1] = 1.
  Preconditions: n = 2. -/
theorem spec_11 (n : Std.I64) (hn : n.val = 2) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r ∧
        at? r 0 = some 1 ∧ at? r 1 = some 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 2), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r ∧
        at? r 0 = some 1 ∧ at? r 1 = some 1) := by
  sorry

/-- Whenever the function returns a result r, 2 <= r[0] <= 9 and 2 <= r[1] <= 9.
  Preconditions: n = 11. -/
theorem spec_12 (n : Std.I64) (hn : n.val = 11)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r) :
    ∃ a b : Int,
      at? r 0 = some a ∧ at? r 1 = some b ∧ 2 ≤ a ∧ a ≤ 9 ∧ 2 ≤ b ∧ b ≤ 9 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 11)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.GetNoZeroIntegers.get_no_zero_integers n = Result.ok r), ∃ a b : Int,
      at? r 0 = some a ∧ at? r 1 = some b ∧ 2 ≤ a ∧ a ≤ 9 ∧ 2 ≤ b ∧ b ≤ 9) := by
  sorry

end AegisSpec.GetNoZeroIntegers
