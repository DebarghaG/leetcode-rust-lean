import Aegis.FindComplement.Code.Funs

/-!
# Specifications of `Aegis.FindComplement.find_complement`

LeetCode problem `number-complement`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.FindComplement

namespace AegisSpec.FindComplement

def popcount (x : ℤ) : Nat :=
  ((List.range (x.natAbs + 1)).filter (fun i => x.natAbs.testBit i)).length

/-- Let k be the unique positive integer such that 2^(k-1) <= num < 2^k. The function returns a result r and r = 2^k - 1 - num.
  Preconditions: 1 <= num < 2^31. -/
theorem spec_1 (num : Std.I64) (k : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_lo : 2 ^ (k - 1) ≤ num.val) (hk_hi : num.val < 2 ^ k) :
    ∃ r : Std.I64,
      find_complement num = Result.ok r ∧ r.val = 2 ^ k - 1 - num.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (num : Std.I64) (k : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_lo : 2 ^ (k - 1) ≤ num.val) (hk_hi : num.val < 2 ^ k), ∃ r : Std.I64,
      find_complement num = Result.ok r ∧ r.val = 2 ^ k - 1 - num.val) := by
  sorry

/-- The function does not fail: for every num with 1 <= num < 2^31, find_complement num returns a result, i.e. there exists an integer r such that the result is Result.ok r.
  Preconditions: 1 <= num < 2^31. -/
theorem spec_2 (num : Std.I64)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31) :
    ∃ r : Std.I64, find_complement num = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (num : Std.I64)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31), ∃ r : Std.I64, find_complement num = Result.ok r) := by
  sorry

/-- Let k be the unique positive integer such that 2^(k-1) <= num < 2^k, and let p = 2^(k-1). The function returns a result r with 0 <= r < p.
  Preconditions: 1 <= num < 2^31. -/
theorem spec_3 (num : Std.I64) (k : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_lo : 2 ^ (k - 1) ≤ num.val) (hk_hi : num.val < 2 ^ k) :
    ∃ r : Std.I64,
      find_complement num = Result.ok r ∧ 0 ≤ r.val ∧ r.val < 2 ^ (k - 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (num : Std.I64) (k : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_lo : 2 ^ (k - 1) ≤ num.val) (hk_hi : num.val < 2 ^ k), ∃ r : Std.I64,
      find_complement num = Result.ok r ∧ 0 ≤ r.val ∧ r.val < 2 ^ (k - 1)) := by
  sorry

/-- Let k be the unique positive integer such that 2^(k-1) <= num < 2^k. The function returns a result r and, for every integer i with 0 <= i < k, the i-th bit of r is the complement of the i-th bit of num: (r / 2^i) mod 2 = 1 - ((num / 2^i) mod 2).
  Preconditions: 1 <= num < 2^31. -/
theorem spec_4 (num : Std.I64) (k : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_lo : 2 ^ (k - 1) ≤ num.val) (hk_hi : num.val < 2 ^ k) :
    ∃ r : Std.I64,
      find_complement num = Result.ok r ∧
        ∀ i : Nat, i < k → (r.val / 2 ^ i) % 2 = 1 - (num.val / 2 ^ i) % 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (num : Std.I64) (k : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_lo : 2 ^ (k - 1) ≤ num.val) (hk_hi : num.val < 2 ^ k), ∃ r : Std.I64,
      find_complement num = Result.ok r ∧
        ∀ i : Nat, i < k → (r.val / 2 ^ i) % 2 = 1 - (num.val / 2 ^ i) % 2) := by
  sorry

/-- Let k be the unique positive integer such that 2^(k-1) <= num < 2^k. The function returns a result r and, for every integer i with i >= k, the i-th bit of r is 0; equivalently, r < 2^k.
  Preconditions: 1 <= num < 2^31. -/
theorem spec_5 (num : Std.I64) (k : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_lo : 2 ^ (k - 1) ≤ num.val) (hk_hi : num.val < 2 ^ k) :
    ∃ r : Std.I64,
      find_complement num = Result.ok r ∧
        (∀ i : Nat, k ≤ i → (r.val / 2 ^ i) % 2 = 0) ∧ r.val < 2 ^ k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (num : Std.I64) (k : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_lo : 2 ^ (k - 1) ≤ num.val) (hk_hi : num.val < 2 ^ k), ∃ r : Std.I64,
      find_complement num = Result.ok r ∧
        (∀ i : Nat, k ≤ i → (r.val / 2 ^ i) % 2 = 0) ∧ r.val < 2 ^ k) := by
  sorry

/-- Let k be the unique positive integer such that 2^(k-1) <= num < 2^k. The function returns a result r and r AND num = 0, where AND is bitwise conjunction: no bit position has a 1 in both r and num.
  Preconditions: 1 <= num < 2^31. -/
theorem spec_6 (num : Std.I64) (k : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_lo : 2 ^ (k - 1) ≤ num.val) (hk_hi : num.val < 2 ^ k) :
    ∃ r : Std.I64,
      find_complement num = Result.ok r ∧ r.val.toNat &&& num.val.toNat = 0 ∧
        ∀ i : Nat, (r.val / 2 ^ i) % 2 * ((num.val / 2 ^ i) % 2) = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (num : Std.I64) (k : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_lo : 2 ^ (k - 1) ≤ num.val) (hk_hi : num.val < 2 ^ k), ∃ r : Std.I64,
      find_complement num = Result.ok r ∧ r.val.toNat &&& num.val.toNat = 0 ∧
        ∀ i : Nat, (r.val / 2 ^ i) % 2 * ((num.val / 2 ^ i) % 2) = 0) := by
  sorry

/-- Let k be the unique positive integer such that 2^(k-1) <= num < 2^k. The function returns a result r and r OR num = 2^k - 1, where OR is bitwise disjunction: every bit position below k is 1 in exactly one of r and num.
  Preconditions: 1 <= num < 2^31. -/
theorem spec_7 (num : Std.I64) (k : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_lo : 2 ^ (k - 1) ≤ num.val) (hk_hi : num.val < 2 ^ k) :
    ∃ r : Std.I64,
      find_complement num = Result.ok r ∧ r.val.toNat ||| num.val.toNat = 2 ^ k - 1 ∧
        ∀ i : Nat, i < k → (r.val / 2 ^ i) % 2 + (num.val / 2 ^ i) % 2 = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (num : Std.I64) (k : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_lo : 2 ^ (k - 1) ≤ num.val) (hk_hi : num.val < 2 ^ k), ∃ r : Std.I64,
      find_complement num = Result.ok r ∧ r.val.toNat ||| num.val.toNat = 2 ^ k - 1 ∧
        ∀ i : Nat, i < k → (r.val / 2 ^ i) % 2 + (num.val / 2 ^ i) % 2 = 1) := by
  sorry

/-- Let k be the unique positive integer such that 2^(k-1) <= num < 2^k. The function returns a result r and popcount(r) = k - popcount(num), where popcount(x) is the number of 1-bits in the standard binary representation of the nonnegative integer x.
  Preconditions: 1 <= num < 2^31. -/
theorem spec_8 (num : Std.I64) (k : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_lo : 2 ^ (k - 1) ≤ num.val) (hk_hi : num.val < 2 ^ k) :
    ∃ r : Std.I64,
      find_complement num = Result.ok r ∧ popcount r.val = k - popcount num.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (num : Std.I64) (k : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_lo : 2 ^ (k - 1) ≤ num.val) (hk_hi : num.val < 2 ^ k), ∃ r : Std.I64,
      find_complement num = Result.ok r ∧ popcount r.val = k - popcount num.val) := by
  sorry

/-- If num = 2^k - 1 for some positive integer k, then the function returns r = 0.
  Preconditions: 1 <= num < 2^31. -/
theorem spec_9 (num : Std.I64) (k : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_eq : num.val = 2 ^ k - 1) :
    ∃ r : Std.I64, find_complement num = Result.ok r ∧ r.val = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (num : Std.I64) (k : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_eq : num.val = 2 ^ k - 1), ∃ r : Std.I64, find_complement num = Result.ok r ∧ r.val = 0) := by
  sorry

/-- If num = 2^m for some integer m with 0 <= m <= 30, then the function returns r = num - 1.
  Preconditions: 1 <= num < 2^31. -/
theorem spec_10 (num : Std.I64) (m : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hm_le : m ≤ 30) (hm_eq : num.val = 2 ^ m) :
    ∃ r : Std.I64, find_complement num = Result.ok r ∧ r.val = num.val - 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (num : Std.I64) (m : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hm_le : m ≤ 30) (hm_eq : num.val = 2 ^ m), ∃ r : Std.I64, find_complement num = Result.ok r ∧ r.val = num.val - 1) := by
  sorry

/-- Let k be the unique positive integer such that 2^(k-1) <= num < 2^k. If num < 2^k - 1, then the function returns r with r > 0.
  Preconditions: 1 <= num < 2^31. -/
theorem spec_11 (num : Std.I64) (k : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_lo : 2 ^ (k - 1) ≤ num.val) (hk_hi : num.val < 2 ^ k)
    (hnum_lt_max : num.val < 2 ^ k - 1) :
    ∃ r : Std.I64, find_complement num = Result.ok r ∧ 0 < r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (num : Std.I64) (k : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_lo : 2 ^ (k - 1) ≤ num.val) (hk_hi : num.val < 2 ^ k)
    (hnum_lt_max : num.val < 2 ^ k - 1), ∃ r : Std.I64, find_complement num = Result.ok r ∧ 0 < r.val) := by
  sorry

/-- The function returns a result r and r mod 2 = 1 - (num mod 2).
  Preconditions: 1 <= num < 2^31. -/
theorem spec_12 (num : Std.I64)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31) :
    ∃ r : Std.I64,
      find_complement num = Result.ok r ∧ r.val % 2 = 1 - num.val % 2 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (num : Std.I64)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31), ∃ r : Std.I64,
      find_complement num = Result.ok r ∧ r.val % 2 = 1 - num.val % 2) := by
  sorry

/-- The function returns a result r and r < num.
  Preconditions: 1 <= num < 2^31. -/
theorem spec_13 (num : Std.I64)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31) :
    ∃ r : Std.I64, find_complement num = Result.ok r ∧ r.val < num.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (num : Std.I64)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31), ∃ r : Std.I64, find_complement num = Result.ok r ∧ r.val < num.val) := by
  sorry

/-- Let k be the unique positive integer such that 2^(k-1) <= num < 2^k. If the k-bit binary representation of num contains exactly one 0 bit (equivalently, num = 2^k - 1 - 2^j for some integer j with 0 <= j < k), then the function returns r = 2^j.
  Preconditions: 1 <= num < 2^31. -/
theorem spec_14 (num : Std.I64) (k j : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_lo : 2 ^ (k - 1) ≤ num.val) (hk_hi : num.val < 2 ^ k)
    (hj_lt : j < k) (hnum_eq : num.val = 2 ^ k - 1 - 2 ^ j) :
    ∃ r : Std.I64, find_complement num = Result.ok r ∧ r.val = 2 ^ j := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (num : Std.I64) (k j : Nat)
    (hnum : 1 ≤ num.val) (hnum_lt : num.val < 2 ^ 31)
    (hk_pos : 1 ≤ k) (hk_lo : 2 ^ (k - 1) ≤ num.val) (hk_hi : num.val < 2 ^ k)
    (hj_lt : j < k) (hnum_eq : num.val = 2 ^ k - 1 - 2 ^ j), ∃ r : Std.I64, find_complement num = Result.ok r ∧ r.val = 2 ^ j) := by
  sorry

end AegisSpec.FindComplement
