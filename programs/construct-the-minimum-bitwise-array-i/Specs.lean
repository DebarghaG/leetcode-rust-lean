import Aegis.MinBitwiseArray.Code.Funs

/-!
# Specifications of `Aegis.MinBitwiseArray.min_bitwise_array`

LeetCode problem `construct-the-minimum-bitwise-array-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinBitwiseArray

namespace AegisSpec.MinBitwiseArray

def IsPrimeInput (n : I64) : Prop :=
  Nat.Prime n.val.toNat ∧ 2 ≤ n.val ∧ n.val ≤ 1000

def OrSucc (x p : Nat) : Prop := x ||| (x + 1) = p

def HasOrSucc (n : I64) : Prop := ∃ x : Nat, OrSucc x n.val.toNat

def IsLeastOrSucc (n : I64) (x : Nat) : Prop :=
  OrSucc x n.val.toNat ∧ ∀ y : Nat, OrSucc y n.val.toNat → x ≤ y

def IsTwoAdicExp (p e : Nat) : Prop := 2 ^ e ∣ p + 1 ∧ ¬ (2 ^ (e + 1) ∣ p + 1)

/-- The function returns a result r, and len(r) = len(nums). For every i with 0 <= i < len(nums), let p = nums[i]. If there exists a nonnegative integer x such that x OR (x+1) = p, where OR is bitwise OR on nonnegative integers, then r[i] is the least such x; otherwise r[i] = -1.
  Preconditions: len(nums) is between 1 and 100 inclusive, and for every i with 0 <= i < len(nums), nums[i] is a prime integer with 2 <= nums[i] <= 1000. -/
theorem spec_1 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])) :
    ∃ r : alloc.vec.Vec I64,
      min_bitwise_array nums = ok r ∧ r.val.length = nums.val.length ∧
        ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
          (HasOrSucc (nums.val[i]) → IsLeastOrSucc (nums.val[i]) (r.val[i]).val.toNat) ∧
            (¬ HasOrSucc (nums.val[i]) → (r.val[i]).val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])), ∃ r : alloc.vec.Vec I64,
      min_bitwise_array nums = ok r ∧ r.val.length = nums.val.length ∧
        ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
          (HasOrSucc (nums.val[i]) → IsLeastOrSucc (nums.val[i]) (r.val[i]).val.toNat) ∧
            (¬ HasOrSucc (nums.val[i]) → (r.val[i]).val = -1)) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(nums).
  Preconditions: len(nums) is between 1 and 100 inclusive, and for every i with 0 <= i < len(nums), nums[i] is a prime integer with 2 <= nums[i] <= 1000. -/
theorem spec_2 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])) :
    ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r → r.val.length = nums.val.length := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])), ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r → r.val.length = nums.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), if r[i] != -1 then r[i] >= 0 and, writing x for the integer value of r[i], x OR (x+1) = nums[i].
  Preconditions: len(nums) is between 1 and 100 inclusive, and for every i with 0 <= i < len(nums), nums[i] is a prime integer with 2 <= nums[i] <= 1000. -/
theorem spec_3 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])) :
    ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
        (r.val[i]).val ≠ -1 →
          0 ≤ (r.val[i]).val ∧
            (r.val[i]).val.toNat ||| ((r.val[i]).val.toNat + 1) = (nums.val[i]).val.toNat := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])), ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
        (r.val[i]).val ≠ -1 →
          0 ≤ (r.val[i]).val ∧
            (r.val[i]).val.toNat ||| ((r.val[i]).val.toNat + 1) = (nums.val[i]).val.toNat) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r[i] = -1 if and only if there is no nonnegative integer x such that x OR (x+1) = nums[i].
  Preconditions: len(nums) is between 1 and 100 inclusive, and for every i with 0 <= i < len(nums), nums[i] is a prime integer with 2 <= nums[i] <= 1000. -/
theorem spec_4 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])) :
    ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
        ((r.val[i]).val = -1 ↔ ¬ HasOrSucc (nums.val[i])) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])), ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
        ((r.val[i]).val = -1 ↔ ¬ HasOrSucc (nums.val[i]))) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums) and r[i] != -1, every nonnegative integer y satisfying y OR (y+1) = nums[i] satisfies the integer inequality r[i] <= y.
  Preconditions: len(nums) is between 1 and 100 inclusive, and for every i with 0 <= i < len(nums), nums[i] is a prime integer with 2 <= nums[i] <= 1000. -/
theorem spec_5 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])) :
    ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
        (r.val[i]).val ≠ -1 →
          ∀ (y : Nat), OrSucc y (nums.val[i]).val.toNat → (r.val[i]).val ≤ (y : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])), ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
        (r.val[i]).val ≠ -1 →
          ∀ (y : Nat), OrSucc y (nums.val[i]).val.toNat → (r.val[i]).val ≤ (y : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), if r[i] != -1 then 0 <= r[i] < nums[i].
  Preconditions: len(nums) is between 1 and 100 inclusive, and for every i with 0 <= i < len(nums), nums[i] is a prime integer with 2 <= nums[i] <= 1000. -/
theorem spec_6 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])) :
    ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
        (r.val[i]).val ≠ -1 → 0 ≤ (r.val[i]).val ∧ (r.val[i]).val < (nums.val[i]).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])), ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
        (r.val[i]).val ≠ -1 → 0 ≤ (r.val[i]).val ∧ (r.val[i]).val < (nums.val[i]).val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r[i] = -1 if and only if nums[i] = 2.
  Preconditions: len(nums) is between 1 and 100 inclusive, and for every i with 0 <= i < len(nums), nums[i] is a prime integer with 2 <= nums[i] <= 1000. -/
theorem spec_7 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])) :
    ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
        ((r.val[i]).val = -1 ↔ (nums.val[i]).val = 2) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])), ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
        ((r.val[i]).val = -1 ↔ (nums.val[i]).val = 2)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), if nums[i] != 2 then, writing x for the integer value of r[i], x >= 0 and x OR (x+1) = nums[i].
  Preconditions: len(nums) is between 1 and 100 inclusive, and for every i with 0 <= i < len(nums), nums[i] is a prime integer with 2 <= nums[i] <= 1000. -/
theorem spec_8 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])) :
    ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
        (nums.val[i]).val ≠ 2 →
          0 ≤ (r.val[i]).val ∧
            (r.val[i]).val.toNat ||| ((r.val[i]).val.toNat + 1) = (nums.val[i]).val.toNat := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])), ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
        (nums.val[i]).val ≠ 2 →
          0 ≤ (r.val[i]).val ∧
            (r.val[i]).val.toNat ||| ((r.val[i]).val.toNat + 1) = (nums.val[i]).val.toNat) := by
  sorry

/-- Whenever the function returns a result r, for all i and j with 0 <= i < len(nums) and 0 <= j < len(nums), if nums[i] = nums[j] then r[i] = r[j].
  Preconditions: len(nums) is between 1 and 100 inclusive, and for every i with 0 <= i < len(nums), nums[i] is a prime integer with 2 <= nums[i] <= 1000. -/
theorem spec_9 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])) :
    ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length)
        (j : Nat) (hj : j < nums.val.length) (hj' : j < r.val.length),
        nums.val[i] = nums.val[j] → r.val[i] = r.val[j] := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])), ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length)
        (j : Nat) (hj : j < nums.val.length) (hj' : j < r.val.length),
        nums.val[i] = nums.val[j] → r.val[i] = r.val[j]) := by
  sorry

/-- The function returns a result r; it does not fail, overflow, or panic on any input satisfying the preconditions.
  Preconditions: len(nums) is between 1 and 100 inclusive, and for every i with 0 <= i < len(nums), nums[i] is a prime integer with 2 <= nums[i] <= 1000. -/
theorem spec_10 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])) :
    ∃ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])), ∃ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums) and r[i] != -1, r[i] is odd if and only if nums[i] mod 4 = 3; equivalently, r[i] is even if and only if nums[i] mod 4 = 1.
  Preconditions: len(nums) is between 1 and 100 inclusive, and for every i with 0 <= i < len(nums), nums[i] is a prime integer with 2 <= nums[i] <= 1000. -/
theorem spec_11 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])) :
    ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
        (r.val[i]).val ≠ -1 →
          (Odd (r.val[i]).val ↔ (nums.val[i]).val % 4 = 3) ∧
            (Even (r.val[i]).val ↔ (nums.val[i]).val % 4 = 1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])), ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
        (r.val[i]).val ≠ -1 →
          (Odd (r.val[i]).val ↔ (nums.val[i]).val % 4 = 3) ∧
            (Even (r.val[i]).val ↔ (nums.val[i]).val % 4 = 1)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), if nums[i] mod 4 = 1 then r[i] = nums[i] - 1.
  Preconditions: len(nums) is between 1 and 100 inclusive, and for every i with 0 <= i < len(nums), nums[i] is a prime integer with 2 <= nums[i] <= 1000. -/
theorem spec_12 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])) :
    ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
        (nums.val[i]).val % 4 = 1 → (r.val[i]).val = (nums.val[i]).val - 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])), ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
        (nums.val[i]).val % 4 = 1 → (r.val[i]).val = (nums.val[i]).val - 1) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), let p = nums[i] and let e be the largest nonnegative integer such that 2^e divides p + 1. If p = 2 then r[i] = -1; otherwise e >= 1 and r[i] = p - 2^(e-1).
  Preconditions: len(nums) is between 1 and 100 inclusive, and for every i with 0 <= i < len(nums), nums[i] is a prime integer with 2 <= nums[i] <= 1000. -/
theorem spec_13 (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])) :
    ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
        ∀ (e : Nat), IsTwoAdicExp (nums.val[i]).val.toNat e →
          ((nums.val[i]).val.toNat = 2 → (r.val[i]).val = -1) ∧
            ((nums.val[i]).val.toNat ≠ 2 →
              1 ≤ e ∧ (r.val[i]).val = (nums.val[i]).val - ((2 ^ (e - 1) : Nat) : Int)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100)
    (hprime : ∀ (i : Nat) (hi : i < nums.val.length), IsPrimeInput (nums.val[i])), ∀ r : alloc.vec.Vec I64, min_bitwise_array nums = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length) (hi' : i < r.val.length),
        ∀ (e : Nat), IsTwoAdicExp (nums.val[i]).val.toNat e →
          ((nums.val[i]).val.toNat = 2 → (r.val[i]).val = -1) ∧
            ((nums.val[i]).val.toNat ≠ 2 →
              1 ≤ e ∧ (r.val[i]).val = (nums.val[i]).val - ((2 ^ (e - 1) : Nat) : Int))) := by
  sorry

end AegisSpec.MinBitwiseArray
