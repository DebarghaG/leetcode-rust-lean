import Aegis.XorGame.Code.Funs

/-!
# Specifications of `Aegis.XorGame.xor_game`

LeetCode problem `chalkboard-xor-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.XorGame

def xorAll (l : List Std.I64) : ℕ :=
  l.foldr (fun x acc => x.val.toNat ^^^ acc) 0

/-- The function returns a result r and r is true if and only if X = 0 or len(nums) is even, where X is the bitwise XOR of all elements of nums: X = nums[0] XOR nums[1] XOR ... XOR nums[len(nums)-1]. Thus r is exactly the truth value of Alice winning the chalkboard game under optimal play.
  Preconditions: nums is a slice of 64-bit integers satisfying 1 <= len(nums) <= 1000 and, for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^16 (65536). -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ (Slice.len nums).val)
    (hlen_hi : (Slice.len nums).val ≤ 1000)
    (hval : ∀ (i : ℕ) (hi : i < (Slice.len nums).val),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val < 2 ^ 16) :
    ∃ r, Aegis.XorGame.xor_game nums = ok r ∧
      (r = true ↔ xorAll nums.val = 0 ∨ Even (Slice.len nums).val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ (Slice.len nums).val)
    (hlen_hi : (Slice.len nums).val ≤ 1000)
    (hval : ∀ (i : ℕ) (hi : i < (Slice.len nums).val),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val < 2 ^ 16), ∃ r, Aegis.XorGame.xor_game nums = ok r ∧
      (r = true ↔ xorAll nums.val = 0 ∨ Even (Slice.len nums).val)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r and does not fail: there is no arithmetic overflow, out-of-bounds access, or panic.
  Preconditions: nums is a slice of 64-bit integers satisfying 1 <= len(nums) <= 1000 and, for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^16 (65536). -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ (Slice.len nums).val)
    (hlen_hi : (Slice.len nums).val ≤ 1000)
    (hval : ∀ (i : ℕ) (hi : i < (Slice.len nums).val),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val < 2 ^ 16) :
    ∃ r, Aegis.XorGame.xor_game nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ (Slice.len nums).val)
    (hlen_hi : (Slice.len nums).val ≤ 1000)
    (hval : ∀ (i : ℕ) (hi : i < (Slice.len nums).val),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val < 2 ^ 16), ∃ r, Aegis.XorGame.xor_game nums = ok r) := by
  sorry

/-- The function returns true.
  Preconditions: nums is a slice of 64-bit integers satisfying 1 <= len(nums) <= 1000 and, for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^16 (65536). Let X be the bitwise XOR of all elements of nums, and assume X = 0. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ (Slice.len nums).val)
    (hlen_hi : (Slice.len nums).val ≤ 1000)
    (hval : ∀ (i : ℕ) (hi : i < (Slice.len nums).val),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val < 2 ^ 16)
    (hxor : xorAll nums.val = 0) :
    ∃ r, Aegis.XorGame.xor_game nums = ok r ∧ r = true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ (Slice.len nums).val)
    (hlen_hi : (Slice.len nums).val ≤ 1000)
    (hval : ∀ (i : ℕ) (hi : i < (Slice.len nums).val),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val < 2 ^ 16)
    (hxor : xorAll nums.val = 0), ∃ r, Aegis.XorGame.xor_game nums = ok r ∧ r = true) := by
  sorry

/-- The function returns true if and only if X = 0, where X is the bitwise XOR of all elements of nums.
  Preconditions: nums is a slice of 64-bit integers satisfying 1 <= len(nums) <= 1000 and, for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^16 (65536). Assume len(nums) is odd. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ (Slice.len nums).val)
    (hlen_hi : (Slice.len nums).val ≤ 1000)
    (hval : ∀ (i : ℕ) (hi : i < (Slice.len nums).val),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val < 2 ^ 16)
    (hodd : Odd (Slice.len nums).val) :
    ∃ r, Aegis.XorGame.xor_game nums = ok r ∧
      (r = true ↔ xorAll nums.val = 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ (Slice.len nums).val)
    (hlen_hi : (Slice.len nums).val ≤ 1000)
    (hval : ∀ (i : ℕ) (hi : i < (Slice.len nums).val),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val < 2 ^ 16)
    (hodd : Odd (Slice.len nums).val), ∃ r, Aegis.XorGame.xor_game nums = ok r ∧
      (r = true ↔ xorAll nums.val = 0)) := by
  sorry

/-- If the function returns false, then len(nums) is odd and X != 0, where X is the bitwise XOR of all elements of nums.
  Preconditions: nums is a slice of 64-bit integers satisfying 1 <= len(nums) <= 1000 and, for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^16 (65536). -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ (Slice.len nums).val)
    (hlen_hi : (Slice.len nums).val ≤ 1000)
    (hval : ∀ (i : ℕ) (hi : i < (Slice.len nums).val),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val < 2 ^ 16) :
    ∀ r, Aegis.XorGame.xor_game nums = ok r → r = false →
      Odd (Slice.len nums).val ∧ xorAll nums.val ≠ 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ (Slice.len nums).val)
    (hlen_hi : (Slice.len nums).val ≤ 1000)
    (hval : ∀ (i : ℕ) (hi : i < (Slice.len nums).val),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val < 2 ^ 16), ∀ r, Aegis.XorGame.xor_game nums = ok r → r = false →
      Odd (Slice.len nums).val ∧ xorAll nums.val ≠ 0) := by
  sorry

/-- The function returns true if and only if len(nums) is even.
  Preconditions: nums is a slice of 64-bit integers satisfying 1 <= len(nums) <= 1000 and, for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^16 (65536). Let X be the bitwise XOR of all elements of nums, and assume X != 0. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ (Slice.len nums).val)
    (hlen_hi : (Slice.len nums).val ≤ 1000)
    (hval : ∀ (i : ℕ) (hi : i < (Slice.len nums).val),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val < 2 ^ 16)
    (hxor : xorAll nums.val ≠ 0) :
    ∃ r, Aegis.XorGame.xor_game nums = ok r ∧
      (r = true ↔ Even (Slice.len nums).val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ (Slice.len nums).val)
    (hlen_hi : (Slice.len nums).val ≤ 1000)
    (hval : ∀ (i : ℕ) (hi : i < (Slice.len nums).val),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val < 2 ^ 16)
    (hxor : xorAll nums.val ≠ 0), ∃ r, Aegis.XorGame.xor_game nums = ok r ∧
      (r = true ↔ Even (Slice.len nums).val)) := by
  sorry

/-- For every slice ys of 64-bit integers that is a permutation of nums (same length and same multiset of values), the function returns the same Boolean on nums and on ys: if r is the result for nums and s is the result for ys, then r = s.
  Preconditions: nums is a slice of 64-bit integers satisfying 1 <= len(nums) <= 1000 and, for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^16 (65536). -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ (Slice.len nums).val)
    (hlen_hi : (Slice.len nums).val ≤ 1000)
    (hval : ∀ (i : ℕ) (hi : i < (Slice.len nums).val),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val < 2 ^ 16)
    (ys : Slice Std.I64) (hperm : List.Perm nums.val ys.val) :
    ∀ r s, Aegis.XorGame.xor_game nums = ok r → Aegis.XorGame.xor_game ys = ok s →
      r = s := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ (Slice.len nums).val)
    (hlen_hi : (Slice.len nums).val ≤ 1000)
    (hval : ∀ (i : ℕ) (hi : i < (Slice.len nums).val),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val < 2 ^ 16)
    (ys : Slice Std.I64) (hperm : List.Perm nums.val ys.val), ∀ r s, Aegis.XorGame.xor_game nums = ok r → Aegis.XorGame.xor_game ys = ok s →
      r = s) := by
  sorry

/-- For every integer x with 0 <= x < 2^16, if ys is the slice obtained by appending x twice to nums, then the function returns the same Boolean on nums and on ys.
  Preconditions: nums is a slice of 64-bit integers satisfying 1 <= len(nums) <= 1000 and, for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^16 (65536). Assume len(nums) <= 998. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ (Slice.len nums).val)
    (hlen_hi : (Slice.len nums).val ≤ 1000)
    (hval : ∀ (i : ℕ) (hi : i < (Slice.len nums).val),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val < 2 ^ 16)
    (hlen : (Slice.len nums).val ≤ 998) :
    ∀ (x : Std.I64), 0 ≤ x.val → x.val < 2 ^ 16 →
      ∀ (ys : Slice Std.I64), ys.val = nums.val ++ [x, x] →
        ∀ r s, Aegis.XorGame.xor_game nums = ok r → Aegis.XorGame.xor_game ys = ok s →
          r = s := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ (Slice.len nums).val)
    (hlen_hi : (Slice.len nums).val ≤ 1000)
    (hval : ∀ (i : ℕ) (hi : i < (Slice.len nums).val),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val < 2 ^ 16)
    (hlen : (Slice.len nums).val ≤ 998), ∀ (x : Std.I64), 0 ≤ x.val → x.val < 2 ^ 16 →
      ∀ (ys : Slice Std.I64), ys.val = nums.val ++ [x, x] →
        ∀ r s, Aegis.XorGame.xor_game nums = ok r → Aegis.XorGame.xor_game ys = ok s →
          r = s) := by
  sorry

/-- For every slice ys of 64-bit integers satisfying the same constraints, if the bitwise XOR of all elements of ys equals the bitwise XOR of all elements of nums and len(ys) has the same parity as len(nums), then the function returns the same Boolean on nums and on ys.
  Preconditions: nums is a slice of 64-bit integers satisfying 1 <= len(nums) <= 1000 and, for every i with 0 <= i < len(nums), 0 <= nums[i] < 2^16 (65536). -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ (Slice.len nums).val)
    (hlen_hi : (Slice.len nums).val ≤ 1000)
    (hval : ∀ (i : ℕ) (hi : i < (Slice.len nums).val),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val < 2 ^ 16)
    (ys : Slice Std.I64)
    (hlen_lo' : 1 ≤ (Slice.len ys).val)
    (hlen_hi' : (Slice.len ys).val ≤ 1000)
    (hval' : ∀ (i : ℕ) (hi : i < (Slice.len ys).val),
      0 ≤ (ys.val[i]'hi).val ∧ (ys.val[i]'hi).val < 2 ^ 16)
    (hxor : xorAll ys.val = xorAll nums.val)
    (hpar : Even (Slice.len ys).val ↔ Even (Slice.len nums).val) :
    ∀ r s, Aegis.XorGame.xor_game nums = ok r → Aegis.XorGame.xor_game ys = ok s →
      r = s := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ (Slice.len nums).val)
    (hlen_hi : (Slice.len nums).val ≤ 1000)
    (hval : ∀ (i : ℕ) (hi : i < (Slice.len nums).val),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val < 2 ^ 16)
    (ys : Slice Std.I64)
    (hlen_lo' : 1 ≤ (Slice.len ys).val)
    (hlen_hi' : (Slice.len ys).val ≤ 1000)
    (hval' : ∀ (i : ℕ) (hi : i < (Slice.len ys).val),
      0 ≤ (ys.val[i]'hi).val ∧ (ys.val[i]'hi).val < 2 ^ 16)
    (hxor : xorAll ys.val = xorAll nums.val)
    (hpar : Even (Slice.len ys).val ↔ Even (Slice.len nums).val), ∀ r s, Aegis.XorGame.xor_game nums = ok r → Aegis.XorGame.xor_game ys = ok s →
      r = s) := by
  sorry

end AegisSpec.XorGame
