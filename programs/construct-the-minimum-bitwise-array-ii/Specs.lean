import Aegis.MinBitwiseArray.Code.Funs

/-!
# Specifications of `Aegis.MinBitwiseArray.min_bitwise_array`

LeetCode problem `construct-the-minimum-bitwise-array-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinBitwiseArray

def bitOr (x y : ℤ) : ℤ := ((x.natAbs ||| y.natAbs : ℕ) : ℤ)

def valAt? (l : List Std.I64) (i : ℕ) : Option ℤ := (l[i]?).map (fun x => x.val)

def IsPrimeInt (n : ℤ) : Prop := 2 ≤ n ∧ n.natAbs.Prime

def IsLeastBitOrPreimage (n v : ℤ) : Prop :=
  (∃ x : ℤ, 0 ≤ x ∧ bitOr x (x + 1) = n ∧ v = x ∧
      ∀ y : ℤ, 0 ≤ y → bitOr y (y + 1) = n → x ≤ y) ∨
    (v = -1 ∧ ∀ x : ℤ, 0 ≤ x → bitOr x (x + 1) ≠ n)

def IsTwoAdicExp (n : ℤ) (t : ℕ) : Prop :=
  (2 : ℤ) ^ t ∣ n + 1 ∧ ¬ ((2 : ℤ) ^ (t + 1) ∣ n + 1)

def bitSet (n : ℤ) (k : ℕ) : Prop := n.natAbs.testBit k = true

/-- Whenever `min_bitwise_array(nums)` returns `Ok r`, the vector r has length len(nums), and for every index i with 0 <= i < len(nums), r[i] is the least nonnegative integer x such that `x | (x + 1) = nums[i]`, where `|` is 64-bit bitwise OR; if no such nonnegative integer exists, then r[i] = -1.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), nums[i] is a prime integer and 2 <= nums[i] <= 10^9. -/
theorem spec_1 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r) :
    r.val.length = nums.val.length ∧
      ∀ (i : ℕ) (hi : i < nums.val.length),
        ∃ v : ℤ, valAt? r.val i = some v ∧ IsLeastBitOrPreimage (nums.val[i]).val v := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r), r.val.length = nums.val.length ∧
      ∀ (i : ℕ) (hi : i < nums.val.length),
        ∃ v : ℤ, valAt? r.val i = some v ∧ IsLeastBitOrPreimage (nums.val[i]).val v) := by
  sorry

/-- `min_bitwise_array(nums)` returns `Ok r` for some vector r; it does not fail, overflow, panic, or access out of bounds on these inputs.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), nums[i] is a prime integer and 2 <= nums[i] <= 10^9. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9) :
    ∃ r : alloc.vec.Vec Std.I64, Aegis.MinBitwiseArray.min_bitwise_array nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9), ∃ r : alloc.vec.Vec Std.I64, Aegis.MinBitwiseArray.min_bitwise_array nums = ok r) := by
  sorry

/-- Whenever `min_bitwise_array(nums)` returns `Ok r`, `len(r) = len(nums)`; the output has exactly one entry for each input entry and no extra entries.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), nums[i] is a prime integer and 2 <= nums[i] <= 10^9. -/
theorem spec_3 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r) :
    r.val.length = nums.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r), r.val.length = nums.val.length) := by
  sorry

/-- Whenever `min_bitwise_array(nums)` returns `Ok r`, for every index i with 0 <= i < len(nums), `-1 <= r[i] < nums[i]`.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), nums[i] is a prime integer and 2 <= nums[i] <= 10^9. -/
theorem spec_4 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r) :
    ∀ (i : ℕ) (hi : i < nums.val.length),
      ∃ v : ℤ, valAt? r.val i = some v ∧ -1 ≤ v ∧ v < (nums.val[i]).val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r), ∀ (i : ℕ) (hi : i < nums.val.length),
      ∃ v : ℤ, valAt? r.val i = some v ∧ -1 ≤ v ∧ v < (nums.val[i]).val) := by
  sorry

/-- Whenever `min_bitwise_array(nums)` returns `Ok r`, for every index i with 0 <= i < len(nums), `r[i] = -1` if and only if `nums[i] = 2`.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), nums[i] is a prime integer and 2 <= nums[i] <= 10^9. -/
theorem spec_5 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r) :
    ∀ (i : ℕ) (hi : i < nums.val.length),
      valAt? r.val i = some (-1) ↔ (nums.val[i]).val = 2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r), ∀ (i : ℕ) (hi : i < nums.val.length),
      valAt? r.val i = some (-1) ↔ (nums.val[i]).val = 2) := by
  sorry

/-- Whenever `min_bitwise_array(nums)` returns `Ok r`, for every index i with 0 <= i < len(nums) and `nums[i] != 2`, the returned value is a witness: `r[i] | (r[i] + 1) = nums[i]`.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), nums[i] is a prime integer and 2 <= nums[i] <= 10^9. -/
theorem spec_6 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r) :
    ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val ≠ 2 →
      ∃ v : ℤ, valAt? r.val i = some v ∧ bitOr v (v + 1) = (nums.val[i]).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r), ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val ≠ 2 →
      ∃ v : ℤ, valAt? r.val i = some v ∧ bitOr v (v + 1) = (nums.val[i]).val) := by
  sorry

/-- Whenever `min_bitwise_array(nums)` returns `Ok r`, for every index i with 0 <= i < len(nums) and `r[i] = -1`, there is no 64-bit integer x with `0 <= x` such that `x | (x + 1) = nums[i]`.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), nums[i] is a prime integer and 2 <= nums[i] <= 10^9. -/
theorem spec_7 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r) :
    ∀ (i : ℕ) (hi : i < nums.val.length), valAt? r.val i = some (-1) →
      ∀ x : ℤ, 0 ≤ x → bitOr x (x + 1) ≠ (nums.val[i]).val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r), ∀ (i : ℕ) (hi : i < nums.val.length), valAt? r.val i = some (-1) →
      ∀ x : ℤ, 0 ≤ x → bitOr x (x + 1) ≠ (nums.val[i]).val) := by
  sorry

/-- Whenever `min_bitwise_array(nums)` returns `Ok r`, for every index i with 0 <= i < len(nums) and `nums[i] != 2`, for every 64-bit integer x with `0 <= x < r[i]`, `x | (x + 1) != nums[i]`.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), nums[i] is a prime integer and 2 <= nums[i] <= 10^9. -/
theorem spec_8 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r) :
    ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val ≠ 2 →
      ∃ v : ℤ, valAt? r.val i = some v ∧
        ∀ x : ℤ, 0 ≤ x → x < v → bitOr x (x + 1) ≠ (nums.val[i]).val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r), ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val ≠ 2 →
      ∃ v : ℤ, valAt? r.val i = some v ∧
        ∀ x : ℤ, 0 ≤ x → x < v → bitOr x (x + 1) ≠ (nums.val[i]).val) := by
  sorry

/-- Whenever `min_bitwise_array(nums)` returns `Ok r`, for every index i with 0 <= i < len(nums) and `nums[i] != 2`, let t_i be the positive integer such that `2^{t_i}` divides `nums[i] + 1` but `2^{t_i + 1}` does not divide `nums[i] + 1` (equivalently, t_i is the number of trailing 1 bits in the binary representation of nums[i]); then `r[i] = nums[i] - 2^{t_i - 1}`.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), nums[i] is a prime integer and 2 <= nums[i] <= 10^9. -/
theorem spec_9 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r) :
    ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val ≠ 2 →
      ∃ v : ℤ, valAt? r.val i = some v ∧
        ∀ t : ℕ, 0 < t → IsTwoAdicExp (nums.val[i]).val t →
          v = (nums.val[i]).val - (2 : ℤ) ^ (t - 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r), ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val ≠ 2 →
      ∃ v : ℤ, valAt? r.val i = some v ∧
        ∀ t : ℕ, 0 < t → IsTwoAdicExp (nums.val[i]).val t →
          v = (nums.val[i]).val - (2 : ℤ) ^ (t - 1)) := by
  sorry

/-- Whenever `min_bitwise_array(nums)` returns `Ok r`, for every index i with 0 <= i < len(nums) and `nums[i] != 2`, `r[i] mod 2 = 0` if and only if `nums[i] mod 4 = 1`; equivalently, for odd prime nums[i], r[i] is even exactly when nums[i] is congruent to 1 modulo 4, and r[i] is odd exactly when nums[i] is congruent to 3 modulo 4.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), nums[i] is a prime integer and 2 <= nums[i] <= 10^9. -/
theorem spec_10 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r) :
    ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val ≠ 2 →
      ∃ v : ℤ, valAt? r.val i = some v ∧
        (v % 2 = 0 ↔ (nums.val[i]).val % 4 = 1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r), ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val ≠ 2 →
      ∃ v : ℤ, valAt? r.val i = some v ∧
        (v % 2 = 0 ↔ (nums.val[i]).val % 4 = 1)) := by
  sorry

/-- Whenever `min_bitwise_array(nums)` returns `Ok r`, for all indices i and j with 0 <= i < len(nums) and 0 <= j < len(nums), if `nums[i] = nums[j]`, then `r[i] = r[j]`.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), nums[i] is a prime integer and 2 <= nums[i] <= 10^9. -/
theorem spec_11 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r) :
    ∀ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
      (nums.val[i]).val = (nums.val[j]).val → valAt? r.val i = valAt? r.val j := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r), ∀ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
      (nums.val[i]).val = (nums.val[j]).val → valAt? r.val i = valAt? r.val j) := by
  sorry

/-- Whenever `min_bitwise_array(nums)` returns `Ok r`, for every index i with 0 <= i < len(nums) and `nums[i] != 2`, let t_i be as in spec_9. In the 64-bit binary representations of r[i] and nums[i], all bit positions except position `t_i - 1` agree; at position `t_i - 1`, nums[i] has bit 1 and r[i] has bit 0.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, and for every index i with 0 <= i < len(nums), nums[i] is a prime integer and 2 <= nums[i] <= 10^9. -/
theorem spec_12 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r) :
    ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val ≠ 2 →
      ∃ v : ℤ, valAt? r.val i = some v ∧
        ∀ t : ℕ, 0 < t → IsTwoAdicExp (nums.val[i]).val t →
          (∀ k : ℕ, k < 64 → k ≠ t - 1 → (bitSet v k ↔ bitSet (nums.val[i]).val k)) ∧
            bitSet (nums.val[i]).val (t - 1) ∧ ¬ bitSet v (t - 1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
    (hprime : ∀ (i : ℕ) (hi : i < nums.val.length),
      IsPrimeInt (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10 ^ 9)
    (hres : Aegis.MinBitwiseArray.min_bitwise_array nums = ok r), ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val ≠ 2 →
      ∃ v : ℤ, valAt? r.val i = some v ∧
        ∀ t : ℕ, 0 < t → IsTwoAdicExp (nums.val[i]).val t →
          (∀ k : ℕ, k < 64 → k ≠ t - 1 → (bitSet v k ↔ bitSet (nums.val[i]).val k)) ∧
            bitSet (nums.val[i]).val (t - 1) ∧ ¬ bitSet v (t - 1)) := by
  sorry

end AegisSpec.MinBitwiseArray
