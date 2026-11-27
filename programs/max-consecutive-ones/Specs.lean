import Aegis.FindMaxConsecutiveOnes.Code.Funs

/-!
# Specifications of `Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones`

LeetCode problem `max-consecutive-ones`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindMaxConsecutiveOnes

  def IsOneAt (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : ℕ) : Prop :=
    nums.val[k]? = some 1#i64

  def IsZeroAt (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : ℕ) : Prop :=
    nums.val[k]? = some 0#i64

  def BlockOfOnes (nums : Aeneas.Std.Slice Aeneas.Std.I64) (a b : ℕ) : Prop :=
    ∀ k, a ≤ k → k < b → IsOneAt nums k

  def blockLengths (nums : Aeneas.Std.Slice Aeneas.Std.I64) : Set ℤ :=
    {L | ∃ a b : ℕ, a ≤ b ∧ b ≤ nums.val.length ∧ L = (b : ℤ) - (a : ℤ) ∧ BlockOfOnes nums a b}

  def IsBitSlice (nums : Aeneas.Std.Slice Aeneas.Std.I64) : Prop :=
    ∀ k, k < nums.val.length → IsZeroAt nums k ∨ IsOneAt nums k

  /-- The function returns a result r and r is the maximum length of a contiguous block of entries equal to 1 in nums. Equivalently, let R = { b - a | 0 <= a <= b <= n and nums[k] = 1 for every k with a <= k < b }, where empty blocks of length 0 are included; then r = max(R). Thus r = 0 if no entry of nums is 1, and otherwise r is the largest L such that there is an index s with 0 <= s, s + L <= n, and nums[k] = 1 for every k with s <= k < s + L.
    Preconditions: nums is a slice of 64-bit integers with n = len(nums), 1 <= n <= 100000, and nums[i] is either 0 or 1 for every i with 0 <= i < n. -/
  theorem spec_1 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbits : IsBitSlice nums) :
      ∃ r : Aeneas.Std.I64,
        Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok r ∧
          IsGreatest (blockLengths nums) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbits : IsBitSlice nums), ∃ r : Aeneas.Std.I64,
          Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok r ∧
            IsGreatest (blockLengths nums) r.val) := by
    sorry

  /-- For every valid nums, the function returns a result r; in particular, it does not fail, panic, overflow, or go out of bounds.
    Preconditions: nums is a slice of 64-bit integers with n = len(nums), 1 <= n <= 100000, and nums[i] is either 0 or 1 for every i with 0 <= i < n. -/
  theorem spec_2 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbits : IsBitSlice nums) :
      ∃ r : Aeneas.Std.I64,
        Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbits : IsBitSlice nums), ∃ r : Aeneas.Std.I64,
          Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r and r <= len(nums).
    Preconditions: nums is a slice of 64-bit integers with n = len(nums), 1 <= n <= 100000, and nums[i] is either 0 or 1 for every i with 0 <= i < n. -/
  theorem spec_3 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbits : IsBitSlice nums) :
      ∀ r : Aeneas.Std.I64,
        Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok r →
          0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbits : IsBitSlice nums), ∀ r : Aeneas.Std.I64,
          Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok r →
            0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, there exists an index s such that 0 <= s, s + r <= len(nums), and nums[k] = 1 for every k with s <= k < s + r.
    Preconditions: nums is a slice of 64-bit integers with n = len(nums), 1 <= n <= 100000, and nums[i] is either 0 or 1 for every i with 0 <= i < n. -/
  theorem spec_4 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbits : IsBitSlice nums) :
      ∀ r : Aeneas.Std.I64,
        Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok r → 0 < r.val →
          ∃ s : ℕ, s + r.val.toNat ≤ nums.val.length ∧ BlockOfOnes nums s (s + r.val.toNat) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbits : IsBitSlice nums), ∀ r : Aeneas.Std.I64,
          Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok r → 0 < r.val →
            ∃ s : ℕ, s + r.val.toNat ≤ nums.val.length ∧ BlockOfOnes nums s (s + r.val.toNat)) := by
    sorry

  /-- Whenever the function returns a result r, there is no contiguous block of 1s longer than r: for every a and b with 0 <= a <= b <= len(nums) and b - a > r, there exists an index k with a <= k < b and nums[k] = 0.
    Preconditions: nums is a slice of 64-bit integers with n = len(nums), 1 <= n <= 100000, and nums[i] is either 0 or 1 for every i with 0 <= i < n. -/
  theorem spec_5 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbits : IsBitSlice nums) :
      ∀ r : Aeneas.Std.I64,
        Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok r →
          ∀ a b : ℕ, a ≤ b → b ≤ nums.val.length → (b : ℤ) - (a : ℤ) > r.val →
            ∃ k : ℕ, a ≤ k ∧ k < b ∧ IsZeroAt nums k := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbits : IsBitSlice nums), ∀ r : Aeneas.Std.I64,
          Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok r →
            ∀ a b : ℕ, a ≤ b → b ≤ nums.val.length → (b : ℤ) - (a : ℤ) > r.val →
              ∃ k : ℕ, a ≤ k ∧ k < b ∧ IsZeroAt nums k) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if nums[i] = 0 for every i with 0 <= i < len(nums).
    Preconditions: nums is a slice of 64-bit integers with n = len(nums), 1 <= n <= 100000, and nums[i] is either 0 or 1 for every i with 0 <= i < n. -/
  theorem spec_6 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbits : IsBitSlice nums) :
      ∀ r : Aeneas.Std.I64,
        Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok r →
          (r.val = 0 ↔ ∀ i : ℕ, i < nums.val.length → IsZeroAt nums i) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbits : IsBitSlice nums), ∀ r : Aeneas.Std.I64,
          Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok r →
            (r.val = 0 ↔ ∀ i : ℕ, i < nums.val.length → IsZeroAt nums i)) := by
    sorry

  /-- Whenever the function returns a result r, r = len(nums) if and only if nums[i] = 1 for every i with 0 <= i < len(nums).
    Preconditions: nums is a slice of 64-bit integers with n = len(nums), 1 <= n <= 100000, and nums[i] is either 0 or 1 for every i with 0 <= i < n. -/
  theorem spec_7 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
      (hbits : IsBitSlice nums) :
      ∀ r : Aeneas.Std.I64,
        Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok r →
          (r.val = (nums.val.length : ℤ) ↔
            ∀ i : ℕ, i < nums.val.length → IsOneAt nums i) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100000)
        (hbits : IsBitSlice nums), ∀ r : Aeneas.Std.I64,
          Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok r →
            (r.val = (nums.val.length : ℤ) ↔
              ∀ i : ℕ, i < nums.val.length → IsOneAt nums i)) := by
    sorry

  /-- For every valid nums with len(nums) < 100000, let nums' be the slice obtained by appending one entry equal to 0 to nums. The function returns a result r on nums and a result r' on nums', and r = r'.
    Preconditions: nums is a slice of 64-bit integers with n = len(nums), 1 <= n <= 100000, and nums[i] is either 0 or 1 for every i with 0 <= i < n. -/
  theorem spec_8 (nums nums' : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length < 100000)
      (hbits : IsBitSlice nums)
      (happend : nums'.val = nums.val ++ [0#i64]) :
      ∀ r r' : Aeneas.Std.I64,
        Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok r →
          Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums' = ok r' → r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length < 100000)
        (hbits : IsBitSlice nums)
        (happend : nums'.val = nums.val ++ [0#i64]), ∀ r r' : Aeneas.Std.I64,
          Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok r →
            Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums' = ok r' → r = r') := by
    sorry

  /-- For every valid nums with len(nums) < 100000, let nums' be the slice obtained by prepending one entry equal to 0 to nums. The function returns a result r on nums and a result r' on nums', and r = r'.
    Preconditions: nums is a slice of 64-bit integers with n = len(nums), 1 <= n <= 100000, and nums[i] is either 0 or 1 for every i with 0 <= i < n. -/
  theorem spec_9 (nums nums' : Aeneas.Std.Slice Aeneas.Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length < 100000)
      (hbits : IsBitSlice nums)
      (hprepend : nums'.val = 0#i64 :: nums.val) :
      ∀ r r' : Aeneas.Std.I64,
        Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok r →
          Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums' = ok r' → r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Aeneas.Std.Slice Aeneas.Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length < 100000)
        (hbits : IsBitSlice nums)
        (hprepend : nums'.val = 0#i64 :: nums.val), ∀ r r' : Aeneas.Std.I64,
          Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok r →
            Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums' = ok r' → r = r') := by
    sorry

  end AegisSpec.FindMaxConsecutiveOnes
