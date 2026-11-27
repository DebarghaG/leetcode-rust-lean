import Aegis.LongestMonotonicSubarray.Code.Funs

/-!
# Specifications of `Aegis.LongestMonotonicSubarray.longest_monotonic_subarray`

LeetCode problem `longest-strictly-increasing-or-strictly-decreasing-subarray`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LongestMonotonicSubarray

def size (nums : Slice Std.I64) : Nat := nums.val.length

def elem (nums : Slice Std.I64) (i : Nat) : Int :=
  match nums.val[i]? with
  | some x => x.val
  | none => 0

def StrictIncOn (nums : Slice Std.I64) (a m : Nat) : Prop :=
  ∀ i, a ≤ i → i < a + m - 1 → elem nums i < elem nums (i + 1)

def StrictDecOn (nums : Slice Std.I64) (a m : Nat) : Prop :=
  ∀ i, a ≤ i → i < a + m - 1 → elem nums (i + 1) < elem nums i

def MonotonicOn (nums : Slice Std.I64) (a m : Nat) : Prop :=
  StrictIncOn nums a m ∨ StrictDecOn nums a m

def StrictIncOnV (v : Nat → Int) (a m : Nat) : Prop :=
  ∀ i, a ≤ i → i < a + m - 1 → v i < v (i + 1)

def StrictDecOnV (v : Nat → Int) (a m : Nat) : Prop :=
  ∀ i, a ≤ i → i < a + m - 1 → v (i + 1) < v i

def MonotonicOnV (v : Nat → Int) (a m : Nat) : Prop :=
  StrictIncOnV v a m ∨ StrictDecOnV v a m

def IsMaxMonotonicLen (v : Nat → Int) (n : Nat) (k : Int) : Prop :=
  1 ≤ k ∧
  k ≤ (n : Int) ∧
  (∃ a : Nat, a + k.toNat ≤ n ∧ MonotonicOnV v a k.toNat) ∧
  (∀ (m a : Nat), k < (m : Int) → a + m ≤ n → ¬ MonotonicOnV v a m)

def IsMaxMonotonicLenOf (nums : Slice Std.I64) (k : Int) : Prop :=
  IsMaxMonotonicLen (elem nums) (size nums) k

/-- The function returns a result r. Let k be the integer value of r. Call a contiguous subarray nums[a..b), where 0 <= a < b <= len(nums), strictly increasing if nums[i] < nums[i+1] for every i with a <= i < b-1, and strictly decreasing if nums[i] > nums[i+1] for every i with a <= i < b-1. Then k is the greatest integer with 1 <= k <= len(nums) for which there exists a with 0 <= a and a+k <= len(nums) such that nums[a..a+k) is strictly increasing or strictly decreasing. Equivalently, k is the maximum length of a nonempty contiguous subarray of nums that is either strictly increasing or strictly decreasing.
  Preconditions: len(nums) >= 1, len(nums) <= 50, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50) :
    ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧
        IsMaxMonotonicLenOf nums r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50), ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧
        IsMaxMonotonicLenOf nums r.val) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; in particular, it does not overflow, access out of bounds, or panic.
  Preconditions: len(nums) >= 1, len(nums) <= 50, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50) :
    ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50), ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r) := by
  sorry

/-- The function returns a result r. Let k be the integer value of r. Then 1 <= k <= len(nums).
  Preconditions: len(nums) >= 1, len(nums) <= 50, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50) :
    ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧
        1 ≤ r.val ∧ r.val ≤ (size nums : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50), ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧
        1 ≤ r.val ∧ r.val ≤ (size nums : Int)) := by
  sorry

/-- The function returns a result r. Let k be the integer value of r. There exists an index a with 0 <= a, k >= 1, and a+k <= len(nums) such that either nums[i] < nums[i+1] for every i with a <= i < a+k-1, or nums[i] > nums[i+1] for every i with a <= i < a+k-1.
  Preconditions: len(nums) >= 1, len(nums) <= 50, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50) :
    ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧
        1 ≤ r.val ∧
        ∃ a : Nat,
          a + r.val.toNat ≤ size nums ∧
            (StrictIncOn nums a r.val.toNat ∨ StrictDecOn nums a r.val.toNat) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50), ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧
        1 ≤ r.val ∧
        ∃ a : Nat,
          a + r.val.toNat ≤ size nums ∧
            (StrictIncOn nums a r.val.toNat ∨ StrictDecOn nums a r.val.toNat)) := by
  sorry

/-- The function returns a result r. Let k be the integer value of r. For every length m with k < m <= len(nums) and every index a with 0 <= a and a+m <= len(nums), the contiguous subarray nums[a..a+m) is neither strictly increasing nor strictly decreasing; that is, it is not the case that nums[i] < nums[i+1] for all a <= i < a+m-1, and it is not the case that nums[i] > nums[i+1] for all a <= i < a+m-1.
  Preconditions: len(nums) >= 1, len(nums) <= 50, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50) :
    ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧
        ∀ m : Nat, r.val < (m : Int) → m ≤ size nums →
          ∀ a : Nat, a + m ≤ size nums → ¬ StrictIncOn nums a m ∧ ¬ StrictDecOn nums a m := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50), ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧
        ∀ m : Nat, r.val < (m : Int) → m ≤ size nums →
          ∀ a : Nat, a + m ≤ size nums → ¬ StrictIncOn nums a m ∧ ¬ StrictDecOn nums a m) := by
  sorry

/-- Whenever len(nums) = 1, the function returns a result r and the integer value of r is 1.
  Preconditions: len(nums) >= 1, len(nums) <= 50, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50)
    (hsingle : size nums = 1) :
    ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧ r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50)
    (hsingle : size nums = 1), ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧ r.val = 1) := by
  sorry

/-- Whenever nums[i] = nums[i+1] for every i with 0 <= i < len(nums)-1, the function returns a result r and the integer value of r is 1.
  Preconditions: len(nums) >= 1, len(nums) <= 50, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50)
    (hconst : ∀ i, i < size nums - 1 → elem nums i = elem nums (i + 1)) :
    ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧ r.val = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50)
    (hconst : ∀ i, i < size nums - 1 → elem nums i = elem nums (i + 1)), ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧ r.val = 1) := by
  sorry

/-- Whenever nums[i] < nums[i+1] for every i with 0 <= i < len(nums)-1, the function returns a result r and the integer value of r is len(nums).
  Preconditions: len(nums) >= 1, len(nums) <= 50, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50)
    (hinc : ∀ i, i < size nums - 1 → elem nums i < elem nums (i + 1)) :
    ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧
        r.val = (size nums : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50)
    (hinc : ∀ i, i < size nums - 1 → elem nums i < elem nums (i + 1)), ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧
        r.val = (size nums : Int)) := by
  sorry

/-- Whenever nums[i] > nums[i+1] for every i with 0 <= i < len(nums)-1, the function returns a result r and the integer value of r is len(nums).
  Preconditions: len(nums) >= 1, len(nums) <= 50, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50)
    (hdec : ∀ i, i < size nums - 1 → elem nums (i + 1) < elem nums i) :
    ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧
        r.val = (size nums : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50)
    (hdec : ∀ i, i < size nums - 1 → elem nums (i + 1) < elem nums i), ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧
        r.val = (size nums : Int)) := by
  sorry

/-- If there exists an index i with 0 <= i < len(nums)-1 and nums[i] != nums[i+1], then the function returns a result r whose integer value k satisfies k >= 2.
  Preconditions: len(nums) >= 1, len(nums) <= 50, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50)
    (hnonconst : ∃ i, i < size nums - 1 ∧ elem nums i ≠ elem nums (i + 1)) :
    ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧
        2 ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50)
    (hnonconst : ∃ i, i < size nums - 1 ∧ elem nums i ≠ elem nums (i + 1)), ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧
        2 ≤ r.val) := by
  sorry

/-- The function returns a result r. Let k be the integer value of r. For every index a and every length m with 1 <= m <= len(nums), 0 <= a, and a+m <= len(nums), if either nums[i] < nums[i+1] for every i with a <= i < a+m-1 or nums[i] > nums[i+1] for every i with a <= i < a+m-1, then k >= m.
  Preconditions: len(nums) >= 1, len(nums) <= 50, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50) :
    ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧
        ∀ (a m : Nat), 1 ≤ m → m ≤ size nums → a + m ≤ size nums →
          (StrictIncOn nums a m ∨ StrictDecOn nums a m) → (m : Int) ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50), ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧
        ∀ (a m : Nat), 1 ≤ m → m ≤ size nums → a + m ≤ size nums →
          (StrictIncOn nums a m ∨ StrictDecOn nums a m) → (m : Int) ≤ r.val) := by
  sorry

/-- The function returns a result r. Let k be the integer value of r. For every integer c such that nums[i] + c is representable as a 64-bit signed integer for all i with 0 <= i < len(nums), let nums' be the array with nums'[i] = nums[i] + c. Then k is also the maximum length of a nonempty contiguous subarray of nums' that is either strictly increasing or strictly decreasing, where comparisons are on the integer values nums[i] + c.
  Preconditions: len(nums) >= 1, len(nums) <= 50, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 50. -/
theorem spec_12 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50) :
    ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧
        ∀ c : Int,
          (∀ i, i < size nums → -(2 : Int) ^ 63 ≤ elem nums i + c ∧ elem nums i + c < (2 : Int) ^ 63) →
            IsMaxMonotonicLen (fun i => elem nums i + c) (size nums) r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen50 : size nums ≤ 50)
    (hval : ∀ i, i < size nums → 1 ≤ elem nums i ∧ elem nums i ≤ 50), ∃ r : Std.I64,
      Aegis.LongestMonotonicSubarray.longest_monotonic_subarray nums = ok r ∧
        ∀ c : Int,
          (∀ i, i < size nums → -(2 : Int) ^ 63 ≤ elem nums i + c ∧ elem nums i + c < (2 : Int) ^ 63) →
            IsMaxMonotonicLen (fun i => elem nums i + c) (size nums) r.val) := by
  sorry

end AegisSpec.LongestMonotonicSubarray
