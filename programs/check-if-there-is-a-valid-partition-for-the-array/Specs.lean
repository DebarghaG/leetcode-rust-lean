import Aegis.ValidPartition.Code.Funs

/-!
# Specifications of `Aegis.ValidPartition.valid_partition`

LeetCode problem `check-if-there-is-a-valid-partition-for-the-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std
open Aeneas.Std.Result

namespace AegisSpec.ValidPartition

open Aegis.ValidPartition

def vals (nums : Slice I64) : List Int := nums.val.map (fun x => x.val)

def GoodBlock (l : List Int) (a b : Nat) : Prop :=
  (b - a + 1 = 2 ∧ ∃ x, l[a]? = some x ∧ l[b]? = some x) ∨
  (b - a + 1 = 3 ∧ ∃ x, l[a]? = some x ∧ l[a + 1]? = some x ∧ l[a + 2]? = some x) ∨
  (b - a + 1 = 3 ∧
    ∃ x, l[a]? = some x ∧ l[a + 1]? = some (x + 1) ∧ l[a + 2]? = some (x + 2))

def AdmitsPartition (l : List Int) : Prop :=
  ∃ k : Nat, 1 ≤ k ∧ ∃ c : Nat → Nat,
    c 0 = 0 ∧ c k = l.length ∧
      (∀ j, j < k → c j < c (j + 1)) ∧
      (∀ j, j < k → GoodBlock l (c j) (c (j + 1) - 1))

/-- The function returns a result r and does not fail. r = true if and only if there exist an integer k >= 1 and integers 0 = c_0 < c_1 < ... < c_k = n such that for every j with 0 <= j < k, the contiguous subarray nums[c_j .. c_{j+1}-1] is good, where a subarray nums[a .. b] is good exactly when either (b-a+1 = 2 and nums[a] = nums[b]), or (b-a+1 = 3 and nums[a] = nums[a+1] and nums[a+1] = nums[a+2]), or (b-a+1 = 3 and nums[a+1] = nums[a]+1 and nums[a+2] = nums[a+1]+1). If no such partition exists, r = false.
  Preconditions: Let n = len(nums). 2 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000. -/
theorem spec_1 (nums : Slice I64)
    (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000) :
    ∃ r, valid_partition nums = ok r ∧ (r = true ↔ AdmitsPartition (vals nums)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000), ∃ r, valid_partition nums = ok r ∧ (r = true ↔ AdmitsPartition (vals nums))) := by
  sorry

/-- The function returns a result r and does not fail; no arithmetic overflow, out-of-bounds access, or panic occurs while producing r.
  Preconditions: Let n = len(nums). 2 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000. -/
theorem spec_2 (nums : Slice I64)
    (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000) :
    ∃ r, valid_partition nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000), ∃ r, valid_partition nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if nums[0] = nums[1].
  Preconditions: Let n = len(nums). n = 2, 1 <= nums[0] <= 1000000, and 1 <= nums[1] <= 1000000. -/
theorem spec_3 (nums : Slice I64)
    (hlen : nums.val.length = 2)
    (h0 : 1 ≤ (nums.val[0]'(by omega)).val ∧ (nums.val[0]'(by omega)).val ≤ 1000000)
    (h1 : 1 ≤ (nums.val[1]'(by omega)).val ∧ (nums.val[1]'(by omega)).val ≤ 1000000) :
    ∀ r, valid_partition nums = ok r →
      (r = true ↔ (nums.val[0]'(by omega)).val = (nums.val[1]'(by omega)).val) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : nums.val.length = 2)
    (h0 : 1 ≤ (nums.val[0]'(by omega)).val ∧ (nums.val[0]'(by omega)).val ≤ 1000000)
    (h1 : 1 ≤ (nums.val[1]'(by omega)).val ∧ (nums.val[1]'(by omega)).val ≤ 1000000), ∀ r, valid_partition nums = ok r →
      (r = true ↔ (nums.val[0]'(by omega)).val = (nums.val[1]'(by omega)).val)) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if either (nums[0] = nums[1] and nums[1] = nums[2]) or (nums[1] = nums[0]+1 and nums[2] = nums[1]+1).
  Preconditions: Let n = len(nums). n = 3, and every element of nums is in [1,1000000]. -/
theorem spec_4 (nums : Slice I64)
    (hlen : nums.val.length = 3)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000) :
    ∀ r, valid_partition nums = ok r →
      (r = true ↔
        ((nums.val[0]'(by omega)).val = (nums.val[1]'(by omega)).val ∧
            (nums.val[1]'(by omega)).val = (nums.val[2]'(by omega)).val) ∨
          ((nums.val[1]'(by omega)).val = (nums.val[0]'(by omega)).val + 1 ∧
            (nums.val[2]'(by omega)).val = (nums.val[1]'(by omega)).val + 1)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : nums.val.length = 3)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000), ∀ r, valid_partition nums = ok r →
      (r = true ↔
        ((nums.val[0]'(by omega)).val = (nums.val[1]'(by omega)).val ∧
            (nums.val[1]'(by omega)).val = (nums.val[2]'(by omega)).val) ∨
          ((nums.val[1]'(by omega)).val = (nums.val[0]'(by omega)).val + 1 ∧
            (nums.val[2]'(by omega)).val = (nums.val[1]'(by omega)).val + 1))) := by
  sorry

/-- Whenever the function returns a result r, r = true.
  Preconditions: Let n = len(nums). 2 <= n <= 100000, every element of nums is in [1,1000000], and nums[i] = nums[0] for every i with 0 <= i < n. -/
theorem spec_5 (nums : Slice I64)
    (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (hconst : ∀ i (hi : i < nums.val.length),
      (nums.val[i]).val = (nums.val[0]'(by omega)).val) :
    ∀ r, valid_partition nums = ok r → r = true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (hconst : ∀ i (hi : i < nums.val.length),
      (nums.val[i]).val = (nums.val[0]'(by omega)).val), ∀ r, valid_partition nums = ok r → r = true) := by
  sorry

/-- Whenever the function returns a result r, r = false.
  Preconditions: Let n = len(nums). 2 <= n <= 100000 and every element of nums is in [1,1000000]. For every i with 0 <= i < n-1, nums[i] != nums[i+1]. For every i with 0 <= i < n-2, it is not the case that both nums[i+1] = nums[i]+1 and nums[i+2] = nums[i+1]+1. -/
theorem spec_6 (nums : Slice I64)
    (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (hadj : ∀ i (hi : i < nums.val.length - 1), (nums.val[i]).val ≠ (nums.val[i + 1]).val)
    (htriple : ∀ i (hi : i < nums.val.length - 2),
      ¬ ((nums.val[i + 1]).val = (nums.val[i]).val + 1 ∧
          (nums.val[i + 2]).val = (nums.val[i + 1]).val + 1)) :
    ∀ r, valid_partition nums = ok r → r = false := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (hadj : ∀ i (hi : i < nums.val.length - 1), (nums.val[i]).val ≠ (nums.val[i + 1]).val)
    (htriple : ∀ i (hi : i < nums.val.length - 2),
      ¬ ((nums.val[i + 1]).val = (nums.val[i]).val + 1 ∧
          (nums.val[i + 2]).val = (nums.val[i + 1]).val + 1)), ∀ r, valid_partition nums = ok r → r = false) := by
  sorry

/-- Whenever the function returns a result r, if r = true then either nums[0] = nums[1], or (n >= 3 and nums[1] = nums[0]+1 and nums[2] = nums[1]+1).
  Preconditions: Let n = len(nums). 2 <= n <= 100000 and every element of nums is in [1,1000000]. -/
theorem spec_7 (nums : Slice I64)
    (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000) :
    ∀ r, valid_partition nums = ok r → r = true →
      ((nums.val[0]'(by omega)).val = (nums.val[1]'(by omega)).val ∨
        ∃ (hn : 3 ≤ nums.val.length),
          (nums.val[1]'(by omega)).val = (nums.val[0]'(by omega)).val + 1 ∧
          (nums.val[2]'(by omega)).val = (nums.val[1]'(by omega)).val + 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000), ∀ r, valid_partition nums = ok r → r = true →
      ((nums.val[0]'(by omega)).val = (nums.val[1]'(by omega)).val ∨
        ∃ (hn : 3 ≤ nums.val.length),
          (nums.val[1]'(by omega)).val = (nums.val[0]'(by omega)).val + 1 ∧
          (nums.val[2]'(by omega)).val = (nums.val[1]'(by omega)).val + 1)) := by
  sorry

/-- Whenever the function returns a result r, if r = true then either nums[n-2] = nums[n-1], or (n >= 3 and nums[n-2] = nums[n-3]+1 and nums[n-1] = nums[n-2]+1).
  Preconditions: Let n = len(nums). 2 <= n <= 100000 and every element of nums is in [1,1000000]. -/
theorem spec_8 (nums : Slice I64)
    (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000) :
    ∀ r, valid_partition nums = ok r → r = true →
      ((nums.val[nums.val.length - 2]'(by omega)).val =
          (nums.val[nums.val.length - 1]'(by omega)).val ∨
        (3 ≤ nums.val.length ∧
          (nums.val[nums.val.length - 2]'(by omega)).val =
            (nums.val[nums.val.length - 3]'(by omega)).val + 1 ∧
          (nums.val[nums.val.length - 1]'(by omega)).val =
            (nums.val[nums.val.length - 2]'(by omega)).val + 1)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000), ∀ r, valid_partition nums = ok r → r = true →
      ((nums.val[nums.val.length - 2]'(by omega)).val =
          (nums.val[nums.val.length - 1]'(by omega)).val ∨
        (3 ≤ nums.val.length ∧
          (nums.val[nums.val.length - 2]'(by omega)).val =
            (nums.val[nums.val.length - 3]'(by omega)).val + 1 ∧
          (nums.val[nums.val.length - 1]'(by omega)).val =
            (nums.val[nums.val.length - 2]'(by omega)).val + 1))) := by
  sorry

/-- Whenever the function returns a result r, if there exists an index i with 0 < i < n such that the prefix nums[0 .. i-1] admits a valid partition and the suffix nums[i .. n-1] is a good block, then r = true.
  Preconditions: Let n = len(nums). 2 <= n <= 100000 and every element of nums is in [1,1000000]. -/
theorem spec_9 (nums : Slice I64)
    (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000) :
    ∀ r, valid_partition nums = ok r →
      (∃ i, 0 < i ∧ i < nums.val.length ∧
        AdmitsPartition ((vals nums).extract 0 i) ∧
        GoodBlock (vals nums) i (nums.val.length - 1)) →
      r = true := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000), ∀ r, valid_partition nums = ok r →
      (∃ i, 0 < i ∧ i < nums.val.length ∧
        AdmitsPartition ((vals nums).extract 0 i) ∧
        GoodBlock (vals nums) i (nums.val.length - 1)) →
      r = true) := by
  sorry

/-- The calls valid_partition(nums) and valid_partition(shifted) both return results, and their Boolean results are equal.
  Preconditions: Let n = len(nums). 2 <= n <= 100000 and every element of nums is in [1,1000000]. Let c be an integer and let shifted be a slice of length n with shifted[i] = nums[i]+c for every i with 0 <= i < n. Assume each nums[i]+c is representable as a 64-bit integer and 1 <= shifted[i] <= 1000000 for every i. -/
theorem spec_10 (nums shifted : Slice I64) (c : Int)
    (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (hlen' : shifted.val.length = nums.val.length)
    (hshift : ∀ i (hi : i < nums.val.length),
      (shifted.val[i]).val = (nums.val[i]).val + c)
    (hrepr : ∀ i (hi : i < nums.val.length),
      -((2 : Int) ^ 63) ≤ (nums.val[i]).val + c ∧ (nums.val[i]).val + c < (2 : Int) ^ 63)
    (hrange' : ∀ i (hi : i < shifted.val.length),
      1 ≤ (shifted.val[i]).val ∧ (shifted.val[i]).val ≤ 1000000) :
    ∃ r1 r2, valid_partition nums = ok r1 ∧ valid_partition shifted = ok r2 ∧ r1 = r2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums shifted : Slice I64) (c : Int)
    (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (hlen' : shifted.val.length = nums.val.length)
    (hshift : ∀ i (hi : i < nums.val.length),
      (shifted.val[i]).val = (nums.val[i]).val + c)
    (hrepr : ∀ i (hi : i < nums.val.length),
      -((2 : Int) ^ 63) ≤ (nums.val[i]).val + c ∧ (nums.val[i]).val + c < (2 : Int) ^ 63)
    (hrange' : ∀ i (hi : i < shifted.val.length),
      1 ≤ (shifted.val[i]).val ∧ (shifted.val[i]).val ≤ 1000000), ∃ r1 r2, valid_partition nums = ok r1 ∧ valid_partition shifted = ok r2 ∧ r1 = r2) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if n is divisible by 3.
  Preconditions: Let n = len(nums). 2 <= n <= 100000, every element of nums is in [1,1000000], and for every i with 0 <= i < n-1, nums[i+1] = nums[i]+1. -/
theorem spec_11 (nums : Slice I64)
    (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (hinc : ∀ i (hi : i < nums.val.length - 1),
      (nums.val[i + 1]).val = (nums.val[i]).val + 1) :
    ∀ r, valid_partition nums = ok r → (r = true ↔ 3 ∣ nums.val.length) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (hinc : ∀ i (hi : i < nums.val.length - 1),
      (nums.val[i + 1]).val = (nums.val[i]).val + 1), ∀ r, valid_partition nums = ok r → (r = true ↔ 3 ∣ nums.val.length)) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if nums[0] = nums[1] and nums[2] = nums[3].
  Preconditions: Let n = len(nums). n = 4 and every element of nums is in [1,1000000]. -/
theorem spec_12 (nums : Slice I64)
    (hlen : nums.val.length = 4)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000) :
    ∀ r, valid_partition nums = ok r →
      (r = true ↔
        ((nums.val[0]'(by omega)).val = (nums.val[1]'(by omega)).val ∧
          (nums.val[2]'(by omega)).val = (nums.val[3]'(by omega)).val)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : nums.val.length = 4)
    (hrange : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000), ∀ r, valid_partition nums = ok r →
      (r = true ↔
        ((nums.val[0]'(by omega)).val = (nums.val[1]'(by omega)).val ∧
          (nums.val[2]'(by omega)).val = (nums.val[3]'(by omega)).val))) := by
  sorry

end AegisSpec.ValidPartition
