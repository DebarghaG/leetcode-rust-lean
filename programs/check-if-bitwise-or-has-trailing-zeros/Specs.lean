import Aegis.HasTrailingZeros.Code.Funs

/-!
# Specifications of `Aegis.HasTrailingZeros.has_trailing_zeros`

LeetCode problem `check-if-bitwise-or-has-trailing-zeros`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.HasTrailingZeros

  def item (nums : Slice Std.I64) (i : Nat) : Int :=
    match nums.val[i]? with
    | some x => x.val
    | none => 0

  def EvenInt (v : Int) : Prop := ∃ k : Int, v = 2 * k

  def OddInt (v : Int) : Prop := ∃ k : Int, v = 2 * k + 1

  def bor (a b : Int) : Int := ((BitVec.ofInt 64 a) ||| (BitVec.ofInt 64 b)).toInt

  def orOver (f : Nat → Int) : List Nat → Int
    | [] => 0
    | i :: is => bor (f i) (orOver f is)

  def swapList (l : List Std.I64) (i j : Nat) : List Std.I64 :=
    (l.set i (l[j]!)).set j (l[i]!)

  /-- The function returns a result r, and r = true if and only if there exists a set S of indices such that S is a subset of {0, 1, ..., len(nums)-1}, |S| >= 2, and the bitwise OR of nums[k] over all k in S is even (equivalently, has at least one trailing zero in binary).
    Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ item nums i ∧ item nums i ≤ 100) :
      ∃ r, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r ∧
        (r = true ↔ ∃ S : List Nat, (∀ k ∈ S, k < nums.val.length) ∧ S.Nodup ∧
          2 ≤ S.length ∧ EvenInt (orOver (item nums) S)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ item nums i ∧ item nums i ≤ 100), ∃ r, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r ∧
          (r = true ↔ ∃ S : List Nat, (∀ k ∈ S, k < nums.val.length) ∧ S.Nodup ∧
            2 ≤ S.length ∧ EvenInt (orOver (item nums) S))) := by
    sorry

  /-- For every valid nums, the function returns a result r and does not fail (no panic, no out-of-bounds access, and no arithmetic or bitwise-operation overflow).
    Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ item nums i ∧ item nums i ≤ 100) :
      ∃ r, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ item nums i ∧ item nums i ≤ 100), ∃ r, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, if there exist distinct indices i and j with 0 <= i < j < len(nums) such that nums[i] is even and nums[j] is even, then r = true.
    Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ item nums i ∧ item nums i ≤ 100) :
      ∀ r, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r →
        (∃ i j, i < j ∧ j < nums.val.length ∧ EvenInt (item nums i) ∧
          EvenInt (item nums j)) →
        r = true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ item nums i ∧ item nums i ≤ 100), ∀ r, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r →
          (∃ i j, i < j ∧ j < nums.val.length ∧ EvenInt (item nums i) ∧
            EvenInt (item nums j)) →
          r = true) := by
    sorry

  /-- Whenever the function returns a result r, if r = true, then there exist distinct indices i and j with 0 <= i < j < len(nums) such that nums[i] is even and nums[j] is even.
    Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ item nums i ∧ item nums i ≤ 100) :
      ∀ r, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r → r = true →
        ∃ i j, i < j ∧ j < nums.val.length ∧ EvenInt (item nums i) ∧
          EvenInt (item nums j) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ item nums i ∧ item nums i ≤ 100), ∀ r, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r → r = true →
          ∃ i j, i < j ∧ j < nums.val.length ∧ EvenInt (item nums i) ∧
            EvenInt (item nums j)) := by
    sorry

  /-- For every valid nums with len(nums) = 2, whenever the function returns a result r, r = true if and only if both nums[0] and nums[1] are even.
    Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ item nums i ∧ item nums i ≤ 100)
      (hlen2 : nums.val.length = 2) :
      ∀ r, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r →
        (r = true ↔ EvenInt (item nums 0) ∧ EvenInt (item nums 1)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ item nums i ∧ item nums i ≤ 100)
        (hlen2 : nums.val.length = 2), ∀ r, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r →
          (r = true ↔ EvenInt (item nums 0) ∧ EvenInt (item nums 1))) := by
    sorry

  /-- For every valid nums such that nums[i] is odd for every i with 0 <= i < len(nums), whenever the function returns a result r, r = false.
    Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ item nums i ∧ item nums i ≤ 100)
      (hodd : ∀ i, i < nums.val.length → OddInt (item nums i)) :
      ∀ r, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r → r = false := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ item nums i ∧ item nums i ≤ 100)
        (hodd : ∀ i, i < nums.val.length → OddInt (item nums i)), ∀ r, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r → r = false) := by
    sorry

  /-- For every such nums and nums2 satisfying, for every i with 0 <= i < len(nums), nums[i] is even if and only if nums2[i] is even, whenever has_trailing_zeros(nums) returns r and has_trailing_zeros(nums2) returns r2, we have r = r2.
    Preconditions: nums and nums2 are slices of 64-bit signed integers, each has length between 2 and 100 inclusive, each entry of each is between 1 and 100 inclusive, and len(nums) = len(nums2). -/
  theorem spec_7 (nums nums2 : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ item nums i ∧ item nums i ≤ 100)
      (hlen2 : 2 ≤ nums2.val.length) (hlen2' : nums2.val.length ≤ 100)
      (hrange2 : ∀ i, i < nums2.val.length → 1 ≤ item nums2 i ∧ item nums2 i ≤ 100)
      (hlen_eq : nums.val.length = nums2.val.length)
      (heven : ∀ i, i < nums.val.length → (EvenInt (item nums i) ↔ EvenInt (item nums2 i))) :
      ∀ r r2, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r →
        Aegis.HasTrailingZeros.has_trailing_zeros nums2 = ok r2 → r = r2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ item nums i ∧ item nums i ≤ 100)
        (hlen2 : 2 ≤ nums2.val.length) (hlen2' : nums2.val.length ≤ 100)
        (hrange2 : ∀ i, i < nums2.val.length → 1 ≤ item nums2 i ∧ item nums2 i ≤ 100)
        (hlen_eq : nums.val.length = nums2.val.length)
        (heven : ∀ i, i < nums.val.length → (EvenInt (item nums i) ↔ EvenInt (item nums2 i))), ∀ r r2, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r →
          Aegis.HasTrailingZeros.has_trailing_zeros nums2 = ok r2 → r = r2) := by
    sorry

  /-- For every valid nums and every pair of indices i and j with 0 <= i < j < len(nums), let nums_swapped be the slice obtained from nums by exchanging the entries at positions i and j. Whenever has_trailing_zeros(nums) returns r and has_trailing_zeros(nums_swapped) returns r_swapped, we have r = r_swapped.
    Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_8 (nums nums_swapped : Slice Std.I64) (i j : Nat)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ k, k < nums.val.length → 1 ≤ item nums k ∧ item nums k ≤ 100)
      (hij : i < j) (hj : j < nums.val.length)
      (hswap : nums_swapped.val = swapList nums.val i j) :
      ∀ r r_swapped, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r →
        Aegis.HasTrailingZeros.has_trailing_zeros nums_swapped = ok r_swapped →
        r = r_swapped := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums_swapped : Slice Std.I64) (i j : Nat)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ k, k < nums.val.length → 1 ≤ item nums k ∧ item nums k ≤ 100)
        (hij : i < j) (hj : j < nums.val.length)
        (hswap : nums_swapped.val = swapList nums.val i j), ∀ r r_swapped, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r →
          Aegis.HasTrailingZeros.has_trailing_zeros nums_swapped = ok r_swapped →
          r = r_swapped) := by
    sorry

  /-- Let nums_appended be the slice obtained by appending x to nums, so len(nums_appended) = len(nums)+1, nums_appended[k] = nums[k] for 0 <= k < len(nums), and nums_appended[len(nums)] = x. Whenever has_trailing_zeros(nums) returns r and has_trailing_zeros(nums_appended) returns r_appended, we have r = r_appended.
    Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 99, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and x is an odd integer with 1 <= x <= 100. -/
  theorem spec_9 (nums nums_appended : Slice Std.I64) (x : Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 99)
      (hrange : ∀ k, k < nums.val.length → 1 ≤ item nums k ∧ item nums k ≤ 100)
      (hx_odd : OddInt x.val) (hx1 : 1 ≤ x.val) (hx100 : x.val ≤ 100)
      (happ : nums_appended.val = nums.val ++ [x]) :
      ∀ r r_appended, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r →
        Aegis.HasTrailingZeros.has_trailing_zeros nums_appended = ok r_appended →
        r = r_appended := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums_appended : Slice Std.I64) (x : Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 99)
        (hrange : ∀ k, k < nums.val.length → 1 ≤ item nums k ∧ item nums k ≤ 100)
        (hx_odd : OddInt x.val) (hx1 : 1 ≤ x.val) (hx100 : x.val ≤ 100)
        (happ : nums_appended.val = nums.val ++ [x]), ∀ r r_appended, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r →
          Aegis.HasTrailingZeros.has_trailing_zeros nums_appended = ok r_appended →
          r = r_appended) := by
    sorry

  /-- Let nums_appended be the slice obtained by appending x to nums. Whenever has_trailing_zeros(nums) returns true and has_trailing_zeros(nums_appended) returns r_appended, we have r_appended = true.
    Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 99, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and x is an integer with 1 <= x <= 100. -/
  theorem spec_10 (nums nums_appended : Slice Std.I64) (x : Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 99)
      (hrange : ∀ k, k < nums.val.length → 1 ≤ item nums k ∧ item nums k ≤ 100)
      (hx1 : 1 ≤ x.val) (hx100 : x.val ≤ 100)
      (happ : nums_appended.val = nums.val ++ [x]) :
      ∀ r_appended, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok true →
        Aegis.HasTrailingZeros.has_trailing_zeros nums_appended = ok r_appended →
        r_appended = true := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums_appended : Slice Std.I64) (x : Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 99)
        (hrange : ∀ k, k < nums.val.length → 1 ≤ item nums k ∧ item nums k ≤ 100)
        (hx1 : 1 ≤ x.val) (hx100 : x.val ≤ 100)
        (happ : nums_appended.val = nums.val ++ [x]), ∀ r_appended, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok true →
          Aegis.HasTrailingZeros.has_trailing_zeros nums_appended = ok r_appended →
          r_appended = true) := by
    sorry

  /-- Let nums_appended be the slice obtained by appending x to nums. Whenever has_trailing_zeros(nums_appended) returns r_appended, we have r_appended = true.
    Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 99, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100, exactly one index i has nums[i] even, and x is an even integer with 1 <= x <= 100. -/
  theorem spec_11 (nums nums_appended : Slice Std.I64) (x : Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 99)
      (hrange : ∀ k, k < nums.val.length → 1 ≤ item nums k ∧ item nums k ≤ 100)
      (hexactly : ∃ i, i < nums.val.length ∧ EvenInt (item nums i) ∧
        ∀ k, k < nums.val.length → EvenInt (item nums k) → k = i)
      (hx_even : EvenInt x.val) (hx1 : 1 ≤ x.val) (hx100 : x.val ≤ 100)
      (happ : nums_appended.val = nums.val ++ [x]) :
      ∀ r_appended, Aegis.HasTrailingZeros.has_trailing_zeros nums_appended = ok r_appended →
        r_appended = true := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums_appended : Slice Std.I64) (x : Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 99)
        (hrange : ∀ k, k < nums.val.length → 1 ≤ item nums k ∧ item nums k ≤ 100)
        (hexactly : ∃ i, i < nums.val.length ∧ EvenInt (item nums i) ∧
          ∀ k, k < nums.val.length → EvenInt (item nums k) → k = i)
        (hx_even : EvenInt x.val) (hx1 : 1 ≤ x.val) (hx100 : x.val ≤ 100)
        (happ : nums_appended.val = nums.val ++ [x]), ∀ r_appended, Aegis.HasTrailingZeros.has_trailing_zeros nums_appended = ok r_appended →
          r_appended = true) := by
    sorry

  /-- Whenever has_trailing_zeros(nums) returns false, for every pair of distinct indices i and j with 0 <= i < j < len(nums), the bitwise OR of nums[i] and nums[j] is odd (equivalently, has no trailing zero).
    Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ item nums i ∧ item nums i ≤ 100) :
      ∀ r, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r → r = false →
        ∀ i j, i < j → j < nums.val.length →
          OddInt (bor (item nums i) (item nums j)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ item nums i ∧ item nums i ≤ 100), ∀ r, Aegis.HasTrailingZeros.has_trailing_zeros nums = ok r → r = false →
          ∀ i j, i < j → j < nums.val.length →
            OddInt (bor (item nums i) (item nums j))) := by
    sorry

  end AegisSpec.HasTrailingZeros
