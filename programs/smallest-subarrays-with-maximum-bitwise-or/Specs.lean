import Aegis.SmallestSubarrays.Code.Funs

/-!
# Specifications of `Aegis.SmallestSubarrays.smallest_subarrays`

LeetCode problem `smallest-subarrays-with-maximum-bitwise-or`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SmallestSubarrays

  def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def orInt (a b : Int) : Int := ((a.toNat ||| b.toNat : Nat) : Int)

  def listOr : List Int → Int
    | [] => 0
    | x :: xs => orInt x (listOr xs)

  def blockOr (l : List Int) (start len : Nat) : Int := listOr ((l.drop start).take len)

  def suffixOr (l : List Int) (start : Nat) : Int := blockOr l start (l.length - start)

  def IsLeastGoodLen (l : List Int) (i : Nat) (L : Int) : Prop :=
    1 ≤ L ∧ L ≤ (l.length : Int) - (i : Int) ∧
      blockOr l i L.toNat = suffixOr l i ∧
        ∀ L' : Int, 1 ≤ L' → L' < L → blockOr l i L'.toNat ≠ suffixOr l i

  /-- Whenever the function returns a result r, len(r) = n and, for every index i with 0 <= i < n, the entry r[i] is the least integer L such that 1 <= L <= n - i and the bitwise OR of nums[i], nums[i+1], ..., nums[i+L-1] equals the bitwise OR of the whole suffix nums[i], nums[i+1], ..., nums[n-1]. The bitwise OR of a one-element block is just that element.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hval : ∀ (k : Nat) (hk : k < nums.val.length),
        0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000) :
      ∀ (r : alloc.vec.Vec Std.I64),
        Aegis.SmallestSubarrays.smallest_subarrays nums = ok r →
          r.val.length = nums.val.length ∧
            ∀ (i : Nat) (hi : i < r.val.length),
              IsLeastGoodLen (vals nums) i (r.val[i]).val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hval : ∀ (k : Nat) (hk : k < nums.val.length),
          0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000), ∀ (r : alloc.vec.Vec Std.I64),
          Aegis.SmallestSubarrays.smallest_subarrays nums = ok r →
            r.val.length = nums.val.length ∧
              ∀ (i : Nat) (hi : i < r.val.length),
                IsLeastGoodLen (vals nums) i (r.val[i]).val) := by
    sorry

  /-- Under these preconditions the function returns a result r; it does not fail, overflow, panic, or go out of bounds.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hval : ∀ (k : Nat) (hk : k < nums.val.length),
        0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.SmallestSubarrays.smallest_subarrays nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hval : ∀ (k : Nat) (hk : k < nums.val.length),
          0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000), ∃ r : alloc.vec.Vec Std.I64, Aegis.SmallestSubarrays.smallest_subarrays nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = n, i.e., the answer has exactly one entry for every starting index of nums.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hval : ∀ (k : Nat) (hk : k < nums.val.length),
        0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64)
      (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r) :
      r.val.length = nums.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hval : ∀ (k : Nat) (hk : k < nums.val.length),
          0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64)
        (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r), r.val.length = nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r of length n, for every i with 0 <= i < n, 1 <= r[i] <= n - i. In particular every answer is a non-empty subarray length and does not extend past the end of nums.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hval : ∀ (k : Nat) (hk : k < nums.val.length),
        0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64)
      (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r)
      (hrlen : r.val.length = nums.val.length) :
      ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (r.val[i]'(by omega)).val ∧
          (r.val[i]'(by omega)).val ≤ (nums.val.length : Int) - (i : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hval : ∀ (k : Nat) (hk : k < nums.val.length),
          0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64)
        (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r)
        (hrlen : r.val.length = nums.val.length), ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (r.val[i]'(by omega)).val ∧
            (r.val[i]'(by omega)).val ≤ (nums.val.length : Int) - (i : Int)) := by
    sorry

  /-- Whenever the function returns a result r of length n, for every i with 0 <= i < n, the bitwise OR of the contiguous block nums[i], nums[i+1], ..., nums[i + r[i] - 1] is equal to the bitwise OR of the suffix nums[i], nums[i+1], ..., nums[n-1].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hval : ∀ (k : Nat) (hk : k < nums.val.length),
        0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64)
      (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r)
      (hrlen : r.val.length = nums.val.length) :
      ∀ (i : Nat) (hi : i < nums.val.length),
        blockOr (vals nums) i (r.val[i]'(by omega)).val.toNat = suffixOr (vals nums) i := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hval : ∀ (k : Nat) (hk : k < nums.val.length),
          0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64)
        (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r)
        (hrlen : r.val.length = nums.val.length), ∀ (i : Nat) (hi : i < nums.val.length),
          blockOr (vals nums) i (r.val[i]'(by omega)).val.toNat = suffixOr (vals nums) i) := by
    sorry

  /-- Whenever the function returns a result r of length n, for every i with 0 <= i < n and every integer L with 1 <= L < r[i], the bitwise OR of nums[i], nums[i+1], ..., nums[i+L-1] is not equal to the bitwise OR of the suffix nums[i], nums[i+1], ..., nums[n-1].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hval : ∀ (k : Nat) (hk : k < nums.val.length),
        0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64)
      (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r)
      (hrlen : r.val.length = nums.val.length) :
      ∀ (i : Nat) (hi : i < nums.val.length) (L : Int),
        1 ≤ L → L < (r.val[i]'(by omega)).val →
          blockOr (vals nums) i L.toNat ≠ suffixOr (vals nums) i := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hval : ∀ (k : Nat) (hk : k < nums.val.length),
          0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64)
        (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r)
        (hrlen : r.val.length = nums.val.length), ∀ (i : Nat) (hi : i < nums.val.length) (L : Int),
          1 ≤ L → L < (r.val[i]'(by omega)).val →
            blockOr (vals nums) i L.toNat ≠ suffixOr (vals nums) i) := by
    sorry

  /-- Whenever the function returns a result r of length n, for every i with 0 <= i < n and every integer L with r[i] <= L <= n - i, the bitwise OR of nums[i], nums[i+1], ..., nums[i+L-1] is equal to the bitwise OR of the suffix nums[i], nums[i+1], ..., nums[n-1].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hval : ∀ (k : Nat) (hk : k < nums.val.length),
        0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64)
      (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r)
      (hrlen : r.val.length = nums.val.length) :
      ∀ (i : Nat) (hi : i < nums.val.length) (L : Int),
        (r.val[i]'(by omega)).val ≤ L → L ≤ (nums.val.length : Int) - (i : Int) →
          blockOr (vals nums) i L.toNat = suffixOr (vals nums) i := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hval : ∀ (k : Nat) (hk : k < nums.val.length),
          0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64)
        (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r)
        (hrlen : r.val.length = nums.val.length), ∀ (i : Nat) (hi : i < nums.val.length) (L : Int),
          (r.val[i]'(by omega)).val ≤ L → L ≤ (nums.val.length : Int) - (i : Int) →
            blockOr (vals nums) i L.toNat = suffixOr (vals nums) i) := by
    sorry

  /-- Whenever the function returns a result r of length n, r[n-1] = 1.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hval : ∀ (k : Nat) (hk : k < nums.val.length),
        0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64)
      (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r)
      (hrlen : r.val.length = nums.val.length) :
      (r.val[nums.val.length - 1]'(by omega)).val = 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hval : ∀ (k : Nat) (hk : k < nums.val.length),
          0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64)
        (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r)
        (hrlen : r.val.length = nums.val.length), (r.val[nums.val.length - 1]'(by omega)).val = 1) := by
    sorry

  /-- Whenever the function returns a result r of length n, for every i with 0 <= i < n, r[i] = 1 if and only if nums[i] is equal to the bitwise OR of the suffix nums[i], nums[i+1], ..., nums[n-1].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hval : ∀ (k : Nat) (hk : k < nums.val.length),
        0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64)
      (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r)
      (hrlen : r.val.length = nums.val.length) :
      ∀ (i : Nat) (hi : i < nums.val.length),
        ((r.val[i]'(by omega)).val = 1 ↔ (nums.val[i]).val = suffixOr (vals nums) i) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hval : ∀ (k : Nat) (hk : k < nums.val.length),
          0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64)
        (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r)
        (hrlen : r.val.length = nums.val.length), ∀ (i : Nat) (hi : i < nums.val.length),
          ((r.val[i]'(by omega)).val = 1 ↔ (nums.val[i]).val = suffixOr (vals nums) i)) := by
    sorry

  /-- Whenever the function returns a result r of length n, for every i with 0 <= i < n - 1, r[i] = n - i if and only if the bitwise OR of nums[i], nums[i+1], ..., nums[n-2] is different from the bitwise OR of the suffix nums[i], nums[i+1], ..., nums[n-1].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hval : ∀ (k : Nat) (hk : k < nums.val.length),
        0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64)
      (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r)
      (hrlen : r.val.length = nums.val.length) :
      ∀ (i : Nat) (hi : i < nums.val.length - 1),
        ((r.val[i]'(by omega)).val = (nums.val.length : Int) - (i : Int) ↔
          blockOr (vals nums) i (nums.val.length - 1 - i) ≠ suffixOr (vals nums) i) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hval : ∀ (k : Nat) (hk : k < nums.val.length),
          0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64)
        (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r)
        (hrlen : r.val.length = nums.val.length), ∀ (i : Nat) (hi : i < nums.val.length - 1),
          ((r.val[i]'(by omega)).val = (nums.val.length : Int) - (i : Int) ↔
            blockOr (vals nums) i (nums.val.length - 1 - i) ≠ suffixOr (vals nums) i)) := by
    sorry

  /-- Whenever the function returns a result r of length n, for every i with 0 <= i < n - 1 and nums[i] = 0, letting T be the bitwise OR of the suffix nums[i+1], nums[i+2], ..., nums[n-1], we have: if T = 0 then r[i] = 1, and if T != 0 then r[i] = r[i+1] + 1.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hval : ∀ (k : Nat) (hk : k < nums.val.length),
        0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64)
      (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r)
      (hrlen : r.val.length = nums.val.length) :
      ∀ (i : Nat) (hi : i < nums.val.length - 1),
        (nums.val[i]).val = 0 →
          (suffixOr (vals nums) (i + 1) = 0 → (r.val[i]'(by omega)).val = 1) ∧
            (suffixOr (vals nums) (i + 1) ≠ 0 →
              (r.val[i]'(by omega)).val = (r.val[i + 1]'(by omega)).val + 1) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hval : ∀ (k : Nat) (hk : k < nums.val.length),
          0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64)
        (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r)
        (hrlen : r.val.length = nums.val.length), ∀ (i : Nat) (hi : i < nums.val.length - 1),
          (nums.val[i]).val = 0 →
            (suffixOr (vals nums) (i + 1) = 0 → (r.val[i]'(by omega)).val = 1) ∧
              (suffixOr (vals nums) (i + 1) ≠ 0 →
                (r.val[i]'(by omega)).val = (r.val[i + 1]'(by omega)).val + 1)) := by
    sorry

  /-- Whenever the function returns a result r of length n, for every i with 0 <= i < n - 1, r[i] <= r[i+1] + 1.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
      (hval : ∀ (k : Nat) (hk : k < nums.val.length),
        0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64)
      (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r)
      (hrlen : r.val.length = nums.val.length) :
      ∀ (i : Nat) (hi : i < nums.val.length - 1),
        (r.val[i]'(by omega)).val ≤ (r.val[i + 1]'(by omega)).val + 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
        (hval : ∀ (k : Nat) (hk : k < nums.val.length),
          0 ≤ (nums.val[k]).val ∧ (nums.val[k]).val ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64)
        (hrun : Aegis.SmallestSubarrays.smallest_subarrays nums = ok r)
        (hrlen : r.val.length = nums.val.length), ∀ (i : Nat) (hi : i < nums.val.length - 1),
          (r.val[i]'(by omega)).val ≤ (r.val[i + 1]'(by omega)).val + 1) := by
    sorry

  end AegisSpec.SmallestSubarrays
