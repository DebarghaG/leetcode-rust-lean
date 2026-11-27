import Aegis.MinimumSubarrayLength.Code.Funs

/-!
# Specifications of `Aegis.MinimumSubarrayLength.minimum_subarray_length`

LeetCode problem `shortest-subarray-with-or-at-least-k-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumSubarrayLength

  open Aegis.MinimumSubarrayLength (minimum_subarray_length)

  def orZ (a b : ℤ) : ℤ := ((a.toNat ||| b.toNat : ℕ) : ℤ)

  def listOr (xs : List ℤ) : ℤ := xs.foldl (fun acc x => orZ acc x) 0

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def orRange (nums : Slice Std.I64) (l u : ℕ) : ℤ := listOr (((vals nums).drop l).take (u - l))

  def totalOr (nums : Slice Std.I64) : ℤ := listOr (vals nums)

  def Special (nums : Slice Std.I64) (k : ℤ) (l u : ℕ) : Prop :=
    l < u ∧ u ≤ nums.val.length ∧ k ≤ orRange nums l u

  def HasSpecial (nums : Slice Std.I64) (k : ℤ) : Prop := ∃ l u : ℕ, Special nums k l u

  def span (l u : ℕ) : ℤ := (u : ℤ) - (l : ℤ)

  def Precondition (nums : Slice Std.I64) (k : Std.I64) : Prop :=
    1 ≤ nums.val.length ∧
      (∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000) ∧
      0 ≤ k.val ∧ k.val ≤ 1000000000

  /-- Let n = len(nums). Define a subarray [l,u), with 0 <= l < u <= n, to be special when the bitwise OR of nums[l], nums[l+1], ..., nums[u-1], interpreted as a non-negative integer, is at least k. The function returns a result r and: if at least one special subarray exists, then r is the minimum of u-l over all special subarrays [l,u); equivalently, r >= 1, some special subarray has length r, and no special subarray has length less than r. If no special subarray exists, then r = -1.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1,000,000,000; and 0 <= k <= 1,000,000,000. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000) :
      ∃ r : Std.I64,
        minimum_subarray_length nums k = ok r ∧
          (HasSpecial nums k.val →
            1 ≤ r.val ∧
              (∃ l u : ℕ, Special nums k.val l u ∧ span l u = r.val) ∧
              (∀ l u : ℕ, Special nums k.val l u → r.val ≤ span l u)) ∧
          (¬ HasSpecial nums k.val → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000), ∃ r : Std.I64,
          minimum_subarray_length nums k = ok r ∧
            (HasSpecial nums k.val →
              1 ≤ r.val ∧
                (∃ l u : ℕ, Special nums k.val l u ∧ span l u = r.val) ∧
                (∀ l u : ℕ, Special nums k.val l u → r.val ≤ span l u)) ∧
            (¬ HasSpecial nums k.val → r.val = -1)) := by
    sorry

  /-- The function returns a result r and does not fail: for every input satisfying the preconditions there is no panic, no out-of-bounds access, and no signed 64-bit overflow.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1,000,000,000; and 0 <= k <= 1,000,000,000. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000) :
      ∃ r : Std.I64, minimum_subarray_length nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000), ∃ r : Std.I64, minimum_subarray_length nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 1 <= r <= len(nums).
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1,000,000,000; and 0 <= k <= 1,000,000,000. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000) :
      ∀ r : Std.I64, minimum_subarray_length nums k = ok r →
        r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000), ∀ r : Std.I64, minimum_subarray_length nums k = ok r →
          r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ))) := by
    sorry

  /-- Whenever the function returns a result r, r != -1 if and only if there exist integers l and u with 0 <= l < u <= len(nums) such that the bitwise OR of nums[l], nums[l+1], ..., nums[u-1] is at least k.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1,000,000,000; and 0 <= k <= 1,000,000,000. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000) :
      ∀ r : Std.I64, minimum_subarray_length nums k = ok r →
        (r.val ≠ -1 ↔ HasSpecial nums k.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000), ∀ r : Std.I64, minimum_subarray_length nums k = ok r →
          (r.val ≠ -1 ↔ HasSpecial nums k.val)) := by
    sorry

  /-- Whenever the function returns a result r, let n = len(nums) and let O be the bitwise OR of all elements nums[0], nums[1], ..., nums[n-1]. Then r = -1 if and only if O < k; equivalently, r != -1 if and only if O >= k.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1,000,000,000; and 0 <= k <= 1,000,000,000. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000) :
      ∀ r : Std.I64, minimum_subarray_length nums k = ok r →
        (r.val = -1 ↔ totalOr nums < k.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000), ∀ r : Std.I64, minimum_subarray_length nums k = ok r →
          (r.val = -1 ↔ totalOr nums < k.val)) := by
    sorry

  /-- Whenever the function returns a result r with r >= 1, there exists an integer l such that 0 <= l, l+r <= len(nums), and the bitwise OR of nums[l], nums[l+1], ..., nums[l+r-1] is at least k.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1,000,000,000; and 0 <= k <= 1,000,000,000. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000) :
      ∀ r : Std.I64, minimum_subarray_length nums k = ok r → 1 ≤ r.val →
        ∃ l : ℕ, l + r.val.toNat ≤ nums.val.length ∧
          k.val ≤ orRange nums l (l + r.val.toNat) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000), ∀ r : Std.I64, minimum_subarray_length nums k = ok r → 1 ≤ r.val →
          ∃ l : ℕ, l + r.val.toNat ≤ nums.val.length ∧
            k.val ≤ orRange nums l (l + r.val.toNat)) := by
    sorry

  /-- Whenever the function returns a result r with r >= 1, for every pair of integers l,u with 0 <= l < u <= len(nums), if the bitwise OR of nums[l], nums[l+1], ..., nums[u-1] is at least k, then u-l >= r.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1,000,000,000; and 0 <= k <= 1,000,000,000. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000) :
      ∀ r : Std.I64, minimum_subarray_length nums k = ok r → 1 ≤ r.val →
        ∀ l u : ℕ, Special nums k.val l u → r.val ≤ span l u := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000), ∀ r : Std.I64, minimum_subarray_length nums k = ok r → 1 ≤ r.val →
          ∀ l u : ℕ, Special nums k.val l u → r.val ≤ span l u) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if there exists an index i with 0 <= i < len(nums) and nums[i] >= k.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1,000,000,000; and 0 <= k <= 1,000,000,000. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000) :
      ∀ r : Std.I64, minimum_subarray_length nums k = ok r →
        (r.val = 1 ↔ ∃ (i : ℕ) (hi : i < nums.val.length), k.val ≤ (nums.val[i]'hi).val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000), ∀ r : Std.I64, minimum_subarray_length nums k = ok r →
          (r.val = 1 ↔ ∃ (i : ℕ) (hi : i < nums.val.length), k.val ≤ (nums.val[i]'hi).val)) := by
    sorry

  /-- Whenever the function returns a result r with r > 1, for every index i with 0 <= i < len(nums), nums[i] < k.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1,000,000,000; and 0 <= k <= 1,000,000,000. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000) :
      ∀ r : Std.I64, minimum_subarray_length nums k = ok r → 1 < r.val →
        ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]'hi).val < k.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000), ∀ r : Std.I64, minimum_subarray_length nums k = ok r → 1 < r.val →
          ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]'hi).val < k.val) := by
    sorry

  /-- Whenever the function returns a result r with r = -1, for every index i with 0 <= i < len(nums), nums[i] < k.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1,000,000,000; and 0 <= k <= 1,000,000,000. -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000) :
      ∀ r : Std.I64, minimum_subarray_length nums k = ok r → r.val = -1 →
        ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]'hi).val < k.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000), ∀ r : Std.I64, minimum_subarray_length nums k = ok r → r.val = -1 →
          ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]'hi).val < k.val) := by
    sorry

  /-- Whenever the function returns a result r and k = 0, r = 1.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1,000,000,000; and 0 <= k <= 1,000,000,000. -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000) :
      ∀ r : Std.I64, minimum_subarray_length nums k = ok r → k.val = 0 → r.val = 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000), ∀ r : Std.I64, minimum_subarray_length nums k = ok r → k.val = 0 → r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, if k > 0 and nums[i] = 0 for every index i with 0 <= i < len(nums), then r = -1.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1,000,000,000; and 0 <= k <= 1,000,000,000. -/
  theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000) :
      ∀ r : Std.I64, minimum_subarray_length nums k = ok r → 0 < k.val →
        (∀ x ∈ nums.val, x.val = 0) → r.val = -1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000), ∀ r : Std.I64, minimum_subarray_length nums k = ok r → 0 < k.val →
          (∀ x ∈ nums.val, x.val = 0) → r.val = -1) := by
    sorry

  /-- Whenever the function returns a result r and len(nums) = 1, r = 1 if nums[0] >= k, and r = -1 otherwise.
    Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1,000,000,000; and 0 <= k <= 1,000,000,000. -/
  theorem spec_13 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000) :
      ∀ r : Std.I64, minimum_subarray_length nums k = ok r → nums.val.length = 1 →
        (k.val ≤ (nums.val[0]'(by omega)).val → r.val = 1) ∧
          ((nums.val[0]'(by omega)).val < k.val → r.val = -1) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_low : 0 ≤ k.val) (hk_high : k.val ≤ 1000000000), ∀ r : Std.I64, minimum_subarray_length nums k = ok r → nums.val.length = 1 →
          (k.val ≤ (nums.val[0]'(by omega)).val → r.val = 1) ∧
            ((nums.val[0]'(by omega)).val < k.val → r.val = -1)) := by
    sorry

  end AegisSpec.MinimumSubarrayLength
