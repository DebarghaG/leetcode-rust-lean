import Aegis.MaxSumMinProduct.Code.Funs

/-!
# Specifications of `Aegis.MaxSumMinProduct.max_sum_min_product`

LeetCode problem `maximum-subarray-min-product`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxSumMinProduct

  def p : Int := 1000000007

  def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def numAt (nums : Slice Std.I64) (i : Nat) : Int := (vals nums).getD i 0

  def mn (l : List Int) (i j : Nat) : Int := ((l.drop i).take (j + 1 - i)).min?.getD 0

  def sm (l : List Int) (i j : Nat) : Int := ((l.drop i).take (j + 1 - i)).sum

  def mp (l : List Int) (i j : Nat) : Int := mn l i j * sm l i j

  def minProducts (l : List Int) : List Int :=
    ((List.range l.length).map
        (fun i => (List.range (l.length - i)).map (fun k => mp l i (i + k)))).flatten

  def maxMinProduct (l : List Int) : Int := (minProducts l).max?.getD 0

  def maxElem (l : List Int) : Int := l.max?.getD 0

  /-- Let p = 10^9 + 7. For 0 <= i <= j < n let mn(i,j) = min{ nums[k] : i <= k <= j }, sm(i,j) = sum_{k=i}^{j} nums[k], mp(i,j) = mn(i,j) * sm(i,j), and M = max{ mp(i,j) : 0 <= i <= j < n }. The function returns a result r such that 0 <= r < p and r is congruent to M modulo p; equivalently r = M mod p, the unique integer in [0, p-1] congruent to M.
    Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 10000000. It is guaranteed that the maximum min-product M (as defined in the statement) is at most 2^63 - 1, so it fits in a 64-bit signed integer. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hlen' : nums.val.length ≤ 100000)
      (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
      (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1) :
      ∃ r, _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r ∧
        0 ≤ r.val ∧ r.val < p ∧ r.val = maxMinProduct (vals nums) % p := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hlen' : nums.val.length ≤ 100000)
        (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
        (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1), ∃ r, _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r ∧
          0 ≤ r.val ∧ r.val < p ∧ r.val = maxMinProduct (vals nums) % p) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it never fails (no 64-bit signed arithmetic overflow, no out-of-bounds index access, no panic).
    Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 10000000. It is guaranteed that the maximum min-product M is at most 2^63 - 1. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hlen' : nums.val.length ≤ 100000)
      (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
      (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1) :
      ∃ r, _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hlen' : nums.val.length ≤ 100000)
        (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
        (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1), ∃ r, _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r) := by
    sorry

  /-- If n = 1 then r = (nums[0] * nums[0]) mod (10^9 + 7); that is, 0 <= r < 10^9+7 and r is congruent to nums[0]^2 modulo 10^9+7.
    Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 10000000. It is guaranteed that the maximum min-product M is at most 2^63 - 1. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen1 : nums.val.length = 1)
      (hlen : 1 ≤ nums.val.length)
      (hlen' : nums.val.length ≤ 100000)
      (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
      (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1) :
      ∃ r, _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r ∧
        0 ≤ r.val ∧ r.val < p ∧ r.val = (numAt nums 0 * numAt nums 0) % p := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen1 : nums.val.length = 1)
        (hlen : 1 ≤ nums.val.length)
        (hlen' : nums.val.length ≤ 100000)
        (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
        (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1), ∃ r, _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r ∧
          0 ≤ r.val ∧ r.val < p ∧ r.val = (numAt nums 0 * numAt nums 0) % p) := by
    sorry

  /-- If n = 2 then the maximum min-product is M = max(nums[0]*nums[0], nums[1]*nums[1], min(nums[0], nums[1]) * (nums[0] + nums[1])) and r = M mod (10^9 + 7).
    Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 10000000. It is guaranteed that the maximum min-product M is at most 2^63 - 1. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen2 : nums.val.length = 2)
      (hlen : 1 ≤ nums.val.length)
      (hlen' : nums.val.length ≤ 100000)
      (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
      (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1) :
      ∃ r, _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r ∧
        maxMinProduct (vals nums) =
          max (numAt nums 0 * numAt nums 0)
            (max (numAt nums 1 * numAt nums 1)
              (min (numAt nums 0) (numAt nums 1) * (numAt nums 0 + numAt nums 1))) ∧
        r.val = maxMinProduct (vals nums) % p := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen2 : nums.val.length = 2)
        (hlen : 1 ≤ nums.val.length)
        (hlen' : nums.val.length ≤ 100000)
        (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
        (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1), ∃ r, _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r ∧
          maxMinProduct (vals nums) =
            max (numAt nums 0 * numAt nums 0)
              (max (numAt nums 1 * numAt nums 1)
                (min (numAt nums 0) (numAt nums 1) * (numAt nums 0 + numAt nums 1))) ∧
          r.val = maxMinProduct (vals nums) % p) := by
    sorry

  /-- If nums[0] = nums[1] = ... = nums[n-1] = c, then M = c * c * n and r = (c * c * n) mod (10^9 + 7).
    Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 10000000. It is guaranteed that the maximum min-product M is at most 2^63 - 1. -/
  theorem spec_5 (nums : Slice Std.I64) (c : Int)
      (hall : ∀ x ∈ vals nums, x = c)
      (hlen : 1 ≤ nums.val.length)
      (hlen' : nums.val.length ≤ 100000)
      (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
      (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1) :
      ∃ r, _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r ∧
        maxMinProduct (vals nums) = c * c * (nums.val.length : Int) ∧
        r.val = (c * c * (nums.val.length : Int)) % p := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (c : Int)
        (hall : ∀ x ∈ vals nums, x = c)
        (hlen : 1 ≤ nums.val.length)
        (hlen' : nums.val.length ≤ 100000)
        (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
        (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1), ∃ r, _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r ∧
          maxMinProduct (vals nums) = c * c * (nums.val.length : Int) ∧
          r.val = (c * c * (nums.val.length : Int)) % p) := by
    sorry

  /-- There exist indices i, j with 0 <= i <= j < n such that mp(i,j) = M and r = mp(i,j) mod (10^9 + 7), where mn, sm, mp, and M are as defined in spec_1.
    Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 10000000. It is guaranteed that the maximum min-product M is at most 2^63 - 1. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hlen' : nums.val.length ≤ 100000)
      (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
      (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1) :
      ∃ i j r, i ≤ j ∧ j < nums.val.length ∧
        mp (vals nums) i j = maxMinProduct (vals nums) ∧
        _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r ∧
        r.val = mp (vals nums) i j % p := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hlen' : nums.val.length ≤ 100000)
        (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
        (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1), ∃ i j r, i ≤ j ∧ j < nums.val.length ∧
          mp (vals nums) i j = maxMinProduct (vals nums) ∧
          _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r ∧
          r.val = mp (vals nums) i j % p) := by
    sorry

  /-- For every 0 <= i <= j < n, mp(i,j) <= M, where M is the maximum min-product and r = M mod (10^9 + 7). Equivalently, no non-empty contiguous subarray has min-product strictly larger than the maximum whose residue is returned.
    Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 10000000. It is guaranteed that the maximum min-product M is at most 2^63 - 1. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hlen' : nums.val.length ≤ 100000)
      (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
      (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1) :
      (∃ r, _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r ∧
          r.val = maxMinProduct (vals nums) % p) ∧
        (∀ i j, i ≤ j → j < nums.val.length →
          mp (vals nums) i j ≤ maxMinProduct (vals nums)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hlen' : nums.val.length ≤ 100000)
        (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
        (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1), (∃ r, _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r ∧
            r.val = maxMinProduct (vals nums) % p) ∧
          (∀ i j, i ≤ j → j < nums.val.length →
            mp (vals nums) i j ≤ maxMinProduct (vals nums))) := by
    sorry

  /-- If M < 10^9 + 7 then r = M, i.e., the returned value equals the unreduced maximum min-product.
    Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 10000000. It is guaranteed that the maximum min-product M is at most 2^63 - 1. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hMlt : maxMinProduct (vals nums) < p)
      (hlen : 1 ≤ nums.val.length)
      (hlen' : nums.val.length ≤ 100000)
      (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
      (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1) :
      ∃ r, _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r ∧
        r.val = maxMinProduct (vals nums) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hMlt : maxMinProduct (vals nums) < p)
        (hlen : 1 ≤ nums.val.length)
        (hlen' : nums.val.length ≤ 100000)
        (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
        (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1), ∃ r, _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r ∧
          r.val = maxMinProduct (vals nums)) := by
    sorry

  /-- 0 <= r <= M, where M is the maximum min-product.
    Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 10000000. It is guaranteed that the maximum min-product M is at most 2^63 - 1. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hlen' : nums.val.length ≤ 100000)
      (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
      (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1) :
      ∃ r, _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r ∧
        0 ≤ r.val ∧ r.val ≤ maxMinProduct (vals nums) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hlen' : nums.val.length ≤ 100000)
        (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
        (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1), ∃ r, _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r ∧
          0 ≤ r.val ∧ r.val ≤ maxMinProduct (vals nums)) := by
    sorry

  /-- r = 0 if and only if M is divisible by 10^9 + 7; if M is not divisible by 10^9 + 7 then 1 <= r < 10^9 + 7.
    Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 10000000. It is guaranteed that the maximum min-product M is at most 2^63 - 1. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlen : 1 ≤ nums.val.length)
      (hlen' : nums.val.length ≤ 100000)
      (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
      (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1) :
      ∃ r, _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r ∧
        (r.val = 0 ↔ p ∣ maxMinProduct (vals nums)) ∧
        (¬ p ∣ maxMinProduct (vals nums) → 1 ≤ r.val ∧ r.val < p) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 1 ≤ nums.val.length)
        (hlen' : nums.val.length ≤ 100000)
        (hpos : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10000000)
        (hM : maxMinProduct (vals nums) ≤ 2 ^ 63 - 1), ∃ r, _root_.Aegis.MaxSumMinProduct.max_sum_min_product nums = ok r ∧
          (r.val = 0 ↔ p ∣ maxMinProduct (vals nums)) ∧
          (¬ p ∣ maxMinProduct (vals nums) → 1 ≤ r.val ∧ r.val < p)) := by
    sorry

  end AegisSpec.MaxSumMinProduct
