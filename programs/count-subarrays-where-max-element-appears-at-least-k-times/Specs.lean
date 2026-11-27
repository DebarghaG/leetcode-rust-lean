import Aegis.CountSubarrays.Code.Funs

/-!
# Specifications of `Aegis.CountSubarrays.count_subarrays`

LeetCode problem `count-subarrays-where-max-element-appears-at-least-k-times`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountSubarrays (count_subarrays)

  namespace AegisSpec.CountSubarrays

  def elems (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def maxOf (xs : List ℤ) : ℤ := xs.foldr max (xs.headD 0)

  def maxVal (nums : Slice Std.I64) : ℤ := maxOf (elems nums)

  def countOf (xs : List ℤ) (M : ℤ) : ℕ := xs.countP (fun x => x == M)

  def countBetween (xs : List ℤ) (M : ℤ) (L R : ℕ) : ℕ :=
    ((List.range (R + 1)).filter (fun i => decide (L ≤ i) && (xs[i]! == M))).length

  def countSubarraysWith (xs : List ℤ) (M : ℤ) (t : ℕ) : ℕ :=
    ((List.range xs.length).map (fun L =>
        ((List.range xs.length).filter
          (fun R => decide (L ≤ R ∧ t ≤ countBetween xs M L R))).length)).sum

  def firstIdx (xs : List ℤ) (M : ℤ) : ℕ :=
    ((List.range xs.length).find? (fun i => xs[i]! == M)).getD 0

  def lastIdx (xs : List ℤ) (M : ℤ) : ℕ :=
    (((List.range xs.length).filter (fun i => xs[i]! == M)).reverse).headD 0

  def positionsOf (xs : List ℤ) (M : ℤ) : List ℕ :=
    (List.range xs.length).filter (fun i => xs[i]! == M)

  def extPos (xs : List ℤ) (M : ℤ) (t : ℕ) : ℤ :=
    if t = 0 then -1
    else if t ≤ (positionsOf xs M).length then (((positionsOf xs M)[t - 1]! : ℕ) : ℤ)
    else (xs.length : ℤ)

  def windowWeight (xs : List ℤ) (M : ℤ) (a b : ℕ) : ℤ :=
    (extPos xs M (a + 1) - extPos xs M a) * (extPos xs M (b + 2) - extPos xs M (b + 1))

  def windowSum (xs : List ℤ) (M : ℤ) (t : ℕ) : ℤ :=
    ((List.range (positionsOf xs M).length).map (fun a =>
        (((List.range (positionsOf xs M).length).filter
            (fun b => decide (a ≤ b ∧ t ≤ b - a + 1))).map
          (fun b => windowWeight xs M a b)).sum)).sum

  def gapsFrom (M : ℤ) : ℕ → List ℤ → List ℕ
    | run, [] => if run = 0 then [] else [run]
    | run, x :: rest =>
      if x = M then (if run = 0 then [] else [run]) ++ gapsFrom M 0 rest
      else gapsFrom M (run + 1) rest

  def gapsOf (xs : List ℤ) (M : ℤ) : List ℕ := gapsFrom M 0 xs

  def gapsSum (xs : List ℤ) (M : ℤ) : ℕ := ((gapsOf xs M).map (fun g => g * (g + 1) / 2)).sum

  /-- Let M = max { nums[j] | 0 <= j < n }. The function returns a result res and res equals the number of pairs of integers (L,R) such that 0 <= L <= R < n and the number of indices i with L <= i <= R and nums[i] = M is at least k. In other words, res is the number of nonempty contiguous subarrays of nums in which the global maximum M occurs at least k times.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= 100000. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (h_nums : ∀ i, i < nums.val.length →
        1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000) :
      ∃ res : Std.I64, count_subarrays nums k = ok res ∧
        res.val = ((countSubarraysWith (elems nums) (maxVal nums) k.val.toNat : ℕ) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (h_nums : ∀ i, i < nums.val.length →
          1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000), ∃ res : Std.I64, count_subarrays nums k = ok res ∧
          res.val = ((countSubarraysWith (elems nums) (maxVal nums) k.val.toNat : ℕ) : ℤ)) := by
    sorry

  /-- Under the preconditions, the function returns a result; it does not fail, panic, overflow, or access an out-of-bounds index.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= 100000. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (h_nums : ∀ i, i < nums.val.length →
        1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000) :
      ∃ res : Std.I64, count_subarrays nums k = ok res := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (h_nums : ∀ i, i < nums.val.length →
          1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000), ∃ res : Std.I64, count_subarrays nums k = ok res) := by
    sorry

  /-- Let res be the returned result. Then 0 <= res <= n*(n+1)/2.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= 100000. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (h_nums : ∀ i, i < nums.val.length →
        1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000) :
      ∀ res : Std.I64, count_subarrays nums k = ok res →
        0 ≤ res.val ∧
          res.val ≤ (((nums.val.length * (nums.val.length + 1)) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (h_nums : ∀ i, i < nums.val.length →
          1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000), ∀ res : Std.I64, count_subarrays nums k = ok res →
          0 ≤ res.val ∧
            res.val ≤ (((nums.val.length * (nums.val.length + 1)) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- Let M = max { nums[j] | 0 <= j < n } and let c be the number of indices i with 0 <= i < n and nums[i] = M. Let first be the smallest index i with nums[i] = M and last be the largest index i with nums[i] = M. If c >= k, then the returned result res satisfies res >= (first+1)*(n-last).
    Preconditions: Let n = len(nums). n >= 1, n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= 100000. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (h_nums : ∀ i, i < nums.val.length →
        1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000) :
      ∀ res : Std.I64, count_subarrays nums k = ok res →
        k.val.toNat ≤ countOf (elems nums) (maxVal nums) →
          (((firstIdx (elems nums) (maxVal nums) + 1 : ℕ) : ℤ) *
              (((nums.val.length - lastIdx (elems nums) (maxVal nums) : ℕ)) : ℤ) ≤ res.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (h_nums : ∀ i, i < nums.val.length →
          1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000), ∀ res : Std.I64, count_subarrays nums k = ok res →
          k.val.toNat ≤ countOf (elems nums) (maxVal nums) →
            (((firstIdx (elems nums) (maxVal nums) + 1 : ℕ) : ℤ) *
                (((nums.val.length - lastIdx (elems nums) (maxVal nums) : ℕ)) : ℤ) ≤ res.val)) := by
    sorry

  /-- Suppose nums[i] = nums[0] for every i with 0 <= i < n. Let res be the returned result. If k <= n, then res = (n-k+1)*(n-k+2)/2; if k > n, then res = 0.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= 100000. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (h_nums : ∀ i, i < nums.val.length →
        1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
      (h_const : ∀ i, i < nums.val.length → (elems nums)[i]! = (elems nums)[0]!) :
      ∀ res : Std.I64, count_subarrays nums k = ok res →
        ((k.val ≤ (nums.val.length : ℤ) →
            res.val =
              (((nums.val.length - k.val.toNat + 1) * (nums.val.length - k.val.toNat + 2) /
                  2 : ℕ) : ℤ)) ∧
          ((nums.val.length : ℤ) < k.val → res.val = 0)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (h_nums : ∀ i, i < nums.val.length →
          1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
        (h_const : ∀ i, i < nums.val.length → (elems nums)[i]! = (elems nums)[0]!), ∀ res : Std.I64, count_subarrays nums k = ok res →
          ((k.val ≤ (nums.val.length : ℤ) →
              res.val =
                (((nums.val.length - k.val.toNat + 1) * (nums.val.length - k.val.toNat + 2) /
                    2 : ℕ) : ℤ)) ∧
            ((nums.val.length : ℤ) < k.val → res.val = 0))) := by
    sorry

  /-- Let rev be the sequence of length n with rev[i] = nums[n-1-i] for every i with 0 <= i < n, and let M' = max { rev[j] | 0 <= j < n }. The returned result res equals the number of pairs (L,R) with 0 <= L <= R < n such that the number of indices i with L <= i <= R and rev[i] = M' is at least k.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= 100000. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (h_nums : ∀ i, i < nums.val.length →
        1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000) :
      ∀ (rev : List ℤ), rev.length = nums.val.length →
        (∀ i, i < rev.length →
          rev[i]! = (elems nums)[nums.val.length - 1 - i]!) →
          ∀ res : Std.I64, count_subarrays nums k = ok res →
            res.val = ((countSubarraysWith rev (maxOf rev) k.val.toNat : ℕ) : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (h_nums : ∀ i, i < nums.val.length →
          1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000), ∀ (rev : List ℤ), rev.length = nums.val.length →
          (∀ i, i < rev.length →
            rev[i]! = (elems nums)[nums.val.length - 1 - i]!) →
            ∀ res : Std.I64, count_subarrays nums k = ok res →
              res.val = ((countSubarraysWith rev (maxOf rev) k.val.toNat : ℕ) : ℤ)) := by
    sorry

  /-- Let M = max { nums[j] | 0 <= j < n }. For every sequence nums2 of length n such that nums2[i] = M whenever nums[i] = M and 1 <= nums2[i] < M whenever nums[i] < M, the number of pairs (L,R) with 0 <= L <= R < n for which the number of indices i with L <= i <= R and nums2[i] = M is at least k is exactly the returned result res.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= 100000. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (h_nums : ∀ i, i < nums.val.length →
        1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000) :
      ∀ res : Std.I64, count_subarrays nums k = ok res →
        ∀ nums2 : List ℤ, nums2.length = nums.val.length →
          (∀ i, i < nums2.length →
            (elems nums)[i]! = maxVal nums → nums2[i]! = maxVal nums) →
            (∀ i, i < nums2.length →
              (elems nums)[i]! < maxVal nums → 1 ≤ nums2[i]! ∧ nums2[i]! < maxVal nums) →
              res.val = ((countSubarraysWith nums2 (maxVal nums) k.val.toNat : ℕ) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (h_nums : ∀ i, i < nums.val.length →
          1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000), ∀ res : Std.I64, count_subarrays nums k = ok res →
          ∀ nums2 : List ℤ, nums2.length = nums.val.length →
            (∀ i, i < nums2.length →
              (elems nums)[i]! = maxVal nums → nums2[i]! = maxVal nums) →
              (∀ i, i < nums2.length →
                (elems nums)[i]! < maxVal nums → 1 ≤ nums2[i]! ∧ nums2[i]! < maxVal nums) →
                res.val = ((countSubarraysWith nums2 (maxVal nums) k.val.toNat : ℕ) : ℤ)) := by
    sorry

  /-- Let M = max { nums[j] | 0 <= j < n }. For every positive integer t, let A(t) be the number of pairs (L,R) with 0 <= L <= R < n such that the number of indices i with L <= i <= R and nums[i] = M is at least t. Let res be the returned result. Then for every t with 1 <= t <= k, res <= A(t); and for every t with k <= t <= 100000, res >= A(t).
    Preconditions: Let n = len(nums). n >= 1, n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= 100000. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (h_nums : ∀ i, i < nums.val.length →
        1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000) :
      ∀ res : Std.I64, count_subarrays nums k = ok res →
        (∀ t : ℕ, 1 ≤ t → t ≤ k.val.toNat →
            res.val ≤ ((countSubarraysWith (elems nums) (maxVal nums) t : ℕ) : ℤ)) ∧
          (∀ t : ℕ, k.val.toNat ≤ t → t ≤ 100000 →
            ((countSubarraysWith (elems nums) (maxVal nums) t : ℕ) : ℤ) ≤ res.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (h_nums : ∀ i, i < nums.val.length →
          1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000), ∀ res : Std.I64, count_subarrays nums k = ok res →
          (∀ t : ℕ, 1 ≤ t → t ≤ k.val.toNat →
              res.val ≤ ((countSubarraysWith (elems nums) (maxVal nums) t : ℕ) : ℤ)) ∧
            (∀ t : ℕ, k.val.toNat ≤ t → t ≤ 100000 →
              ((countSubarraysWith (elems nums) (maxVal nums) t : ℕ) : ℤ) ≤ res.val)) := by
    sorry

  /-- Let M = max { nums[j] | 0 <= j < n }. Let p_0 < p_1 < ... < p_{c-1} be all indices with nums[p_j] = M. Set p_{-1} = -1 and p_c = n. The returned result res equals the sum, over all integer pairs (a,b) with 0 <= a <= b < c and b-a+1 >= k, of (p_a - p_{a-1}) * (p_{b+1} - p_b). If no such pair exists, the sum is 0.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= 100000. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (h_nums : ∀ i, i < nums.val.length →
        1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000) :
      ∀ res : Std.I64, count_subarrays nums k = ok res →
        res.val = windowSum (elems nums) (maxVal nums) k.val.toNat := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (h_nums : ∀ i, i < nums.val.length →
          1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000), ∀ res : Std.I64, count_subarrays nums k = ok res →
          res.val = windowSum (elems nums) (maxVal nums) k.val.toNat) := by
    sorry

  /-- Let M = max { nums[j] | 0 <= j < n } and let c be the number of indices i with 0 <= i < n and nums[i] = M. The returned result is positive if and only if c >= k. Equivalently, there exists a counted subarray if and only if the whole array contains M at least k times.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= 100000. -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (h_nums : ∀ i, i < nums.val.length →
        1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000) :
      ∀ res : Std.I64, count_subarrays nums k = ok res →
        (0 < res.val ↔ k.val.toNat ≤ countOf (elems nums) (maxVal nums)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (h_nums : ∀ i, i < nums.val.length →
          1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000), ∀ res : Std.I64, count_subarrays nums k = ok res →
          (0 < res.val ↔ k.val.toNat ≤ countOf (elems nums) (maxVal nums))) := by
    sorry

  /-- Assume k = 1. Let M = max { nums[j] | 0 <= j < n }. Let g_1, ..., g_s be the lengths of all maximal contiguous blocks of indices i with nums[i] != M, including blocks before the first occurrence of M, between consecutive occurrences of M, and after the last occurrence of M; zero-length blocks are omitted. Then the returned result res satisfies res = n*(n+1)/2 - sum_{j=1}^s g_j*(g_j+1)/2.
    Preconditions: Let n = len(nums). n >= 1, n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000; and 1 <= k <= 100000. -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (h_nums : ∀ i, i < nums.val.length →
        1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000) (hk_one : k.val = 1) :
      ∀ res : Std.I64, count_subarrays nums k = ok res →
        res.val = (((nums.val.length * (nums.val.length + 1)) / 2 : ℕ) : ℤ) -
          ((gapsSum (elems nums) (maxVal nums) : ℕ) : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (h_nums : ∀ i, i < nums.val.length →
          1 ≤ (elems nums)[i]! ∧ (elems nums)[i]! ≤ 1000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000) (hk_one : k.val = 1), ∀ res : Std.I64, count_subarrays nums k = ok res →
          res.val = (((nums.val.length * (nums.val.length + 1)) / 2 : ℕ) : ℤ) -
            ((gapsSum (elems nums) (maxVal nums) : ℕ) : ℤ)) := by
    sorry

  end AegisSpec.CountSubarrays
