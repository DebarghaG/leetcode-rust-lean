import Aegis.SplitArray.Code.Funs

/-!
# Specifications of `Aegis.SplitArray.split_array`

LeetCode problem `split-array-largest-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SplitArray

def contents (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def len (nums : Slice Std.I64) : ℕ := (contents nums).length

def entry (nums : Slice Std.I64) (i : ℕ) : ℤ := (contents nums).getD i 0

def total (l : List ℤ) : ℤ := l.sum

def prefixSum (l : List ℤ) (p : ℕ) : ℤ := (l.take p).sum

def segSum (l : List ℤ) (a b : ℕ) : ℤ := ((l.drop a).take (b - a)).sum

def IsSplit (n k : ℕ) (p : ℕ → ℕ) : Prop :=
  p 0 = 0 ∧ p k = n ∧ ∀ j, j < k → p j < p (j + 1)

def segSums (l : List ℤ) (k : ℕ) (p : ℕ → ℕ) : List ℤ :=
  (List.range k).map (fun j => segSum l (p j) (p (j + 1)))

def maxSeg (l : List ℤ) (k : ℕ) (p : ℕ → ℕ) : ℤ :=
  if h : k = 0 then 0
  else
    (Finset.range k).sup' (Finset.nonempty_range_iff.mpr h)
      (fun j => segSum l (p j) (p (j + 1)))

def maxElem (l : List ℤ) : ℤ :=
  if h : l.length ≠ 0 then
    (Finset.range l.length).sup' (Finset.nonempty_range_iff.mpr h) (fun i => l.getD i 0)
  else 0

def bestTwoSplit (l : List ℤ) : ℤ :=
  if h : (Finset.Icc 1 (l.length - 1)).Nonempty then
    (Finset.Icc 1 (l.length - 1)).inf' h
      (fun p => max (prefixSum l p) (total l - prefixSum l p))
  else 0

def IsOptimalSplit (l : List ℤ) (k : ℕ) (r : ℤ) : Prop :=
  (∃ p, IsSplit l.length k p ∧ (∀ j, j < k → segSum l (p j) (p (j + 1)) ≤ r) ∧
      ∃ j, j < k ∧ segSum l (p j) (p (j + 1)) = r) ∧
    (∀ p, IsSplit l.length k p → r ≤ maxSeg l k p)

/-- The function returns a result r, and r is exactly the minimum possible largest segment sum for a split of nums into k non-empty contiguous subarrays. More precisely: (a) there exist integer indices 0 = p_0 < p_1 < ... < p_k = len(nums) such that, for every j with 0 <= j < k, the segment sum S_j = nums[p_j] + nums[p_j+1] + ... + nums[p_{j+1}-1] satisfies S_j <= r, and at least one such S_j equals r; and (b) for every choice of integer indices 0 = q_0 < q_1 < ... < q_k = len(nums), if T_j = nums[q_j] + ... + nums[q_{j+1}-1] for 0 <= j < k, then max_{0<=j<k} T_j >= r.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 1 <= k <= min(50, len(nums)). -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)) :
    ∃ r, Aegis.SplitArray.split_array nums k = ok r ∧
      IsOptimalSplit (contents nums) k.val.toNat r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)), ∃ r, Aegis.SplitArray.split_array nums k = ok r ∧
      IsOptimalSplit (contents nums) k.val.toNat r.val) := by
  sorry

/-- The function returns a result r and does not fail: for every input satisfying the preconditions, there is no arithmetic overflow, no out-of-bounds indexing, and no panic.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 1 <= k <= min(50, len(nums)). -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)) :
    ∃ r, Aegis.SplitArray.split_array nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)), ∃ r, Aegis.SplitArray.split_array nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r >= nums[i].
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 1 <= k <= min(50, len(nums)). -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)) :
    ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      ∀ i, i < len nums → entry nums i ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)), ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      ∀ i, i < len nums → entry nums i ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if total = sum_{i=0}^{len(nums)-1} nums[i], then k * r >= total. Equivalently, r is at least the smallest integer t such that k * t >= total (the ceiling of total/k).
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 1 <= k <= min(50, len(nums)). -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)) :
    ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      total (contents nums) ≤ k.val * r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)), ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      total (contents nums) ≤ k.val * r.val) := by
  sorry

/-- Whenever the function returns a result r, if total = sum_{i=0}^{len(nums)-1} nums[i], then r <= total.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 1 <= k <= min(50, len(nums)). -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)) :
    ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      r.val ≤ total (contents nums) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)), ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      r.val ≤ total (contents nums)) := by
  sorry

/-- Whenever the function returns a result r, there exist integer indices 0 = p_0 < p_1 < ... < p_k = len(nums) such that every segment sum nums[p_j] + ... + nums[p_{j+1}-1] (for 0 <= j < k) is at most r, and at least one of these k segment sums is equal to r.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 1 <= k <= min(50, len(nums)). -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)) :
    ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      ∃ p, IsSplit (len nums) k.val.toNat p ∧
        (∀ j, j < k.val.toNat → segSum (contents nums) (p j) (p (j + 1)) ≤ r.val) ∧
        ∃ j, j < k.val.toNat ∧ segSum (contents nums) (p j) (p (j + 1)) = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)), ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      ∃ p, IsSplit (len nums) k.val.toNat p ∧
        (∀ j, j < k.val.toNat → segSum (contents nums) (p j) (p (j + 1)) ≤ r.val) ∧
        ∃ j, j < k.val.toNat ∧ segSum (contents nums) (p j) (p (j + 1)) = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every choice of integer indices 0 = q_0 < q_1 < ... < q_k = len(nums), the maximum of the k segment sums nums[q_j] + ... + nums[q_{j+1}-1] (0 <= j < k) is at least r.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 1 <= k <= min(50, len(nums)). -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)) :
    ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      ∀ q, IsSplit (len nums) k.val.toNat q →
        r.val ≤ maxSeg (contents nums) k.val.toNat q := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)), ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      ∀ q, IsSplit (len nums) k.val.toNat q →
        r.val ≤ maxSeg (contents nums) k.val.toNat q) := by
  sorry

/-- Whenever the function returns a result r, there exist indices l and u with 0 <= l <= u < len(nums) such that r = nums[l] + nums[l+1] + ... + nums[u].
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 1 <= k <= min(50, len(nums)). -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)) :
    ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      ∃ a b, a ≤ b ∧ b < len nums ∧ r.val = segSum (contents nums) a (b + 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)), ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      ∃ a b, a ≤ b ∧ b < len nums ∧ r.val = segSum (contents nums) a (b + 1)) := by
  sorry

/-- Whenever the function returns a result r, r = sum_{i=0}^{len(nums)-1} nums[i].
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 1 <= k <= min(50, len(nums)); k = 1. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ))
    (hk : k.val = 1) :
    ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      r.val = total (contents nums) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ))
    (hk : k.val = 1), ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      r.val = total (contents nums)) := by
  sorry

/-- Whenever the function returns a result r, r = max_{0 <= i < len(nums)} nums[i].
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 1 <= k <= min(50, len(nums)); k = len(nums). -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ))
    (hk : k.val = (len nums : ℤ)) :
    ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      r.val = maxElem (contents nums) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ))
    (hk : k.val = (len nums : ℤ)), ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      r.val = maxElem (contents nums)) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 1 <= k <= min(50, len(nums)); for every i with 0 <= i < len(nums), nums[i] = 0. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ))
    (hzero : ∀ i, i < len nums → entry nums i = 0) :
    ∀ r, Aegis.SplitArray.split_array nums k = ok r → r.val = 0 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ))
    (hzero : ∀ i, i < len nums → entry nums i = 0), ∀ r, Aegis.SplitArray.split_array nums k = ok r → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, for every integer k' with k < k' <= len(nums), there exist integer indices 0 = p_0 < p_1 < ... < p_{k'} = len(nums) such that every segment sum nums[p_j] + ... + nums[p_{j+1}-1] (for 0 <= j < k') is at most r.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 1 <= k <= min(50, len(nums)). -/
theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)) :
    ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      ∀ k' : ℕ, k.val < (k' : ℤ) → k' ≤ len nums →
        ∃ p, IsSplit (len nums) k' p ∧
          ∀ j, j < k' → segSum (contents nums) (p j) (p (j + 1)) ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)), ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      ∀ k' : ℕ, k.val < (k' : ℤ) → k' ≤ len nums →
        ∃ p, IsSplit (len nums) k' p ∧
          ∀ j, j < k' → segSum (contents nums) (p j) (p (j + 1)) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer k' with 1 <= k' < k and every choice of integer indices 0 = q_0 < q_1 < ... < q_{k'} = len(nums), the maximum of the k' segment sums nums[q_j] + ... + nums[q_{j+1}-1] (0 <= j < k') is at least r.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 1 <= k <= min(50, len(nums)). -/
theorem spec_13 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)) :
    ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      ∀ k' : ℕ, 1 ≤ k' → (k' : ℤ) < k.val →
        ∀ q, IsSplit (len nums) k' q →
          r.val ≤ maxSeg (contents nums) k' q := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ)), ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      ∀ k' : ℕ, 1 ≤ k' → (k' : ℤ) < k.val →
        ∀ q, IsSplit (len nums) k' q →
          r.val ≤ maxSeg (contents nums) k' q) := by
  sorry

/-- Whenever the function returns a result r, let P(p) = nums[0] + nums[1] + ... + nums[p-1] for 1 <= p <= len(nums), and let total = P(len(nums)). Then r = min { max(P(p), total - P(p)) | 1 <= p < len(nums) }.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 1 <= k <= min(50, len(nums)); k = 2. -/
theorem spec_14 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ))
    (hk : k.val = 2) :
    ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      r.val = bestTwoSplit (contents nums) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 1000)
    (hnn : ∀ i, i < len nums → 0 ≤ entry nums i)
    (hle : ∀ i, i < len nums → entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ min (50 : ℤ) (len nums : ℤ))
    (hk : k.val = 2), ∀ r, Aegis.SplitArray.split_array nums k = ok r →
      r.val = bestTwoSplit (contents nums)) := by
  sorry

end AegisSpec.SplitArray
