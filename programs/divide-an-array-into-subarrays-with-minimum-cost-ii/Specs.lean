import Aegis.MinimumCost.Code.Funs

/-!
# Specifications of `Aegis.MinimumCost.minimum_cost`

LeetCode problem `divide-an-array-into-subarrays-with-minimum-cost-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinimumCost (minimum_cost)

  namespace AegisSpec.MinimumCost

  def len (nums : Slice Std.I64) : ℕ := nums.val.length

  def elem (nums : Slice Std.I64) (i : ℕ) : ℤ := (nums.val.getD i 0#i64).val

  def minList (d : ℤ) (l : List ℤ) : ℤ := (l.min?).getD d

  def feasible (nums : Slice Std.I64) (k dist : Std.I64) (s : ℕ → ℕ) : Prop :=
    s 0 = 0 ∧
      (∀ i, i + 1 < k.val.toNat → s i < s (i + 1)) ∧
      (∀ i, i < k.val.toNat → s i ≤ len nums - 1) ∧
      s (k.val.toNat - 1) ≤ s 1 + dist.val.toNat

  def pathSum (nums : Slice Std.I64) (k : Std.I64) (s : ℕ → ℕ) : ℤ :=
    (Finset.range k.val.toNat).sum (fun i => elem nums (s i))

  def tailVals (nums : Slice Std.I64) : List ℤ :=
    (List.range (len nums - 1)).map (fun i => elem nums (i + 1))

  def tailMin (nums : Slice Std.I64) : ℤ := minList (elem nums 1) (tailVals nums)

  def sumSmallest (l : List ℤ) (t : ℕ) : ℤ :=
    ((l.mergeSort (fun a b => a ≤ b)).take t).sum

  def sumSmallestTail (nums : Slice Std.I64) (k : Std.I64) : ℤ :=
    sumSmallest (tailVals nums) (k.val.toNat - 1)

  def windowSums (nums : Slice Std.I64) (k : Std.I64) : List ℤ :=
    (List.range (len nums - (k.val.toNat - 1))).map
      (fun i => (Finset.range (k.val.toNat - 1)).sum (fun j => elem nums (1 + i + j)))

  def windowMin (nums : Slice Std.I64) (k : Std.I64) : ℤ :=
    minList (elem nums 1) (windowSums nums k)

  def pairSums (nums : Slice Std.I64) (dist : Std.I64) : List ℤ :=
    ((List.range (len nums)).product (List.range (len nums))).filterMap
      (fun p =>
        if 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ len nums - 1 ∧ p.2 - p.1 ≤ dist.val.toNat then
          some (elem nums p.1 + elem nums p.2)
        else none)

  def pairMin (nums : Slice Std.I64) (dist : Std.I64) : ℤ :=
    minList (elem nums 1 + elem nums 2) (pairSums nums dist)

  /-- The function returns a result r, and r is the minimum, over all integer sequences s_0, s_1, ..., s_{k-1} satisfying s_0 = 0, 0 < s_1 < s_2 < ... < s_{k-1} <= n - 1, and s_{k-1} - s_1 <= dist, of the sum nums[s_0] + nums[s_1] + ... + nums[s_{k-1}]. For k = 2 the distance condition is s_1 - s_1 = 0 <= dist, which holds under the preconditions.
    Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Either (k = 2 and dist >= 1) or (3 <= k <= n and k - 2 <= dist). -/
  theorem spec_1 (nums : Slice Std.I64) (k dist : Std.I64)
      (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
      (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
      (hk : (k.val = 2 ∧ 1 ≤ dist.val) ∨
        (3 ≤ k.val ∧ k.val ≤ (len nums : ℤ) ∧ k.val - 2 ≤ dist.val)) :
      ∃ r, minimum_cost nums k dist = ok r ∧
        (∀ s, feasible nums k dist s → r.val ≤ pathSum nums k s) ∧
        (∃ s, feasible nums k dist s ∧ r.val = pathSum nums k s) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k dist : Std.I64)
        (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
        (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
        (hk : (k.val = 2 ∧ 1 ≤ dist.val) ∨
          (3 ≤ k.val ∧ k.val ≤ (len nums : ℤ) ∧ k.val - 2 ≤ dist.val)), ∃ r, minimum_cost nums k dist = ok r ∧
          (∀ s, feasible nums k dist s → r.val ≤ pathSum nums k s) ∧
          (∃ s, feasible nums k dist s ∧ r.val = pathSum nums k s)) := by
    sorry

  /-- For every input satisfying the preconditions, minimum_cost does not fail: it returns a result r.
    Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Either (k = 2 and dist >= 1) or (3 <= k <= n and k - 2 <= dist). -/
  theorem spec_2 (nums : Slice Std.I64) (k dist : Std.I64)
      (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
      (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
      (hk : (k.val = 2 ∧ 1 ≤ dist.val) ∨
        (3 ≤ k.val ∧ k.val ≤ (len nums : ℤ) ∧ k.val - 2 ≤ dist.val)) :
      ∃ r, minimum_cost nums k dist = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k dist : Std.I64)
        (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
        (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
        (hk : (k.val = 2 ∧ 1 ≤ dist.val) ∨
          (3 ≤ k.val ∧ k.val ≤ (len nums : ℤ) ∧ k.val - 2 ≤ dist.val)), ∃ r, minimum_cost nums k dist = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= nums[0] + (k - 1) * m, where m is the minimum of nums[1], nums[2], ..., nums[n-1].
    Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Either (k = 2 and dist >= 1) or (3 <= k <= n and k - 2 <= dist). -/
  theorem spec_3 (nums : Slice Std.I64) (k dist : Std.I64)
      (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
      (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
      (hk : (k.val = 2 ∧ 1 ≤ dist.val) ∨
        (3 ≤ k.val ∧ k.val ≤ (len nums : ℤ) ∧ k.val - 2 ≤ dist.val)) :
      ∀ r, minimum_cost nums k dist = ok r →
        elem nums 0 + (k.val - 1) * tailMin nums ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k dist : Std.I64)
        (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
        (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
        (hk : (k.val = 2 ∧ 1 ≤ dist.val) ∨
          (3 ≤ k.val ∧ k.val ≤ (len nums : ℤ) ∧ k.val - 2 ≤ dist.val)), ∀ r, minimum_cost nums k dist = ok r →
          elem nums 0 + (k.val - 1) * tailMin nums ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= nums[0] + nums[1] + nums[2] + ... + nums[k-1].
    Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Either (k = 2 and dist >= 1) or (3 <= k <= n and k - 2 <= dist). -/
  theorem spec_4 (nums : Slice Std.I64) (k dist : Std.I64)
      (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
      (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
      (hk : (k.val = 2 ∧ 1 ≤ dist.val) ∨
        (3 ≤ k.val ∧ k.val ≤ (len nums : ℤ) ∧ k.val - 2 ≤ dist.val)) :
      ∀ r, minimum_cost nums k dist = ok r →
        r.val ≤ (Finset.range k.val.toNat).sum (fun i => elem nums i) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k dist : Std.I64)
        (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
        (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
        (hk : (k.val = 2 ∧ 1 ≤ dist.val) ∨
          (3 ≤ k.val ∧ k.val ≤ (len nums : ℤ) ∧ k.val - 2 ≤ dist.val)), ∀ r, minimum_cost nums k dist = ok r →
          r.val ≤ (Finset.range k.val.toNat).sum (fun i => elem nums i)) := by
    sorry

  /-- Whenever the function returns a result r, there exist integers s_0, s_1, ..., s_{k-1} such that s_0 = 0, 0 < s_1 < s_2 < ... < s_{k-1} <= n - 1, s_{k-1} - s_1 <= dist, and r = nums[s_0] + nums[s_1] + ... + nums[s_{k-1}].
    Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Either (k = 2 and dist >= 1) or (3 <= k <= n and k - 2 <= dist). -/
  theorem spec_5 (nums : Slice Std.I64) (k dist : Std.I64)
      (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
      (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
      (hk : (k.val = 2 ∧ 1 ≤ dist.val) ∨
        (3 ≤ k.val ∧ k.val ≤ (len nums : ℤ) ∧ k.val - 2 ≤ dist.val)) :
      ∀ r, minimum_cost nums k dist = ok r →
        ∃ s, feasible nums k dist s ∧ r.val = pathSum nums k s := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k dist : Std.I64)
        (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
        (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
        (hk : (k.val = 2 ∧ 1 ≤ dist.val) ∨
          (3 ≤ k.val ∧ k.val ≤ (len nums : ℤ) ∧ k.val - 2 ≤ dist.val)), ∀ r, minimum_cost nums k dist = ok r →
          ∃ s, feasible nums k dist s ∧ r.val = pathSum nums k s) := by
    sorry

  /-- Whenever the function returns a result r, for every integer sequence t_0, t_1, ..., t_{k-1} satisfying t_0 = 0, 0 < t_1 < t_2 < ... < t_{k-1} <= n - 1, and t_{k-1} - t_1 <= dist, we have r <= nums[t_0] + nums[t_1] + ... + nums[t_{k-1}].
    Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Either (k = 2 and dist >= 1) or (3 <= k <= n and k - 2 <= dist). -/
  theorem spec_6 (nums : Slice Std.I64) (k dist : Std.I64)
      (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
      (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
      (hk : (k.val = 2 ∧ 1 ≤ dist.val) ∨
        (3 ≤ k.val ∧ k.val ≤ (len nums : ℤ) ∧ k.val - 2 ≤ dist.val)) :
      ∀ r, minimum_cost nums k dist = ok r →
        ∀ t, feasible nums k dist t → r.val ≤ pathSum nums k t := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k dist : Std.I64)
        (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
        (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
        (hk : (k.val = 2 ∧ 1 ≤ dist.val) ∨
          (3 ≤ k.val ∧ k.val ≤ (len nums : ℤ) ∧ k.val - 2 ≤ dist.val)), ∀ r, minimum_cost nums k dist = ok r →
          ∀ t, feasible nums k dist t → r.val ≤ pathSum nums k t) := by
    sorry

  /-- The function returns r = nums[0] + nums[1] + ... + nums[n-1].
    Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. k = n and dist >= n - 2. -/
  theorem spec_7 (nums : Slice Std.I64) (k dist : Std.I64)
      (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
      (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
      (hk : k.val = (len nums : ℤ))
      (hdist : (len nums : ℤ) - 2 ≤ dist.val) :
      ∃ r, minimum_cost nums k dist = ok r ∧
        r.val = (Finset.range (len nums)).sum (fun i => elem nums i) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k dist : Std.I64)
        (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
        (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
        (hk : k.val = (len nums : ℤ))
        (hdist : (len nums : ℤ) - 2 ≤ dist.val), ∃ r, minimum_cost nums k dist = ok r ∧
          r.val = (Finset.range (len nums)).sum (fun i => elem nums i)) := by
    sorry

  /-- The function returns r = nums[0] + (the sum of the k-1 smallest values in the multiset {nums[1], nums[2], ..., nums[n-1]}), where the k-1 smallest values are taken with multiplicity from the distinct indices 1 through n-1.
    Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. 3 <= k <= n and dist >= n - 2. -/
  theorem spec_8 (nums : Slice Std.I64) (k dist : Std.I64)
      (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
      (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
      (hk : 3 ≤ k.val ∧ k.val ≤ (len nums : ℤ))
      (hdist : (len nums : ℤ) - 2 ≤ dist.val) :
      ∃ r, minimum_cost nums k dist = ok r ∧
        r.val = elem nums 0 + sumSmallestTail nums k := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k dist : Std.I64)
        (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
        (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
        (hk : 3 ≤ k.val ∧ k.val ≤ (len nums : ℤ))
        (hdist : (len nums : ℤ) - 2 ≤ dist.val), ∃ r, minimum_cost nums k dist = ok r ∧
          r.val = elem nums 0 + sumSmallestTail nums k) := by
    sorry

  /-- The function returns r = nums[0] + min { nums[s] + nums[s+1] + ... + nums[s+k-2] | 1 <= s <= n - k + 1 }.
    Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. 3 <= k <= n and dist = k - 2. -/
  theorem spec_9 (nums : Slice Std.I64) (k dist : Std.I64)
      (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
      (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
      (hk : 3 ≤ k.val ∧ k.val ≤ (len nums : ℤ))
      (hdist : dist.val = k.val - 2) :
      ∃ r, minimum_cost nums k dist = ok r ∧
        r.val = elem nums 0 + windowMin nums k := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k dist : Std.I64)
        (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
        (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
        (hk : 3 ≤ k.val ∧ k.val ≤ (len nums : ℤ))
        (hdist : dist.val = k.val - 2), ∃ r, minimum_cost nums k dist = ok r ∧
          r.val = elem nums 0 + windowMin nums k) := by
    sorry

  /-- The function returns r = nums[0] + min { nums[i] | 1 <= i <= n - 1 }.
    Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. k = 2 and dist >= 1. -/
  theorem spec_10 (nums : Slice Std.I64) (k dist : Std.I64)
      (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
      (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
      (hk : k.val = 2) (hdist : 1 ≤ dist.val) :
      ∃ r, minimum_cost nums k dist = ok r ∧
        r.val = elem nums 0 + tailMin nums := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k dist : Std.I64)
        (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
        (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
        (hk : k.val = 2) (hdist : 1 ≤ dist.val), ∃ r, minimum_cost nums k dist = ok r ∧
          r.val = elem nums 0 + tailMin nums) := by
    sorry

  /-- The function returns r = nums[0] + min { nums[i] + nums[j] | 1 <= i < j <= n - 1 and j - i <= dist }.
    Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. k = 3 and dist >= 1. -/
  theorem spec_11 (nums : Slice Std.I64) (k dist : Std.I64)
      (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
      (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
      (hk : k.val = 3) (hdist : 1 ≤ dist.val) :
      ∃ r, minimum_cost nums k dist = ok r ∧
        r.val = elem nums 0 + pairMin nums dist := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k dist : Std.I64)
        (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
        (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
        (hk : k.val = 3) (hdist : 1 ≤ dist.val), ∃ r, minimum_cost nums k dist = ok r ∧
          r.val = elem nums 0 + pairMin nums dist) := by
    sorry

  /-- If minimum_cost(nums, k, dist1) returns r1 and minimum_cost(nums, k, dist2) returns r2, then r2 <= r1.
    Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. 3 <= k <= n. Let dist1 and dist2 be integers with k - 2 <= dist1 <= dist2. -/
  theorem spec_12 (nums : Slice Std.I64) (k dist1 dist2 : Std.I64)
      (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
      (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
      (hk : 3 ≤ k.val ∧ k.val ≤ (len nums : ℤ))
      (hd1 : k.val - 2 ≤ dist1.val) (hd2 : dist1.val ≤ dist2.val) :
      ∀ r1 r2, minimum_cost nums k dist1 = ok r1 → minimum_cost nums k dist2 = ok r2 →
        r2.val ≤ r1.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (k dist1 dist2 : Std.I64)
        (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
        (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
        (hk : 3 ≤ k.val ∧ k.val ≤ (len nums : ℤ))
        (hd1 : k.val - 2 ≤ dist1.val) (hd2 : dist1.val ≤ dist2.val), ∀ r1 r2, minimum_cost nums k dist1 = ok r1 → minimum_cost nums k dist2 = ok r2 →
          r2.val ≤ r1.val) := by
    sorry

  /-- If minimum_cost(nums, k1, dist) returns r1 and minimum_cost(nums, k2, dist) returns r2, then r1 <= r2.
    Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Let k1 and k2 be integers with 3 <= k1 <= k2 <= n. Let dist be an integer with k2 - 2 <= dist. -/
  theorem spec_13 (nums : Slice Std.I64) (k1 k2 dist : Std.I64)
      (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
      (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
      (hk1 : 3 ≤ k1.val) (hk2 : k1.val ≤ k2.val) (hk3 : k2.val ≤ (len nums : ℤ))
      (hdist : k2.val - 2 ≤ dist.val) :
      ∀ r1 r2, minimum_cost nums k1 dist = ok r1 → minimum_cost nums k2 dist = ok r2 →
        r1.val ≤ r2.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (k1 k2 dist : Std.I64)
        (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
        (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
        (hk1 : 3 ≤ k1.val) (hk2 : k1.val ≤ k2.val) (hk3 : k2.val ≤ (len nums : ℤ))
        (hdist : k2.val - 2 ≤ dist.val), ∀ r1 r2, minimum_cost nums k1 dist = ok r1 → minimum_cost nums k2 dist = ok r2 →
          r1.val ≤ r2.val) := by
    sorry

  /-- The function returns r = k * c.
    Preconditions: Let n = len(nums). 3 <= n <= 100000. There is an integer c with 1 <= c <= 1000000000 such that nums[i] = c for all i with 0 <= i < n. 3 <= k <= n and k - 2 <= dist. -/
  theorem spec_14 (nums : Slice Std.I64) (k dist : Std.I64)
      (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
      (c : ℤ) (hc1 : 1 ≤ c) (hc2 : c ≤ 1000000000)
      (hconst : ∀ i, i < len nums → elem nums i = c)
      (hk : 3 ≤ k.val ∧ k.val ≤ (len nums : ℤ) ∧ k.val - 2 ≤ dist.val) :
      ∃ r, minimum_cost nums k dist = ok r ∧ r.val = k.val * c := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (k dist : Std.I64)
        (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
        (c : ℤ) (hc1 : 1 ≤ c) (hc2 : c ≤ 1000000000)
        (hconst : ∀ i, i < len nums → elem nums i = c)
        (hk : 3 ≤ k.val ∧ k.val ≤ (len nums : ℤ) ∧ k.val - 2 ≤ dist.val), ∃ r, minimum_cost nums k dist = ok r ∧ r.val = k.val * c) := by
    sorry

  /-- If minimum_cost(nums, k, dist) returns r and minimum_cost(nums2, k, dist) returns r2, then r <= r2.
    Preconditions: Let n = len(nums). 3 <= n <= 100000. For every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Let nums2 be another array of length n with 1 <= nums2[i] <= 1000000000 for every i with 0 <= i < n. Suppose nums[i] <= nums2[i] for every i with 0 <= i < n. Let k and dist satisfy either (k = 2 and dist >= 1) or (3 <= k <= n and k - 2 <= dist). -/
  theorem spec_15 (nums nums2 : Slice Std.I64) (k dist : Std.I64)
      (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
      (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
      (hlen2 : len nums2 = len nums)
      (hvals2 : ∀ i, i < len nums2 → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 1000000000)
      (hle : ∀ i, i < len nums → elem nums i ≤ elem nums2 i)
      (hk : (k.val = 2 ∧ 1 ≤ dist.val) ∨
        (3 ≤ k.val ∧ k.val ≤ (len nums : ℤ) ∧ k.val - 2 ≤ dist.val)) :
      ∀ r r2, minimum_cost nums k dist = ok r → minimum_cost nums2 k dist = ok r2 →
        r.val ≤ r2.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (k dist : Std.I64)
        (hn : 3 ≤ len nums) (hn' : len nums ≤ 100000)
        (hvals : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
        (hlen2 : len nums2 = len nums)
        (hvals2 : ∀ i, i < len nums2 → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 1000000000)
        (hle : ∀ i, i < len nums → elem nums i ≤ elem nums2 i)
        (hk : (k.val = 2 ∧ 1 ≤ dist.val) ∨
          (3 ≤ k.val ∧ k.val ≤ (len nums : ℤ) ∧ k.val - 2 ≤ dist.val)), ∀ r r2, minimum_cost nums k dist = ok r → minimum_cost nums2 k dist = ok r2 →
          r.val ≤ r2.val) := by
    sorry

  end AegisSpec.MinimumCost
