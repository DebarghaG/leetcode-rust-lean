import Aegis.PartitionArray.Code.Funs

/-!
# Specifications of `Aegis.PartitionArray.partition_array`

LeetCode problem `partition-array-such-that-maximum-difference-is-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.PartitionArray (partition_array)

namespace AegisSpec.PartitionArray

def numsVal (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def valAt (a : List ℤ) (i : ℕ) : ℤ := (a[i]?).getD 0

def IsMinValue (a : List ℤ) (lo : ℤ) : Prop := (∀ x ∈ a, lo ≤ x) ∧ lo ∈ a

def IsMaxValue (a : List ℤ) (hi : ℤ) : Prop := (∀ x ∈ a, x ≤ hi) ∧ hi ∈ a

def valueSet (a : List ℤ) : Finset ℤ := a.toFinset

def nDistinct (a : List ℤ) : ℕ := (valueSet a).card

def IsValidPartition (a : List ℤ) (k : ℤ) (m : ℕ) (S : Fin m → Finset ℕ) : Prop :=
  (∀ j : Fin m, (S j).Nonempty) ∧
  (∀ (j : Fin m) (i : ℕ), i ∈ S j → i < a.length) ∧
  (∀ (j j' : Fin m), j ≠ j' → ∀ i : ℕ, i ∈ S j → i ∈ S j' → False) ∧
  (∀ i : ℕ, i < a.length → ∃ j : Fin m, i ∈ S j) ∧
  (∀ (j : Fin m) (i : ℕ), i ∈ S j → ∀ i' : ℕ, i' ∈ S j → |valAt a i - valAt a i'| ≤ k)

def HasValidPartition (a : List ℤ) (k : ℤ) (m : ℤ) : Prop :=
  ∃ mn : ℕ, m = (mn : ℤ) ∧ ∃ S : Fin mn → Finset ℕ, IsValidPartition a k mn S

def IsLeastPartitionSize (a : List ℤ) (k : ℤ) (m : ℤ) : Prop :=
  1 ≤ m ∧ HasValidPartition a k m ∧
    ∀ m' : ℤ, 1 ≤ m' → m' < m → ¬ HasValidPartition a k m'

def IsBlockSplit (s : List ℤ) (k : ℤ) (m : ℕ) : Prop :=
  ∃ bs : List (List ℤ), bs.length = m ∧ bs.flatten = s ∧
    (∀ b ∈ bs, b ≠ []) ∧ (∀ b ∈ bs, ∀ x ∈ b, ∀ y ∈ b, |y - x| ≤ k)

def IsSubMultiset (b a : List ℤ) : Prop := ∀ v : ℤ, b.count v ≤ a.count v

def IsSeparated (a : List ℤ) (k : ℤ) (T : Finset ℕ) : Prop :=
  (∀ i ∈ T, i < a.length) ∧
    (∀ i ∈ T, ∀ i' ∈ T, i ≠ i' → k < |valAt a i - valAt a i'|)

/-- Define a valid m-partition of nums (for an integer m >= 1) as a collection S_1,...,S_m of nonempty subsets of the index set {0,...,len(nums)-1} that are pairwise disjoint and whose union is the whole index set, such that for every j with 1 <= j <= m, max_{i in S_j} nums[i] - min_{i in S_j} nums[i] <= k. (Each S_j, read in increasing index order, is a subsequence.) Let M be the least integer m >= 1 for which nums has a valid m-partition. The function returns a result r and r = M.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000) :
    ∃ r : Std.I64, partition_array nums k = ok r ∧
      IsLeastPartitionSize (numsVal nums) k.val r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000), ∃ r : Std.I64, partition_array nums k = ok r ∧
      IsLeastPartitionSize (numsVal nums) k.val r.val) := by
  sorry

/-- The function returns a result r (it does not fail, overflow, panic, or access an index out of bounds) for every input satisfying the preconditions.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000) :
    ∃ r : Std.I64, partition_array nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000), ∃ r : Std.I64, partition_array nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000) :
    ∀ r : Std.I64, partition_array nums k = ok r → 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : Std.I64, partition_array nums k = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= len(nums).
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000) :
    ∀ r : Std.I64, partition_array nums k = ok r → r.val ≤ (nums.val.length : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : Std.I64, partition_array nums k = ok r → r.val ≤ (nums.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r <= D, where D is the number of distinct values occurring in nums, i.e. the cardinality of the set {v | there exists i with 0 <= i < len(nums) and nums[i] = v}.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000) :
    ∀ r : Std.I64, partition_array nums k = ok r → r.val ≤ (nDistinct (numsVal nums) : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : Std.I64, partition_array nums k = ok r → r.val ≤ (nDistinct (numsVal nums) : ℤ)) := by
  sorry

/-- Let lo = min_{0 <= i < len(nums)} nums[i] and hi = max_{0 <= i < len(nums)} nums[i]. Whenever the function returns a result r, r = 1 if and only if hi - lo <= k.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64) (lo hi : ℤ)
    (hlo : IsMinValue (numsVal nums) lo) (hhi : IsMaxValue (numsVal nums) hi)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000) :
    ∀ r : Std.I64, partition_array nums k = ok r → (r.val = 1 ↔ hi - lo ≤ k) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (lo hi : ℤ)
    (hlo : IsMinValue (numsVal nums) lo) (hhi : IsMaxValue (numsVal nums) hi)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : Std.I64, partition_array nums k = ok r → (r.val = 1 ↔ hi - lo ≤ k)) := by
  sorry

/-- Whenever the function returns a result r, r = D, where D is the number of distinct values occurring in nums.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; k = 0. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk : k.val = 0) :
    ∀ r : Std.I64, partition_array nums k = ok r → r.val = (nDistinct (numsVal nums) : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk : k.val = 0), ∀ r : Std.I64, partition_array nums k = ok r → r.val = (nDistinct (numsVal nums) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, nums has a valid r-partition: there are r nonempty pairwise disjoint index sets S_1,...,S_r whose union is {0,...,len(nums)-1} and, for every j with 1 <= j <= r, max_{i in S_j} nums[i] - min_{i in S_j} nums[i] <= k.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000) :
    ∀ r : Std.I64, partition_array nums k = ok r → HasValidPartition (numsVal nums) k.val r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : Std.I64, partition_array nums k = ok r → HasValidPartition (numsVal nums) k.val r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer m with 1 <= m < r there is no valid m-partition of nums, where a valid m-partition is a collection of m nonempty pairwise disjoint index sets covering all indices and each having maximum value minus minimum value at most k.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000) :
    ∀ r : Std.I64, partition_array nums k = ok r →
      ∀ m : ℤ, 1 ≤ m → m < r.val → ¬ HasValidPartition (numsVal nums) k.val m := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : Std.I64, partition_array nums k = ok r →
      ∀ m : ℤ, 1 ≤ m → m < r.val → ¬ HasValidPartition (numsVal nums) k.val m) := by
  sorry

/-- Let sorted be a nondecreasing rearrangement of nums (same multiset of values). Whenever the function returns a result r, r is the least integer m >= 1 such that sorted can be split into m nonempty contiguous blocks sorted[l_0..u_0], sorted[l_1..u_1], ..., sorted[l_{m-1}..u_{m-1}] covering all positions, with sorted[u_j] - sorted[l_j] <= k for every j with 0 <= j < m.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64) (sorted : List ℤ)
    (hsorted : sorted.Pairwise (· ≤ ·)) (hperm : sorted.Perm (numsVal nums))
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000) :
    ∀ r : Std.I64, partition_array nums k = ok r →
      ∃ m : ℕ, r.val = (m : ℤ) ∧ 1 ≤ m ∧ IsBlockSplit sorted k.val m ∧
        ∀ m' : ℕ, 1 ≤ m' → m' < m → ¬ IsBlockSplit sorted k.val m' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (sorted : List ℤ)
    (hsorted : sorted.Pairwise (· ≤ ·)) (hperm : sorted.Perm (numsVal nums))
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : Std.I64, partition_array nums k = ok r →
      ∃ m : ℕ, r.val = (m : ℤ) ∧ 1 ≤ m ∧ IsBlockSplit sorted k.val m ∧
        ∀ m' : ℕ, 1 ≤ m' → m' < m → ¬ IsBlockSplit sorted k.val m') := by
  sorry

/-- Whenever partition_array nums k returns a result r and partition_array nums' k returns a result r', we have r = r'.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; nums' is any list of 64-bit integers with len(nums') = len(nums) and the same multiset of values as nums (each value occurs the same number of times); 0 <= k <= 100000. -/
theorem spec_11 (nums nums' : Slice Std.I64) (k : Std.I64)
    (hlen' : nums'.val.length = nums.val.length) (hperm : nums'.val.Perm nums.val)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000) :
    ∀ r r' : Std.I64, partition_array nums k = ok r → partition_array nums' k = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
    (hlen' : nums'.val.length = nums.val.length) (hperm : nums'.val.Perm nums.val)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r r' : Std.I64, partition_array nums k = ok r → partition_array nums' k = ok r' →
      r.val = r'.val) := by
  sorry

/-- Whenever partition_array nums k returns a result r and partition_array uniq k returns a result r_u, we have r = r_u.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; uniq is any list obtained from nums by keeping exactly one occurrence of each distinct value and deleting all other occurrences (so uniq has no repeated values and the same set of distinct values as nums); 0 <= k <= 100000. -/
theorem spec_12 (nums uniq : Slice Std.I64) (k : Std.I64)
    (huniq : (uniq.val.map (fun x => x.val)).Perm ((numsVal nums).dedup))
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000) :
    ∀ r ru : Std.I64, partition_array nums k = ok r → partition_array uniq k = ok ru →
      r.val = ru.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums uniq : Slice Std.I64) (k : Std.I64)
    (huniq : (uniq.val.map (fun x => x.val)).Perm ((numsVal nums).dedup))
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r ru : Std.I64, partition_array nums k = ok r → partition_array uniq k = ok ru →
      r.val = ru.val) := by
  sorry

/-- Whenever partition_array nums k1 returns a result r1 and partition_array nums k2 returns a result r2, we have r1 >= r2.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k1 <= k2 <= 100000. -/
theorem spec_13 (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hk12 : k1.val ≤ k2.val) (hk1 : 0 ≤ k1.val) (hk2 : k2.val ≤ 100000)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r1 r2 : Std.I64, partition_array nums k1 = ok r1 → partition_array nums k2 = ok r2 →
      r2.val ≤ r1.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hk12 : k1.val ≤ k2.val) (hk1 : 0 ≤ k1.val) (hk2 : k2.val ≤ 100000)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000), ∀ r1 r2 : Std.I64, partition_array nums k1 = ok r1 → partition_array nums k2 = ok r2 →
      r2.val ≤ r1.val) := by
  sorry

/-- Whenever partition_array nums k returns a result r and partition_array nums' k returns a result r', we have r' <= r.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; nums' is a nonempty list of 64-bit integers that is a submultiset of nums (i.e., every value occurs in nums' no more often than in nums) and satisfies 0 <= nums'[i] <= 100000 for every i; 0 <= k <= 100000. -/
theorem spec_14 (nums nums' : Slice Std.I64) (k : Std.I64)
    (hne : nums'.val ≠ [])
    (hsub : IsSubMultiset (nums'.val.map (fun x => x.val)) (numsVal nums))
    (hval' : ∀ x ∈ nums'.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000) :
    ∀ r r' : Std.I64, partition_array nums k = ok r → partition_array nums' k = ok r' →
      r'.val ≤ r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
    (hne : nums'.val ≠ [])
    (hsub : IsSubMultiset (nums'.val.map (fun x => x.val)) (numsVal nums))
    (hval' : ∀ x ∈ nums'.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r r' : Std.I64, partition_array nums k = ok r → partition_array nums' k = ok r' →
      r'.val ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, for every set T of indices with T subset of {0,...,len(nums)-1}, if |nums[i] - nums[j]| > k for every two distinct indices i,j in T, then |T| <= r.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
theorem spec_15 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000) :
    ∀ r : Std.I64, partition_array nums k = ok r →
      ∀ T : Finset ℕ, IsSeparated (numsVal nums) k.val T → (T.card : ℤ) ≤ r.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : Std.I64, partition_array nums k = ok r →
      ∀ T : Finset ℕ, IsSeparated (numsVal nums) k.val T → (T.card : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r equals the maximum cardinality of a set T of indices with T subset of {0,...,len(nums)-1} such that |nums[i] - nums[j]| > k for every two distinct indices i,j in T.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000; 0 <= k <= 100000. -/
theorem spec_16 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000) :
    ∀ r : Std.I64, partition_array nums k = ok r →
      ∃ T : Finset ℕ, IsSeparated (numsVal nums) k.val T ∧ (T.card : ℤ) = r.val ∧
        ∀ T' : Finset ℕ, IsSeparated (numsVal nums) k.val T' → T'.card ≤ T.card := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hval : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : Std.I64, partition_array nums k = ok r →
      ∃ T : Finset ℕ, IsSeparated (numsVal nums) k.val T ∧ (T.card : ℤ) = r.val ∧
        ∀ T' : Finset ℕ, IsSeparated (numsVal nums) k.val T' → T'.card ≤ T.card) := by
  sorry

end AegisSpec.PartitionArray
