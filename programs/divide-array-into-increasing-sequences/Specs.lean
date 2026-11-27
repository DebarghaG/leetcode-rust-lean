import Aegis.CanDivideIntoSubsequences.Code.Funs

/-!
# Specifications of `Aegis.CanDivideIntoSubsequences.can_divide_into_subsequences`

LeetCode problem `divide-array-into-increasing-sequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CanDivideIntoSubsequences

open Aegis.CanDivideIntoSubsequences (can_divide_into_subsequences)

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def valueAt (nums : Slice Std.I64) (i : Nat) : Int := (vals nums).getD i 0

def countValue (nums : Slice Std.I64) (v : Int) : Nat :=
  ((vals nums).filter (fun x => x = v)).length

def maxFreq (nums : Slice Std.I64) : Nat :=
  ((vals nums).toFinset).sup (fun v => countValue nums v)

def Nondecreasing (nums : Slice Std.I64) : Prop :=
  ∀ i j : Nat, i < j → j < nums.val.length → valueAt nums i ≤ valueAt nums j

def StrictlyIncreasing (nums : Slice Std.I64) (s : Finset Nat) : Prop :=
  ∀ i ∈ s, ∀ i' ∈ s, i < i' → valueAt nums i < valueAt nums i'

def IsIndexPartition (n : Nat) (P : Finset (Finset Nat)) : Prop :=
  (∀ s ∈ P, s ⊆ Finset.range n) ∧
  (∀ s ∈ P, ∀ t ∈ P, s ≠ t → Disjoint s t) ∧
  (P.biUnion id = Finset.range n) ∧
  (∀ s ∈ P, s.Nonempty)

def IsStrictPartition (nums : Slice Std.I64) (P : Finset (Finset Nat)) : Prop :=
  IsIndexPartition nums.val.length P ∧ ∀ s ∈ P, StrictlyIncreasing nums s

def IsValidPartition (nums : Slice Std.I64) (k : Std.I64) (P : Finset (Finset Nat)) : Prop :=
  IsStrictPartition nums P ∧ ∀ s ∈ P, k.val ≤ (s.card : Int)

/-- Whenever the function returns a result r, r = true if and only if there exists an integer m >= 1 and a collection of m pairwise disjoint nonempty subsets S_1, ..., S_m of the index set {0, 1, ..., len(nums)-1} whose union is exactly {0, 1, ..., len(nums)-1}, such that for every j with 1 <= j <= m: (a) for any two indices i, i' in S_j with i < i', we have nums[i] < nums[i']; and (b) the cardinality of S_j is at least k.
  Preconditions: 1 <= k <= len(nums) <= 10^5; nums is sorted in non-decreasing order (i.e., for all i, j with 0 <= i < j < len(nums), nums[i] <= nums[j]); and 1 <= nums[i] <= 10^5 for every i with 0 <= i < len(nums). -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hlen : nums.val.length ≤ 10 ^ 5)
    (hsorted : Nondecreasing nums)
    (hvals : ∀ i, i < nums.val.length → 1 ≤ valueAt nums i ∧ valueAt nums i ≤ 10 ^ 5)
    (r : Bool) (hr : can_divide_into_subsequences nums k = ok r) :
    (r = true ↔
      ∃ m : Nat, 1 ≤ m ∧ ∃ P : Finset (Finset Nat), P.card = m ∧ IsValidPartition nums k P) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hlen : nums.val.length ≤ 10 ^ 5)
    (hsorted : Nondecreasing nums)
    (hvals : ∀ i, i < nums.val.length → 1 ≤ valueAt nums i ∧ valueAt nums i ≤ 10 ^ 5)
    (r : Bool) (hr : can_divide_into_subsequences nums k = ok r), (r = true ↔
      ∃ m : Nat, 1 ≤ m ∧ ∃ P : Finset (Finset Nat), P.card = m ∧ IsValidPartition nums k P)) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if for every integer v, the number of indices i with 0 <= i < len(nums) and nums[i] = v, multiplied by k, is at most len(nums).
  Preconditions: 1 <= k <= len(nums) <= 10^5; nums is sorted in non-decreasing order; and 1 <= nums[i] <= 10^5 for every i with 0 <= i < len(nums). -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hlen : nums.val.length ≤ 10 ^ 5)
    (hsorted : Nondecreasing nums)
    (hvals : ∀ i, i < nums.val.length → 1 ≤ valueAt nums i ∧ valueAt nums i ≤ 10 ^ 5)
    (r : Bool) (hr : can_divide_into_subsequences nums k = ok r) :
    (r = true ↔ ∀ v : Int, (countValue nums v : Int) * k.val ≤ (nums.val.length : Int)) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hlen : nums.val.length ≤ 10 ^ 5)
    (hsorted : Nondecreasing nums)
    (hvals : ∀ i, i < nums.val.length → 1 ≤ valueAt nums i ∧ valueAt nums i ≤ 10 ^ 5)
    (r : Bool) (hr : can_divide_into_subsequences nums k = ok r), (r = true ↔ ∀ v : Int, (countValue nums v : Int) * k.val ≤ (nums.val.length : Int))) := by
  sorry

/-- The function returns a result r (i.e., it does not fail).
  Preconditions: 1 <= k <= len(nums) <= 10^5; nums is sorted in non-decreasing order; and 1 <= nums[i] <= 10^5 for every i with 0 <= i < len(nums). -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hlen : nums.val.length ≤ 10 ^ 5)
    (hsorted : Nondecreasing nums)
    (hvals : ∀ i, i < nums.val.length → 1 ≤ valueAt nums i ∧ valueAt nums i ≤ 10 ^ 5) :
    ∃ r, can_divide_into_subsequences nums k = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hlen : nums.val.length ≤ 10 ^ 5)
    (hsorted : Nondecreasing nums)
    (hvals : ∀ i, i < nums.val.length → 1 ≤ valueAt nums i ∧ valueAt nums i ≤ 10 ^ 5), ∃ r, can_divide_into_subsequences nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r and r = true, for every integer v, the number of indices i with 0 <= i < len(nums) and nums[i] = v is at most floor(len(nums) / k).
  Preconditions: 1 <= k <= len(nums) <= 10^5; nums is sorted in non-decreasing order; and 1 <= nums[i] <= 10^5 for every i with 0 <= i < len(nums). -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hlen : nums.val.length ≤ 10 ^ 5)
    (hsorted : Nondecreasing nums)
    (hvals : ∀ i, i < nums.val.length → 1 ≤ valueAt nums i ∧ valueAt nums i ≤ 10 ^ 5)
    (r : Bool) (hr : can_divide_into_subsequences nums k = ok r) (hr_true : r = true) :
    ∀ v : Int, (countValue nums v : Int) ≤ (nums.val.length : Int) / k.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hlen : nums.val.length ≤ 10 ^ 5)
    (hsorted : Nondecreasing nums)
    (hvals : ∀ i, i < nums.val.length → 1 ≤ valueAt nums i ∧ valueAt nums i ≤ 10 ^ 5)
    (r : Bool) (hr : can_divide_into_subsequences nums k = ok r) (hr_true : r = true), ∀ v : Int, (countValue nums v : Int) ≤ (nums.val.length : Int) / k.val) := by
  sorry

/-- Whenever the function returns a result r and r = true, there exists a valid partition of the index set {0, ..., len(nums)-1} into exactly maxfreq pairwise disjoint strictly increasing subsequences, each of length at least k, where maxfreq is the maximum, over all integers v, of the number of indices i with 0 <= i < len(nums) and nums[i] = v.
  Preconditions: 1 <= k <= len(nums) <= 10^5; nums is sorted in non-decreasing order; and 1 <= nums[i] <= 10^5 for every i with 0 <= i < len(nums). -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hlen : nums.val.length ≤ 10 ^ 5)
    (hsorted : Nondecreasing nums)
    (hvals : ∀ i, i < nums.val.length → 1 ≤ valueAt nums i ∧ valueAt nums i ≤ 10 ^ 5)
    (r : Bool) (hr : can_divide_into_subsequences nums k = ok r) (hr_true : r = true) :
    ∃ P : Finset (Finset Nat), P.card = maxFreq nums ∧ IsValidPartition nums k P := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hlen : nums.val.length ≤ 10 ^ 5)
    (hsorted : Nondecreasing nums)
    (hvals : ∀ i, i < nums.val.length → 1 ≤ valueAt nums i ∧ valueAt nums i ≤ 10 ^ 5)
    (r : Bool) (hr : can_divide_into_subsequences nums k = ok r) (hr_true : r = true), ∃ P : Finset (Finset Nat), P.card = maxFreq nums ∧ IsValidPartition nums k P) := by
  sorry

/-- Whenever the function returns a result r and r = false, for every collection of pairwise disjoint strictly increasing subsequences whose union is the index set {0, ..., len(nums)-1}, at least one subsequence has length less than k.
  Preconditions: 1 <= k <= len(nums) <= 10^5; nums is sorted in non-decreasing order; and 1 <= nums[i] <= 10^5 for every i with 0 <= i < len(nums). -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hlen : nums.val.length ≤ 10 ^ 5)
    (hsorted : Nondecreasing nums)
    (hvals : ∀ i, i < nums.val.length → 1 ≤ valueAt nums i ∧ valueAt nums i ≤ 10 ^ 5)
    (r : Bool) (hr : can_divide_into_subsequences nums k = ok r) (hr_false : r = false) :
    ∀ P : Finset (Finset Nat), IsStrictPartition nums P → ∃ s ∈ P, (s.card : Int) < k.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hlen : nums.val.length ≤ 10 ^ 5)
    (hsorted : Nondecreasing nums)
    (hvals : ∀ i, i < nums.val.length → 1 ≤ valueAt nums i ∧ valueAt nums i ≤ 10 ^ 5)
    (r : Bool) (hr : can_divide_into_subsequences nums k = ok r) (hr_false : r = false), ∀ P : Finset (Finset Nat), IsStrictPartition nums P → ∃ s ∈ P, (s.card : Int) < k.val) := by
  sorry

/-- Whenever the function returns a result r and r = true, for every valid partition of the index set {0, ..., len(nums)-1} into pairwise disjoint strictly increasing subsequences each of length at least k, the number of subsequences in the partition is at least maxfreq, where maxfreq is the maximum frequency of any value in nums.
  Preconditions: 1 <= k <= len(nums) <= 10^5; nums is sorted in non-decreasing order; and 1 <= nums[i] <= 10^5 for every i with 0 <= i < len(nums). -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hlen : nums.val.length ≤ 10 ^ 5)
    (hsorted : Nondecreasing nums)
    (hvals : ∀ i, i < nums.val.length → 1 ≤ valueAt nums i ∧ valueAt nums i ≤ 10 ^ 5)
    (r : Bool) (hr : can_divide_into_subsequences nums k = ok r) (hr_true : r = true) :
    ∀ P : Finset (Finset Nat), IsValidPartition nums k P → maxFreq nums ≤ P.card := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hlen : nums.val.length ≤ 10 ^ 5)
    (hsorted : Nondecreasing nums)
    (hvals : ∀ i, i < nums.val.length → 1 ≤ valueAt nums i ∧ valueAt nums i ≤ 10 ^ 5)
    (r : Bool) (hr : can_divide_into_subsequences nums k = ok r) (hr_true : r = true), ∀ P : Finset (Finset Nat), IsValidPartition nums k P → maxFreq nums ≤ P.card) := by
  sorry

/-- Whenever the function returns a result r and r = true, for every valid partition of the index set {0, ..., len(nums)-1} into pairwise disjoint strictly increasing subsequences each of length at least k, the number of subsequences in the partition is at most floor(len(nums) / k).
  Preconditions: 1 <= k <= len(nums) <= 10^5; nums is sorted in non-decreasing order; and 1 <= nums[i] <= 10^5 for every i with 0 <= i < len(nums). -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hlen : nums.val.length ≤ 10 ^ 5)
    (hsorted : Nondecreasing nums)
    (hvals : ∀ i, i < nums.val.length → 1 ≤ valueAt nums i ∧ valueAt nums i ≤ 10 ^ 5)
    (r : Bool) (hr : can_divide_into_subsequences nums k = ok r) (hr_true : r = true) :
    ∀ P : Finset (Finset Nat),
      IsValidPartition nums k P → (P.card : Int) ≤ (nums.val.length : Int) / k.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hlen : nums.val.length ≤ 10 ^ 5)
    (hsorted : Nondecreasing nums)
    (hvals : ∀ i, i < nums.val.length → 1 ≤ valueAt nums i ∧ valueAt nums i ≤ 10 ^ 5)
    (r : Bool) (hr : can_divide_into_subsequences nums k = ok r) (hr_true : r = true), ∀ P : Finset (Finset Nat),
      IsValidPartition nums k P → (P.card : Int) ≤ (nums.val.length : Int) / k.val) := by
  sorry

/-- Whenever the function returns a result r2 on input (nums, k2) and a result r1 on input (nums, k1), if r2 = true then r1 = true.
  Preconditions: Let k1 and k2 be integers with 1 <= k1 <= k2 <= len(nums) <= 10^5. Assume nums is sorted in non-decreasing order and 1 <= nums[i] <= 10^5 for every i with 0 <= i < len(nums). -/
theorem spec_9 (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hk1_pos : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_le : k2.val ≤ (nums.val.length : Int))
    (hlen : nums.val.length ≤ 10 ^ 5)
    (hsorted : Nondecreasing nums)
    (hvals : ∀ i, i < nums.val.length → 1 ≤ valueAt nums i ∧ valueAt nums i ≤ 10 ^ 5)
    (r1 r2 : Bool)
    (hr1 : can_divide_into_subsequences nums k1 = ok r1)
    (hr2 : can_divide_into_subsequences nums k2 = ok r2) :
    r2 = true → r1 = true := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hk1_pos : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_le : k2.val ≤ (nums.val.length : Int))
    (hlen : nums.val.length ≤ 10 ^ 5)
    (hsorted : Nondecreasing nums)
    (hvals : ∀ i, i < nums.val.length → 1 ≤ valueAt nums i ∧ valueAt nums i ≤ 10 ^ 5)
    (r1 r2 : Bool)
    (hr1 : can_divide_into_subsequences nums k1 = ok r1)
    (hr2 : can_divide_into_subsequences nums k2 = ok r2), r2 = true → r1 = true) := by
  sorry

end AegisSpec.CanDivideIntoSubsequences
