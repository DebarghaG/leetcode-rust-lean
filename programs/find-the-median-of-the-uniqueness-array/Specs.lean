import Aegis.MedianOfUniquenessArray.Code.Funs

/-!
# Specifications of `Aegis.MedianOfUniquenessArray.median_of_uniqueness_array`

LeetCode problem `find-the-median-of-the-uniqueness-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MedianOfUniquenessArray

open Aeneas Aeneas.Std Result

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def distinctCount (l : List Int) : Nat := l.dedup.length

def subDistinct (l : List Int) (i j : Nat) : Nat :=
  distinctCount ((l.drop i).take (j + 1 - i))

def numDistinct (nums : Slice Std.I64) (i j : Nat) : Nat := subDistinct (vals nums) i j

def uniquenessArray (nums : Slice Std.I64) : List Int :=
  (List.range nums.val.length).flatMap fun i =>
    (List.range (nums.val.length - i)).map fun k => ((numDistinct nums i (i + k) : Nat) : Int)

def sortAsc (l : List Int) : List Int := l.mergeSort (· ≤ ·)

def subarrayCount (n : Nat) : Nat := n * (n + 1) / 2

def medianIndex (n : Nat) : Nat := (subarrayCount n - 1) / 2

def valueCount (nums : Slice Std.I64) : Nat := distinctCount (vals nums)

def countLe (nums : Slice Std.I64) (k : Int) : Nat :=
  (uniquenessArray nums).countP (fun x => decide (x ≤ k))

def countEq (nums : Slice Std.I64) (k : Int) : Nat :=
  (uniquenessArray nums).countP (fun x => decide (x = k))

def sortedSubarrayLengths (n : Nat) : List Int :=
  sortAsc ((List.range n).flatMap fun i =>
    (List.range (n - i)).map fun k => ((k + 1 : Nat) : Int))

/-- Let n = len(nums). For every pair (i,j) with 0 <= i <= j < n, let d(i,j) be the number of distinct integer values among nums[i], nums[i+1], ..., nums[j]. Let U be the multiset containing d(i,j) for all such pairs, and let L = n*(n+1)/2 be its size. Let t = (L - 1) / 2 using integer division. The function returns a result r (it does not fail) and, when U is sorted in non-decreasing order as a 0-indexed sequence U_sorted of length L, we have r = U_sorted[t]. Equivalently, r is the median of the uniqueness array under the problem's smaller-middle tie rule.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r ∧
        (sortAsc (uniquenessArray nums))[medianIndex nums.val.length]? = some r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∃ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r ∧
        (sortAsc (uniquenessArray nums))[medianIndex nums.val.length]? = some r.val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not panic, fail, or overflow. In particular, the returned value is a valid i64.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∃ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, we have 1 <= r.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r → 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, let D be the number of distinct values occurring in the whole array nums, i.e. the cardinality of the set { nums[i] | 0 <= i < len(nums) }. Then r <= D.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        r.val ≤ (valueCount nums : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        r.val ≤ (valueCount nums : Int)) := by
  sorry

/-- Whenever the function returns a result r, if len(nums) <= 3 then r = 1.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_5 (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hsmall : nums.val.length ≤ 3) :
    ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hsmall : nums.val.length ≤ 3), ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, if all entries of nums are equal (that is, nums[i] = nums[0] for every 0 <= i < len(nums)), then r = 1.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_6 (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hconst : ∀ i (hi : i < nums.val.length), (nums.val[i]).val = (nums.val[0]).val) :
    ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hconst : ∀ i (hi : i < nums.val.length), (nums.val[i]).val = (nums.val[0]).val), ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, if the entries of nums are pairwise distinct (that is, nums[i] != nums[j] for every 0 <= i < j < len(nums)), then r is the median, using the same smaller-middle tie rule, of the multiset M that contains one copy of j - i + 1 for every pair 0 <= i <= j < len(nums). Equivalently, with n = len(nums), L = n*(n+1)/2, and t = (L - 1) / 2, r is the t-th element (0-indexed) of M after sorting in non-decreasing order.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_7 (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hnd : (vals nums).Nodup) :
    ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        (sortedSubarrayLengths nums.val.length)[medianIndex nums.val.length]? = some r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hnd : (vals nums).Nodup), ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        (sortedSubarrayLengths nums.val.length)[medianIndex nums.val.length]? = some r.val) := by
  sorry

/-- Whenever the function returns a result r, let n = len(nums), L = n*(n+1)/2, t = (L - 1) / 2, and for every 0 <= i <= j < n let d(i,j) be the number of distinct values in nums[i..j]. Then the number of pairs (i,j) with 0 <= i <= j < n and d(i,j) <= r is at least t + 1.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_8 (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        medianIndex nums.val.length + 1 ≤ countLe nums r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        medianIndex nums.val.length + 1 ≤ countLe nums r.val) := by
  sorry

/-- Whenever the function returns a result r, let n = len(nums), L = n*(n+1)/2, t = (L - 1) / 2, and for every 0 <= i <= j < n let d(i,j) be the number of distinct values in nums[i..j]. For every integer k with 1 <= k < r, the number of pairs (i,j) with 0 <= i <= j < n and d(i,j) <= k is at most t.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_9 (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        ∀ k : Int, 1 ≤ k → k < r.val → countLe nums k ≤ medianIndex nums.val.length := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        ∀ k : Int, 1 ≤ k → k < r.val → countLe nums k ≤ medianIndex nums.val.length) := by
  sorry

/-- Whenever the function returns a result r, there exist indices i and j with 0 <= i <= j < len(nums) such that the subarray nums[i..j] has exactly r distinct values.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_10 (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        ∃ i j : Nat, i ≤ j ∧ j < nums.val.length ∧ (numDistinct nums i j : Int) = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        ∃ i j : Nat, i ≤ j ∧ j < nums.val.length ∧ (numDistinct nums i j : Int) = r.val) := by
  sorry

/-- Let n = len(nums) and let rev be the array of length n defined by rev[k] = nums[n - 1 - k] for every 0 <= k < n. Whenever the function returns r on nums and returns r_rev on rev, we have r = r_rev.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_11 (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (rev : Slice Std.I64)
    (hrev : rev.val.length = nums.val.length)
    (hrevvals : ∀ k (hk : k < rev.val.length),
      (rev.val[k]).val = (nums.val[nums.val.length - 1 - k]).val) :
    ∀ (r r_rev : Std.I64),
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        Aegis.MedianOfUniquenessArray.median_of_uniqueness_array rev = ok r_rev →
          r.val = r_rev.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (rev : Slice Std.I64)
    (hrev : rev.val.length = nums.val.length)
    (hrevvals : ∀ k (hk : k < rev.val.length),
      (rev.val[k]).val = (nums.val[nums.val.length - 1 - k]).val), ∀ (r r_rev : Std.I64),
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        Aegis.MedianOfUniquenessArray.median_of_uniqueness_array rev = ok r_rev →
          r.val = r_rev.val) := by
  sorry

/-- Let f be any injective function whose domain is the set of values occurring in nums and whose codomain is {1, 2, ..., 100000}. Define nums' by nums'[i] = f(nums[i]) for every 0 <= i < len(nums). Whenever the function returns r on nums and returns r' on nums', we have r = r'.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_12 (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (g : Int → Int)
    (hg_inj : ∀ x ∈ vals nums, ∀ y ∈ vals nums, g x = g y → x = y)
    (hg_cod : ∀ x ∈ vals nums, 1 ≤ g x ∧ g x ≤ 100000)
    (nums' : Slice Std.I64)
    (hmap : vals nums' = (vals nums).map g) :
    ∀ (r r' : Std.I64),
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums' = ok r' →
          r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (g : Int → Int)
    (hg_inj : ∀ x ∈ vals nums, ∀ y ∈ vals nums, g x = g y → x = y)
    (hg_cod : ∀ x ∈ vals nums, 1 ≤ g x ∧ g x ≤ 100000)
    (nums' : Slice Std.I64)
    (hmap : vals nums' = (vals nums).map g), ∀ (r r' : Std.I64),
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums' = ok r' →
          r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, let n = len(nums), L = n*(n+1)/2, t = (L - 1) / 2, and let c1 be the number of subarrays nums[i..j] with 0 <= i <= j < n whose number of distinct values equals 1. Then r = 1 if and only if c1 >= t + 1.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_13 (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        (r.val = 1 ↔ medianIndex nums.val.length + 1 ≤ countEq nums 1) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        (r.val = 1 ↔ medianIndex nums.val.length + 1 ≤ countEq nums 1)) := by
  sorry

/-- Whenever the function returns a result r, if len(nums) = 4, then r = 1 if there exists an index i with 0 <= i < 3 and nums[i] = nums[i+1], and r = 2 otherwise.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
theorem spec_14 (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hlen4 : nums.val.length = 4) :
    ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        ((∃ (i : Nat) (_ : i < 3),
            (nums.val[i]'(by omega)).val = (nums.val[i + 1]'(by omega)).val) →
            r.val = 1) ∧
          (¬ (∃ (i : Nat) (_ : i < 3),
            (nums.val[i]'(by omega)).val = (nums.val[i + 1]'(by omega)).val) →
            r.val = 2) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hlen : nums.val.length ≤ 100000)
    (hbound : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
    (hlen4 : nums.val.length = 4), ∀ r : Std.I64,
      Aegis.MedianOfUniquenessArray.median_of_uniqueness_array nums = ok r →
        ((∃ (i : Nat) (_ : i < 3),
            (nums.val[i]'(by omega)).val = (nums.val[i + 1]'(by omega)).val) →
            r.val = 1) ∧
          (¬ (∃ (i : Nat) (_ : i < 3),
            (nums.val[i]'(by omega)).val = (nums.val[i + 1]'(by omega)).val) →
            r.val = 2)) := by
  sorry

end AegisSpec.MedianOfUniquenessArray
