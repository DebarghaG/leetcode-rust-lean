import Aegis.CountOfPairs.Code.Funs

/-!
# Specifications of `Aegis.CountOfPairs.count_of_pairs`

LeetCode problem `find-the-count-of-monotonic-pairs-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountOfPairs

namespace AegisSpec.CountOfPairs

def vals (s : Slice I64) : List ℤ := s.val.map (fun x => x.val)

def maxEntry (l : List ℤ) : ℕ := l.foldr (fun x m => max x.toNat m) 0

def riseAt (l : List ℤ) (i : ℕ) : ℤ :=
  (Finset.range i).sum (fun k => max 0 (l.getD (k + 1) 0 - l.getD k 0))

def riseList (l : List ℤ) : List ℤ := (List.range l.length).map (riseAt l)

def IsMonotonicPair (nums arr1 arr2 : List ℤ) : Prop :=
  arr1.length = nums.length ∧
  arr2.length = nums.length ∧
  (∀ x ∈ arr1, 0 ≤ x) ∧
  (∀ x ∈ arr2, 0 ≤ x) ∧
  List.Pairwise (· ≤ ·) arr1 ∧
  List.Pairwise (· ≥ ·) arr2 ∧
  arr1.zipWith (· + ·) arr2 = nums

noncomputable def numMonotonicPairs (nums : List ℤ) : ℕ := by
  classical
  let M := maxEntry nums
  exact ((Finset.univ : Finset ((Fin nums.length → Fin (M + 1)) ×
      (Fin nums.length → Fin (M + 1)))).filter
    (fun p => IsMonotonicPair nums
      (List.ofFn fun i => ((p.1 i : ℕ) : ℤ))
      (List.ofFn fun i => ((p.2 i : ℕ) : ℤ)))).card

/-- Whenever count_of_pairs nums returns a result r, r is the unique integer with 0 <= r < 1000000007 that is congruent modulo 1000000007 to the number of monotonic pairs for nums. A monotonic pair is an ordered pair (arr1, arr2) of arrays of length n of non-negative integers such that (1) arr1[0] <= arr1[1] <= ... <= arr1[n-1], (2) arr2[0] >= arr2[1] >= ... >= arr2[n-1], and (3) arr1[i] + arr2[i] = nums[i] for every i with 0 <= i < n. The number of such pairs is finite because arr1[i] is then an integer with 0 <= arr1[i] <= nums[i].
  Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 2000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000. -/
theorem spec_1 (nums : Slice I64) (n : ℕ) (hn : n = nums.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2000)
    (hb : ∀ i, i < n → 1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000)
    (r : I64) (h : count_of_pairs nums = ok r) :
    0 ≤ r.val ∧ r.val < 1000000007 ∧
      ∃ k : ℤ, (numMonotonicPairs (vals nums) : ℤ) = r.val + k * 1000000007 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (hn : n = nums.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2000)
    (hb : ∀ i, i < n → 1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000)
    (r : I64) (h : count_of_pairs nums = ok r), 0 ≤ r.val ∧ r.val < 1000000007 ∧
      ∃ k : ℤ, (numMonotonicPairs (vals nums) : ℤ) = r.val + k * 1000000007) := by
  sorry

/-- For every input satisfying the preconditions, count_of_pairs nums returns a result r; it does not fail, panic, overflow, or access memory out of bounds.
  Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 2000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000. -/
theorem spec_2 (nums : Slice I64) (n : ℕ) (hn : n = nums.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2000)
    (hb : ∀ i, i < n → 1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000) :
    ∃ r : I64, count_of_pairs nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (hn : n = nums.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2000)
    (hb : ∀ i, i < n → 1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000), ∃ r : I64, count_of_pairs nums = ok r) := by
  sorry

/-- Whenever count_of_pairs nums returns a result r, r <= binomial(n + max(nums), n) as an ordinary integer, where max(nums) = max{nums[i] : 0 <= i < n} and binomial(A,B) is the ordinary binomial coefficient. This holds because r is at most the unmodded count, every monotonic pair is determined by arr1, and arr1 is a non-decreasing length-n sequence with all entries in {0,1,...,max(nums)}; there are binomial(n + max(nums), n) such sequences.
  Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 2000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000. -/
theorem spec_3 (nums : Slice I64) (n : ℕ) (hn : n = nums.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2000)
    (hb : ∀ i, i < n → 1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000)
    (r : I64) (h : count_of_pairs nums = ok r) :
    r.val ≤ (Nat.choose (n + maxEntry (vals nums)) n : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (hn : n = nums.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2000)
    (hb : ∀ i, i < n → 1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000)
    (r : I64) (h : count_of_pairs nums = ok r), r.val ≤ (Nat.choose (n + maxEntry (vals nums)) n : ℤ)) := by
  sorry

/-- Whenever nums is non-decreasing and count_of_pairs nums returns r, r = binomial(n + nums[0], n) mod 1000000007.
  Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 2000, for every i with 0 <= i < n, 1 <= nums[i] <= 1000, and nums[0] <= nums[1] <= ... <= nums[n-1]. -/
theorem spec_4 (nums : Slice I64) (n : ℕ) (hn : n = nums.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2000)
    (hb : ∀ i, i < n → 1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000)
    (hmono : ∀ i j, i < j → j < n → (vals nums).getD i 0 ≤ (vals nums).getD j 0)
    (r : I64) (h : count_of_pairs nums = ok r) :
    r.val = ((Nat.choose (n + ((vals nums).getD 0 0).toNat) n % 1000000007 : ℕ) : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (hn : n = nums.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2000)
    (hb : ∀ i, i < n → 1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000)
    (hmono : ∀ i j, i < j → j < n → (vals nums).getD i 0 ≤ (vals nums).getD j 0)
    (r : I64) (h : count_of_pairs nums = ok r), r.val = ((Nat.choose (n + ((vals nums).getD 0 0).toNat) n % 1000000007 : ℕ) : ℤ)) := by
  sorry

/-- Whenever nums is non-increasing and count_of_pairs nums returns r, r = binomial(n + nums[n-1], n) mod 1000000007.
  Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 2000, for every i with 0 <= i < n, 1 <= nums[i] <= 1000, and nums[0] >= nums[1] >= ... >= nums[n-1]. -/
theorem spec_5 (nums : Slice I64) (n : ℕ) (hn : n = nums.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2000)
    (hb : ∀ i, i < n → 1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000)
    (hmono : ∀ i j, i < j → j < n → (vals nums).getD j 0 ≤ (vals nums).getD i 0)
    (r : I64) (h : count_of_pairs nums = ok r) :
    r.val = ((Nat.choose (n + ((vals nums).getD (n - 1) 0).toNat) n % 1000000007 : ℕ) : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (hn : n = nums.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2000)
    (hb : ∀ i, i < n → 1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000)
    (hmono : ∀ i j, i < j → j < n → (vals nums).getD j 0 ≤ (vals nums).getD i 0)
    (r : I64) (h : count_of_pairs nums = ok r), r.val = ((Nat.choose (n + ((vals nums).getD (n - 1) 0).toNat) n % 1000000007 : ℕ) : ℤ)) := by
  sorry

/-- Whenever count_of_pairs nums returns r, the ordinary (unmodded) number of monotonic pairs for nums is zero if and only if there exists an index i with 0 <= i < n such that sum_{k=0}^{i-1} max(0, nums[k+1] - nums[k]) > nums[i], where an empty sum (i = 0) is 0. Consequently, if such an i exists then r = 0; if no such i exists then the ordinary number of monotonic pairs is positive (and r is that positive number modulo 1000000007, which may still be 0).
  Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 2000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000. -/
theorem spec_6 (nums : Slice I64) (n : ℕ) (hn : n = nums.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2000)
    (hb : ∀ i, i < n → 1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000)
    (r : I64) (h : count_of_pairs nums = ok r) :
    (numMonotonicPairs (vals nums) = 0 ↔
        ∃ i, i < n ∧ (vals nums).getD i 0 < riseAt (vals nums) i) ∧
      ((∃ i, i < n ∧ (vals nums).getD i 0 < riseAt (vals nums) i) → r.val = 0) ∧
      ((¬ ∃ i, i < n ∧ (vals nums).getD i 0 < riseAt (vals nums) i) →
        0 < numMonotonicPairs (vals nums)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (hn : n = nums.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2000)
    (hb : ∀ i, i < n → 1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000)
    (r : I64) (h : count_of_pairs nums = ok r), (numMonotonicPairs (vals nums) = 0 ↔
        ∃ i, i < n ∧ (vals nums).getD i 0 < riseAt (vals nums) i) ∧
      ((∃ i, i < n ∧ (vals nums).getD i 0 < riseAt (vals nums) i) → r.val = 0) ∧
      ((¬ ∃ i, i < n ∧ (vals nums).getD i 0 < riseAt (vals nums) i) →
        0 < numMonotonicPairs (vals nums))) := by
  sorry

/-- Let rev(nums) be the slice of length n defined by rev(nums)[i] = nums[n-1-i] for 0 <= i < n. Whenever count_of_pairs nums returns r and count_of_pairs rev(nums) returns r_rev, r = r_rev.
  Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 2000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000. -/
theorem spec_7 (nums rev : Slice I64) (n : ℕ) (hn : n = nums.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2000)
    (hb : ∀ i, i < n → 1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000)
    (hrev : rev.val = nums.val.reverse)
    (r r_rev : I64) (h : count_of_pairs nums = ok r)
    (h' : count_of_pairs rev = ok r_rev) :
    r = r_rev := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums rev : Slice I64) (n : ℕ) (hn : n = nums.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2000)
    (hb : ∀ i, i < n → 1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000)
    (hrev : rev.val = nums.val.reverse)
    (r r_rev : I64) (h : count_of_pairs nums = ok r)
    (h' : count_of_pairs rev = ok r_rev), r = r_rev) := by
  sorry

/-- Whenever count_of_pairs nums returns a non-zero result r, define rise(i) = sum_{k=0}^{i-1} max(0, nums[k+1] - nums[k]) for 0 <= i < n, with rise(0) = 0. Then rise(i) <= nums[i] for every i, and the pair of arrays (arr1, arr2) with arr1[i] = rise(i) and arr2[i] = nums[i] - rise(i) is a monotonic pair for nums.
  Preconditions: nums is a slice of 64-bit integers, n = len(nums), 1 <= n <= 2000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000. -/
theorem spec_8 (nums : Slice I64) (n : ℕ) (hn : n = nums.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2000)
    (hb : ∀ i, i < n → 1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000)
    (r : I64) (h : count_of_pairs nums = ok r) (hr : r.val ≠ 0) :
    (∀ i, i < n → riseAt (vals nums) i ≤ (vals nums).getD i 0) ∧
      IsMonotonicPair (vals nums) (riseList (vals nums))
        ((vals nums).zipWith (fun x y => x - y) (riseList (vals nums))) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (hn : n = nums.val.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2000)
    (hb : ∀ i, i < n → 1 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000)
    (r : I64) (h : count_of_pairs nums = ok r) (hr : r.val ≠ 0), (∀ i, i < n → riseAt (vals nums) i ≤ (vals nums).getD i 0) ∧
      IsMonotonicPair (vals nums) (riseList (vals nums))
        ((vals nums).zipWith (fun x y => x - y) (riseList (vals nums)))) := by
  sorry

end AegisSpec.CountOfPairs
