import Aegis.MinimumDifference.Code.Funs

/-!
# Specifications of `Aegis.MinimumDifference.minimum_difference`

LeetCode problem `minimum-difference-in-sums-after-removal-of-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumDifference

namespace AegisSpec.MinimumDifference

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def entry (nums : Slice Std.I64) (i : Nat) : Int :=
  match nums.val[i]? with
  | some x => x.val
  | none => 0

def sumAt (nums : Slice Std.I64) (l : List Nat) : Int :=
  (l.map (entry nums)).sum

def rangeSum (nums : Slice Std.I64) (lo hi : Nat) : Int :=
  (((vals nums).drop lo).take (hi - lo)).sum

def D (nums : Slice Std.I64) (n : Nat) (l : List Nat) : Int :=
  sumAt nums (l.take n) - sumAt nums (l.drop n)

def IsIndexSeq (nums : Slice Std.I64) (n : Nat) (l : List Nat) : Prop :=
  l.length = 2 * n ∧ l.Pairwise (· < ·) ∧ ∀ i ∈ l, i < nums.val.length

def sumSmallest (k : Nat) (l : List Int) : Int :=
  ((List.insertionSort (· ≤ ·) l).take k).sum

def sumLargest (k : Nat) (l : List Int) : Int :=
  (((List.insertionSort (· ≤ ·) l).reverse).take k).sum

def prefixSmallestSum (nums : Slice Std.I64) (n j : Nat) : Int :=
  sumSmallest n ((vals nums).take j)

def suffixLargestSum (nums : Slice Std.I64) (n j : Nat) : Int :=
  sumLargest n ((vals nums).drop j)

def sliceMin (nums : Slice Std.I64) : Int := (vals nums).min?.getD 0

def sliceMax (nums : Slice Std.I64) : Int := (vals nums).max?.getD 0

/-- minimum_difference nums returns Result.ok r, and r is the minimum of the set of all integers D(i) = (sum_{k=0}^{n-1} nums[i_k]) - (sum_{k=n}^{2n-1} nums[i_k]), where i_0 < i_1 < ... < i_{2n-1} ranges over all strictly increasing sequences of 2n indices with 0 <= i_k < len(nums). In symbols, r = min { D(i) | 0 <= i_0 < ... < i_{2n-1} < len(nums) }.
  Preconditions: Let n = len(nums)/3. The slice nums satisfies len(nums) = 3*n, 1 <= n <= 100000, and 1 <= nums[i] <= 100000 for every i with 0 <= i < len(nums). -/
theorem spec_1 (nums : Slice Std.I64) (n : Nat)
    (hn_len : nums.val.length = 3 * n) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000) :
    ∃ r : Std.I64, minimum_difference nums = ok r ∧
      (∀ l : List Nat, IsIndexSeq nums n l → r.val ≤ D nums n l) ∧
      (∃ l : List Nat, IsIndexSeq nums n l ∧ D nums n l = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : nums.val.length = 3 * n) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000), ∃ r : Std.I64, minimum_difference nums = ok r ∧
      (∀ l : List Nat, IsIndexSeq nums n l → r.val ≤ D nums n l) ∧
      (∃ l : List Nat, IsIndexSeq nums n l ∧ D nums n l = r.val)) := by
  sorry

/-- Under the preconditions, minimum_difference nums returns a result: there exists an i64 r such that the result is Result.ok r. It does not overflow, panic, or otherwise fail.
  Preconditions: Let n = len(nums)/3. The slice nums satisfies len(nums) = 3*n, 1 <= n <= 100000, and 1 <= nums[i] <= 100000 for every i with 0 <= i < len(nums). -/
theorem spec_2 (nums : Slice Std.I64) (n : Nat)
    (hn_len : nums.val.length = 3 * n) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000) :
    ∃ r : Std.I64, minimum_difference nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : nums.val.length = 3 * n) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000), ∃ r : Std.I64, minimum_difference nums = ok r) := by
  sorry

/-- Whenever minimum_difference nums returns Result.ok r, for every strictly increasing sequence 0 <= i_0 < i_1 < ... < i_{2n-1} < len(nums), we have r <= (sum_{k=0}^{n-1} nums[i_k]) - (sum_{k=n}^{2n-1} nums[i_k]).
  Preconditions: Let n = len(nums)/3. The slice nums satisfies len(nums) = 3*n, 1 <= n <= 100000, and 1 <= nums[i] <= 100000 for every i with 0 <= i < len(nums). -/
theorem spec_3 (nums : Slice Std.I64) (n : Nat)
    (hn_len : nums.val.length = 3 * n) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000)
    (r : Std.I64) (hr : minimum_difference nums = ok r) :
    ∀ l : List Nat, IsIndexSeq nums n l → r.val ≤ D nums n l := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : nums.val.length = 3 * n) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000)
    (r : Std.I64) (hr : minimum_difference nums = ok r), ∀ l : List Nat, IsIndexSeq nums n l → r.val ≤ D nums n l) := by
  sorry

/-- Whenever minimum_difference nums returns Result.ok r, there exists a strictly increasing sequence 0 <= i_0 < i_1 < ... < i_{2n-1} < len(nums) such that (sum_{k=0}^{n-1} nums[i_k]) - (sum_{k=n}^{2n-1} nums[i_k]) = r.
  Preconditions: Let n = len(nums)/3. The slice nums satisfies len(nums) = 3*n, 1 <= n <= 100000, and 1 <= nums[i] <= 100000 for every i with 0 <= i < len(nums). -/
theorem spec_4 (nums : Slice Std.I64) (n : Nat)
    (hn_len : nums.val.length = 3 * n) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000)
    (r : Std.I64) (hr : minimum_difference nums = ok r) :
    ∃ l : List Nat, IsIndexSeq nums n l ∧ D nums n l = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : nums.val.length = 3 * n) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000)
    (r : Std.I64) (hr : minimum_difference nums = ok r), ∃ l : List Nat, IsIndexSeq nums n l ∧ D nums n l = r.val) := by
  sorry

/-- Whenever minimum_difference nums returns Result.ok r, let mn = min_{0 <= i < len(nums)} nums[i] and mx = max_{0 <= i < len(nums)} nums[i]. Then -n*(mx-mn) <= r <= n*(mx-mn).
  Preconditions: Let n = len(nums)/3. The slice nums satisfies len(nums) = 3*n, 1 <= n <= 100000, and 1 <= nums[i] <= 100000 for every i with 0 <= i < len(nums). -/
theorem spec_5 (nums : Slice Std.I64) (n : Nat)
    (hn_len : nums.val.length = 3 * n) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000)
    (r : Std.I64) (hr : minimum_difference nums = ok r) :
    -((n : Int) * (sliceMax nums - sliceMin nums)) ≤ r.val ∧
      r.val ≤ (n : Int) * (sliceMax nums - sliceMin nums) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : nums.val.length = 3 * n) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000)
    (r : Std.I64) (hr : minimum_difference nums = ok r), -((n : Int) * (sliceMax nums - sliceMin nums)) ≤ r.val ∧
      r.val ≤ (n : Int) * (sliceMax nums - sliceMin nums)) := by
  sorry

/-- Whenever minimum_difference nums returns Result.ok r, r <= (sum_{i=0}^{n-1} nums[i]) - (sum_{i=2n}^{3n-1} nums[i]).
  Preconditions: Let n = len(nums)/3. The slice nums satisfies len(nums) = 3*n, 1 <= n <= 100000, and 1 <= nums[i] <= 100000 for every i with 0 <= i < len(nums). -/
theorem spec_6 (nums : Slice Std.I64) (n : Nat)
    (hn_len : nums.val.length = 3 * n) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000)
    (r : Std.I64) (hr : minimum_difference nums = ok r) :
    r.val ≤ rangeSum nums 0 n - rangeSum nums (2 * n) (3 * n) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : nums.val.length = 3 * n) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000)
    (r : Std.I64) (hr : minimum_difference nums = ok r), r.val ≤ rangeSum nums 0 n - rangeSum nums (2 * n) (3 * n)) := by
  sorry

/-- Whenever minimum_difference nums returns Result.ok r, r = 0.
  Preconditions: Let n = len(nums)/3. The slice nums satisfies len(nums) = 3*n, 1 <= n <= 100000, and 1 <= nums[i] <= 100000 for every i with 0 <= i < len(nums). Additionally, there is an integer c such that nums[i] = c for every i with 0 <= i < len(nums). -/
theorem spec_7 (nums : Slice Std.I64) (n : Nat)
    (hn_len : nums.val.length = 3 * n) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000)
    (c : Int) (hc : ∀ i : Nat, i < nums.val.length → entry nums i = c)
    (r : Std.I64) (hr : minimum_difference nums = ok r) :
    r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : nums.val.length = 3 * n) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000)
    (c : Int) (hc : ∀ i : Nat, i < nums.val.length → entry nums i = c)
    (r : Std.I64) (hr : minimum_difference nums = ok r), r.val = 0) := by
  sorry

/-- Whenever minimum_difference nums returns Result.ok r, r = (sum_{i=0}^{n-1} nums[i]) - (sum_{i=2n}^{3n-1} nums[i]).
  Preconditions: Let n = len(nums)/3. The slice nums satisfies len(nums) = 3*n, 1 <= n <= 100000, and 1 <= nums[i] <= 100000 for every i with 0 <= i < len(nums). Additionally, nums is nondecreasing: nums[0] <= nums[1] <= ... <= nums[len(nums)-1]. -/
theorem spec_8 (nums : Slice Std.I64) (n : Nat)
    (hn_len : nums.val.length = 3 * n) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000)
    (h_sorted : ∀ i j : Nat, i ≤ j → j < nums.val.length → entry nums i ≤ entry nums j)
    (r : Std.I64) (hr : minimum_difference nums = ok r) :
    r.val = rangeSum nums 0 n - rangeSum nums (2 * n) (3 * n) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : nums.val.length = 3 * n) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000)
    (h_sorted : ∀ i j : Nat, i ≤ j → j < nums.val.length → entry nums i ≤ entry nums j)
    (r : Std.I64) (hr : minimum_difference nums = ok r), r.val = rangeSum nums 0 n - rangeSum nums (2 * n) (3 * n)) := by
  sorry

/-- Whenever minimum_difference nums returns Result.ok r and minimum_difference nums' returns Result.ok r', we have r' = r.
  Preconditions: Let nums and nums' be two slices of the same length, both satisfying: with n = len(nums)/3 = len(nums')/3, len(nums) = 3*n, 1 <= n <= 100000, and all entries of both slices lie in [1, 100000]. Let c be an integer such that nums'[i] = nums[i] + c for every i with 0 <= i < len(nums). -/
theorem spec_9 (nums nums' : Slice Std.I64) (n : Nat) (c : Int)
    (hn_len : nums.val.length = 3 * n) (hn_len' : nums'.val.length = 3 * n)
    (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000)
    (h_lo' : ∀ i : Nat, i < nums'.val.length → 1 ≤ entry nums' i)
    (h_hi' : ∀ i : Nat, i < nums'.val.length → entry nums' i ≤ 100000)
    (hc : ∀ i : Nat, i < nums.val.length → entry nums' i = entry nums i + c)
    (r r' : Std.I64) (hr : minimum_difference nums = ok r)
    (hr' : minimum_difference nums' = ok r') :
    r'.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (n : Nat) (c : Int)
    (hn_len : nums.val.length = 3 * n) (hn_len' : nums'.val.length = 3 * n)
    (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000)
    (h_lo' : ∀ i : Nat, i < nums'.val.length → 1 ≤ entry nums' i)
    (h_hi' : ∀ i : Nat, i < nums'.val.length → entry nums' i ≤ 100000)
    (hc : ∀ i : Nat, i < nums.val.length → entry nums' i = entry nums i + c)
    (r r' : Std.I64) (hr : minimum_difference nums = ok r)
    (hr' : minimum_difference nums' = ok r'), r'.val = r.val) := by
  sorry

/-- Whenever minimum_difference nums returns Result.ok r and minimum_difference nums' returns Result.ok r', we have r' = c * r.
  Preconditions: Let nums and nums' be two slices of the same length, both satisfying: with n = len(nums)/3 = len(nums')/3, len(nums) = 3*n, 1 <= n <= 100000, and all entries of both slices lie in [1, 100000]. Let c be a positive integer such that nums'[i] = c * nums[i] for every i with 0 <= i < len(nums). -/
theorem spec_10 (nums nums' : Slice Std.I64) (n : Nat) (c : Int)
    (hn_len : nums.val.length = 3 * n) (hn_len' : nums'.val.length = 3 * n)
    (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000)
    (h_lo' : ∀ i : Nat, i < nums'.val.length → 1 ≤ entry nums' i)
    (h_hi' : ∀ i : Nat, i < nums'.val.length → entry nums' i ≤ 100000)
    (hc_pos : 0 < c)
    (hc : ∀ i : Nat, i < nums.val.length → entry nums' i = c * entry nums i)
    (r r' : Std.I64) (hr : minimum_difference nums = ok r)
    (hr' : minimum_difference nums' = ok r') :
    r'.val = c * r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (n : Nat) (c : Int)
    (hn_len : nums.val.length = 3 * n) (hn_len' : nums'.val.length = 3 * n)
    (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000)
    (h_lo' : ∀ i : Nat, i < nums'.val.length → 1 ≤ entry nums' i)
    (h_hi' : ∀ i : Nat, i < nums'.val.length → entry nums' i ≤ 100000)
    (hc_pos : 0 < c)
    (hc : ∀ i : Nat, i < nums.val.length → entry nums' i = c * entry nums i)
    (r r' : Std.I64) (hr : minimum_difference nums = ok r)
    (hr' : minimum_difference nums' = ok r'), r'.val = c * r.val) := by
  sorry

/-- Whenever minimum_difference nums returns Result.ok r, for each integer j with n <= j <= 2n, let P(j) be the sum of the n smallest elements, with multiplicity, of the prefix nums[0..j-1], and let Q(j) be the sum of the n largest elements, with multiplicity, of the suffix nums[j..3n-1]. Then r = min_{n <= j <= 2n} (P(j) - Q(j)).
  Preconditions: Let n = len(nums)/3. The slice nums satisfies len(nums) = 3*n, 1 <= n <= 100000, and 1 <= nums[i] <= 100000 for every i with 0 <= i < len(nums). -/
theorem spec_11 (nums : Slice Std.I64) (n : Nat)
    (hn_len : nums.val.length = 3 * n) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000)
    (r : Std.I64) (hr : minimum_difference nums = ok r) :
    (∀ j : Nat, n ≤ j → j ≤ 2 * n →
        r.val ≤ prefixSmallestSum nums n j - suffixLargestSum nums n j) ∧
      (∃ j : Nat, n ≤ j ∧ j ≤ 2 * n ∧
        prefixSmallestSum nums n j - suffixLargestSum nums n j = r.val) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : nums.val.length = 3 * n) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (h_lo : ∀ i : Nat, i < nums.val.length → 1 ≤ entry nums i)
    (h_hi : ∀ i : Nat, i < nums.val.length → entry nums i ≤ 100000)
    (r : Std.I64) (hr : minimum_difference nums = ok r), (∀ j : Nat, n ≤ j → j ≤ 2 * n →
        r.val ≤ prefixSmallestSum nums n j - suffixLargestSum nums n j) ∧
      (∃ j : Nat, n ≤ j ∧ j ≤ 2 * n ∧
        prefixSmallestSum nums n j - suffixLargestSum nums n j = r.val)) := by
  sorry

end AegisSpec.MinimumDifference
