import Aegis.SubsequenceSumOr.Code.Funs

/-!
# Specifications of `Aegis.SubsequenceSumOr.subsequence_sum_or`

LeetCode problem `bitwise-or-of-all-subsequence-sums`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.SubsequenceSumOr

namespace AegisSpec.SubsequenceSumOr

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def total (nums : Slice Std.I64) : Int := (vals nums).sum

def subsetSum (nums : Slice Std.I64) (S : Finset ℕ) : Int :=
  ∑ i ∈ S, (vals nums).getD i 0

def nthBit (x : Int) (b : ℕ) : Int := (x / 2 ^ b) % 2

def ior (a b : Int) : Int := Int.ofNat (a.toNat ||| b.toNat)

/-- Let T = sum_{i=0}^{n-1} nums[i]. For each subset S of the index set {0,...,n-1}, define sum(S) = sum_{i in S} nums[i], with the empty subset giving 0. The function returns a result r such that r >= 0 and, for every integer b with 0 <= b < 63, the b-th bit of r (that is, floor(r / 2^b) mod 2) is 1 if and only if there exists a subset S of {0,...,n-1} for which the b-th bit of sum(S) is 1. Equivalently, r is the bitwise OR of all values sum(S) over all subsets S of indices.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every integer i with 0 <= i < n, 0 <= nums[i] <= 1000000000. Under these constraints the total sum of nums is at most 10^14, so all subset sums fit in signed 64-bit integers. -/
theorem spec_1 (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000) :
    ∃ r : Std.I64, subsequence_sum_or nums = ok r ∧ 0 ≤ r.val ∧
      ∀ b : ℕ, b < 63 →
        (nthBit r.val b = 1 ↔
          ∃ S : Finset ℕ, S ⊆ Finset.range nums.val.length ∧
            nthBit (subsetSum nums S) b = 1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000), ∃ r : Std.I64, subsequence_sum_or nums = ok r ∧ 0 ≤ r.val ∧
      ∀ b : ℕ, b < 63 →
        (nthBit r.val b = 1 ↔
          ∃ S : Finset ℕ, S ⊆ Finset.range nums.val.length ∧
            nthBit (subsetSum nums S) b = 1)) := by
  sorry

/-- Whenever the input satisfies the preconditions, the function returns a result r; it never fails (no panic, no out-of-bounds access, and no signed 64-bit overflow).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every integer i with 0 <= i < n, 0 <= nums[i] <= 1000000000. Under these constraints the total sum of nums is at most 10^14, so all subset sums fit in signed 64-bit integers. -/
theorem spec_2 (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000) :
    ∃ r : Std.I64, subsequence_sum_or nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000), ∃ r : Std.I64, subsequence_sum_or nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every integer i with 0 <= i < n, 0 <= nums[i] <= 1000000000. Under these constraints the total sum of nums is at most 10^14, so all subset sums fit in signed 64-bit integers. -/
theorem spec_3 (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000) :
    ∀ r : Std.I64, subsequence_sum_or nums = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000), ∀ r : Std.I64, subsequence_sum_or nums = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer b with 0 <= b < 63, if 2^b > T where T = sum_{i=0}^{n-1} nums[i], then the b-th bit of r is 0.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every integer i with 0 <= i < n, 0 <= nums[i] <= 1000000000. Under these constraints the total sum of nums is at most 10^14, so all subset sums fit in signed 64-bit integers. -/
theorem spec_4 (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000) :
    ∀ r : Std.I64, subsequence_sum_or nums = ok r →
      ∀ b : ℕ, b < 63 → (2 : Int) ^ b > total nums → nthBit r.val b = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000), ∀ r : Std.I64, subsequence_sum_or nums = ok r →
      ∀ b : ℕ, b < 63 → (2 : Int) ^ b > total nums → nthBit r.val b = 0) := by
  sorry

/-- Whenever the function returns a result r, if nums[i] = 0 for every i with 0 <= i < n, then r = 0.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every integer i with 0 <= i < n, 0 <= nums[i] <= 1000000000. Under these constraints the total sum of nums is at most 10^14, so all subset sums fit in signed 64-bit integers. -/
theorem spec_5 (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000) :
    ∀ r : Std.I64, subsequence_sum_or nums = ok r →
      (∀ i : ℕ, i < nums.val.length → (vals nums).getD i 0 = 0) → r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000), ∀ r : Std.I64, subsequence_sum_or nums = ok r →
      (∀ i : ℕ, i < nums.val.length → (vals nums).getD i 0 = 0) → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, if n = 1, then r = nums[0].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every integer i with 0 <= i < n, 0 <= nums[i] <= 1000000000. Under these constraints the total sum of nums is at most 10^14, so all subset sums fit in signed 64-bit integers. -/
theorem spec_6 (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000) :
    ∀ r : Std.I64, subsequence_sum_or nums = ok r →
      nums.val.length = 1 → r.val = (vals nums).getD 0 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000), ∀ r : Std.I64, subsequence_sum_or nums = ok r →
      nums.val.length = 1 → r.val = (vals nums).getD 0 0) := by
  sorry

/-- Whenever the function returns a result r, for every subset S of {0,...,n-1}, if sum(S) = sum_{i in S} nums[i], then (sum(S) | r) = r; equivalently, every bit that is 1 in sum(S) is also 1 in r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every integer i with 0 <= i < n, 0 <= nums[i] <= 1000000000. Under these constraints the total sum of nums is at most 10^14, so all subset sums fit in signed 64-bit integers. -/
theorem spec_7 (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000) :
    ∀ r : Std.I64, subsequence_sum_or nums = ok r →
      ∀ S : Finset ℕ, S ⊆ Finset.range nums.val.length →
        ∀ b : ℕ, b < 63 → nthBit (subsetSum nums S) b = 1 → nthBit r.val b = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000), ∀ r : Std.I64, subsequence_sum_or nums = ok r →
      ∀ S : Finset ℕ, S ⊆ Finset.range nums.val.length →
        ∀ b : ℕ, b < 63 → nthBit (subsetSum nums S) b = 1 → nthBit r.val b = 1) := by
  sorry

/-- Whenever the function returns a result r, for every integer b with 0 <= b < 63, if the b-th bit of r is 1, then there exists a subset S of {0,...,n-1} such that the b-th bit of sum(S) = sum_{i in S} nums[i] is 1.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every integer i with 0 <= i < n, 0 <= nums[i] <= 1000000000. Under these constraints the total sum of nums is at most 10^14, so all subset sums fit in signed 64-bit integers. -/
theorem spec_8 (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000) :
    ∀ r : Std.I64, subsequence_sum_or nums = ok r →
      ∀ b : ℕ, b < 63 → nthBit r.val b = 1 →
        ∃ S : Finset ℕ, S ⊆ Finset.range nums.val.length ∧
          nthBit (subsetSum nums S) b = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000), ∀ r : Std.I64, subsequence_sum_or nums = ok r →
      ∀ b : ℕ, b < 63 → nthBit r.val b = 1 →
        ∃ S : Finset ℕ, S ⊆ Finset.range nums.val.length ∧
          nthBit (subsetSum nums S) b = 1) := by
  sorry

/-- Whenever the function returns a result r, the 0-th bit of r is 1 if and only if there exists an index i with 0 <= i < n such that nums[i] is odd (nums[i] mod 2 = 1).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every integer i with 0 <= i < n, 0 <= nums[i] <= 1000000000. Under these constraints the total sum of nums is at most 10^14, so all subset sums fit in signed 64-bit integers. -/
theorem spec_9 (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000) :
    ∀ r : Std.I64, subsequence_sum_or nums = ok r →
      (nthBit r.val 0 = 1 ↔
        ∃ i : ℕ, i < nums.val.length ∧ (vals nums).getD i 0 % 2 = 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000), ∀ r : Std.I64, subsequence_sum_or nums = ok r →
      (nthBit r.val 0 = 1 ↔
        ∃ i : ℕ, i < nums.val.length ∧ (vals nums).getD i 0 % 2 = 1)) := by
  sorry

/-- Whenever the function returns a result r, for every integer k with 1 <= k < 63, if every nums[i] is divisible by 2^k (that is, nums[i] mod 2^k = 0 for all i with 0 <= i < n), then r mod 2^k = 0.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every integer i with 0 <= i < n, 0 <= nums[i] <= 1000000000. Under these constraints the total sum of nums is at most 10^14, so all subset sums fit in signed 64-bit integers. -/
theorem spec_10 (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000) :
    ∀ r : Std.I64, subsequence_sum_or nums = ok r →
      ∀ k : ℕ, 1 ≤ k → k < 63 →
        (∀ i : ℕ, i < nums.val.length → (vals nums).getD i 0 % 2 ^ k = 0) →
          r.val % 2 ^ k = 0 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000), ∀ r : Std.I64, subsequence_sum_or nums = ok r →
      ∀ k : ℕ, 1 ≤ k → k < 63 →
        (∀ i : ℕ, i < nums.val.length → (vals nums).getD i 0 % 2 ^ k = 0) →
          r.val % 2 ^ k = 0) := by
  sorry

/-- Whenever the function returns a result r, for every index j with 0 <= j < n and nums[j] = 0, and for every integer b with 0 <= b < 63, the b-th bit of r is 1 if and only if there exists a subset S of {0,...,n-1} \ {j} such that the b-th bit of sum_{i in S} nums[i] is 1.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every integer i with 0 <= i < n, 0 <= nums[i] <= 1000000000. Under these constraints the total sum of nums is at most 10^14, so all subset sums fit in signed 64-bit integers. -/
theorem spec_11 (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000) :
    ∀ r : Std.I64, subsequence_sum_or nums = ok r →
      ∀ j : ℕ, j < nums.val.length → (vals nums).getD j 0 = 0 →
        ∀ b : ℕ, b < 63 →
          (nthBit r.val b = 1 ↔
            ∃ S : Finset ℕ, S ⊆ Finset.range nums.val.length ∧ j ∉ S ∧
              nthBit (subsetSum nums S) b = 1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000), ∀ r : Std.I64, subsequence_sum_or nums = ok r →
      ∀ j : ℕ, j < nums.val.length → (vals nums).getD j 0 = 0 →
        ∀ b : ℕ, b < 63 →
          (nthBit r.val b = 1 ↔
            ∃ S : Finset ℕ, S ⊆ Finset.range nums.val.length ∧ j ∉ S ∧
              nthBit (subsetSum nums S) b = 1)) := by
  sorry

/-- Whenever the function returns a result r, if n = 2, then r = nums[0] | nums[1] | (nums[0] + nums[1]), where | denotes bitwise OR.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every integer i with 0 <= i < n, 0 <= nums[i] <= 1000000000. Under these constraints the total sum of nums is at most 10^14, so all subset sums fit in signed 64-bit integers. -/
theorem spec_12 (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000) :
    ∀ r : Std.I64, subsequence_sum_or nums = ok r →
      nums.val.length = 2 →
        r.val = ior (ior ((vals nums).getD 0 0) ((vals nums).getD 1 0))
          ((vals nums).getD 0 0 + (vals nums).getD 1 0) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000), ∀ r : Std.I64, subsequence_sum_or nums = ok r →
      nums.val.length = 2 →
        r.val = ior (ior ((vals nums).getD 0 0) ((vals nums).getD 1 0))
          ((vals nums).getD 0 0 + (vals nums).getD 1 0)) := by
  sorry

/-- Let p be any permutation of {0,...,n-1}, and define nums' by nums'[i] = nums[p(i)]. If the function returns r on nums and returns r' on nums', then r = r'. Equivalently, the result depends only on the multiset of values in nums, not on their order.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and for every integer i with 0 <= i < n, 0 <= nums[i] <= 1000000000. -/
theorem spec_13 (nums nums' : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hperm : (vals nums).Perm (vals nums')) :
    ∀ r r' : Std.I64, subsequence_sum_or nums = ok r →
      subsequence_sum_or nums' = ok r' → r.val = r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hbdd : ∀ i : ℕ, i < nums.val.length →
      0 ≤ (vals nums).getD i 0 ∧ (vals nums).getD i 0 ≤ 1000000000)
    (hperm : (vals nums).Perm (vals nums')), ∀ r r' : Std.I64, subsequence_sum_or nums = ok r →
      subsequence_sum_or nums' = ok r' → r.val = r'.val) := by
  sorry

end AegisSpec.SubsequenceSumOr
