import Aegis.MinimumOperations.Code.Funs

/-!
# Specifications of `Aegis.MinimumOperations.minimum_operations`

LeetCode problem `merge-operations-to-turn-array-into-a-palindrome`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumOperations

namespace AegisSpec.MinimumOperations

def entry (nums : Slice Std.I64) (i : ℕ) (hi : i < nums.val.length) : ℤ := (nums.val[i]).val

def entries (nums : Slice Std.I64) : List ℤ := nums.val.map fun x => x.val

def totalSum (nums : Slice Std.I64) : ℤ := (entries nums).sum

def ValidIn (nums : Slice Std.I64) : Prop :=
  1 ≤ nums.val.length ∧ nums.val.length ≤ 100000 ∧
    ∀ i (hi : i < nums.val.length), 1 ≤ entry nums i hi ∧ entry nums i hi ≤ 1000000

def IsPalindrome (nums : Slice Std.I64) : Prop :=
  ∀ i (hi : i < nums.val.length),
    entry nums i hi = entry nums (nums.val.length - 1 - i) (by omega)

def segSum (nums : Slice Std.I64) (p q : ℕ) : ℤ :=
  ((nums.val.drop p).take (q - p)).foldr (fun x acc => x.val + acc) 0

def IsBlockPartition (n m : ℕ) (b : Fin (m + 1) → ℕ) : Prop :=
  b 0 = 0 ∧ b (Fin.last m) = n ∧ ∀ j : Fin m, b j.castSucc < b j.succ

def IsPalindromicPartition (nums : Slice Std.I64) (m : ℕ) (b : Fin (m + 1) → ℕ) : Prop :=
  IsBlockPartition nums.val.length m b ∧
    ∀ j : Fin m,
      segSum nums (b j.castSucc) (b j.succ) =
        segSum nums (b (Fin.rev j).castSucc) (b (Fin.rev j).succ)

def HasPalindromePartition (nums : Slice Std.I64) (m : ℕ) : Prop :=
  ∃ b : Fin (m + 1) → ℕ, IsPalindromicPartition nums m b

noncomputable def maxPalindromicBlocks (nums : Slice Std.I64) : ℕ :=
  letI := Classical.decPred (fun m => 1 ≤ m ∧ HasPalindromePartition nums m)
  Nat.findGreatest (fun m => 1 ≤ m ∧ HasPalindromePartition nums m) nums.val.length

lemma val_length_le_max (nums : Slice Std.I64) : nums.val.length ≤ Usize.max := by
  have h2 : nums.val.length = nums.leng := Aeneas.Data.ListN.ListN_length nums.list
  have h1 := nums.bound
  omega

def mkSlice (l : List Std.I64) (h : l.length ≤ Usize.max) : Slice Std.I64 :=
  ⟨l.length, Aeneas.Data.ListN.ListN.fromList l, h⟩

@[simp]
lemma mkSlice_val (l : List Std.I64) (h : l.length ≤ Usize.max) : (mkSlice l h).val = l := by
  simp only [mkSlice, Slice.val]
  exact Aeneas.Data.ListN.ListN.from_to_inverse

def reverseNums (nums : Slice Std.I64) : Slice Std.I64 :=
  mkSlice nums.val.reverse (by
    rw [List.length_reverse]
    exact val_length_le_max nums)

def innerNums (nums : Slice Std.I64) : Slice Std.I64 :=
  mkSlice ((nums.val.drop 1).take (nums.val.length - 2)) (by
    have h1 : (nums.val.drop 1).length ≤ Usize.max := by
      rw [List.length_drop]
      have h := val_length_le_max nums
      omega
    refine le_trans ?_ h1
    rw [List.length_take]
    exact Nat.min_le_right _ _)

def scaleNums (c : ℤ) (nums : Slice Std.I64) : Slice Std.I64 :=
  mkSlice (nums.val.map fun x => (⟨BitVec.ofInt 64 (c * x.val)⟩ : Std.I64))
    (by rw [List.length_map]; exact val_length_le_max nums)

/-- Let n = len(nums). A partition of nums into m contiguous nonempty blocks consists of indices 0 = b_0 < b_1 < ... < b_m = n; its block sums are S_j = nums[b_j] + nums[b_j+1] + ... + nums[b_{j+1}-1] for 0 <= j < m. Such a partition is palindromic if S_j = S_{m-1-j} for every j with 0 <= j < m. Let m* be the largest m in {1, 2, ..., n} for which a palindromic partition of nums into m blocks exists (m = 1 always works, so m* is well-defined). The function returns a result r and r = n - m*.
  Preconditions: nums is a nonempty array with len(nums) <= 100000, and 1 <= nums[i] <= 1000000 for every i with 0 <= i < len(nums). -/
theorem spec_1 (nums : Slice Std.I64) (h : ValidIn nums) :
    ∃ r : Std.I64, minimum_operations nums = ok r ∧
      r.val = (nums.val.length : ℤ) - (maxPalindromicBlocks nums : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidIn nums), ∃ r : Std.I64, minimum_operations nums = ok r ∧
      r.val = (nums.val.length : ℤ) - (maxPalindromicBlocks nums : ℤ)) := by
  sorry

/-- The function returns a result r and does not fail (no arithmetic overflow, no out-of-bounds access, no panic) for every input satisfying the preconditions.
  Preconditions: nums is a nonempty array with len(nums) <= 100000, and 1 <= nums[i] <= 1000000 for every i with 0 <= i < len(nums). -/
theorem spec_2 (nums : Slice Std.I64) (h : ValidIn nums) :
    ∃ r : Std.I64, minimum_operations nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidIn nums), ∃ r : Std.I64, minimum_operations nums = ok r) := by
  sorry

/-- The function returns a result r and 0 <= r <= n - 1, where n = len(nums).
  Preconditions: nums is a nonempty array with len(nums) <= 100000, and 1 <= nums[i] <= 1000000 for every i with 0 <= i < len(nums). -/
theorem spec_3 (nums : Slice Std.I64) (h : ValidIn nums) :
    ∃ r : Std.I64, minimum_operations nums = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidIn nums), ∃ r : Std.I64, minimum_operations nums = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) - 1) := by
  sorry

/-- The function returns a result r and r = 0 if and only if nums is a palindrome, i.e., nums[i] = nums[n-1-i] for every i with 0 <= i < n (where n = len(nums)).
  Preconditions: nums is a nonempty array with len(nums) <= 100000, and 1 <= nums[i] <= 1000000 for every i with 0 <= i < len(nums). -/
theorem spec_4 (nums : Slice Std.I64) (h : ValidIn nums) :
    ∃ r : Std.I64, minimum_operations nums = ok r ∧ (r.val = 0 ↔ IsPalindrome nums) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidIn nums), ∃ r : Std.I64, minimum_operations nums = ok r ∧ (r.val = 0 ↔ IsPalindrome nums)) := by
  sorry

/-- The function returns a result r and there exists a palindromic partition of nums into exactly n - r contiguous nonempty blocks: there are indices 0 = b_0 < b_1 < ... < b_m = n with m = n - r such that the block sums S_j = nums[b_j] + ... + nums[b_{j+1}-1] satisfy S_j = S_{m-1-j} for every 0 <= j < m.
  Preconditions: nums is a nonempty array with len(nums) <= 100000, and 1 <= nums[i] <= 1000000 for every i with 0 <= i < len(nums). -/
theorem spec_5 (nums : Slice Std.I64) (h : ValidIn nums) :
    ∃ r : Std.I64, minimum_operations nums = ok r ∧
      ∃ m : ℕ, (m : ℤ) = (nums.val.length : ℤ) - r.val ∧ HasPalindromePartition nums m := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidIn nums), ∃ r : Std.I64, minimum_operations nums = ok r ∧
      ∃ m : ℕ, (m : ℤ) = (nums.val.length : ℤ) - r.val ∧ HasPalindromePartition nums m) := by
  sorry

/-- The function returns a result r and, for every integer k with n - r < k <= n, there is no palindromic partition of nums into k contiguous nonempty blocks: for every choice of indices 0 = b_0 < b_1 < ... < b_k = n (where n = len(nums)), the block sums S_j = nums[b_j] + ... + nums[b_{j+1}-1] do not satisfy S_j = S_{k-1-j} for all 0 <= j < k.
  Preconditions: nums is a nonempty array with len(nums) <= 100000, and 1 <= nums[i] <= 1000000 for every i with 0 <= i < len(nums). -/
theorem spec_6 (nums : Slice Std.I64) (h : ValidIn nums) :
    ∃ r : Std.I64, minimum_operations nums = ok r ∧
      ∀ k : ℕ, (nums.val.length : ℤ) - r.val < (k : ℤ) → k ≤ nums.val.length →
        ¬ HasPalindromePartition nums k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidIn nums), ∃ r : Std.I64, minimum_operations nums = ok r ∧
      ∀ k : ℕ, (nums.val.length : ℤ) - r.val < (k : ℤ) → k ≤ nums.val.length →
        ¬ HasPalindromePartition nums k) := by
  sorry

/-- Let n = len(nums) and let reverse(nums) be the array with reverse(nums)[i] = nums[n-1-i]. The function returns a result r on nums and the function returns the same result r on reverse(nums); equivalently minimum_operations(nums) = minimum_operations(reverse(nums)).
  Preconditions: nums is a nonempty array with len(nums) <= 100000, and 1 <= nums[i] <= 1000000 for every i with 0 <= i < len(nums). -/
theorem spec_7 (nums : Slice Std.I64) (h : ValidIn nums) :
    ∃ r : Std.I64,
      minimum_operations nums = ok r ∧ minimum_operations (reverseNums nums) = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidIn nums), ∃ r : Std.I64,
      minimum_operations nums = ok r ∧ minimum_operations (reverseNums nums) = ok r) := by
  sorry

/-- If len(nums) = 2, then the function returns r = 0 when nums[0] = nums[1], and returns r = 1 when nums[0] != nums[1].
  Preconditions: nums is a nonempty array with len(nums) <= 100000, and 1 <= nums[i] <= 1000000 for every i with 0 <= i < len(nums). -/
theorem spec_8 (nums : Slice Std.I64) (h : ValidIn nums) (hlen : nums.val.length = 2) :
    (entry nums 0 (by omega) = entry nums 1 (by omega) →
        ∃ r : Std.I64, minimum_operations nums = ok r ∧ r.val = 0) ∧
      (entry nums 0 (by omega) ≠ entry nums 1 (by omega) →
        ∃ r : Std.I64, minimum_operations nums = ok r ∧ r.val = 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidIn nums) (hlen : nums.val.length = 2), (entry nums 0 (by omega) = entry nums 1 (by omega) →
        ∃ r : Std.I64, minimum_operations nums = ok r ∧ r.val = 0) ∧
      (entry nums 0 (by omega) ≠ entry nums 1 (by omega) →
        ∃ r : Std.I64, minimum_operations nums = ok r ∧ r.val = 1)) := by
  sorry

/-- Let n = len(nums) and let the function return r. Then r <= n - 2 if and only if there exists an integer k with 2 <= k <= n and a palindromic partition of nums into k contiguous nonempty blocks (i.e., indices 0 = b_0 < b_1 < ... < b_k = n whose block sums S_j = nums[b_j] + ... + nums[b_{j+1}-1] satisfy S_j = S_{k-1-j} for all 0 <= j < k).
  Preconditions: nums is a nonempty array with len(nums) <= 100000, and 1 <= nums[i] <= 1000000 for every i with 0 <= i < len(nums). -/
theorem spec_9 (nums : Slice Std.I64) (h : ValidIn nums) :
    ∃ r : Std.I64, minimum_operations nums = ok r ∧
      (r.val ≤ (nums.val.length : ℤ) - 2 ↔
        ∃ k : ℕ, 2 ≤ k ∧ k ≤ nums.val.length ∧ HasPalindromePartition nums k) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidIn nums), ∃ r : Std.I64, minimum_operations nums = ok r ∧
      (r.val ≤ (nums.val.length : ℤ) - 2 ↔
        ∃ k : ℕ, 2 ≤ k ∧ k ≤ nums.val.length ∧ HasPalindromePartition nums k)) := by
  sorry

/-- For every positive integer c such that c * nums[i] <= 2^63 - 1 for all i and c * (nums[0] + nums[1] + ... + nums[n-1]) <= 2^63 - 1, let nums' be the array with nums'[i] = c * nums[i]. Then the result returned by the function on nums' equals the result returned by the function on nums.
  Preconditions: nums is a nonempty array with len(nums) <= 100000, and 1 <= nums[i] <= 1000000 for every i with 0 <= i < len(nums). -/
theorem spec_10 (nums : Slice Std.I64) (h : ValidIn nums) (c : ℤ) (hc : 0 < c)
    (hmul : ∀ i (hi : i < nums.val.length), c * entry nums i hi ≤ 2 ^ 63 - 1)
    (hsum : c * totalSum nums ≤ 2 ^ 63 - 1) :
    minimum_operations (scaleNums c nums) = minimum_operations nums := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidIn nums) (c : ℤ) (hc : 0 < c)
    (hmul : ∀ i (hi : i < nums.val.length), c * entry nums i hi ≤ 2 ^ 63 - 1)
    (hsum : c * totalSum nums ≤ 2 ^ 63 - 1), minimum_operations (scaleNums c nums) = minimum_operations nums) := by
  sorry

/-- Let n = len(nums), suppose nums[0] = nums[n-1], and let inner be the contiguous subarray of length n - 2 given by inner[j] = nums[j+1] for 0 <= j < n-2. Then the function returns a result r on nums, the function returns a result r' on inner, and r <= r'.
  Preconditions: nums is a nonempty array with 3 <= len(nums) <= 100000, and 1 <= nums[i] <= 1000000 for every i with 0 <= i < len(nums). -/
theorem spec_11 (nums : Slice Std.I64) (h : ValidIn nums) (hlen : 3 ≤ nums.val.length)
    (hends : entry nums 0 (by omega) = entry nums (nums.val.length - 1) (by omega)) :
    ∃ r r' : Std.I64,
      minimum_operations nums = ok r ∧ minimum_operations (innerNums nums) = ok r' ∧
        r.val ≤ r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidIn nums) (hlen : 3 ≤ nums.val.length)
    (hends : entry nums 0 (by omega) = entry nums (nums.val.length - 1) (by omega)), ∃ r r' : Std.I64,
      minimum_operations nums = ok r ∧ minimum_operations (innerNums nums) = ok r' ∧
        r.val ≤ r'.val) := by
  sorry

/-- Let n = len(nums) and let S = nums[0] + nums[1] + ... + nums[n-1]. The function returns a result r, and if S is odd then n - r is odd (equivalently r has the same parity as n - 1).
  Preconditions: nums is a nonempty array with len(nums) <= 100000, and 1 <= nums[i] <= 1000000 for every i with 0 <= i < len(nums). -/
theorem spec_12 (nums : Slice Std.I64) (h : ValidIn nums) :
    ∃ r : Std.I64, minimum_operations nums = ok r ∧
      (Odd (totalSum nums) → Odd ((nums.val.length : ℤ) - r.val)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidIn nums), ∃ r : Std.I64, minimum_operations nums = ok r ∧
      (Odd (totalSum nums) → Odd ((nums.val.length : ℤ) - r.val))) := by
  sorry

/-- Let n = len(nums) and let inner be the contiguous subarray of length n-2 given by inner[j] = nums[j+1] for 0 <= j < n-2. Then the function returns a result r on nums, the function returns a result r' on inner, and r = r'.
  Preconditions: nums is a nonempty array with 3 <= len(nums) <= 100000, 1 <= nums[i] <= 1000000 for every i, and nums[0] = nums[n-1]. -/
theorem spec_13 (nums : Slice Std.I64) (h : ValidIn nums) (hlen : 3 ≤ nums.val.length)
    (hends : entry nums 0 (by omega) = entry nums (nums.val.length - 1) (by omega)) :
    ∃ r r' : Std.I64,
      minimum_operations nums = ok r ∧ minimum_operations (innerNums nums) = ok r' ∧
        r.val = r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidIn nums) (hlen : 3 ≤ nums.val.length)
    (hends : entry nums 0 (by omega) = entry nums (nums.val.length - 1) (by omega)), ∃ r r' : Std.I64,
      minimum_operations nums = ok r ∧ minimum_operations (innerNums nums) = ok r' ∧
        r.val = r'.val) := by
  sorry

end AegisSpec.MinimumOperations
