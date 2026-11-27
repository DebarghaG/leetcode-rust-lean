import Aegis.IncremovableSubarrayCount.Code.Funs

/-!
# Specifications of `Aegis.IncremovableSubarrayCount.incremovable_subarray_count`

LeetCode problem `count-the-number-of-incremovable-subarrays-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IncremovableSubarrayCount

open Aegis.IncremovableSubarrayCount (incremovable_subarray_count)

def contents (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

def StrictlyIncreasing (l : List ℤ) : Prop := l.Pairwise (· < ·)

instance instDecidableStrictlyIncreasing (l : List ℤ) : Decidable (StrictlyIncreasing l) :=
  inferInstanceAs (Decidable (l.Pairwise (· < ·)))

def AdjacentIncreasing (l : List ℤ) : Prop :=
  ∀ i : Fin (l.length - 1), l.get ⟨i.1, by omega⟩ < l.get ⟨i.1 + 1, by omega⟩

def deleteBlock (l : List ℤ) (a b : ℕ) : List ℤ := l.take a ++ l.drop (b + 1)

def BlockIncremovable (l : List ℤ) (a b : ℕ) : Prop :=
  a ≤ b ∧ b < l.length ∧ StrictlyIncreasing (deleteBlock l a b)

instance instDecidableBlockIncremovable (l : List ℤ) (a b : ℕ) :
    Decidable (BlockIncremovable l a b) := by
  unfold BlockIncremovable
  infer_instance

def incremovablePairs (l : List ℤ) : Finset (ℕ × ℕ) :=
  ((Finset.range l.length).product (Finset.range l.length)).filter
    (fun p => p.1 ≤ p.2 ∧ StrictlyIncreasing (deleteBlock l p.1 p.2))

def incremovableCount (l : List ℤ) : ℕ := (incremovablePairs l).card

def incPrefixLen (l : List ℤ) : ℕ :=
  Nat.findGreatest (fun k => StrictlyIncreasing (l.take k)) l.length

def incSuffixLen (l : List ℤ) : ℕ :=
  Nat.findGreatest (fun q => StrictlyIncreasing (l.drop (l.length - q))) l.length

def indicator (P : Prop) [Decidable P] : ℤ := if P then 1 else 0

/-- Whenever incremovable_subarray_count nums returns a result c, c is the number of pairs (l,r) of integers such that 0 <= l <= r < n and the sequence obtained by deleting the contiguous block nums[l], nums[l+1], ..., nums[r] from nums is strictly increasing. Equivalently, the remaining sequence is the concatenation nums[0], ..., nums[l-1], nums[r+1], ..., nums[n-1], and it must satisfy every consecutive-pair inequality; the empty sequence and all singleton sequences are strictly increasing.
  Preconditions: nums is a slice of 64-bit integers with n = len(nums), 1 <= n <= 100000, and 1 <= nums[i] <= 1000000000 for every 0 <= i < n. -/
theorem spec_1 (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_res : incremovable_subarray_count nums = ok c) :
    c.val = (incremovableCount (contents nums) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_res : incremovable_subarray_count nums = ok c), c.val = (incremovableCount (contents nums) : ℤ)) := by
  sorry

/-- For every nums satisfying the preconditions, incremovable_subarray_count nums returns a result: there exists an i64 c such that the call evaluates to Result.ok c. It does not panic, get an out-of-bounds index, or overflow.
  Preconditions: nums is a slice of 64-bit integers with n = len(nums), 1 <= n <= 100000, and 1 <= nums[i] <= 1000000000 for every 0 <= i < n. -/
theorem spec_2 (nums : Slice I64) (n : ℕ)
    (h_len : n = nums.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000) :
    ∃ c : I64, incremovable_subarray_count nums = ok c := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ)
    (h_len : n = nums.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000), ∃ c : I64, incremovable_subarray_count nums = ok c) := by
  sorry

/-- Whenever incremovable_subarray_count nums returns c, c <= n(n+1)/2.
  Preconditions: nums is a slice of 64-bit integers with n = len(nums), 1 <= n <= 100000, and 1 <= nums[i] <= 1000000000 for every 0 <= i < n. -/
theorem spec_3 (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_res : incremovable_subarray_count nums = ok c) :
    c.val ≤ (n : ℤ) * ((n : ℤ) + 1) / 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_res : incremovable_subarray_count nums = ok c), c.val ≤ (n : ℤ) * ((n : ℤ) + 1) / 2) := by
  sorry

/-- Whenever incremovable_subarray_count nums returns c, c >= 1.
  Preconditions: nums is a slice of 64-bit integers with n = len(nums), 1 <= n <= 100000, and 1 <= nums[i] <= 1000000000 for every 0 <= i < n. -/
theorem spec_4 (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_res : incremovable_subarray_count nums = ok c) :
    1 ≤ c.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_res : incremovable_subarray_count nums = ok c), 1 ≤ c.val) := by
  sorry

/-- Whenever incremovable_subarray_count nums returns c, c >= 3.
  Preconditions: nums is a slice of 64-bit integers with n = len(nums), 2 <= n <= 100000, and 1 <= nums[i] <= 1000000000 for every 0 <= i < n. -/
theorem spec_5 (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_pos : 2 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_res : incremovable_subarray_count nums = ok c) :
    3 ≤ c.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_pos : 2 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_res : incremovable_subarray_count nums = ok c), 3 ≤ c.val) := by
  sorry

/-- Whenever incremovable_subarray_count nums returns c, c = 1.
  Preconditions: nums is a slice of 64-bit integers with n = len(nums) = 1, and 1 <= nums[0] <= 1000000000. -/
theorem spec_6 (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_n : n = 1)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_res : incremovable_subarray_count nums = ok c) :
    c.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_n : n = 1)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_res : incremovable_subarray_count nums = ok c), c.val = 1) := by
  sorry

/-- Whenever incremovable_subarray_count nums returns c, c = 3.
  Preconditions: nums is a slice of 64-bit integers with n = len(nums) = 2, and 1 <= nums[i] <= 1000000000 for i = 0,1. -/
theorem spec_7 (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_n : n = 2)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_res : incremovable_subarray_count nums = ok c) :
    c.val = 3 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_n : n = 2)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_res : incremovable_subarray_count nums = ok c), c.val = 3) := by
  sorry

/-- Whenever incremovable_subarray_count nums returns c, c = 3 + [nums[1] < nums[2]] + [nums[0] < nums[2]] + [nums[0] < nums[1]], where [P] is 1 if P is true and 0 otherwise.
  Preconditions: nums is a slice of 64-bit integers with n = len(nums) = 3, and 1 <= nums[i] <= 1000000000 for i = 0,1,2. -/
theorem spec_8 (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_n : n = 3)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_res : incremovable_subarray_count nums = ok c) :
    c.val = 3
      + indicator ((nums.val.get ⟨1, by omega⟩).val < (nums.val.get ⟨2, by omega⟩).val)
      + indicator ((nums.val.get ⟨0, by omega⟩).val < (nums.val.get ⟨2, by omega⟩).val)
      + indicator ((nums.val.get ⟨0, by omega⟩).val < (nums.val.get ⟨1, by omega⟩).val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_n : n = 3)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_res : incremovable_subarray_count nums = ok c), c.val = 3
      + indicator ((nums.val.get ⟨1, by omega⟩).val < (nums.val.get ⟨2, by omega⟩).val)
      + indicator ((nums.val.get ⟨0, by omega⟩).val < (nums.val.get ⟨2, by omega⟩).val)
      + indicator ((nums.val.get ⟨0, by omega⟩).val < (nums.val.get ⟨1, by omega⟩).val)) := by
  sorry

/-- Whenever incremovable_subarray_count nums returns c, c = n(n+1)/2.
  Preconditions: nums is a slice of 64-bit integers with n = len(nums), 1 <= n <= 100000, 1 <= nums[i] <= 1000000000 for every 0 <= i < n, and nums[i] < nums[i+1] for every 0 <= i < n-1. -/
theorem spec_9 (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_incr : AdjacentIncreasing (contents nums))
    (h_res : incremovable_subarray_count nums = ok c) :
    c.val = (n : ℤ) * ((n : ℤ) + 1) / 2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_incr : AdjacentIncreasing (contents nums))
    (h_res : incremovable_subarray_count nums = ok c), c.val = (n : ℤ) * ((n : ℤ) + 1) / 2) := by
  sorry

/-- Whenever incremovable_subarray_count nums returns c, if n >= 2 then c = 3, and if n = 1 then c = 1.
  Preconditions: nums is a slice of 64-bit integers with n = len(nums), 1 <= n <= 100000, 1 <= nums[i] <= 1000000000 for every 0 <= i < n, and nums[i] >= nums[i+1] for every 0 <= i < n-1. -/
theorem spec_10 (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_dec : ∀ i : Fin (n - 1),
      (nums.val.get ⟨i.1 + 1, by omega⟩).val ≤ (nums.val.get ⟨i.1, by omega⟩).val)
    (h_res : incremovable_subarray_count nums = ok c) :
    (2 ≤ n → c.val = 3) ∧ (n = 1 → c.val = 1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_dec : ∀ i : Fin (n - 1),
      (nums.val.get ⟨i.1 + 1, by omega⟩).val ≤ (nums.val.get ⟨i.1, by omega⟩).val)
    (h_res : incremovable_subarray_count nums = ok c), (2 ≤ n → c.val = 3) ∧ (n = 1 → c.val = 1)) := by
  sorry

/-- Whenever incremovable_subarray_count nums returns c and incremovable_subarray_count nums' returns c', we have c = c'.
  Preconditions: nums and nums' are slices of 64-bit integers, both satisfy the problem constraints, n = len(nums) = len(nums'), and for every i,j with 0 <= i < n and 0 <= j < n, nums[i] < nums[j] iff nums'[i] < nums'[j]. -/
theorem spec_11 (nums nums' : Slice I64) (n : ℕ) (c c' : I64)
    (h_len : n = nums.val.length) (h_len' : n = nums'.val.length)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_bounds' : ∀ i : Fin nums'.val.length,
      1 ≤ (nums'.val.get i).val ∧ (nums'.val.get i).val ≤ 1000000000)
    (h_order : ∀ i j : Fin n,
      (nums.val.get ⟨i.1, by omega⟩).val < (nums.val.get ⟨j.1, by omega⟩).val ↔
      (nums'.val.get ⟨i.1, by omega⟩).val < (nums'.val.get ⟨j.1, by omega⟩).val)
    (h_res : incremovable_subarray_count nums = ok c)
    (h_res' : incremovable_subarray_count nums' = ok c') :
    c = c' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums' : Slice I64) (n : ℕ) (c c' : I64)
    (h_len : n = nums.val.length) (h_len' : n = nums'.val.length)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_bounds' : ∀ i : Fin nums'.val.length,
      1 ≤ (nums'.val.get i).val ∧ (nums'.val.get i).val ≤ 1000000000)
    (h_order : ∀ i j : Fin n,
      (nums.val.get ⟨i.1, by omega⟩).val < (nums.val.get ⟨j.1, by omega⟩).val ↔
      (nums'.val.get ⟨i.1, by omega⟩).val < (nums'.val.get ⟨j.1, by omega⟩).val)
    (h_res : incremovable_subarray_count nums = ok c)
    (h_res' : incremovable_subarray_count nums' = ok c'), c = c') := by
  sorry

/-- Let p be the largest integer with 0 <= p <= n such that the sequence nums[0], nums[1], ..., nums[p-1] is strictly increasing; for p = 0 or p = 1 this condition is vacuous. Whenever incremovable_subarray_count nums returns c, c >= min(p, n-1) + 1.
  Preconditions: nums is a slice of 64-bit integers with n = len(nums), 1 <= n <= 100000, and 1 <= nums[i] <= 1000000000 for every 0 <= i < n. -/
theorem spec_12 (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_res : incremovable_subarray_count nums = ok c) :
    ((min (incPrefixLen (contents nums)) (n - 1) : ℕ) : ℤ) + 1 ≤ c.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_res : incremovable_subarray_count nums = ok c), ((min (incPrefixLen (contents nums)) (n - 1) : ℕ) : ℤ) + 1 ≤ c.val) := by
  sorry

/-- Let q be the largest integer with 0 <= q <= n such that the last q elements nums[n-q], nums[n-q+1], ..., nums[n-1] form a strictly increasing sequence; for q = 0 or q = 1 this condition is vacuous. Whenever incremovable_subarray_count nums returns c, c >= min(q, n-1) + 1.
  Preconditions: nums is a slice of 64-bit integers with n = len(nums), 1 <= n <= 100000, and 1 <= nums[i] <= 1000000000 for every 0 <= i < n. -/
theorem spec_13 (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_res : incremovable_subarray_count nums = ok c) :
    ((min (incSuffixLen (contents nums)) (n - 1) : ℕ) : ℤ) + 1 ≤ c.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_res : incremovable_subarray_count nums = ok c), ((min (incSuffixLen (contents nums)) (n - 1) : ℕ) : ℤ) + 1 ≤ c.val) := by
  sorry

/-- Whenever incremovable_subarray_count nums returns c, if n != 2 and c = n(n+1)/2, then nums[i] < nums[i+1] for every 0 <= i < n-1.
  Preconditions: nums is a slice of 64-bit integers with n = len(nums), 1 <= n <= 100000, and 1 <= nums[i] <= 1000000000 for every 0 <= i < n. -/
theorem spec_14 (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_n : n ≠ 2)
    (h_res : incremovable_subarray_count nums = ok c)
    (h_c : c.val = (n : ℤ) * ((n : ℤ) + 1) / 2) :
    AdjacentIncreasing (contents nums) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice I64) (n : ℕ) (c : I64)
    (h_len : n = nums.val.length) (h_pos : 1 ≤ n) (h_le : n ≤ 100000)
    (h_bounds : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000000000)
    (h_n : n ≠ 2)
    (h_res : incremovable_subarray_count nums = ok c)
    (h_c : c.val = (n : ℤ) * ((n : ℤ) + 1) / 2), AdjacentIncreasing (contents nums)) := by
  sorry

end AegisSpec.IncremovableSubarrayCount
