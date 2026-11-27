import Aegis.HalveArray.Code.Funs

/-!
# Specifications of `Aegis.HalveArray.halve_array`

LeetCode problem `minimum-operations-to-halve-array-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.HalveArray (halve_array)

namespace AegisSpec.HalveArray

def vals (l : List Std.I64) : List ℤ := l.map (fun x => x.val)

def entry (l : List Std.I64) (i : ℕ) : ℤ := (vals l).getD i 0

def size (nums : Slice Std.I64) : ℕ := nums.val.length

def total (nums : Slice Std.I64) : ℤ := (vals nums.val).sum

def InBounds (nums : Slice Std.I64) : Prop :=
  1 ≤ size nums ∧ size nums ≤ 100000 ∧
    ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000

def planCost (c : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, c i

def finalSum (nums : Slice Std.I64) (c : ℕ → ℕ) : ℚ :=
  ∑ i ∈ Finset.range (size nums), (entry nums.val i : ℚ) / (2 : ℚ) ^ c i

def feasible (nums : Slice Std.I64) (k : ℕ) : Prop :=
  ∃ c : ℕ → ℕ, planCost c (size nums) = k ∧ finalSum nums c ≤ (total nums : ℚ) / 2

def permRel (nums nums' : Slice Std.I64) : Prop :=
  size nums' = size nums ∧ ∃ π : Equiv.Perm (Fin (size nums)),
    ∀ i : Fin (size nums), entry nums'.val i.val = entry nums.val (π i).val

def hasDominant (nums : Slice Std.I64) : Prop :=
  ∃ i : ℕ, i < size nums ∧ 2 * total nums ≤ 3 * entry nums.val i

def hasPair (nums : Slice Std.I64) : Prop :=
  ∃ i j : ℕ, i < size nums ∧ j < size nums ∧ i ≠ j ∧
    total nums ≤ entry nums.val i + entry nums.val j

/-- Let n = len(nums) and S = sum_{i=0}^{n-1} nums[i] (as an exact integer/rational sum). The function returns a result r, and r is the least natural number k for which there exist natural numbers c_0, ..., c_{n-1} satisfying sum_{i=0}^{n-1} c_i = k and sum_{i=0}^{n-1} nums[i] / 2^{c_i} <= S / 2. Here c_i is the total number of operations applied to the original element nums[i], including operations applied to values obtained by halving it; divisions are exact rational divisions. Equivalently, r is the minimum number of operations needed to make the sum of the current numbers at most half of the initial sum S.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000. -/
theorem spec_1 (nums : Slice Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000)
    (hr : halve_array nums = ok r) :
    0 ≤ r.val ∧ feasible nums r.val.toNat ∧ ∀ k : ℕ, feasible nums k → r.val.toNat ≤ k := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000)
    (hr : halve_array nums = ok r), 0 ≤ r.val ∧ feasible nums r.val.toNat ∧ ∀ k : ℕ, feasible nums k → r.val.toNat ≤ k) := by
  sorry

/-- For every such input, the function returns a result r; it does not fail, panic, go out of bounds, or overflow.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000) :
    ∃ r : Std.I64, halve_array nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000), ∃ r : Std.I64, halve_array nums = ok r) := by
  sorry

/-- Whenever the function returns a result r on such an input, r >= 1.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000. -/
theorem spec_3 (nums : Slice Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000)
    (hr : halve_array nums = ok r) :
    1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000)
    (hr : halve_array nums = ok r), 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r on such an input, r <= len(nums).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000. -/
theorem spec_4 (nums : Slice Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000)
    (hr : halve_array nums = ok r) :
    r.val ≤ (size nums : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000)
    (hr : halve_array nums = ok r), r.val ≤ (size nums : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = 1.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000, and len(nums) = 1. -/
theorem spec_5 (nums : Slice Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000)
    (hsize : size nums = 1)
    (hr : halve_array nums = ok r) :
    r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000)
    (hsize : size nums = 1)
    (hr : halve_array nums = ok r), r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, r = 2.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000, and len(nums) = 2. -/
theorem spec_6 (nums : Slice Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000)
    (hsize : size nums = 2)
    (hr : halve_array nums = ok r) :
    r.val = 2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000)
    (hsize : size nums = 2)
    (hr : halve_array nums = ok r), r.val = 2) := by
  sorry

/-- Whenever the function returns a result r, r >= 2.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000, and len(nums) >= 2. -/
theorem spec_7 (nums : Slice Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000)
    (hsize : 2 ≤ size nums)
    (hr : halve_array nums = ok r) :
    2 ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000)
    (hsize : 2 ≤ size nums)
    (hr : halve_array nums = ok r), 2 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = len(nums).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, and there exists an integer c with 1 <= c <= 10000000 such that nums[i] = c for every index i with 0 <= i < len(nums). -/
theorem spec_8 (nums : Slice Std.I64) (r : Std.I64) (c : ℤ)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hc1 : 1 ≤ c) (hc2 : c ≤ 10000000)
    (hconst : ∀ i : ℕ, i < size nums → entry nums.val i = c)
    (hr : halve_array nums = ok r) :
    r.val = (size nums : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64) (c : ℤ)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hc1 : 1 ≤ c) (hc2 : c ≤ 10000000)
    (hconst : ∀ i : ℕ, i < size nums → entry nums.val i = c)
    (hr : halve_array nums = ok r), r.val = (size nums : ℤ)) := by
  sorry

/-- If the function returns r on nums and r' on nums', then r' = r.
  Preconditions: nums and nums' are both slices of 64-bit integers satisfying the problem constraints, they have the same length n, and there is a permutation pi of {0, ..., n-1} such that nums'[i] = nums[pi(i)] for every i. -/
theorem spec_9 (nums nums' : Slice Std.I64) (r r' : Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000)
    (hlen1' : 1 ≤ size nums') (hlen2' : size nums' ≤ 100000)
    (hval' : ∀ i : ℕ, i < size nums' → 1 ≤ entry nums'.val i ∧ entry nums'.val i ≤ 10000000)
    (hperm : permRel nums nums')
    (hr : halve_array nums = ok r) (hr' : halve_array nums' = ok r') :
    r'.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (r r' : Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000)
    (hlen1' : 1 ≤ size nums') (hlen2' : size nums' ≤ 100000)
    (hval' : ∀ i : ℕ, i < size nums' → 1 ≤ entry nums'.val i ∧ entry nums'.val i ≤ 10000000)
    (hperm : permRel nums nums')
    (hr : halve_array nums = ok r) (hr' : halve_array nums' = ok r'), r'.val = r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 2 if and only if at least one of the following holds: (a) there is an index i with 3 * nums[i] >= 2 * S; or (b) there are distinct indices i and j with nums[i] + nums[j] >= S. If neither condition holds, then r >= 3.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000, and len(nums) >= 2. Let S = sum(nums). -/
theorem spec_10 (nums : Slice Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000)
    (hsize : 2 ≤ size nums)
    (hr : halve_array nums = ok r) :
    (r.val = 2 ↔ hasDominant nums ∨ hasPair nums) ∧
      (¬(hasDominant nums ∨ hasPair nums) → 3 ≤ r.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000)
    (hsize : 2 ≤ size nums)
    (hr : halve_array nums = ok r), (r.val = 2 ↔ hasDominant nums ∨ hasPair nums) ∧
      (¬(hasDominant nums ∨ hasPair nums) → 3 ≤ r.val)) := by
  sorry

/-- Whenever the function returns a result r, for every natural number k with r <= k, there exists a feasible plan using exactly k operations: there are natural numbers c_i with sum c_i = k and sum nums[i] / 2^{c_i} <= S / 2.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000, and for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000. -/
theorem spec_11 (nums : Slice Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000)
    (hr : halve_array nums = ok r) :
    ∀ k : ℕ, r.val ≤ (k : ℤ) → feasible nums k := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hlen1 : 1 ≤ size nums) (hlen2 : size nums ≤ 100000)
    (hval : ∀ i : ℕ, i < size nums → 1 ≤ entry nums.val i ∧ entry nums.val i ≤ 10000000)
    (hr : halve_array nums = ok r), ∀ k : ℕ, r.val ≤ (k : ℤ) → feasible nums k) := by
  sorry

end AegisSpec.HalveArray
