import Aegis.MinimumSize.Code.Funs

/-!
# Specifications of `Aegis.MinimumSize.minimum_size`

LeetCode problem `minimum-limit-of-balls-in-a-bag`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumSize

open Aegis.MinimumSize

def vals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

def ceilDiv (a b : ℤ) : ℤ := -((-a).fdiv b)

def floorDiv (a b : ℤ) : ℤ := a.fdiv b

def cost (l : List ℤ) (X : ℤ) : ℤ := (l.map (fun a => ceilDiv a X - 1)).sum

def total (l : List ℤ) : ℤ := l.sum

def listMax : List ℤ → ℤ
  | [] => 0
  | a :: rest => rest.foldr max a

def UniqueMax (l : List ℤ) : Prop :=
  ∃ j : Fin l.length, l.get j = listMax l ∧ ∀ k : Fin l.length, l.get k = listMax l → k = j

def deleteOnes : List ℤ → List ℤ → Prop
  | [], l => l = []
  | a :: l', l => (∃ l₀, l = a :: l₀ ∧ deleteOnes l' l₀) ∨ (a = 1 ∧ deleteOnes l' l)

def InsertOnes (l l' : List ℤ) : Prop := deleteOnes l' l

/-- For every input satisfying the preconditions, the function returns a result r and r is the least integer X with 1 <= X such that cost(X) <= maxOperations, where cost(X) = sum_{i=0}^{len(nums)-1} (ceil_div(nums[i], X) - 1), and ceil_div(a, b) denotes the least integer q with q * b >= a (for positive integers a and b). Equivalently, 1 <= r, cost(r) <= maxOperations, and for every integer X with 1 <= X < r, cost(X) > maxOperations.
  Preconditions: 1 <= len(nums) <= 10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 0 <= maxOperations <= 10^9 (maxOperations = 0 is allowed to cover the provided example [1000000000], 0 -> 1000000000). -/
theorem spec_1 (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length) (h_len_le : nums.length ≤ 10 ^ 5)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9) :
    ∃ r : I64, minimum_size nums maxOperations = ok r ∧
      1 ≤ r.val ∧ cost (vals nums) r.val ≤ maxOperations.val ∧
      (∀ X : ℤ, 1 ≤ X → X < r.val → maxOperations.val < cost (vals nums) X) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length) (h_len_le : nums.length ≤ 10 ^ 5)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9), ∃ r : I64, minimum_size nums maxOperations = ok r ∧
      1 ≤ r.val ∧ cost (vals nums) r.val ≤ maxOperations.val ∧
      (∀ X : ℤ, 1 ≤ X → X < r.val → maxOperations.val < cost (vals nums) X)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; in particular, it does not panic, overflow, or fail due to out-of-bounds access. No further property of r is claimed by this specification.
  Preconditions: 1 <= len(nums) <= 10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 0 <= maxOperations <= 10^9 (maxOperations = 0 is allowed to cover the provided example [1000000000], 0 -> 1000000000). -/
theorem spec_2 (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length) (h_len_le : nums.length ≤ 10 ^ 5)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9) :
    ∃ r : I64, minimum_size nums maxOperations = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length) (h_len_le : nums.length ≤ 10 ^ 5)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9), ∃ r : I64, minimum_size nums maxOperations = ok r) := by
  sorry

/-- For every input satisfying the preconditions, if the function returns r, then r >= ceil_div(max(nums), maxOperations + 1), where max(nums) = max_{0 <= i < len(nums)} nums[i] and ceil_div(a,b) denotes the least integer q with q * b >= a (b > 0).
  Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 0 <= maxOperations <= 10^9. -/
theorem spec_3 (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9) :
    ∀ r : I64, minimum_size nums maxOperations = ok r →
      ceilDiv (listMax (vals nums)) (maxOperations.val + 1) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9), ∀ r : I64, minimum_size nums maxOperations = ok r →
      ceilDiv (listMax (vals nums)) (maxOperations.val + 1) ≤ r.val) := by
  sorry

/-- For every input satisfying the preconditions, if the function returns r, then r >= ceil_div(S, len(nums) + maxOperations), where S = sum_{i=0}^{len(nums)-1} nums[i] and ceil_div(a,b) denotes the least integer q with q * b >= a (b > 0).
  Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 0 <= maxOperations <= 10^9. -/
theorem spec_4 (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9) :
    ∀ r : I64, minimum_size nums maxOperations = ok r →
      ceilDiv (total (vals nums)) ((nums.length : ℤ) + maxOperations.val) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9), ∀ r : I64, minimum_size nums maxOperations = ok r →
      ceilDiv (total (vals nums)) ((nums.length : ℤ) + maxOperations.val) ≤ r.val) := by
  sorry

/-- For every input satisfying the preconditions, if the function returns r, then r <= max(nums), where max(nums) = max_{0 <= i < len(nums)} nums[i].
  Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 0 <= maxOperations <= 10^9. -/
theorem spec_5 (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9) :
    ∀ r : I64, minimum_size nums maxOperations = ok r →
      r.val ≤ listMax (vals nums) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9), ∀ r : I64, minimum_size nums maxOperations = ok r →
      r.val ≤ listMax (vals nums)) := by
  sorry

/-- For every input satisfying the preconditions, if the function returns r, then r <= ceil_div(max(nums), floor_div(maxOperations, len(nums)) + 1), where max(nums) = max_{0 <= i < len(nums)} nums[i], floor_div(a,b) is the greatest integer q with q * b <= a (a >= 0, b > 0), and ceil_div(a,b) is the least integer q with q * b >= a (b > 0).
  Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 0 <= maxOperations <= 10^9. -/
theorem spec_6 (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9) :
    ∀ r : I64, minimum_size nums maxOperations = ok r →
      r.val ≤
        ceilDiv (listMax (vals nums)) (floorDiv maxOperations.val (nums.length : ℤ) + 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9), ∀ r : I64, minimum_size nums maxOperations = ok r →
      r.val ≤
        ceilDiv (listMax (vals nums)) (floorDiv maxOperations.val (nums.length : ℤ) + 1)) := by
  sorry

/-- For every input satisfying the preconditions, if the function returns r, then r = max(nums), where max(nums) = max_{0 <= i < len(nums)} nums[i].
  Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; maxOperations = 0. -/
theorem spec_7 (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_zero : maxOperations.val = 0) :
    ∀ r : I64, minimum_size nums maxOperations = ok r →
      r.val = listMax (vals nums) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_zero : maxOperations.val = 0), ∀ r : I64, minimum_size nums maxOperations = ok r →
      r.val = listMax (vals nums)) := by
  sorry

/-- For every input satisfying the preconditions, if the function returns r, then r = 1.
  Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 0 <= maxOperations <= 10^9; maxOperations >= S - len(nums), where S = sum_{i=0}^{len(nums)-1} nums[i]. -/
theorem spec_8 (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9)
    (h_ops_big : total (vals nums) - (nums.length : ℤ) ≤ maxOperations.val) :
    ∀ r : I64, minimum_size nums maxOperations = ok r → r.val = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9)
    (h_ops_big : total (vals nums) - (nums.length : ℤ) ≤ maxOperations.val), ∀ r : I64, minimum_size nums maxOperations = ok r → r.val = 1) := by
  sorry

/-- For every input satisfying the preconditions, if the function returns r, then r = ceil_div(nums[0], maxOperations + 1), where ceil_div(a,b) is the least integer q with q * b >= a (b > 0).
  Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 0 <= maxOperations <= 10^9; len(nums) = 1. -/
theorem spec_9 (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9)
    (h_len_one : nums.length = 1) :
    ∀ r : I64, minimum_size nums maxOperations = ok r →
      r.val = ceilDiv ((vals nums).getD 0 0) (maxOperations.val + 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9)
    (h_len_one : nums.length = 1), ∀ r : I64, minimum_size nums maxOperations = ok r →
      r.val = ceilDiv ((vals nums).getD 0 0) (maxOperations.val + 1)) := by
  sorry

/-- For every input satisfying the preconditions, if the function returns r, then r < max(nums), where max(nums) = max_{0 <= i < len(nums)} nums[i].
  Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 0 <= maxOperations <= 10^9; maxOperations >= 1; max(nums) >= 2; there is exactly one index j with 0 <= j < len(nums) and nums[j] = max(nums). -/
theorem spec_10 (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9)
    (h_ops_pos : 1 ≤ maxOperations.val)
    (h_max_ge : 2 ≤ listMax (vals nums))
    (h_unique : UniqueMax (vals nums)) :
    ∀ r : I64, minimum_size nums maxOperations = ok r → r.val < listMax (vals nums) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9)
    (h_ops_pos : 1 ≤ maxOperations.val)
    (h_max_ge : 2 ≤ listMax (vals nums))
    (h_unique : UniqueMax (vals nums)), ∀ r : I64, minimum_size nums maxOperations = ok r → r.val < listMax (vals nums)) := by
  sorry

/-- If the function returns r1 on (nums, maxOperations1) and r2 on (nums, maxOperations2), then r1 >= r2.
  Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 0 <= maxOperations1 <= maxOperations2 <= 10^9. -/
theorem spec_11 (nums : Slice I64) (maxOperations₁ maxOperations₂ : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations₁.val)
    (h_ops_mono : maxOperations₁.val ≤ maxOperations₂.val)
    (h_ops_hi : maxOperations₂.val ≤ 10 ^ 9) :
    ∀ r₁ r₂ : I64, minimum_size nums maxOperations₁ = ok r₁ →
      minimum_size nums maxOperations₂ = ok r₂ → r₂.val ≤ r₁.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (maxOperations₁ maxOperations₂ : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations₁.val)
    (h_ops_mono : maxOperations₁.val ≤ maxOperations₂.val)
    (h_ops_hi : maxOperations₂.val ≤ 10 ^ 9), ∀ r₁ r₂ : I64, minimum_size nums maxOperations₁ = ok r₁ →
      minimum_size nums maxOperations₂ = ok r₂ → r₂.val ≤ r₁.val) := by
  sorry

/-- If the function returns r on (nums, maxOperations) and r' on (nums', maxOperations), then r = r'.
  Preconditions: nums and nums' are nonempty slices with all entries in [1,10^9]; nums' is a permutation (reordering) of nums, i.e., it has the same length and the same multiset of entries; 0 <= maxOperations <= 10^9. -/
theorem spec_12 (nums nums' : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length) (h_len_pos' : 1 ≤ nums'.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_entries' : ∀ a ∈ vals nums', 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_perm : (vals nums).Perm (vals nums'))
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9) :
    ∀ r r' : I64, minimum_size nums maxOperations = ok r →
      minimum_size nums' maxOperations = ok r' → r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums' : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length) (h_len_pos' : 1 ≤ nums'.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_entries' : ∀ a ∈ vals nums', 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_perm : (vals nums).Perm (vals nums'))
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9), ∀ r r' : I64, minimum_size nums maxOperations = ok r →
      minimum_size nums' maxOperations = ok r' → r.val = r'.val) := by
  sorry

/-- If the function returns r on (nums, maxOperations) and r1 on (nums1, maxOperations), then r1 = r.
  Preconditions: nums is a nonempty slice with all entries in [1,10^9]; nums1 is obtained by inserting any number (possibly zero) of extra entries equal to 1 into nums, and len(nums1) <= 10^5; 0 <= maxOperations <= 10^9. -/
theorem spec_13 (nums nums₁ : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_entries₁ : ∀ a ∈ vals nums₁, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_insert : InsertOnes (vals nums) (vals nums₁))
    (h_len₁ : nums₁.length ≤ 10 ^ 5)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9) :
    ∀ r r₁ : I64, minimum_size nums maxOperations = ok r →
      minimum_size nums₁ maxOperations = ok r₁ → r₁.val = r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums nums₁ : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_entries₁ : ∀ a ∈ vals nums₁, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_insert : InsertOnes (vals nums) (vals nums₁))
    (h_len₁ : nums₁.length ≤ 10 ^ 5)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9), ∀ r r₁ : I64, minimum_size nums maxOperations = ok r →
      minimum_size nums₁ maxOperations = ok r₁ → r₁.val = r.val) := by
  sorry

/-- If the function returns r on (nums, maxOperations) and r' on (nums', maxOperations), then r <= r'.
  Preconditions: nums and nums' are nonempty slices of the same length, with 1 <= nums[i] <= nums'[i] <= 10^9 for every i; 0 <= maxOperations <= 10^9. -/
theorem spec_14 (nums nums' : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_len_eq : nums.length = nums'.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_entries' : ∀ a ∈ vals nums', 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_point : ∀ i : ℕ, i < nums.length → (vals nums).getD i 0 ≤ (vals nums').getD i 0)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9) :
    ∀ r r' : I64, minimum_size nums maxOperations = ok r →
      minimum_size nums' maxOperations = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums nums' : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_len_eq : nums.length = nums'.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_entries' : ∀ a ∈ vals nums', 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_point : ∀ i : ℕ, i < nums.length → (vals nums).getD i 0 ≤ (vals nums').getD i 0)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9), ∀ r r' : I64, minimum_size nums maxOperations = ok r →
      minimum_size nums' maxOperations = ok r' → r.val ≤ r'.val) := by
  sorry

/-- For every input satisfying the preconditions, if the function returns r, then there exist integers p_0, ..., p_{len(nums)-1} such that for every i with 0 <= i < len(nums): 1 <= p_i <= nums[i], p_i * r >= nums[i], and sum_{i=0}^{len(nums)-1} (p_i - 1) <= maxOperations.
  Preconditions: len(nums) >= 1; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 0 <= maxOperations <= 10^9. -/
theorem spec_15 (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9) :
    ∀ r : I64, minimum_size nums maxOperations = ok r →
      ∃ p : List ℤ, p.length = (vals nums).length ∧
        (∀ i : ℕ, i < (vals nums).length →
          1 ≤ p.getD i 0 ∧ p.getD i 0 ≤ (vals nums).getD i 0 ∧
            (vals nums).getD i 0 ≤ p.getD i 0 * r.val) ∧
        p.sum ≤ maxOperations.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9), ∀ r : I64, minimum_size nums maxOperations = ok r →
      ∃ p : List ℤ, p.length = (vals nums).length ∧
        (∀ i : ℕ, i < (vals nums).length →
          1 ≤ p.getD i 0 ∧ p.getD i 0 ≤ (vals nums).getD i 0 ∧
            (vals nums).getD i 0 ≤ p.getD i 0 * r.val) ∧
        p.sum ≤ maxOperations.val) := by
  sorry

/-- For every input satisfying the preconditions, if the function returns r, then r = 1 if and only if maxOperations >= S - len(nums).
  Preconditions: 1 <= len(nums) <= 10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 0 <= maxOperations <= 10^9; let S = sum_{i=0}^{len(nums)-1} nums[i]. -/
theorem spec_16 (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length) (h_len_le : nums.length ≤ 10 ^ 5)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9) :
    ∀ r : I64, minimum_size nums maxOperations = ok r →
      (r.val = 1 ↔ total (vals nums) - (nums.length : ℤ) ≤ maxOperations.val) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (nums : Slice I64) (maxOperations : I64)
    (h_len_pos : 1 ≤ nums.length) (h_len_le : nums.length ≤ 10 ^ 5)
    (h_entries : ∀ a ∈ vals nums, 1 ≤ a ∧ a ≤ 10 ^ 9)
    (h_ops_lo : 0 ≤ maxOperations.val) (h_ops_hi : maxOperations.val ≤ 10 ^ 9), ∀ r : I64, minimum_size nums maxOperations = ok r →
      (r.val = 1 ↔ total (vals nums) - (nums.length : ℤ) ≤ maxOperations.val)) := by
  sorry

end AegisSpec.MinimumSize
