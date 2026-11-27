import Aegis.MaximumTop.Code.Funs

/-!
# Specifications of `Aegis.MaximumTop.maximum_top`

LeetCode problem `maximize-the-topmost-element-after-k-moves`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaximumTop

namespace AegisSpec.MaximumTop

def valAt (nums : Slice I64) (i : Nat) : Int :=
  ((nums.val[i]?).map (fun x => x.val)).getD (-1)

def IsGreatestOn (nums : Slice I64) (S : List Nat) (r : Int) : Prop :=
  (∃ i, i ∈ S ∧ valAt nums i = r) ∧ ∀ i, i ∈ S → valAt nums i ≤ r

def listMax : List Int → Int
  | [] => -1
  | x :: xs => max x (listMax xs)

def maxEntry (nums : Slice I64) : Int :=
  listMax (nums.val.map (fun x => x.val))

/-- Let n = len(nums). The function returns a result r, and r is determined as follows. (1) If k = 0, then r = nums[0]. (2) Otherwise, if n = 1, then r = nums[0] when k is even, and r = -1 when k is odd. (3) Otherwise n >= 2: (a) if k < n, then r is the largest value in the set { nums[i] | 0 <= i <= k-2 } union { nums[k] }, with the first set empty when k = 1; (b) if k = n, then r is the largest value among nums[0], nums[1], ..., nums[n-2]; (c) if k > n, then r is the largest value among nums[0], nums[1], ..., nums[n-1].
  Preconditions: 1 <= len(nums) <= 10^5; 0 <= k <= 10^9; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_1 (nums : Slice I64) (k : I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10 ^ 5)
    (hk_ge : 0 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hvals : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 10 ^ 9) :
    ∃ r, maximum_top nums k = ok r ∧
      (k.val = 0 → r.val = valAt nums 0) ∧
      (k.val ≠ 0 → nums.val.length = 1 →
        (Even k.val → r.val = valAt nums 0) ∧ (Odd k.val → r.val = -1)) ∧
      (2 ≤ nums.val.length → 1 ≤ k.val → k.val < (nums.val.length : Int) →
        IsGreatestOn nums (List.range (k.val.toNat - 1) ++ [k.val.toNat]) r.val) ∧
      (2 ≤ nums.val.length → k.val = (nums.val.length : Int) →
        IsGreatestOn nums (List.range (nums.val.length - 1)) r.val) ∧
      (2 ≤ nums.val.length → (nums.val.length : Int) < k.val →
        IsGreatestOn nums (List.range nums.val.length) r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10 ^ 5)
    (hk_ge : 0 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hvals : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 10 ^ 9), ∃ r, maximum_top nums k = ok r ∧
      (k.val = 0 → r.val = valAt nums 0) ∧
      (k.val ≠ 0 → nums.val.length = 1 →
        (Even k.val → r.val = valAt nums 0) ∧ (Odd k.val → r.val = -1)) ∧
      (2 ≤ nums.val.length → 1 ≤ k.val → k.val < (nums.val.length : Int) →
        IsGreatestOn nums (List.range (k.val.toNat - 1) ++ [k.val.toNat]) r.val) ∧
      (2 ≤ nums.val.length → k.val = (nums.val.length : Int) →
        IsGreatestOn nums (List.range (nums.val.length - 1)) r.val) ∧
      (2 ≤ nums.val.length → (nums.val.length : Int) < k.val →
        IsGreatestOn nums (List.range nums.val.length) r.val)) := by
  sorry

/-- The function returns a result r; in particular, it does not fail, panic, or overflow on any input satisfying the preconditions.
  Preconditions: 1 <= len(nums) <= 10^5; 0 <= k <= 10^9; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_2 (nums : Slice I64) (k : I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10 ^ 5)
    (hk_ge : 0 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hvals : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 10 ^ 9) :
    ∃ r, maximum_top nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10 ^ 5)
    (hk_ge : 0 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hvals : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 10 ^ 9), ∃ r, maximum_top nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exists an index i with 0 <= i < len(nums) such that r = nums[i].
  Preconditions: 1 <= len(nums) <= 10^5; 0 <= k <= 10^9; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_3 (nums : Slice I64) (k : I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10 ^ 5)
    (hk_ge : 0 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hvals : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (r : I64) (hres : maximum_top nums k = ok r) (hne : r.val ≠ -1) :
    ∃ x, x ∈ nums.val ∧ x.val = r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10 ^ 5)
    (hk_ge : 0 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hvals : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (r : I64) (hres : maximum_top nums k = ok r) (hne : r.val ≠ -1), ∃ x, x ∈ nums.val ∧ x.val = r.val) := by
  sorry

/-- Whenever the function returns a result r with r != -1, 0 <= r <= max_{0 <= i < len(nums)} nums[i].
  Preconditions: 1 <= len(nums) <= 10^5; 0 <= k <= 10^9; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_4 (nums : Slice I64) (k : I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10 ^ 5)
    (hk_ge : 0 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hvals : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (r : I64) (hres : maximum_top nums k = ok r) (hne : r.val ≠ -1) :
    0 ≤ r.val ∧ r.val ≤ maxEntry nums := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10 ^ 5)
    (hk_ge : 0 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hvals : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (r : I64) (hres : maximum_top nums k = ok r) (hne : r.val ≠ -1), 0 ≤ r.val ∧ r.val ≤ maxEntry nums) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if len(nums) = 1 and k is odd.
  Preconditions: 1 <= len(nums) <= 10^5; 0 <= k <= 10^9; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9. -/
theorem spec_5 (nums : Slice I64) (k : I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10 ^ 5)
    (hk_ge : 0 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hvals : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (r : I64) (hres : maximum_top nums k = ok r) :
    (r.val = -1 ↔ nums.val.length = 1 ∧ Odd k.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10 ^ 5)
    (hk_ge : 0 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hvals : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (r : I64) (hres : maximum_top nums k = ok r), (r.val = -1 ↔ nums.val.length = 1 ∧ Odd k.val)) := by
  sorry

/-- The function returns r and r >= nums[k].
  Preconditions: 1 <= len(nums) <= 10^5; 0 <= k <= 10^9; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9; let n = len(nums); n >= 2; 1 <= k < n. -/
theorem spec_6 (nums : Slice I64) (k : I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10 ^ 5)
    (hk_ge : 0 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hvals : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hn : 2 ≤ nums.val.length) (hk_one : 1 ≤ k.val)
    (hkn : k.val < (nums.val.length : Int)) :
    ∃ r, maximum_top nums k = ok r ∧ valAt nums k.val.toNat ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10 ^ 5)
    (hk_ge : 0 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hvals : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hn : 2 ≤ nums.val.length) (hk_one : 1 ≤ k.val)
    (hkn : k.val < (nums.val.length : Int)), ∃ r, maximum_top nums k = ok r ∧ valAt nums k.val.toNat ≤ r.val) := by
  sorry

/-- The function returns r and, for every i with 0 <= i <= k-2, r >= nums[i].
  Preconditions: 1 <= len(nums) <= 10^5; 0 <= k <= 10^9; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^9; let n = len(nums); n >= 2; 2 <= k < n. -/
theorem spec_7 (nums : Slice I64) (k : I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10 ^ 5)
    (hk_ge : 0 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hvals : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hn : 2 ≤ nums.val.length) (hk_two : 2 ≤ k.val)
    (hkn : k.val < (nums.val.length : Int)) :
    ∃ r, maximum_top nums k = ok r ∧
      ∀ i : Nat, (i : Int) ≤ k.val - 2 → valAt nums i ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10 ^ 5)
    (hk_ge : 0 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hvals : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hn : 2 ≤ nums.val.length) (hk_two : 2 ≤ k.val)
    (hkn : k.val < (nums.val.length : Int)), ∃ r, maximum_top nums k = ok r ∧
      ∀ i : Nat, (i : Int) ≤ k.val - 2 → valAt nums i ≤ r.val) := by
  sorry

/-- Whenever maximum_top nums k returns r and maximum_top nums' k returns r', we have r = r'.
  Preconditions: Both nums and nums' satisfy 1 <= len <= 10^5 and all entries are between 0 and 10^9; 0 <= k <= 10^9; 0 <= k < len(nums); 0 <= k < len(nums'); for every i with 0 <= i <= k, nums[i] = nums'[i]. -/
theorem spec_8 (nums nums' : Slice I64) (k : I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10 ^ 5)
    (hlen_ge' : 1 ≤ nums'.val.length) (hlen_le' : nums'.val.length ≤ 10 ^ 5)
    (hvals : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hvals' : ∀ x ∈ nums'.val, 0 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hk_ge : 0 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hkn : k.val < (nums.val.length : Int))
    (hkn' : k.val < (nums'.val.length : Int))
    (hagree : ∀ i : Nat, (i : Int) ≤ k.val → valAt nums i = valAt nums' i)
    (r r' : I64) (hres : maximum_top nums k = ok r)
    (hres' : maximum_top nums' k = ok r') :
    r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice I64) (k : I64)
    (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10 ^ 5)
    (hlen_ge' : 1 ≤ nums'.val.length) (hlen_le' : nums'.val.length ≤ 10 ^ 5)
    (hvals : ∀ x ∈ nums.val, 0 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hvals' : ∀ x ∈ nums'.val, 0 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (hk_ge : 0 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hkn : k.val < (nums.val.length : Int))
    (hkn' : k.val < (nums'.val.length : Int))
    (hagree : ∀ i : Nat, (i : Int) ≤ k.val → valAt nums i = valAt nums' i)
    (r r' : I64) (hres : maximum_top nums k = ok r)
    (hres' : maximum_top nums' k = ok r'), r = r') := by
  sorry

end AegisSpec.MaximumTop
