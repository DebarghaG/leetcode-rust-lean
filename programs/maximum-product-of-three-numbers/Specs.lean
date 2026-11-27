import Aegis.MaximumProduct.Code.Funs

/-!
# Specifications of `Aegis.MaximumProduct.maximum_product`

LeetCode problem `maximum-product-of-three-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaximumProduct

namespace AegisSpec.MaximumProduct

def entries (nums : Slice Std.I64) : List ℤ :=
  nums.val.map (fun x => x.val)

def entry (nums : Slice Std.I64) (i : Nat) : ℤ := (nums.val[i]!).val

def sortedEntries (nums : Slice Std.I64) : List ℤ :=
  (entries nums).mergeSort (fun a b => a ≤ b)

def sortedEntry (nums : Slice Std.I64) (t : Nat) : ℤ :=
  (sortedEntries nums)[t]!

/-- The function returns a result r, and r is exactly the maximum product of three entries at distinct positions: (a) for every i, j, k with 0 <= i < j < k < len(nums), nums[i] * nums[j] * nums[k] <= r; and (b) there exist p, q, s with 0 <= p < q < s < len(nums) such that nums[p] * nums[q] * nums[s] = r.
  Preconditions: len(nums) is between 3 and 10000 inclusive, and for every index i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000) :
    ∃ r : Std.I64, maximum_product nums = ok r ∧
      (∀ i j k : Nat, i < j → j < k → k < nums.val.length →
        entry nums i * entry nums j * entry nums k ≤ r.val) ∧
      (∃ p q s : Nat, p < q ∧ q < s ∧ s < nums.val.length ∧
        entry nums p * entry nums q * entry nums s = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000), ∃ r : Std.I64, maximum_product nums = ok r ∧
      (∀ i j k : Nat, i < j → j < k → k < nums.val.length →
        entry nums i * entry nums j * entry nums k ≤ r.val) ∧
      (∃ p q s : Nat, p < q ∧ q < s ∧ s < nums.val.length ∧
        entry nums p * entry nums q * entry nums s = r.val)) := by
  sorry

/-- Under these preconditions the function returns a result r; it does not fail (no overflow, out-of-bounds, or panic).
  Preconditions: len(nums) is between 3 and 10000 inclusive, and for every index i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000) :
    ∃ r : Std.I64, maximum_product nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000), ∃ r : Std.I64, maximum_product nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, -1000000000 <= r <= 1000000000.
  Preconditions: len(nums) is between 3 and 10000 inclusive, and for every index i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000) :
    ∀ r : Std.I64, maximum_product nums = ok r →
      -1000000000 ≤ r.val ∧ r.val ≤ 1000000000 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000), ∀ r : Std.I64, maximum_product nums = ok r →
      -1000000000 ≤ r.val ∧ r.val ≤ 1000000000) := by
  sorry

/-- Whenever the function returns a result r, there exist indices i, j, k with 0 <= i < j < k < len(nums) such that r = nums[i] * nums[j] * nums[k].
  Preconditions: len(nums) is between 3 and 10000 inclusive, and for every index i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000) :
    ∀ r : Std.I64, maximum_product nums = ok r →
      ∃ i j k : Nat, i < j ∧ j < k ∧ k < nums.val.length ∧
        r.val = entry nums i * entry nums j * entry nums k := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000), ∀ r : Std.I64, maximum_product nums = ok r →
      ∃ i j k : Nat, i < j ∧ j < k ∧ k < nums.val.length ∧
        r.val = entry nums i * entry nums j * entry nums k) := by
  sorry

/-- Whenever the function returns a result r, for every triple of indices i, j, k with 0 <= i < j < k < len(nums), we have nums[i] * nums[j] * nums[k] <= r.
  Preconditions: len(nums) is between 3 and 10000 inclusive, and for every index i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000) :
    ∀ r : Std.I64, maximum_product nums = ok r →
      ∀ i j k : Nat, i < j → j < k → k < nums.val.length →
        entry nums i * entry nums j * entry nums k ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000), ∀ r : Std.I64, maximum_product nums = ok r →
      ∀ i j k : Nat, i < j → j < k → k < nums.val.length →
        entry nums i * entry nums j * entry nums k ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, let a_0 <= a_1 <= ... <= a_{len(nums)-1} be the entries of nums sorted in nondecreasing order (counting duplicates). Then r = max(a_0 * a_1 * a_{len(nums)-1}, a_{len(nums)-3} * a_{len(nums)-2} * a_{len(nums)-1}).
  Preconditions: len(nums) is between 3 and 10000 inclusive, and for every index i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000) :
    ∀ r : Std.I64, maximum_product nums = ok r →
      r.val = max
        (sortedEntry nums 0 * sortedEntry nums 1 * sortedEntry nums (nums.val.length - 1))
        (sortedEntry nums (nums.val.length - 3) * sortedEntry nums (nums.val.length - 2) *
          sortedEntry nums (nums.val.length - 1)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000), ∀ r : Std.I64, maximum_product nums = ok r →
      r.val = max
        (sortedEntry nums 0 * sortedEntry nums 1 * sortedEntry nums (nums.val.length - 1))
        (sortedEntry nums (nums.val.length - 3) * sortedEntry nums (nums.val.length - 2) *
          sortedEntry nums (nums.val.length - 1))) := by
  sorry

/-- Whenever the function returns a result r, let a_0 <= a_1 <= ... <= a_{len(nums)-1} be the entries of nums sorted in nondecreasing order. Then r = a_{len(nums)-3} * a_{len(nums)-2} * a_{len(nums)-1}.
  Preconditions: len(nums) is between 3 and 10000 inclusive, for every index i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000, and either (for every i, nums[i] >= 0) or (for every i, nums[i] <= 0). -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000)
    (hsign : (∀ i : Nat, i < nums.val.length → 0 ≤ entry nums i) ∨
      (∀ i : Nat, i < nums.val.length → entry nums i ≤ 0)) :
    ∀ r : Std.I64, maximum_product nums = ok r →
      r.val = sortedEntry nums (nums.val.length - 3) * sortedEntry nums (nums.val.length - 2) *
        sortedEntry nums (nums.val.length - 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000)
    (hsign : (∀ i : Nat, i < nums.val.length → 0 ≤ entry nums i) ∨
      (∀ i : Nat, i < nums.val.length → entry nums i ≤ 0)), ∀ r : Std.I64, maximum_product nums = ok r →
      r.val = sortedEntry nums (nums.val.length - 3) * sortedEntry nums (nums.val.length - 2) *
        sortedEntry nums (nums.val.length - 1)) := by
  sorry

/-- Whenever the function returns a result r, if there exists an index z with 0 <= z < len(nums) and nums[z] = 0, then r >= 0.
  Preconditions: len(nums) is between 3 and 10000 inclusive, and for every index i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000) :
    ∀ r : Std.I64, maximum_product nums = ok r →
      (∃ z : Nat, z < nums.val.length ∧ entry nums z = 0) → 0 ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000), ∀ r : Std.I64, maximum_product nums = ok r →
      (∃ z : Nat, z < nums.val.length ∧ entry nums z = 0) → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if there exist indices i, j, k with 0 <= i < j < k < len(nums) and nums[i] * nums[j] * nums[k] > 0, then r > 0.
  Preconditions: len(nums) is between 3 and 10000 inclusive, and for every index i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000) :
    ∀ r : Std.I64, maximum_product nums = ok r →
      (∃ i j k : Nat, i < j ∧ j < k ∧ k < nums.val.length ∧
        0 < entry nums i * entry nums j * entry nums k) → 0 < r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000), ∀ r : Std.I64, maximum_product nums = ok r →
      (∃ i j k : Nat, i < j ∧ j < k ∧ k < nums.val.length ∧
        0 < entry nums i * entry nums j * entry nums k) → 0 < r.val) := by
  sorry

/-- Whenever the function returns r on nums and r' on nums', we have r = r'.
  Preconditions: len(nums) is between 3 and 10000 inclusive, for every index i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000, and nums' is any slice with len(nums') = len(nums) and the same multiset of entries as nums. -/
theorem spec_10 (nums nums' : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000)
    (hlen' : nums'.val.length = nums.val.length)
    (hperm : (entries nums').Perm (entries nums)) :
    ∀ r r' : Std.I64, maximum_product nums = ok r → maximum_product nums' = ok r' → r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hlen : 3 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 10000)
    (hbnd : ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000)
    (hlen' : nums'.val.length = nums.val.length)
    (hperm : (entries nums').Perm (entries nums)), ∀ r r' : Std.I64, maximum_product nums = ok r → maximum_product nums' = ok r' → r = r') := by
  sorry

end AegisSpec.MaximumProduct
