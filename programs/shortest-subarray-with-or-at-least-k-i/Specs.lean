import Aegis.MinimumSubarrayLength.Code.Funs

/-!
# Specifications of `Aegis.MinimumSubarrayLength.minimum_subarray_length`

LeetCode problem `shortest-subarray-with-or-at-least-k-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumSubarrayLength

def listOR (xs : List I64) : ℕ :=
  List.foldl (fun acc x => acc ||| x.val.toNat) 0 xs

def segOR (xs : List I64) (l h : ℕ) : ℕ :=
  listOR (List.take (h + 1 - l) (List.drop l xs))

def Special (nums : List I64) (k : I64) (l h : ℕ) : Prop :=
  l ≤ h ∧ h < nums.length ∧ k.val ≤ (segOR nums l h : ℤ)

def HasSpecial (nums : List I64) (k : I64) : Prop :=
  ∃ l h : ℕ, Special nums k l h

def FullORGe (nums : List I64) (k : I64) : Prop :=
  k.val ≤ (listOR nums : ℤ)

/-- For a contiguous subarray nums[l..h] with 0 <= l <= h < len(nums), let OR(l,h) denote the bitwise OR of nums[l], nums[l+1], ..., nums[h]. Whenever the function returns a result ans, ans is the length of a shortest special non-empty contiguous subarray, or -1 if no special subarray exists: (1) if there exists a pair (l,h) with 0 <= l <= h < len(nums) and OR(l,h) >= k, then 1 <= ans <= len(nums), there exists such a pair with h-l+1 = ans, and every such pair satisfies h-l+1 >= ans; (2) if no such pair exists, then ans = -1.
  Preconditions: 1 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; 0 <= k < 64. -/
theorem spec_1 (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64) :
    ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      ((HasSpecial nums.val k →
          (1 ≤ ans.val ∧ ans.val ≤ (nums.val.length : ℤ)) ∧
          (∃ l h : ℕ, Special nums.val k l h ∧ (h : ℤ) - (l : ℤ) + 1 = ans.val) ∧
          (∀ (l h : ℕ), Special nums.val k l h →
            ans.val ≤ (h : ℤ) - (l : ℤ) + 1)) ∧
        (¬ HasSpecial nums.val k → ans.val = -1)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64), ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      ((HasSpecial nums.val k →
          (1 ≤ ans.val ∧ ans.val ≤ (nums.val.length : ℤ)) ∧
          (∃ l h : ℕ, Special nums.val k l h ∧ (h : ℤ) - (l : ℤ) + 1 = ans.val) ∧
          (∀ (l h : ℕ), Special nums.val k l h →
            ans.val ≤ (h : ℤ) - (l : ℤ) + 1)) ∧
        (¬ HasSpecial nums.val k → ans.val = -1))) := by
  sorry

/-- For every nums and k satisfying the preconditions, the function returns a result ans; it does not fail, panic, or overflow.
  Preconditions: 1 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; 0 <= k < 64. -/
theorem spec_2 (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64) :
    ∃ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64), ∃ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans) := by
  sorry

/-- Whenever the function returns a result ans, either ans = -1 or 1 <= ans <= len(nums).
  Preconditions: 1 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; 0 <= k < 64. -/
theorem spec_3 (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64) :
    ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      ans.val = -1 ∨ (1 ≤ ans.val ∧ ans.val ≤ (nums.val.length : ℤ)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64), ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      ans.val = -1 ∨ (1 ≤ ans.val ∧ ans.val ≤ (nums.val.length : ℤ))) := by
  sorry

/-- Whenever the function returns a result ans with ans > 0, there exists an integer l such that 0 <= l, l + ans - 1 < len(nums), and the bitwise OR of nums[l], nums[l+1], ..., nums[l+ans-1] is at least k.
  Preconditions: 1 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; 0 <= k < 64. -/
theorem spec_4 (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64) :
    ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      0 < ans.val →
        ∃ l h : ℕ, l ≤ h ∧ h < nums.val.length ∧
          (h : ℤ) - (l : ℤ) + 1 = ans.val ∧ k.val ≤ (segOR nums.val l h : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64), ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      0 < ans.val →
        ∃ l h : ℕ, l ≤ h ∧ h < nums.val.length ∧
          (h : ℤ) - (l : ℤ) + 1 = ans.val ∧ k.val ≤ (segOR nums.val l h : ℤ)) := by
  sorry

/-- Whenever the function returns a result ans with ans > 0, every non-empty contiguous subarray nums[l..h], where 0 <= l <= h < len(nums), whose bitwise OR is at least k has length h - l + 1 >= ans.
  Preconditions: 1 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; 0 <= k < 64. -/
theorem spec_5 (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64) :
    ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      0 < ans.val →
        ∀ (l h : ℕ), Special nums.val k l h → ans.val ≤ (h : ℤ) - (l : ℤ) + 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64), ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      0 < ans.val →
        ∀ (l h : ℕ), Special nums.val k l h → ans.val ≤ (h : ℤ) - (l : ℤ) + 1) := by
  sorry

/-- Whenever the function returns a result ans with ans = -1, every non-empty contiguous subarray nums[l..h], where 0 <= l <= h < len(nums), has bitwise OR strictly less than k.
  Preconditions: 1 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; 0 <= k < 64. -/
theorem spec_6 (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64) :
    ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      ans.val = -1 →
        ∀ (l h : ℕ), l ≤ h → h < nums.val.length →
          (segOR nums.val l h : ℤ) < k.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64), ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      ans.val = -1 →
        ∀ (l h : ℕ), l ≤ h → h < nums.val.length →
          (segOR nums.val l h : ℤ) < k.val) := by
  sorry

/-- Whenever the function returns a result ans, ans = 1 if and only if there exists an index i with 0 <= i < len(nums) and nums[i] >= k.
  Preconditions: 1 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; 0 <= k < 64. -/
theorem spec_7 (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64) :
    ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      (ans.val = 1 ↔
        ∃ (i : ℕ) (hi : i < nums.val.length), k.val ≤ (nums.val[i]'hi).val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64), ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      (ans.val = 1 ↔
        ∃ (i : ℕ) (hi : i < nums.val.length), k.val ≤ (nums.val[i]'hi).val)) := by
  sorry

/-- Let FullOR be the bitwise OR of all elements nums[0], nums[1], ..., nums[len(nums)-1]. Whenever the function returns a result ans, ans = -1 if and only if FullOR < k.
  Preconditions: 1 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; 0 <= k < 64. -/
theorem spec_8 (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64) :
    ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      (ans.val = -1 ↔ ¬ FullORGe nums.val k) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64), ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      (ans.val = -1 ↔ ¬ FullORGe nums.val k)) := by
  sorry

/-- Whenever the function returns a result ans and len(nums) = 1, ans = 1 if nums[0] >= k, and ans = -1 if nums[0] < k.
  Preconditions: 1 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; 0 <= k < 64. -/
theorem spec_9 (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64) :
    ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      nums.val.length = 1 →
        ((k.val ≤ (nums.val[0]'(by omega)).val → ans.val = 1) ∧
         ((nums.val[0]'(by omega)).val < k.val → ans.val = -1)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64), ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      nums.val.length = 1 →
        ((k.val ≤ (nums.val[0]'(by omega)).val → ans.val = 1) ∧
         ((nums.val[0]'(by omega)).val < k.val → ans.val = -1))) := by
  sorry

/-- Whenever the function returns a result ans with ans = len(nums), the bitwise OR of all elements nums[0], nums[1], ..., nums[len(nums)-1] is at least k.
  Preconditions: 1 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; 0 <= k < 64. -/
theorem spec_10 (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64) :
    ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      ans.val = (nums.val.length : ℤ) → FullORGe nums.val k := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64), ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      ans.val = (nums.val.length : ℤ) → FullORGe nums.val k) := by
  sorry

/-- Whenever the function returns a result ans and k = 0, ans = 1.
  Preconditions: 1 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; 0 <= k < 64. -/
theorem spec_11 (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64) :
    ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      k.val = 0 → ans.val = 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64), ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      k.val = 0 → ans.val = 1) := by
  sorry

/-- Whenever the function returns a result ans and every element of nums is 0, ans = 1 if k = 0 and ans = -1 if k > 0.
  Preconditions: 1 <= len(nums) <= 50; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; 0 <= k < 64. -/
theorem spec_12 (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64) :
    ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      (∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]'hi).val = 0) →
        ((k.val = 0 → ans.val = 1) ∧ (0 < k.val → ans.val = -1)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 50)
    (hnum : ∀ (i : ℕ) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
    (hk0 : 0 ≤ k.val) (hk64 : k.val < 64), ∀ ans : I64, Aegis.MinimumSubarrayLength.minimum_subarray_length nums k = ok ans →
      (∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]'hi).val = 0) →
        ((k.val = 0 → ans.val = 1) ∧ (0 < k.val → ans.val = -1))) := by
  sorry

end AegisSpec.MinimumSubarrayLength
