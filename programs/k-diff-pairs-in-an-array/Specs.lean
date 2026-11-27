import Aegis.FindPairs.Code.Funs

/-!
# Specifications of `Aegis.FindPairs.find_pairs`

LeetCode problem `k-diff-pairs-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindPairs

def cnt (nums : Slice I64) (v : ℤ) : ℕ :=
  (nums.val.map (fun x => x.val)).countP (fun w => w = v)

def support (nums : Slice I64) : Set ℤ :=
  {v : ℤ | 1 ≤ cnt nums v}

def repeated (nums : Slice I64) : Set ℤ :=
  {v : ℤ | 2 ≤ cnt nums v}

def pairSources (nums : Slice I64) (k : ℤ) : Set ℤ :=
  {x : ℤ | 1 ≤ cnt nums x ∧ 1 ≤ cnt nums (x + k)}

def bounded (nums : Slice I64) : Prop :=
  ∀ (i : ℕ) (_hi : i < nums.val.length),
    -(10 : ℤ) ^ 7 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 : ℤ) ^ 7

/-- Whenever the function returns a result r, the following holds. Let cnt(v) be the number of indices i with 0 ≤ i < len(nums) and nums[i] = v. If k > 0, then r = |{ x ∈ ℤ : cnt(x) ≥ 1 ∧ cnt(x + k) ≥ 1 }|. If k = 0, then r = |{ x ∈ ℤ : cnt(x) ≥ 2 }|. Here |S| denotes the number of elements of the finite set S. Pairs are unordered and unique by their values, so each distinct pair of values is counted once.
  Preconditions: nums is a slice of 64-bit integers with len(nums) ≥ 1, for every i with 0 ≤ i < len(nums) it holds that -10^7 ≤ nums[i] ≤ 10^7, and k is a 64-bit integer with 0 ≤ k ≤ 10^7. -/
theorem spec_1 (nums : Slice I64) (k : I64)
    (_hlen : 1 ≤ nums.val.length) (_hb : bounded nums)
    (_hk_lo : 0 ≤ k.val) (_hk_hi : k.val ≤ (10 : ℤ) ^ 7) :
    ∀ r : I64, Aegis.FindPairs.find_pairs nums k = ok r →
      (0 < k.val → r.val = ((pairSources nums k.val).ncard : ℤ)) ∧
      (k.val = 0 → r.val = ((repeated nums).ncard : ℤ)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (_hlen : 1 ≤ nums.val.length) (_hb : bounded nums)
    (_hk_lo : 0 ≤ k.val) (_hk_hi : k.val ≤ (10 : ℤ) ^ 7), ∀ r : I64, Aegis.FindPairs.find_pairs nums k = ok r →
      (0 < k.val → r.val = ((pairSources nums k.val).ncard : ℤ)) ∧
      (k.val = 0 → r.val = ((repeated nums).ncard : ℤ))) := by
  sorry

/-- Whenever the function returns a result r, it holds that r ≥ 0.
  Preconditions: nums is a slice of 64-bit integers with len(nums) ≥ 1, for every i with 0 ≤ i < len(nums) it holds that -10^7 ≤ nums[i] ≤ 10^7, and k is a 64-bit integer with 0 ≤ k ≤ 10^7. -/
theorem spec_2 (nums : Slice I64) (k : I64)
    (_hlen : 1 ≤ nums.val.length) (_hb : bounded nums)
    (_hk_lo : 0 ≤ k.val) (_hk_hi : k.val ≤ (10 : ℤ) ^ 7) :
    ∀ r : I64, Aegis.FindPairs.find_pairs nums k = ok r → 0 ≤ r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (_hlen : 1 ≤ nums.val.length) (_hb : bounded nums)
    (_hk_lo : 0 ≤ k.val) (_hk_hi : k.val ≤ (10 : ℤ) ^ 7), ∀ r : I64, Aegis.FindPairs.find_pairs nums k = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, it holds that r ≤ len(nums).
  Preconditions: nums is a slice of 64-bit integers with len(nums) ≥ 1, for every i with 0 ≤ i < len(nums) it holds that -10^7 ≤ nums[i] ≤ 10^7, and k is a 64-bit integer with 0 ≤ k ≤ 10^7. -/
theorem spec_3 (nums : Slice I64) (k : I64)
    (_hlen : 1 ≤ nums.val.length) (_hb : bounded nums)
    (_hk_lo : 0 ≤ k.val) (_hk_hi : k.val ≤ (10 : ℤ) ^ 7) :
    ∀ r : I64, Aegis.FindPairs.find_pairs nums k = ok r → r.val ≤ (nums.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (_hlen : 1 ≤ nums.val.length) (_hb : bounded nums)
    (_hk_lo : 0 ≤ k.val) (_hk_hi : k.val ≤ (10 : ℤ) ^ 7), ∀ r : I64, Aegis.FindPairs.find_pairs nums k = ok r → r.val ≤ (nums.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, it holds that r ≤ |{ v ∈ ℤ : cnt(v) ≥ 1 }|, where cnt(v) is the number of indices i with 0 ≤ i < len(nums) and nums[i] = v.
  Preconditions: nums is a slice of 64-bit integers with len(nums) ≥ 1, for every i with 0 ≤ i < len(nums) it holds that -10^7 ≤ nums[i] ≤ 10^7, and k is a 64-bit integer with 0 ≤ k ≤ 10^7. -/
theorem spec_4 (nums : Slice I64) (k : I64)
    (_hlen : 1 ≤ nums.val.length) (_hb : bounded nums)
    (_hk_lo : 0 ≤ k.val) (_hk_hi : k.val ≤ (10 : ℤ) ^ 7) :
    ∀ r : I64, Aegis.FindPairs.find_pairs nums k = ok r → r.val ≤ ((support nums).ncard : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (_hlen : 1 ≤ nums.val.length) (_hb : bounded nums)
    (_hk_lo : 0 ≤ k.val) (_hk_hi : k.val ≤ (10 : ℤ) ^ 7), ∀ r : I64, Aegis.FindPairs.find_pairs nums k = ok r → r.val ≤ ((support nums).ncard : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, it holds that r = 0 if and only if for all indices i, j with 0 ≤ i < len(nums), 0 ≤ j < len(nums), and i ≠ j, we have |nums[i] - nums[j]| ≠ k.
  Preconditions: nums is a slice of 64-bit integers with len(nums) ≥ 1, for every i with 0 ≤ i < len(nums) it holds that -10^7 ≤ nums[i] ≤ 10^7, and k is a 64-bit integer with 0 ≤ k ≤ 10^7. -/
theorem spec_5 (nums : Slice I64) (k : I64)
    (_hlen : 1 ≤ nums.val.length) (_hb : bounded nums)
    (_hk_lo : 0 ≤ k.val) (_hk_hi : k.val ≤ (10 : ℤ) ^ 7) :
    ∀ r : I64, Aegis.FindPairs.find_pairs nums k = ok r →
      (r.val = 0 ↔
        ∀ (i j : ℕ) (_hi : i < nums.val.length) (_hj : j < nums.val.length), i ≠ j →
          |(nums.val[i]).val - (nums.val[j]).val| ≠ k.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (_hlen : 1 ≤ nums.val.length) (_hb : bounded nums)
    (_hk_lo : 0 ≤ k.val) (_hk_hi : k.val ≤ (10 : ℤ) ^ 7), ∀ r : I64, Aegis.FindPairs.find_pairs nums k = ok r →
      (r.val = 0 ↔
        ∀ (i j : ℕ) (_hi : i < nums.val.length) (_hj : j < nums.val.length), i ≠ j →
          |(nums.val[i]).val - (nums.val[j]).val| ≠ k.val)) := by
  sorry

/-- Whenever the function returns a result r for nums and a result r' for nums', we have r = r'.
  Preconditions: nums is a slice of 64-bit integers with len(nums) ≥ 1, for every i with 0 ≤ i < len(nums) it holds that -10^7 ≤ nums[i] ≤ 10^7, and k is a 64-bit integer with 0 ≤ k ≤ 10^7. nums' is a slice of 64-bit integers with len(nums') = len(nums), for every i it holds that -10^7 ≤ nums'[i] ≤ 10^7, and for every integer v, the number of indices i with nums'[i] = v equals the number of indices i with nums[i] = v (i.e., nums' is a permutation of nums). -/
theorem spec_6 (nums nums' : Slice I64) (k : I64)
    (_hlen : 1 ≤ nums.val.length) (_hb : bounded nums)
    (_hk_lo : 0 ≤ k.val) (_hk_hi : k.val ≤ (10 : ℤ) ^ 7)
    (_hlen' : nums'.val.length = nums.val.length) (_hb' : bounded nums')
    (_hperm : ∀ v : ℤ, cnt nums' v = cnt nums v) :
    ∀ r r' : I64, Aegis.FindPairs.find_pairs nums k = ok r →
      Aegis.FindPairs.find_pairs nums' k = ok r' → r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums nums' : Slice I64) (k : I64)
    (_hlen : 1 ≤ nums.val.length) (_hb : bounded nums)
    (_hk_lo : 0 ≤ k.val) (_hk_hi : k.val ≤ (10 : ℤ) ^ 7)
    (_hlen' : nums'.val.length = nums.val.length) (_hb' : bounded nums')
    (_hperm : ∀ v : ℤ, cnt nums' v = cnt nums v), ∀ r r' : I64, Aegis.FindPairs.find_pairs nums k = ok r →
      Aegis.FindPairs.find_pairs nums' k = ok r' → r = r') := by
  sorry

/-- Whenever the function returns a result r for nums and a result r' for nums', we have r' ≥ r.
  Preconditions: nums is a slice of 64-bit integers with len(nums) ≥ 1, for every i with 0 ≤ i < len(nums) it holds that -10^7 ≤ nums[i] ≤ 10^7, and k is a 64-bit integer with 0 ≤ k ≤ 10^7. nums' is a slice of 64-bit integers with len(nums') = len(nums) + 1, for every i with 0 ≤ i < len(nums) we have nums'[i] = nums[i], and nums'[len(nums)] is some 64-bit integer with -10^7 ≤ nums'[len(nums)] ≤ 10^7. -/
theorem spec_7 (nums nums' : Slice I64) (k : I64)
    (_hlen : 1 ≤ nums.val.length) (_hb : bounded nums)
    (_hk_lo : 0 ≤ k.val) (_hk_hi : k.val ≤ (10 : ℤ) ^ 7)
    (_hlen' : nums'.val.length = nums.val.length + 1)
    (_hprefix : ∀ (i : ℕ) (hi : i < nums.val.length), nums'.val[i]'(by omega) = nums.val[i])
    (_hlast : -(10 : ℤ) ^ 7 ≤ (nums'.val[nums.val.length]'(by omega)).val ∧
      (nums'.val[nums.val.length]'(by omega)).val ≤ (10 : ℤ) ^ 7) :
    ∀ r r' : I64, Aegis.FindPairs.find_pairs nums k = ok r →
      Aegis.FindPairs.find_pairs nums' k = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums nums' : Slice I64) (k : I64)
    (_hlen : 1 ≤ nums.val.length) (_hb : bounded nums)
    (_hk_lo : 0 ≤ k.val) (_hk_hi : k.val ≤ (10 : ℤ) ^ 7)
    (_hlen' : nums'.val.length = nums.val.length + 1)
    (_hprefix : ∀ (i : ℕ) (hi : i < nums.val.length), nums'.val[i]'(by omega) = nums.val[i])
    (_hlast : -(10 : ℤ) ^ 7 ≤ (nums'.val[nums.val.length]'(by omega)).val ∧
      (nums'.val[nums.val.length]'(by omega)).val ≤ (10 : ℤ) ^ 7), ∀ r r' : I64, Aegis.FindPairs.find_pairs nums k = ok r →
      Aegis.FindPairs.find_pairs nums' k = ok r' → r.val ≤ r'.val) := by
  sorry

/-- The function returns a result r (it does not panic, overflow, or go out of bounds).
  Preconditions: nums is a slice of 64-bit integers with len(nums) ≥ 1, for every i with 0 ≤ i < len(nums) it holds that -10^7 ≤ nums[i] ≤ 10^7, and k is a 64-bit integer with 0 ≤ k ≤ 10^7. -/
theorem spec_8 (nums : Slice I64) (k : I64)
    (_hlen : 1 ≤ nums.val.length) (_hb : bounded nums)
    (_hk_lo : 0 ≤ k.val) (_hk_hi : k.val ≤ (10 : ℤ) ^ 7) :
    ∃ r : I64, Aegis.FindPairs.find_pairs nums k = ok r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (_hlen : 1 ≤ nums.val.length) (_hb : bounded nums)
    (_hk_lo : 0 ≤ k.val) (_hk_hi : k.val ≤ (10 : ℤ) ^ 7), ∃ r : I64, Aegis.FindPairs.find_pairs nums k = ok r) := by
  sorry

end AegisSpec.FindPairs
