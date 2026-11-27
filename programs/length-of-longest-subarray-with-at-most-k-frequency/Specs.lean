import Aegis.MaxSubarrayLength.Code.Funs

/-!
# Specifications of `Aegis.MaxSubarrayLength.max_subarray_length`

LeetCode problem `length-of-longest-subarray-with-at-most-k-frequency`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxSubarrayLength (max_subarray_length)

namespace AegisSpec.MaxSubarrayLength

noncomputable section

open Classical

def elems (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

def countIn (xs : List ℤ) (l r : ℕ) (v : ℤ) : ℕ :=
  ((xs.drop l).take (r - l)).countP (fun x => x = v)

def GoodWindow (xs : List ℤ) (k : ℤ) (l r : ℕ) : Prop :=
  ∀ v : ℤ, (countIn xs l r v : ℤ) ≤ k

def maxGoodLen (xs : List ℤ) (k : ℤ) : ℕ :=
  ((Finset.range (xs.length + 1)).product (Finset.range (xs.length + 1))).sup
    (fun p : ℕ × ℕ =>
      if p.1 < p.2 ∧ GoodWindow xs k p.1 p.2 then p.2 - p.1 else 0)

def PairwiseDistinctWindow (xs : List ℤ) (l r : ℕ) : Prop :=
  ((xs.drop l).take (r - l)).Nodup

def maxDistinctLen (xs : List ℤ) : ℕ :=
  ((Finset.range (xs.length + 1)).product (Finset.range (xs.length + 1))).sup
    (fun p : ℕ × ℕ =>
      if p.1 < p.2 ∧ PairwiseDistinctWindow xs p.1 p.2 then p.2 - p.1 else 0)

def distinctCount (xs : List ℤ) : ℕ := xs.dedup.length

def Pre (nums : Slice I64) (k : I64) : Prop :=
  1 ≤ nums.val.length ∧ nums.val.length ≤ 100000 ∧
    (∀ (i : ℕ) (h : i < nums.val.length), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000) ∧
    1 ≤ k.val ∧ k.val ≤ (nums.val.length : ℤ)

/-- The function returns a result res and res equals the maximum length of a good subarray of nums. A subarray is a pair (l, r) with 0 <= l < r <= len(nums) representing the sequence nums[l], nums[l+1], ..., nums[r-1], and its length is r - l. It is good if for every integer value v, the number of indices i with l <= i < r and nums[i] = v is at most k. Equivalently, for every index i with l <= i < r, the number of indices j with l <= j < r and nums[j] = nums[i] is at most k. Thus res = max { r - l | 0 <= l < r <= len(nums) and nums[l..r) is good }.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= len(nums). -/
theorem spec_1 (nums : Slice I64) (k : I64) (hpre : Pre nums k) :
    ∃ res : I64, max_subarray_length nums k = ok res ∧
      res.val = ((maxGoodLen (elems nums) k.val : ℕ) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : Pre nums k), ∃ res : I64, max_subarray_length nums k = ok res ∧
      res.val = ((maxGoodLen (elems nums) k.val : ℕ) : ℤ)) := by
  sorry

/-- The function returns a result res and 1 <= res <= len(nums).
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= len(nums). -/
theorem spec_2 (nums : Slice I64) (k : I64) (hpre : Pre nums k) :
    ∃ res : I64, max_subarray_length nums k = ok res ∧
      1 ≤ res.val ∧ res.val ≤ (nums.val.length : ℤ) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : Pre nums k), ∃ res : I64, max_subarray_length nums k = ok res ∧
      1 ≤ res.val ∧ res.val ≤ (nums.val.length : ℤ)) := by
  sorry

/-- The function returns a result res and res >= k.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= len(nums). -/
theorem spec_3 (nums : Slice I64) (k : I64) (hpre : Pre nums k) :
    ∃ res : I64, max_subarray_length nums k = ok res ∧ k.val ≤ res.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : Pre nums k), ∃ res : I64, max_subarray_length nums k = ok res ∧ k.val ≤ res.val) := by
  sorry

/-- The function does not fail: for every input satisfying the preconditions, it returns a result res without overflow, panic, or out-of-bounds access.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= len(nums). -/
theorem spec_4 (nums : Slice I64) (k : I64) (hpre : Pre nums k) :
    ∃ res : I64, max_subarray_length nums k = ok res := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : Pre nums k), ∃ res : I64, max_subarray_length nums k = ok res) := by
  sorry

/-- The function returns a result res and there exists a good subarray of nums of length res. A subarray nums[l..r) (0 <= l < r <= len(nums)) is good if for every integer value v, the count of indices i with l <= i < r and nums[i] = v is at most k.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= len(nums). -/
theorem spec_5 (nums : Slice I64) (k : I64) (hpre : Pre nums k) :
    ∃ res : I64, max_subarray_length nums k = ok res ∧
      ∃ (l r : ℕ), l < r ∧ r ≤ nums.val.length ∧ GoodWindow (elems nums) k.val l r ∧
        res.val = ((r - l : ℕ) : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : Pre nums k), ∃ res : I64, max_subarray_length nums k = ok res ∧
      ∃ (l r : ℕ), l < r ∧ r ≤ nums.val.length ∧ GoodWindow (elems nums) k.val l r ∧
        res.val = ((r - l : ℕ) : ℤ)) := by
  sorry

/-- The function returns a result res and for every good subarray of nums of length L, L <= res. A subarray nums[l..r) (0 <= l < r <= len(nums)) is good if for every integer value v, the count of indices i with l <= i < r and nums[i] = v is at most k.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= len(nums). -/
theorem spec_6 (nums : Slice I64) (k : I64) (hpre : Pre nums k) :
    ∃ res : I64, max_subarray_length nums k = ok res ∧
      ∀ (l r : ℕ), l < r → r ≤ nums.val.length → GoodWindow (elems nums) k.val l r →
        ((r - l : ℕ) : ℤ) ≤ res.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : Pre nums k), ∃ res : I64, max_subarray_length nums k = ok res ∧
      ∀ (l r : ℕ), l < r → r ≤ nums.val.length → GoodWindow (elems nums) k.val l r →
        ((r - l : ℕ) : ℤ) ≤ res.val) := by
  sorry

/-- If for every index i with 0 <= i < len(nums), the number of indices j with 0 <= j < len(nums) and nums[j] = nums[i] is at most k, then the function returns a result res and res = len(nums).
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= len(nums). -/
theorem spec_7 (nums : Slice I64) (k : I64) (hpre : Pre nums k)
    (hall : ∀ (i : ℕ) (h : i < nums.val.length),
      (countIn (elems nums) 0 nums.val.length (nums.val[i]).val : ℤ) ≤ k.val) :
    ∃ res : I64, max_subarray_length nums k = ok res ∧ res.val = (nums.val.length : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : Pre nums k)
    (hall : ∀ (i : ℕ) (h : i < nums.val.length),
      (countIn (elems nums) 0 nums.val.length (nums.val[i]).val : ℤ) ≤ k.val), ∃ res : I64, max_subarray_length nums k = ok res ∧ res.val = (nums.val.length : ℤ)) := by
  sorry

/-- If there exists an integer v such that for every i with 0 <= i < len(nums), nums[i] = v, then the function returns a result res and res = k.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= len(nums). -/
theorem spec_8 (nums : Slice I64) (k : I64) (hpre : Pre nums k)
    (hconst : ∃ v : ℤ, ∀ (i : ℕ) (h : i < nums.val.length), (nums.val[i]).val = v) :
    ∃ res : I64, max_subarray_length nums k = ok res ∧ res.val = k.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : Pre nums k)
    (hconst : ∃ v : ℤ, ∀ (i : ℕ) (h : i < nums.val.length), (nums.val[i]).val = v), ∃ res : I64, max_subarray_length nums k = ok res ∧ res.val = k.val) := by
  sorry

/-- If k = 1, then the function returns a result res and res equals the maximum length of a subarray of nums in which all elements are pairwise distinct; that is, there exist l, r with 0 <= l < r <= len(nums) such that r - l = res and for every i, j with l <= i < j < r, nums[i] != nums[j], and for every l', r' with 0 <= l' < r' <= len(nums), if for every i, j with l' <= i < j < r' we have nums[i] != nums[j], then r' - l' <= res.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= len(nums). -/
theorem spec_9 (nums : Slice I64) (k : I64) (hpre : Pre nums k) (hk : k.val = 1) :
    ∃ res : I64, max_subarray_length nums k = ok res ∧
      (∃ (l r : ℕ), l < r ∧ r ≤ nums.val.length ∧
        PairwiseDistinctWindow (elems nums) l r ∧ res.val = ((r - l : ℕ) : ℤ)) ∧
      (∀ (l r : ℕ), l < r → r ≤ nums.val.length → PairwiseDistinctWindow (elems nums) l r →
        ((r - l : ℕ) : ℤ) ≤ res.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : Pre nums k) (hk : k.val = 1), ∃ res : I64, max_subarray_length nums k = ok res ∧
      (∃ (l r : ℕ), l < r ∧ r ≤ nums.val.length ∧
        PairwiseDistinctWindow (elems nums) l r ∧ res.val = ((r - l : ℕ) : ℤ)) ∧
      (∀ (l r : ℕ), l < r → r ≤ nums.val.length → PairwiseDistinctWindow (elems nums) l r →
        ((r - l : ℕ) : ℤ) ≤ res.val)) := by
  sorry

/-- For the given nums and k, let res be the result. Then for every integer k' with 1 <= k' <= k, the maximum length of a good subarray of nums with frequency limit k' is at most res. Here a subarray nums[l..r) is good with limit k' if for every integer value v, the count of indices i with l <= i < r and nums[i] = v is at most k'.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= len(nums). -/
theorem spec_10 (nums : Slice I64) (k : I64) (hpre : Pre nums k) :
    ∃ res : I64, max_subarray_length nums k = ok res ∧
      ∀ k' : ℤ, 1 ≤ k' → k' ≤ k.val → ((maxGoodLen (elems nums) k' : ℕ) : ℤ) ≤ res.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : Pre nums k), ∃ res : I64, max_subarray_length nums k = ok res ∧
      ∀ k' : ℤ, 1 ≤ k' → k' ≤ k.val → ((maxGoodLen (elems nums) k' : ℕ) : ℤ) ≤ res.val) := by
  sorry

/-- The result depends only on the equality pattern of nums: for any array nums' of the same length such that for all i, j with 0 <= i < len(nums) and 0 <= j < len(nums), nums[i] = nums[j] if and only if nums'[i] = nums'[j], and for the same k, the function returns the same result for nums' as for nums. That is, max_subarray_length(nums, k) = max_subarray_length(nums', k).
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= len(nums). -/
theorem spec_11 (nums nums' : Slice I64) (k : I64) (hpre : Pre nums k)
    (hlen : nums'.val.length = nums.val.length)
    (hpattern : ∀ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
      ((nums.val[i]).val = (nums.val[j]).val ↔ (nums'.val[i]).val = (nums'.val[j]).val)) :
    max_subarray_length nums k = max_subarray_length nums' k := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums' : Slice I64) (k : I64) (hpre : Pre nums k)
    (hlen : nums'.val.length = nums.val.length)
    (hpattern : ∀ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
      ((nums.val[i]).val = (nums.val[j]).val ↔ (nums'.val[i]).val = (nums'.val[j]).val)), max_subarray_length nums k = max_subarray_length nums' k) := by
  sorry

/-- Let nums_rev be the array defined by nums_rev[i] = nums[len(nums)-1-i] for 0 <= i < len(nums). Then the function returns the same result for nums_rev and k as for nums and k.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= len(nums). -/
theorem spec_12 (nums nums_rev : Slice I64) (k : I64) (hpre : Pre nums k)
    (hrev : nums_rev.val = nums.val.reverse) :
    max_subarray_length nums_rev k = max_subarray_length nums k := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums_rev : Slice I64) (k : I64) (hpre : Pre nums k)
    (hrev : nums_rev.val = nums.val.reverse), max_subarray_length nums_rev k = max_subarray_length nums k) := by
  sorry

/-- For any array nums' with len(nums') = len(nums) + 1 and nums'[i] = nums[i] for 0 <= i < len(nums), and any integer x such that nums'[len(nums)] = x, let res be the result for nums and k, and res' be the result for nums' and k. Then res' <= res + 1.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= len(nums). -/
theorem spec_13 (nums nums' : Slice I64) (k x : I64) (hpre : Pre nums k)
    (hlen : nums'.val.length = nums.val.length + 1)
    (hprefix : ∀ (i : ℕ) (h : i < nums.val.length), nums'.val[i] = nums.val[i])
    (hlast : nums'.val[nums.val.length] = x) :
    ∃ res res' : I64, max_subarray_length nums k = ok res ∧
      max_subarray_length nums' k = ok res' ∧ res'.val ≤ res.val + 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums nums' : Slice I64) (k x : I64) (hpre : Pre nums k)
    (hlen : nums'.val.length = nums.val.length + 1)
    (hprefix : ∀ (i : ℕ) (h : i < nums.val.length), nums'.val[i] = nums.val[i])
    (hlast : nums'.val[nums.val.length] = x), ∃ res res' : I64, max_subarray_length nums k = ok res ∧
      max_subarray_length nums' k = ok res' ∧ res'.val ≤ res.val + 1) := by
  sorry

/-- For any indices l, r with 0 <= l < r <= len(nums) and r - l >= k, let nums' be the subarray nums[l..r) (i.e., nums'[i] = nums[l+i] for 0 <= i < r-l). Let res be the result for nums and k, and res' be the result for nums' and k. Then res' <= res.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= len(nums). -/
theorem spec_14 (nums nums' : Slice I64) (k : I64) (l r : ℕ) (hpre : Pre nums k)
    (hlr : l < r) (hr : r ≤ nums.val.length) (hk : k.val ≤ (r : ℤ) - (l : ℤ))
    (hsub : nums'.val = (nums.val.drop l).take (r - l)) :
    ∃ res res' : I64, max_subarray_length nums k = ok res ∧
      max_subarray_length nums' k = ok res' ∧ res'.val ≤ res.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums nums' : Slice I64) (k : I64) (l r : ℕ) (hpre : Pre nums k)
    (hlr : l < r) (hr : r ≤ nums.val.length) (hk : k.val ≤ (r : ℤ) - (l : ℤ))
    (hsub : nums'.val = (nums.val.drop l).take (r - l)), ∃ res res' : I64, max_subarray_length nums k = ok res ∧
      max_subarray_length nums' k = ok res' ∧ res'.val ≤ res.val) := by
  sorry

/-- Let D be the number of distinct values in nums, i.e., the cardinality of the set { nums[i] | 0 <= i < len(nums) }. The function returns a result res and res <= k * D.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= len(nums). -/
theorem spec_15 (nums : Slice I64) (k : I64) (hpre : Pre nums k) :
    ∃ res : I64, max_subarray_length nums k = ok res ∧
      res.val ≤ k.val * ((distinctCount (elems nums) : ℕ) : ℤ) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : Pre nums k), ∃ res : I64, max_subarray_length nums k = ok res ∧
      res.val ≤ k.val * ((distinctCount (elems nums) : ℕ) : ℤ)) := by
  sorry

/-- For any integer x with 1 <= x <= 1000000000, let nums' be the array of length len(nums) + 1 with nums'[i] = nums[i] for 0 <= i < len(nums) and nums'[len(nums)] = x. Let res be the result for nums and k, and res' be the result for nums' and k. Then res <= res'.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= len(nums). -/
theorem spec_16 (nums nums' : Slice I64) (k x : I64) (hpre : Pre nums k)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 1000000000)
    (hlen : nums'.val.length = nums.val.length + 1)
    (hprefix : ∀ (i : ℕ) (h : i < nums.val.length), nums'.val[i] = nums.val[i])
    (hlast : nums'.val[nums.val.length] = x) :
    ∃ res res' : I64, max_subarray_length nums k = ok res ∧
      max_subarray_length nums' k = ok res' ∧ res.val ≤ res'.val := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (nums nums' : Slice I64) (k x : I64) (hpre : Pre nums k)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 1000000000)
    (hlen : nums'.val.length = nums.val.length + 1)
    (hprefix : ∀ (i : ℕ) (h : i < nums.val.length), nums'.val[i] = nums.val[i])
    (hlast : nums'.val[nums.val.length] = x), ∃ res res' : I64, max_subarray_length nums k = ok res ∧
      max_subarray_length nums' k = ok res' ∧ res.val ≤ res'.val) := by
  sorry

/-- The function returns a result res and res = len(nums) if and only if for every index i with 0 <= i < len(nums), the number of indices j with 0 <= j < len(nums) and nums[j] = nums[i] is at most k.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= len(nums). -/
theorem spec_17 (nums : Slice I64) (k : I64) (hpre : Pre nums k) :
    (∃ res : I64, max_subarray_length nums k = ok res ∧ res.val = (nums.val.length : ℤ)) ↔
      (∀ (i : ℕ) (h : i < nums.val.length),
        (countIn (elems nums) 0 nums.val.length (nums.val[i]).val : ℤ) ≤ k.val) := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hpre : Pre nums k), (∃ res : I64, max_subarray_length nums k = ok res ∧ res.val = (nums.val.length : ℤ)) ↔
      (∀ (i : ℕ) (h : i < nums.val.length),
        (countIn (elems nums) 0 nums.val.length (nums.val[i]).val : ℤ) ≤ k.val)) := by
  sorry

end

end AegisSpec.MaxSubarrayLength
