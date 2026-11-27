import Aegis.CountSubarrays.Code.Funs

/-!
# Specifications of `Aegis.CountSubarrays.count_subarrays`

LeetCode problem `number-of-subarrays-with-and-value-of-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountSubarrays

open Aegis.CountSubarrays

def sliceValues (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def entry (xs : List ℤ) (i : ℕ) : ℤ := (xs[i]?).getD 0

def elemAt (nums : Slice Std.I64) (i : ℕ) : ℤ := entry (sliceValues nums) i

def bitAnd (a b : ℤ) : ℤ := ((a.toNat &&& b.toNat : ℕ) : ℤ)

def rangeAnd : List ℤ → ℤ
  | [] => 0
  | x :: rest => rest.foldl bitAnd x

def subarrayAnd (xs : List ℤ) (l r : ℕ) : ℤ := rangeAnd ((xs.drop l).take (r + 1 - l))

def countSubarrays (xs : List ℤ) (k : ℤ) : ℕ :=
  (((Finset.range xs.length).product (Finset.range xs.length)).filter
      (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ subarrayAnd xs p.1 p.2 = k)).card

def countValue (xs : List ℤ) (k : ℤ) : ℕ :=
  ((Finset.range xs.length).filter (fun i => entry xs i = k)).card

def adjacentCount (xs : List ℤ) (k : ℤ) : ℕ :=
  ((Finset.range (xs.length - 1)).filter
      (fun i => bitAnd (entry xs i) (entry xs (i + 1)) = k)).card

def replaceAt (xs : List ℤ) (i : ℕ) (x : ℤ) : List ℤ := xs.set i x

/-- The function returns a result res and res equals the number of pairs (l, r) of integer indices such that 0 <= l <= r < len(nums) and the bitwise AND of all entries nums[l], nums[l+1], ..., nums[r] equals k. A subarray is a non-empty contiguous segment, identified by its two endpoints l and r; the AND of a one-element segment is the element itself.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000, and 0 <= k <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∃ res : Std.I64, count_subarrays nums k = ok res ∧
      res.val = (countSubarrays (sliceValues nums) k.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000), ∃ res : Std.I64, count_subarrays nums k = ok res ∧
      res.val = (countSubarrays (sliceValues nums) k.val : ℤ)) := by
  sorry

/-- The function returns a result res and does not fail: on every input satisfying the preconditions there is no arithmetic overflow, no out-of-bounds indexing, and no panic.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000, and 0 <= k <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∃ res : Std.I64, count_subarrays nums k = ok res := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000), ∃ res : Std.I64, count_subarrays nums k = ok res) := by
  sorry

/-- Whenever the function returns a result res, 0 <= res <= len(nums) * (len(nums) + 1) / 2. Equivalently, res is between zero and the total number of non-empty contiguous subarrays of nums, inclusive.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000, and 0 <= k <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ res : Std.I64, count_subarrays nums k = ok res →
      0 ≤ res.val ∧
        res.val ≤ (((nums.length * (nums.length + 1) / 2) : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000), ∀ res : Std.I64, count_subarrays nums k = ok res →
      0 ≤ res.val ∧
        res.val ≤ (((nums.length * (nums.length + 1) / 2) : ℕ) : ℤ)) := by
  sorry

/-- The function returns a result res and res = 1 if nums[0] = k, and res = 0 otherwise.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000, 0 <= k <= 1000000000, and len(nums) = 1. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (hlen : nums.length = 1) :
    ∃ res : Std.I64, count_subarrays nums k = ok res ∧
      res.val = (if elemAt nums 0 = k.val then 1 else 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (hlen : nums.length = 1), ∃ res : Std.I64, count_subarrays nums k = ok res ∧
      res.val = (if elemAt nums 0 = k.val then 1 else 0)) := by
  sorry

/-- The function returns a result res and res = (if nums[0] = k then 1 else 0) + (if nums[1] = k then 1 else 0) + (if (nums[0] bitwise AND nums[1]) = k then 1 else 0).
  Preconditions: len(nums) >= 1, len(nums) <= 100000, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000, 0 <= k <= 1000000000, and len(nums) = 2. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (hlen : nums.length = 2) :
    ∃ res : Std.I64, count_subarrays nums k = ok res ∧
      res.val = (if elemAt nums 0 = k.val then 1 else 0)
        + (if elemAt nums 1 = k.val then 1 else 0)
        + (if bitAnd (elemAt nums 0) (elemAt nums 1) = k.val then 1 else 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (hlen : nums.length = 2), ∃ res : Std.I64, count_subarrays nums k = ok res ∧
      res.val = (if elemAt nums 0 = k.val then 1 else 0)
        + (if elemAt nums 1 = k.val then 1 else 0)
        + (if bitAnd (elemAt nums 0) (elemAt nums 1) = k.val then 1 else 0)) := by
  sorry

/-- The function returns a result res and res = len(nums) * (len(nums) + 1) / 2.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000, 0 <= k <= 1000000000, and for every i with 0 <= i < len(nums), nums[i] = k. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (hconst : ∀ (j : ℕ), (hj : j < nums.length) → (nums.val[j]).val = k.val) :
    ∃ res : Std.I64, count_subarrays nums k = ok res ∧
      res.val = (((nums.length * (nums.length + 1) / 2) : ℕ) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (hconst : ∀ (j : ℕ), (hj : j < nums.length) → (nums.val[j]).val = k.val), ∃ res : Std.I64, count_subarrays nums k = ok res ∧
      res.val = (((nums.length * (nums.length + 1) / 2) : ℕ) : ℤ)) := by
  sorry

/-- The function returns a result res and res = 0.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000, 0 <= k <= 1000000000, and there exists an integer x such that 0 <= x <= 1000000000, x != k, and for every i with 0 <= i < len(nums), nums[i] = x. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (hother : ∃ x : ℤ, 0 ≤ x ∧ x ≤ 1000000000 ∧ x ≠ k.val ∧
      ∀ (j : ℕ), (hj : j < nums.length) → (nums.val[j]).val = x) :
    ∃ res : Std.I64, count_subarrays nums k = ok res ∧ res.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (hother : ∃ x : ℤ, 0 ≤ x ∧ x ≤ 1000000000 ∧ x ≠ k.val ∧
      ∀ (j : ℕ), (hj : j < nums.length) → (nums.val[j]).val = x), ∃ res : Std.I64, count_subarrays nums k = ok res ∧ res.val = 0) := by
  sorry

/-- Whenever the function returns a result res, res >= 1.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000, 0 <= k <= 1000000000, and there exist integer indices l and r with 0 <= l <= r < len(nums) such that the bitwise AND of nums[l], ..., nums[r] equals k. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (hwit : ∃ (l r : ℕ), l ≤ r ∧ r < nums.length ∧
      subarrayAnd (sliceValues nums) l r = k.val) :
    ∀ res : Std.I64, count_subarrays nums k = ok res → 1 ≤ res.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (hwit : ∃ (l r : ℕ), l ≤ r ∧ r < nums.length ∧
      subarrayAnd (sliceValues nums) l r = k.val), ∀ res : Std.I64, count_subarrays nums k = ok res → 1 ≤ res.val) := by
  sorry

/-- Whenever the function returns a result res, res is at least the number of indices i with 0 <= i < len(nums) and nums[i] = k.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000, and 0 <= k <= 1000000000. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ res : Std.I64, count_subarrays nums k = ok res →
      (countValue (sliceValues nums) k.val : ℤ) ≤ res.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000), ∀ res : Std.I64, count_subarrays nums k = ok res →
      (countValue (sliceValues nums) k.val : ℤ) ≤ res.val) := by
  sorry

/-- Whenever the function returns a result res, res is at least the number of indices i with 0 <= i < len(nums) - 1 and (nums[i] bitwise AND nums[i+1]) = k.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000, and 0 <= k <= 1000000000. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∀ res : Std.I64, count_subarrays nums k = ok res →
      (adjacentCount (sliceValues nums) k.val : ℤ) ≤ res.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000), ∀ res : Std.I64, count_subarrays nums k = ok res →
      (adjacentCount (sliceValues nums) k.val : ℤ) ≤ res.val) := by
  sorry

/-- Let nums' be the array with nums'[j] = nums[j] for every j with 0 <= j < len(nums) and j != i, and nums'[i] = x. Whenever the function returns a result res for nums, res equals the number of pairs (l, r) with 0 <= l <= r < len(nums) such that the bitwise AND of nums'[l], ..., nums'[r] equals k; equivalently, res equals the count that the same problem statement would give for nums'.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000, 0 <= k <= 1000000000, k > 0, 0 <= i < len(nums), (nums[i] bitwise AND k) != k, 0 <= x <= 1000000000, and (x bitwise AND k) != k. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64) (i : ℕ) (x : ℤ)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (hkpos : 0 < k.val)
    (hi : i < nums.length)
    (hni : bitAnd (nums.val[i]).val k.val ≠ k.val)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1000000000)
    (hxn : bitAnd x k.val ≠ k.val) :
    ∀ res : Std.I64, count_subarrays nums k = ok res →
      res.val =
        (countSubarrays (replaceAt (sliceValues nums) i x) k.val : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (i : ℕ) (x : ℤ)
    (hnil : 1 ≤ nums.length) (hcap : nums.length ≤ 100000)
    (helem : ∀ (j : ℕ), (hj : j < nums.length) →
      0 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 1000000000)
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000000000)
    (hkpos : 0 < k.val)
    (hi : i < nums.length)
    (hni : bitAnd (nums.val[i]).val k.val ≠ k.val)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1000000000)
    (hxn : bitAnd x k.val ≠ k.val), ∀ res : Std.I64, count_subarrays nums k = ok res →
      res.val =
        (countSubarrays (replaceAt (sliceValues nums) i x) k.val : ℤ)) := by
  sorry

end AegisSpec.CountSubarrays
