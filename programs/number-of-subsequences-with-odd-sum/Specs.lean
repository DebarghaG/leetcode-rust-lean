import Aegis.SubsequenceCount.Code.Funs

/-!
# Specifications of `Aegis.SubsequenceCount.subsequence_count`

LeetCode problem `number-of-subsequences-with-odd-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SubsequenceCount

def modulus : ℕ := 1000000007

def vals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

def IsOdd (z : ℤ) : Prop := z % 2 ≠ 0

def IsEven (z : ℤ) : Prop := z % 2 = 0

def oddCount (nums : Slice I64) : ℕ := (vals nums).countP (fun z => decide (z % 2 ≠ 0))

def pow2Mod (e : ℕ) : ℕ := 2 ^ e % modulus

def indexedSum (nums : Slice I64) (S : Finset (Fin (vals nums).length)) : ℤ :=
  Finset.sum S (fun i => (vals nums).get i)

def oddSubsetCount (nums : Slice I64) : ℕ :=
  Finset.card
    (Finset.filter (fun S : Finset (Fin (vals nums).length) => (indexedSum nums S) % 2 ≠ 0)
      Finset.univ)

def indexSelection (nums : Slice I64) (S : Finset (Fin (vals nums).length)) : List ℤ :=
  List.filterMap (fun i => if i ∈ S then some ((vals nums).get i) else none)
    (List.finRange (vals nums).length)

def AllEven (nums : Slice I64) : Prop :=
  ∀ i : Fin (vals nums).length, IsEven ((vals nums).get i)

def EntriesInRange (nums : Slice I64) : Prop :=
  ∀ i : Fin (vals nums).length, 1 ≤ (vals nums).get i ∧ (vals nums).get i ≤ 1000000000

def headVal (nums : Slice I64) : ℤ := (vals nums).headD 0

/-- Let M = 1000000007, let n = len(nums), and let O be the number of indices i with 0 <= i < n such that nums[i] is odd. The function returns a result r and r = (if O > 0 then (2^(n-1)) mod M else 0), where mod denotes the least non-negative remainder.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_1 (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums) :
    ∃ r : I64, Aegis.SubsequenceCount.subsequence_count nums = Result.ok r ∧
      r.val = (if 0 < oddCount nums then (pow2Mod (nums.val.length - 1) : ℤ) else 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums), ∃ r : I64, Aegis.SubsequenceCount.subsequence_count nums = Result.ok r ∧
      r.val = (if 0 < oddCount nums then (pow2Mod (nums.val.length - 1) : ℤ) else 0)) := by
  sorry

/-- For every nums satisfying the preconditions, the function returns a result r; it does not fail, panic, or report arithmetic overflow.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums) :
    ∃ r : I64, Aegis.SubsequenceCount.subsequence_count nums = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums), ∃ r : I64, Aegis.SubsequenceCount.subsequence_count nums = Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r < 1000000007.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_3 (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums) (r : I64)
    (hr : Aegis.SubsequenceCount.subsequence_count nums = Result.ok r) :
    0 ≤ r.val ∧ r.val < (modulus : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums) (r : I64)
    (hr : Aegis.SubsequenceCount.subsequence_count nums = Result.ok r), 0 ≤ r.val ∧ r.val < (modulus : ℤ)) := by
  sorry

/-- Let n = len(nums), and let C be the number of subsets S of {0,...,n-1} such that the integer sum of nums[i] over all i in S is odd. Whenever the function returns a result r, r = C mod 1000000007.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_4 (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums) (r : I64)
    (hr : Aegis.SubsequenceCount.subsequence_count nums = Result.ok r) :
    r.val = (oddSubsetCount nums : ℤ) % (modulus : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums) (r : I64)
    (hr : Aegis.SubsequenceCount.subsequence_count nums = Result.ok r), r.val = (oddSubsetCount nums : ℤ) % (modulus : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if every element nums[i] with 0 <= i < len(nums) is even.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_5 (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums) (r : I64)
    (hr : Aegis.SubsequenceCount.subsequence_count nums = Result.ok r) :
    (r.val = 0 ↔ AllEven nums) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums) (r : I64)
    (hr : Aegis.SubsequenceCount.subsequence_count nums = Result.ok r), (r.val = 0 ↔ AllEven nums)) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if nums[0] is odd, and r = 0 if nums[0] is even.
  Preconditions: len(nums) = 1 and 1 <= nums[0] <= 1000000000. -/
theorem spec_6 (nums : Slice I64) (r : I64)
    (hlen : nums.val.length = 1)
    (hval_lo : 1 ≤ headVal nums) (hval_hi : headVal nums ≤ 1000000000)
    (hr : Aegis.SubsequenceCount.subsequence_count nums = Result.ok r) :
    (IsOdd (headVal nums) → r.val = 1) ∧ (IsEven (headVal nums) → r.val = 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (r : I64)
    (hlen : nums.val.length = 1)
    (hval_lo : 1 ≤ headVal nums) (hval_hi : headVal nums ≤ 1000000000)
    (hr : Aegis.SubsequenceCount.subsequence_count nums = Result.ok r), (IsOdd (headVal nums) → r.val = 1) ∧ (IsEven (headVal nums) → r.val = 0)) := by
  sorry

/-- Whenever the function returns r on nums and r' on nums', we have r = r'.
  Preconditions: nums and nums' both satisfy 1 <= length <= 100000 and all entries are in [1,1000000000]; len(nums) = len(nums'); and for every i with 0 <= i < len(nums), nums[i] is odd if and only if nums'[i] is odd. -/
theorem spec_7 (nums nums' : Slice I64) (r r' : I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums)
    (hlen_lo' : 1 ≤ nums'.val.length) (hlen_hi' : nums'.val.length ≤ 100000)
    (hrange' : EntriesInRange nums')
    (hlen : nums.val.length = nums'.val.length)
    (hpar : ∀ i : Fin nums.val.length,
      IsOdd (nums.val.get i).val ↔ IsOdd (nums'.val.get (Fin.cast hlen i)).val)
    (hr : Aegis.SubsequenceCount.subsequence_count nums = Result.ok r)
    (hr' : Aegis.SubsequenceCount.subsequence_count nums' = Result.ok r') :
    r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums nums' : Slice I64) (r r' : I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums)
    (hlen_lo' : 1 ≤ nums'.val.length) (hlen_hi' : nums'.val.length ≤ 100000)
    (hrange' : EntriesInRange nums')
    (hlen : nums.val.length = nums'.val.length)
    (hpar : ∀ i : Fin nums.val.length,
      IsOdd (nums.val.get i).val ↔ IsOdd (nums'.val.get (Fin.cast hlen i)).val)
    (hr : Aegis.SubsequenceCount.subsequence_count nums = Result.ok r)
    (hr' : Aegis.SubsequenceCount.subsequence_count nums' = Result.ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns r on nums and r' on nums', r' = (2 * r) mod 1000000007.
  Preconditions: nums satisfies 1 <= len(nums) <= 100000 and all entries are in [1,1000000000]; nums contains at least one odd element; x is an integer with 1 <= x <= 1000000000; len(nums) + 1 <= 100000. Let nums' be the concatenation of nums and [x]. -/
theorem spec_8 (nums nums' : Slice I64) (x : I64) (r r' : I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums)
    (hodd : 0 < oddCount nums)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 1000000000)
    (hlen_hi' : nums.val.length + 1 ≤ 100000)
    (hcat : nums'.val = nums.val ++ [x])
    (hr : Aegis.SubsequenceCount.subsequence_count nums = Result.ok r)
    (hr' : Aegis.SubsequenceCount.subsequence_count nums' = Result.ok r') :
    r'.val = (2 * r.val) % (modulus : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice I64) (x : I64) (r r' : I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums)
    (hodd : 0 < oddCount nums)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 1000000000)
    (hlen_hi' : nums.val.length + 1 ≤ 100000)
    (hcat : nums'.val = nums.val ++ [x])
    (hr : Aegis.SubsequenceCount.subsequence_count nums = Result.ok r)
    (hr' : Aegis.SubsequenceCount.subsequence_count nums' = Result.ok r'), r'.val = (2 * r.val) % (modulus : ℤ)) := by
  sorry

/-- Whenever the function returns r' on nums', r' = (2^(len(nums))) mod 1000000007.
  Preconditions: nums satisfies 1 <= len(nums) <= 100000 and all entries are in [1,1000000000]; every nums[i] is even; x is odd with 1 <= x <= 1000000000; len(nums) + 1 <= 100000. Let nums' be the concatenation of nums and [x]. -/
theorem spec_9 (nums nums' : Slice I64) (x : I64) (r' : I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums)
    (heven : AllEven nums)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 1000000000) (hx_odd : IsOdd x.val)
    (hlen_hi' : nums.val.length + 1 ≤ 100000)
    (hcat : nums'.val = nums.val ++ [x])
    (hr' : Aegis.SubsequenceCount.subsequence_count nums' = Result.ok r') :
    r'.val = (pow2Mod nums.val.length : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice I64) (x : I64) (r' : I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums)
    (heven : AllEven nums)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 1000000000) (hx_odd : IsOdd x.val)
    (hlen_hi' : nums.val.length + 1 ≤ 100000)
    (hcat : nums'.val = nums.val ++ [x])
    (hr' : Aegis.SubsequenceCount.subsequence_count nums' = Result.ok r'), r'.val = (pow2Mod nums.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a nonzero result r, there exists an index j with 0 <= j < len(nums) such that nums[j] is odd; moreover, the one-element index subset {j} is then a subsequence whose sum is odd.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_10 (nums : Slice I64) (r : I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums)
    (hr : Aegis.SubsequenceCount.subsequence_count nums = Result.ok r)
    (hr_ne : r.val ≠ 0) :
    ∃ j : Fin (vals nums).length,
      IsOdd ((vals nums).get j) ∧
      (indexSelection nums {j}).Sublist (vals nums) ∧
      IsOdd ((indexSelection nums {j}).sum) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (r : I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums)
    (hr : Aegis.SubsequenceCount.subsequence_count nums = Result.ok r)
    (hr_ne : r.val ≠ 0), ∃ j : Fin (vals nums).length,
      IsOdd ((vals nums).get j) ∧
      (indexSelection nums {j}).Sublist (vals nums) ∧
      IsOdd ((indexSelection nums {j}).sum)) := by
  sorry

end AegisSpec.SubsequenceCount
