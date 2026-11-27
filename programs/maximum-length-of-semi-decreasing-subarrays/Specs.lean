import Aegis.MaxSubarrayLength.Code.Funs

/-!
# Specifications of `Aegis.MaxSubarrayLength.max_subarray_length`

LeetCode problem `maximum-length-of-semi-decreasing-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxSubarrayLength

namespace AegisSpec.MaxSubarrayLength

abbrev SliceI64 := Slice Std.I64

def length (nums : SliceI64) : Nat := nums.val.length

def values (nums : SliceI64) : List Int := nums.val.map (fun x => x.val)

def nth (nums : SliceI64) (i : Nat) : Int := (values nums).getD i 0

def span (i j : Nat) : Int := (j : Int) - (i : Int) + 1

def IsInversion (nums : SliceI64) (i j : Nat) : Prop :=
  i < j ∧ j < length nums ∧ nth nums j < nth nums i

def HasInversion (nums : SliceI64) : Prop := ∃ i j : Nat, IsInversion nums i j

def candidates (nums : SliceI64) : Set Int :=
  {0} ∪ {L : Int | ∃ i j : Nat, IsInversion nums i j ∧ span i j = L}

def IsMaximum (nums : SliceI64) (r : Int) : Prop :=
  r ∈ candidates nums ∧ ∀ L ∈ candidates nums, L ≤ r

/-- The function returns a result r and r = max({0} union {j - i + 1 | 0 <= i < j < len(nums) and nums[i] > nums[j]}). Equivalently: r = 0 if there are no indices i, j with 0 <= i < j < len(nums) and nums[i] > nums[j]; otherwise r is the largest integer L for which there exist i, j with 0 <= i < j < len(nums), nums[i] > nums[j], and j - i + 1 = L.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_1 (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000) :
    ∃ r, max_subarray_length nums = ok r ∧ IsMaximum nums r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000), ∃ r, max_subarray_length nums = ok r ∧ IsMaximum nums r.val) := by
  sorry

/-- The function returns a result r for every nums satisfying the preconditions; it does not fail, panic, or overflow.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000) :
    ∃ r, max_subarray_length nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000), ∃ r, max_subarray_length nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(nums).
  Preconditions: len(nums) >= 1 and len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_3 (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000) :
    ∀ r, max_subarray_length nums = ok r → 0 ≤ r.val ∧ r.val ≤ (length nums : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000), ∀ r, max_subarray_length nums = ok r → 0 ≤ r.val ∧ r.val ≤ (length nums : Int)) := by
  sorry

/-- Whenever the function returns a result r, r != 1; that is, either r = 0 or 2 <= r <= len(nums).
  Preconditions: len(nums) >= 1 and len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_4 (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000) :
    ∀ r, max_subarray_length nums = ok r → r.val ≠ 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000), ∀ r, max_subarray_length nums = ok r → r.val ≠ 1) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there do not exist indices i, j with 0 <= i < j < len(nums) and nums[i] > nums[j].
  Preconditions: len(nums) >= 1 and len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_5 (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000) :
    ∀ r, max_subarray_length nums = ok r → (r.val = 0 ↔ ¬ HasInversion nums) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000), ∀ r, max_subarray_length nums = ok r → (r.val = 0 ↔ ¬ HasInversion nums)) := by
  sorry

/-- Whenever the function returns a result r with r > 0, there exist indices i, j such that 0 <= i < j < len(nums), nums[i] > nums[j], and j - i + 1 = r.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_6 (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000) :
    ∀ r, max_subarray_length nums = ok r → 0 < r.val →
      ∃ i j, IsInversion nums i j ∧ span i j = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000), ∀ r, max_subarray_length nums = ok r → 0 < r.val →
      ∃ i j, IsInversion nums i j ∧ span i j = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every i, j with 0 <= i < j < len(nums) and nums[i] > nums[j], we have j - i + 1 <= r.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_7 (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000) :
    ∀ r, max_subarray_length nums = ok r →
      ∀ i j, IsInversion nums i j → span i j ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000), ∀ r, max_subarray_length nums = ok r →
      ∀ i j, IsInversion nums i j → span i j ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = len(nums) if and only if nums[0] > nums[len(nums)-1].
  Preconditions: len(nums) >= 1 and len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_8 (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000) :
    ∀ r, max_subarray_length nums = ok r →
      (r.val = (length nums : Int) ↔ nth nums 0 > nth nums (length nums - 1)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000), ∀ r, max_subarray_length nums = ok r →
      (r.val = (length nums : Int) ↔ nth nums 0 > nth nums (length nums - 1))) := by
  sorry

/-- The function returns a result r and r = 0.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000, and for every i with 0 <= i + 1 < len(nums), nums[i] <= nums[i+1]. -/
theorem spec_9 (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
    (hsorted : ∀ i, i + 1 < length nums → nth nums i ≤ nth nums (i + 1)) :
    ∃ r, max_subarray_length nums = ok r ∧ r.val = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
    (hsorted : ∀ i, i + 1 < length nums → nth nums i ≤ nth nums (i + 1)), ∃ r, max_subarray_length nums = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r and r = 2 if nums[0] > nums[1], and r = 0 otherwise.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000, and len(nums) = 2. -/
theorem spec_10 (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
    (hlen : length nums = 2) :
    ∃ r, max_subarray_length nums = ok r ∧
      (if nth nums 0 > nth nums 1 then r.val = 2 else r.val = 0) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
    (hlen : length nums = 2), ∃ r, max_subarray_length nums = ok r ∧
      (if nth nums 0 > nth nums 1 then r.val = 2 else r.val = 0)) := by
  sorry

/-- For every integer c, if b is a slice with len(b) = len(nums) and b[i] = nums[i] + c for every i with 0 <= i < len(nums), and if -1000000000 <= b[i] <= 1000000000 for every i, then the function returns a result r on nums and a result r_b on b, and r = r_b.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_11 (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
    (c : Int) (b : SliceI64)
    (hlen : length b = length nums)
    (hshift : ∀ i, i < length nums → nth b i = nth nums i + c)
    (hvalb : ∀ i, i < length b → -1000000000 ≤ nth b i ∧ nth b i ≤ 1000000000) :
    ∃ r rb, max_subarray_length nums = ok r ∧ max_subarray_length b = ok rb ∧ r.val = rb.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
    (c : Int) (b : SliceI64)
    (hlen : length b = length nums)
    (hshift : ∀ i, i < length nums → nth b i = nth nums i + c)
    (hvalb : ∀ i, i < length b → -1000000000 ≤ nth b i ∧ nth b i ≤ 1000000000), ∃ r rb, max_subarray_length nums = ok r ∧ max_subarray_length b = ok rb ∧ r.val = rb.val) := by
  sorry

/-- For every l, m with 0 <= l <= m < len(nums), let b be the slice of length m - l + 1 defined by b[t] = nums[l + t] for every t with 0 <= t < m - l + 1. If r is the result on nums and r_b is the result on b, then r_b <= r.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_12 (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
    (l m : Nat) (hlm : l ≤ m) (hm : m < length nums) (b : SliceI64)
    (hlen : length b = m - l + 1)
    (hsub : ∀ t, t < m - l + 1 → nth b t = nth nums (l + t)) :
    ∃ r rb, max_subarray_length nums = ok r ∧ max_subarray_length b = ok rb ∧ rb.val ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : SliceI64)
    (hn1 : 1 ≤ length nums) (hn2 : length nums ≤ 100000)
    (hval : ∀ i, i < length nums → -1000000000 ≤ nth nums i ∧ nth nums i ≤ 1000000000)
    (l m : Nat) (hlm : l ≤ m) (hm : m < length nums) (b : SliceI64)
    (hlen : length b = m - l + 1)
    (hsub : ∀ t, t < m - l + 1 → nth b t = nth nums (l + t)), ∃ r rb, max_subarray_length nums = ok r ∧ max_subarray_length b = ok rb ∧ rb.val ≤ r.val) := by
  sorry

end AegisSpec.MaxSubarrayLength
