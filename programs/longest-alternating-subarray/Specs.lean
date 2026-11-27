import Aegis.AlternatingSubarray.Code.Funs

/-!
# Specifications of `Aegis.AlternatingSubarray.alternating_subarray`

LeetCode problem `longest-alternating-subarray`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.AlternatingSubarray

def len (nums : Slice I64) : ℤ := (nums.val.length : ℤ)

def elem (nums : Slice I64) (i : ℤ) : ℤ := (nums.val.getD i.toNat default).val

def IsAltWindow (nums : Slice I64) (l m : ℤ) : Prop :=
  0 ≤ l ∧ l + m ≤ len nums ∧
    ∀ j : ℤ, 0 ≤ j → j < m → elem nums (l + j) = elem nums l + (j % 2)

def GoodLen (nums : Slice I64) (m : ℤ) : Prop :=
  ∃ l : ℤ, IsAltWindow nums l m ∧ 1 < m

def StepAt (nums : Slice I64) (i : ℤ) : Prop := elem nums (i + 1) = elem nums i + 1

/-- Whenever the function returns a result r, the following holds. Define A to be the set of all integers m for which there exists an integer l with 0 <= l, m > 1, l + m <= len(nums), and, for every j with 0 <= j < m, nums[l+j] = nums[l] + (j mod 2). If A is empty, then r = -1. If A is not empty, then r = max(A).
  Preconditions: len(nums) >= 2 and len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_1 (nums : Slice I64)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∀ r, Aegis.AlternatingSubarray.alternating_subarray nums = ok r →
      (((¬ ∃ m : ℤ, GoodLen nums m) → r.val = -1) ∧
        ((∃ m : ℤ, GoodLen nums m) →
          GoodLen nums r.val ∧ ∀ m : ℤ, GoodLen nums m → m ≤ r.val)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000), ∀ r, Aegis.AlternatingSubarray.alternating_subarray nums = ok r →
      (((¬ ∃ m : ℤ, GoodLen nums m) → r.val = -1) ∧
        ((∃ m : ℤ, GoodLen nums m) →
          GoodLen nums r.val ∧ ∀ m : ℤ, GoodLen nums m → m ≤ r.val))) := by
  sorry

/-- The function returns a result r; it does not fail (no overflow, out-of-bounds access, or panic).
  Preconditions: len(nums) >= 2 and len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_2 (nums : Slice I64)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∃ r, Aegis.AlternatingSubarray.alternating_subarray nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000), ∃ r, Aegis.AlternatingSubarray.alternating_subarray nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1, or 2 <= r <= len(nums).
  Preconditions: len(nums) >= 2 and len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_3 (nums : Slice I64)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∀ r, Aegis.AlternatingSubarray.alternating_subarray nums = ok r →
      r.val = -1 ∨ (2 ≤ r.val ∧ r.val ≤ len nums) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000), ∀ r, Aegis.AlternatingSubarray.alternating_subarray nums = ok r →
      r.val = -1 ∨ (2 ≤ r.val ∧ r.val ≤ len nums)) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if there is no index i with 0 <= i < len(nums) - 1 and nums[i+1] = nums[i] + 1.
  Preconditions: len(nums) >= 2 and len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_4 (nums : Slice I64)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∀ r, Aegis.AlternatingSubarray.alternating_subarray nums = ok r →
      (r.val = -1 ↔
        ¬ ∃ i : ℤ, 0 ≤ i ∧ i < len nums - 1 ∧ StepAt nums i) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000), ∀ r, Aegis.AlternatingSubarray.alternating_subarray nums = ok r →
      (r.val = -1 ↔
        ¬ ∃ i : ℤ, 0 ≤ i ∧ i < len nums - 1 ∧ StepAt nums i)) := by
  sorry

/-- Whenever the function returns a result r, r = len(nums) if and only if for every j with 0 <= j < len(nums), nums[j] = nums[0] + (j mod 2).
  Preconditions: len(nums) >= 2 and len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_5 (nums : Slice I64)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∀ r, Aegis.AlternatingSubarray.alternating_subarray nums = ok r →
      (r.val = len nums ↔
        ∀ j : ℤ, 0 ≤ j → j < len nums → elem nums j = elem nums 0 + (j % 2)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000), ∀ r, Aegis.AlternatingSubarray.alternating_subarray nums = ok r →
      (r.val = len nums ↔
        ∀ j : ℤ, 0 ≤ j → j < len nums → elem nums j = elem nums 0 + (j % 2))) := by
  sorry

/-- Whenever the function returns a result r with r >= 2, there exists an integer l such that 0 <= l, l + r <= len(nums), and for every j with 0 <= j < r, nums[l+j] = nums[l] + (j mod 2).
  Preconditions: len(nums) >= 2 and len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_6 (nums : Slice I64)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∀ r, Aegis.AlternatingSubarray.alternating_subarray nums = ok r → 2 ≤ r.val →
      ∃ l : ℤ, 0 ≤ l ∧ l + r.val ≤ len nums ∧
        ∀ j : ℤ, 0 ≤ j → j < r.val →
          elem nums (l + j) = elem nums l + (j % 2) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000), ∀ r, Aegis.AlternatingSubarray.alternating_subarray nums = ok r → 2 ≤ r.val →
      ∃ l : ℤ, 0 ≤ l ∧ l + r.val ≤ len nums ∧
        ∀ j : ℤ, 0 ≤ j → j < r.val →
          elem nums (l + j) = elem nums l + (j % 2)) := by
  sorry

/-- Whenever the function returns a result r with r >= 2, for every integer l and every integer m such that 0 <= l, m > 1, l + m <= len(nums), and for every j with 0 <= j < m, nums[l+j] = nums[l] + (j mod 2), we have m <= r.
  Preconditions: len(nums) >= 2 and len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_7 (nums : Slice I64)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∀ r, Aegis.AlternatingSubarray.alternating_subarray nums = ok r → 2 ≤ r.val →
      ∀ l m : ℤ, 0 ≤ l → 1 < m → l + m ≤ len nums →
        (∀ j : ℤ, 0 ≤ j → j < m → elem nums (l + j) = elem nums l + (j % 2)) →
        m ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000), ∀ r, Aegis.AlternatingSubarray.alternating_subarray nums = ok r → 2 ≤ r.val →
      ∀ l m : ℤ, 0 ≤ l → 1 < m → l + m ≤ len nums →
        (∀ j : ℤ, 0 ≤ j → j < m → elem nums (l + j) = elem nums l + (j % 2)) →
        m ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r with r >= 2, for every integer m with 2 <= m <= r, there exists an integer l such that 0 <= l, l + m <= len(nums), and for every j with 0 <= j < m, nums[l+j] = nums[l] + (j mod 2).
  Preconditions: len(nums) >= 2 and len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_8 (nums : Slice I64)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∀ r, Aegis.AlternatingSubarray.alternating_subarray nums = ok r → 2 ≤ r.val →
      ∀ m : ℤ, 2 ≤ m → m ≤ r.val →
        ∃ l : ℤ, 0 ≤ l ∧ l + m ≤ len nums ∧
          ∀ j : ℤ, 0 ≤ j → j < m →
            elem nums (l + j) = elem nums l + (j % 2) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000), ∀ r, Aegis.AlternatingSubarray.alternating_subarray nums = ok r → 2 ≤ r.val →
      ∀ m : ℤ, 2 ≤ m → m ≤ r.val →
        ∃ l : ℤ, 0 ≤ l ∧ l + m ≤ len nums ∧
          ∀ j : ℤ, 0 ≤ j → j < m →
            elem nums (l + j) = elem nums l + (j % 2)) := by
  sorry

/-- Whenever the function returns a result r, r = 2 if and only if (there exists an index i with 0 <= i < len(nums)-1 and nums[i+1] = nums[i] + 1) and (there does not exist an index i with 0 <= i < len(nums)-2 such that nums[i+1] = nums[i] + 1 and nums[i+2] = nums[i]).
  Preconditions: len(nums) >= 2 and len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_9 (nums : Slice I64)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000) :
    ∀ r, Aegis.AlternatingSubarray.alternating_subarray nums = ok r →
      (r.val = 2 ↔
        (∃ i : ℤ, 0 ≤ i ∧ i < len nums - 1 ∧ StepAt nums i) ∧
          ¬ ∃ i : ℤ, 0 ≤ i ∧ i < len nums - 2 ∧
            StepAt nums i ∧ elem nums (i + 2) = elem nums i) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000), ∀ r, Aegis.AlternatingSubarray.alternating_subarray nums = ok r →
      (r.val = 2 ↔
        (∃ i : ℤ, 0 ≤ i ∧ i < len nums - 1 ∧ StepAt nums i) ∧
          ¬ ∃ i : ℤ, 0 ≤ i ∧ i < len nums - 2 ∧
            StepAt nums i ∧ elem nums (i + 2) = elem nums i)) := by
  sorry

/-- Whenever the function returns a result r on input nums and a result r' on input nums', we have r = r'.
  Preconditions: len(nums) >= 2 and len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. Let c be an integer and nums' be a slice of 64-bit integers with len(nums') = len(nums), and for every i with 0 <= i < len(nums), nums'[i] = nums[i] + c and 1 <= nums'[i] <= 10000. -/
theorem spec_10 (nums nums' : Slice I64) (c : ℤ)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000)
    (hlen' : len nums' = len nums)
    (hshift : ∀ i : ℤ, 0 ≤ i → i < len nums → elem nums' i = elem nums i + c)
    (hbound' : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums' i ∧ elem nums' i ≤ 10000) :
    ∀ r r', Aegis.AlternatingSubarray.alternating_subarray nums = ok r →
      Aegis.AlternatingSubarray.alternating_subarray nums' = ok r' → r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice I64) (c : ℤ)
    (hlen2 : 2 ≤ len nums) (hlen100 : len nums ≤ 100)
    (hbound : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums i ∧ elem nums i ≤ 10000)
    (hlen' : len nums' = len nums)
    (hshift : ∀ i : ℤ, 0 ≤ i → i < len nums → elem nums' i = elem nums i + c)
    (hbound' : ∀ i : ℤ, 0 ≤ i → i < len nums →
      1 ≤ elem nums' i ∧ elem nums' i ≤ 10000), ∀ r r', Aegis.AlternatingSubarray.alternating_subarray nums = ok r →
      Aegis.AlternatingSubarray.alternating_subarray nums' = ok r' → r.val = r'.val) := by
  sorry

end AegisSpec.AlternatingSubarray
