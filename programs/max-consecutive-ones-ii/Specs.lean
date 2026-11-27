import Aegis.FindMaxConsecutiveOnes.Code.Funs

/-!
# Specifications of `Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones`

LeetCode problem `max-consecutive-ones-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindMaxConsecutiveOnes

def IsWindow (nums : List Std.I64) (l t : ℕ) : Prop :=
  l ≤ t ∧ t ≤ nums.length

def zeroCount (nums : List Std.I64) (l t : ℕ) : ℕ :=
  ((nums.drop l).take (t - l)).countP (fun x => x.val == 0)

def oneCount (nums : List Std.I64) (l t : ℕ) : ℕ :=
  ((nums.drop l).take (t - l)).countP (fun x => x.val == 1)

def AtMostOneZero (nums : List Std.I64) (l t : ℕ) : Prop :=
  zeroCount nums l t ≤ 1

def AllOne (nums : List Std.I64) (l t : ℕ) : Prop :=
  ((nums.drop l).take (t - l)).all (fun x => x.val == 1) = true

def ZeroAt (nums : List Std.I64) (z : ℕ) : Prop :=
  nums[z]?.map (fun x => x.val) = some 0

def OneAt (nums : List Std.I64) (z : ℕ) : Prop :=
  nums[z]?.map (fun x => x.val) = some 1

def WindowValue (nums : List Std.I64) (m : ℤ) : Prop :=
  ∃ l t : ℕ, IsWindow nums l t ∧ ((t - l : ℕ) : ℤ) = m ∧ AtMostOneZero nums l t

def runLeft (nums : List Std.I64) (z : ℕ) : ℕ :=
  ((nums.take z).reverse.takeWhile (fun x => x.val == 1)).length

def runRight (nums : List Std.I64) (z : ℕ) : ℕ :=
  ((nums.drop (z + 1)).takeWhile (fun x => x.val == 1)).length

/-- Whenever the function returns a result out, out is the maximum length of a contiguous interval nums[l..t) with 0 <= l <= t <= len(nums) that contains at most one index i with l <= i < t and nums[i] = 0. Equivalently, out is the largest m for which there exist l and t with 0 <= l <= t <= len(nums), t - l = m, and at most one zero in nums[l..t).
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1. -/
theorem spec_1 (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out) :
    IsGreatest {m : ℤ | WindowValue nums.val m} out.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out), IsGreatest {m : ℤ | WindowValue nums.val m} out.val) := by
  sorry

/-- Under these preconditions, the function returns a result out; it does not fail by arithmetic overflow, out-of-bounds access, or panic.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1. -/
theorem spec_2 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1) :
    ∃ out : Std.I64, Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1), ∃ out : Std.I64, Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out) := by
  sorry

/-- Whenever the function returns a result out, 1 <= out <= len(nums).
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1. -/
theorem spec_3 (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out) :
    1 ≤ out.val ∧ out.val ≤ (nums.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out), 1 ≤ out.val ∧ out.val ≤ (nums.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result out, there exist indices l and t with 0 <= l <= t <= len(nums), t - l = out, and at most one index i with l <= i < t and nums[i] = 0.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1. -/
theorem spec_4 (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out) :
    ∃ l t : ℕ, IsWindow nums.val l t ∧ ((t - l : ℕ) : ℤ) = out.val ∧
      AtMostOneZero nums.val l t := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out), ∃ l t : ℕ, IsWindow nums.val l t ∧ ((t - l : ℕ) : ℤ) = out.val ∧
      AtMostOneZero nums.val l t) := by
  sorry

/-- Whenever the function returns a result out, for every l and t with 0 <= l <= t <= len(nums), if the interval nums[l..t) contains at most one zero, then t - l <= out.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1. -/
theorem spec_5 (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out) :
    ∀ l t : ℕ, IsWindow nums.val l t → AtMostOneZero nums.val l t →
      ((t - l : ℕ) : ℤ) ≤ out.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out), ∀ l t : ℕ, IsWindow nums.val l t → AtMostOneZero nums.val l t →
      ((t - l : ℕ) : ℤ) ≤ out.val) := by
  sorry

/-- Whenever the function returns a result out, out = len(nums).
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1; additionally, every nums[i] = 1 for 0 <= i < len(nums). -/
theorem spec_6 (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_all_one : AllOne nums.val 0 nums.val.length)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out) :
    out.val = (nums.val.length : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_all_one : AllOne nums.val 0 nums.val.length)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out), out.val = (nums.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result out, out = 1.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1; additionally, every nums[i] = 0 for 0 <= i < len(nums). -/
theorem spec_7 (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_all_zero : zeroCount nums.val 0 nums.val.length = nums.val.length)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out) :
    out.val = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_all_zero : zeroCount nums.val 0 nums.val.length = nums.val.length)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out), out.val = 1) := by
  sorry

/-- Whenever the function returns a result out, for every l and t with 0 <= l <= t <= len(nums), if nums[i] = 1 for every i with l <= i < t, then t - l <= out.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1. -/
theorem spec_8 (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out) :
    ∀ l t : ℕ, IsWindow nums.val l t → AllOne nums.val l t → ((t - l : ℕ) : ℤ) ≤ out.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out), ∀ l t : ℕ, IsWindow nums.val l t → AllOne nums.val l t → ((t - l : ℕ) : ℤ) ≤ out.val) := by
  sorry

/-- Whenever the function returns a result out, out >= 2.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1; additionally, len(nums) >= 2 and there exists an index i with 0 <= i < len(nums) and nums[i] = 1. -/
theorem spec_9 (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_len_ge_two : 2 ≤ nums.val.length)
    (h_exists_one : ∃ i : ℕ, i < nums.val.length ∧ OneAt nums.val i)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out) :
    2 ≤ out.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_len_ge_two : 2 ≤ nums.val.length)
    (h_exists_one : ∃ i : ℕ, i < nums.val.length ∧ OneAt nums.val i)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out), 2 ≤ out.val) := by
  sorry

/-- Whenever the function returns a result out, out = 2.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1; additionally, len(nums) >= 2 and there is exactly one index i with 0 <= i < len(nums) and nums[i] = 1. -/
theorem spec_10 (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_len_ge_two : 2 ≤ nums.val.length)
    (h_exists_one : ∃ i : ℕ, i < nums.val.length ∧ OneAt nums.val i)
    (h_unique_one : ∃ i : ℕ, i < nums.val.length ∧ OneAt nums.val i ∧
      ∀ j : ℕ, j < nums.val.length → OneAt nums.val j → j = i)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out) :
    out.val = 2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_len_ge_two : 2 ≤ nums.val.length)
    (h_exists_one : ∃ i : ℕ, i < nums.val.length ∧ OneAt nums.val i)
    (h_unique_one : ∃ i : ℕ, i < nums.val.length ∧ OneAt nums.val i ∧
      ∀ j : ℕ, j < nums.val.length → OneAt nums.val j → j = i)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out), out.val = 2) := by
  sorry

/-- Whenever the function returns a result out, the following holds. For each zero index z with 0 <= z < len(nums) and nums[z] = 0, let L(z) be the largest a with 0 <= a <= z such that nums[i] = 1 for every i with z-a <= i < z, and let R(z) be the largest b with 0 <= b < len(nums)-z such that nums[i] = 1 for every i with z < i <= z+b. Then out = max { L(z) + 1 + R(z) | 0 <= z < len(nums) and nums[z] = 0 }.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1; additionally, there are at least two indices z with nums[z] = 0 and at least one index j with nums[j] = 1. -/
theorem spec_11 (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_two_zeros : 2 ≤ zeroCount nums.val 0 nums.val.length)
    (h_exists_one : ∃ j : ℕ, j < nums.val.length ∧ OneAt nums.val j)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out) :
    IsGreatest
      {m : ℤ | ∃ z : ℕ, z < nums.val.length ∧ ZeroAt nums.val z ∧
        ((runLeft nums.val z : ℤ) + 1 + (runRight nums.val z : ℤ)) = m} out.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_two_zeros : 2 ≤ zeroCount nums.val 0 nums.val.length)
    (h_exists_one : ∃ j : ℕ, j < nums.val.length ∧ OneAt nums.val j)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out), IsGreatest
      {m : ℤ | ∃ z : ℕ, z < nums.val.length ∧ ZeroAt nums.val z ∧
        ((runLeft nums.val z : ℤ) + 1 + (runRight nums.val z : ℤ)) = m} out.val) := by
  sorry

/-- Whenever the function returns a result out, out <= (the number of indices i with 0 <= i < len(nums) and nums[i] = 1) + 1.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1. -/
theorem spec_12 (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out) :
    out.val ≤ (oneCount nums.val 0 nums.val.length : ℤ) + 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (out : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out), out.val ≤ (oneCount nums.val 0 nums.val.length : ℤ) + 1) := by
  sorry

/-- Let revnums be the array with len(revnums) = len(nums) and revnums[i] = nums[len(nums)-1-i] for 0 <= i < len(nums). Whenever the function returns out on nums and returns out' on revnums, out = out'.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1. -/
theorem spec_13 (nums revnums : Slice Std.I64) (out out' : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_rev : revnums.val = nums.val.reverse)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out)
    (h_out' : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones revnums = ok out') :
    out = out' := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums revnums : Slice Std.I64) (out out' : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ 100000)
    (h_values : ∀ i : ℕ, i < nums.val.length → nums.val[i]!.val = 0 ∨ nums.val[i]!.val = 1)
    (h_rev : revnums.val = nums.val.reverse)
    (h_out : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones nums = ok out)
    (h_out' : Aegis.FindMaxConsecutiveOnes.find_max_consecutive_ones revnums = ok out'), out = out') := by
  sorry

end AegisSpec.FindMaxConsecutiveOnes
