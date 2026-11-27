import Aegis.MaximumSum.Code.Funs

/-!
# Specifications of `Aegis.MaximumSum.maximum_sum`

LeetCode problem `max-sum-of-a-pair-with-equal-sum-of-digits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumSum

def vals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

def digitSum (x : ℤ) : ℤ := ∑ k ∈ Finset.range 10, (x / 10 ^ k) % 10

def HasEqualDigitSumPair (l : List ℤ) : Prop :=
  ∃ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
    i < j ∧ digitSum (l[i]'hi) = digitSum (l[j]'hj)

def IsMaxEqualDigitSumPairSum (l : List ℤ) (r : ℤ) : Prop :=
  (∃ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
      i < j ∧ digitSum (l[i]'hi) = digitSum (l[j]'hj) ∧ r = l[i]'hi + l[j]'hj) ∧
    (∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
      i < j → digitSum (l[i]'hi) = digitSum (l[j]'hj) → l[i]'hi + l[j]'hj ≤ r)

def IsListMax (l : List ℤ) (m : ℤ) : Prop :=
  (∃ x ∈ l, x = m) ∧ ∀ x ∈ l, x ≤ m

def IsSumOfTwoLargest (l : List ℤ) (r : ℤ) : Prop :=
  ∃ (a₀ a₁ : ℤ) (rest : List ℤ),
    l.Perm (a₀ :: a₁ :: rest) ∧ a₁ ≤ a₀ ∧ (∀ x ∈ rest, x ≤ a₁) ∧ r = a₀ + a₁

def IsInsertionOf (l ys : List ℤ) (v : ℤ) : Prop :=
  ∃ pre post : List ℤ, l = pre ++ post ∧ ys = pre ++ [v] ++ post

/-- Whenever the function returns a result r, the following holds. If there exist indices i and j with 0 <= i < j < len(nums) and D(nums[i]) = D(nums[j]), then r = max{ nums[i] + nums[j] | 0 <= i < j < len(nums) and D(nums[i]) = D(nums[j]) }. If no such indices exist, then r = -1.
  Preconditions: len(nums) >= 1; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. Write D(x) for the sum of the decimal digits of an integer x in [1,1000000000], i.e. D(x) = sum_{k=0}^{9} ((x / 10^k) mod 10), where / is integer division and mod is remainder. Indices are 0-based. -/
theorem spec_1 (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    {r : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r) :
    (HasEqualDigitSumPair (vals nums) → IsMaxEqualDigitSumPairSum (vals nums) r.val) ∧
      (¬ HasEqualDigitSumPair (vals nums) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    {r : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r), (HasEqualDigitSumPair (vals nums) → IsMaxEqualDigitSumPairSum (vals nums) r.val) ∧
      (¬ HasEqualDigitSumPair (vals nums) → r.val = -1)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, overflow, or access out of bounds) for every input satisfying the preconditions.
  Preconditions: len(nums) >= 1; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. Write D(x) for the sum of the decimal digits of an integer x in [1,1000000000], i.e. D(x) = sum_{k=0}^{9} ((x / 10^k) mod 10), where / is integer division and mod is remainder. Indices are 0-based. -/
theorem spec_2 (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000) :
    ∃ r : I64, Aegis.MaximumSum.maximum_sum nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000), ∃ r : I64, Aegis.MaximumSum.maximum_sum nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if there are no indices i and j with 0 <= i < j < len(nums) and D(nums[i]) = D(nums[j]).
  Preconditions: len(nums) >= 1; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. Write D(x) for the sum of the decimal digits of an integer x in [1,1000000000], i.e. D(x) = sum_{k=0}^{9} ((x / 10^k) mod 10), where / is integer division and mod is remainder. Indices are 0-based. -/
theorem spec_3 (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    {r : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r) :
    (r.val = -1 ↔ ¬ HasEqualDigitSumPair (vals nums)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    {r : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r), (r.val = -1 ↔ ¬ HasEqualDigitSumPair (vals nums))) := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exist indices i and j such that 0 <= i < j < len(nums), D(nums[i]) = D(nums[j]), and nums[i] + nums[j] = r.
  Preconditions: len(nums) >= 1; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. Write D(x) for the sum of the decimal digits of an integer x in [1,1000000000], i.e. D(x) = sum_{k=0}^{9} ((x / 10^k) mod 10), where / is integer division and mod is remainder. Indices are 0-based. -/
theorem spec_4 (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    {r : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r) (hr : r.val ≠ -1) :
    ∃ (i j : ℕ) (hi : i < (vals nums).length) (hj : j < (vals nums).length),
      i < j ∧ digitSum ((vals nums)[i]'hi) = digitSum ((vals nums)[j]'hj) ∧
        r.val = (vals nums)[i]'hi + (vals nums)[j]'hj := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    {r : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r) (hr : r.val ≠ -1), ∃ (i j : ℕ) (hi : i < (vals nums).length) (hj : j < (vals nums).length),
      i < j ∧ digitSum ((vals nums)[i]'hi) = digitSum ((vals nums)[j]'hj) ∧
        r.val = (vals nums)[i]'hi + (vals nums)[j]'hj) := by
  sorry

/-- Whenever the function returns a result r with r != -1, for every pair of indices i and j with 0 <= i < j < len(nums) and D(nums[i]) = D(nums[j]), we have nums[i] + nums[j] <= r.
  Preconditions: len(nums) >= 1; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. Write D(x) for the sum of the decimal digits of an integer x in [1,1000000000], i.e. D(x) = sum_{k=0}^{9} ((x / 10^k) mod 10), where / is integer division and mod is remainder. Indices are 0-based. -/
theorem spec_5 (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    {r : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r) (hr : r.val ≠ -1) :
    ∀ (i j : ℕ) (hi : i < (vals nums).length) (hj : j < (vals nums).length),
      i < j → digitSum ((vals nums)[i]'hi) = digitSum ((vals nums)[j]'hj) →
        (vals nums)[i]'hi + (vals nums)[j]'hj ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    {r : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r) (hr : r.val ≠ -1), ∀ (i j : ℕ) (hi : i < (vals nums).length) (hj : j < (vals nums).length),
      i < j → digitSum ((vals nums)[i]'hi) = digitSum ((vals nums)[j]'hj) →
        (vals nums)[i]'hi + (vals nums)[j]'hj ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 2 <= r <= 2000000000.
  Preconditions: len(nums) >= 1; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. Write D(x) for the sum of the decimal digits of an integer x in [1,1000000000], i.e. D(x) = sum_{k=0}^{9} ((x / 10^k) mod 10), where / is integer division and mod is remainder. Indices are 0-based. -/
theorem spec_6 (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    {r : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r) :
    r.val = -1 ∨ (2 ≤ r.val ∧ r.val ≤ 2000000000) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    {r : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r), r.val = -1 ∨ (2 ≤ r.val ∧ r.val ≤ 2000000000)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, r <= 2 * max{ nums[i] | 0 <= i < len(nums) }.
  Preconditions: len(nums) >= 1; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. Write D(x) for the sum of the decimal digits of an integer x in [1,1000000000], i.e. D(x) = sum_{k=0}^{9} ((x / 10^k) mod 10), where / is integer division and mod is remainder. Indices are 0-based. -/
theorem spec_7 (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    {r : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r) (hr : r.val ≠ -1) :
    ∀ m : ℤ, IsListMax (vals nums) m → r.val ≤ 2 * m := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    {r : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r) (hr : r.val ≠ -1), ∀ m : ℤ, IsListMax (vals nums) m → r.val ≤ 2 * m) := by
  sorry

/-- Whenever len(nums) = 1, the function returns r = -1.
  Preconditions: len(nums) >= 1; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. Write D(x) for the sum of the decimal digits of an integer x in [1,1000000000], i.e. D(x) = sum_{k=0}^{9} ((x / 10^k) mod 10), where / is integer division and mod is remainder. Indices are 0-based. -/
theorem spec_8 (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    {r : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r) (hlen1 : nums.val.length = 1) :
    r.val = -1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    {r : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r) (hlen1 : nums.val.length = 1), r.val = -1) := by
  sorry

/-- Whenever len(nums) = 2, if D(nums[0]) = D(nums[1]) then the function returns r = nums[0] + nums[1]; otherwise it returns r = -1.
  Preconditions: len(nums) >= 1; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. Write D(x) for the sum of the decimal digits of an integer x in [1,1000000000], i.e. D(x) = sum_{k=0}^{9} ((x / 10^k) mod 10), where / is integer division and mod is remainder. Indices are 0-based. -/
theorem spec_9 (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    {r : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r) (hlen2 : nums.val.length = 2) :
    (digitSum (nums.val[0]'(by omega)).val = digitSum (nums.val[1]'(by omega)).val →
        r.val = (nums.val[0]'(by omega)).val + (nums.val[1]'(by omega)).val) ∧
      (digitSum (nums.val[0]'(by omega)).val ≠ digitSum (nums.val[1]'(by omega)).val →
        r.val = -1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    {r : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r) (hlen2 : nums.val.length = 2), (digitSum (nums.val[0]'(by omega)).val = digitSum (nums.val[1]'(by omega)).val →
        r.val = (nums.val[0]'(by omega)).val + (nums.val[1]'(by omega)).val) ∧
      (digitSum (nums.val[0]'(by omega)).val ≠ digitSum (nums.val[1]'(by omega)).val →
        r.val = -1)) := by
  sorry

/-- If the function returns r on nums and r' on ys, then r = r'.
  Preconditions: len(nums) >= 1; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. Let ys be any slice with len(ys) = len(nums), all entries of ys in [1,1000000000], and ys a permutation of nums (there exists a bijection p from {0,...,len(nums)-1} to {0,...,len(ys)-1} such that ys[p(i)] = nums[i] for every i). Write D(x) for the sum of the decimal digits of an integer x in [1,1000000000], i.e. D(x) = sum_{k=0}^{9} ((x / 10^k) mod 10), where / is integer division and mod is remainder. Indices are 0-based. -/
theorem spec_10 (nums ys : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hlen' : 1 ≤ ys.val.length)
    (hb' : ∀ i (hi : i < ys.val.length),
      1 ≤ (ys.val[i]'hi).val ∧ (ys.val[i]'hi).val ≤ 1000000000)
    (hsame : ys.val.length = nums.val.length) (hperm : (vals ys).Perm (vals nums))
    {r r' : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r)
    (hres' : Aegis.MaximumSum.maximum_sum ys = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums ys : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hlen' : 1 ≤ ys.val.length)
    (hb' : ∀ i (hi : i < ys.val.length),
      1 ≤ (ys.val[i]'hi).val ∧ (ys.val[i]'hi).val ≤ 1000000000)
    (hsame : ys.val.length = nums.val.length) (hperm : (vals ys).Perm (vals nums))
    {r r' : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r)
    (hres' : Aegis.MaximumSum.maximum_sum ys = ok r'), r.val = r'.val) := by
  sorry

/-- If the function returns r on nums and r' on ys, then r != -1 implies r' != -1 and r' >= r.
  Preconditions: len(nums) >= 1; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. Let v be an integer with 1 <= v <= 1000000000, and let ys be any slice obtained from nums by inserting one additional value v at some position, so len(ys) = len(nums) + 1 and deleting that occurrence from ys recovers nums. Write D(x) for the sum of the decimal digits of an integer x in [1,1000000000], i.e. D(x) = sum_{k=0}^{9} ((x / 10^k) mod 10), where / is integer division and mod is remainder. Indices are 0-based. -/
theorem spec_11 (nums ys : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hlen' : 1 ≤ ys.val.length)
    (hb' : ∀ i (hi : i < ys.val.length),
      1 ≤ (ys.val[i]'hi).val ∧ (ys.val[i]'hi).val ≤ 1000000000)
    {v : ℤ} (hv1 : 1 ≤ v) (hv2 : v ≤ 1000000000) (hins : IsInsertionOf (vals nums) (vals ys) v)
    {r r' : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r)
    (hres' : Aegis.MaximumSum.maximum_sum ys = ok r') :
    r.val ≠ -1 → r'.val ≠ -1 ∧ r.val ≤ r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums ys : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hlen' : 1 ≤ ys.val.length)
    (hb' : ∀ i (hi : i < ys.val.length),
      1 ≤ (ys.val[i]'hi).val ∧ (ys.val[i]'hi).val ≤ 1000000000)
    {v : ℤ} (hv1 : 1 ≤ v) (hv2 : v ≤ 1000000000) (hins : IsInsertionOf (vals nums) (vals ys) v)
    {r r' : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r)
    (hres' : Aegis.MaximumSum.maximum_sum ys = ok r'), r.val ≠ -1 → r'.val ≠ -1 ∧ r.val ≤ r'.val) := by
  sorry

/-- Whenever len(nums) >= 2 and D(nums[i]) = D(nums[j]) for every pair of indices 0 <= i < j < len(nums), the function returns r equal to the sum of the two largest elements of nums, counting multiplicity; that is, if the elements of nums in nonincreasing order are a0 >= a1 >= ..., then r = a0 + a1.
  Preconditions: len(nums) >= 1; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. Write D(x) for the sum of the decimal digits of an integer x in [1,1000000000], i.e. D(x) = sum_{k=0}^{9} ((x / 10^k) mod 10), where / is integer division and mod is remainder. Indices are 0-based. -/
theorem spec_12 (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    {r : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r) (hlen2 : 2 ≤ nums.val.length)
    (hall : ∀ (i j : ℕ) (hi : i < (vals nums).length) (hj : j < (vals nums).length),
      i < j → digitSum ((vals nums)[i]'hi) = digitSum ((vals nums)[j]'hj)) :
    IsSumOfTwoLargest (vals nums) r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (hlen : 1 ≤ nums.val.length)
    (hb : ∀ i (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    {r : I64} (hres : Aegis.MaximumSum.maximum_sum nums = ok r) (hlen2 : 2 ≤ nums.val.length)
    (hall : ∀ (i j : ℕ) (hi : i < (vals nums).length) (hj : j < (vals nums).length),
      i < j → digitSum ((vals nums)[i]'hi) = digitSum ((vals nums)[j]'hj)), IsSumOfTwoLargest (vals nums) r.val) := by
  sorry

end AegisSpec.MaximumSum
